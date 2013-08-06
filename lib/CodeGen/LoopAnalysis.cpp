//===--- LoopAnalysis.cpp - Analyze Loops for Vectorization -----*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Analyze loops for vectorization purposes.
//
//===----------------------------------------------------------------------===//

#include "LoopAnalysis.h"

#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/PassRegistry.h"
#include "llvm/PassManagers.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Assembly/PrintModulePass.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/CodeGen/RegAllocRegistry.h"
#include "llvm/CodeGen/SchedulerRegistry.h"
#include "llvm/MC/SubtargetFeature.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/Timer.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/Transforms/Utils/Cloning.h" // CloneFunction()
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h" // FunctionType
#include "llvm/IR/Constants.h" // UndefValue
#include "llvm/IR/Instructions.h" // CallInst
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/IR/IntrinsicInst.h"

#include <iostream>

#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"

#include "llvm/ADT/MapVector.h"

using namespace llvm;

namespace llvm {

struct RuntimePointerCheck {
    RuntimePointerCheck() : Need(false) {}

    /// Reset the state of the pointer runtime information.
    void reset() {
        Need = false;
        Pointers.clear();
        Starts.clear();
        Ends.clear();
    }

    /// Insert a pointer and calculate the start and end SCEVs.
    void insert(ScalarEvolution *mSCEV, Loop *Lp, Value *Ptr, bool WritePtr,
            unsigned DepSetId)
    {
        const SCEV *Sc = mSCEV->getSCEV(Ptr);
        const SCEVAddRecExpr *AR = dyn_cast<SCEVAddRecExpr>(Sc);
        assert(AR && "Invalid addrec expression");
        const SCEV *Ex = mSCEV->getBackedgeTakenCount(Lp);
        const SCEV *ScEnd = AR->evaluateAtIteration(Ex, *mSCEV);
        Pointers.push_back(Ptr);
        Starts.push_back(AR->getStart());
        Ends.push_back(ScEnd);
        IsWritePtr.push_back(WritePtr);
        DependencySetId.push_back(DepSetId);
    }

    /// This flag indicates if we need to add the runtime check.
    bool Need;
    /// Holds the pointers that we need to check.
    SmallVector<TrackingVH<Value>, 2> Pointers;
    /// Holds the pointer value at the beginning of the loop.
    SmallVector<const SCEV*, 2> Starts;
    /// Holds the pointer value at the end of the loop.
    SmallVector<const SCEV*, 2> Ends;
    /// Holds the information if this pointer is used for writing to memory.
    SmallVector<bool, 2> IsWritePtr;
    /// Holds the id of the set of pointers that could be dependent because of a
    /// shared underlying object.
    SmallVector<unsigned, 2> DependencySetId;
};


void initializeLoopAnalyzerPass(PassRegistry&);

struct LoopAnalyzer : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid

  Module*          mModule;
  LLVMContext*     mContext;
  LoopInfo*        mLoopInfo;
  DominatorTree*   mDomTree;
  ScalarEvolution* mSCEV;
  DataLayout*      mDataLayout;
  raw_ostream*     mOut;

  TargetLibraryInfo* mTLI;
  RuntimePointerCheck mPtrRtCheck;

  enum LoopType
  {
      NOT_VECTORIZABLE,
      VECTORIZABLE_TRIVIAL,
      VECTORIZABLE_COMMON,
      VECTORIZABLE_MULTIOP,
      VECTORIZABLE_NOISE
  };

  void printLoopType(const LoopType lt, const Loop& loop, raw_ostream& out) const;
  std::string loopTypeToString(const LoopType lt) const;

  LoopAnalyzer(raw_ostream* out=0);
  virtual ~LoopAnalyzer();
  virtual bool runOnFunction(Function &F);
  virtual void getAnalysisUsage(AnalysisUsage &AU) const;

  struct ReductionUpdate
  {
    ~ReductionUpdate();

    // The update operation.
    Instruction*      mOperation;
    // The operands that are *not* part of the reduction SCC.
    typedef SmallVector<Value*, 2> OtherOperandsVec;
    OtherOperandsVec* mOtherOperands;
    // The users of this update operation that are *not* part of the reduction SCC (if any).
    typedef SetVector<Instruction*> ResultUsersVec;
    ResultUsersVec*   mResultUsers;
    // The alloca of the scalar result of this reduction operation (given
    // as output parameter to call).
    Instruction*      mIntermediateResultPtr;
  };

  typedef MapVector<Instruction*, ReductionUpdate*> RedUpMapType;

  struct ReductionVariable
  {
    ~ReductionVariable();

    // The reduction phi in the loop header.
    PHINode*      mPhi;
    // The start value (phi operand from pre header).
    Value*        mStartVal;
    // All update operations that belong to the reduction SCC.
    RedUpMapType* mUpdates;
    // The final reduction result user (if any).
    PHINode*      mResultUser;

    // The position where the reduction operations will be performed after WFV.
    Instruction*  mReductionPos;
    // The scalar reduction function (dummy declaration only).
    Function*     mReductionFn;
    // The call to the scalar reduction function.
    CallInst*     mReductionFnCall;
    // The SIMD reduction function.
    Function*     mReductionFnSIMD;

    // The alloca that stores the final reduction result in the original function.
    AllocaInst*   mResultPtr;

    // The argument of the SIMD reduction function that corresponds to the reduction phi.
    Argument*     mPhiArg;
    // The argument of the SIMD reduction function that corresponds to the result pointer.
    Argument*     mOutArg;
    // The store instruction that writes back the final reduction result to mOutArg.
    StoreInst*    mStoreBack;
    // The value that goes back to the reduction phi from the latch in the original function.
    Instruction*  mBackEdgeVal;

    // Store information whether this reduction can be optimized in the classic way.
    bool          mCanOptimizeWithVector;
    unsigned      mCommonOpcode;
  };

  typedef SmallVector<ReductionVariable*, 2> RedVarVecType;

  //////////////////////////////////////////////////////////////////////////////
  // Helper functions for collectReductionVariables().
  //////////////////////////////////////////////////////////////////////////////

  // TODO: There's a problem with store-load chains that we don't detect
  //       to be part of the SCC!
  bool findReductionSCC(Instruction*                  curInst,
                        PHINode*                      reductionPhi,
                        const Loop&                   loop,
                        RedUpMapType&                 reductionSCC,
                        SmallPtrSet<Instruction*, 8>& visitedInsts);

  void gatherConditions(BasicBlock*                        block,
                        BasicBlock*                        succBB,
                        const BasicBlock*                  latchBB,
                        const DominatorTree&               domTree,
                        ReductionUpdate::OtherOperandsVec& otherOperands,
                        SmallPtrSet<BasicBlock*, 8>&       visitedBlocks);

  void gatherReductionUpdateInfo(RedUpMapType&        reductionSCC,
                                 const PHINode*       reductionPhi,
                                 const BasicBlock*    latchBB,
                                 const DominatorTree& domTree);

  //////////////////////////////////////////////////////////////////////////////

  void collectReductionVariables(RedVarVecType&       redVars,
                                 PHINode*             indVarPhi,
                                 const Loop&          loop,
                                 const DominatorTree& domTree,
                                 raw_ostream&         out);

  bool dependsOnControlFlow(Instruction* inst, const Loop& loop, const DominatorTree& domTree);

  bool isCAUpdateOp(const unsigned opcode);

  bool canVectorizeMemory(Loop* TheLoop);

  LoopType analyzeLoop(Loop*        loop,
                       Loop*        parentLoop,
                       raw_ostream& out);
};

char LoopAnalyzer::ID = 0;
}

// Pass declarations

INITIALIZE_PASS_BEGIN(LoopAnalyzer, "analyze-loops",
                      "Analyze loops for vectorization", false, true)
//INITIALIZE_PASS_DEPENDENCY(AliasAnalysis)
//INITIALIZE_PASS_DEPENDENCY(TargetTransformInfo)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolution)
INITIALIZE_PASS_DEPENDENCY(LoopSimplify)
INITIALIZE_PASS_DEPENDENCY(LoopInfo)
INITIALIZE_PASS_DEPENDENCY(DominatorTree)
INITIALIZE_PASS_END(LoopAnalyzer, "analyze-loops",
                    "Analyze loops for vectorization", false, true)


namespace llvm {
namespace loopanalysis {

LoopAnalysis::LoopAnalysis(Module* M) : Mod(CloneModule(M)) {}
LoopAnalysis::~LoopAnalysis() { delete Mod; }

void LoopAnalysis::Analyze()
{
  PrettyStackTraceString CrashInfoLoopAnalysis("LOOPANALYZER: Analyzing loops");

  //////////////////////////////////////////////////////////////////////////////
  // LOOP ANALYZER: CATEGORIZE LOOPS IN TERMS OF THEIR VECTORIZABILITY.
  //////////////////////////////////////////////////////////////////////////////

  std::string error;
  raw_fd_ostream out("loop_analysis.txt", error, raw_fd_ostream::F_Append);

  out << "\n\nLoop analysis of module: '" << Mod->getModuleIdentifier() << "':\n";

  PassManager PM;
  PM.add(new DataLayout(Mod));
  // Perform some standard optimizations upfront.
  PM.add(createTypeBasedAliasAnalysisPass());
  PM.add(createBasicAliasAnalysisPass());
  PM.add(createScalarReplAggregatesPass());
  // Perform some transformations that ease loop vectorization.
  PM.add(createLoopSimplifyPass());
  PM.add(createIndVarSimplifyPass());
  PM.add(createLCSSAPass());
  PM.add(createScalarEvolutionAliasAnalysisPass());
  // Now analyze the code.
  PM.add(new LoopAnalyzer(&out));
  PM.run(*Mod);

  return;
}

} // namespace loopanalysis


typedef LoopAnalyzer::ReductionUpdate ReductionUpdate;
typedef LoopAnalyzer::ReductionVariable ReductionVariable;
typedef LoopAnalyzer::ReductionUpdate::ResultUsersVec ResultUsersVec;
typedef LoopAnalyzer::ReductionUpdate::OtherOperandsVec OtherOperandsVec;

void
LoopAnalyzer::printLoopType(const LoopType lt, const Loop& loop, raw_ostream& out) const
{
  if (lt == NOT_VECTORIZABLE) out << "  summary: NOT_VECTORIZABLE\n";
  out << "loop with header " << loop.getHeader()->getName();
  switch (lt)
  {
    case NOT_VECTORIZABLE:
    {
      out << " is not vectorizable!\n";
      break;
    }
    case VECTORIZABLE_TRIVIAL:
    {
      out << " is trivially vectorizable!\n";
      break;
    }
    case VECTORIZABLE_COMMON:
    {
      out << " is vectorizable with reductions!\n";
      break;
    }
    case VECTORIZABLE_MULTIOP:
    {
      out << " is vectorizable if multiple reduction operations supported!\n";
      break;
    }
    case VECTORIZABLE_NOISE:
    {
      out << " is vectorizable by noise!\n";
      break;
    }
  }
}

std::string
LoopAnalyzer::loopTypeToString(const LoopType lt) const
{
  switch (lt)
  {
    case NOT_VECTORIZABLE: return "NOT_VECTORIZABLE";
    case VECTORIZABLE_TRIVIAL: return "VECTORIZABLE_TRIVIAL";
    case VECTORIZABLE_COMMON: return "VECTORIZABLE_COMMON";
    case VECTORIZABLE_MULTIOP: return "VECTORIZABLE_MULTIOP";
    case VECTORIZABLE_NOISE: return "VECTORIZABLE_NOISE";
  }
}

LoopAnalyzer::LoopAnalyzer(raw_ostream* out) : FunctionPass(ID), mOut(out)
{
  initializeLoopAnalyzerPass(*PassRegistry::getPassRegistry());
}

LoopAnalyzer::~LoopAnalyzer() { }

bool
LoopAnalyzer::runOnFunction(Function &F)
{
    mModule     = F.getParent();
    mContext    = &F.getContext();
    mLoopInfo   = &getAnalysis<LoopInfo>();
    mDomTree    = &getAnalysis<DominatorTree>();
    mSCEV       = &getAnalysis<ScalarEvolution>();
    mDataLayout = getAnalysisIfAvailable<DataLayout>();
    mTLI        = getAnalysisIfAvailable<TargetLibraryInfo>();

    if (!mOut) mOut = &(outs());

    (*mOut) << "\nLoop analysis of function: '" << F.getName() << "':\n";

    for (LoopInfo::iterator L=mLoopInfo->begin(), LE=mLoopInfo->end(); L!=LE; ++L)
    {
        const LoopType lt = analyzeLoop(*L, NULL, *mOut);
        printLoopType(lt, **L, *mOut);
    }

    return false;
}

void
LoopAnalyzer::getAnalysisUsage(AnalysisUsage &AU) const
{
    //AU.addRequiredID(LoopSimplifyID); // "Unable to schedule"
    //AU.addRequiredID(LCSSAID); // "Unable to schedule"
    AU.addRequired<ScalarEvolution>();
    AU.addRequired<LoopInfo>();
    AU.addRequired<DominatorTree>();
    AU.addRequired<DataLayout>();
    AU.setPreservesAll();
}


ReductionUpdate::~ReductionUpdate()
{
    mOtherOperands->clear();
    mResultUsers->clear();
    delete mOtherOperands;
    delete mResultUsers;
}

ReductionVariable::~ReductionVariable()
{
    for (RedUpMapType::iterator it=mUpdates->begin(),
        E=mUpdates->end(); it!=E; ++it)
    {
        delete it->second;
    }
    delete mUpdates;
}

//////////////////////////////////////////////////////////////////////////////
// Helper functions for collectReductionVariables().
//////////////////////////////////////////////////////////////////////////////

// TODO: There's a problem with store-load chains that we don't detect
//       to be part of the SCC!
bool
LoopAnalyzer::findReductionSCC(Instruction*                  curInst,
                               PHINode*                      reductionPhi,
                               const Loop&                   loop,
                               RedUpMapType&                 reductionSCC,
                               SmallPtrSet<Instruction*, 8>& visitedInsts)
{
    assert (curInst && reductionPhi);

    if (visitedInsts.count(curInst)) return false;
    visitedInsts.insert(curInst);

    if (reductionSCC.count(curInst)) return true;
    if (curInst == reductionPhi) return true;

    // Recurse into the operands and see if we can find the reduction phi or
    // another instruction that is already part of the SCC.
    bool isInSCC = false;
    for (Instruction::op_iterator O=curInst->op_begin(),
         OE=curInst->op_end(); O!=OE; ++O)
    {
        // Don't recurse into non-instruction operands.
        if (!isa<Instruction>(*O)) continue;
        Instruction* opInst = cast<Instruction>(*O);

        // If this predecessor is already in the SCC, don't recurse into it.
        if (reductionPhi == opInst || reductionSCC.count(opInst))
        {
            isInSCC = true;
            continue;
        }

        // Don't recurse into blocks that are not in the loop.
        BasicBlock* opBB = opInst->getParent();
        if (!loop.contains(opBB)) continue;

        // Recurse.
        isInSCC |= findReductionSCC(opInst, reductionPhi, loop, reductionSCC, visitedInsts);
    }

    if (!isInSCC) return false;

    ReductionUpdate* redUp = new ReductionUpdate();
    redUp->mOperation = curInst;

    reductionSCC[curInst] = redUp;

    return true;
}

void
LoopAnalyzer::gatherConditions(BasicBlock*                  block,
                               BasicBlock*                  succBB,
                               const BasicBlock*            latchBB,
                               const DominatorTree&         domTree,
                               OtherOperandsVec&            otherOperands,
                               SmallPtrSet<BasicBlock*, 8>& visitedBlocks)
{
    assert (block && latchBB);

    if (visitedBlocks.count(block)) return;
    visitedBlocks.insert(block);

    // If succBB is not set this is the first block of this path,
    // so we don't want to add any condition.
    TerminatorInst* terminator = block->getTerminator();
    if (succBB && terminator->getNumSuccessors() > 1)
    {
        if (const BranchInst* brI = dyn_cast<BranchInst>(terminator))
        {
            assert (brI->isConditional());
            otherOperands.push_back(brI->getCondition());
        }
        else if (SwitchInst* swI = dyn_cast<SwitchInst>(terminator))
        {
            otherOperands.push_back(swI->getCondition());
            ConstantInt* caseDest = swI->findCaseDest(succBB);
            // The case value can be null if the successor is the default case or not unique.
            if (caseDest) otherOperands.push_back(caseDest);
        }
        else
        {
            assert (false && "not implemented!");
        }
    }

    // If this block dominates the loop latch block, we are done for this path.
    if (domTree.dominates(block, latchBB)) return;

    // Otherwise, recurse into predecessors.
    for (pred_iterator P=pred_begin(block), PE=pred_end(block); P!=PE; ++P)
    {
        BasicBlock* predBB = *P;
        gatherConditions(predBB, block, latchBB, domTree, otherOperands, visitedBlocks);
    }
}

void
LoopAnalyzer::gatherReductionUpdateInfo(RedUpMapType&        reductionSCC,
                                        const PHINode*       reductionPhi,
                                        const BasicBlock*    latchBB,
                                        const DominatorTree& domTree)
{
    for (RedUpMapType::iterator it=reductionSCC.begin(),
        E=reductionSCC.end(); it!=E; ++it)
    {
        ReductionUpdate& redUp = *it->second;
        Instruction* updateOp = redUp.mOperation;

        // Add all operands that are not part of the SCC to the "other operands" set.
        OtherOperandsVec* otherOperands = new OtherOperandsVec();
        for (Instruction::op_iterator O=updateOp->op_begin(),
            OE=updateOp->op_end(); O!=OE; ++O)
        {
            if (isa<BasicBlock>(*O)) continue;
            if (isa<Function>(*O)) continue;

            if (Instruction* opInst = dyn_cast<Instruction>(*O))
            {
                if (reductionPhi == opInst) continue;
                if (reductionSCC.count(opInst)) continue;
            }
            otherOperands->push_back(*O);
        }
        redUp.mOtherOperands = otherOperands;

        // Add all users that are not part of the SCC to the "result users" set.
        ResultUsersVec* resultUsers = new ResultUsersVec();
        for (Instruction::use_iterator U=updateOp->use_begin(),
            UE=updateOp->use_end(); U!=UE; ++U)
        {
            assert (isa<Instruction>(*U));
            Instruction* useI = cast<Instruction>(*U);
            if (reductionPhi == useI) continue;
            if (reductionSCC.count(useI)) continue;

            resultUsers->insert(useI);
        }
        redUp.mResultUsers = resultUsers;

        // More concretely, we collect all conditions that this update depends upon.
        // NOTE: It would be beneficial to have WFV divergence information here.
        BasicBlock* block = updateOp->getParent();
        SmallPtrSet<BasicBlock*, 8> visitedBlocks;
        gatherConditions(block, NULL, latchBB, domTree, *otherOperands, visitedBlocks);

        // The other information is only inserted later.
        redUp.mIntermediateResultPtr = NULL;
    }
}

//////////////////////////////////////////////////////////////////////////////

// TODO: Make sure there is no interference between reduction variables.
void
LoopAnalyzer::collectReductionVariables(RedVarVecType&       redVars,
                                        PHINode*             indVarPhi,
                                        const Loop&          loop,
                                        const DominatorTree& domTree,
                                        raw_ostream&         out)
{
    assert (indVarPhi);

    BasicBlock* preheaderBB = loop.getLoopPreheader();
    BasicBlock* headerBB    = loop.getHeader();
    BasicBlock* latchBB     = loop.getLoopLatch();
    BasicBlock* exitBB      = loop.getExitBlock();

    for (BasicBlock::iterator I=headerBB->begin(),
        IE=headerBB->end(); I!=IE; ++I)
    {
        if (headerBB->getFirstNonPHI() == I) break;
        if (indVarPhi == I) continue;

        PHINode* reductionPhi = cast<PHINode>(I);
        if (reductionPhi->getNumIncomingValues() != 2)
        {
            out << "  has phi with more than 2 incoming values (not in LCSSA)!\n";
            continue;
        }

        ReductionVariable* redVar = new ReductionVariable();
        redVar->mPhi = reductionPhi;

        assert (reductionPhi->getIncomingValueForBlock(preheaderBB));
        redVar->mStartVal = reductionPhi->getIncomingValueForBlock(preheaderBB);

        assert (reductionPhi->getIncomingValueForBlock(latchBB));
        if (!isa<Instruction>(reductionPhi->getIncomingValueForBlock(latchBB)))
        {
            out << "  has phi with non-instruction value incoming from latch: ";
            out << *reductionPhi << "\n";
            continue;
        }
        Instruction* backEdgeVal = cast<Instruction>(reductionPhi->getIncomingValueForBlock(latchBB));
        redVar->mBackEdgeVal = backEdgeVal;

        RedUpMapType* reductionSCC = new RedUpMapType();
        SmallPtrSet<Instruction*, 8> visitedInsts;
        findReductionSCC(backEdgeVal, reductionPhi, loop, *reductionSCC, visitedInsts);

        // If there is no SCC, this is no reduction (should only happen if this
        // is the induction variable phi that could not be determined to be it).
        if (reductionSCC->empty())
        {
            out << "  has empty reduction SCC for phi: " << *reductionPhi << "\n";
            continue;
        }

        gatherReductionUpdateInfo(*reductionSCC, reductionPhi, latchBB, domTree);

        redVar->mUpdates = reductionSCC;

        // There does not need to be a result user, but there may be one.
        redVar->mResultUser = NULL;
        for (BasicBlock::iterator I2=exitBB->begin(),
            IE2=exitBB->end(); I2!=IE2; ++I2)
        {
            if (exitBB->getFirstNonPHI() == I2) break;
            PHINode* exitPhi = cast<PHINode>(I2);
            if (exitPhi->getNumIncomingValues() != 1)
            {
                out << "  has exit phi with more than one incoming value (not in LCSSA)!\n";
                bool found = false;
                for (unsigned i=0, e=exitPhi->getNumIncomingValues(); i<e; ++i)
                {
                    found |= exitPhi->getIncomingValue(i) == reductionPhi;
                }
                if (!found) continue;
            }
            else if (exitPhi->getIncomingValue(0) != reductionPhi)
            {
                continue;
            }

            if (redVar->mResultUser)
            {
                out << "  has more than one reduction user outside the loop (not in LCSSA)!\n";
            }
            redVar->mResultUser = exitPhi;
        }

        // Check if this reduction can be optimized, i.e. performed using vector
        // instructions and a post-loop horizontal vector update operation.
        // Do not consider phis when testing for a common opcode.
        bool hasCommonOpcode = true;
        unsigned commonOpcode = 0;
        bool hasIntermediateUses = false;
        for (RedUpMapType::const_iterator it=reductionSCC->begin(),
            E=reductionSCC->end(); it!=E; ++it)
        {
            const ReductionUpdate& redUp = *it->second;

            const unsigned redUpOpcode = redUp.mOperation->getOpcode();
            assert (redUpOpcode != 0 && "expected opcode 0 not to exist!");

            if (!isa<PHINode>(redUp.mOperation) &&
                commonOpcode != redUpOpcode)
            {
                if (commonOpcode == 0)
                {
                    commonOpcode = redUpOpcode;
                }
                else
                {
                    hasCommonOpcode = false;
                }
            }

            if (!redUp.mResultUsers->empty())
            {
                hasIntermediateUses = true;
            }
        }

        // If all updates are phis, set the opcode accordingly.
        if (hasCommonOpcode && commonOpcode == 0 && !reductionSCC->empty())
        {
            assert (isa<PHINode>(reductionSCC->begin()->second->mOperation));
            commonOpcode = reductionSCC->begin()->second->mOperation->getOpcode();
        }

        if (!hasIntermediateUses &&
            hasCommonOpcode &&
            isCAUpdateOp(commonOpcode))
        {
            redVar->mCanOptimizeWithVector = true;
        }

        redVar->mCommonOpcode = hasCommonOpcode ? commonOpcode : 0;

        // Sanity check.
        for (Instruction::use_iterator U=reductionPhi->use_begin(),
            UE=reductionPhi->use_end(); U!=UE; ++U)
        {
            assert (isa<Instruction>(*U));
            Instruction* useI = cast<Instruction>(*U);
            if (loop.contains(useI->getParent())) continue;
            if (useI != redVar->mResultUser)
            {
                out << "  has more than one reduction user outside the loop (not in LCSSA)!\n";
            }
        }

        // The other information is only inserted later.
        redVar->mReductionFn     = NULL;
        redVar->mReductionFnCall = NULL;
        redVar->mReductionFnSIMD = NULL;
        redVar->mResultPtr = NULL;
        redVar->mPhiArg = NULL;
        redVar->mOutArg = NULL;
        redVar->mStoreBack = NULL;

        redVars.push_back(redVar);
    }
}

bool
LoopAnalyzer::isCAUpdateOp(const unsigned opcode)
{
    switch (opcode)
    {
        case Instruction::Add:
        case Instruction::FAdd:
        case Instruction::Mul:
        case Instruction::FMul:
        case Instruction::And:
        case Instruction::Or:
        case Instruction::Xor:
        case Instruction::Shl:
        case Instruction::LShr:
        case Instruction::AShr:
        case Instruction::PHI:
        case Instruction::Select:
        case Instruction::GetElementPtr:
            return true;
        default:
            return false;
    }
}

bool
LoopAnalyzer::dependsOnControlFlow(Instruction*         inst,
                                   const Loop&          loop,
                                   const DominatorTree& domTree)
{
    assert (inst);
    return !domTree.dominates(inst->getParent(), loop.getLoopLatch());
}


namespace {
/// \brief Analyses memory accesses in a loop.
///
/// Checks whether run time pointer checks are needed and builds sets for data
/// dependence checking.
class AccessAnalysis {
public:
    /// \brief Read or write access location.
    typedef PointerIntPair<Value *, 1, bool> MemAccessInfo;
    typedef SmallPtrSet<MemAccessInfo, 8> MemAccessInfoSet;

    /// \brief Set of potential dependent memory accesses.
    typedef EquivalenceClasses<MemAccessInfo> DepCandidates;

    AccessAnalysis(DataLayout *Dl, DepCandidates &DA) :
        DL(Dl), DepCands(DA), AreAllWritesIdentified(true),
        AreAllReadsIdentified(true), IsRTCheckNeeded(false) {}

    /// \brief Register a load  and whether it is only read from.
    void addLoad(Value *Ptr, bool IsReadOnly) {
        Accesses.insert(MemAccessInfo(Ptr, false));
        if (IsReadOnly)
            ReadOnlyPtr.insert(Ptr);
    }

    /// \brief Register a store.
    void addStore(Value *Ptr) {
        Accesses.insert(MemAccessInfo(Ptr, true));
    }

    /// \brief Check whether we can check the pointers at runtime for
    /// non-intersection.
    bool canCheckPtrAtRT(RuntimePointerCheck &RtCheck,
            unsigned &NumComparisons, ScalarEvolution *SE,
            Loop *TheLoop);

    /// \brief Goes over all memory accesses, checks whether a RT check is needed
    /// and builds sets of dependent accesses.
    void buildDependenceSets() {
        // Process read-write pointers first.
        processMemAccesses(false);
        // Next, process read pointers.
        processMemAccesses(true);
    }

    bool isRTCheckNeeded() { return IsRTCheckNeeded; }

    bool isDependencyCheckNeeded() { return !CheckDeps.empty(); }

    MemAccessInfoSet &getDependenciesToCheck() { return CheckDeps; }

private:
    typedef SetVector<MemAccessInfo> PtrAccessSet;
    typedef DenseMap<Value*, MemAccessInfo> UnderlyingObjToAccessMap;

    /// \brief Go over all memory access or only the deferred ones if
    /// \p UseDeferred is true and check whether runtime pointer checks are needed
    /// and build sets of dependency check candidates.
    void processMemAccesses(bool UseDeferred);

    /// Set of all accesses.
    PtrAccessSet Accesses;

    /// Set of access to check after all writes have been processed.
    PtrAccessSet DeferredAccesses;

    /// Map of pointers to last access encountered.
    UnderlyingObjToAccessMap ObjToLastAccess;

    /// Set of accesses that need a further dependence check.
    MemAccessInfoSet CheckDeps;

    /// Set of pointers that are read only.
    SmallPtrSet<Value*, 16> ReadOnlyPtr;

    /// Set of underlying objects already written to.
    SmallPtrSet<Value*, 16> WriteObjects;

    DataLayout *DL;

    /// Sets of potentially dependent accesses - members of one set share an
    /// underlying pointer. The set "CheckDeps" identfies which sets really need a
    /// dependence check.
    DepCandidates &DepCands;

    bool AreAllWritesIdentified;
    bool AreAllReadsIdentified;
    bool IsRTCheckNeeded;
};

} // end anonymous namespace

/// \brief Check whether a pointer can participate in a runtime bounds check.
static bool hasComputableBounds(ScalarEvolution *SE, Value *Ptr) {
    const SCEV *PtrScev = SE->getSCEV(Ptr);
    const SCEVAddRecExpr *AR = dyn_cast<SCEVAddRecExpr>(PtrScev);
    if (!AR)
        return false;

    return AR->isAffine();
}

bool AccessAnalysis::canCheckPtrAtRT(
        RuntimePointerCheck &RtCheck,
        unsigned &NumComparisons, ScalarEvolution *SE,
        Loop *TheLoop) {
    // Find pointers with computable bounds. We are going to use this information
    // to place a runtime bound check.
    unsigned NumReadPtrChecks = 0;
    unsigned NumWritePtrChecks = 0;
    bool CanDoRT = true;

    bool IsDepCheckNeeded = isDependencyCheckNeeded();
    // We assign consecutive id to access from different dependence sets.
    // Accesses within the same set don't need a runtime check.
    unsigned RunningDepId = 1;
    DenseMap<Value *, unsigned> DepSetId;

    for (PtrAccessSet::iterator AI = Accesses.begin(), AE = Accesses.end();
            AI != AE; ++AI) {
        const MemAccessInfo &Access = *AI;
        Value *Ptr = Access.getPointer();
        bool IsWrite = Access.getInt();

        // Just add write checks if we have both.
        if (!IsWrite && Accesses.count(MemAccessInfo(Ptr, true)))
            continue;

        if (IsWrite)
            ++NumWritePtrChecks;
        else
            ++NumReadPtrChecks;

        if (hasComputableBounds(SE, Ptr)) {
            // The id of the dependence set.
            unsigned DepId;

            if (IsDepCheckNeeded) {
                Value *Leader = DepCands.getLeaderValue(Access).getPointer();
                unsigned &LeaderId = DepSetId[Leader];
                if (!LeaderId)
                    LeaderId = RunningDepId++;
                DepId = LeaderId;
            } else
                // Each access has its own dependence set.
                DepId = RunningDepId++;

            RtCheck.insert(SE, TheLoop, Ptr, IsWrite, DepId);

            //DEBUG(dbgs() << "LV: Found a runtime check ptr:" << *Ptr <<"\n");
        } else {
            CanDoRT = false;
        }
    }

    if (IsDepCheckNeeded && CanDoRT && RunningDepId == 2)
        NumComparisons = 0; // Only one dependence set.
    else
        NumComparisons = (NumWritePtrChecks * (NumReadPtrChecks +
                    NumWritePtrChecks - 1));
    return CanDoRT;
}

namespace loopanalysis {
bool isNoAliasCall(const Value *V) {
  if (isa<CallInst>(V) || isa<InvokeInst>(V))
    return ImmutableCallSite(cast<Instruction>(V))
      .paramHasAttr(0, Attribute::NoAlias);
  return false;
}
bool isNoAliasArgument(const Value *V)
{
    if (const Argument *A = dyn_cast<Argument>(V))
        return A->hasNoAliasAttr();
    return false;
}
}

static bool isFunctionScopeIdentifiedObject(Value *Ptr) {
    return loopanalysis::isNoAliasArgument(Ptr) || loopanalysis::isNoAliasCall(Ptr) || isa<AllocaInst>(Ptr);
}

void AccessAnalysis::processMemAccesses(bool UseDeferred) {
    // We process the set twice: first we process read-write pointers, last we
    // process read-only pointers. This allows us to skip dependence tests for
    // read-only pointers.

    PtrAccessSet &S = UseDeferred ? DeferredAccesses : Accesses;
    for (PtrAccessSet::iterator AI = S.begin(), AE = S.end(); AI != AE; ++AI) {
        const MemAccessInfo &Access = *AI;
        Value *Ptr = Access.getPointer();
        bool IsWrite = Access.getInt();

        DepCands.insert(Access);

        // Memorize read-only pointers for later processing and skip them in the
        // first round (they need to be checked after we have seen all write
        // pointers). Note: we also mark pointer that are not consecutive as
        // "read-only" pointers (so that we check "a[b[i]] +="). Hence, we need the
        // second check for "!IsWrite".
        bool IsReadOnlyPtr = ReadOnlyPtr.count(Ptr) && !IsWrite;
        if (!UseDeferred && IsReadOnlyPtr) {
            DeferredAccesses.insert(Access);
            continue;
        }

        bool NeedDepCheck = false;
        // Check whether there is the possiblity of dependency because of underlying
        // objects being the same.
        typedef SmallVector<Value*, 16> ValueVector;
        ValueVector TempObjects;
        GetUnderlyingObjects(Ptr, TempObjects, DL);
        for (ValueVector::iterator UI = TempObjects.begin(), UE = TempObjects.end();
                UI != UE; ++UI) {
            Value *UnderlyingObj = *UI;

            // If this is a write then it needs to be an identified object.  If this a
            // read and all writes (so far) are identified function scope objects we
            // don't need an identified underlying object but only an Argument (the
            // next write is going to invalidate this assumption if it is
            // unidentified).
            // This is a micro-optimization for the case where all writes are
            // identified and we have one argument pointer.
            // Otherwise, we do need a runtime check.
            if ((IsWrite && !isFunctionScopeIdentifiedObject(UnderlyingObj)) ||
                    (!IsWrite && (!AreAllWritesIdentified ||
                                  !isa<Argument>(UnderlyingObj)) &&
                     !isIdentifiedObject(UnderlyingObj))) {
                //DEBUG(dbgs() << "LV: Found an unidentified " <<
                        //(IsWrite ?  "write" : "read" ) << " ptr:" << *UnderlyingObj <<
                        //"\n");
                IsRTCheckNeeded = (IsRTCheckNeeded ||
                        !isIdentifiedObject(UnderlyingObj) ||
                        !AreAllReadsIdentified);

                if (IsWrite)
                    AreAllWritesIdentified = false;
                if (!IsWrite)
                    AreAllReadsIdentified = false;
            }

            // If this is a write - check other reads and writes for conflicts.  If
            // this is a read only check other writes for conflicts (but only if there
            // is no other write to the ptr - this is an optimization to catch "a[i] =
            // a[i] + " without having to do a dependence check).
            if ((IsWrite || IsReadOnlyPtr) && WriteObjects.count(UnderlyingObj))
                NeedDepCheck = true;

            if (IsWrite)
                WriteObjects.insert(UnderlyingObj);

            // Create sets of pointers connected by shared underlying objects.
            UnderlyingObjToAccessMap::iterator Prev =
                ObjToLastAccess.find(UnderlyingObj);
            if (Prev != ObjToLastAccess.end())
                DepCands.unionSets(Access, Prev->second);

            ObjToLastAccess[UnderlyingObj] = Access;
        }

        if (NeedDepCheck)
            CheckDeps.insert(Access);
    }
}

namespace {

class MemoryDepChecker {
public:
    typedef PointerIntPair<Value *, 1, bool> MemAccessInfo;
    typedef SmallPtrSet<MemAccessInfo, 8> MemAccessInfoSet;

    MemoryDepChecker(ScalarEvolution *Se, DataLayout *Dl, const Loop *L) :
        mSCEV(Se), mDataLayout(Dl), InnermostLoop(L), AccessIdx(0) {}

    /// \brief Register the location (instructions are given increasing numbers)
    /// of a write access.
    void addAccess(StoreInst *SI) {
        Value *Ptr = SI->getPointerOperand();
        Accesses[MemAccessInfo(Ptr, true)].push_back(AccessIdx);
        InstMap.push_back(SI);
        ++AccessIdx;
    }

    /// \brief Register the location (instructions are given increasing numbers)
    /// of a write access.
    void addAccess(LoadInst *LI) {
        Value *Ptr = LI->getPointerOperand();
        Accesses[MemAccessInfo(Ptr, false)].push_back(AccessIdx);
        InstMap.push_back(LI);
        ++AccessIdx;
    }

    /// \brief Check whether the dependencies between the accesses are safe.
    ///
    /// Only checks sets with elements in \p CheckDeps.
    bool areDepsSafe(AccessAnalysis::DepCandidates &AccessSets,
            MemAccessInfoSet &CheckDeps);

    /// \brief The maximum number of bytes of a vector register we can vectorize
    /// the accesses safely with.
    unsigned getMaxSafeDepDistBytes() { return MaxSafeDepDistBytes; }

private:
    ScalarEvolution *mSCEV;
    DataLayout *mDataLayout;
    const Loop *InnermostLoop;

    /// \brief Maps access locations (ptr, read/write) to program order.
    DenseMap<MemAccessInfo, std::vector<unsigned> > Accesses;

    /// \brief Memory access instructions in program order.
    SmallVector<Instruction *, 16> InstMap;

    /// \brief The program order index to be used for the next instruction.
    unsigned AccessIdx;

    // We can access this many bytes in parallel safely.
    unsigned MaxSafeDepDistBytes;

    /// \brief Check whether there is a plausible dependence between the two
    /// accesses.
    ///
    /// Access \p A must happen before \p B in program order. The two indices
    /// identify the index into the program order map.
    ///
    /// This function checks  whether there is a plausible dependence (or the
    /// absence of such can't be proved) between the two accesses. If there is a
    /// plausible dependence but the dependence distance is bigger than one
    /// element access it records this distance in \p MaxSafeDepDistBytes (if this
    /// distance is smaller than any other distance encountered so far).
    /// Otherwise, this function returns true signaling a possible dependence.
    bool isDependent(const MemAccessInfo &A, unsigned AIdx,
            const MemAccessInfo &B, unsigned BIdx);

    /// \brief Check whether the data dependence could prevent store-load
    /// forwarding.
    bool couldPreventStoreLoadForward(unsigned Distance, unsigned TypeByteSize);
};

} // unnamed namespace

static bool isInBoundsGep(Value *Ptr) {
    if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(Ptr))
        return GEP->isInBounds();
    return false;
}

/// \brief Check whether the access through \p Ptr has a constant stride.
static int isStridedPtr(ScalarEvolution *SE, DataLayout *DL, Value *Ptr,
        const Loop *Lp) {
    const Type *Ty = Ptr->getType();
    assert(Ty->isPointerTy() && "Unexpected non ptr");

    // Make sure that the pointer does not point to aggregate types.
    const PointerType *PtrTy = cast<PointerType>(Ty);
    if (PtrTy->getElementType()->isAggregateType()) {
        //DEBUG(dbgs() << "LV: Bad stride - Not a pointer to a scalar type" << *Ptr <<
                //"\n");
        return 0;
    }

    const SCEV *PtrScev = SE->getSCEV(Ptr);
    const SCEVAddRecExpr *AR = dyn_cast<SCEVAddRecExpr>(PtrScev);
    if (!AR) {
        //DEBUG(dbgs() << "LV: Bad stride - Not an AddRecExpr pointer "
                //<< *Ptr << " SCEV: " << *PtrScev << "\n");
        return 0;
    }

    // The accesss function must stride over the innermost loop.
    if (Lp != AR->getLoop()) {
        //DEBUG(dbgs() << "LV: Bad stride - Not striding over innermost loop " <<
                //*Ptr << " SCEV: " << *PtrScev << "\n");
    }

    // The address calculation must not wrap. Otherwise, a dependence could be
    // inverted.
    // An inbounds getelementptr that is a AddRec with a unit stride
    // cannot wrap per definition. The unit stride requirement is checked later.
    // An getelementptr without an inbounds attribute and unit stride would have
    // to access the pointer value "0" which is undefined behavior in address
    // space 0, therefore we can also vectorize this case.
    bool IsInBoundsGEP = isInBoundsGep(Ptr);
    bool IsNoWrapAddRec = AR->getNoWrapFlags(SCEV::NoWrapMask);
    bool IsInAddressSpaceZero = PtrTy->getAddressSpace() == 0;
    if (!IsNoWrapAddRec && !IsInBoundsGEP && !IsInAddressSpaceZero) {
        //DEBUG(dbgs() << "LV: Bad stride - Pointer may wrap in the address space "
                //<< *Ptr << " SCEV: " << *PtrScev << "\n");
        return 0;
    }

    // Check the step is constant.
    const SCEV *Step = AR->getStepRecurrence(*SE);

    // Calculate the pointer stride and check if it is consecutive.
    const SCEVConstant *C = dyn_cast<SCEVConstant>(Step);
    if (!C) {
        //DEBUG(dbgs() << "LV: Bad stride - Not a constant strided " << *Ptr <<
                //" SCEV: " << *PtrScev << "\n");
        return 0;
    }

    int64_t Size = DL->getTypeAllocSize(PtrTy->getElementType());
    const APInt &APStepVal = C->getValue()->getValue();

    // Huge step value - give up.
    if (APStepVal.getBitWidth() > 64)
        return 0;

    int64_t StepVal = APStepVal.getSExtValue();

    // Strided access.
    int64_t Stride = StepVal / Size;
    int64_t Rem = StepVal % Size;
    if (Rem)
        return 0;

    // If the SCEV could wrap but we have an inbounds gep with a unit stride we
    // know we can't "wrap around the address space". In case of address space
    // zero we know that this won't happen without triggering undefined behavior.
    if (!IsNoWrapAddRec && (IsInBoundsGEP || IsInAddressSpaceZero) &&
            Stride != 1 && Stride != -1)
        return 0;

    return Stride;
}

bool MemoryDepChecker::couldPreventStoreLoadForward(unsigned Distance,
        unsigned TypeByteSize) {
    // If loads occur at a distance that is not a multiple of a feasible vector
    // factor store-load forwarding does not take place.
    // Positive dependences might cause troubles because vectorizing them might
    // prevent store-load forwarding making vectorized code run a lot slower.
    //   a[i] = a[i-3] ^ a[i-8];
    //   The stores to a[i:i+1] don't align with the stores to a[i-3:i-2] and
    //   hence on your typical architecture store-load forwarding does not take
    //   place. Vectorizing in such cases does not make sense.
    // Store-load forwarding distance.
    const unsigned NumCyclesForStoreLoadThroughMemory = 8*TypeByteSize;
    // Maximum vector factor.
#define MaxVectorWidth 64
    unsigned MaxVFWithoutSLForwardIssues = MaxVectorWidth*TypeByteSize;
    if(MaxSafeDepDistBytes < MaxVFWithoutSLForwardIssues)
        MaxVFWithoutSLForwardIssues = MaxSafeDepDistBytes;

    for (unsigned vf = 2*TypeByteSize; vf <= MaxVFWithoutSLForwardIssues;
            vf *= 2) {
        if (Distance % vf && Distance / vf < NumCyclesForStoreLoadThroughMemory) {
            MaxVFWithoutSLForwardIssues = (vf >>=1);
            break;
        }
    }

    if (MaxVFWithoutSLForwardIssues< 2*TypeByteSize) {
        //DEBUG(dbgs() << "LV: Distance " << Distance <<
                //" that could cause a store-load forwarding conflict\n");
        return true;
    }

    if (MaxVFWithoutSLForwardIssues < MaxSafeDepDistBytes &&
            MaxVFWithoutSLForwardIssues != MaxVectorWidth*TypeByteSize)
        MaxSafeDepDistBytes = MaxVFWithoutSLForwardIssues;
    return false;
}

bool MemoryDepChecker::isDependent(const MemAccessInfo &A, unsigned AIdx,
        const MemAccessInfo &B, unsigned BIdx) {
    assert (AIdx < BIdx && "Must pass arguments in program order");

    Value *APtr = A.getPointer();
    Value *BPtr = B.getPointer();
    bool AIsWrite = A.getInt();
    bool BIsWrite = B.getInt();

    // Two reads are independent.
    if (!AIsWrite && !BIsWrite)
        return false;

    const SCEV *AScev = mSCEV->getSCEV(APtr);
    const SCEV *BScev = mSCEV->getSCEV(BPtr);

    int StrideAPtr = isStridedPtr(mSCEV, mDataLayout, APtr, InnermostLoop);
    int StrideBPtr = isStridedPtr(mSCEV, mDataLayout, BPtr, InnermostLoop);

    const SCEV *Src = AScev;
    const SCEV *Sink = BScev;

    // If the induction step is negative we have to invert source and sink of the
    // dependence.
    if (StrideAPtr < 0) {
        //Src = BScev;
        //Sink = AScev;
        std::swap(APtr, BPtr);
        std::swap(Src, Sink);
        std::swap(AIsWrite, BIsWrite);
        std::swap(AIdx, BIdx);
        std::swap(StrideAPtr, StrideBPtr);
    }

    const SCEV *Dist = mSCEV->getMinusSCEV(Sink, Src);

    //DEBUG(dbgs() << "LV: Src Scev: " << *Src << "Sink Scev: " << *Sink
            //<< "(Induction step: " << StrideAPtr <<  ")\n");
    //DEBUG(dbgs() << "LV: Distance for " << *InstMap[AIdx] << " to "
            //<< *InstMap[BIdx] << ": " << *Dist << "\n");

    // Need consecutive accesses. We don't want to vectorize
    // "A[B[i]] += ..." and similar code or pointer arithmetic that could wrap in
    // the address space.
    if (!StrideAPtr || !StrideBPtr || StrideAPtr != StrideBPtr){
        //DEBUG(dbgs() << "Non-consecutive pointer access\n");
        return true;
    }

    const SCEVConstant *C = dyn_cast<SCEVConstant>(Dist);
    if (!C) {
        //DEBUG(dbgs() << "LV: Dependence because of non constant distance\n");
        return true;
    }

    Type *ATy = APtr->getType()->getPointerElementType();
    Type *BTy = BPtr->getType()->getPointerElementType();
    unsigned TypeByteSize = mDataLayout->getTypeAllocSize(ATy);

    // Negative distances are not plausible dependencies.
    const APInt &Val = C->getValue()->getValue();
    if (Val.isNegative()) {
        bool IsTrueDataDependence = (AIsWrite && !BIsWrite);
        if (IsTrueDataDependence &&
                (couldPreventStoreLoadForward(Val.abs().getZExtValue(), TypeByteSize) ||
                 ATy != BTy))
            return true;

        //DEBUG(dbgs() << "LV: Dependence is negative: NoDep\n");
        return false;
    }

    // Write to the same location with the same size.
    // Could be improved to assert type sizes are the same (i32 == float, etc).
    if (Val == 0) {
        if (ATy == BTy)
            return false;
        //DEBUG(dbgs() << "LV: Zero dependence difference but different types");
        return true;
    }

    assert(Val.isStrictlyPositive() && "Expect a positive value");

    // Positive distance bigger than max vectorization factor.
    if (ATy != BTy) {
        //DEBUG(dbgs() <<
                //"LV: ReadWrite-Write positive dependency with different types");
        return false;
    }

    unsigned Distance = (unsigned) Val.getZExtValue();

    // The distance must be bigger than the size needed for a vectorized version
    // of the operation and the size of the vectorized operation must not be
    // bigger than the currrent maximum size.
    if (Distance < 2*TypeByteSize ||
            2*TypeByteSize > MaxSafeDepDistBytes) {
        //DEBUG(dbgs() << "LV: Failure because of Positive distance "
                //<< Val.getSExtValue() << "\n");
        return true;
    }

    MaxSafeDepDistBytes = Distance < MaxSafeDepDistBytes ?
        Distance : MaxSafeDepDistBytes;

    bool IsTrueDataDependence = (!AIsWrite && BIsWrite);
    if (IsTrueDataDependence &&
            couldPreventStoreLoadForward(Distance, TypeByteSize))
        return true;

    //DEBUG(dbgs() << "LV: Positive distance " << Val.getSExtValue() <<
            //" with max VF=" << MaxSafeDepDistBytes/TypeByteSize << "\n");

    return false;
}

bool
MemoryDepChecker::areDepsSafe(AccessAnalysis::DepCandidates &AccessSets,
        MemAccessInfoSet &CheckDeps) {

    MaxSafeDepDistBytes = -1U;
    while (!CheckDeps.empty()) {
        MemAccessInfo CurAccess = *CheckDeps.begin();

        // Get the relevant memory access set.
        EquivalenceClasses<MemAccessInfo>::iterator I =
            AccessSets.findValue(AccessSets.getLeaderValue(CurAccess));

        // Check accesses within this set.
        EquivalenceClasses<MemAccessInfo>::member_iterator AI, AE;
        AI = AccessSets.member_begin(I), AE = AccessSets.member_end();

        // Check every access pair.
        while (AI != AE) {
            CheckDeps.erase(*AI);
            EquivalenceClasses<MemAccessInfo>::member_iterator OI = llvm::next(AI);
            while (OI != AE) {
                // Check every accessing instruction pair in program order.
                for (std::vector<unsigned>::iterator I1 = Accesses[*AI].begin(),
                        I1E = Accesses[*AI].end(); I1 != I1E; ++I1)
                    for (std::vector<unsigned>::iterator I2 = Accesses[*OI].begin(),
                            I2E = Accesses[*OI].end(); I2 != I2E; ++I2) {
                        if (*I1 < *I2 && isDependent(*AI, *I1, *OI, *I2))
                            return false;
                        if (*I2 < *I1 && isDependent(*OI, *I2, *AI, *I1))
                            return false;
                    }
                ++OI;
            }
            AI++;
        }
    }
    return true;
}

static Intrinsic::ID
getIntrinsicIDForCall(CallInst *CI, const TargetLibraryInfo *TLI) {
    // If we have an intrinsic call, check if it is trivially vectorizable.
    if (IntrinsicInst *II = dyn_cast<IntrinsicInst>(CI)) {
        switch (II->getIntrinsicID()) {
            case Intrinsic::sqrt:
            case Intrinsic::sin:
            case Intrinsic::cos:
            case Intrinsic::exp:
            case Intrinsic::exp2:
            case Intrinsic::log:
            case Intrinsic::log10:
            case Intrinsic::log2:
            case Intrinsic::fabs:
            case Intrinsic::floor:
            case Intrinsic::ceil:
            case Intrinsic::trunc:
            case Intrinsic::rint:
            case Intrinsic::nearbyint:
            case Intrinsic::pow:
            case Intrinsic::fma:
            case Intrinsic::fmuladd:
                return II->getIntrinsicID();
            default:
                return Intrinsic::not_intrinsic;
        }
    }

    if (!TLI)
        return Intrinsic::not_intrinsic;

    LibFunc::Func Func;
    Function *F = CI->getCalledFunction();
    // We're going to make assumptions on the semantics of the functions, check
    // that the target knows that it's available in this environment.
    if (!F || !TLI->getLibFunc(F->getName(), Func))
        return Intrinsic::not_intrinsic;

    // Otherwise check if we have a call to a function that can be turned into a
    // vector intrinsic.
    switch (Func) {
        default:
            break;
        case LibFunc::sin:
        case LibFunc::sinf:
        case LibFunc::sinl:
            return Intrinsic::sin;
        case LibFunc::cos:
        case LibFunc::cosf:
        case LibFunc::cosl:
            return Intrinsic::cos;
        case LibFunc::exp:
        case LibFunc::expf:
        case LibFunc::expl:
            return Intrinsic::exp;
        case LibFunc::exp2:
        case LibFunc::exp2f:
        case LibFunc::exp2l:
            return Intrinsic::exp2;
        case LibFunc::log:
        case LibFunc::logf:
        case LibFunc::logl:
            return Intrinsic::log;
        case LibFunc::log10:
        case LibFunc::log10f:
        case LibFunc::log10l:
            return Intrinsic::log10;
        case LibFunc::log2:
        case LibFunc::log2f:
        case LibFunc::log2l:
            return Intrinsic::log2;
        case LibFunc::fabs:
        case LibFunc::fabsf:
        case LibFunc::fabsl:
            return Intrinsic::fabs;
        case LibFunc::floor:
        case LibFunc::floorf:
        case LibFunc::floorl:
            return Intrinsic::floor;
        case LibFunc::ceil:
        case LibFunc::ceilf:
        case LibFunc::ceill:
            return Intrinsic::ceil;
        case LibFunc::trunc:
        case LibFunc::truncf:
        case LibFunc::truncl:
            return Intrinsic::trunc;
        case LibFunc::rint:
        case LibFunc::rintf:
        case LibFunc::rintl:
            return Intrinsic::rint;
        case LibFunc::nearbyint:
        case LibFunc::nearbyintf:
        case LibFunc::nearbyintl:
            return Intrinsic::nearbyint;
        case LibFunc::pow:
        case LibFunc::powf:
        case LibFunc::powl:
            return Intrinsic::pow;
    }

    return Intrinsic::not_intrinsic;
}

// Adopted from LoopVectorize.cpp (2013-08-06)
bool
LoopAnalyzer::canVectorizeMemory(Loop* TheLoop)
{
    assert (TheLoop);
    typedef SmallVector<Value*, 16> ValueVector;
    typedef SmallPtrSet<Value*, 16> ValueSet;

    // Holds the Load and Store *instructions*.
    ValueVector Loads;
    ValueVector Stores;

    // Holds all the different accesses in the loop.
    unsigned NumReads = 0;
    unsigned NumReadWrites = 0;

    mPtrRtCheck.Pointers.clear();
    mPtrRtCheck.Starts.clear();
    mPtrRtCheck.Ends.clear();
    mPtrRtCheck.Need = false;

    const bool IsAnnotatedParallel = TheLoop->isAnnotatedParallel();
    MemoryDepChecker DepChecker(mSCEV, mDataLayout, TheLoop);

    // For each block.
    for (Loop::block_iterator bb = TheLoop->block_begin(),
            be = TheLoop->block_end(); bb != be; ++bb) {

        // Scan the BB and collect legal loads and stores.
        for (BasicBlock::iterator it = (*bb)->begin(), e = (*bb)->end(); it != e;
                ++it) {

            // If this is a load, save it. If this instruction can read from memory
            // but is not a load, then we quit. Notice that we don't handle function
            // calls that read or write.
            if (it->mayReadFromMemory()) {
                // Many math library functions read the rounding mode. We will only
                // vectorize a loop if it contains known function calls that don't set
                // the flag. Therefore, it is safe to ignore this read from memory.
                CallInst *Call = dyn_cast<CallInst>(it);
                if (Call && getIntrinsicIDForCall(Call, mTLI))
                    continue;

                LoadInst *Ld = dyn_cast<LoadInst>(it);
                if (!Ld) return false;
                if (!Ld->isSimple() && !IsAnnotatedParallel) {
                    //DEBUG(dbgs() << "LV: Found a non-simple load.\n");
                    return false;
                }
                Loads.push_back(Ld);
                DepChecker.addAccess(Ld);
                continue;
            }

            // Save 'store' instructions. Abort if other instructions write to memory.
            if (it->mayWriteToMemory()) {
                StoreInst *St = dyn_cast<StoreInst>(it);
                if (!St) return false;
                if (!St->isSimple() && !IsAnnotatedParallel) {
                    //DEBUG(dbgs() << "LV: Found a non-simple store.\n");
                    return false;
                }
                Stores.push_back(St);
                DepChecker.addAccess(St);
            }
        } // next instr.
    } // next block.

    // Now we have two lists that hold the loads and the stores.
    // Next, we find the pointers that they use.

    // Check if we see any stores. If there are no stores, then we don't
    // care if the pointers are *restrict*.
    if (!Stores.size()) {
        //DEBUG(dbgs() << "LV: Found a read-only loop!\n");
        return true;
    }

    AccessAnalysis::DepCandidates DependentAccesses;
    AccessAnalysis Accesses(mDataLayout, DependentAccesses);

    // Holds the analyzed pointers. We don't want to call GetUnderlyingObjects
    // multiple times on the same object. If the ptr is accessed twice, once
    // for read and once for write, it will only appear once (on the write
    // list). This is okay, since we are going to check for conflicts between
    // writes and between reads and writes, but not between reads and reads.
    ValueSet Seen;

    ValueVector::iterator I, IE;
    for (I = Stores.begin(), IE = Stores.end(); I != IE; ++I) {
        StoreInst *ST = cast<StoreInst>(*I);
        Value* Ptr = ST->getPointerOperand();

        //if (isUniform(Ptr)) {
            ////DEBUG(dbgs() << "LV: We don't allow storing to uniform addresses\n");
            //return false;
        //}

        // If we did *not* see this pointer before, insert it to  the read-write
        // list. At this phase it is only a 'write' list.
        if (Seen.insert(Ptr)) {
            ++NumReadWrites;
            Accesses.addStore(Ptr);
        }
    }

    if (IsAnnotatedParallel) {
        //DEBUG(dbgs()
                //<< "LV: A loop annotated parallel, ignore memory dependency "
                //<< "checks.\n");
        return true;
    }

    SmallPtrSet<Value *, 16> ReadOnlyPtr;
    for (I = Loads.begin(), IE = Loads.end(); I != IE; ++I) {
        LoadInst *LD = cast<LoadInst>(*I);
        Value* Ptr = LD->getPointerOperand();
        // If we did *not* see this pointer before, insert it to the
        // read list. If we *did* see it before, then it is already in
        // the read-write list. This allows us to vectorize expressions
        // such as A[i] += x;  Because the address of A[i] is a read-write
        // pointer. This only works if the index of A[i] is consecutive.
        // If the address of i is unknown (for example A[B[i]]) then we may
        // read a few words, modify, and write a few words, and some of the
        // words may be written to the same address.
        bool IsReadOnlyPtr = false;
        if (Seen.insert(Ptr) || !isStridedPtr(mSCEV, mDataLayout, Ptr, TheLoop)) {
            ++NumReads;
            IsReadOnlyPtr = true;
        }
        Accesses.addLoad(Ptr, IsReadOnlyPtr);
    }

    // If we write (or read-write) to a single destination and there are no
    // other reads in this loop then is it safe to vectorize.
    if (NumReadWrites == 1 && NumReads == 0) {
        //DEBUG(dbgs() << "LV: Found a write-only loop!\n");
        return true;
    }

    // Build dependence sets and check whether we need a runtime pointer bounds
    // check.
    Accesses.buildDependenceSets();
    bool NeedRTCheck = Accesses.isRTCheckNeeded();

    // Find pointers with computable bounds. We are going to use this information
    // to place a runtime bound check.
    unsigned NumComparisons = 0;
    bool CanDoRT = false;
    if (NeedRTCheck)
        CanDoRT = Accesses.canCheckPtrAtRT(mPtrRtCheck, NumComparisons, mSCEV, TheLoop);


    //DEBUG(dbgs() << "LV: We need to do " << NumComparisons <<
            //" pointer comparisons.\n");

    // If we only have one set of dependences to check pointers among we don't
    // need a runtime check.
    if (NumComparisons == 0 && NeedRTCheck)
        NeedRTCheck = false;

    // Check that we did not collect too many pointers or found a unsizeable
    // pointer.
#define RuntimeMemoryCheckThreshold 8
    if (!CanDoRT || NumComparisons > RuntimeMemoryCheckThreshold) {
        mPtrRtCheck.reset();
        CanDoRT = false;
    }

    if (CanDoRT) {
        //DEBUG(dbgs() << "LV: We can perform a memory runtime check if needed.\n");
    }

    if (NeedRTCheck && !CanDoRT) {
        //DEBUG(dbgs() << "LV: We can't vectorize because we can't find " <<
                //"the array bounds.\n");
        mPtrRtCheck.reset();
        return false;
    }

    mPtrRtCheck.Need = NeedRTCheck;

    bool CanVecMem = true;
    unsigned MaxSafeDepDistBytes = -1U;
    if (Accesses.isDependencyCheckNeeded()) {
        //DEBUG(dbgs() << "LV: Checking memory dependencies\n");
        CanVecMem = DepChecker.areDepsSafe(DependentAccesses,
                Accesses.getDependenciesToCheck());
        MaxSafeDepDistBytes = DepChecker.getMaxSafeDepDistBytes();
    }

    //DEBUG(dbgs() << "LV: We "<< (NeedRTCheck ? "" : "don't") <<
            //" need a runtime memory check.\n");

    return CanVecMem;
}

LoopAnalyzer::LoopType
LoopAnalyzer::analyzeLoop(Loop*        loop,
                          Loop*        parentLoop,
                          raw_ostream& out)
{
    assert (loop);

    const bool hasNestedLoops = loop->begin() != loop->end();

    bool childrenAreVectorizable = true;
    for (Loop::iterator SL=loop->begin(), SLE=loop->end(); SL!=SLE; ++SL)
    {
        const LoopType lt = analyzeLoop(*SL, loop, out);
        childrenAreVectorizable &= lt != NOT_VECTORIZABLE;
        printLoopType(lt, **SL, out);
    }

    BasicBlock* preheaderBB = loop->getLoopPreheader();
    BasicBlock* headerBB    = loop->getHeader();
    BasicBlock* latchBB     = loop->getLoopLatch();
    BasicBlock* exitBB      = loop->getExitBlock();
    BasicBlock* exitingBB   = loop->getExitingBlock();

    out << "\nanalyzing loop with header: '" << headerBB->getName() << "'\n";

    if (parentLoop)
    {
        out << "  is nested in loop with header: '"
            << parentLoop->getHeader()->getName() << "'\n";
    }
    else
    {
        out << "  is outer loop.\n";
    }

    if (hasNestedLoops)
    {
        out << "  has nested loop(s).\n";
    }

    bool isVectorizable = true;

    if (!preheaderBB || !headerBB || !latchBB)
    {
        out << "  is not simplified!\n";
        isVectorizable = false;
    }

    if (!loop->isLoopSimplifyForm())
    {
        out << "  is not simplified!\n";
        isVectorizable = false;
    }

    if (!loop->isLCSSAForm(*mDomTree))
    {
        out << "  is not in LCSSA form!\n";
        isVectorizable = false;
    }

    if (loop->getNumBackEdges() > 1)
    {
        out << "  has bad number of back edges: " << loop->getNumBackEdges() << "\n";
        isVectorizable = false;
    }

    if (!exitBB)
    {
        out << "  has multiple exits!\n";
        isVectorizable = false;
    }

    if (exitingBB)
    {
        const SCEV* ExitCount = mSCEV->getExitCount(loop, exitingBB);
        if (ExitCount == mSCEV->getCouldNotCompute())
        {
            out << "  has unknown exit count!\n";
            isVectorizable = false;
        }
        else
        {
            out << "  has exit count: " << *ExitCount << "\n";
        }
    }

    // TODO: Do we really need an induction variable?
    // Adopted from LLVM Loop Vectorizer.
    PHINode* indVarPhi = loop->getCanonicalInductionVariable();
    for (BasicBlock::iterator I=headerBB->begin(), IE=headerBB->end(); I!=IE; ++I)
    {
        if (!isa<PHINode>(I)) break;
        PHINode* phi = cast<PHINode>(I);
        Type* PhiTy = phi->getType();

        // We only handle integer and pointer induction variables.
        if (!PhiTy->isIntegerTy() && !PhiTy->isPointerTy()) continue;

        // Check that the PHI is consecutive.
        const SCEV* PhiScev = mSCEV->getSCEV(phi);
        const SCEVAddRecExpr* AR = dyn_cast<SCEVAddRecExpr>(PhiScev);
        if (!AR) continue;

        const SCEV* Step = AR->getStepRecurrence(*mSCEV);

        // Integer inductions need to have a stride of one.
        if (PhiTy->isIntegerTy())
        {
            if (Step->isOne() || Step->isAllOnesValue())
            {
                if (indVarPhi)
                {
                    if (indVarPhi != phi)
                    {
                        out << "  has additional induction variable: " << *phi << "\n";
                    }
                }
                else
                {
                    out << "  induction variable: " << *phi << "\n";
                    indVarPhi = phi;
                }
                break;
            }
            continue;
        }

        // Calculate the pointer stride and check if it is consecutive.
        const SCEVConstant* C = dyn_cast<SCEVConstant>(Step);
        if (!C) continue;

        assert(PhiTy->isPointerTy() && "The PHI must be a pointer");
        uint64_t Size = mDataLayout->getTypeAllocSize(PhiTy->getPointerElementType());
        if (C->getValue()->equalsInt(Size) || C->getValue()->equalsInt(0 - Size))
        {
            if (indVarPhi)
            {
                if (indVarPhi != phi) out << "  has additional induction variable: " << *phi << "\n";
            }
            else
            {
                out << "  induction variable: " << *phi << "\n";
                indVarPhi = phi;
            }
            break;
        }
    }

    if (!indVarPhi)
    {
        out << "  has no usable induction variable for vectorization!\n";
        isVectorizable = false;
    }

    // We ignore the rest of the analysis if the loop is already known not to be vectorizable.
    // The constraints up to this point are valid for all possible vectorization approaches.
    if (!isVectorizable) return NOT_VECTORIZABLE;

    // For this analysis, take memory dependencies into account to prevent false positives.
    if (!canVectorizeMemory(loop))
    {
        out << "  has non-vectorizable memory access operations!\n";
        return NOT_VECTORIZABLE;
    }

    RedVarVecType redVars;
    collectReductionVariables(redVars, indVarPhi, *loop, *mDomTree, out);

    bool rIntermResUsedOutsideLoop = false;
    bool rMultiOpSame = false;
    bool rMultiOpNonSame = false;
    bool rNonCAUpdateOp = false;
    bool rDependsOnControlFlow = false;

    // While testing each reduction variable, we also collect *all* operations
    // that belong to any reduction SCC.
    SmallPtrSet<Instruction*, 16> reductionOps;
    for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
    {
        ReductionVariable& redVar = **it;
        PHINode*      P = redVar.mPhi;
        Value*        S = redVar.mStartVal;
        RedUpMapType* U = redVar.mUpdates;
        PHINode*      R = redVar.mResultUser; // Can be NULL.

        out << "  has loop-carried dependence:\n";
        out << "    phi             : " << *P << "\n";
        out << "    start value     : " << *S << "\n";
        if (R) out << "    has out-of-loop user: " << *R << "\n";
        else out << "    has no out-of-loop user.\n";

        if (U->size() > 1)
        {
            out << "    has multiple updates!\n";
        }

        for (RedUpMapType::const_iterator it=U->begin(), E=U->end(); it!=E; ++it)
        {
            const ReductionUpdate& redUp = *it->second;
            out << "    update operation: " << *redUp.mOperation << "\n";

            Loop* updateOpLoop = mLoopInfo->getLoopFor(redUp.mOperation->getParent());
            if (loop != updateOpLoop)
            {
                out << "      is inside inner loop with header: '"
                    << updateOpLoop->getHeader()->getName() << "'\n";
            }

            if (isCAUpdateOp(redUp.mOperation->getOpcode()))
            {
                out << "      is associative/commutative operation!\n";
            }
            else
            {
                out << "      is non-associative/non-commutative operation!\n";
                rNonCAUpdateOp = true;
            }

#if 0
            const SetVector<Value*>& otherOperands = *redUp.mOtherOperands;
            for (SetVector<Value*>::const_iterator it2=otherOperands.begin(),
                E2=otherOperands.end(); it2!=E2; ++it2)
            {
                Value* operand = *it2;
            }
#endif

            if (dependsOnControlFlow(redUp.mOperation, *loop, *mDomTree))
            {
                out << "    depends on control flow!\n";
                rDependsOnControlFlow = true;
            }

            const SetVector<Instruction*>& resultUsers = *redUp.mResultUsers;
            for (SetVector<Instruction*>::const_iterator it2=resultUsers.begin(),
                E2=resultUsers.end(); it2!=E2; ++it2)
            {
                Instruction* user = *it2;
                out << "      result user: " << *user << "\n";
                if (!loop->contains(user->getParent()))
                {
                    out << "        is not part of loop!\n";
                    rIntermResUsedOutsideLoop = true;
                }
            }

            reductionOps.insert(redUp.mOperation);
        }

        if (U->size() > 1)
        {
            if (redVar.mCommonOpcode == 0)
            {
                out << "    has multiple update operations of different types!\n";
                rMultiOpNonSame = true;
            }
            else
            {
                out << "    has multiple update operations of same type!\n";
                rMultiOpSame = true;
            }
        }

        reductionOps.insert(redVar.mPhi);
    }

    // Must not have non-reduction values with users outside the loop.
    for (BasicBlock::iterator I=exitBB->begin(), IE=exitBB->end(); I!=IE; ++I)
    {
        if (!isa<PHINode>(I)) break;
        PHINode* phi = cast<PHINode>(I);

        bool isReductionOpUser = false;
        for (PHINode::op_iterator O=phi->op_begin(), OE=phi->op_end(); O!=OE; ++O)
        {
            if (!isa<Instruction>(*O)) continue;
            Instruction* opInst = cast<Instruction>(*O);
            if (!reductionOps.count(opInst)) continue;
            isReductionOpUser = true;
            break;
        }

        if (!isReductionOpUser)
        {
            out << "  has 'output' value that is not connected to any reduction!\n";
            return NOT_VECTORIZABLE;
        }
    }

    if (rIntermResUsedOutsideLoop)
    {
        out << "  has at least one reduction with at least one intermediate result that is used outside loop!\n";
        return NOT_VECTORIZABLE; // TODO: Is that so?
    }

    // Check which type of loop we have.
    // Defaults are "trivial" (no loop-carried dependencies), or "common" (simple reductions).
    LoopType loopType = redVars.empty() ? VECTORIZABLE_TRIVIAL : VECTORIZABLE_COMMON;

    if (rMultiOpSame)
    {
        out << "  has at least one reduction with multiple update operations of same type!\n";
        loopType = VECTORIZABLE_MULTIOP;
    }

    if (rMultiOpNonSame)
    {
        out << "  has at least one reduction with multiple update operations of different type!\n";
        loopType = VECTORIZABLE_NOISE;
    }

    if (rNonCAUpdateOp)
    {
        out << "  has at least one reduction with at least one non-associative/non-commutative update operation!\n";
        loopType = VECTORIZABLE_NOISE;
    }

    if (rDependsOnControlFlow)
    {
        out << "  has at least one reduction with at least one update operation that depends on control flow!\n";
        loopType = VECTORIZABLE_NOISE;
    }

    // Dump a single line with all information.
    out << "  summary: "
        << loopTypeToString(loopType)
        << (rMultiOpSame ? " MULTI_OP_SAME" : "")
        << (rMultiOpNonSame ? " MULTI_OP_NON_SAME" : "")
        << (rNonCAUpdateOp ? " NON_CA_UPDATE" : "")
        << (rDependsOnControlFlow ? " CF_DEP" : "")
        << " IDENTIFIER=" << preheaderBB->getParent()->getParent()->getModuleIdentifier()
        << "#" << preheaderBB->getParent()->getName()
        << "\n";

    return loopType;
}

} // namespace llvm
