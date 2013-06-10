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

#include <iostream>

#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"

#include "llvm/ADT/MapVector.h"

using namespace llvm;

namespace llvm {

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

LoopAnalysis::LoopAnalysis(Module* M) : Mod(M) {}
LoopAnalysis::~LoopAnalysis() {}

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
    default:
    {
      assert (false && "should never happen!");
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
    default: assert (false && "should never happen"); return "VECTORIZABLE_UNKNOWN";
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
            assert (swI->findCaseDest(succBB));
            otherOperands.push_back(swI->findCaseDest(succBB));
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
    BasicBlock* exitBB      = loop.getUniqueExitBlock();

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
    BasicBlock* exitBB      = loop->getUniqueExitBlock();
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

    // We ignore memory dependencies anyway!
    // TODO: For this analysis, though, we should take them into account
    //       to prevent false positives.
    //if (!loop->isAnnotatedParallel()) { /* Check loads and stores. */ }

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
