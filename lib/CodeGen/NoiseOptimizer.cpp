//===--- NoiseOptimizer.cpp - Noise Optimizations --------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// The optimizer for noise functions
//
//===----------------------------------------------------------------------===//

#include "NoiseOptimizer.h"
#include "CGNoise.h"
#include "NoiseOptimization.h"

#ifdef COMPILE_NOISE_WFV_WRAPPER
#include "NoiseWFVWrapper.h"
#endif

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

//#define NOISE_ANALYZE_REDUCTIONS

#ifdef NOISE_ANALYZE_REDUCTIONS
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#endif

using namespace llvm;

namespace {

Function* GetNoiseFunction(const MDNode* mdNode)
{
    assert (mdNode->getNumOperands() == 2);
    // First operand is the function.
    assert (isa<Function>(mdNode->getOperand(0)));
    return cast<Function>(mdNode->getOperand(0));
}

llvm::MDNode* GetNoiseOptDesc(const MDNode* mdNode)
{
    assert (mdNode->getNumOperands() == 2);
    // Second operand is the noise-optimization metadata.
    assert (isa<llvm::MDNode>(mdNode->getOperand(1)));
    return cast<llvm::MDNode>(mdNode->getOperand(1));
}

} // unnamed namespace

namespace llvm {

// Collects all blocks between the block "block" and the end block "endBB"
// TODO: There's functionality inside LLVM for this: llvm::Region
template<unsigned SetSize>
void collectBlocks(BasicBlock* block,
                   BasicBlock* endBB,
                   SmallPtrSet<BasicBlock*, SetSize>& region)
{
  if (region.count(block)) return;
  region.insert(block);

  if (block == endBB) return;

  TerminatorInst* terminator = block->getTerminator();
  for (unsigned i=0, e=terminator->getNumSuccessors(); i<e; ++i)
  {
    collectBlocks<SetSize>(terminator->getSuccessor(i), endBB, region);
  }
}

void initializeNoiseExtractorPass(PassRegistry&);
void initializeNoiseInlinerPass(PassRegistry&);
void initializeNoiseSpecializerPass(PassRegistry&);
#ifdef NOISE_ANALYZE_REDUCTIONS
void initializeNoiseReductionAnalyzerPass(PassRegistry&);
#endif

struct NoiseExtractor : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid

  noise::NoiseFnInfoVecType* noiseFnInfoVec;
  NamedMDNode*               MD;
  SmallSet<Function*, 64>    createdFunctions;
  Module*                    Mod;
  LLVMContext*               Context;

  NoiseExtractor(noise::NoiseFnInfoVecType* noiseFuncInfoVec=0,
                 NamedMDNode*               mdNode=0)
  : FunctionPass(ID), noiseFnInfoVec(noiseFuncInfoVec), MD(mdNode) {
    initializeNoiseExtractorPass(*PassRegistry::getPassRegistry());
  }

  virtual ~NoiseExtractor()
  { }

  MDNode* getCompoundStmtNoiseMD(const BasicBlock& block)
  {
      return block.getTerminator()->getMetadata("noise_compound_stmt");
  }

  bool hasNoiseFunctionAttribute(const Function& function) const {
    for (unsigned i=0, e=MD->getNumOperands(); i<e; ++i) {
      MDNode* functionMDN = MD->getOperand(i);
      Function* noiseFn = GetNoiseFunction(functionMDN);
      if (noiseFn == &function) return true;
    }

    return false;
  }

  template<unsigned SetSize>
  bool resolveMarkers(BasicBlock*                        block,
                      SmallPtrSet<BasicBlock*, SetSize>& visitedBlocks,
                      const bool                         isTopLevel)
  {
    if (visitedBlocks.count(block)) return false;
    visitedBlocks.insert(block);

    MDNode* noiseMD = getCompoundStmtNoiseMD(*block);
    if (!noiseMD) return false;

    // Handle compound statement attributes.
    assert (isa<BasicBlock>(noiseMD->getOperand(0)));
    assert (isa<BasicBlock>(noiseMD->getOperand(1)));
    assert (isa<MDNode>(noiseMD->getOperand(2)));

    // Recurse into nested noise regions (if any).
    // To do so properly, we need to reconstruct the region after we
    // extracted a noise region and then start iterating again.
    BasicBlock* entryBB = cast<BasicBlock>(noiseMD->getOperand(0));
    BasicBlock* exitBB  = cast<BasicBlock>(noiseMD->getOperand(1));

    SmallPtrSet<BasicBlock*, SetSize> region;
    bool iterate = true;
    while (iterate)
    {
        iterate = false;
        region.clear();
        collectBlocks<SetSize>(entryBB, exitBB, region);

        for (typename SmallPtrSet<BasicBlock*, SetSize>::iterator it=region.begin(),
            E=region.end(); it!=E; ++it)
        {
            if (resolveMarkers<SetSize>(*it, visitedBlocks, false))
            {
                iterate = true;
                break;
            }
        }
    }

    // Create new function from the marked range.
    SmallVector<BasicBlock*, SetSize> regionVec(region.begin(), region.end());
    CodeExtractor extractor(regionVec);
    Function* extractedFn = extractor.extractCodeRegion();
    extractedFn->setName(extractedFn->getName()+".extracted");

    // Create new NoiseFnInfo object.
    assert (extractedFn->getNumUses() == 1 &&
            "There should be only one call to an extracted function");
    assert (isa<CallInst>(*extractedFn->use_begin()));
    CallInst* call = cast<CallInst>(*extractedFn->use_begin());
    noise::NoiseFnInfo* nfi = new noise::NoiseFnInfo(extractedFn, call, !isTopLevel);
    noiseFnInfoVec->push_back(nfi);

    //outs() << "extracted function: " << *extractedFn << "\n";
    //outs() << "source function: " << *call->getParent()->getParent() << "\n";

    // Create global (function) metadata for the new function from the statement attribute.
    assert(Mod);

    llvm::Value* params[] = { extractedFn, noiseMD->getOperand(2) };
    MD->addOperand(llvm::MDNode::get(*Context, llvm::ArrayRef<llvm::Value*>(params)));

    createdFunctions.insert(extractedFn);

    return true;
  }

  virtual bool runOnFunction(Function &F)
  {
    // If this was an extracted function, skip the extraction operation.
    if(createdFunctions.count(&F))
      return false;

    Mod = F.getParent();
    Context = &F.getContext();

    // Test each block of the function for a noise marker and extract
    // the corresponding region.
    // We extract nested regions exactly in the order that we apply
    // the optimizations and re-inlining later. Thus, we have to recurse
    // *before* extracting a region.
    // To do this properly, we need to reconstruct the region after we
    // extracted a noise region and then start iterating again.
    SmallPtrSet<BasicBlock*, 32> visitedBlocks;
    bool iterate = true;
    while (iterate)
    {
      iterate = false;
      for (Function::iterator BB = F.begin(), BBE=F.end(); BB!=BBE; ++BB)
      {
        const bool isTopLevel = !hasNoiseFunctionAttribute(*BB->getParent());
        if (resolveMarkers(BB, visitedBlocks, isTopLevel))
        {
          iterate = true;
          break;
        }
      }
    }

    return true;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
  }
};

// This custom inlining pass is required since the built-in functionality
// cannot inline functions which are in different modules
// TODO: This should not be necessary anymore.
struct NoiseInliner : public FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid

  explicit NoiseInliner()
  : FunctionPass(ID) {
    initializeNoiseInlinerPass(*PassRegistry::getPassRegistry());
  }

  virtual ~NoiseInliner()
  { }

  virtual bool runOnFunction(Function &F)
  {
    // Collect all blocks which belong to the function.
    SmallPtrSet<BasicBlock*, 32> functionRegion;
    collectBlocks<32>(&F.front(), &F.back(), functionRegion);
    // Loop over the collected blocks and find all interesting call instructions
    SmallVector<CallInst*, 32> calls;
    for (SmallPtrSet<BasicBlock*, 32>::iterator it = functionRegion.begin(),
         e = functionRegion.end(); it != e; ++it)
    {
      for(BasicBlock::iterator bit = (*it)->begin(), e = (*it)->end(); bit != e; ++bit)
      {
        if(!isa<CallInst>(*bit))
          continue;
        calls.push_back(&cast<CallInst>(*bit));
      }
    }
    // inline each call
    for(SmallVector<CallInst*, 32>::iterator it = calls.begin(),
        e = calls.end(); it != e; ++it)
    {
      InlineFunctionInfo IFI;
      InlineFunction(*it, IFI);
    }

    return true;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
  }
};

struct NoiseSpecializer : public FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid

  const StringRef            mVariable;
  const SmallVector<int, 4>* mValues;

  explicit NoiseSpecializer() : FunctionPass(ID), mVariable(""), mValues(0)
  {
    assert (false && "empty constructor must never be called!");
    initializeNoiseSpecializerPass(*PassRegistry::getPassRegistry());
  }

  NoiseSpecializer(StringRef&                 variable,
                   const SmallVector<int, 4>& values)
  : FunctionPass(ID), mVariable(variable), mValues(&values)
  {
    initializeNoiseSpecializerPass(*PassRegistry::getPassRegistry());
  }

  virtual ~NoiseSpecializer()
  { }

  virtual bool runOnFunction(Function &F)
  {
    return false;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
  }
};

#ifdef NOISE_ANALYZE_REDUCTIONS
struct NoiseReductionAnalyzer : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid

  Module*          mModule;
  LLVMContext*     mContext;
  LoopInfo*        mLoopInfo;
  DominatorTree*   mDomTree;
  ScalarEvolution* mSCEV;
  DataLayout*      mDataLayout;

  NoiseReductionAnalyzer()
  : FunctionPass(ID)
  {
    initializeNoiseReductionAnalyzerPass(*PassRegistry::getPassRegistry());
  }

  virtual ~NoiseReductionAnalyzer()
  { }

  virtual bool runOnFunction(Function &F)
  {
    mModule     = F.getParent();
    mContext    = &F.getContext();
    mLoopInfo   = &getAnalysis<LoopInfo>();
    mDomTree    = &getAnalysis<DominatorTree>();
    mSCEV       = &getAnalysis<ScalarEvolution>();
    mDataLayout = getAnalysisIfAvailable<DataLayout>();

    std::string error;
    raw_fd_ostream out("noise_reduction_analysis.txt", error, raw_fd_ostream::F_Append);
    //raw_ostream& out = outs();

    out << "\n\nNoise reduction analysis of function: '" << F.getName() << "':\n";

    for (LoopInfo::iterator L=mLoopInfo->begin(), LE=mLoopInfo->end(); L!=LE; ++L)
    {
      if (analyzeLoop(*L, NULL, out))
      {
        out << "  is vectorizable outer loop!\n";
      }
    }

    return false;
  }

  struct ReductionUpdate
  {
    ~ReductionUpdate()
    {
      mOtherOperands->clear();
      mResultUsers->clear();
      delete mOtherOperands;
      delete mResultUsers;
    }

    // The update operation.
    Instruction*             mOperation;
    // The operands that are *not* part of the reduction SCC.
    SetVector<Value*>*       mOtherOperands;
    // The users of this update operation that are *not* part of the reduction SCC (if any).
    SetVector<Instruction*>* mResultUsers;
    // The mask that is required for this update.
    bool                     mRequiresMask;
    // The mask that is required for this update.
    Value*                   mMask;
    // The result vector that contains the W different results of each iteration.
    Value*                   mResultVector;
  };

  typedef DenseMap<Instruction*, ReductionUpdate*> RedUpMapType;

  struct ReductionVariable
  {
    ~ReductionVariable()
    {
      for (RedUpMapType::iterator it=mUpdates->begin(),
           E=mUpdates->end(); it!=E; ++it)
      {
        delete it->second;
      }
      delete mUpdates;
    }

    // The reduction phi in the loop header.
    PHINode*      mPhi;
    // The start value (phi operand from pre header).
    Value*        mStartVal;
    // All update operations that belong to the reduction SCC.
    RedUpMapType* mUpdates;
    // The final reduction result user (if any).
    PHINode*      mResultUser;
  };

  typedef SmallVector<ReductionVariable*, 2> RedVarVecType;

  // TODO: There's a problem with store-load chains that we don't detect
  //       to be part of the SCC!
  bool
  findReductionSCC(Instruction*                  curInst,
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
  gatherReductionUpdateInfo(RedUpMapType&        reductionSCC,
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
      SetVector<Value*>* otherOps = new SetVector<Value*>();
      for (Instruction::op_iterator O=updateOp->op_begin(),
           OE=updateOp->op_end(); O!=OE; ++O)
      {
        if (Instruction* opInst = dyn_cast<Instruction>(*O))
        {
          if (reductionPhi == opInst) continue;
          if (reductionSCC.count(opInst)) continue;
        }
        otherOps->insert(*O);
      }
      redUp.mOtherOperands = otherOps;

      // Add all users that are not part of the SCC to the "result users" set.
      SetVector<Instruction*>* resultUsers = new SetVector<Instruction*>();
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

      // Find out if this operation may require masked reduction.
      // NOTE: It would be beneficial to have WFV divergence information here.
      redUp.mRequiresMask = isa<PHINode>(updateOp) || isa<SelectInst>(updateOp) ||
          !domTree.dominates(updateOp->getParent(), latchBB);

      // The mask value is only used later (if at all).
      redUp.mMask = 0;

      // The result vector value is only used later (if at all).
      redUp.mResultVector = 0;
    }
  }

  // TODO: Make sure there is no interference between reduction variables.
  void
  collectReductionVariables(RedVarVecType&       redVars,
                            PHINode*             indVarPhi,
                            const Loop&          loop,
                            const LoopInfo&      loopInfo,
                            const DominatorTree& domTree,
                            raw_ostream&         out)
  {
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
      Instruction* backEdgeOp = cast<Instruction>(reductionPhi->getIncomingValueForBlock(latchBB));

      RedUpMapType* reductionSCC = new RedUpMapType();
      SmallPtrSet<Instruction*, 8> visitedInsts;
      findReductionSCC(backEdgeOp, reductionPhi, loop, *reductionSCC, visitedInsts);

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
      redVar->mResultUser = 0;
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

      redVars.push_back(redVar);
    }
  }

  bool analyzeLoop(Loop*        loop,
                   Loop*        parentLoop,
                   raw_ostream& out)
  {
    assert (loop);

    //const bool hasNestedLoops = loop->begin() != loop->end();

    bool childrenAreVectorizable = true;
    for (Loop::iterator SL=loop->begin(), SLE=loop->end(); SL!=SLE; ++SL)
    {
      const bool isVectorizable = analyzeLoop(*SL, loop, out);
      childrenAreVectorizable &= isVectorizable;
      if (isVectorizable)
      {
        out << "  is vectorizable inner loop!\n";
      }
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
    PHINode* indVarPhi = NULL;
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
            out << "  has additional induction variable: " << *phi << "\n";
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
          out << "  has additional induction variable: " << *phi << "\n";
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

    // We ignore the rest of the analysis if there are multiple exits.
    if (!exitBB) return false;

    RedVarVecType redVars;
    collectReductionVariables(redVars, indVarPhi, *loop, *mLoopInfo, *mDomTree, out);

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

      if (U->size() > 1) out << "    has multiple updates!\n";
      unsigned opcode = U->empty() ? 0 : U->begin()->second->mOperation->getOpcode();
      bool hasDifferentUpdateOperations = false;

      for (RedUpMapType::const_iterator it=U->begin(), E=U->end(); it!=E; ++it)
      {
        const ReductionUpdate& redUp = *it->second;
        out << "    update operation: " << *redUp.mOperation << "\n";
        if (redUp.mRequiresMask) out << "      requires mask!\n";

        Loop* updateOpLoop = mLoopInfo->getLoopFor(redUp.mOperation->getParent());
        if (loop != updateOpLoop)
        {
          out << "      is inside inner loop with header: '"
              << updateOpLoop->getHeader()->getName() << "'\n";
        }

        switch (redUp.mOperation->getOpcode())
        {
          case Instruction::Add:
          case Instruction::Sub:
          case Instruction::Mul:
          case Instruction::UDiv:
          case Instruction::SDiv:
          case Instruction::URem:
          case Instruction::SRem:
            out << "      is integer operation!\n";
            break;
          case Instruction::Shl:
          case Instruction::LShr:
          case Instruction::AShr:
            out << "      is shift operation!\n";
            break;
          case Instruction::Or:
          case Instruction::And:
          case Instruction::Xor:
            out << "      is bitwise operation!\n";
            break;
          case Instruction::FAdd:
          case Instruction::FSub:
          case Instruction::FMul:
          case Instruction::FDiv:
          case Instruction::FRem:
            out << "      is floating point operation!\n";
            break;
          default:
            out << "      is complex operation!\n";
        }

        hasDifferentUpdateOperations |= opcode != redUp.mOperation->getOpcode();

#if 0
        const SetVector<Value*>& otherOperands = *redUp.mOtherOperands;
        for (SetVector<Value*>::const_iterator it2=otherOperands.begin(),
             E2=otherOperands.end(); it2!=E2; ++it2)
        {
          Value* operand = *it2;
        }
#endif

        const SetVector<Instruction*>& resultUsers = *redUp.mResultUsers;
        for (SetVector<Instruction*>::const_iterator it2=resultUsers.begin(),
             E2=resultUsers.end(); it2!=E2; ++it2)
        {
          Instruction* user = *it2;
          out << "      result user: " << *user << "\n";
          if (!loop->contains(user->getParent()))
          {
            out << "        is not part of loop!\n";
            isVectorizable = false; // TODO: ?
          }
        }

        reductionOps.insert(redUp.mOperation);
      }

      if (hasDifferentUpdateOperations)
      {
        out << "    has different update operations (possibly non-associative)!\n";
        isVectorizable = false;
      }

      reductionOps.insert(redVar.mPhi);
    }

    // TODO: Must not have non-reduction values with users outside the loop.
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
        isVectorizable = false;
      }
    }

    return isVectorizable;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      //AU.addRequiredID(LoopSimplifyID); // "Unable to schedule"
      //AU.addRequiredID(LCSSAID); // "Unable to schedule"
      AU.addRequired<ScalarEvolution>();
      AU.addRequired<LoopInfo>();
      AU.addRequired<DominatorTree>();
      AU.addRequired<DataLayout>();
      AU.setPreservesAll();
  }
};
#endif


char NoiseExtractor::ID = 0;
char NoiseInliner::ID = 0;
char NoiseSpecializer::ID = 0;
#ifdef NOISE_ANALYZE_REDUCTIONS
char NoiseReductionAnalyzer::ID = 0;
#endif
}

// Pass declarations

INITIALIZE_PASS_BEGIN(NoiseExtractor, "noise-extract",
                      "Extract code blocks into noise functions", false, false)
INITIALIZE_PASS_END(NoiseExtractor, "noise-extract",
                    "Extract code blocks into noise functions", false, false)

INITIALIZE_PASS_BEGIN(NoiseInliner, "noise-inline",
                      "Forces inlining of calls", false, false)
INITIALIZE_PASS_END(NoiseInliner, "noise-inline",
                    "Forces inlining of calls", false, false)

INITIALIZE_PASS_BEGIN(NoiseSpecializer, "noise-specialize",
                      "Specializes code for specific values of a variable", false, false)
INITIALIZE_PASS_END(NoiseSpecializer, "noise-specialize",
                    "Specializes code for specific values of a variable", false, false)

#ifdef NOISE_ANALYZE_REDUCTIONS
INITIALIZE_PASS_BEGIN(NoiseReductionAnalyzer, "noise-analyze-reductions",
                      "Analyze loops with loop-carried dependencies", false, true)
//INITIALIZE_PASS_DEPENDENCY(AliasAnalysis)
//INITIALIZE_PASS_DEPENDENCY(TargetTransformInfo)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolution)
INITIALIZE_PASS_DEPENDENCY(LoopSimplify)
INITIALIZE_PASS_DEPENDENCY(LoopInfo)
INITIALIZE_PASS_DEPENDENCY(DominatorTree)
INITIALIZE_PASS_END(NoiseReductionAnalyzer, "noise-analyze-reductions",
                    "Analyze loops with loop-carried dependencies", false, true)
#endif


namespace llvm {
namespace noise {

// NoiseFnInfo

void NoiseFnInfo::UpdateOptDesc(MDNode* OptDesc)
{
  // according to the description from NoiseOptimization.h
  size_t numOps = OptDesc->getNumOperands();
  for(size_t i = 0; i < numOps; ++i)
    assert( isa<NoiseOptimization>(OptDesc->getOperand(i)) && "invalid noise opt" );

  mOptDesc = OptDesc;
}

NoiseOptimization* NoiseFnInfo::GetOptimization(size_t i) {
  assert( isa<NoiseOptimization>(mOptDesc->getOperand(i)) );
  return cast<NoiseOptimization>(mOptDesc->getOperand(i));
}

size_t NoiseFnInfo::GetNumOptimizations() const {
  return mOptDesc->getNumOperands();
}

void NoiseOptimizations::Instantiate(NoiseOptimization* Opt, PassRegistry* Registry,
                                     FunctionPassManager& Passes)
{
  const StringRef pass = GetPassName(Opt);
  if(pass == "inline")
    Passes.add(new NoiseInliner());
  else if(pass == "unroll") {
    const int count = NoiseOptimizations::HasPassArg(Opt, 0U) ?
      NoiseOptimizations::GetPassArgAsInt(Opt, 0U) : -1;

    outs() << "Running pass: indvars\n";
    outs() << "Running pass: loop-rotate\n";

    Passes.add(createIndVarSimplifyPass()); // TODO: Shouldn't this be left to the user?
    Passes.add(createLoopRotatePass()); // TODO: Shouldn't this be left to the user?
    Passes.add(createLoopUnrollPass(-1, count, false));
  } else if(pass == "opt") {
    PassManagerBuilder builder;
    // use 2 instead of 3 in order to avoid the creation of passes which
    // are incompatible with our pass setup
    // during (the invocation of the populateModulePassManager method)
    builder.OptLevel = 2U;
    builder.SizeLevel = 0U;
    builder.DisableUnitAtATime = true;
    builder.populateFunctionPassManager(Passes);
    builder.populateModulePassManager(Passes);
  } else if(pass == "specialize") {
    // pass = "specialize(x,1,2,3)"
    StringRef variable = NoiseOptimizations::GetPassArgAsString(Opt, 0U);
    SmallVector<int, 4> values;
    for(size_t i = 0, e = values.size(); i < e; ++i)
      values.push_back(NoiseOptimizations::GetPassArgAsInt(Opt, i));
    Passes.add(new NoiseSpecializer(variable, values));
  } else if(pass == "wfv") {
#ifndef COMPILE_NOISE_WFV_WRAPPER
    errs() << "ERROR: No support for WFV is available\n";
#else
    outs() << "Running pass: loop-simplify\n";
    outs() << "Running pass: lowerswitch\n";
    outs() << "Running pass: indvars\n";
    outs() << "Running pass: lcssa\n";

    // Add preparatory passes for WFV.
    Passes.add(createLoopSimplifyPass());
    Passes.add(createLowerSwitchPass());
    // Add induction variable simplification pass.
    Passes.add(createIndVarSimplifyPass());
    // Convert to loop-closed SSA form to simplify applicability analysis.
    Passes.add(createLCSSAPass());

    // WFV may receive argument to specify vectorization width, whether to
    // use AVX and whether to use the divergence analysis.
    // "wfv-vectorize"          -> width 4, do not use avx, use divergence analysis (default)
    // "wfv-vectorize (4,0,1)"  -> width 4, do not use avx, use divergence analysis (default)
    // "wfv-vectorize (8,1,1)"  -> width 8, use avx, use divergence analysis
    // "wfv-vectorize (8,1)"    -> width 8, use avx, use divergence analysis
    // "wfv-vectorize (16,0,0)" -> width 16, do not use avx, do not use divergence analysis
    unsigned   vectorizationWidth = NoiseOptimizations::HasPassArg(Opt, 0U) ?
        (unsigned)NoiseOptimizations::GetPassArgAsInt(Opt, 0U) : 4U;
    bool       useAVX = NoiseOptimizations::HasPassArg(Opt, 1U) &&
        NoiseOptimizations::GetPassArgAsInt(Opt, 1U);
    bool       useDivergenceAnalysis = NoiseOptimizations::HasPassArg(Opt, 2U) ?
        NoiseOptimizations::GetPassArgAsInt(Opt, 2U) : true;
    const bool verbose = false;

    // Add WFV pass wrapper.
    Passes.add(new NoiseWFVWrapper(vectorizationWidth,
                                   useAVX,
                                   useDivergenceAnalysis,
                                   verbose));
#endif
  } else {
    const PassInfo* info = Registry->getPassInfo(pass);
    if(!info) {
      errs() << "ERROR: Pass not found: " << pass << "\n";
      return;
    }
    Passes.add(info->createPass());
  }
}

// Noise Optimizer

NoiseOptimizer::NoiseOptimizer(llvm::Module *M)
  : Mod(M)
  , NoiseMod(new Module("noiseMod", Mod->getContext()))
  , Registry(PassRegistry::getPassRegistry())
  , MD(Mod->getOrInsertNamedMetadata("noise"))
{ }

NoiseOptimizer::~NoiseOptimizer()
{
  for (NoiseFnInfoVecType::iterator it=noiseFnInfoVec.begin(),
       E=noiseFnInfoVec.end(); it!=E; ++it)
  {
    delete *it;
  }
  delete NoiseMod;
}

struct NoisePassListener : public PassRegistrationListener {

  NoisePassListener() {}

  virtual ~NoisePassListener() {}

  virtual void passRegistered(const PassInfo *) {}

  void enumeratePasses();

  virtual void passEnumerate(const PassInfo * p)
  {
    outs() << p->getPassArgument() << " (" << p->getPassName() << ")\n";
  }
};

namespace {

Function* createDummyFunction(Function* noiseFn)
{
    assert (noiseFn);
    Module* mod = noiseFn->getParent();
    LLVMContext& context = mod->getContext();

    // Create dummy block.
    BasicBlock* entryBB = BasicBlock::Create(context, "");

    SmallVector<Value*, 4> values;
    for (Function::iterator BB=noiseFn->begin(), BBE=noiseFn->end(); BB!=BBE; ++BB)
    {
      for (BasicBlock::iterator I=BB->begin(), IE=BB->end(); I!=IE; ++I)
      {
        // Handle global variables etc.
        for (Instruction::op_iterator O=I->op_begin(), OE=I->op_end(); O!=OE; ++O)
        {
          Value* opVal = cast<Value>(*O);
          if (isa<Function>(opVal)) continue;
          if (isa<BasicBlock>(opVal)) continue;

          if (!isa<GlobalValue>(opVal) &&
              !isa<GlobalVariable>(opVal) &&
              !isa<ConstantExpr>(opVal))
          {
            continue;
          }
          values.push_back(new LoadInst(opVal, "", entryBB));
        }

        // Handle calls to other functions.
        if (!isa<CallInst>(I)) continue;

        CallInst* call = cast<CallInst>(I);

        Function* callee = call->getCalledFunction();
        if (!callee) continue;

        // Create dummy arguments.
        SmallVector<Value*, 2> args;
        for (unsigned i=0, e=call->getNumArgOperands(); i<e; ++i)
        {
          Value* oldArg = call->getArgOperand(i);
          args.push_back(UndefValue::get(oldArg->getType()));
        }

        // Create dummy call.
        CallInst* dummyCall = CallInst::Create(callee, args, "", entryBB);
        if (!dummyCall->getType()->isVoidTy()) values.push_back(dummyCall);
      }
    }

    if (entryBB->empty()) return NULL;

    // Create dummy function with one parameter per dummy value.
    SmallVector<Type*, 4> argTypes;
    for (SmallVector<Value*, 4>::iterator it=values.begin(), E=values.end(); it!=E; ++it)
    {
        Type* argType = (*it)->getType();
        assert (!argType->isVoidTy());
        argTypes.push_back(PointerType::getUnqual(argType));
    }

    FunctionType* type = FunctionType::get(Type::getVoidTy(context), argTypes, false);

    Function* dummyFn = Function::Create(type, GlobalValue::ExternalLinkage, "dummy", mod);

    // Add the entry block to the function.
    dummyFn->getBasicBlockList().push_back(entryBB);

    // Create a store operation for each value to prevent deletion of the load.
    Function::arg_iterator A = dummyFn->arg_begin();
    for (SmallVector<Value*, 4>::iterator it=values.begin(), E=values.end(); it!=E; ++it, ++A)
    {
        Value* value = *it;
        Value* ptr   = A;
        assert (!value->getType()->isVoidTy());
        new StoreInst(value, ptr, false, entryBB);
    }

    // Finally, create a return instruction to finish the block and function.
    ReturnInst::Create(context, entryBB);

    return dummyFn;
}

} // unnamed namespace

// TODO: Support "negative" noise attributes (e.g. "subtraction" of specified
//       passes from O3).
void NoiseOptimizer::PerformOptimization()
{
  // Initialize all passes linked into all libraries (see InitializePasses.h).
  // This way, they are registerd so we can add them via getPassInfo().
  initializeCore(*PassRegistry::getPassRegistry());
  initializeTransformUtils(*PassRegistry::getPassRegistry());
  initializeScalarOpts(*PassRegistry::getPassRegistry());
  initializeVectorization(*PassRegistry::getPassRegistry());
  initializeInstCombine(*PassRegistry::getPassRegistry());
  initializeIPO(*PassRegistry::getPassRegistry());
  initializeInstrumentation(*PassRegistry::getPassRegistry());
  initializeAnalysis(*PassRegistry::getPassRegistry());
  initializeIPA(*PassRegistry::getPassRegistry());
  initializeCodeGen(*PassRegistry::getPassRegistry());
  initializeTarget(*PassRegistry::getPassRegistry());

#ifdef NOISE_ANALYZE_REDUCTIONS
  PrettyStackTraceString CrashInfoNoise("NOISE: Analyzing reductions");
  //////////////////////////////////////////////////////////////////////////////
  // REDUCTION ANALYZER: CATEGORIZE LOOPS IN TERMS OF THEIR VECTORIZABILITY.
  //////////////////////////////////////////////////////////////////////////////
  {
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
    PM.add(new NoiseReductionAnalyzer());
    PM.run(*Mod);
  }
  return;
#endif

  // If there is no noise attribute, return immediately.
  if (MD->getNumOperands() == 0) return;

  PrettyStackTraceString CrashInfo("NOISE: Optimizing functions");

  {
    // Perform some standard optimizations upfront.
    // NOTE: This should not interfere with the user-defined optimizations.
    //       If we don't do this transformation to SSA here (before
    //       extraction), later phases are unable to optimize the extracted
    //       function because of aliasing problems (the generated function
    //       will usually have lots of pointer parameters).
    PassManager PM;
    PM.add(new DataLayout(Mod));
    PM.add(createTypeBasedAliasAnalysisPass());
    PM.add(createBasicAliasAnalysisPass());
    PM.add(createScalarReplAggregatesPass());
    PM.run(*Mod);
  }

  // Extract noise code regions from compound statements into separate functions.
  // These functions look exactly like functions with noise function attribute.
  {
    PassManager PM;
    PM.add(new NoiseExtractor(&noiseFnInfoVec, MD));
    PM.run(*Mod);
  }

  //outs() << "Module after compound noise extraction: " << *Mod;

  // Get the corresponding noise attribute.
  // We cannot just iterate over the metadata since the order of the
  // functions is important (for nested attributes). We have to be able
  // to iterate the extracted functions in that same order.
  for (unsigned i=0, e=MD->getNumOperands(); i<e; ++i) {
    MDNode* functionMDN = MD->getOperand(i);
    Function* noiseFn = GetNoiseFunction(functionMDN);

    NoiseFnInfo* nfi = 0;
    for (unsigned i=0, e=noiseFnInfoVec.size(); i<e; ++i)
    {
      if (noiseFnInfoVec[i]->mOrigFn != noiseFn) continue;
      nfi = noiseFnInfoVec[i];
      break;
    }

    // If the function is not inside noiseFnInfoVec, it was not extracted from code
    // but corresponds to a noise function attribute. In this case, there
    // is no NoiseFnInfo object yet.
    if (!nfi)
    {
      nfi = new NoiseFnInfo(noiseFn);
      noiseFnInfoVec.push_back(nfi);
    }

    nfi->UpdateOptDesc(GetNoiseOptDesc(functionMDN));
    assert (nfi->mOptDesc);

    // Make sure that no other optimizations than the requested ones are
    // executed on that function.
    // To this end, we clone "top level" functions (all others are inlined
    // after noise optimizations anyway) and delete the body of the original
    // function.
    // This way, there is no connection between the original code and the
    // noise function, so the rest of the original code can still be optimized
    // normally without affecting the noise part.
    if (nfi->mReinline) continue;

    ValueToValueMapTy valueMap;
    Function* movedNoiseFn = CloneFunction(noiseFn, valueMap, false);
    movedNoiseFn->setName(noiseFn->getName()+".noise");
    nfi->mMovedFn = movedNoiseFn;
    Mod->getFunctionList().push_back(movedNoiseFn);

    // Update NoiseFnInfo objects that have their mCall member point into
    // the moved function, and thus, have to be updated to the new function.
    // Otherwise, we can not inline the functions back in order.
    for (unsigned i=0, e=noiseFnInfoVec.size(); i<e; ++i)
    {
      NoiseFnInfo* nfi = noiseFnInfoVec[i];
      if (!nfi->mCall) continue;
      if (nfi->mCall->getParent()->getParent() != noiseFn) continue;
      nfi->mCall = cast<CallInst>(valueMap[nfi->mCall]);
    }

    // Make the old function an external declaration so the rest of the
    // code is still valid and can be optimized.
    noiseFn->deleteBody();
  }

  // Now optimize each function separately (execute the requested passes) and
  // inline functions from nested noise attributes again.
  // NOTE: We must not inline functions that were created from "top-level"
  //       noise attributes, since this code then would be optimized with all
  //       other optimizations again.
  // NOTE: The module vector obeys the correct nesting order, so we first
  //       optimize the innermost code blocks, inline them, and then continue
  //       with the parents.
  for (unsigned i=0, e=noiseFnInfoVec.size(); i<e; ++i)
  {
    NoiseFnInfo*   nfi    = noiseFnInfoVec[i];
    Function*     noiseFn = nfi->mReinline ? nfi->mOrigFn : nfi->mMovedFn;

    assert (!nfi->mReinline || !nfi->mMovedFn);

    // Display all available passes.
    //NoisePassListener list;
    //Registry->enumerateWith(&list);
    outs() << "Running noise optimizations on function '"
      << noiseFn->getName() << "': \n";

    // Run requested noise passes.
    FunctionPassManager NoisePasses(Mod);
    NoisePasses.add(new DataLayout(Mod));

    // Run CFG simplification upfront to remove the blocks we introduced
    // ourselves.
    // TODO: Replace this by some simple code that only removes *exactly* the
    //       blocks and instructions we introduced so the user is not confused.
    NoisePasses.add(createCFGSimplificationPass());

    for(size_t i = 0, e = nfi->GetNumOptimizations(); i < e; ++i) {
      NoiseOptimization* noiseOpt = nfi->GetOptimization(i);
      outs() << "Running pass: " << NoiseOptimizations::GetPassName(noiseOpt) << "\n";
      NoiseOptimizations::Instantiate(noiseOpt, Registry, NoisePasses);
    }

    // TODO: Remove this when reaching "production" state or so.
    NoisePasses.add(createVerifierPass());

    // Run the required passes
    NoisePasses.run(*noiseFn);

    // If this is a function that was created from a top-level noise attribute,
    // we are done.
    if (!nfi->mReinline) continue;

    // If mCall is not set, this was a noise function attribute.
    // Thus, we must not inline/remove anything.
    if (!nfi->mCall) continue;

    // We want to run some optimizations on the function after inlining,
    // so we have to fetch it from the call before it is gone.
    Function* parentFn = nfi->mCall->getParent()->getParent();

    // Otherwise, inline the only call to this function.
    InlineFunctionInfo IFI;
    InlineFunction(nfi->mCall, IFI);

    // Remove the now inlined noise function again.
    assert (noiseFn->use_empty());
    noiseFn->eraseFromParent();
    nfi->mMovedFn = 0;

    {
      // Perform some standard optimizations after inlining.
      // TODO: This may disturb user experience.
      FunctionPassManager PM(Mod);
      PM.add(new DataLayout(Mod));
      PM.add(createTypeBasedAliasAnalysisPass());
      PM.add(createBasicAliasAnalysisPass());
      PM.add(createCFGSimplificationPass());
      PM.add(createScalarReplAggregatesPass());
      PM.add(createEarlyCSEPass());
      PM.run(*parentFn);
    }

    //outs() << "module after reinlining: " << *Mod << "\n";
  }

  // At this point, all noise functions that were not "top level" are
  // inlined and erased.
  //outs() << "module after passes: " << *Mod << "\n";

  // Finally, move all "top-level" noise functions into a different
  // module and set calls to them to an external declaration. This is to
  // prevent the standard optimizations etc. to run on noise functions.
  // They are reassembled later.
  for (unsigned i=0, e=noiseFnInfoVec.size(); i<e; ++i)
  {
    NoiseFnInfo* nfi      = noiseFnInfoVec[i];
    Function*    noiseFn  = nfi->mMovedFn;

    // If this is no top level function, continue.
    if (!noiseFn) continue;

    assert (!nfi->mReinline && "there should be no non-top level function left!");

    // Before we move the function, we have to create a dummy that calls
    // all functions that are also called in the current noise function.
    // This is to prevent their deletion during the standard optimizations.
    Function* dummyFn = createDummyFunction(noiseFn);
    if (dummyFn) dummyFnVec.push_back(dummyFn);

    // Move function to noise module.
    noiseFn->removeFromParent();
    assert (!Mod->getFunction(noiseFn->getName()));
    NoiseMod->getFunctionList().push_back(noiseFn);

    // If this is a "function noise" function without use, the original
    // function can be removed by the module optimizations.
    // To ensure that we catch such cases, we have to do two things:
    // - Set the original function to NULL.
    // - Set the name of the moved noise function to the original name
    //   so we don't lose track of it.
    CallInst* call = nfi->mCall;
    if (!call && nfi->mOrigFn->use_empty())
    {
      noiseFn->takeName(nfi->mOrigFn);
      nfi->mOrigFn = 0;
    }

    // Update call to temporarily point to original function again
    // (the external declaration that has not been moved).
    // This is only valid for non-function noise.
    if (call) call->setCalledFunction(nfi->mOrigFn);
  }

  // If we have moved top-level functions that include calls to "compound
  // noise" functions, we also have to move the declarations of those callees.
  // The declarations in question are those that have a use in the NoiseMod.
  for (unsigned i=0, e=noiseFnInfoVec.size(); i<e; ++i)
  {
    NoiseFnInfo* nfi      = noiseFnInfoVec[i];
    Function*    noiseFn  = nfi->mMovedFn;

    // If this is no top level function, continue.
    if (!noiseFn) continue;

    // TODO: What is this?!
  }

  //outs() << "module after outsourcing: " << *Mod << "\n";
  //outs() << "noise module after outsourcing: " << *NoiseMod << "\n";
}

void NoiseOptimizer::Reassemble()
{
  // If there is no noise attribute, return immediately.
  if (MD->getNumOperands() == 0) return;

  PrettyStackTraceString CrashInfo("NOISE: reassemble module after optimizations");

  for (SmallVector<Function*, 4>::iterator it=dummyFnVec.begin(),
       E=dummyFnVec.end(); it!=E; ++it)
  {
    (*it)->eraseFromParent();
  }

  for (unsigned i=0, e=noiseFnInfoVec.size(); i<e; ++i) {
    NoiseFnInfo* nfi = noiseFnInfoVec[i];

    if (nfi->mReinline) continue; // Has already been reassembled/inlined.

    Function* movedNoiseFn = nfi->mMovedFn;
    assert (movedNoiseFn);
    assert (movedNoiseFn->getParent() == NoiseMod);

    Function* decl = nfi->mOrigFn;

    if (!decl)
    {
      // This is a "function noise" function without use, so it is likely that
      // it got deleted during the "normal" optimization phase.
      // NOTE: We have to make this query *before* moving the function!
      decl = Mod->getFunction(movedNoiseFn->getName());
    }

    // Move function back to Mod.
    movedNoiseFn->removeFromParent();
    Mod->getFunctionList().push_back(movedNoiseFn);
    assert (movedNoiseFn->getParent() == Mod);

    // If the original function was indeed removed, skip everything else.
    if (!decl) continue;

    assert (Mod == nfi->mOrigFn->getParent());

    // Replace uses of declaration by function.
    decl->replaceAllUsesWith(movedNoiseFn);

    // Make sure the function has the same name again.
    movedNoiseFn->takeName(decl);

    // Remove declaration from TheModule.
    decl->eraseFromParent();

    // If mCall is not set, this was a noise function attribute.
    // Thus, we must not inline/remove anything.
    if (!nfi->mCall) return;

    // We have multiple options here.
    // 1) We mark the parent function as "noinline" after the noise function
    // was extracted to NoiseMod. This way, the standard optimizer would not
    // inline it, preventing cases where we have more than one call.
    // 2) If we don't mark it as "noinline", the parent function will often be
    // inlined because most of the code was extracted. Thus, we could inline
    // *all* calls to the function here, which could possibly result in too much
    // code being inlined. Thus, we should let the inliner decide whether to
    // inline or not, and possibly leave the new function in the module.
    // This in turn could be confusing to the user, because the originally
    // written function was inlined, but a new one is called.
    // 3) Mark as "noinline", inline the (then only) call back into the original
    // function, then run the standard inliner again on that one.

    // If mCall is set, inline the call to this function.
    InlineFunctionInfo IFI;
    InlineFunction(nfi->mCall, IFI);

    // There may be additional calls (see comment above).
    // For now, we don't care and simply attempt to inline all calls (option 2).
    SmallVector<CallInst*, 2> callVec;
    for (Function::use_iterator U=movedNoiseFn->use_begin(),
         UE=movedNoiseFn->use_end(); U!=UE; ++U)
    {
      if (!isa<CallInst>(*U)) continue;
      callVec.push_back(cast<CallInst>(*U));
    }
    for (SmallVector<CallInst*, 2>::iterator it=callVec.begin(),
         E=callVec.end(); it!=E; ++it)
    {
      InlineFunctionInfo IFI;
      InlineFunction(*it, IFI);
    }

    // Remove the now inlined noise function again.
    if (movedNoiseFn->use_empty())
    {
      movedNoiseFn->eraseFromParent();
    }

    //outs() << "module after reinlining: " << *Mod << "\n";

    {
      // Perform some standard optimizations after inlining.
      // TODO: This may disturb user experience.
      PassManager PM;
      PM.add(new DataLayout(Mod));
      PM.add(createTypeBasedAliasAnalysisPass());
      PM.add(createBasicAliasAnalysisPass());
      PM.add(createCFGSimplificationPass());
      PM.add(createScalarReplAggregatesPass());
      PM.add(createEarlyCSEPass());
      PM.run(*Mod);
    }

    //outs() << "module after post inlining std opts: " << *Mod << "\n";
  }
}

void NoiseOptimizer::Finalize()
{
  // Remove noise metadata from TheModule.
  // TODO: Only if we know that there is only noise metadata inside.
  // TODO: If we don't do this, CodeGenPasses->run() fails with an assertion.
  MD->eraseFromParent();
  //outs() << "module after noise: " << *Mod;
}

}
}
