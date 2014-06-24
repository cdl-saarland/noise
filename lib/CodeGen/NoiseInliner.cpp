//===--- NoiseInliner.cpp - Noise Function Inliner ------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Noise inliner definitions
//
//===----------------------------------------------------------------------===//

#include "NoiseInliner.h"

#include "llvm/Pass.h"
#include "llvm/PassRegistry.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace llvm {

template<unsigned SetSize>
void collectBlocks(BasicBlock* block, BasicBlock* endBB, SmallPtrSet<BasicBlock*, SetSize>& region)
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

void initializeNoiseInlinerPass(llvm::PassRegistry&);

// This custom inlining pass is required since the built-in functionality
// cannot inline functions which are in different modules
struct NoiseInliner : public FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid

  SmallVector<std::string, 2> functionNames;
  SmallPtrSet<Function*, 2>   functions;

  explicit NoiseInliner()
    : FunctionPass(ID) {
    initializeNoiseInlinerPass(*PassRegistry::getPassRegistry());
  }

  explicit NoiseInliner(SmallVector<std::string, 2> &fnNames)
  : FunctionPass(ID), functionNames(fnNames) {
    initializeNoiseInlinerPass(*PassRegistry::getPassRegistry());
  }

  virtual ~NoiseInliner()
  { }

  virtual bool runOnFunction(Function &F)
  {
    const bool inlineAll = functionNames.empty();

    // Get Functions from input strings (if any).
    Module* mod = F.getParent();
    for (SmallVector<std::string, 2>::iterator it=functionNames.begin(),
         E=functionNames.end(); it!=E; ++it)
    {
      Function* fn = mod->getFunction(*it);
      if (!fn)
      {
        errs() << "ERROR: Function requested for inlining does not exist in module: '"
          << *it << "'!\n";
        abort();
      }

      functions.insert(fn);
    }

    // Collect blocks that belong to the marked region.
    SmallPtrSet<BasicBlock*, 32> functionRegion;
    collectBlocks<32>(&F.front(), &F.back(), functionRegion);

    // For all specified functions, collect all calls within the marked code segment.
    // If no function names were given, collect all calls to any function.
    SmallVector<CallInst*, 32> calls;
    for (SmallPtrSet<BasicBlock*, 32>::iterator it = functionRegion.begin(),
         e = functionRegion.end(); it != e; ++it)
    {
      for(BasicBlock::iterator I=(*it)->begin(), IE=(*it)->end(); I!=IE; ++I)
      {
        if (!isa<CallInst>(I)) continue;
        CallInst* call = cast<CallInst>(I);
        if (!inlineAll && !functions.count(call->getCalledFunction())) continue;
        calls.push_back(call);
      }
    }

    // Inline each of the collected calls.
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

Pass* createNoiseInlinerPass(SmallVector<std::string, 2> &fnNames) {
  return new NoiseInliner(fnNames);
}

char NoiseInliner::ID = 0;

} // namespace llvm

INITIALIZE_PASS_BEGIN(NoiseInliner, "noise-inline",
                      "Forces inlining of calls", false, false)
INITIALIZE_PASS_END(NoiseInliner, "noise-inline",
                    "Forces inlining of calls", false, false)
