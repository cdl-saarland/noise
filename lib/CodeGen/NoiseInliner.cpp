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

#include "llvm/Pass.h"
#include "llvm/PassRegistry.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Support/raw_ostream.h"

#include "NoiseInliner.h"
#include "NoiseOptimization.h"

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
  noise::NoiseDiagnostics     *Diag;

  explicit NoiseInliner()
    : FunctionPass(ID) {
    initializeNoiseInlinerPass(*PassRegistry::getPassRegistry());
  }

  explicit NoiseInliner(SmallVector<std::string, 2> &fnNames, noise::NoiseDiagnostics &Diag)
  : FunctionPass(ID), functionNames(fnNames), Diag(&Diag) {
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
        clang::DiagnosticBuilder builder = Diag->Report(Diag->err_inline_cannot_find_func);
        builder.AddString(*it);
        continue;
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

    Diag->TerminateOnError();

    return true;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
  }
};

Pass* createNoiseInlinerPass(SmallVector<std::string, 2> &fnNames, noise::NoiseDiagnostics &Diag) {
  return new NoiseInliner(fnNames, Diag);
}

char NoiseInliner::ID = 0;

} // namespace llvm

INITIALIZE_PASS_BEGIN(NoiseInliner, "noise-inline",
                      "Inline functions", false, false)
INITIALIZE_PASS_END(NoiseInliner, "noise-inline",
                    "Inline functions", false, false)
