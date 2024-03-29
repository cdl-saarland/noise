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
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"
#include "llvm/Transforms/Utils/Cloning.h" // CloneFunction()
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h" // FunctionType
#include "llvm/IR/Constants.h" // UndefValue
#include "llvm/IR/Instructions.h" // CallInst

#include "NoiseInliner.h"

#include <iostream>
#include <sstream>

using namespace clang;
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

MDNode* getCompoundStmtNoiseMD(const BasicBlock& block)
{
  return block.getTerminator()->getMetadata("noise_compound_stmt");
}

const MDNode* getNoiseFunctionAttributeMDN(const Function&    function,
                                           const NamedMDNode& MD)
{
  for (unsigned i=0, e=MD.getNumOperands(); i<e; ++i) {
    const MDNode* functionMDN = MD.getOperand(i);
    const Function* noiseFn = GetNoiseFunction(functionMDN);
    if (noiseFn == &function) return functionMDN;
  }

  return 0;
}

} // unnamed namespace

namespace llvm {

void initializeNoiseExtractorPass(PassRegistry&);

struct NoiseExtractor : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid

  noise::NoiseFnInfoVecType *noiseFnInfoVec;
  NamedMDNode               *MD;
  SmallSet<Function*, 64>    createdFunctions;
  Module                    *Mod;
  LLVMContext               *Context;
  noise::NoiseDiagnostics   *Diag;

  NoiseExtractor(noise::NoiseFnInfoVecType *NoiseFuncInfoVec=0,
                 NamedMDNode               *MdNode=0,
                 noise::NoiseDiagnostics   *Diag = 0)
   : FunctionPass(ID), noiseFnInfoVec(NoiseFuncInfoVec), MD(MdNode), Diag(Diag)
  {
    initializeNoiseExtractorPass(*PassRegistry::getPassRegistry());
  }

  virtual ~NoiseExtractor()
  { }

  template<unsigned SetSize>
  bool resolveMarkers(BasicBlock*                        block,
                      SmallPtrSet<BasicBlock*, SetSize>& visitedBlocks)
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
            if (resolveMarkers<SetSize>(*it, visitedBlocks))
            {
                iterate = true;
                break;
            }
        }
    }

    // Things currently break if there is a return statement inside the region,
    // so we forbid this.
    for (typename SmallPtrSet<BasicBlock*, SetSize>::iterator it=region.begin(),
         E=region.end(); it!=E; ++it)
    {
      if (!isa<ReturnInst>((*it)->getTerminator())) continue;

      Diag->Report(Diag->err_invalid_nested_return) << (*it)->getParent()->getName();
    }

    Diag->TerminateOnError();

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
    noise::NoiseFnInfo* nfi = new noise::NoiseFnInfo(extractedFn, call, true);
    noiseFnInfoVec->push_back(nfi);

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
        if (resolveMarkers(BB, visitedBlocks))
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

char NoiseExtractor::ID = 0;

} // namespace llvm

INITIALIZE_PASS_BEGIN(NoiseExtractor, "noise-extract",
                      "Extract code blocks into noise functions", false, false)
INITIALIZE_PASS_END(NoiseExtractor, "noise-extract",
                    "Extract code blocks into noise functions", false, false)

namespace llvm {
namespace noise {

// NoiseFnInfo

void NoiseFnInfo::UpdateOptDesc(MDNode* OptDesc, NoiseDiagnostics &Diag)
{
  // according to the description from NoiseOptimization.h
  size_t numOps = OptDesc->getNumOperands();
  for (size_t i = 0; i < numOps; ++i)
  {
    Value *value = OptDesc->getOperand(i);
    if (!isa<NoiseOptimization>(value))
      Diag.Report(Diag.err_invalid_opt) << value;
  }

  mOptDesc = OptDesc;
}

NoiseOptimization* NoiseFnInfo::GetOptimization(size_t i) {
  assert( isa<NoiseOptimization>(mOptDesc->getOperand(i)) );
  return cast<NoiseOptimization>(mOptDesc->getOperand(i));
}

size_t NoiseFnInfo::GetNumOptimizations() const {
  return mOptDesc->getNumOperands();
}

// Noise Optimizer

NoiseOptimizer::NoiseOptimizer(llvm::Module *M, clang::DiagnosticsEngine &Diag)
  : NoiseDiagnostics(Diag)
  , Mod(M)
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
        // Handle global values.
        for (Instruction::op_iterator O=I->op_begin(), OE=I->op_end(); O!=OE; ++O)
        {
          Value* opVal = cast<Value>(*O);
          if (isa<Function>(opVal)) continue;
          if (isa<BasicBlock>(opVal)) continue;

          if (isa<GlobalValue>(opVal))
          {
            values.push_back(opVal);
          }

          if (!isa<ConstantExpr>(opVal)) continue;
          ConstantExpr* ce = cast<ConstantExpr>(opVal);

          for (ConstantExpr::op_iterator O2=ce->op_begin(), OE2=ce->op_end(); O2!=OE2; ++O2)
          {
            Value* opVal2 = cast<Value>(*O2);
            if (!isa<GlobalValue>(opVal2)) continue;
            values.push_back(opVal2);
          }
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

void createDummyVarNameCalls(Module*            module,
                             const NamedMDNode& MD,
                             NoiseDiagnostics &Diag)
{
  // Handle noise specialize attributes.
  for (Module::iterator F=module->begin(), FE=module->end(); F!=FE; ++F)
  {
    // First, find out for which variables per function we have to generate
    // dummy function calls.
    SmallSet<std::string, 2> specializeVarNames;

    // Check noise strings from function metadata for passes that need a variable name.
    const MDNode* noiseFnAttrMDN = getNoiseFunctionAttributeMDN(*F, MD);
    if (noiseFnAttrMDN)
    {
      MDNode* noiseDescStrs = cast<MDNode>(noiseFnAttrMDN->getOperand(1)); // 0 = function, 1 = desc strings
      for (unsigned i=0, e=noiseDescStrs->getNumOperands(); i<e; ++i)
      {
        NoiseOptimization* noiseOpt = cast<MDNode>(noiseDescStrs->getOperand(i));
        NoiseOptimizationInfo info(noiseOpt, Diag);
        if (info.GetType() != NOISE_OPTIMIZATION_TYPE_SPECIALIZE)
          continue;
        StringRef passArg = info.GetArgAsString(0);
        specializeVarNames.insert(passArg.str());
      }
    }

    // Check noise strings from compound metadata for passes that need a variable name.
    bool hasNoiseCmp = false;
    for (Function::const_iterator BB = F->begin(), BBE=F->end(); BB!=BBE; ++BB)
    {
      MDNode* noiseMD = getCompoundStmtNoiseMD(*BB);
      if (!noiseMD) continue;
      hasNoiseCmp = true;
      MDNode* noiseDescStrs = cast<MDNode>(noiseMD->getOperand(2)); // 0 = entry, 1 = exit, 2 = desc strings
      for (unsigned i=0, e=noiseDescStrs->getNumOperands(); i<e; ++i)
      {
        NoiseOptimization* noiseOpt = cast<MDNode>(noiseDescStrs->getOperand(i));
        NoiseOptimizationInfo info(noiseOpt, Diag);
        if (info.GetType() != NOISE_OPTIMIZATION_TYPE_SPECIALIZE)
          continue;
        specializeVarNames.insert(info.GetArgAsString(0).str());
      }
    }

    // If there was no noise metadata, skip this function.
    if (!noiseFnAttrMDN && !hasNoiseCmp) continue;

    // Generate dummy calls to retain variable name mapping after SROA.
    for (Function::iterator BB=F->begin(), BBE=F->end(); BB!=BBE; ++BB)
    {
      for (BasicBlock::iterator I=BB->begin(), IE=BB->end(); I!=IE; ++I)
      {
        if (!isa<AllocaInst>(I)) continue;
        if (!I->hasMetadata()) continue;

        MDNode* noiseVarNameMD = I->getMetadata("noise_varname");
        if (!noiseVarNameMD) continue;

        assert (noiseVarNameMD->getNumOperands() == 1);
        assert (isa<MDString>(noiseVarNameMD->getOperand(0)));
        MDString* varNameMDS = cast<MDString>(noiseVarNameMD->getOperand(0));
        std::string varName = varNameMDS->getString().str();

        if (!specializeVarNames.count(varName)) continue;

        std::stringstream sstr;
        sstr << "__noise_specialize_" << varName;
        const std::string& specializeFnName = sstr.str();

        if (module->getFunction(specializeFnName))
        {
          DiagnosticBuilder builder = Diag.Report(Diag.err_specialize_multiple_var_with_same_name);
          builder.AddString(varName);
        }

        Type* type = I->getType();
        FunctionType* fType = FunctionType::get(type->getPointerElementType(),
                                                type->getPointerElementType(),
                                                false);

        Function* dummyFn = Function::Create(fType,
                                             Function::ExternalLinkage,
                                             specializeFnName,
                                             module);
        dummyFn->setDoesNotAccessMemory();
        dummyFn->setDoesNotThrow();

        DominatorTree domTree;
        domTree.runOnFunction(*F);
        StoreInst* firstStore = 0;
        Value* specializedVal = 0;
        BasicBlock* curBlock = 0;
        for(Value::use_iterator it = I->use_begin(), e = I->use_end(); it != e; ++it)
        {
          if(!isa<StoreInst>(*it)) continue;
          StoreInst* storeI = cast<StoreInst>(*it);
          BasicBlock* instBlock = storeI->getParent();
          if(curBlock == 0 || domTree.dominates(instBlock, curBlock))
            curBlock = instBlock;
          else if(domTree.dominates(curBlock, instBlock))
            continue;
          else
          {
            // Reset block as this block cannot contain the first store
            curBlock = 0;
          }

          // Remember store values
          assert (storeI->getPointerOperand() == I);
          firstStore = storeI;
          specializedVal = storeI->getValueOperand();
        }
        if (!curBlock)
        {
          DiagnosticBuilder builder = Diag.Report(Diag.err_specialize_no_use_of_specialized_var);
          builder.AddString(varName);
          continue;
        }
        assert (specializedVal);

        CallInst* call = CallInst::Create(dummyFn,
                                          ArrayRef<Value*>(specializedVal),
                                          "specializeCall", I);
        call->setDoesNotAccessMemory();
        call->setDoesNotThrow();

        // In the first reachable use of I that is a store,
        // replace the operand by our call.
        Value* op = firstStore->getOperand(0);
        if (!dyn_cast<ConstantInt>(op) && !dyn_cast<Argument>(op) && !dyn_cast<AllocaInst>(op) && !dyn_cast<LoadInst>(op))
        {
          DiagnosticBuilder builder = Diag.Report(Diag.err_specialize_no_use_of_specialized_var);
          builder.AddString(varName);
          continue;
        }
        // Wire our specialization function
        firstStore->setOperand(0, call);
        // Place the instruction before the origin I
        I->moveBefore(call);
      }
    }
    Diag.TerminateOnError();
  }
}

} // unnamed namespace

// TODO: Support "negative" noise attributes (e.g. "subtraction" of specified
//       passes from O3).
void NoiseOptimizer::PerformOptimization()
{
  // Initialize all passes linked into all libraries (see InitializePasses.h).
  // This way, they are registered so we can add them via getPassInfo().
  PassRegistry &registry = *PassRegistry::getPassRegistry();
  initializeCore(registry);
  initializeTransformUtils(registry);
  initializeScalarOpts(registry);
  initializeVectorization(registry);
  initializeInstCombine(registry);
  initializeIPO(registry);
  initializeInstrumentation(registry);
  initializeAnalysis(registry);
  initializeIPA(registry);
  initializeCodeGen(registry);
  initializeTarget(registry);

  PrettyStackTraceString CrashInfo("NOISE: Optimizing functions");

  // Before transforming to SROA, create dummy calls for phases like
  // specialize that need to have a mapping of variable names to SSA
  // values.
  createDummyVarNameCalls(Mod, *MD, *this);

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
    PM.add(createLoopSimplifyPass());
    PM.add(createIndVarSimplifyPass());
    PM.run(*Mod);
  }

  // Extract noise code regions from compound statements into separate functions.
  // These functions look exactly like functions with noise function attribute.
  {
    PassManager PM;
    PM.add(new NoiseExtractor(&noiseFnInfoVec, MD, this));
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

    nfi->UpdateOptDesc(GetNoiseOptDesc(functionMDN), *this);
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
    NoiseFnInfo* nfi     = noiseFnInfoVec[i];
    Function*    noiseFn = nfi->mReinline ? nfi->mOrigFn : nfi->mMovedFn;

    assert (!nfi->mReinline || !nfi->mMovedFn);

    // Remove exactly the blocks and instructions that we introduced in CGNoise.cpp.
    // NOTE: Using CFG simplification instead makes problems with WFV (or any other loop optimization).
    //       Bug #1377 shows an example where this results in an if-statement at
    //       the end of the loop body getting converted into 2 back edges. The
    //       following loop simplification then creates two nested loops, resulting
    //       in WFV not being able to find a canonical induction variable anymore.
    SmallVector<BasicBlock*, 2> eraseVec;
    for (Function::iterator BB=noiseFn->begin(), BBE=noiseFn->end(); BB!=BBE; ++BB)
    {
      TerminatorInst* ti = BB->getTerminator();
      if (!getCompoundStmtNoiseMD(*BB) && !ti->getMetadata("noise_tmp_block")) continue;
      if (BB->getInstList().size() != 1) continue;
      assert (ti->getNumSuccessors() == 1 && "expected noise tmp block to have exactly one successor!");

      for (pred_iterator P=pred_begin(BB), PE=pred_end(BB); P!=PE; ++P)
      {
        BasicBlock* predBB = *P;
        BasicBlock* succBB = ti->getSuccessor(0);
        TerminatorInst* predTI = predBB->getTerminator();

        for (unsigned i=0, e=predTI->getNumSuccessors(); i<e; ++i)
        {
          if (predTI->getSuccessor(i) != BB) continue;
          predTI->setSuccessor(i, succBB);
        }
      }

      eraseVec.push_back(BB);
    }
    for (SmallVector<BasicBlock*, 2>::iterator it=eraseVec.begin(),
         E=eraseVec.end(); it!=E; ++it)
    {
      (*it)->eraseFromParent();
    }

    outs() << "Running noise optimizations on function '" << noiseFn->getName() << "': \n";

    // Run requested noise passes.
    NoiseOptimizations optimizations(registry, *this);
    for(size_t i = 0, e = nfi->GetNumOptimizations(); i < e; ++i) {
      NoiseOptimization* noiseOpt = nfi->GetOptimization(i);
      optimizations.Register(noiseOpt);
    }
    FunctionPassManager NoisePasses(Mod);
    NoisePasses.add(new DataLayout(Mod));
    optimizations.Populate(NoisePasses);
    TerminateOnError();

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

    // Are there additional uses left?
    // This is required in cases in which further optimizations created additional
    // references to this function. However, we additionally track the main call (mCall)
    // to know the origin of this function
    for (Value::use_iterator it = noiseFn->use_begin(), e = noiseFn->use_end(); it != e; ++it)
    {
      CallInst* instr = cast<CallInst>(*it);
      if(instr->getParent()->getParent() != parentFn)
        InlineFunction(instr, IFI);
    }

    // Remove the now inlined noise function again.
    assert (noiseFn->use_empty());
    noiseFn->eraseFromParent();
    nfi->mMovedFn = 0;

    {
      // Perform some standard optimizations after inlining.
      FunctionPassManager PM(Mod);
      PM.add(new DataLayout(Mod));
      NoiseOptimizations defaultOpts(registry, *this);
      defaultOpts.RegisterDefaultOpts();
      defaultOpts.Populate(PM);
      PM.run(*parentFn);
      TerminateOnError();
    }
  }

  // At this point, all noise functions that were not "top level" are
  // inlined and erased.

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
}

void NoiseOptimizer::Reassemble()
{
  assert (MD->getNumOperands() != 0);

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
    if (!nfi->mCall) continue;

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
    // Caution: as the original call might be inlined, we have to check all uses
    // and NOT the stored one (as it might be invalid right now).
    // Furthermore, there may be additional calls (see comment above).
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

    {
      // Perform some standard optimizations after inlining.
      PassManager PM;
      PM.add(new DataLayout(Mod));
      NoiseOptimizations defaultOpts(*PassRegistry::getPassRegistry(), *this);
      defaultOpts.RegisterDefaultOpts();
      defaultOpts.Populate(PM);
      PM.run(*Mod);
      TerminateOnError();
    }
  }
}

void NoiseOptimizer::Finalize()
{
  // Remove noise metadata from TheModule.
  // TODO: Only if we know that there is only noise metadata inside.
  // TODO: If we don't do this, CodeGenPasses->run() fails with an assertion.
  MD->eraseFromParent();
}

}
}
