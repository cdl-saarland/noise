//===--- NoiseAttrParser.cpp - Noise Optimizations ------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// The parser for noise attributes
//
//===----------------------------------------------------------------------===//

#include "NoiseAttrParser.h"
#include "clang/AST/Attr.h" // NoiseAttr
#include "NoiseOptimization.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Constants.h"
#include "llvm/PassManager.h"
#include "llvm/PassRegistry.h"

namespace llvm {
namespace noise {

NoiseAttrParser::NoiseAttrParser(LLVMContext& C)
  : C(C)
{
}

NoiseAttrParser::~NoiseAttrParser()
{ }

typedef SmallVector<Value*, 8> NoiseOptimizationVec;

MDNode* NoiseAttrParser::Parse(const clang::NoiseAttr& attr)
{
  NoiseOptimizationVec noiseOpts;
  StringRef str = attr.getOpt();

  // arguments can have to following formats:
  // - passName1 passName2 ...
  // - passName1( arg1, arg2, ... ) passName2 ...
  // - passName1( arg1, arg2, ... ) passName2( arg1, arg2, ... )  ...

  // primitive parsing functionality for pass data
  // TODO: nicer way of reading input descriptions (RegExp)
  for(size_t index = str.find_first_not_of(' '), e = str.size();
          index < e && index != StringRef::npos; index = str.find_first_not_of(' ', index))
  {
    // read pass name
    size_t nextIndex = std::min(str.find(' ', index), str.find('(', index));

    NoiseOptimizationVec args;

    if(nextIndex == StringRef::npos)
      args.push_back(MDString::get(C, str.substr(index, e - index)));
    else
    {
      StringRef t = str.substr(index, nextIndex - index);
      args.push_back(MDString::get(C, t));

      // jump over whitespaces
      nextIndex = str.find_first_not_of(' ', nextIndex);

      // check for paren
      if(nextIndex != StringRef::npos && str[nextIndex] == '(')
      {
        // move to argument
        index = str.find_first_not_of(' ', ++nextIndex);

        while(str[nextIndex] != ')' && nextIndex < e)
        {
          nextIndex = std::min(str.find(',', nextIndex + 1), str.find(')', nextIndex + 1));
          if(nextIndex == StringRef::npos)
            break;

          // take argument
          StringRef arg = str.substr(index, nextIndex - index).trim(", ");

          Value* parsedArg;
          if(arg[0] == '-' || isdigit(arg[0]))
          {
            // integer argument
            int value;
            arg.getAsInteger(10, value);
            parsedArg = ConstantInt::get(C, APInt(32, value));
          }
          else
          {
            // string argument
            parsedArg = MDString::get(C, arg);
          }
          args.push_back(parsedArg);

          // move to next argument
          index = nextIndex;
        }
        // jump over additional whitespaces: b   )
        nextIndex = str.find_first_not_of(' ', nextIndex);
        if(str[nextIndex++] != ')')
          errs() << "unterminated argument list: " << str << "\n";
      }

    }

    noiseOpts.push_back(NoiseOptimizations::CreateOptimization(C, args));

    // move to next element
    index = nextIndex;
  }

  const size_t numNoiseOpts = noiseOpts.size();
  return MDNode::get(C, ArrayRef<Value*>(numNoiseOpts > 0 ? &noiseOpts[0] : 0,
          numNoiseOpts));
}

}
}
