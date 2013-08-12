set(LLVM_LINK_COMPONENTS
  asmparser
  bitreader
  bitwriter
  irreader
  instrumentation
  ipo
  linker
  vectorize
  )

add_clang_library(clangCodeGen
  BackendUtil.cpp
  CGAtomic.cpp
  CGBlocks.cpp
  CGBuiltin.cpp
  CGCall.cpp
  CGClass.cpp
  CGCUDANV.cpp
  CGCUDARuntime.cpp
  CGCXX.cpp
  CGCXXABI.cpp
  CGCleanup.cpp
  CGDebugInfo.cpp
  CGDecl.cpp
  CGDeclCXX.cpp
  CGException.cpp
  CGExpr.cpp
  CGExprAgg.cpp
  CGExprComplex.cpp
  CGExprConstant.cpp
  CGExprCXX.cpp
  CGExprScalar.cpp
  CGNoise.cpp
  CGObjC.cpp
  CGObjCGNU.cpp
  CGObjCMac.cpp
  CGObjCRuntime.cpp
  CGOpenCLRuntime.cpp
  CGRecordLayoutBuilder.cpp
  CGRTTI.cpp
  CGStmt.cpp
  CGVTables.cpp
  CGVTT.cpp
  CodeGenAction.cpp
  CodeGenFunction.cpp
  CodeGenModule.cpp
  CodeGenTBAA.cpp
  CodeGenTypes.cpp
  ItaniumCXXABI.cpp
  LoopAnalysis.cpp
  MicrosoftCXXABI.cpp
  ModuleBuilder.cpp
  NoiseAttrParser.cpp
  NoiseFusion.cpp
  NoiseOptimization.cpp
  NoiseOptimizer.cpp
  NoiseSpecializer.cpp
  NoiseWFVWrapper.cpp
  TargetInfo.cpp
  )

add_dependencies(clangCodeGen
  ClangARMNeon
  ClangAttrClasses
  ClangAttrList
  ClangCommentNodes
  ClangDeclNodes
  ClangDiagnosticCommon
  ClangDiagnosticFrontend
  ClangStmtNodes
  )

target_link_libraries(clangCodeGen
  clangBasic
  clangAST
  clangFrontend
  )

#
# Check if WFV is available & set flags etc. accordingly if so
#

set(WFV_POSSIBLE_LIBS WFV.lib WFV.so WFV.dll libWFV libWFV.so libWFV.a libWFV.dll)
find_path(WFV_INCLUDE_DIR NAMES wfvInterface.h wfvInterface_C.h PATHS $ENV{WFV_INSTALL_DIR}/include)
find_path(WFV_LIBRARY_DIR NAMES ${WFV_POSSIBLE_LIBS} PATHS $ENV{WFV_INSTALL_DIR}/lib)

if (WFV_LIBRARY_DIR)
  find_library(WFV_LIBS NAMES ${WFV_POSSIBLE_LIBS} PATHS ${WFV_LIBRARY_DIR})
endif()

#message("WFV_POSSIBLE_LIBS: " ${WFV_POSSIBLE_LIBS})
#message("WFV_INCLUDE_DIR: " ${WFV_INCLUDE_DIR})
#message("WFV_LIBRARY_DIR: " ${WFV_LIBRARY_DIR})
#message("WFV_LIBS: " ${WFV_LIBS})

if (WFV_INCLUDE_DIR AND WFV_LIBS)
  message("-- Found WFV: " ${WFV_LIBS})
  include_directories(${WFV_INCLUDE_DIR})
  add_definitions(-DCOMPILE_NOISE_WFV_WRAPPER)
  target_link_libraries(clangCodeGen ${WFV_LIBS} pthread dl m)
else()
  message("-- ERROR: Could not find WFV - Disabled!")
endif()
