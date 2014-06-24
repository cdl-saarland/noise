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
  NoiseInliner.cpp
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

find_package( WFV2 QUIET )
if( WFV2_FOUND )
  include_directories(${WFV2_INCLUDE_DIR})
  add_definitions(-DCOMPILE_NOISE_WFV_WRAPPER)
  if( MSVC )
    target_link_libraries(clangCodeGen ${WFV2_LIBRARIES})
    add_definitions ( "-DWFV_LIB" )
    add_definitions ( "-DWFV_STATIC_LIBS" )
    message("Using MSVC linking")
  else()
    target_link_libraries(clangCodeGen ${WFV2_LIBRARIES} pthread dl m)
  endif()
  message("-- Found WFV: " ${WFV2_LIBRARIES})
else()
  message("-- ERROR: Could not find WFV - Disabled!")
endif()

