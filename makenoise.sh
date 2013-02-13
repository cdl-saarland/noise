export LLVM_INSTALL_DIR=/home/karrenberg/proj/noise/install_debug
export WFV_INSTALL_DIR=/home/karrenberg/proj/wfv2/build/linux-debug/

# Build Clang.
make clang-only -C ../../../build_debug/ -j2
