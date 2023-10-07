{ stdenv
, runCommand
, lib
, cmake
, coreutils
, python3
, git
, fetchFromGitHub
, ninja
}:

stdenv.mkDerivation rec {
    pname = "llvm-project";
    version = "unstable-2023-05-02";
    requiredSystemFeatures = [ "big-parallel" ];
    nativeBuildInputs = [ cmake ninja python3 ];
    src = fetchFromGitHub {
      owner = "llvm";
      repo = pname;
      rev = "b2417f51dbbd7435eb3aaf203de24de6754da50e";
      hash = "sha256-1pIULcViMIINrFDnpUyGnKyA0HvFawjh0HzWU/WshiM=";
    };
    cmakeDir = "../llvm";
    cmakeFlags = [
      "-DLLVM_ENABLE_BINDINGS=OFF"
      "-DLLVM_ENABLE_OCAMLDOC=OFF"
      "-DLLVM_BUILD_EXAMPLES=OFF"
      "-DLLVM_ENABLE_PROJECTS=mlir;clang"
      "-DLLVM_TARGETS_TO_BUILD=host;RISCV"
      "-DLLVM_INSTALL_UTILS=ON"
    ];
    checkTarget = "check-mlir check-clang";
    }
