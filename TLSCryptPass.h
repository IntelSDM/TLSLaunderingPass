#pragma once

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"

struct TLSCryptPass : llvm::PassInfoMixin<TLSCryptPass>
{
    llvm::PreservedAnalyses run(llvm::Module& m, llvm::ModuleAnalysisManager&);
};

bool RunTLSCrypt(llvm::Module& m);

extern llvm::cl::opt<bool> TLSCryptEnable;