#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_os_ostream.h"
#include "WPA/Andersen.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "Util/Options.h"
#include "Graphs/SVFG.h"
#include "SVF-LLVM/LLVMUtil.h"
#include <cassert>
#include <stdlib.h>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

using namespace SVF;

void runPointerAnalysis(Module &modu, std::vector<llvm::Value *> &pointers) {
    SVFModule* svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(modu);

    /// Build Program Assignment Graph (SVFIR)
    SVFIRBuilder builder(svfModule);
    SVFIR* pag = builder.build();

    /// Create Andersen's pointer analysis
    Andersen* ander = AndersenWaveDiff::createAndersenWaveDiff(pag);

    ///TODO run pointer analysis
    

    // Cleanup
    AndersenWaveDiff::releaseAndersenWaveDiff();
    SVFIR::releaseSVFIR();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();
}

std::vector<PointsTo> getPointsToSets(Module &modu, const std::vector<llvm::Value*>& pointers) {
    SVFModule* svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(modu);
    SVFIRBuilder builder(svfModule);
    SVFIR* pag = builder.build();
    Andersen* ander = AndersenWaveDiff::createAndersenWaveDiff(pag);



    std::vector<PointsTo> pointsToSets;

    for (llvm::Value* val : pointers) {
        SVFValue* svfVal = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(val);
        NodeID pNodeId = ander->getPAG()->getValueNode(svfVal);
        const PointsTo& pts = ander->getPts(pNodeId);
        pointsToSets.push_back(pts);
    }

    return pointsToSets;
}


void collectPointerValues(llvm::Instruction *inst, std::vector<llvm::Value *> &pointerValues) {
    if (inst->getType()->isPointerTy()) {
        pointerValues.push_back(inst);
    }
    for (llvm::Use &operand : inst->operands()) {
        if (llvm::Value *v = operand.get()) {
            if (v->getType()->isPointerTy() && !llvm::isa<Function>(v)) {
                pointerValues.push_back(v);
            }
        }
    }
}

int main(int argc, char *argv[]) {
    // Initialize the LLVM context and create a source manager.
    llvm::LLVMContext context;
    llvm::SMDiagnostic smDiag;
    llvm::raw_os_ostream debugOut(std::cout);

    assert(argc >= 4);
    
    // Load the LLVM IR file.
    std::unique_ptr<llvm::Module> modu = parseIRFile(argv[1], smDiag, context);
    int unsafe_start = atoi(argv[2]);
    int unsafe_end = atoi(argv[3]);

    if (!modu) {
        // Handle any parsing errors here.
        smDiag.print("LLVM IR Parsing Error", llvm::errs());
        return 1;
    }

    // TODO get ALL pointer types from instruction no matter if they're local or temporary
    // then somehow check if they exist outside of the unsafe scope
    
    // Iterate through all functions in the module and print their names.
    for (Function& func : *modu) {
        // Iterate through all basic blocks of a function
        for (BasicBlock& block : func) {
            // Not sure if this is necessary
            if (block.hasName()) {
                // Iterate through al linstructions in basic blocks
                for (Instruction& instruction : block) {
                    // Check for metadata on the instruction
                    if (instruction.hasMetadata()) {
                        llvm::SmallVector<std::pair<unsigned, llvm::MDNode *>> smallvec{};
                        // Get vec of all metadata for the instruction
                        instruction.getAllMetadata(smallvec);
                        for (auto &mdpair : smallvec) {
                            llvm::MDNode *metadata = mdpair.second;
                            // Dynamically cast to DILocation for file line information
                            // TODO look for custom metadata if we modify rustc to propagate unsafe block info
                            if (auto *dbgLoc = llvm::dyn_cast<llvm::DILocation>(metadata)) {
                                unsigned line = dbgLoc->getLine();
                                // Compare the instruction's position to the unsafe blocks
                                if (line >= unsafe_start && line <= unsafe_end) {
                                    instruction.print(debugOut);
                                    std::cout << std::endl;
                                    std::vector<llvm::Value *> pointers;
                                    collectPointerValues(&instruction, pointers);
                                    for (auto ptr : pointers) {
                                        std::cout << ptr->getName().data() << std::endl;
                                    }
                                    runPointerAnalysis(*modu, pointers);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // Cleanup
    llvm::llvm_shutdown();
    return 0;
}
