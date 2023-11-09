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
#include <unordered_map>
#include <fstream>
#include <string> 
#include <nlohmann/json.hpp>

using namespace SVF;
using json = nlohmann::json;

std::vector<PointsTo> getPointsToSets(Andersen *ander, Module &modu, const std::vector<const llvm::Value*> pointers) {
    std::vector<PointsTo> pointsToSets;
    for (const llvm::Value* val : pointers) {
        const SVFValue* svfVal = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(val);
        NodeID pNodeId = ander->getPAG()->getValueNode(svfVal);
        const PointsTo& pts = ander->getPts(pNodeId);
        pointsToSets.push_back(pts);
    }

    return pointsToSets;
}

std::unordered_map<const llvm::Value*, std::vector<const llvm::Value*>> reverseMapPointsToSets(
    Andersen *ander,
    Module &modu,
    const std::vector<PointsTo>& pointsToSets,
    const std::vector<const llvm::Value*>& pointers
    ) {

    //TODO map { Value : Vec<Value> }
    std::unordered_map<const llvm::Value*, std::vector<const llvm::Value*>> reverseMap;

    for (size_t i = 0; i < pointsToSets.size(); ++i) {
        const PointsTo& pts = pointsToSets[i];
        const llvm::Value* pointer = pointers[i];

        for (NodeID nodeId : pts) {
            PAGNode* targetObj = ander->getPAG()->getGNode(nodeId);

            if (targetObj->hasValue()) {
                // Assuming a direct mapping is possible, convert SVF::SVFValue to llvm::Value*
                const llvm::Value *llvmValue = LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(targetObj->getValue());
                //TODO do an insert into a vec or something
                if (reverseMap.find(llvmValue) == reverseMap.end()) {
                    // If not, add a new entry with a vector containing the current pointer
                    reverseMap[llvmValue] = {pointer};
                } else {
                    // If yes, append the current pointer to the existing vector
                    reverseMap[llvmValue].push_back(pointer);
                }
            }
        }
    }

    return reverseMap;
}



void collectPointerValues(llvm::Instruction *inst, std::vector<const llvm::Value *> &pointerValues) {
    if (inst->getType()->isPointerTy()) {
        pointerValues.push_back(inst);
    }
    for (llvm::Use &operand : inst->operands()) {
        if (const llvm::Value *v = operand.get()) {
            if (v->getType()->isPointerTy() && !llvm::isa<Function>(v)) {
                pointerValues.push_back(v);
            }
        }
    }
}

void collectValues(llvm::Instruction *inst, const llvm::Value *val, std::vector<const llvm::Value *> &pointerValues) {
    if (inst == val) {
        pointerValues.push_back(inst);
    }
    for (llvm::Use &operand : inst->operands()) {
        if (const llvm::Value *v = operand.get()) {
            if (v == val) {
                pointerValues.push_back(v);
            }
        }
    }
}

std::unordered_map<const llvm::Value*, std::vector<const llvm::Value*>> runPointerAnalysis(Module &modu, std::vector<const llvm::Value *> pointers) {
    SVFModule* svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(modu);

    /// Build Program Assignment Graph (SVFIR)
    SVFIRBuilder builder(svfModule);
    SVFIR* pag = builder.build();

    /// Create Andersen's pointer analysis
    Andersen* ander = AndersenWaveDiff::createAndersenWaveDiff(pag);

    std::vector<PointsTo> PointToSets = getPointsToSets(ander, modu, pointers);
    std::unordered_map<const llvm::Value*, std::vector<const llvm::Value*>> reverseMapping = reverseMapPointsToSets(ander, modu, PointToSets, pointers);

    // Cleanup
    AndersenWaveDiff::releaseAndersenWaveDiff();
    SVFIR::releaseSVFIR();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();

    return reverseMapping;
}


int main(int argc, char *argv[]) {
    // Initialize the LLVM context and create a source manager.
    llvm::LLVMContext context;
    llvm::SMDiagnostic smDiag;
    llvm::raw_os_ostream debugOut(std::cout);

    assert(argc >= 4);
    
    // Load the LLVM IR file.
    std::unique_ptr<llvm::Module> modu = parseIRFile(argv[1], smDiag, context);
    
    //FIXME un-hardcode this shit
    std::ifstream locationsFile("../io/locations.txt");
    if (!locationsFile.is_open()) {
        std::cerr << "Error: Unable to open locations.txt" << std::endl;
        return 1;
    }

    std::string line;
    // [(filename, (unsafe_start, unsafe_end))]
    std::vector<std::pair<std::string, std::vector<std::pair<int, int>>> > locations;

    //FIXME we never get more than the first filename
    while (std::getline(locationsFile, line)) {
        std::string filename = line;
        std::vector<std::pair<int, int>> range;
        while (std::getline(locationsFile, line) && !line.empty()) {
            int start, end;
            if (sscanf(line.c_str(), "(%d,%d)", &start, &end) == 2) {
                range.push_back(std::make_pair(start, end));
            }
        }

        locations.push_back(std::make_pair(filename, range));
    }

    // Close the locations file
    locationsFile.close();

    //DEBUG stuff
    for (auto location : locations) {
        std::cout << location.first << std::endl;
        for (auto range : location.second) {
            std::cout << range.first << " " << range.second << std::endl;
        }
    }
    std::cout << "Going into main loop" << std::endl;

    for (int i = 0; i < locations.size(); i++) {
        const std::string& filename = locations[i].first;
        const std::vector<std::pair<int, int>>& ranges = locations[i].second;

        //FIXME this doesn't make sense????? You need do a find() or something instead of equals.
        // Issue here is that you're only considering the i'th range, but we need to consider all ranges for this location!!
        int unsafe_start = ranges[i].first;
        int unsafe_end = ranges[i].second;

        //DEBUG stuff
        std::cout << unsafe_start << " " << unsafe_end << std::endl;
        continue;

        //sscanf(locations[1].c_str(), "(%d,%d)", &unsafe_start, &unsafe_end) == 2;


        //int unsafe_start = atoi(argv[2]);
        //int unsafe_end = atoi(argv[3]);

        if (!modu) {
            // Handle any parsing errors here.
            smDiag.print("LLVM IR Parsing Error", llvm::errs());
            return 1;
        }

        std::unordered_map<const llvm::Value*, std::vector<const llvm::Value*>> reverseMapping;
        std::vector<const llvm::Value *> pointers;

        // STEP 1: Iterate through all instructions and find unsafe pointers
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
                                if (auto *dbgLoc = llvm::dyn_cast<llvm::DILocation>(metadata)) {
                                    unsigned line = dbgLoc->getLine();
                                    // Compare the instruction's position to the unsafe blocks
                                    //TODO are there cases where there isn't metadata, but we know current basic block is inside unsafe?
                                    if (line >= unsafe_start && line <= unsafe_end) {
                                        // instruction.print(debugOut);
                                        // std::cout << std::endl;
                                        collectPointerValues(&instruction, pointers);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // STEP 2: for each unsafe pointer, run pointer analysis
        reverseMapping = runPointerAnalysis(*modu, pointers);

        // [{filename : { alloc : [{name : _, line : _}]}}]
        // STEP 3: find the location of the allocations that have unsafe pointers to them
        for (const auto& mapping : reverseMapping) {
            const llvm::Value* llvmValue = mapping.first; // allocation results from analysis
            std::cout << "Results' value: " << llvmValue->getName().str() << std::endl;
            bool allocaflag = false; // flag set up if we encountered an alloca on current llvmValue
            for (Function& func : *modu) {
                for (BasicBlock& block : func) {
                    for (Instruction& instruction : block) {
                        // Get pointers from an instruction
                        std::vector<const llvm::Value *> values;
                        // Value * equality implies Value equality
                        collectValues(&instruction, llvmValue, values);
                        for (const llvm::Value *v : values) {
                            // std::cout << "HURRAY" << std::endl;
                            // Check if this is a variable declaration/definition
                            if (llvm::isa<llvm::AllocaInst>(&instruction) || llvm::isa<llvm::GlobalVariable>(llvmValue)) {
                                // We found an alloca for current llvmValue, but does it have debug info???
                                // Set flag up by default
                                allocaflag = true;
                            }
                            if (allocaflag) { // catch all for conditions to print debug info line
                                // Check if has metadata
                                if (instruction.hasMetadata()) {
                                    llvm::SmallVector<std::pair<unsigned, llvm::MDNode*>> smallvec{};
                                    instruction.getAllMetadata(smallvec);
                                    for (auto& mdpair : smallvec) {
                                        llvm::MDNode* metadata = mdpair.second;
                                        if (auto* dbgLoc = llvm::dyn_cast<llvm::DILocation>(metadata)) {
                                            // Set flag down since we found the line for alloca
                                            allocaflag = false;
                                            unsigned line = dbgLoc->getLine();
                                            std::cout << "Variable: " << llvmValue->getName().str() << " defined at line " << line << std::endl;
                                        }
                                    }
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
