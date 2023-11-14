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
#include <unordered_set>
#include <fstream>
#include <string> 
#include <nlohmann/json.hpp>

using namespace SVF;
using json = nlohmann::json;

typedef struct PointersPlus {
    const llvm::Value *value;
    unsigned line;
    BasicBlock *block;
    std::pair<unsigned, unsigned> *unsafe;
} PointersPlus;

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

std::unordered_map<const llvm::Value*, std::vector<PointersPlus>> reverseMapPointsToSets(
    Andersen *ander,
    Module &modu,
    const std::vector<PointsTo>& pointsToSets,
    const std::vector<PointersPlus> &pointers_lines
    ) {

    std::unordered_map<const llvm::Value*, std::vector<PointersPlus>> reverseMap;
    std::unordered_set<const llvm::Value *> original_pointers_set;
    for (auto ptline : pointers_lines) {
        original_pointers_set.emplace(ptline.value);
    }

    for (size_t i = 0; i < pointsToSets.size(); ++i) {
        const PointsTo& pts = pointsToSets[i];
        PointersPlus pt_line = pointers_lines[i];

        for (NodeID nodeId : pts) {
            PAGNode* targetObj = ander->getPAG()->getGNode(nodeId);

            if (targetObj->hasValue()) {
                // Assuming a direct mapping is possible, convert SVF::SVFValue to llvm::Value*
                const llvm::Value *llvmValue = LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(targetObj->getValue());
                if (llvmValue->getName().str() == ""
                    // || original_pointers_set.find(llvmValue) != original_pointers_set.end()
                    ) {
                    break;
                }
                if (reverseMap.find(llvmValue) == reverseMap.end()) {
                    // If not, add a new entry with a vector containing the current pointer
                    reverseMap[llvmValue] = {pt_line};
                } else {
                    // If yes, append the current pointer to the existing vector
                    reverseMap[llvmValue].push_back(pt_line);
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

std::unordered_map<const llvm::Value*, std::vector<PointersPlus>> runPointerAnalysis(
    Module &modu,
    std::vector<PointersPlus> pointers_lines) {
    SVFModule* svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(modu);

    /// Build Program Assignment Graph (SVFIR)
    SVFIRBuilder builder(svfModule);
    SVFIR* pag = builder.build();

    /// Create Andersen's pointer analysis
    Andersen* ander = AndersenWaveDiff::createAndersenWaveDiff(pag);

    std::vector<const llvm::Value *> pointers;
    for (auto x : pointers_lines) {
        pointers.push_back(x.value);
    }
    std::vector<PointsTo> pointToSets = getPointsToSets(ander, modu, pointers);
    std::unordered_map<const llvm::Value*, std::vector<PointersPlus>> reverseMapping = reverseMapPointsToSets(ander, modu, pointToSets, pointers_lines);

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

    assert(argc >= 2);
    std::string locationspath{argv[2]};
    std::string irpath{argv[1]};
    
    // Load the LLVM IR file.
    std::unique_ptr<llvm::Module> modu = parseIRFile(argv[1], smDiag, context);
    
    std::ifstream locationsFile(locationspath);
    if (!locationsFile.is_open()) {
        std::cerr << "Error: Unable to open locations.txt" << std::endl;
        return 1;
    }

    std::string line;
    // [(filename, (unsafe_start, unsafe_end))]
    std::vector<std::pair<std::string, std::vector<std::pair<unsigned, unsigned>>> > locations;

    std::string filename = "";
    std::vector<std::pair<unsigned, unsigned>> range;
    while (std::getline(locationsFile, line)) {
        int start, end;
        if (sscanf(line.c_str(), "(%u,%u)", &start, &end) == 2) {
            if (filename == "") {break;} // we have some issue
            range.push_back(std::make_pair(start, end));
        }
        else {
            if (filename != "") {
                locations.push_back(std::make_pair(filename, range));
                range = {};
            }
            filename = line;
        }
    }
    if (filename != "") {
        locations.push_back(std::make_pair(filename, range));
    }

    // Close the locations file
    locationsFile.close();

    // [{filename : [{ alloc: line, pointers: [{name : _, line : _}]}]}]
    json output = json::array();

    //DEBUG stuff
    // for (auto location : locations) {
    //     std::cout << location.first << std::endl;
    //     for (auto range : location.second) {
    //         std::cout << range.first << " " << range.second << std::endl;
    //     }
    // }
    // std::cout << "Going into main loop" << std::endl;

    for (int i = 0; i < locations.size(); i++) {
        const std::string& filename = locations[i].first;
        std::vector<std::pair<unsigned, unsigned>>& ranges = locations[i].second;

        if (!modu) {
            // Handle any parsing errors here.
            smDiag.print("LLVM IR Parsing Error", llvm::errs());
            return 1;
        }

        std::unordered_map<const llvm::Value*, std::vector<PointersPlus>> reverseMapping;
        std::vector<PointersPlus> pointers_lines;

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
                                    for (std::pair<unsigned, unsigned> &range : ranges) {
                                        int unsafe_start = range.first;
                                        int unsafe_end = range.second;
                                        if (line >= unsafe_start && line <= unsafe_end) {
                                            // instruction.print(debugOut);
                                            // std::cout << std::endl;
                                            std::vector<const llvm::Value *> pointers;
                                            collectPointerValues(&instruction, pointers);
                                            for (auto ptr : pointers) {
                                                pointers_lines.push_back({ptr, line, &block, &range});
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

        // STEP 2: for each unsafe pointer, run pointer analysis
        reverseMapping = runPointerAnalysis(*modu, pointers_lines);
        json alloc_arr = json::array();

        // STEP 3: find the location of the allocations that have unsafe pointers to them
        for (const auto& mapping : reverseMapping) {
            const llvm::Value* allocsite = mapping.first; // allocation results from analysis
            std::cout << "Results' value: " << allocsite->getName().str() << std::endl;
            for (Function& func : *modu) {
                for (BasicBlock& block : func) {
                    bool allocaflag = false; // flag set up if we encountered an alloca on current allocsite
                    for (Instruction& instruction : block) {
                        // Get pointers from an instruction
                        std::vector<const llvm::Value *> values;
                        // Value * equality implies Value equality
                        collectValues(&instruction, allocsite, values);
                        for (const llvm::Value *v : values) {
                            // std::cout << "HURRAY" << std::endl;
                            // Check if this is a variable declaration/definition
                            if (llvm::isa<llvm::AllocaInst>(&instruction) || llvm::isa<llvm::GlobalVariable>(allocsite)) {
                                // We found an alloca for current allocsite, but does it have debug info???
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
                                            // We found the allocsite's line!
                                            // Set flag down since we found the line for alloca
                                            allocaflag = false;
                                            unsigned line = dbgLoc->getLine();
                                            // Construct json unsafe pointers array
                                            std::unordered_set<json> pointers_set;
                                            for (auto pt_line : mapping.second) {
                                                std::cout << "Pointer: " << allocsite->getName().str() << " defined at line " << line << std::endl;
                                                // Ignore pointers from the same block AND ignore this allocsite if it's in the same unsafe region
                                                if (pt_line.block == &block
                                                    || (line >= pt_line.unsafe->first && line <= pt_line.unsafe->second)) {
                                                    continue;
                                                }
                                                if (allocsite->getName().str() == pt_line.value->getName().str() && line == pt_line.line) {
                                                    std::cout << "Pointer: " << allocsite->getName().str() << " defined at line " << line << " ptr value " << pt_line.value << " cur val " << v << " ptr block " << pt_line.block << " cur block " << &block << std::endl;
                                                }
                                                json pt_obj = {{"name", pt_line.value->getName().str()}, {"line", pt_line.line}};
                                                pointers_set.emplace(pt_obj);
                                            }
                                            if (pointers_set.size() == 0) { continue; }
                                            json pointers(pointers_set);
                                            alloc_arr.push_back({{"allocvar", allocsite->getName().str()}, {"allocline", line}, {"pointers", pointers}});
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        output.push_back({{"filename", filename}, {"results", alloc_arr}});
    }
    std::ofstream outfile;
    outfile.open("results.json");
    outfile << output << std::endl;
    outfile.close();

    // Cleanup
    llvm::llvm_shutdown();
    return 0;
}
