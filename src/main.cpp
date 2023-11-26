#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_os_ostream.h"
#include "WPA/Andersen.h"
#include "WPA/VersionedFlowSensitive.h"
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
    const char *filename;
} PointersPlus;

std::vector<PointsTo> getPointsToSets(PointerAnalysis *pa, Module &modu, const std::vector<const llvm::Value*> pointers) {
    std::vector<PointsTo> pointsToSets;
    for (const llvm::Value* val : pointers) {
        const SVFValue* svfVal = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(val);
        NodeID pNodeId = pa->getPAG()->getValueNode(svfVal);
        const PointsTo& pts = pa->getPts(pNodeId);
        pointsToSets.push_back(pts);
    }

    return pointsToSets;
}

std::unordered_map<const llvm::Value*, std::vector<PointersPlus>> reverseMapPointsToSets(
    PointerAnalysis *pa,
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
            PAGNode* targetObj = pa->getPAG()->getGNode(nodeId);

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

bool isAllocation(llvm::Instruction *inst, const llvm::Value *val) {
    //NOTE previously we casted glovalvariable for allocsite aka val
    if (!(llvm::isa<llvm::AllocaInst>(inst) || llvm::isa<llvm::GlobalVariable>(inst))) {
        return false;
    }
    if (inst == val) {
        return true;
    }
    for (llvm::Use &operand : inst->operands()) {
        if (const llvm::Value *v = operand.get()) {
            if (v == val) {
                return true;
            }
        }
    }
    return false;
}

std::vector<PointersPlus> traverseOnSVFG(const SVFG* vfg, const Value* allocval, std::vector<PointersPlus> &potentialPointers)
{
    SVFIR* pag = SVFIR::getPAG();
    SVFValue* svfval = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(allocval);

    const PAGNode* pNode = pag->getGNode(pag->getValueNode(svfval));
    const VFGNode* vNode = vfg->getDefSVFGNode(pNode);
    FIFOWorkList<const VFGNode*> worklist;
    Set<const VFGNode*> visited;
    worklist.push(vNode);

    /// Traverse along VFG
    while (!worklist.empty())
    {
        const VFGNode* vNode = worklist.pop();
        for (VFGNode::const_iterator it = vNode->OutEdgeBegin(), eit =
                    vNode->OutEdgeEnd(); it != eit; ++it)
        {
            VFGEdge* edge = *it;
            VFGNode* succNode = edge->getDstNode();
            if (visited.find(succNode) == visited.end())
            {
                visited.insert(succNode);
                worklist.push(succNode);
            }
        }
    }

    std::vector<PointersPlus> ret;

    /// Collect all LLVM Values
    for(Set<const VFGNode*>::const_iterator it = visited.begin(), eit = visited.end(); it!=eit; ++it)
    {
        const VFGNode* node = *it;
        /// can only query VFGNode involving top-level pointers (starting with % or @ in LLVM IR)
        // const PAGNode* pNode = vfg->getLHSTopLevPtr(node);
        // const Value* val = LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(pNode->getValue());
        const SVFValue *svfval = node->getValue();
        if (svfval == nullptr) { continue; }
        const Value *val = LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(svfval);
        for (auto pp : potentialPointers) {
            if (val == pp.value) {
                // std::cout << "VFG worked?? " << val->getName().str() << std::endl;
                ret.push_back(pp);
            }
        }
    }
    return ret;
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
    // FlowSensitive *vfspta = VersionedFlowSensitive::createVFSWPA(pag);
    PointerAnalysis *pa = ander;

    std::vector<const llvm::Value *> pointers;
    for (auto x : pointers_lines) {
        pointers.push_back(x.value);
    }
    std::vector<PointsTo> pointToSets = getPointsToSets(pa, modu, pointers);
    std::unordered_map<const llvm::Value*, std::vector<PointersPlus>> reverseMapping = reverseMapPointsToSets(pa, modu, pointToSets, pointers_lines);

    // Initialize value-flow analysis
    SVFGBuilder svfBuilder;
    SVFG* svfg = svfBuilder.buildFullSVFG(ander);

    // PTACallGraph* callgraph = ander->getPTACallGraph();
    // VFG *vfg = new VFG(callgraph);

    // For each allocsite, verify that all pointers in mapping can be reached via value-flow analysis
    std::unordered_map<const llvm::Value*, std::vector<PointersPlus>> ret;
    for (auto &pair : reverseMapping) {
        // std::vector<PointersPlus> pps = traverseOnVFG(vfg, pair.first, pair.second);
        std::vector<PointersPlus> pps = traverseOnSVFG(svfg, pair.first, pair.second);
        if (pps.size() > 0) {
            ret[pair.first] = pps;
        }
    }
    ret = reverseMapping;

    // Cleanup
    // delete vfg;
    VersionedFlowSensitive::releaseVFSWPA();
    AndersenWaveDiff::releaseAndersenWaveDiff();
    SVFIR::releaseSVFIR();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();

    return ret;
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

    json output = json::array();

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
                                const char *dbgfilename = dbgLoc->getScope()->getFilename().data();
                                for (int i = 0; i < locations.size(); i++) {
                                    const std::string& filename = locations[i].first;
                                    std::vector<std::pair<unsigned, unsigned>>& ranges = locations[i].second;

                                    if (dbgfilename == filename) {
                                        // Compare the instruction's position to the unsafe blocks
                                        for (std::pair<unsigned, unsigned> &range : ranges) {
                                            int unsafe_start = range.first;
                                            int unsafe_end = range.second;
                                            if (line >= unsafe_start && line <= unsafe_end) {
                                                std::vector<const llvm::Value *> pointers;
                                                collectPointerValues(&instruction, pointers);
                                                for (auto ptr : pointers) {
                                                    pointers_lines.push_back({ptr, line, &block, &range, dbgfilename});
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
        }
    }

    // STEP 2: for each unsafe pointer, run pointer analysis
    reverseMapping = runPointerAnalysis(*modu, pointers_lines);

    // STEP 3: find the location of the allocations that have unsafe pointers to them
    for (const auto& mapping : reverseMapping) {
        const llvm::Value* allocsite = mapping.first; // allocation results from analysis
        // std::cout << "Results' value: " << allocsite->getName().str() << std::endl;
        //DEBUG
        // for (auto &pp : mapping.second) {
        //     std::cout << "Debug Pointer name " << pp.value->getName().str() << std::endl;
        // }
        for (Function& func : *modu) {
            for (BasicBlock& block : func) {
                bool allocaflag = false; // flag set up if we encountered an alloca on current allocsite
                for (Instruction& instruction : block) {
                    if (!allocaflag) {
                        allocaflag = isAllocation(&instruction, allocsite);
                        // if (allocaflag) { std::cout << "found something allocated" << std::endl; }
                    }
                    if (allocaflag && instruction.hasMetadata()) { // catch all for conditions to print debug info line
                        // std::cout << "Inst has metadata alloca" << std::endl;
                        llvm::SmallVector<std::pair<unsigned, llvm::MDNode*>> smallvec{};
                        instruction.getAllMetadata(smallvec);
                        for (auto& mdpair : smallvec) {
                            llvm::MDNode* metadata = mdpair.second;
                            if (auto* dbgLoc = llvm::dyn_cast<llvm::DILocation>(metadata)) {
                                // We found the allocsite's line!
                                // Set flag down since we found the line for alloca
                                allocaflag = false;
                                unsigned line = dbgLoc->getLine();
                                const char *dbgfilename = dbgLoc->getScope()->getFilename().data();
                                // Construct json unsafe pointers array
                                std::unordered_set<json> pointers_set;
                                for (auto pt_line : mapping.second) {
                                    // std::cout << "Pointer: " << allocsite->getName().str() << " defined at line " << line << std::endl;
                                    // Ignore pointers from the same block AND ignore this allocsite if it's in the same unsafe region
                                    if (pt_line.block == &block
                                        || (strcmp(dbgfilename, pt_line.filename) == 0 && line >= pt_line.unsafe->first && line <= pt_line.unsafe->second)) {
                                        continue;
                                    }
                                    // if (allocsite->getName().str() == pt_line.value->getName().str() && line == pt_line.line) {
                                    //     std::cout << "Pointer: " << allocsite->getName().str() << " defined at line " << line << " ptr value " << pt_line.value << " cur block " << &block << std::endl;
                                    // }
                                    json pt_obj = {{"name", pt_line.value->getName().str()}, {"line", pt_line.line}, {"filename", pt_line.filename}};
                                    pointers_set.emplace(pt_obj);
                                }
                                if (pointers_set.size() == 0) { continue; }
                                json pointers(pointers_set);
                                // alloc_arr.push_back({{"allocvar", allocsite->getName().str()}, {"allocline", line}, {"filename", filename} {"pointers", pointers}});
                                output.push_back({{"allocvar", allocsite->getName().str()}, {"allocline", line}, {"filename", dbgfilename}, {"pointers", pointers}});
                            }
                        }
                    }
                    // }
                }
            }
        }
    }
    std::ofstream outfile;
    outfile.open("results.json");
    outfile << output << std::endl;
    outfile.close();

    // Cleanup
    llvm::llvm_shutdown();
    return 0;
}
