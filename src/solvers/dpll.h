#pragma once
#include <vector>
#include <cstdint>

using Literal = int32_t;
using Variable = uint32_t;

enum class Value : uint8_t {
    FALSE = 0,
    TRUE = 1,
    UNDEF = 2
};

class DPLLSolver {
public:
    DPLLSolver(const std::vector<std::vector<Literal>>& input_clauses);
    std::pair<bool, std::vector<Literal>> solve();
    uint32_t getNumDecisions() const;
    uint32_t getNumPropagations() const;
private:
    std::vector<std::vector<Literal>> clauses;
    std::vector<Value> assignment;
    std::vector<std::vector<uint32_t>> pos_occurrences;
    std::vector<std::vector<uint32_t>> neg_occurrences;
    uint32_t num_vars;
    uint32_t num_decisions;
    uint32_t num_propagations;

    bool dpll();
    bool unitPropagate();
    void pureLiteralEliminate();
    bool isClauseSatisfied(uint32_t clauseIdx) const;
    bool allClausesSatisfied() const;
    Variable pickBranchVariable();
}; 