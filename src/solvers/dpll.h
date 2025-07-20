#pragma once
#include <vector>
#include <cstdint>
#include <unordered_map>

class DPLLSolver
{
public:
    DPLLSolver(const std::vector<std::vector<int32_t>> &clauses);
    std::pair<bool, std::vector<int32_t>> solve();
    uint32_t getNumDecisions() const;
    uint32_t getNumPropagations() const;

private:
    enum class Value
    {
        FALSE,
        TRUE,
        UNDEF
    };

    struct Watch
    {
        int32_t literal;
        uint32_t clause_idx;

        Watch(int32_t lit, uint32_t idx) : literal(lit), clause_idx(idx) {}
    };

    std::vector<std::vector<int32_t>> clauses;
    std::vector<Value> assignment;
    uint32_t num_vars;
    uint32_t num_decisions;
    uint32_t num_propagations;

    // Variable mapping
    std::unordered_map<int32_t, uint32_t> var_to_idx;
    std::vector<int32_t> idx_to_var;

    // Watched literals data structures
    std::vector<std::vector<Watch>> pos_watches;             // Watches for positive literals
    std::vector<std::vector<Watch>> neg_watches;             // Watches for negative literals
    std::vector<std::pair<int32_t, int32_t>> clause_watches; // Which literals we're watching in each clause

    bool dpll(int depth = 0);
    bool unitPropagate();
    void pureLiteralEliminate();
    bool isClauseSatisfied(uint32_t clauseIdx) const;
    bool allClausesSatisfied() const;
    uint32_t pickBranchVariable();

    // New helper methods for watched literals
    void initWatches();
    bool findNewWatch(uint32_t clause_idx, int32_t false_lit);
    void addWatch(int32_t lit, uint32_t clause_idx);
    bool propagateLiteral(int32_t lit);
    Value getLiteralValue(int32_t lit) const;
    std::vector<std::vector<int32_t>> removeTautologies(const std::vector<std::vector<int32_t>> &input_clauses);
};