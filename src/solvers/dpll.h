#pragma once

#include <vector>
#include <set>
#include <unordered_map>
#include <utility>

class Formula {
public:
    // Vector that stores all clauses, where each clause is a vector of literals
    // Polarity (positive or negative) of each literal is stored in the literals vector
    std::vector<std::vector<int>> clauses;
    
    // Maps variable index to its assignment (-1: unassigned, 0: true, 1: false)
    std::vector<int> literals;
    
    // Literal frequency for branching heuristics
    std::vector<int> literal_frequency;
    
    // Polarity bias (positive occurrences - negative occurrences)
    // Useful to know what to branch on
    std::vector<int> literal_polarity;
    
    Formula() {}
    
    Formula(const Formula& f) : 
        clauses(f.clauses), 
        literals(f.literals),
        literal_frequency(f.literal_frequency),
        literal_polarity(f.literal_polarity) {}
};


class DPLL {
public:
    std::pair<bool, std::vector<int>> solve(const std::vector<std::vector<int>>& cnf);

private:
    // Returns 0 if normal exit, 1 if satisfied, -1 if unsatisfied
    int unit_propagate(Formula& f);
    
    // Applies the value of a literal to all clauses
    // Returns 0 if normal exit, 1 if satisfied, -1 if unsatisfied
    int apply_transform(Formula& f, int literal_index);
    
    // Recursive DPLL implementation
    // Returns 0 if normal exit, 2 if completed with result
    int dpll_recursive(Formula f);
    
    // Converts the result to the expected return format
    std::pair<bool, std::vector<int>> prepare_result(const Formula& f, bool is_sat);
}; 