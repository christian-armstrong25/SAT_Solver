#include "dpll.h"
#include <algorithm>
#include <cmath>

std::pair<bool, std::vector<int>> DPLL::solve(const std::vector<std::vector<int>>& cnf) {
    // Initialize the formula
    Formula formula;
    
    // Count the number of variables
    int max_var = 0;
    for (const auto& clause : cnf) {
        for (int lit : clause) {
            max_var = std::max(max_var, std::abs(lit));
        }
    }
    
    // Initialize data structures
    formula.clauses = cnf;

    formula.literals.resize(max_var + 1, -1); // +1 because variables are 1-indexed
    
    formula.literal_frequency.resize(max_var + 1, 0);
    formula.literal_polarity.resize(max_var + 1, 0);
    for (const auto& clause : formula.clauses) {
        for (int lit : clause) {
            int var = std::abs(lit);
            formula.literal_frequency[var]++;
            
            if (lit > 0) {
                formula.literal_polarity[var]++;
            } else {
                formula.literal_polarity[var]--;
            }
        }
    }
    
    int result = dpll_recursive(formula);
    
    return (result == 2) ? prepare_result(formula, true) : prepare_result(formula, false);
}

int DPLL::unit_propagate(Formula& f) {
    bool unit_clause_found = false;
    
    // Check SAT
    if (f.clauses.empty()) {
        return 1;
    }
    
    do {
        unit_clause_found = false;
        
        for (int i = 0; i < f.clauses.size(); i++) {
            // Check UNSAT
            if (f.clauses[i].empty()) {
                return -1;
            }
            
            if (f.clauses[i].size() == 1) {
                int lit = f.clauses[i][0];
                int var = std::abs(lit);
                bool val = (lit > 0); 
                
                // Set the variable value (0 for true, 1 for false)
                f.literals[var] = val ? 0 : 1;
                
                f.literal_frequency[var] = -1;
                
                // Apply this change to the formula
                int transform_result = apply_transform(f, var);
                if (transform_result != 0) {
                    return transform_result;
                }
                
                unit_clause_found = true;
                break;
            }
        }
    } while (unit_clause_found);
    
    return 0;
}

int DPLL::apply_transform(Formula& f, int var) {
    int value = f.literals[var]; // 0 for true, 1 for false
    int lit_val = (value == 0) ? var : -var; // Positive if true, negative if false
    
    // For each clause
    for (int i = 0; i < f.clauses.size(); i++) {
        // For each literal in the clause
        for (int j = 0; j < f.clauses[i].size(); j++) {
            int lit = f.clauses[i][j];
            
            if (lit == lit_val) { 
                // If the literal matches our assignment
                // this clause is satisfied
                f.clauses.erase(f.clauses.begin() + i);
                i--; 
                
                // Check SAT
                if (f.clauses.empty()) {
                    return 1; 
                }
                break; 
            } 
            else if (std::abs(lit) == var) { 
                // If it's the same variable but opposite polarity
                // remove this literal from clause
                f.clauses[i].erase(f.clauses[i].begin() + j);
                j--; 
                
                // Check UNSAT
                if (f.clauses[i].empty()) {
                    return -1; 
                }
                break; 
            }
        }
    }
    
    return 0;
}

int DPLL::dpll_recursive(Formula f) {
    // Perform unit propagation
    int result = unit_propagate(f);
    
    if (result == 1) { 
        // SAT
        return 2; 
    } 
    else if (result == -1) { 
        // UNSAT
        return 0; 
    }
    
    // Find variable with maximum frequency to branch on
    int max_freq = -1;
    int max_var = -1;
    
    for (int i = 1; i < f.literal_frequency.size(); i++) {
        if (f.literal_frequency[i] > max_freq) {
            max_freq = f.literal_frequency[i];
            max_var = i;
        }
    }
    
    // If no variables to branch on
    if (max_var == -1) {
        // Check SAT
        if (f.clauses.empty()) {
            return 2; 
        }
        // Otherwise, UNSAT
        return 0; 
    }
    
    // Branch on the chosen variable
    // Try both values, do higher polarity first
    for (int j = 0; j < 2; j++) {
        Formula new_f = f; // This clones the formula
        
        // Saw this code online, very smart code. Looping through 0 and 1
        // is highkey genius here.
        // Takes higher polarity first, then other variable second
        // Since j = 0 is true, j = 1 is false
        int assignment;
        if (new_f.literal_polarity[max_var] > 0) {
            assignment = j;
        } else {
            assignment = (j + 1) % 2;
        }
        
        new_f.literals[max_var] = assignment;
        new_f.literal_frequency[max_var] = -1; 
        
        int transform_result = apply_transform(new_f, max_var);
        
        if (transform_result == 1) { 
            // SAT
            return 2; 
        } 
        else if (transform_result == -1) { 
            // UNSAT
            continue; 
        }
        
        // Recursively continue DPLL
        int dpll_result = dpll_recursive(new_f);
        if (dpll_result == 2) { 
            // SAT
            return dpll_result; 
        }
    }
    
    // If we reach here, no assignment satisfies the formula in this branch
    return 0; 
}

std::pair<bool, std::vector<int>> DPLL::prepare_result(const Formula& f, bool is_sat) {
    if (!is_sat) {
        return {false, {}};
    }
    
    std::vector<int> assignment;
    for (int i = 1; i < f.literals.size(); i++) {
        if (f.literals[i] != -1) {
            assignment.push_back((f.literals[i] == 0) ? i : -i);
        } else {
            // Unassigned vars, but formula is SAT
            // So we can set them arbitrarily to true
            assignment.push_back(i);
        }
    }
    
    return {true, assignment};
} 