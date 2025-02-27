#include <algorithm>
#include <vector>
#include <unordered_map>
#include <iostream>

#include "dpll.h"
using Literal = int32_t;
using Variable = uint32_t;

DPLLSolver::DPLLSolver(const std::vector<std::vector<Literal>>& input_clauses) {
    clauses = input_clauses;

    // Initialize variables
    num_vars = 0;
    for (const auto& clause : clauses) {
        for (Literal literal : clause) {
            Variable var = std::abs(literal);
            num_vars = std::max(num_vars, var);
        }
    }

    assignment.resize(num_vars + 1, Value::UNDEF);
    pos_occurrences.resize(num_vars + 1);
    neg_occurrences.resize(num_vars + 1);

    for (uint32_t i = 0; i < clauses.size(); ++i) {
        for (Literal literal : clauses[i]) {
            Variable var = std::abs(literal);
            if (literal > 0) {
                pos_occurrences[var].push_back(i);
            } else {
                neg_occurrences[var].push_back(i);
            }
        }
    }

    num_decisions = 0;
    num_propagations = 0;
}

std::pair<bool, std::vector<Literal>> DPLLSolver::solve() {
    bool is_sat = dpll();
    std::cout << "is_sat: " << is_sat << std::endl;
    if (!is_sat) {
        return {false, std::vector<Literal>()};
    }
    
    std::vector<Literal> result;
    for (Variable var = 1; var <= num_vars; ++var) {
        if (assignment[var] != Value::UNDEF) {
            result.push_back(assignment[var] == Value::TRUE ? var : -var);
        }
    }
    return {true, result};
}

bool DPLLSolver::dpll() {
    // Save the current assignment state
    std::vector<Value> saved_assignment = assignment;
    
    if (!unitPropagate()) {
        assignment = saved_assignment;  // Restore state
        return false;
    }

    pureLiteralEliminate();
    
    if (allClausesSatisfied()) {
        return true;
    }
    
    Variable var = pickBranchVariable();
    num_decisions++;
    
    assignment[var] = Value::TRUE;
    if (dpll()) {
        return true;
    }
    
    // Restore state before trying FALSE
    assignment = saved_assignment;
    assignment[var] = Value::FALSE;
    if (dpll()) {
        return true;
    }
    
    // Restore state before returning
    assignment = saved_assignment;
    return false;
}

// Unit propagation
bool DPLLSolver::unitPropagate() {
    bool found = true;
    while (found) {
        found = false;
        
        for (uint32_t i = 0; i < clauses.size(); ++i) {
            // Skip satisfied clauses
            if (isClauseSatisfied(i)) {
                continue;
            }
            
            // Check if it's a unit clause
            int unassignedCount = 0;
            Literal unassignedLit = 0;
            
            for (Literal lit : clauses[i]) {
                Variable var = std::abs(lit);
                
                if (assignment[var] == Value::UNDEF) {
                    unassignedCount++;
                    unassignedLit = lit;
                } else if ((lit > 0 && assignment[var] == Value::TRUE) || 
                          (lit < 0 && assignment[var] == Value::FALSE)) {
                    // Literal is satisfied
                    unassignedCount = -1; // Mark clause as satisfied
                    break;
                }
            }
            
            if (unassignedCount == 0) {
                // All literals are false -> conflict
                return false;
            } else if (unassignedCount == 1) {
                // Unit clause found
                Variable var = std::abs(unassignedLit);
                Value val = (unassignedLit > 0) ? Value::TRUE : Value::FALSE;
                
                assignment[var] = val;
                num_propagations++;
                found = true; // Continue propagating
                break; // Restart the loop since assignments changed
            }
        }
    }
    
    return true;
}

// Pure literal elimination
void DPLLSolver::pureLiteralEliminate() {
    for (Variable var = 1; var <= num_vars; ++var) {
        if (assignment[var] != Value::UNDEF) {
            continue; // Skip assigned variables
        }
        
        bool appearsPositive = false;
        bool appearsNegative = false;
        
        // Check positive occurrences
        for (uint32_t clauseIdx : pos_occurrences[var]) {
            if (!isClauseSatisfied(clauseIdx)) {
                appearsPositive = true;
                break;
            }
        }
        
        // Check negative occurrences
        for (uint32_t clauseIdx : neg_occurrences[var]) {
            if (!isClauseSatisfied(clauseIdx)) {
                appearsNegative = true;
                break;
            }
        }
        
        // If pure, assign it
        if (appearsPositive && !appearsNegative) {
            assignment[var] = Value::TRUE;
        } else if (!appearsPositive && appearsNegative) {
            assignment[var] = Value::FALSE;
        }
    }
}

// Check if a clause is satisfied under the current assignment
bool DPLLSolver::isClauseSatisfied(uint32_t clauseIdx) const {
    for (Literal lit : clauses[clauseIdx]) {
        Variable var = std::abs(lit);
        if ((lit > 0 && assignment[var] == Value::TRUE) || 
            (lit < 0 && assignment[var] == Value::FALSE)) {
            return true;
        }
    }
    return false;
}

// Check if all clauses are satisfied
bool DPLLSolver::allClausesSatisfied() const {
    bool allSatisfied = true;
    for (uint32_t i = 0; i < clauses.size(); ++i) {
        if (!isClauseSatisfied(i)) {
            // Check if clause has any unassigned variables
            bool hasUnassigned = false;
            for (Literal lit : clauses[i]) {
                Variable var = std::abs(lit);
                if (assignment[var] == Value::UNDEF) {
                    hasUnassigned = true;
                    break;
                }
            }
            
            if (!hasUnassigned) {
                // Clause is falsified (all literals assigned and false)
                return false;
            }
            allSatisfied = false;  // Clause is not satisfied yet
        }
    }
    return allSatisfied;  // Only true if all clauses are satisfied
}

// Simple heuristic to choose a variable
Variable DPLLSolver::pickBranchVariable() {
    // Find first unassigned variable
    for (Variable var = 1; var <= num_vars; ++var) {
        if (assignment[var] == Value::UNDEF) {
            return var;
        }
    }
    return 0; // Should not happen
}

// Stats accessors
uint32_t DPLLSolver::getNumDecisions() const { return num_decisions; }
uint32_t DPLLSolver::getNumPropagations() const { return num_propagations; }