#include <algorithm>
#include <vector>
#include <unordered_map>
#include <iostream>

#include "dpll.h"
using Literal = int32_t;
using Variable = uint32_t;
using ClauseIndex = uint32_t;

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
    pos_watches.resize(num_vars + 1);
    neg_watches.resize(num_vars + 1);
    clause_watches.resize(clauses.size());

    initWatches();
    num_decisions = 0;
    num_propagations = 0;
}

void DPLLSolver::initWatches() {
    for (ClauseIndex i = 0; i < clauses.size(); ++i) {
        const auto& clause = clauses[i];
        if (clause.empty()) continue;

        // Watch first literal
        addWatch(clause[0], i);
        
        // For unit clauses, watch the same literal twice
        if (clause.size() == 1) {
            addWatch(clause[0], i);
        } else {
            // Watch second literal for non-unit clauses
            addWatch(clause[1], i);
        }
        
        clause_watches[i] = {clause[0], clause.size() > 1 ? clause[1] : clause[0]};
    }
}

void DPLLSolver::addWatch(Literal lit, ClauseIndex clause_idx) {
    if (lit > 0) {
        pos_watches[lit].emplace_back(lit, clause_idx);
    } else {
        neg_watches[-lit].emplace_back(lit, clause_idx);
    }
}

DPLLSolver::Value DPLLSolver::getLiteralValue(Literal lit) const {
    DPLLSolver::Value var_value = assignment[std::abs(lit)];
    if (var_value == DPLLSolver::Value::UNDEF) return DPLLSolver::Value::UNDEF;
    return (lit > 0) == (var_value == DPLLSolver::Value::TRUE) ? DPLLSolver::Value::TRUE : DPLLSolver::Value::FALSE;
}

bool DPLLSolver::findNewWatch(ClauseIndex clause_idx, Literal false_lit) {
    const auto& clause = clauses[clause_idx];
    auto& watches = clause_watches[clause_idx];
    
    // Find the other watched literal
    Literal other_watch = (watches.first == false_lit) ? watches.second : watches.first;
    
    // Look for a new literal to watch
    for (Literal lit : clause) {
        if (lit != false_lit && lit != other_watch) {
            if (getLiteralValue(lit) != Value::FALSE) {
                // Update the watches
                if (watches.first == false_lit) {
                    watches.first = lit;
                } else {
                    watches.second = lit;
                }
                
                // Remove old watch and add new one
                addWatch(lit, clause_idx);
                return true;
            }
        }
    }
    
    return false;  // No new watch found
}

bool DPLLSolver::propagateLiteral(Literal lit) {
    // Get the watches that need to be checked
    auto& watches = (lit > 0) ? neg_watches[lit] : pos_watches[-lit];
    
    size_t i = 0;
    while (i < watches.size()) {
        ClauseIndex clause_idx = watches[i].clause_idx;
        Literal watch_lit = watches[i].literal;
        
        // Try to find new watch
        if (findNewWatch(clause_idx, watch_lit)) {
            // Remove this watch since we found a new one
            watches[i] = watches.back();
            watches.pop_back();
            continue;
        }
        
        // Get the other watch
        auto& clause_watch = clause_watches[clause_idx];
        Literal other_watch = (watch_lit == clause_watch.first) ? 
                            clause_watch.second : clause_watch.first;
        
        // Check the other watched literal
        Value other_value = getLiteralValue(other_watch);
        if (other_value == Value::TRUE) {
            // Clause is satisfied
            i++;
            continue;
        }
        
        if (other_value == Value::FALSE) {
            // Conflict detected
            return false;
        }
        
        // Unit propagation case
        Variable var = std::abs(other_watch);
        assignment[var] = (other_watch > 0) ? Value::TRUE : Value::FALSE;
        num_propagations++;
        
        if (!propagateLiteral(other_watch)) {
            return false;
        }
        
        i++;
    }
    
    return true;
}

bool DPLLSolver::unitPropagate() {
    for (Variable var = 1; var <= num_vars; var++) {
        if (assignment[var] != Value::UNDEF) {
            Literal lit = assignment[var] == Value::TRUE ? var : -var;
            if (!propagateLiteral(lit)) {
                return false;
            }
        }
    }
    return true;
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

// Pure literal elimination
void DPLLSolver::pureLiteralEliminate() {
    for (Variable var = 1; var <= num_vars; ++var) {
        if (assignment[var] != Value::UNDEF) {
            continue; // Skip assigned variables
        }
        
        bool appearsPositive = false;
        bool appearsNegative = false;
        
        // Check positive occurrences
        for (const Watch& watch : pos_watches[var]) {
            if (!isClauseSatisfied(watch.clause_idx)) {
                appearsPositive = true;
                break;
            }
        }
        
        // Check negative occurrences
        for (const Watch& watch : neg_watches[var]) {
            if (!isClauseSatisfied(watch.clause_idx)) {
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