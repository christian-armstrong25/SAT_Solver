#include <algorithm>
#include <vector>
#include <unordered_map>
#include <iostream>
#include <unordered_set>

#include "dpll.h"
using Literal = int32_t;
using Variable = uint32_t;
using ClauseIndex = uint32_t;

DPLLSolver::DPLLSolver(const std::vector<std::vector<Literal>>& input_clauses) {
    std::unordered_set<Variable> unique_vars;
    
    for (const auto& clause : input_clauses) {
        for (Literal lit : clause) {
            Variable var = std::abs(lit);
            unique_vars.insert(var);
        }
    }
    
    idx_to_var.push_back(0); // Add dummy at index 0
    uint32_t next_idx = 1;
    
    for (Variable var : unique_vars) {
        var_to_idx[var] = next_idx;
        idx_to_var.push_back(var);
        next_idx++;
    }
    
    std::vector<std::vector<Literal>> mapped_clauses;
    for (const auto& clause : input_clauses) {
        std::vector<Literal> mapped_clause;
        for (Literal lit : clause) {
            Variable var = std::abs(lit);
            Literal mapped_lit = (lit > 0) ? var_to_idx[var] : -var_to_idx[var];
            mapped_clause.push_back(mapped_lit);
        }
        mapped_clauses.push_back(mapped_clause);
    }
    
    clauses = removeTautologies(mapped_clauses);
    num_vars = idx_to_var.size() - 1;
    
    assignment.resize(num_vars + 1, Value::UNDEF);
    pos_watches.resize(num_vars + 1);
    neg_watches.resize(num_vars + 1);
    clause_watches.resize(clauses.size());

    initWatches();
    num_decisions = 0;
    num_propagations = 0;
}

std::vector<std::vector<Literal>> DPLLSolver::removeTautologies(const std::vector<std::vector<Literal>>& input_clauses) {
    std::vector<std::vector<Literal>> filtered_clauses;
    for (const auto& clause : input_clauses) {
        if (clause.empty()) continue;
        std::unordered_set<Literal> clause_set(clause.begin(), clause.end());
        bool has_contradiction = false;

        for (Literal lit : clause) {
            if (clause_set.count(-lit)) {
                has_contradiction = true;
                std::cout << "Tautology found and removed: ";
                break;
            }
        }

        if (!has_contradiction) {
            filtered_clauses.push_back(clause);
        }
    }

    return filtered_clauses;
}

void DPLLSolver::initWatches() {
    for (ClauseIndex i = 0; i < clauses.size(); ++i) {
        const auto& clause = clauses[i];
        if (clause.empty()) continue;

        addWatch(clause[0], i);
        
        if (clause.size() == 1) {
            addWatch(clause[0], i);
        } else {
            addWatch(clause[1], i);
        }
        
        clause_watches[i] = {clause[0], clause.size() > 1 ? clause[1] : clause[0]};
    }
}

void DPLLSolver::addWatch(Literal lit, ClauseIndex clause_idx) {
    Variable var = std::abs(lit);
    if (var == 0 || var > num_vars || clause_idx >= clauses.size()) {
        return;
    }
    
    if (lit > 0) {
        pos_watches[var].emplace_back(lit, clause_idx);
    } else {
        neg_watches[var].emplace_back(lit, clause_idx);
    }
}

DPLLSolver::Value DPLLSolver::getLiteralValue(Literal lit) const {
    DPLLSolver::Value var_value = assignment[std::abs(lit)];
    if (var_value == DPLLSolver::Value::UNDEF) return DPLLSolver::Value::UNDEF;
    return (lit > 0) == (var_value == DPLLSolver::Value::TRUE) ? DPLLSolver::Value::TRUE : DPLLSolver::Value::FALSE;
}

bool DPLLSolver::findNewWatch(ClauseIndex clause_idx, Literal false_lit) {
    if (clause_idx >= clauses.size()) return false;
    
    const auto& clause = clauses[clause_idx];
    auto& watches = clause_watches[clause_idx];
    
    Literal other_watch = (watches.first == false_lit) ? watches.second : watches.first;
    
    Value other_watch_value = getLiteralValue(other_watch);
    if (other_watch_value == Value::TRUE) {
        return true;
    }
    
    // First pass: look for TRUE literals to watch
    for (Literal lit : clause) {
        if (lit != false_lit && lit != other_watch) {
            Value lit_value = getLiteralValue(lit);
            if (lit_value == Value::TRUE) {
                if (watches.first == false_lit) {
                    watches.first = lit;
                } else {
                    watches.second = lit;
                }
                
                addWatch(lit, clause_idx);
                
                Variable abs_false_lit = std::abs(false_lit);
                auto& old_watches = (false_lit > 0) ? pos_watches[abs_false_lit] : neg_watches[abs_false_lit];
                
                for (size_t i = 0; i < old_watches.size(); ++i) {
                    if (old_watches[i].clause_idx == clause_idx && old_watches[i].literal == false_lit) {
                        old_watches[i] = old_watches.back();
                        old_watches.pop_back();
                        break;
                    }
                }
                
                return true;
            }
        }
    }
    
    // Second pass: look for UNDEFINED literals
    for (Literal lit : clause) {
        if (lit != false_lit && lit != other_watch) {
            Value lit_value = getLiteralValue(lit);
            if (lit_value == Value::UNDEF) {
                if (watches.first == false_lit) {
                    watches.first = lit;
                } else {
                    watches.second = lit;
                }
                
                addWatch(lit, clause_idx);
                
                Variable abs_false_lit = std::abs(false_lit);
                auto& old_watches = (false_lit > 0) ? pos_watches[abs_false_lit] : neg_watches[abs_false_lit];
                
                for (size_t i = 0; i < old_watches.size(); ++i) {
                    if (i < old_watches.size() && 
                       old_watches[i].clause_idx == clause_idx && 
                       old_watches[i].literal == false_lit) {
                        old_watches[i] = old_watches.back();
                        old_watches.pop_back();
                        break;
                    }
                }
                
                return true;
            }
        }
    }
    
    return false;
}

bool DPLLSolver::propagateLiteral(Literal lit) {
    Variable var = std::abs(lit);
    assignment[var] = (lit > 0) ? Value::TRUE : Value::FALSE;
    return true;
}

bool DPLLSolver::unitPropagate() {
    std::vector<Literal> propagation_queue;
    std::vector<bool> in_queue(num_vars + 1, false);
    
    // Initialize the propagation queue with unit clauses and already assigned variables
    for (ClauseIndex i = 0; i < clauses.size(); ++i) {
        const auto& clause = clauses[i];
        if (clause.size() == 1) {
            Literal lit = clause[0];
            Variable var = std::abs(lit);
            
            if (assignment[var] == Value::UNDEF) {
                assignment[var] = (lit > 0) ? Value::TRUE : Value::FALSE;
                num_propagations++;
                
                if (!in_queue[var]) {
                    propagation_queue.push_back(lit);
                    in_queue[var] = true;
                }
            } else if ((lit > 0 && assignment[var] == Value::FALSE) || 
                       (lit < 0 && assignment[var] == Value::TRUE)) {
                return false;
            }
        }
    }
    
    for (Variable var = 1; var <= num_vars; var++) {
        if (assignment[var] != Value::UNDEF && !in_queue[var]) {
            Literal lit = (assignment[var] == Value::TRUE) ? var : -var;
            propagation_queue.push_back(lit);
            in_queue[var] = true;
        }
    }
    
    size_t queue_index = 0;
    const size_t MAX_ITERATIONS = 1000000;
    size_t iteration_count = 0;
    
    while (queue_index < propagation_queue.size() && iteration_count < MAX_ITERATIONS) {
        iteration_count++;
        
        if (iteration_count >= MAX_ITERATIONS) {
            return false;
        }
        
        Literal lit = propagation_queue[queue_index++];
        if (lit == 0) continue;
        
        Literal false_lit = -lit;
        Variable var = std::abs(lit);
        
        auto& watches = (false_lit > 0) ? pos_watches[var] : neg_watches[var];
        
        size_t i = 0;
        while (i < watches.size()) {
            if (i >= watches.size()) break;
            
            ClauseIndex clause_idx = watches[i].clause_idx;
            if (clause_idx >= clauses.size()) {
                i++;
                continue;
            }
            
            if (isClauseSatisfied(clause_idx)) {
                i++;
                continue;
            }
            
            Literal watch_lit = watches[i].literal;
            
            if (findNewWatch(clause_idx, watch_lit)) {
                continue;
            }
            
            auto& clause_watch = clause_watches[clause_idx];
            Literal other_watch = (watch_lit == clause_watch.first) ? 
                                clause_watch.second : clause_watch.first;
            
            Value other_value = getLiteralValue(other_watch);
            
            if (other_value == Value::TRUE) {
                i++;
                continue;
            }
            
            if (other_value == Value::FALSE) {
                return false;
            }
            
            Variable unit_var = std::abs(other_watch);
            if (unit_var > 0 && unit_var <= num_vars) {
                if (assignment[unit_var] != Value::UNDEF) {
                    if ((other_watch > 0) != (assignment[unit_var] == Value::TRUE)) {
                        return false;
                    }
                } else {
                    assignment[unit_var] = (other_watch > 0) ? Value::TRUE : Value::FALSE;
                    num_propagations++;
                    
                    if (!in_queue[unit_var]) {
                        propagation_queue.push_back(other_watch);
                        in_queue[unit_var] = true;
                    }
                }
            }
            
            i++;
        }
    }
    
    return true;
}

std::pair<bool, std::vector<Literal>> DPLLSolver::solve() {
    // The main entry point for solving the SAT instance
    // This calls the recursive DPLL function and converts the result to original variable indices
    bool is_sat = dpll();
    
    if (!is_sat) {
        return {false, std::vector<Literal>()};
    }
    
    // Assign TRUE to any remaining unassigned variables
    for (Variable var = 1; var <= num_vars; ++var) {
        if (assignment[var] == Value::UNDEF) {
            assignment[var] = Value::TRUE;
        }
    }
    
    // Convert the internal variable indices back to the original problem indices
    std::vector<Literal> result;
    for (Variable var = 1; var <= num_vars; ++var) {
        Variable original_var = idx_to_var[var];
        result.push_back(assignment[var] == Value::TRUE ? original_var : -original_var);
    }
    
    // Verify that all clauses are satisfied with our assignment
    for (const auto& clause : clauses) {
        bool clause_satisfied = false;
        for (Literal lit : clause) {
            Variable var = std::abs(lit);
            if ((lit > 0 && assignment[var] == Value::TRUE) || 
                (lit < 0 && assignment[var] == Value::FALSE)) {
                clause_satisfied = true;
                break;
            }
        }
        if (!clause_satisfied) {
            return {false, std::vector<Literal>()};
        }
    }
    
    return {true, result};
}

bool DPLLSolver::dpll(int depth) {
    // Depth parameter was used to limit recursion depth
    // if (depth > 1000) {
    //     return false;
    // }
    
    // Save current assignment for backtracking
    std::vector<Value> saved_assignment = assignment;
    
    // STEP 1: Unit Propagation - find and assign variables that must take specific values
    // This is a critical optimization in modern SAT solvers
    if (!unitPropagate()) {
        // If a contradiction is found during propagation, backtrack
        assignment = saved_assignment;
        return false;
    }
    
    // STEP 2: Pure Literal Elimination - assign values to literals that appear with only one polarity
    pureLiteralEliminate();
    
    // STEP 3: Check if all clauses are satisfied with current partial assignment
    bool allSatisfied = true;
    
    for (uint32_t i = 0; i < clauses.size(); ++i) {
        if (!isClauseSatisfied(i)) {
            allSatisfied = false;
            
            // Check if the clause can potentially be satisfied with further assignments
            bool hasPotentialToSatisfy = false;
            for (Literal lit : clauses[i]) {
                Variable var = std::abs(lit);
                if (assignment[var] == Value::UNDEF) {
                    hasPotentialToSatisfy = true;
                    break;
                }
            }
            
            // If a clause cannot be satisfied, backtrack
            if (!hasPotentialToSatisfy) {
                assignment = saved_assignment;
                return false;
            }
        }
    }
    
    // If all clauses are satisfied, we've found a solution
    if (allSatisfied) {
        return true;
    }
    
    // STEP 4: Choose a variable for branching using a heuristic
    Variable var = pickBranchVariable();
    if (var == 0) {
        return false;
    }
    
    num_decisions++;
    
    // STEP 5: Try assigning values to the chosen variable
    // Heuristically determine which value to try first
    uint32_t true_satisfied = 0;
    uint32_t false_satisfied = 0;
    
    // Count how many clauses would be satisfied with each assignment
    for (uint32_t i = 0; i < clauses.size(); ++i) {
        if (isClauseSatisfied(i)) continue;
        
        bool contains_pos = false;
        bool contains_neg = false;
        bool has_other_undefined = false;
        
        for (Literal lit : clauses[i]) {
            Variable lit_var = std::abs(lit);
            
            if (lit_var == var) {
                if (lit > 0) {
                    contains_pos = true;
                } else {
                    contains_neg = true;
                }
            } else if (assignment[lit_var] == Value::UNDEF) {
                has_other_undefined = true;
            }
        }
        
        if (contains_pos && !has_other_undefined) true_satisfied++;
        if (contains_neg && !has_other_undefined) false_satisfied++;
    }
    
    for (const auto& watch : pos_watches[var]) {
        ClauseIndex clause_idx = watch.clause_idx;
        if (!isClauseSatisfied(clause_idx)) {
            true_satisfied++;
        }
    }
    
    for (const auto& watch : neg_watches[var]) {
        ClauseIndex clause_idx = watch.clause_idx;
        if (!isClauseSatisfied(clause_idx)) {
            false_satisfied++;
        }
    }
    
    bool try_true_first = (true_satisfied >= false_satisfied);
    
    assignment[var] = try_true_first ? Value::TRUE : Value::FALSE;
    if (dpll(depth + 1)) {
        return true;
    }
    
    assignment = saved_assignment;
    assignment[var] = try_true_first ? Value::FALSE : Value::TRUE;
    if (dpll(depth + 1)) {
        return true;
    }
    
    assignment = saved_assignment;
    return false;
}

void DPLLSolver::pureLiteralEliminate() {
    std::vector<bool> hasPositiveOccurrence(num_vars + 1, false);
    std::vector<bool> hasNegativeOccurrence(num_vars + 1, false);
    
    for (ClauseIndex i = 0; i < clauses.size(); ++i) {
        if (isClauseSatisfied(i)) {
            continue;
        }
        
        for (Literal lit : clauses[i]) {
            Variable var = std::abs(lit);
            
            if (assignment[var] != Value::UNDEF) {
                continue;
            }
            
            if (lit > 0) {
                hasPositiveOccurrence[var] = true;
            } else {
                hasNegativeOccurrence[var] = true;
            }
        }
    }
    
    bool assigned_pure_literal = false;
    for (Variable var = 1; var <= num_vars; ++var) {
        if (assignment[var] != Value::UNDEF) {
            continue;
        }
        
        if (hasPositiveOccurrence[var] && !hasNegativeOccurrence[var]) {
            assignment[var] = Value::TRUE;
            assigned_pure_literal = true;
        } 
        else if (!hasPositiveOccurrence[var] && hasNegativeOccurrence[var]) {
            assignment[var] = Value::FALSE;
            assigned_pure_literal = true;
        }
    }
    
    if (assigned_pure_literal) {
        unitPropagate();
    }
}

bool DPLLSolver::isClauseSatisfied(uint32_t clauseIdx) const {
    if (clauseIdx >= clauses.size()) {
        return false;
    }
    
    for (Literal lit : clauses[clauseIdx]) {
        Variable var = std::abs(lit);
        
        if (var == 0 || var >= assignment.size()) {
            continue;
        }
        
        if ((lit > 0 && assignment[var] == Value::TRUE) || 
            (lit < 0 && assignment[var] == Value::FALSE)) {
            return true;
        }
    }
    return false;
}

bool DPLLSolver::allClausesSatisfied() const {
    bool all_clauses_satisfied = true;
    bool all_vars_assigned = true;
    
    for (uint32_t i = 0; i < clauses.size(); ++i) {
        bool clause_satisfied = false;
        
        for (Literal lit : clauses[i]) {
            Variable var = std::abs(lit);
            Value val = assignment[var];
            
            if (val == Value::UNDEF) {
                all_vars_assigned = false;
            }
            
            if ((lit > 0 && val == Value::TRUE) || (lit < 0 && val == Value::FALSE)) {
                clause_satisfied = true;
                break;
            }
        }
        
        if (!clause_satisfied) {
            all_clauses_satisfied = false;
            
            bool has_unassigned = false;
            for (Literal lit : clauses[i]) {
                Variable var = std::abs(lit);
                if (assignment[var] == Value::UNDEF) {
                    has_unassigned = true;
                    break;
                }
            }
            
            if (!has_unassigned) {
                return false;
            }
        }
    }
    
    return all_clauses_satisfied && all_vars_assigned;
}

Variable DPLLSolver::pickBranchVariable() {
    // Using MOMS heuristic
    uint32_t min_size = UINT32_MAX;
    std::vector<std::vector<uint32_t>> counts(2, std::vector<uint32_t>(num_vars + 1, 0));
    Variable first_unassigned = 0;
    
    // Find clauses with minimum number of unassigned variables
    for (uint32_t i = 0; i < clauses.size(); ++i) {
        if (isClauseSatisfied(i)) continue;
        
        uint32_t unassigned_count = 0;
        for (Literal lit : clauses[i]) {
            Variable var = std::abs(lit);
            if (assignment[var] == Value::UNDEF) {
                unassigned_count++;
                if (first_unassigned == 0) first_unassigned = var;
            }
        }
        
        if (unassigned_count > 0) {
            min_size = std::min(min_size, unassigned_count);
        }
    }
    
    if (min_size == UINT32_MAX) return first_unassigned;
    
    for (uint32_t i = 0; i < clauses.size(); ++i) {
        if (isClauseSatisfied(i)) continue;
        
        uint32_t unassigned_count = 0;
        for (Literal lit : clauses[i]) {
            if (assignment[std::abs(lit)] == Value::UNDEF) {
                unassigned_count++;
            }
        }
        
        if (unassigned_count == min_size) {
            for (Literal lit : clauses[i]) {
                Variable var = std::abs(lit);
                if (assignment[var] == Value::UNDEF) {
                    int idx = (lit > 0) ? 1 : 0;
                    counts[idx][var]++;
                }
            }
        }
    }
    
    Variable best_var = 0;
    uint32_t best_score = 0;
    const uint32_t k = 1;
    
    for (Variable var = 1; var <= num_vars; ++var) {
        if (assignment[var] == Value::UNDEF) {
            uint32_t neg = counts[0][var];
            uint32_t pos = counts[1][var];
            uint32_t score = (pos * neg) * (1 << k) + pos + neg;
            
            if (score > best_score) {
                best_score = score;
                best_var = var;
            }
        }
    }
    
    return best_var != 0 ? best_var : first_unassigned;
}

uint32_t DPLLSolver::getNumDecisions() const { return num_decisions; }
uint32_t DPLLSolver::getNumPropagations() const { return num_propagations; }