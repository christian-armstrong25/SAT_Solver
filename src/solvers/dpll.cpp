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
    // Create a mapping from original variables to sequential indices
    std::unordered_set<Variable> unique_vars;
    
    // Collect all variables
    for (const auto& clause : input_clauses) {
        for (Literal lit : clause) {
            Variable var = std::abs(lit);
            unique_vars.insert(var);
        }
    }
    
    // Create mappings
    idx_to_var.push_back(0); // Add dummy at index 0, since our variables start at 1
    uint32_t next_idx = 1;   // Start with index 1
    
    for (Variable var : unique_vars) {
        var_to_idx[var] = next_idx;
        idx_to_var.push_back(var);
        next_idx++;
    }
    
    // Map clauses using our variable mapping
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
    
    // When initialized, first look for tautologies and remove them
    clauses = removeTautologies(mapped_clauses);

    // Initialize variables using the number of mapped variables
    num_vars = idx_to_var.size() - 1; // Subtract 1 for the dummy at index 0
    
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
    // Boundary check
    if (clause_idx >= clauses.size()) return false;
    
    const auto& clause = clauses[clause_idx];
    auto& watches = clause_watches[clause_idx];
    
    // Find the other watched literal
    Literal other_watch = (watches.first == false_lit) ? watches.second : watches.first;
    
    // First pass: look for TRUE literals to watch
    for (Literal lit : clause) {
        if (lit != false_lit && lit != other_watch) {
            Value lit_value = getLiteralValue(lit);
            if (lit_value == Value::TRUE) {
                // Found a TRUE literal - best case! Update watches
                if (watches.first == false_lit) {
                    watches.first = lit;
                } else {
                    watches.second = lit;
                }
                
                // Add new watch
                addWatch(lit, clause_idx);
                
                // Remove old watch
                Variable abs_false_lit = std::abs(false_lit);
                auto& old_watches = (false_lit > 0) ? pos_watches[abs_false_lit] : neg_watches[abs_false_lit];
                
                for (size_t i = 0; i < old_watches.size(); ++i) {
                    if (old_watches[i].clause_idx == clause_idx && old_watches[i].literal == false_lit) {
                        // Replace with last element and pop
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
                // Update watches
                if (watches.first == false_lit) {
                    watches.first = lit;
                } else {
                    watches.second = lit;
                }
                
                // Add new watch
                addWatch(lit, clause_idx);
                
                // Remove old watch
                Variable abs_false_lit = std::abs(false_lit);
                auto& old_watches = (false_lit > 0) ? pos_watches[abs_false_lit] : neg_watches[abs_false_lit];
                
                for (size_t i = 0; i < old_watches.size(); ++i) {
                    if (old_watches[i].clause_idx == clause_idx && old_watches[i].literal == false_lit) {
                        // Replace with last element and pop
                        old_watches[i] = old_watches.back();
                        old_watches.pop_back();
                        break;
                    }
                }
                
                return true;
            }
        }
    }
    
    return false;  // No new watch found - all other literals are FALSE
}

bool DPLLSolver::propagateLiteral(Literal lit) {
    // This function is now just for setting the assignment
    Variable var = std::abs(lit);
    assignment[var] = (lit > 0) ? Value::TRUE : Value::FALSE;
    return true; // No longer call unitPropagate here to avoid recursion
}

bool DPLLSolver::unitPropagate() {
    std::vector<Literal> propagation_queue;
    std::vector<bool> in_queue(num_vars + 1, false);
    
    // First, check if there are already conflicting assignments
    for (Variable var = 1; var <= num_vars; var++) {
        if (assignment[var] != Value::UNDEF) {
            // Check if this assignment satisfies the clauses it's involved in
            Literal lit = assignment[var] == Value::TRUE ? var : -var;
            
            // Add to queue if not already present
            if (!in_queue[var]) {
                propagation_queue.push_back(lit);
                in_queue[var] = true;
            }
        }
    }
    
    // Process queue until empty
    size_t queue_index = 0;
    const size_t MAX_ITERATIONS = 1000000; // Safety limit
    size_t iteration_count = 0;
    
    while (queue_index < propagation_queue.size() && iteration_count < MAX_ITERATIONS) {
        iteration_count++;
        
        if (iteration_count >= MAX_ITERATIONS) {
            return false;
        }
        
        Literal lit = propagation_queue[queue_index++];
        if (lit == 0) continue; // Safety check
        
        // When assigning a literal to true, we need to check clauses where the negation is watched
        auto& watches = (lit > 0) ? neg_watches[std::abs(lit)] : pos_watches[std::abs(lit)];
        
        size_t i = 0;
        while (i < watches.size()) {
            if (i >= watches.size()) break; // Safety check
            
            ClauseIndex clause_idx = watches[i].clause_idx;
            if (clause_idx >= clauses.size()) {
                i++;
                continue;
            }
            
            // Check if the clause is already satisfied by some other literal
            if (isClauseSatisfied(clause_idx)) {
                i++;
                continue;
            }
            
            Literal watch_lit = watches[i].literal;
            
            // Try to find a new watch (either TRUE or UNDEFINED)
            if (findNewWatch(clause_idx, watch_lit)) {
                // Watch list might have changed, don't increment i
                continue;
            }
            
            // Couldn't find a new watch, so the other watch must become true
            auto& clause_watch = clause_watches[clause_idx];
            Literal other_watch = (watch_lit == clause_watch.first) ? 
                                clause_watch.second : clause_watch.first;
            
            // Check the other watched literal
            Value other_value = getLiteralValue(other_watch);
            
            if (other_value == Value::TRUE) {
                // Clause is already satisfied by the other watch
                i++;
                continue;
            }
            
            if (other_value == Value::FALSE) {
                // Both watches are false - conflict detected
                return false;
            }
            
            // Unit propagation case: other_watch must be true
            Variable var = std::abs(other_watch);
            if (var > 0 && var <= num_vars) {
                if (assignment[var] != Value::UNDEF) {
                    // Already assigned - check if consistent
                    if ((other_watch > 0) != (assignment[var] == Value::TRUE)) {
                        return false; // Conflict
                    }
                } else {
                    // Assign and add to queue
                    assignment[var] = (other_watch > 0) ? Value::TRUE : Value::FALSE;
                    num_propagations++;
                    
                    if (!in_queue[var]) {
                        propagation_queue.push_back(other_watch);
                        in_queue[var] = true;
                    }
                }
            }
            
            i++;
        }
    }
    
    return true;
}

std::pair<bool, std::vector<Literal>> DPLLSolver::solve() {
    bool is_sat = dpll();
    
    if (!is_sat) {
        return {false, std::vector<Literal>()};
    }
    
    // Ensure all variables are assigned
    for (Variable var = 1; var <= num_vars; ++var) {
        if (assignment[var] == Value::UNDEF) {
            // Assign any remaining unassigned variables arbitrarily
            assignment[var] = Value::TRUE;
        }
    }
    
    // Build the result and map back to original variable IDs
    std::vector<Literal> result;
    for (Variable var = 1; var <= num_vars; ++var) {
        // Map the internal variable index back to the original variable ID
        Variable original_var = idx_to_var[var];
        result.push_back(assignment[var] == Value::TRUE ? original_var : -original_var);
    }
    
    // Verify solution is correct
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
    // Bail out check for excessive recursion
    if (depth > 1000) {
        return false;
    }
    
    // Save the current assignment state
    std::vector<Value> saved_assignment = assignment;
    
    // Try unit propagation
    if (!unitPropagate()) {
        assignment = saved_assignment;  // Restore state
        return false;
    }
    
    // Apply pure literal elimination
    pureLiteralEliminate();
    
    // First, check if all clauses are satisfied with the current assignment
    bool allSatisfied = true;
    
    for (uint32_t i = 0; i < clauses.size(); ++i) {
        bool clauseSatisfied = isClauseSatisfied(i);
        
        if (!clauseSatisfied) {
            allSatisfied = false;
            
            // Check if any clause is definitely falsified (all literals assigned but unsatisfied)
            bool hasPotentialToSatisfy = false;
            for (Literal lit : clauses[i]) {
                Variable var = std::abs(lit);
                if (assignment[var] == Value::UNDEF) {
                    hasPotentialToSatisfy = true;
                    break;
                }
            }
            
            if (!hasPotentialToSatisfy) {
                // Found a falsified clause
                assignment = saved_assignment;
                return false;
            }
        }
    }
    
    if (allSatisfied) {
        return true;
    }
    
    // Otherwise, we need to branch
    Variable var = pickBranchVariable();
    if (var == 0) {
        return false;
    }
    
    num_decisions++;
    
    // Greedy polarity: try the assignment that satisfies more clauses first
    uint32_t true_satisfied = 0;
    uint32_t false_satisfied = 0;
    
    // Count clauses satisfied by each polarity
    for (uint32_t i = 0; i < clauses.size(); ++i) {
        if (isClauseSatisfied(i)) continue; // Skip already satisfied clauses
        
        // Check if setting var to TRUE satisfies this clause
        bool satisfied_by_true = false;
        bool satisfied_by_false = false;
        
        for (Literal lit : clauses[i]) {
            Variable clause_var = std::abs(lit);
            if (clause_var == var) {
                // If this is our variable
                if (lit > 0) {
                    // Positive literal is satisfied by TRUE
                    satisfied_by_true = true;
                } else {
                    // Negative literal is satisfied by FALSE
                    satisfied_by_false = true;
                }
            }
        }
        
        if (satisfied_by_true) true_satisfied++;
        if (satisfied_by_false) false_satisfied++;
    }
    
    // First try the assignment that satisfies more clauses
    bool try_true_first = (true_satisfied >= false_satisfied);
    
    // Try first polarity
    assignment[var] = try_true_first ? Value::TRUE : Value::FALSE;
    if (dpll(depth + 1)) {
        return true;
    }
    
    // Restore state and try opposite polarity
    assignment = saved_assignment;
    assignment[var] = try_true_first ? Value::FALSE : Value::TRUE;
    if (dpll(depth + 1)) {
        return true;
    }
    
    // Both assignments failed
    assignment = saved_assignment;
    return false;
}

// Pure literal elimination
void DPLLSolver::pureLiteralEliminate() {
    // Count occurrences of each literal in remaining unsatisfied clauses
    std::vector<bool> hasPositiveOccurrence(num_vars + 1, false);
    std::vector<bool> hasNegativeOccurrence(num_vars + 1, false);
    
    // Iterate through all clauses
    for (uint32_t i = 0; i < clauses.size(); ++i) {
        // Skip satisfied clauses
        if (isClauseSatisfied(i)) {
            continue;
        }
        
        // For each literal in the clause
        for (Literal lit : clauses[i]) {
            Variable var = std::abs(lit);
            
            // Skip if already assigned
            if (assignment[var] != Value::UNDEF) {
                continue;
            }
            
            // Mark occurrence
            if (lit > 0) {
                hasPositiveOccurrence[var] = true;
            } else {
                hasNegativeOccurrence[var] = true;
            }
        }
    }
    
    // Assign pure literals
    bool assigned_pure_literal = false;
    for (Variable var = 1; var <= num_vars; ++var) {
        if (assignment[var] != Value::UNDEF) {
            continue; // Skip assigned variables
        }
        
        // If pure positive (appears only as positive)
        if (hasPositiveOccurrence[var] && !hasNegativeOccurrence[var]) {
            assignment[var] = Value::TRUE;
            assigned_pure_literal = true;
        } 
        // If pure negative (appears only as negative)
        else if (!hasPositiveOccurrence[var] && hasNegativeOccurrence[var]) {
            assignment[var] = Value::FALSE;
            assigned_pure_literal = true;
        }
    }
    
    // If we assigned any pure literals, try to assign more after propagation
    if (assigned_pure_literal) {
        unitPropagate(); // Propagate the new assignments
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
    bool all_clauses_satisfied = true;
    bool all_vars_assigned = true;
    
    // Check both clause satisfaction and variable assignment
    for (uint32_t i = 0; i < clauses.size(); ++i) {
        bool clause_satisfied = false;
        
        for (Literal lit : clauses[i]) {
            Variable var = std::abs(lit);
            Value val = assignment[var];
            
            // Track unassigned variables
            if (val == Value::UNDEF) {
                all_vars_assigned = false;
            }
            
            // Check if this literal satisfies the clause
            if ((lit > 0 && val == Value::TRUE) || (lit < 0 && val == Value::FALSE)) {
                clause_satisfied = true;
                break;
            }
        }
        
        // If this clause isn't satisfied, the formula isn't fully satisfied
        if (!clause_satisfied) {
            all_clauses_satisfied = false;
            
            // Check if this clause can potentially be satisfied
            bool has_unassigned = false;
            for (Literal lit : clauses[i]) {
                Variable var = std::abs(lit);
                if (assignment[var] == Value::UNDEF) {
                    has_unassigned = true;
                    break;
                }
            }
            
            // If all literals are assigned but the clause is still unsatisfied,
            // then the formula is definitely unsatisfiable under current assignment
            if (!has_unassigned) {
                return false;
            }
        }
    }
    
    // For a formula to be fully satisfied, all clauses must be satisfied AND all vars must be assigned
    return all_clauses_satisfied && all_vars_assigned;
}

Variable DPLLSolver::pickBranchVariable() {
    // First identify minimum size of unsatisfied clauses and track literal occurrences in one pass
    uint32_t min_size = UINT32_MAX;
    std::vector<std::vector<uint32_t>> counts(2, std::vector<uint32_t>(num_vars + 1, 0));
    Variable first_unassigned = 0;
    
    // First pass - find minimum size
    for (uint32_t i = 0; i < clauses.size(); ++i) {
        if (isClauseSatisfied(i)) continue;
        
        // Count unassigned literals
        uint32_t unassigned_count = 0;
        for (Literal lit : clauses[i]) {
            Variable var = std::abs(lit);
            if (assignment[var] == Value::UNDEF) {
                unassigned_count++;
                // Keep track of first unassigned variable as fallback
                if (first_unassigned == 0) first_unassigned = var;
            }
        }
        
        if (unassigned_count > 0) {
            min_size = std::min(min_size, unassigned_count);
        }
    }
    
    // No unsatisfied clauses or all variables assigned
    if (min_size == UINT32_MAX) return first_unassigned;
    
    // Second pass - collect counts only for minimum-sized clauses
    for (uint32_t i = 0; i < clauses.size(); ++i) {
        if (isClauseSatisfied(i)) continue;
        
        // Check if this is a minimum-sized clause
        uint32_t unassigned_count = 0;
        for (Literal lit : clauses[i]) {
            if (assignment[std::abs(lit)] == Value::UNDEF) {
                unassigned_count++;
            }
        }
        
        if (unassigned_count == min_size) {
            // Count occurrences in minimum clauses
            for (Literal lit : clauses[i]) {
                Variable var = std::abs(lit);
                if (assignment[var] == Value::UNDEF) {
                    // Index 0 for negative, 1 for positive
                    int idx = (lit > 0) ? 1 : 0;
                    counts[idx][var]++;
                }
            }
        }
    }
    
    // Compute MOM's scores and find best variable
    Variable best_var = 0;
    uint32_t best_score = 0;
    const uint32_t k = 1; // Weight parameter
    
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

// Stats accessors
uint32_t DPLLSolver::getNumDecisions() const { return num_decisions; }
uint32_t DPLLSolver::getNumPropagations() const { return num_propagations; }