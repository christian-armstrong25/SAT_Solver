from abc import ABC, abstractmethod
from typing import List, Tuple, Optional, Set, Dict
import random

class Solver(ABC):
    @abstractmethod
    def solve(self, cnf: List[Set[int]]) -> Tuple[bool, Optional[List[int]]]:
        """
        Solves a CNF formula.
        Args:
            - cnf: List of sets, where each set contains the literals in that clause
                   Positive numbers for positive literals, negative for negated
        Returns:
            - Tuple of (is_satisfiable, assignment)
              where assignment is None if unsatisfiable, 
              otherwise a list of literals that satisfy the formula
        """
        pass

class DPLL(Solver):
    def solve(self, cnf: List[Set[int]]) -> Tuple[bool, Optional[List[int]]]:
        if not cnf:  
            return True, []
        
        assignment = {}
        result = self._dpll_recursive(cnf, assignment)
        
        if result[0]: # If SAT
            # Dict to list
            assignment_list = []
            for var, val in result[1].items():
                assignment_list.append(var if val else -var)
            return True, assignment_list
        return False, None
    
    def _dpll_recursive(self, clauses: List[Set[int]], assignment: Dict[int, bool]) -> Tuple[bool, Optional[Dict[int, bool]]]:
        # Keep doing inference steps until no more changes
        changes_made = True
        
        # Try unit propagation
        while changes_made:
            changes_made = False

            # Check termination conditions
            if not clauses:
                return True, assignment
            if any(not clause for clause in clauses):
                return False, None
            
            # Unit propagation                
            unit = self._find_unit_clause(clauses)
            if unit:
                var = abs(unit)  # Get the variable number
                val = unit > 0   # True if positive, False if negative
                assignment[var] = val
                self._simplify_clauses(clauses, unit)
                changes_made = True
                continue
            
            # Pure literal elimination
            pure = self._find_pure_literal(clauses)
            if pure:
                var = abs(pure)  # Get the variable number
                val = pure > 0   # True if positive, False if negative
                assignment[var] = val
                self._simplify_clauses(clauses, pure)
                changes_made = True
                continue
          
            
        # Choose branching literal (from shortest clause)
        lit = next(iter(min(clauses, key=len)))
        var = abs(lit)  # Get the variable number
        
        # Try positive branch
        clauses_copy = [clause.copy() for clause in clauses]
        assignment_copy = assignment.copy()
        assignment_copy[var] = True
        self._simplify_clauses(clauses_copy, var)

        is_sat, ret_assignment = self._dpll_recursive(clauses_copy, assignment_copy)
        if is_sat:
            return True, ret_assignment
            
            
        # Try negative branch
        clauses_copy = [clause.copy() for clause in clauses]
        assignment_copy = assignment.copy()
        assignment_copy[var] = False
        self._simplify_clauses(clauses_copy, -var)

        is_sat, ret_assignment = self._dpll_recursive(clauses_copy, assignment_copy)
        if is_sat:
            return True, ret_assignment
            
        return False, None
    
    def _find_unit_clause(self, clauses: List[Set[int]]) -> Optional[int]:
        """Returns a unit literal if one exists, None otherwise."""
        for clause in clauses:
            if len(clause) == 1:
                return next(iter(clause))
        return None
    
    def _find_pure_literal(self, clauses: List[Set[int]]) -> Optional[int]:
        """Returns a pure literal if one exists, None otherwise."""
        if not clauses:
            return None
            
        # Get all literals
        all_literals = set()
        for clause in clauses:
            all_literals.update(clause)
            
        # Find first pure literal
        for lit in all_literals:
            if -lit not in all_literals:
                return lit
        return None
    
    def _simplify_clauses(self, clauses: List[Set[int]], literal: int) -> None:
        """Simplifies clauses with the given literal. Returns False if contradiction found."""
        i = 0
        while i < len(clauses):
            if literal in clauses[i]:
                clauses.pop(i)
            elif -literal in clauses[i]:
                clauses[i].remove(-literal)
                if not clauses[i]:  # Empty clause
                    return
                i += 1
            else:
                i += 1
        return
