from abc import ABC, abstractmethod
from typing import List, Tuple, Optional, Set
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
        
        assignment = []
        
        return self._dpll_recursive(cnf, assignment, None)
    
    def _dpll_recursive(self, clauses: List[Set[int]], assignment: List[int], literal: int | None) -> Tuple[bool, Optional[List[int]]]:
        if literal is not None:
            assignment.append(literal)
            if not self._simplify_clauses(clauses, literal):
                return False, None
            
        # Unit propagation
        if not self._unit_propagation(clauses, assignment):
            return False, None
        
        # Pure literal elimination
        self._pure_literal_elimination(clauses, assignment)

        # NOTE: this is working right now, but I think we should have pure and unit call dpll recursive when done
        # Or loop until no more changes
        # I think right now we will branch when we dont have to when pure literal elimination is
        # creating a unit clause
        
        if not clauses: 
            return True, assignment
        if any(not clause for clause in clauses):  
            return False, None
            
        # Choose branching literal
        # TODO: we can add heuristics here
        if not clauses:
            return True, assignment
            
        # Try both branches
        lit = next(iter(clauses[0]))

        # Positive branch
        clauses_copy = [clause.copy() for clause in clauses]
        is_sat, ret_assignment = self._dpll_recursive(clauses_copy, assignment.copy(), lit)
        if is_sat:
            return is_sat, ret_assignment
        
        # Negative branch
        clauses_copy = [clause.copy() for clause in clauses]
        return self._dpll_recursive(clauses_copy, assignment.copy(), -lit)
    
    def _unit_propagation(self, clauses: List[Set[int]], assignment: List[int]) -> bool:
        """Performs unit propagation. Returns False if contradiction found."""
        changed = True
        while changed and clauses:
            changed = False
            unit_clauses = [c for c in clauses if len(c) == 1]
            if not unit_clauses:
                break
                
            for clause in unit_clauses:
                unit = next(iter(clause))
                assignment.append(unit)
                if not self._simplify_clauses(clauses, unit):
                    return False
                changed = True
                
        return True
    
    def _pure_literal_elimination(self, clauses: List[Set[int]], assignment: List[int]) -> None:
        """Performs pure literal elimination"""
        if not clauses:
            return
            
        # Get all literals
        all_literals = set()
        for clause in clauses:
            all_literals.update(clause)
            
        # Find pure literals
        pure_lits = {lit for lit in all_literals if -lit not in all_literals}
        
        # Apply pure literals
        for lit in pure_lits:
            assignment.append(lit)
            self._simplify_clauses(clauses, lit)
    
    def _simplify_clauses(self, clauses: List[Set[int]], literal: int) -> bool:
        """Simplifies clauses with the given literal. Removes clauses that are satisfied and removes negative literal from clauses. Returns False if contradiction found."""
        i = 0
        while i < len(clauses):
            if literal in clauses[i]:
                clauses.pop(i)
            elif -literal in clauses[i]:
                clauses[i].remove(-literal)
                if not clauses[i]:
                    return False
                i += 1
            else:
                i += 1
        return True
