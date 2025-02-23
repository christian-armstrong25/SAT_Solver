import sys
import time
import traceback
from pathlib import Path
from dimacs_parser import parse_cnf_file
from solvers.dpll import DPLL

def format_solution(assignment: list) -> str:
    if not assignment:
        return ""
    
    var_assignments = {}
    for lit in assignment:
        var = abs(lit)
        var_assignments[var] = lit > 0
    
    solution_parts = []
    for var in sorted(var_assignments.keys()):
        solution_parts.append(f"{var} {'true' if var_assignments[var] else 'false'}")
    
    return " ".join(solution_parts)

def main():
    if len(sys.argv) < 2:
        print("Usage: python main.py <cnf file>")
        return
    
    input_file = sys.argv[1]
    filename = Path(input_file).name
    
    try:
        clauses = parse_cnf_file(input_file)
        solver = DPLL()

        start_time = time.time()
        is_sat, assignment = solver.solve(clauses)
        end_time = time.time()
        
        result = "SAT" if is_sat else "UNSAT"
        solution_str = f', "Solution": "{format_solution(assignment)}"' if is_sat else ""
        
        print(f'{{"Instance": "{filename}", "Time": {end_time - start_time:.2f}, "Result": "{result}"{solution_str}}}')
    
    except Exception as e:
        print("Error occurred:")
        print(traceback.format_exc())

if __name__ == "__main__":
    main() 