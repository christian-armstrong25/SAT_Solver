from pathlib import Path
from .classes import SATInstance

class DimacsParser:
    @staticmethod
    def parse_cnf_file(filename):
        try:
            with open(filename, 'r') as file:
                sat_instance = None
                
                # Skip comment lines and find problem line
                for line in file:
                    line = line.strip()
                    if not line:
                        continue
                    tokens = line.split()
                    if tokens[0] == 'c':
                        continue
                    if tokens[0] == 'p':
                        break
                
                # Check problem line format
                if tokens[0] != 'p':
                    raise ValueError("Error: DIMACS file does not have problem line")
                
                if tokens[1] != 'cnf':
                    print("Error: DIMACS file format is not cnf")
                    return None
                
                num_vars = int(tokens[2])
                num_clauses = int(tokens[3])
                sat_instance = SATInstance(num_vars, num_clauses)
                
                # Parse clauses
                for line in file:
                    line = line.strip()
                    if not line or line.startswith('c'):
                        continue
                    
                    tokens = line.split()
                    if tokens[-1] != '0':
                        raise ValueError("Error: clause line does not end with 0")
                    
                    # Create clause
                    clause = set()
                    for token in tokens[:-1]:  # Exclude the trailing 0
                        if token:  # Skip empty tokens
                            literal = int(token)
                            clause.add(literal)
                            sat_instance.add_variable(literal)
                    
                    sat_instance.add_clause(clause)
                
                return sat_instance
                
        except FileNotFoundError:
            raise FileNotFoundError(f"Error: DIMACS file is not found {filename}")
        except Exception as e:
            raise Exception(f"Error parsing DIMACS file: {str(e)}") 