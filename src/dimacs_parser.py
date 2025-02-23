def parse_cnf_file(filename):
    """
    Parse a DIMACS CNF file and return the clauses.
    Returns a list of sets, where each set contains the literals in that clause.
    Positive numbers for positive literals, negative for negated literals.
    """
    try:
        with open(filename, 'r') as file:
            clauses = []
            num_vars = 0
            num_clauses = 0
            
            # Skip comment lines and find problem line
            for line in file:
                line = line.strip()
                if not line:
                    continue
                tokens = line.split()
                if tokens[0] == 'c':
                    continue
                if tokens[0] == 'p':
                    if tokens[1] != 'cnf':
                        raise ValueError("Error: DIMACS file format is not CNF")
                    num_vars = int(tokens[2])
                    num_clauses = int(tokens[3])
                    break
            
            # Check if we found the problem line
            if num_vars == 0 or num_clauses == 0:
                raise ValueError("Error: DIMACS file does not have valid problem line")
            
            # Parse clauses
            for line in file:
                line = line.strip()
                if not line or line.startswith('c'):
                    continue
                
                tokens = line.split()
                if tokens[-1] != '0':
                    raise ValueError("Error: clause line does not end with 0")
                
                # Convert tokens to integers and add to clauses as a set
                # Exclude the trailing 0
                clause = set(int(token) for token in tokens[:-1] if token)
                if clause:  # Only add non-empty clauses
                    clauses.append(clause)
            
            # Verify we got the expected number of clauses
            if len(clauses) != num_clauses:
                raise ValueError(f"Error: expected {num_clauses} clauses but got {len(clauses)}")
            
            return clauses
                
    except FileNotFoundError:
        raise FileNotFoundError(f"Error: DIMACS file not found: {filename}")
    except ValueError as e:
        raise ValueError(f"Error parsing DIMACS file: {str(e)}")
    except Exception as e:
        raise Exception(f"Error parsing DIMACS file: {str(e)}") 