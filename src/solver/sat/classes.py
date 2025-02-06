class SATInstance:
    def __init__(self, num_vars, num_clauses):
        self.num_vars = num_vars
        self.num_clauses = num_clauses
        self.vars = set()
        self.clauses = []
    
    def add_variable(self, literal):
        # Variables are strictly positive integers
        self.vars.add(abs(literal))
    
    def add_clause(self, clause):
        self.clauses.append(clause)
    
    def __str__(self):
        output = []
        output.append(f"Number of variables: {self.num_vars}")
        output.append(f"Number of clauses: {self.num_clauses}")
        output.append(f"Variables: {self.vars}")
        for i, clause in enumerate(self.clauses):
            output.append(f"Clause {i}: {clause}")
        return "\n".join(output) 