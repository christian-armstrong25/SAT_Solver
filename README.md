# SAT Solver

A high-performance Boolean Satisfiability (SAT) solver implementing the DPLL (Davis-Putnam-Logemann-Loveland) algorithm with advanced optimizations including watched literals and unit propagation.

## 🎯 Overview

This project implements a complete SAT solver that can determine whether a given Boolean formula in Conjunctive Normal Form (CNF) is satisfiable. The solver uses the DPLL algorithm enhanced with modern SAT solving techniques to efficiently handle both satisfiable and unsatisfiable instances.

## ✨ Features

- **DPLL Algorithm**: Core Davis-Putnam-Logemann-Loveland algorithm implementation
- **Watched Literals**: Efficient clause watching mechanism for fast unit propagation
- **Unit Propagation**: Automatic propagation of unit clauses
- **Pure Literal Elimination**: Optimization to eliminate pure literals
- **Performance Monitoring**: Tracks decision count and propagation statistics
- **JSON Output**: Structured output format for easy parsing
- **DIMACS Parser**: Standard CNF file format support
- **Timeout Support**: Configurable time limits for long-running instances

## 🏗️ Architecture

The solver is built with a modular architecture:

- **Main Solver**: `DPLLSolver` class implementing the core algorithm
- **Parser**: `dimacs_parser` for reading CNF files
- **Watched Literals**: Efficient data structures for clause watching
- **Heuristics**: Variable selection strategies for branching

## 📋 Prerequisites

- **C++17** compatible compiler (GCC 7+ or Clang 5+)
- **Bash** shell environment
- **Python 3** (for virtual environment management)

## 🚀 Installation

1. **Clone the repository**:

   ```bash
   git clone <repository-url>
   cd SAT_Solver
   ```

2. **Set up Python virtual environment** (optional, for package management):

   ```bash
   python3 -m venv venv
   source venv/bin/activate
   pip install -r requirements.txt
   ```

3. **Compile the solver**:
   ```bash
   chmod +x compile.sh
   ./compile.sh
   ```

## 🎮 Usage

### Single Instance

Solve a single CNF file:

```bash
./run.sh <input.cnf>
```

**Example**:

```bash
./run.sh input/toy_simple.cnf
```

### Batch Processing

Run the solver on all files in a directory with time limits:

```bash
./runAll.sh <input_folder/> <time_limit_seconds> <log_file>
```

**Example**:

```bash
./runAll.sh input/ 300 results/batch_run.log
```

### Direct Execution

Run the compiled solver directly:

```bash
./dpll_solver <input.cnf>
```

## 📊 Output Format

The solver outputs results in JSON format:

```json
{
	"Instance": "filename.cnf",
	"Time": 0.123,
	"Result": "SAT",
	"Solution": "1 true 2 false 3 true"
}
```

- **Instance**: Input filename
- **Time**: Execution time in seconds
- **Result**: "SAT" (satisfiable) or "UNSAT" (unsatisfiable)
- **Solution**: Variable assignments (only for SAT instances)

## 📁 Project Structure

```
SAT_Solver/
├── src/
│   ├── main.cpp              # Main program entry point
│   ├── dimacs_parser.cpp     # CNF file parser
│   ├── dimacs_parser.h       # Parser header
│   └── solvers/
│       ├── dpll.cpp          # DPLL algorithm implementation
│       └── dpll.h            # Solver interface
├── input/                    # Test instances
│   ├── toy_simple.cnf        # Simple example
│   ├── toy_solveable.cnf     # Satisfiable instance
│   ├── toy_infeasible.cnf    # Unsatisfiable instance
│   └── ...                   # Additional test cases
├── results/                  # Output logs
├── compile.sh               # Compilation script
├── run.sh                   # Single instance runner
├── runAll.sh                # Batch processing script
└── README.md                # This file
```

## 🧪 Test Instances

The project includes various test instances:

- **Toy Examples**: Simple instances for testing (`toy_simple.cnf`, `toy_solveable.cnf`, `toy_infeasible.cnf`)
- **Benchmark Instances**: Real-world SAT instances in the `input/` directory
- **Performance Tests**: Various sized instances for benchmarking

### Example CNF Format

```
c simple.cnf
c
p cnf 3 2
1 -3 0
2 3 -1 0
```

- `c` lines are comments
- `p cnf <variables> <clauses>` defines the problem
- Each line ending with `0` represents a clause
- Numbers represent literals (positive = variable, negative = negation)

## 🔬 Algorithm Details

### DPLL Algorithm

The solver implements the DPLL algorithm with the following components:

1. **Unit Propagation**: Automatically assign values to unit clauses
2. **Pure Literal Elimination**: Remove literals that appear only positively or negatively
3. **Branching**: Choose unassigned variables for decision making
4. **Backtracking**: Undo decisions when conflicts are detected

### Optimizations

- **Watched Literals**: Efficient clause watching for fast unit propagation
- **Two-Watch Scheme**: Each clause watches two literals for optimal performance
- **Conflict-Driven Learning**: Enhanced backtracking based on conflict analysis

## 📈 Performance

The solver is optimized for performance with:

- **C++17** compilation with `-Ofast` optimization
- **Efficient data structures** for clause representation
- **Memory-conscious** implementation
- **Configurable timeouts** for long-running instances

## 👥 Team

- **tgillin**
- **carmstr8**

## 📝 License

This project is part of CSCI 2951-O coursework.

## 🤝 Contributing

This is an academic project. For questions or issues, please contact the team members listed above.

## 📚 References

- Davis, M., Logemann, G., & Loveland, D. (1962). A machine program for theorem-proving. Communications of the ACM, 5(7), 394-397.
- Marques-Silva, J. P., & Sakallah, K. A. (1999). GRASP: A search algorithm for propositional satisfiability. IEEE Transactions on Computers, 48(5), 506-521.
