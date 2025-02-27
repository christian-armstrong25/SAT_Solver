#include <iostream>
#include <chrono>
#include <string>
#include <filesystem>
#include <stdexcept>
#include <algorithm>  // For std::sort
#include <unordered_map>  // Added for unordered_map

#include "dimacs_parser.h"
#include "solvers/dpll.h"

std::string format_solution(const std::vector<int>& assignment) {
    if (assignment.empty()) {
        return "";
    }
    
    std::unordered_map<int, bool> var_assignments;
    for (int lit : assignment) {
        int var = std::abs(lit);
        var_assignments[var] = lit > 0;
    }
    
    std::string solution;

    std::vector<int> sorted_vars;
    for (const auto& [var, _] : var_assignments) {
        sorted_vars.push_back(var);
    }
    std::sort(sorted_vars.begin(), sorted_vars.end());
    
    bool first = true;
    for (int var : sorted_vars) {
        if (!first) {
            solution += " ";
        }
        first = false;
        solution += std::to_string(var) + " " + (var_assignments[var] ? "true" : "false");
    }
    
    return solution;
}

int main(int argc, char* argv[]) {
    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " <cnf file>" << std::endl;
        return 1;
    }
    
    const std::string input_file = argv[1];
    const std::string filename = std::filesystem::path(input_file).filename().string();
    
    try {
        // Parse CNF file
        std::vector<std::vector<int>> clauses = parse_cnf_file(input_file);
        
        // Create and run solver
        DPLLSolver solver(clauses);
        
        auto start_time = std::chrono::high_resolution_clock::now();
        auto [is_sat, assignment] = solver.solve();
        auto end_time = std::chrono::high_resolution_clock::now();
        
        std::chrono::duration<double> elapsed_seconds = end_time - start_time;
        
        std::string result = is_sat ? "SAT" : "UNSAT";
        std::string solution_str = is_sat ? ", \"Solution\": \"" + format_solution(assignment) + "\"" : "";
        
        // Add solver statistics
        std::cout << "{\"Instance\": \"" << filename 
                  << "\", \"Time\": " << elapsed_seconds.count() 
                  << ", \"Result\": \"" << result << "\""
                  << ", \"Decisions\": " << solver.getNumDecisions()
                  << ", \"Propagations\": " << solver.getNumPropagations()
                  << solution_str << "}" << std::endl;
        
    } catch (const std::exception& e) {
        std::cerr << "Error occurred: " << e.what() << std::endl;
        return 1;
    }
    
    return 0;
} 