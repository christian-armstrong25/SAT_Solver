#include <fstream>
#include <sstream>
#include <string>

std::vector<std::vector<int>> parse_cnf_file(const std::string& filename) {
    std::vector<std::vector<int>> clauses;
    std::ifstream file(filename);
    
    if (!file.is_open()) {
        throw std::runtime_error("Error: DIMACS file not found: " + filename);
    }
    
    int num_vars = 0;
    int num_clauses = 0;
    std::string line;
    
    // Skip comment lines and find problem line
    while (std::getline(file, line)) {
        // Skip empty lines
        if (line.empty()) {
            continue;
        }
        
        std::istringstream iss(line);
        char first_char;
        iss >> first_char;
        
        // Skip comment lines
        if (first_char == 'c') {
            continue;
        }
        
        // Process problem line
        if (first_char == 'p') {
            std::string format;
            iss >> format;
            
            if (format != "cnf") {
                throw std::runtime_error("Error: DIMACS file format is not CNF");
            }
            
            iss >> num_vars >> num_clauses;
            
            if (num_vars <= 0 || num_clauses <= 0) {
                throw std::runtime_error("Error: Invalid number of variables or clauses");
            }
            
            break;
        }
    }
    
    // Check if we found the problem line
    if (num_vars == 0 || num_clauses == 0) {
        throw std::runtime_error("Error: DIMACS file does not have valid problem line");
    }
    
    // Parse clauses
    while (std::getline(file, line)) {
        // Skip empty lines and comments
        if (line.empty() || line[0] == 'c') {
            continue;
        }
        
        std::istringstream iss(line);
        std::vector<int> clause;
        int literal;
        
        while (iss >> literal) {
            if (literal == 0) {
                break; 
            }
            
            if (literal != 0) { 
                clause.push_back(literal);
            }
        }
        
        if (!clause.empty()) { 
            clauses.push_back(clause);
        }
    }
    
    if (static_cast<int>(clauses.size()) != num_clauses) {
        throw std::runtime_error("Error: Expected " + std::to_string(num_clauses) + 
                                 " clauses but got " + std::to_string(clauses.size()));
    }
    
    return clauses;
} 