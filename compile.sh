#!/bin/bash

########################################
############# CSCI 2951-O ##############
########################################

# Compile C++ code with g++
g++ -std=c++17 -Wall -Ofast -flto -march=native -funroll-loops -fomit-frame-pointer -I src/ src/main.cpp src/dimacs_parser.cpp src/solvers/dpll.cpp -o dpll_solver