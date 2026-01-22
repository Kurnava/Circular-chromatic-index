# Circular-chromatic-index
This repository contains source code and components developed for my Annual Project.


# Important Note
These files are not standalone. They are designed to work as a part of external library and require the [ba-graph-library] to function correctly. The code provided here serves as a showcase of my current progress and implementation logic.


# Project Structure & File Mapping
To better understand the implementation, here is how the source files relate to the project goals:


# Algorithmic Optimization
**paths.hpp**: Contains the optimized backtracking implementations for circuit enumeration, including **all_circuits_fast** and **all_circuits_fast_mod**. This is the core of the speed-up for SAT clause generation.


# Exact Methods (Solvers)
**sat/cnf_circular_colouring.hpp**: Implements the logic for generating SAT clauses, including GCD reduction and tight cycle detection.

**sat/exec_circular_colouring.hpp**: The execution wrapper for standard SAT solvers (e.g., Kissat).

**sat/exec_circular_cpsat.hpp**: Integration with Google OR-Tools CP-SAT solver, providing a constraint programming alternative for complex instances.


# Heuristic Methods & Invariants
**invariants/fractional_cvd.hpp**: Contains the randomized heuristic solver based on local search (inspired by Cluster Vertex Deletion methods) used for fast verification of larger graphs.


# Testing Suite
**tests/invariants/test_fractional_cvd.cpp**: Validation of the heuristic and CVD-related logic.

**tests/sat/test_circular_colouring.cpp**: Standard regression tests for the SAT solver.

**tests/sat/test_circular_colouring_cpsat.cpp**: Tests specifically for the CP-SAT integration.

**tests/sat/test_circular_colouring_slow.cpp**: A dedicated suite for "slow" tests, targeting larger or more complex graph instances to verify performance limits.
