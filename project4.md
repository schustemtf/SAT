# Project 4: SAT Solving with Watches

Welcome to Project 4! This project focuses on implementing watches, a critical data structure in modern SAT solvers, and additional optimization techniques to enhance solver performance.

## Task Requirements

1. **Implement Watches**: Your primary task is to implement the watches data structure. Watches give an order-of-magnitude improvement.
2. **Choose Optimization Techniques**: Alongside watches, you must select and implement one or more optimization techniques. You have the flexibility to choose from the following options:

- **Reduce**: Implement clause reduction, a method that simplifies the formula by eliminating redundant or subsumed clauses.
- **VSIDS**: Implement the VSIDS heuristic, which assigns scores to variables based on their influence on conflict detection.
- **Restarts**: Implement restarts, a technique that periodically restarts the search process to avoid getting stuck in local optima. We recommend restarts since they are relatively easy to implement and can significantly improve solver performance.

**Get Started with babysat.cpp**: You can begin your implementation using the provided template babysat.cpp located in the current directory, or choose your code from the last projects.

**Utilize SAT Solver Debugging**: On our [website](https://cca.informatik.uni-freiburg.de/sat/ss23/debug.html), you can find methods for effectively debugging and analyzing SAT solvers.

## Project Timeline

- **Deadline**: Submit your project by 17th July 23:55.
- **Presentation**: The presentation will take place on 20th July.

Happy coding!