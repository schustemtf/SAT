# Project 2 Optimized DPLL SAT Solver

This second project is due on June 12 at 23:55.  You are supposed to add counters (this is the goal of the exercise and a must to have) and optionally other optimizations either to your project 1 code or the model solution in `babysat-dpll.zip` given here. Again just modify `babysat.cpp` and submit this single file through ILIAS (after replacing 'Armin Biere' with your name).

The presentation of solutions will take place in the same week on June 15.

You will need to present your projects at least twice during the semester.

As other optimizations you can simplify checking for the formula to be satisfied, work on better decision heuristics (implement DLIS), or alternatively connect to the miracle library developed by Michele Collevati during his master thesis.

The provided newer version 0.0.1 of `babysat-dpll` has some optimized data structures, measures execution time during running the test cases and also has a conflict limit option (`babysat -c 1000000` limits the number of conflicts to a million).   If as in my case the original DPLL version with clauses remains faster than the counter-based version, you can also submit two versions (via a single zip file containing your two variants of `babysat.cpp` named appropriately).

GPU parallelism for SAT solving heuristics  
<https://ceur-ws.org/Vol-3204/paper_3.pdf>  
<http://clp.dimi.uniud.it/sw/>  
<https://github.com/Colle11/MiraCle>