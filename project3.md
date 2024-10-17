# Project 3 Basic CDCL

Your task in project 3 is to implement a basic CDCL solver with implication graph analysis, deriving and learning a new clause, which is then used for conflict driven backjumping.   In this basic form where the learned clause contains all the decisions on which the conflict depends the code will be very similar to `babysat-backjumping/babysat.cpp` which you find in the `babysats.zip` archive.

Optionally, you might want to implement the first-unique implication point analysis, which simply resolves stamped literals of on the trail backwards which are assigned on the current decision level where the conflict occurs.  Project 4 will be about implementing optimizations to this scheme include minimization (if you already have done the first UIP analysis) and/or clause database reduction and/or restarts and/or watched data structures.

As before please make sure that your code prints your name and submit `babysat.cpp` through ILIAS until June 26 and be prepared to present it in the exercise class on June 29.
