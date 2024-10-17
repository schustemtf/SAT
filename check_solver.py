"""
Check Solver

Given a CNF file in DIMACS format and a log file, check whether all moves of the SAT solver were
legal. The log file has to be in following format:

c DEBUG 0 assign 65
c DEBUG 0 decide -2
c DEBUG 2 conflict
c DEBUG 2 unassign -306@2=2
"""

import re
import argparse


def parse_dimacs(filename):
    """
    Parse a DIMACS file and return the CNF represented as a
    list of lits of ints.
    """
    with open(filename, "r", encoding="utf-8") as file:
        content = file.read()
    clauses = content.split("\n")[:-1]
    clauses.pop(0) # pop header
    clauses = [x[:-2] for x in clauses]
    cnf = []
    for clause in clauses:
        cnf.append(list(map(int, clause.split())))
    return cnf


def is_implied(var, cnf, assignments):
    """
    Return True is a variable is implied by the formula.
    """
    for clause in cnf:
        if var not in clause:
            continue
        if all((-y in assignments for y in (x for x in clause if x != var))):
            return True
    return False


def possible_propagations(cnf, assignments):
    """
    Return a list of units (literals) that is implied by the formula.
    """
    propagations = []
    for clause in cnf:
        if len(clause) == 1 and clause[0] not in assignments:
            propagations.append(clause[0])
        else:
            assigned_opposite = [lit for lit in clause if -lit in assignments]
            unassigned = [
                lit for lit in clause if abs(lit) not in [abs(x) for x in assignments]
            ]
            if len(assigned_opposite) == len(clause) - 1 and len(unassigned) == 1:
                propagations.append(unassigned[0])
    return propagations


def check_conflict(cnf, assignments):
    """
    Return true if there is a conflict.
    """
    for clause in cnf:
        if all((abs(lit) in (abs(x) for x in assignments) for lit in clause)):
            if all((-x in assignments for x in clause)):
                return True
        else:
            continue
    return False


def check_sat_solver(cnf_file, log_file):
    """
    Given a CNF file and a log file, check whether the SAT solver
    only made legal moves.
    """
    cnf = parse_dimacs(cnf_file)
    assignments = []
    decision = False
    with open(log_file, "r", encoding="utf-8") as file:
        for line in file:
            if " assign" in line or " decide" in line:
                var = int(
                    re.search(r"(?:assign|decide) [-]*\d+", line)
                    .group()
                    .replace("assign ", "")
                    .replace("decide ", "")
                )
                if "decide" in line:
                    # If we decide, we must ensure no further propagations were possible
                    propagations = possible_propagations(cnf, assignments)
                    if len(propagations) > 0:
                        print(
                            f"FAULT: Decision made on {var}, but propagations {propagations} were possible"
                        )
                        return False
                    assignments.append(var)
                    decision = True
                else:
                    if decision:
                        decision = False
                        continue
                    # If we assign, we must ensure this was implied by the CNF
                    if not is_implied(var, cnf, assignments):
                        print(f"FAULT: Propagation {var} not implied by the formula")
                        return False
                    assignments.append(var)
            elif "unassign" in line:
                var = int(
                    re.search(r"unassign [-]*\d+", line).group().replace("unassign ", "")
                )
                assert var in assignments
                assignments.pop(assignments.index(var))
            elif re.search(r"DEBUG \d+ conflict", line) is not None:
                if not check_conflict(cnf, assignments):
                    print("FAULT: SAT solver detected conflict, although there is none")
                    return False
    return True


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Check the sanity of SAT solver propagations using log files"
    )

    parser.add_argument(
        "--cnf-file",
        type=str,
        required=True,
    )
    parser.add_argument(
        "--log-file",
        type=str,
        required=True,
    )

    args = parser.parse_args()

    if check_sat_solver(args.cnf_file, args.log_file):
        print("Found no faults in SAT solver")