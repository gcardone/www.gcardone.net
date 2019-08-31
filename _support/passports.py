#!/usr/bin/env python3

import csv
import collections
from ortools.sat.python import cp_model

PRINT_PROGRESS=True

class SolverCallback(cp_model.CpSolverSolutionCallback):
    """SolverCallback prints intermediate solutions."""

    def __init__(self, variables):
        """ Builds a new SolverCallback.

        Args:
          variables: list of variables to print.
        """
        super().__init__()
        self._variables = variables
        self._solution_count = 0

    def on_solution_callback(self):
        self._solution_count += 1
        selected = []
        print(f'Solution {self._solution_count}')
        # Print only the selected passports, which are far fewer than the
        # complete list of passports
        for v in self._variables:
            if self.Value(v):
                selected.append(str(v))
        print('%d: %s\n' % (len(selected), ', '.join(selected)))


if __name__ == '__main__':
    # m is the Constraint Programming model
    m = cp_model.CpModel()

    # visa_free is a map from a destination country to the set of passport
    # that allow visa free travel
    visa_free = collections.defaultdict(set)

    # passport_vars maps passport names to variables managed by the CP-SAT
    # model
    passport_vars = {}

    # Load the passport data, provided by
    # https://github.com/ilyankou/passport-index-dataset/ , each row is in
    # the format:
    # passport country, destination country, <type of access>
    with open('passport-index-tidy.csv', 'r') as f:
        datareader = csv.reader(f)
        for row in datareader:
            # p is the passport being used
            p = row[0]
            # d is the destination country
            d = row[1]
            p_var = passport_vars.setdefault(p, m.NewBoolVar(p))
            # '3' represents visa-free travel, '-1' means that the passport
            # is issued by the destination country
            if row[2] == '3' or row[2] == '-1':
                # Add passport p_var to the set of passports that allow
                # visa-free travel to country d_var
                visa_free[d].add(p_var)

    # For each set of passports that allows visa-free travelling to a country…
    for destination, allowed_passports in visa_free.values():
        # …at least one of the passports must be selected
        m.Add(sum(allowed_passports) >= 1)

    # We also want to minimize the number of selected passports
    m.Minimize(sum(passport_vars.values()))

    solver = cp_model.CpSolver()
    if PRINT_PROGRESS:
        sorted_vars = [passport_vars[p] for p in sorted(passport_vars)]
        # Build a SolverCallback that prints all the selected passports
        # whenever a solution (possibly non-optimal) is found
        solution_printer = SolverCallback(sorted_vars)
        status = solver.SolveWithSolutionCallback(m, solution_printer)
    else:
        status = solver.Solve(m)

    if status == cp_model.OPTIMAL:
        selected_passports = [p for p in passport_vars
                              if solver.Value(passport_vars[p])]
        print(', '.join(sorted(selected_passports)))
    else:
        print('Unable to find an optimal solution')
