#!/usr/bin/env python3

import csv
import time
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
        self._start = time.time()

    def on_solution_callback(self):
        self._solution_count += 1
        selected = []
        delta = time.time() - self._start
        print(f'Solution {self._solution_count} after {delta:.2f} seconds')
        # Print only the selected passports, which are far fewer than the
        # complete list of passports
        for v in self._variables:
            if self.Value(v):
                selected.append(str(v))
        print('%d: %s\n' % (len(selected), ', '.join(selected)))


if __name__ == '__main__':
    # model is the Constraint Programming model
    model = cp_model.CpModel()

    # visa_free is a map from a destination country to the set of passport
    # that allow visa free travel
    visa_free = {}

    # passport_vars maps passport names to variables managed by the CP-SAT
    # model
    passport_vars = {}

    # Load the passport data, provided by
    # https://github.com/ilyankou/passport-index-dataset/ , each row is in
    # the format:
    # passport country, destination country, <type of access>
    with open('passport-index-tidy.csv', 'r') as f:
        datareader = csv.reader(f)
        # skip the header
        next(datareader, None)
        for row in datareader:
            # p is the passport being used
            p = row[0]
            # d is the destination country
            d = row[1]
            p_var = passport_vars.setdefault(p, model.NewBoolVar(p))
            passport_set = visa_free.setdefault(d, set())
            # '3' represents visa-free travel, '-1' means that the passport
            # is issued by the destination country
            if row[2] == '3' or row[2] == '-1':
                # Add passport p_var to the set of passports that allow
                # visa-free travel to country d_var
                visa_free[d].add(p_var)

    # For each set of passports that allows visa-free travelling to a country…
    for destination, allowed_passports in visa_free.items():
        if not allowed_passports:
            print(f'No valid passports for {destination}. Ignoring.')
            continue
        # …at least one of the passports must be selected
        model.Add(sum(allowed_passports) >= 1)

    # We also want to minimize the number of selected passports
    model.Minimize(sum(passport_vars.values()))

    solver = cp_model.CpSolver()
    if PRINT_PROGRESS:
        sorted_vars = [passport_vars[p] for p in sorted(passport_vars)]
        # Build a SolverCallback that prints all the selected passports
        # whenever a solution (possibly non-optimal) is found
        solution_printer = SolverCallback(sorted_vars)
        status = solver.SolveWithSolutionCallback(model, solution_printer)
    else:
        status = solver.Solve(model)

    if status == cp_model.OPTIMAL:
        selected_passports = [p for p in passport_vars
                              if solver.Value(passport_vars[p])]
        print(', '.join(sorted(selected_passports)))
    else:
        print('Unable to find an optimal solution')
