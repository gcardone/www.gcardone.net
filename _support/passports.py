#!/usr/bin/env python3

import csv
import collections
from ortools.sat.python import cp_model

if __name__ == '__main__':
    m = cp_model.CpModel()
    visa_free = collections.defaultdict(set)
    passports = {}
    destinations = {}
    with open('passport-index-tidy.csv', 'r') as f:
        datareader = csv.reader(f)
        for row in datareader:
            p = row[0]
            d = row[1]
            if p not in passports:
                passports[p] = m.NewBoolVar(p)
            if d not in destinations:
                destinations[d] = m.NewBoolVar(f'{d} country')
            if row[2] == '3' or row[2] == '-1':
                visa_free[d].add(p)
    for destination, allowed_passports in visa_free.items():
        p_vars = [passports[p] for p in allowed_passports]
        d_var = destinations[destination]
        m.Add(sum(p_vars) >= 1).OnlyEnforceIf(d_var)
        if len(allowed_passports) == 1:
            m.AddHint(p_vars[0], 1)
            print(f'{p_vars[0]} is required')
    m.Add(sum(destinations.values()) == len(destinations))
    m.Minimize(sum(passports.values()))
    solver = cp_model.CpSolver()
    status = solver.Solve(m)
    for p in sorted(passports):
        if solver.Value(passports[p]):
            print(f'{p}')
