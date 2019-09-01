#!/usr/bin/env python3

import csv
import z3

if __name__ == '__main__':
    optimizer = z3.Optimize()

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
            if p in passport_vars:
                p_var = passport_vars[p]
            else:
                p_var = z3.Int(p)
                optimizer.add(p_var >= 0, p_var <= 1)
                passport_vars[p] = p_var
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
        optimizer.add(sum(allowed_passports) >= 1)

    # We also want to minimize the number of selected passports
    optimizer.minimize(sum(passport_vars.values()))

    if optimizer.check() == z3.sat:
        m = optimizer.model()
        selected_passports = []
        for p_name, p_var in passport_vars.items():
            if m[p_var] == 1:
                selected_passports.append(p_name)
        selected_passports.sort()
        print('Passports: %d' % len(selected_passports))
        print(', '.join(selected_passports))
    else:
        print('Unable to find an optimal solution')
