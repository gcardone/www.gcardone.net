#!/usr/bin/env python3
# /// script
# dependencies = [
#     "num2words",
#     "unidecode",
#     "z3-solver",
# ]
# ///
import collections
import string
import z3
import pudb
from num2words import num2words
from unidecode import unidecode

LETTERS = string.ascii_lowercase
VALID_NUMBERS = 20


def spell_number(n):
    if n == 1:
        return 'una'
    return num2words(n, lang='it')


def string_to_count(s):
    # Strip accents, and keep only a-z characters in s
    s = [c for c in unidecode(s).lower() if c in LETTERS]
    count = collections.Counter(s)
    res = {}
    for c in LETTERS:
        if c in count:
            res[c] = count[c]
        else:
            res[c] = 0
    return res


def add_count_implications(solver, counters, counter_to_spelled):
    for c in LETTERS:
        print(f'Adding counts for {c}')
        v = z3.Int(c)
        solver.add(v >= 0)
        solver.add(v <= VALID_NUMBERS)
        counters[c] = v
        subcount = {}
        counter_to_spelled[c] = subcount
        for subc in LETTERS:
            subcount[subc] = z3.Int(f'{c}_{subc}')
            solver.add(subcount[subc] >= 0)
            solver.add(subcount[subc] <= VALID_NUMBERS)
        for i in range(0, VALID_NUMBERS+1):
            counts = string_to_count(spell_number(i))
            for subc, count in counts.items():
                solver.add(z3.Implies(v == i, subcount[subc] == count))


def add_sum_count(solver, counters, counter_to_spelled):
    for c in LETTERS:
        print(f'Adding self-referential constraints for {c}')
        v = counters[c]
        l = [z3.IntVal(1), z3.IntVal(seed_count[c])]
        for subc in LETTERS:
            l.append(counter_to_spelled[subc][c])
        solver.add(v == sum(l))


if __name__ == '__main__':
    solver = z3.Solver()
    seed_sentence = 'Questa frase ha '
    seed_count = string_to_count(seed_sentence)
    counter_to_spelled = {}
    counters = {}
    add_count_implications(solver, counters, counter_to_spelled)
    add_sum_count(solver, counters, counter_to_spelled)
    print()
    if solver.check() == z3.sat:
        m = solver.model()
        print('Found a solution: ')
        sol = []
        for c in sorted(LETTERS):
            v = m.evaluate(counters[c]).as_long()
            w = spell_number(v)
            sol.append(f'{w} {c}')
        sentence = ', '.join(sol)
        print(f'{seed_sentence} {sentence}')
    else:
        print('No solutions found')
