#!/usr/bin/env python3

import itertools
import pudb
import sys
import z3

def rows():
    """Returns the indexes of rows."""
    return range(0, 9)


def cols():
    """Returns the indexes of columns."""
    return range(0, 9)


def sudoku_from_string(s):
    """Builds a sudoku from a string.

    Args:
        s: string representing a sudoku cell by cell from the top row to the
        bottom road. Admissible characters are 0-9 for known values, . for
        unknown values, and \n (ignored).

    Returns:
      A dictionary (int, int) -> int representing the known values of the
      puzzle. The first int in the tuple is the row (i.e.: y coordinate),
      the second int is the column (i.e.: x coordinate).
    """
    valid_chars = set([str(x) for x in range(1, 10)])
    valid_chars.add('.')
    sudoku = {}
    if len(s) != 81:
        raise ValueError('wrong input size')
    invalid_chars = set(s).difference(valid_chars)
    if invalid_chars:
        err_str = ', '.join(invalid_chars)
        raise ValueError('unexpected character(s): %s' % err_str)
    for r in rows():
        for c in cols():
            char = s[0]
            if char != '.':
                sudoku[(r, c)] = s[0]
            s = s[1:]
    return sudoku


def read_sudoku(f):
    """Reads a sudoku from a file-like object.

    Args:
        f: file object.

    Returns: dictionary (int, int) -> int. See sudoku_from_string for details.
    """
    sudoku = {}
    invar = ''
    valid_chars = set([str(x) for x in range(1, 10)])
    valid_chars.add('.')
    for l in f:
        line = l.strip()
        invar = invar + line
    return sudoku_from_string(invar)


def classic_constraints(s, cells):
    """Adds the classic sudoku constraints to a z3 solver.

    Args:
        s: z3.Solver instance.
        cells: a 9x9 list of lists, where each element is a z3.Int instance.
    """
    # All values must be 1 <= x <= 9.
    for r in rows():
        for c in cols():
            v = cells[r][c]
            s.add(v >= 1)
            s.add(v <= 9)

    # All cells on the same row must be distinct.
    for r in rows():
        s.add(z3.Distinct(cells[r]))

    # All cells on the same column must be distinct.
    for c in cols():
        col = [cells[r][c] for r in rows()]
        s.add(z3.Distinct(col))

    # All cells in a 3x3 matrix must be distinct.
    offsets = list(itertools.product(range(0, 3), range(0, 3)))
    for r in range(0, 9, 3):
        for c in range(0, 9, 3):
            group_cells = []
            for dy, dx in offsets:
                group_cells.append(cells[r+dy][c+dx])
            s.add(z3.Distinct(group_cells))


def valid_coords(c, r):
    """Checks if a column and a row index are within the puzzle bounds.

    Args:
        c: int, column index.
        r: int, row index.

    Returns:
        True if c and r are valid sudoku indexes.
    """
    return (0 <= c <= 8) and (0 <= r <= 8)


def apply_constraints(cells, offsets, symmetrical):
    """Yields all the pairs of cells at a given offset from each other.

    Args:
        cells: a 9x9 list of lists, where each element is a z3.Int instance.
        offsets: a list of relative offsets. Each offset is a (dy, dx) tuple.
                 dy is the row offset, dx is the column offset.
        symmetrical: if true, each pair of cells is yielded only once,
                     otherwise both (cell_a, cell_b) and (cell_b, cell_a) are
                     yielded.

        Yields:
            Two z3.Int references.
    """
    pairs = set()
    for r in rows():
        for c in cols():
            v = cells[r][c]
            for dy, dx in offsets:
                # Get the coordinates of a candidate cell.
                y = r + dy
                x = c + dx
                if not valid_coords(y, x):
                    continue
                pair = tuple(sorted([(r, c), (y, x)]))
                if symmetrical and (pair in pairs):
                    continue
                pairs.add(pair)
                t = cells[y][x]
                yield v, t


def miracle_constraints(s, cells):
    """Adds the miracle sudoku constraints to a z3 solver.

    Args:
        s: z3.Solver instance.
        cells: a 9x9 list of lists, where each element is a z3.Int instance.
    """
    # Knight constraint: all cells that are separated by a chess
    # knight's move must be different. A knight moves following an L shape,
    # where the long bit is 2 cells long and the short bit is 1 cell long.
    # The list below includes all the possible orientations.
    offsets = ((1,-2), (2, -1), (2, 1), (1, 2), (-1, 2), (-2, 1), (-2, -1), (-1, -2))
    for v, t in apply_constraints(cells, offsets, True):
        s.add(v != t)

    # King constraint: all cells that are separated by a chess king's move
    # must be different. The list below does not include vertical and
    # horizontal offsets because they are already enforced by the classical
    # sudoku constraints.
    offsets = list(itertools.product((-1, 1), (-1, 1)))
    for v, t in apply_constraints(cells, offsets, True):
        s.add(v != t)

    # Orthogonal constraint: two orthogonally adjacent cell cannot contain
    # consecutive digits. Note that this relationship is not symmetrical,
    # so we ask apply_constraint to return both (cell_a, cell_b) and
    # (cell_b, cell_a).
    offsets = ((0, -1), (1, 0), (0, 1), (-1, 0))
    for v, t in apply_constraints(cells, offsets, False):
        s.add(t - v != 1)


def add_constraints(s, cells):
    classic_constraints(s, cells)
    miracle_constraints(s, cells)

def solve_sudoku(known_values):
    s = z3.Solver()
    # Create a matrix of None, which will be replaced by Z3 variables. 
    cells = [ [ None for _ in cols() ] for _ in rows() ]
    for r in rows():
        for c in cols():
            # Z3 variables have a name
            v = z3.Int('c_%d_%d' % (r, c))
            cells[r][c] = v
            # If this cell contains a hint, then add a constraint that force
            # the current variable to be equal to the hint.
            if (r, c) in known_values:
                s.add(v == known_values[(r, c)])

    add_constraints(s, cells)
   
    num_sol = 1
    while s.check() == z3.sat:
        print('Solution %d' % num_sol)
        num_sol += 1
        m = s.model()
        # This list will contain the list of new constraints to search for a
        # different solution
        next_sol_constraints = []
        for r in rows():
            for c in cols():
                v = m.evaluate(cells[r][c])
                # We want this cell to have a different value, if possible
                next_sol_constraints.append(cells[r][c] != v.as_long())
                print(v, end=' ')
                if (c+1) % 3 == 0:
                    print('  ', end='')
            print()
            if (r+1) % 3 == 0:
                print()
        # We want at least one of the current values to be different in the
        # next solution
        s.add(z3.Or(next_sol_constraints))
        print()


if __name__ == '__main__':
    if len(sys.argv) == 2:
        with open(sys.argv[1]) as f:
            known_values = read_sudoku(f)
    else:
        known_values = read_sudoku(sys.stdin)
    solve_sudoku(known_values)
