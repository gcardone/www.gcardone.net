---
layout: post
title:  "Solving the Miracle Sudoku with Microsoft Z3"
date:   2020-06-03
excerpt: >
  Solving a miracle sudoku using the Z3 solver.
---

* ToC
{:toc}

# The miracle sudoku

Recently a video of a man solving a particularly hard sudoku went viral:

<iframe width="560" height="315" src="https://www.youtube-nocookie.com/embed/yKf9aUIxdb4" frameborder="0" allow="accelerometer; autoplay; encrypted-media; gyroscope; picture-in-picture" allowfullscreen></iframe>

At the time of writing it was watched 930k times. It's a surprising video because this sudoku puzzle it contains only two clues, yet it has a unique solution. In this article I'll show how to solve it using [Microsoft Z3](https://github.com/Z3Prover/z3) with Python.

Writing the solution took me longer than 25 minutes, so Simon Anthony in the video above was strictly faster than me :)

# Miracle sudoku rules

Unless you've been living under a rock you already know the rules of [modern sudoku](https://en.wikipedia.org/wiki/Sudoku): the goal is to fill a 9×9 grid divided into 3×3 subgrids (called _boxes_ or _blocks_) with all the digits from 1 to 9 included so that each row, columns, and box contains all the digits from 1 to 9 exactly once. A proper sudoku has only one solution.

The *miracle sudoku* solved by Simon Anthony in the video above has several additional rules:

- Any two cells separated by a knght's move or a king's move (in chess) cannot contain the same digit.
- Any two orthogonally adjacent cells cannot contain consecutive digits.

The sudoku in the video above starts with only two hints and yet it has a unique solution.

<table>
<tbody>
<tr>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
</tr>
<tr>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
</tr>
<tr style="border-bottom:2px solid black">
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
</tr>
<tr>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
</tr>
<tr>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">1</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
</tr>
<tr style="border-bottom:2px solid black">
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">2</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
</tr>
<tr>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
</tr>
<tr>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
</tr>
<tr>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%" style="border-right:2px solid black">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
<td style="width:11%">&nbsp;</td>
</tr>
</tbody>
</table>

# Solving a traditional sudoku

Let's start with solving a traditional sudoku. As first step we can encode a sudoku as a string with digits from `0` to `9`, and `.` to mark unknown cells. By convention we will refer to cells using coordinates using a 0-indexed (row, column) format: the top left cell is (0, 0), the top right cell is (0, 8), and the bottom right cell is (8, 8).

We can use a couple of helper functions to read a sudoku:

```python
#!/usr/bin/env python3

import itertools
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

# the code continues in the next snippet
```

Now that we can read a sudoku, we can solve it! The procedure is straightforward:

1. Create a Z3 _solver_. A solver contains _variables_ and _constraints_, and will look for variables that satisfy all the constraints.
1. For each variable, if it is in the same position of a hint of the sudoku, add a constraint requiring the variable to the equal to the hint
1. Add all the sudoku constraints:
   1. All variables must be between `0` and `9` (included)
   1. All variables on the same column must be disjoint (i.e.: different from each other)
   1. All variables on the same row must be disjoint
   1. All variables in the same box must be disjoint
1. Ask the solver if the constraint can be satisfied and if they can:
   1. Get a _model_ from the solver.
   1. Print the value of all the variables in the model.

Z3's python API allows to translate these steps almost literally:

```python
# Main: read a sudoku from a file or stdin
if __name__ == '__main__':
    if len(sys.argv) == 2:
        with open(sys.argv[1]) as f:
            known_values = read_sudoku(f)
    else:
        known_values = read_sudoku(sys.stdin)
    solve_sudoku(known_values)


def solve_sudoku(known_values):
    """Solves a sudoku and prints its solution.

    Args:
      known_values: a dictionary of (int, int) -> int representing the known
                    values in a sudoku instance (i.e.: hints). The first int in
                    the tuple of the keys is the row (0-indexed), the second
                    one is the column (0-indexed).
    """
    # Create a Z3 solver
    s = z3.Solver()
    # Create a matrix of None, which will be replaced by Z3 variables. This
    # is our sudoku.
    cells = [ [ None for _ in cols() ] for _ in rows() ]
    for r in rows():
        for c in cols():
            # Z3 variables have a name
            v = z3.Int('c_%d_%d' % (r, c))
            # Keep a reference to the Z3 variable in our sudoku.
            cells[r][c] = v
            # If this cell contains a hint, then add a constraint that force
            # the current variable to be equal to the hint.
            if (r, c) in known_values:
                s.add(v == known_values[(r, c)])

    # This function adds all the constraints of a classic sudoku
    add_constraints(s, cells)
    
    if s.check() == z3.sat:
        # Retrieve the model from the solver. In this model all the variables
        # are grounded (i.e.: they have a value)
        m = s.model()
        for r in rows():
            for c in cols():
                # Retrieve the grounded value and print it.
                v = m.evaluate(cells[r][c])
                print(v, end=' ')
                # Add vertical spacing for a subgrid
                if (c+1) % 3 == 0:
                    print('  ', end='')
            print()
            # Add horizontal spacing for a subgrid
            if (r+1) % 3 == 0:
                print()
        print()

def add_constraints(s, cells):
    classic_constraints(s, cells)

```

`classic_constraint` is the function that receives a Z3 solver and the integer variables and implements the constraints of a classic sudoku:

```python
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

    # All cells in a 3x3 subgrid must be distinct: for each top left cell of
    # each subgrid select all the other cells in the same subgrid.
    offsets = list(itertools.product(range(0, 3), range(0, 3)))
    for r in range(0, 9, 3):
        for c in range(0, 9, 3):
            group_cells = []
            for dy, dx in offsets:
                group_cells.append(cells[r+dy][c+dx])
            s.add(z3.Distinct(group_cells))
```

That's it. That's all we need to solve a classic sudoku.

{::options parse_block_html="true" /}

<details><summary markdown="span">Click here to see the complete code.</summary>
```python
#!/usr/bin/env python3

import itertools
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


def solve_sudoku(known_values):
    """Solves a sudoku and prints its solution.

    Args:
      known_values: a dictionary of (int, int) -> int representing the known
                    values in a sudoku instance (i.e.: hints). The first int in
                    the tuple of the keys is the row (0-indexed), the second
                    one is the column (0-indexed).
    """
    # Create a Z3 solver
    s = z3.Solver()
    # Create a matrix of None, which will be replaced by Z3 variables. This
    # is our sudoku.
    cells = [ [ None for _ in cols() ] for _ in rows() ]
    for r in rows():
        for c in cols():
            # Z3 variables have a name
            v = z3.Int('c_%d_%d' % (r, c))
            # Keep a reference to the Z3 variable in our sudoku.
            cells[r][c] = v
            # If this cell contains a hint, then add a constraint that force
            # the current variable to be equal to the hint.
            if (r, c) in known_values:
                s.add(v == known_values[(r, c)])

    # This function adds all the constraints of a classic sudoku
    add_constraints(s, cells)
    
    if s.check() == z3.sat:
        # Retrieve the model from the solver. In this model all the variables
        # are grounded (i.e.: they have a value)
        m = s.model()
        for r in rows():
            for c in cols():
                # Retrieve the grounded value and print it.
                v = m.evaluate(cells[r][c])
                print(v, end=' ')
                # Add vertical spacing for a subgrid
                if (c+1) % 3 == 0:
                    print('  ', end='')
            print()
            # Add horizontal spacing for a subgrid
            if (r+1) % 3 == 0:
                print()
        print()

def add_constraints(s, cells):
    classic_constraints(s, cells)


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

    # All cells in a 3x3 subgrid must be distinct: for each top left cell of
    # each subgrid select all the other cells in the same subgrid.
    offsets = list(itertools.product(range(0, 3), range(0, 3)))
    for r in range(0, 9, 3):
        for c in range(0, 9, 3):
            group_cells = []
            for dy, dx in offsets:
                group_cells.append(cells[r+dy][c+dx])
            s.add(z3.Distinct(group_cells))

# Main: read a sudoku from a file or stdin
if __name__ == '__main__':
    if len(sys.argv) == 2:
        with open(sys.argv[1]) as f:
            known_values = read_sudoku(f)
    else:
        known_values = read_sudoku(sys.stdin)
    solve_sudoku(known_values)
```
</details>
<br/>

{::options parse_block_html="false" /}

We can test that this works properly:

```bash
$ cat sudoku_classic
....1..3.
..9..5..8
8.4..6.25
......6..
..8..4...
12..87...
3..9..2..
.65..8...
9........
$ time ./sudoku_solver.py sudoku_classic
7 5 2   8 1 9   4 3 6   
6 3 9   2 4 5   7 1 8   
8 1 4   7 3 6   9 2 5   

4 7 3   5 9 2   6 8 1   
5 9 8   1 6 4   3 7 2   
1 2 6   3 8 7   5 4 9   

3 8 7   9 5 1   2 6 4   
2 6 5   4 7 8   1 9 3   
9 4 1   6 2 3   8 5 7   



real    0m0.148s
user    0m0.157s
sys     0m0.016s
```

Not too shabby for code that is expressive and does not use any specialized algorithms. We can now add the constraints to solve a miracle sudoku

# Solving a miracle sudoku

It turns out to be _really_ simple. We just need to add more constraints.

```python
def add_constraints(s, cells):
    classic_constraints(s, cells)
    miracle_constraints(s, cells)

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
    offsets = ((1,-2), (2, -1), (2, 1), (1, 2), (-1, 2), (-2, 1), (-2, -1),
               (-1, -2))
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

```

We can test this on the original Miracle Sudoku:

```bash
$ cat sudoku_miracle
.........
.........
.........
.........
..1......
......2..
.........
.........
.........
$ time ./sudoku_solver.py sudoku_miracle
4 8 3   7 2 6   1 5 9   
7 2 6   1 5 9   4 8 3   
1 5 9   4 8 3   7 2 6   

8 3 7   2 6 1   5 9 4   
2 6 1   5 9 4   8 3 7   
5 9 4   8 3 7   2 6 1   

3 7 2   6 1 5   9 4 8   
6 1 5   9 4 8   3 7 2   
9 4 8   3 7 2   6 1 5   



real    0m3.670s
user    0m6.051s
sys     0m1.112s
```

The solution is - obviously - exactly the same as the one in the video at the top. Finding a solution in just 3.6s without any special tuning of the solver is impressive.

# Finding all possible miracle sudokus

One could guess that there aren't many valid "miracle sudokus". An easy way to verify this conjecture is to ask Z3 to generate all solution. This can be done by getting one model from the Z3 solver and adding a constraint that requires at least one of the Z3 variables to be different from the values of the current solution, then ask the solver for a new model. Rinse and repeat until the solver can't return any more solutions.

The changes to the core of `solve_sudoku` are trivial:

```python
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
```

Running this code takes 1m7sec on my Intel i7-8700K 3.70GHz, and it generates 72 different sudoku. However a valid sudoku can be rotated and mirrored and still be valid, so there are in fact only 9 different miracle sudokus.

# Further reading

Ben Congdon wrote a nice article on how to [solve the miracle sudoku in Prolog](https://benjamincongdon.me/blog/2020/05/23/Solving-the-Miracle-Sudoku-in-Prolog/).

Håkan Kjellerstrand has an excellent [page on the analysis of miracle sudoku](http://www.hakank.org/picat/miracle_sudoku.pi) using [Picat](http://picat-lang.org/), a logic-based multi-paradigm programming language.

# Conclusion

The last time I wrote a sudoku solver about 10 years ago I used [Knut's Algorithm X](https://en.wikipedia.org/wiki/Knuth%27s_Algorithm_X). It was great fun and the resulting binary took sub-millisecond time to solve a hard sudoku. However the implementation was hard to write and read. Compared to that experience Z3 provides a very intuitive way to solve constraint-based problems like sudoku.


