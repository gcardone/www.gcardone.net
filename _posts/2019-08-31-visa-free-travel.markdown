---
layout: post
title:  "Travelling everywhere without Visa: the set cover problem with Google OR-Tools and Microsoft Z3"
date:   2019-08-31
excerpt: >
  What is the minimal set of passports needed to travel anywhere Visa-free?
---

* ToC
{:toc}

# The Set Cover problem

I'm lucky enough to work in a company that employs people from many different countries. We were comparing the ease of travel given by different passport using [passportindex.org](https://www.passportindex.org). So we wondered: what's the minimum set of passports necessary to travel in any country visa-free?

![A passport](/assets/img/passport.jpg)
*A passport. Photo by [Nicole Geri](https://unsplash.com/@nicolegeri?utm_source=unsplash&utm_medium=referral&utm_content=creditCopyText) on [Unsplash](https://unsplash.com/search/photos/passport?utm_source=unsplash&utm_medium=referral&utm_content=creditCopyText)*

Turns out that it's impossible. Some countries, like Saudi Arabia and North Korea, are only accessible using passports of countries that don't allow dual citizenship. But if we pretend that all countries allow multiple citizenship without restriction, what would be the minimum set of passports that would cover the whole world?

This is an example of [set cover problem](https://en.wikipedia.org/wiki/Set_cover_problem), which is one of Karp's 21 NP-complete problems[^1]. The definition of the problem goes like this:

Given a collection of elements $$U = \lbrace 1, 2, \ldots, n\rbrace$$ called *universe*, and a collection $$S$$ of $$m$$ subsets of $$U$$ whose union is equal to $$U$$ (formally: $$\bigcup_{i=1}^m m_i = U$$), what is the smallest sub-collection of $$S$$ such that the union of its members still equals $$U$$?

![An example of set cover](/assets/img/set_cover.svg)

The image above shows an example of set cover problem. The most obvious greedy algorithm to solve the problem is: until there are uncovered elements, select the set that covers the maximum amount of elements. In the example above at the first iteration we would select $$S_1$$ because it covers 6 elements, then $$S_4$$ because adds 3 more elements, then $$S_3$$, and finally one between $$S_5$$ or $$S_6$$. However there's a smaller solution: $$\lbrace S_3, S_4, S_6\rbrace$$. Imagine now how hard it'd be to find the optimal solution if there were hundreds or more elements and sets.

Set cover problem is definitely not just an interesting theoretical problem, it also has very real world applications. One that is known to everyone is Sudoku, which can be re-stated in the form of set cover. Another one which is not universally known but has a very high monetary impact is shift scheduling: for example airline companies must find a number with different specializations for each shift, often with additional constraints (e.g.: due to labor laws, holidays, and so on). Sometimes set cover problems are hidden in plain sight: imagine to have a database of tagged items, and you want to find the smallest set of tags such that all items are represented at least once. This is another version of the minimal set cover problem.

# Travelling everywhere as minimum set cover problem

Seeing how the visa-free travel problem maps to the minimal set problem is straightforward: the universe $$U$$ is the set of countries, and each passport selects a subset of countries where it allows visa-free travel. We want to select the minimum number of passports that covers all the countries. Easy! But finding the optional solution is way less simple.

## Getting the data

I used [https://github.com/ilyankou/passport-index-dataset/](https://github.com/ilyankou/passport-index-dataset/), which provides a useful CSV file ([passport-index-tidy.csv](https://github.com/ilyankou/passport-index-dataset/blob/master/passport-index-tidy.csv)). Each row of the CSV file contains the country that issued a passport, a destination country, and "3" if the passport allows visa-free travel, and "-1" if the country that issued the passport and the destination country are the same. Now that we have the data, we can find an answer to our question.

## Solving with Google OR-Tools

I first solved the problem using the CP-SAT solver provided by [Google OR-Tools](https://developers.google.com/optimization/) and its Python implementation. The installation of OR-Tools is straightforward:

```bash
pip3 install --user ortools
```

In general the CP-SAT solver works by creating a Constraint Programming model (CP), populating it with variables, adding constraints to those variables, imposing metrics that should me minimized or maximized, and then asking a CP Solver to find a solution.

First, let's open and parse `passport-index-tidy.csv` and create a CP-SAT boolean variable for each passport. Under the hood OR-Tools implements boolean variables as integers with two additional constraints: each variable `x` must satisfy `x >= 0 && x<= 1`.

We are going to create a set for each country, and we are going to put into each set the passport variables that allow visa-free travel. Here's the code:

```python
#!/usr/bin/env python3

import csv
from ortools.sat.python import cp_model

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

            # Get the boolean variable for this passport, otherwise create a
            # new one.
            p_var = passport_vars.setdefault(p, model.NewBoolVar(p))
            # Get the set of passports that allow visa-free travel to country
            # d if it exists, otherwise create a new one.
            passport_set = visa_free.setdefault(d, set())

            # '3' represents visa-free travel, '-1' means that the passport
            # is issued by the destination country
            if row[2] == '3' or row[2] == '-1':
                # Add passport p_var to the set of passports that allow
                # visa-free travel to country d_var
                visa_free[d].add(p_var)
```

At this point `visa_free` will contain a map from countries to all the passport that allow visa-free travel to it. To be able to travel anywhere, we want at least one passport from each set of passports. Since booleans are actually integers constrained to be 0 or 1, we can express this constraint as: the sum of all passport variables for a given destination must be 1 or higher. The code that does this is almost a literal translation:

```python
    # For each set of passports that allows visa-free travelling to a country…
    for destination, allowed_passports in visa_free.items():
        if not allowed_passports:
            print(f'No valid passports for {destination}. Ignoring.')
            continue
        # …at least one of the passports must be selected
        model.Add(sum(allowed_passports) >= 1)
```

The last line of code is the one that actually adds the constraint to the CP model. Variables created with `CpModel.NewBoolVar` overload the `__add__` function, so summing them returns a new object (specifically a `SumArray`) that can store constraints. With `model.Add(sum(allowed_passports) >= 1)` we are asking the solver to make sure that for that given set at least one of the variables is set to 1.

If we didn't ask for anything else then a trivial solution would be to have _all_ the passports. To avoid this, we also ask the solver to minimize the total number of passports:

```python
    model.Minimize(sum(passport_vars.values()))
```

Here we are taking all the passport variables and asking the optimizer to minimize its sum, i.e. to select the minimum number of passports.

We can now ask the solver to search for a solution:

```python
    solver = cp_model.CpSolver()
    status = solver.Solve(model)
    if status == cp_model.OPTIMAL:
        selected_passports = [p for p in passport_vars
                              if solver.Value(passport_vars[p])]
        print('Passports: %d' % len(selected_passports))
        print(', '.join(sorted(selected_passports)))
    else:
        print('Unable to find an optimal solution')
```

That's it! 

Running this code will print:

```bash
$ ./passports_ortools.py
Passports: 23

Afghanistan, Bulgaria, Canada, Comoros, Equatorial Guinea, Ethiopia, Georgia,
Hong Kong, Ivory Coast, Madagascar, Maldives, Nepal, New Zealand, North Korea,
Papua New Guinea, Singapore, Somalia, Sri Lanka, Tunisia, Turkey, Uganda,
United Arab Emirates, Zimbabwe
```

There we go! We need just 23 passports! This is not a viable solution in the real world because some of these countries do not allow dual citizenship, but it does satisfy the constraints that we gave to the CP-SAT solver.

This code takes 2m40s to run on my machine (Intel i7-8700K). Implementing a `cp_model.CpSolverSolutionCallback` to print intermediate solution shows that the optimal solution is found after just 1.20s, but it takes 2m39s for the solver to be convinced that the solution is, in fact, optimal.


## Solving with Microsoft Z3

[Z3](https://github.com/Z3Prover/z3) is a theorem prover from Microsoft Research. Z3 made quite a splash when it was released, and it even won the 2015 [ACM SIGPLAN Programming Languages award](https://www.microsoft.com/en-us/research/blog/z3-wins-2015-acm-sigplan-award/).

Installing Z3 is matter of:

```bash
pip3 install --user z3-solver
```

Z3 is more flexible than Google's CpSolver, but for this specific problem the structure of our program is going to be almost the same, modulo API changes.

First, let's read the data, exactly in the same way as we did wit OR-Tools:

```python
#!/usr/bin/env python3

import csv
import z3

if __name__ == '__main__':
    # optimizer is the z3 Optimizer, which provides functions to minimize
    # or maximize objectives.
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

```

Z3 provides boolean variables that are not built on top of integers variable (at least in the public API). This makes it harder to define the function that we want to minimize (i.e.: select the minimum number of passports), therefore we are going to use integers instead:

```python
            # retrieve the passport variable if it already exists…
            if p in passport_vars:
                p_var = passport_vars[p]
            else:
                # … otherwise create a new one, and make sure that it's
                # 0 ≤ p_var ≤ 1
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
```

Next step: make sure that for each set of passports we select at least one. The code is remarkably similar to the one we wrote for OR-Tools:

```python
    # For each set of passports that allows visa-free travelling to a country…
    for destination, allowed_passports in visa_free.items():
        if not allowed_passports:
            print(f'No valid passports for {destination}. Ignoring.')
            continue
        # …at least one of the passports must be selected
        optimizer.add(sum(allowed_passports) >= 1)

```

Now let's add the optimization goal: try to select the minimum number of passports:

```python
    optimizer.minimize(sum(passport_vars.values()))
```

Now we can check if the model can be satisfied, and if yes what are the selected passports:

```python
    # If the optimizer can find a solution then…
    if optimizer.check() == z3.sat:
        # Load the optimized model
        m = optimizer.model()
        selected_passports = []
        for p_name, p_var in passport_vars.items():
            # Check in the model if the passport is selected
            if m[p_var] == 1:
                selected_passports.append(p_name)

        selected_passports.sort()
        print('Passports: %d' % len(selected_passports))
        print(', '.join(selected_passports))
    else:
        print('Unable to find an optimal solution')
```

That's it!

We can now run the binary:

```bash
Passports: 23

Afghanistan, Australia, Bulgaria, Canada, Comoros, Djibouti, Equatorial Guinea,
Georgia, Hong Kong, India, Madagascar, Malaysia, Maldives, Nigeria,
North Korea, Papua New Guinea, Somalia, Sri Lanka, Tunisia, Turkey, Uganda,
United Arab Emirates, Zimbabwe
```

This version is _phenomenally_ faster than the one implemented with OR-Tools. It takes just 0.6s on my machine for Z3 to find the optimal solution (300x faster than OR-Tools).

# Conclusion and further reading.

This article describes how to find an optimal solution for the set cover problem using Google OR-Tools and Microsoft Z3. However, this is only the beginning. Set cover is NP complete, and finding an optimal solution can become infeasible quite quickly, for this reason there are many approximated algorithms [^2]. There are also other real-life variations: what if elements and sets are dynamically added and removed? What if some elements are weighed more?

For a more theoretical analysis of the Set Cover problem I suggest [Jeremy Kun's article](https://jeremykun.com/2015/05/04/the-many-faces-of-set-cover/) on the topic.


# Footnotes
[^1]: Richard M. Karp (1972). [Reducibility Among Combinatorial Problems](https://doi.org/10.1007%2F978-1-4684-2001-2_9). In R. E. Miller; J. W. Thatcher; J.D. Bohlinger (eds.). Complexity of Computer Computations. New York: Plenum. pp. 85–103.
[^2]: Lim, C. L., Moffat, A., & Wirth, A. (2014). Lazy and eager approaches for the set cover problem. In *Proceedings of the Thirty-Seventh Australasian Computer Science Conference-Volume 147* (pp. 19-27). Australian Computer Society, Inc..
