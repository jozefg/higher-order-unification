## An Explanation of Unification.hs

In order to make this code useful to others, I would like to take the
time to explain exactly how it works. In this file, we will go through
the unification algorithm being used and how it is implemented in the
code.

### The Problem

Before beginning, it's worth clarifying the problem that we're
attempting to solve with this code, namely, what is higher order
unification? The simple answer is that we want to take two terms with
"holes" in them, called metavariables. We then want to figure out how
to replace those metavariables with programs so that the two terms,
once fully filled in, evaluate to the same term.

The issue is, that it's actually undecidable to do this in the general
case. It's therefore only possible to implement a semidecision
procedure that performs relatively well in practice. By a semidecision
procedure, I mean an algorithm that will terminate with a solution
when possible and reject only some of the time. This procedure is
called Huet's algorithm and it's essentially a refinement of the
following algorithm

 1. Generate a solution
 2. Test it
 3. If the solution was correct, stop
 4. Else, go to 1

This is not exactly the most sophisticated algorithm but it does have
the benefit of being obviously a correct semidecision procedure for
our problem. The idea with Huet's algorithm is to gradually produce a
solution and to only produce solutions that are at least not
obviously wrong. By doing this, we drastically cut down the search
space and produce answers reasonably quickly.

## The Set Up
