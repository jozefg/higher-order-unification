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
once fully filled in, evaluate to the same term. Our language will
contain the following constructs,

 1. Variables
 2. Functions (lambdas) and correspondingly application
 3. Metavariables
 4. Function types, in the typical style for a dependently typed
 language: pi types
 5. Universe types

This was originally designed to be part of a typechecker for a
particular dependently typed language, hence the pi types and
universes, but they can safely be ignored and treated as particular
constants.

The main issue is, that it's actually undecidable to do this in the
general case. It's therefore only possible to implement a semidecision
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

To begin with, we introduce the tools that we will need to even code
up the unification algorithm. The first critical point is how we
define the language we're unifying in the first place. I will
represent terms using the so-called "locally nameless" approach. This
means that we use
[de Bruijn](https://en.wikipedia.org/wiki/De_Bruijn_index) to
represent bound variables. However, for free variables we will
generate globally unique identifiers to simplify the process of
carrying around contexts or the like. This does mean that our AST has
two different constructors for variables, free and bound.

``` haskell
    type Id = Int
    type Index = Int
    data Term = FreeVar Id
              | LocalVar Index
              | MetaVar Id
              | Uni
              | Ap Term Term
              | Lam Term
              | Pi Term Term
              deriving (Eq, Show, Ord)
```

Since we're using de Bruijn indices, we also need to define a crucial
helper function called `raise :: Int -> Term -> Term`. This raises all
the variables wrapped in a `LocalVar` constructor up by `i`. This is
done by recursing over the inputted term.

``` haskell
    raise :: Int -> Term -> Term
    raise = go 0
      where go lower i t = case t of
              FreeVar i -> FreeVar i
              LocalVar j -> if i > lower then LocalVar (i + j) else LocalVar j
              MetaVar i -> MetaVar i
              Uni -> Uni
              Ap l r -> go lower i l `Ap` go lower i r
              Lam body -> Lam (go (lower + 1) i body)
              Pi tp body -> Pi (go lower i tp) (go (lower + 1) i body)
```

Using this, we can define substitution on terms. This will be useful
later on directly. For this, we first define the notion of replacing a
de Bruijn variable with a term.

``` haskell
    subst :: Term -> Int -> Term -> Term
    subst new i t = case t of
      FreeVar i -> FreeVar i
      LocalVar j -> case compare j i of
        LT -> LocalVar j
        EQ -> new
        GT -> LocalVar (j - 1)
      MetaVar i -> MetaVar i
      Uni -> Uni
      Ap l r -> subst new i l `Ap` subst new i r
      Lam body -> Lam (subst (raise 1 new) (i + 1) body)
      Pi tp body -> Pi (subst new i tp) (subst (raise 1 new) (i + 1) body)
```

Notice that we have used `raise` to escape `new` as we go under
binders to avoid capturing variables. Similarly, since we're removing
a binding level, if we have any de Bruijn variables that refer to a
binding site outside of the one we're working with we have to lower it
to compensate. That is the reason for the line `GT -> LocalVar (j - 1)`.
Apart from these two complications, substitution is just hunting for
all occurrences of `LocalVar i` and replacing it with `new`. However,
we also have this metavariables so it makes sense that we have a
notion of substitution for these as well. It's simpler than the above
substitution function because we don't have to worry about lowering
variables that might be affected by deleting a metavariable binding
since we're using globally unique identifiers for them.

``` haskell
    substMV :: Term -> Id -> Term -> Term
    substMV new i t = case t of
      FreeVar i -> FreeVar i
      LocalVar i -> LocalVar i
      MetaVar j -> if i == j then new else MetaVar j
      Uni -> Uni
      Ap l r -> substMV new i l `Ap` substMV new i r
      Lam body -> Lam (substMV (raise 1 new) i body)
      Pi tp body -> Pi (substMV new i tp) (substMV (raise 1 new) i body)
```
