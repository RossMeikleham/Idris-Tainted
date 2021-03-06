# Idris-Tainted

| OSX + Linux | Win x86 + x64 |
|-------------|---------------|
|[![Build Status](https://travis-ci.org/RossMeikleham/Idris-Tainted.svg?branch=master)](https://travis-ci.org/RossMeikleham/Idris-CI-Skeleton)|[![Build status](https://ci.appveyor.com/api/projects/status/9m3i7356s75pn72n/branch/master?svg=true)](https://ci.appveyor.com/project/RossMeikleham/idris-tainted)|


Implementation of the Tainted Monad in Idris. See [here](https://github.com/RossMeikleham/Tainted) for the original Haskell implementation.

Simple re-implementation of a Haskell Monad in Idris. The Monad is built by
first defining a Functor instance, then defining the Applicative instance on top of
that, and finally the Monadic instance. Monoid and BoundedLattice instances are
defined and verified as well.

```
SemiGroup -> Monoid

MeetSemiLattice -> BoundedMeetSemiLattice 
                                           \
                                             -> Lattice -> BoundedLattice
JoinSemiLattice -> BoundedJoinSemiLattice  /

Functor -> Applicative -> Monad
```

In addition to defining these instances Idris allows for implementing proofs to verify
the properties of these structures. The Verified instances of each of
these structures are implemented to achieve this.

Proofs are implemented for the following structures:
- SemiGroup
- Monoid
- MeetSemilattice + BoundedMeetSemiLattice
- JoinSemilattice + BoundedJoinSemiLattice
- Lattice
- BoundedLattice
- Functor
- Applicative
- Monad 

TODO:
- Implement Monad Transformer version.

Example Code (source can be found in the example folder):

```idris
module TaintExample

import Data.Tainted


data Expr = 
  Number (Tainted Int)
  | Add Expr Expr

instance Show Expr where
  show (Number x) = "Number (" ++ show x ++ ")"
  show (Add e1 e2) = "Add " ++ show e1 ++ " " ++ show e2

pure1 : Expr
pure1 = Number (Clean 3)

pure2 : Expr
pure2 = Number (Clean 7)

impure1 : Expr
impure1 = Number (Dirty 5)

expr1 : Expr
expr1 = Add pure1 pure2

expr2 : Expr
expr2 = Add impure1 pure1

expr3 : Expr
expr3 = Add pure1 (Add impure1 pure2) 

--Evaluate expression as much as Possible
evalExpr : Expr -> Expr
evalExpr (Number n) = Number n
evalExpr (Add e1 e2) = 
    case (evalExpr e1, evalExpr e2) of
            (Number i, Number j) => Number $ liftA2 (+) i j
            (x, y) => Add x y


reducedExpr1 : Expr
reducedExpr1 = evalExpr expr1

reducedExpr2 : Expr
reducedExpr2 = evalExpr expr2

reducedExpr3 : Expr
reducedExpr3 = evalExpr expr3
```

Evaluating expr1:
```Idris
Number (Clean 10) : Expr
```
Adding 2 clean values 7 and 3 gives a clean value, clean
values haven't become tainted

Evaluating expr2:
```Idris
Number (Dirty 8) : Expr
```
Adding a clean value 3 and dirty value 5 taints the expression as dirty
so the expression evaluates to dirty value of 8


Evaluating expr3:
```Idris
Number (Dirty 15) : Expr
```
This shows the propogation of dirty states, as the inner expression
evaluates to a dirty value, then added with a clean value still
gives a dirty value.
