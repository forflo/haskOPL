# HaskOPL

## Background
OPL is a domain specific language for linear programming.
As you might know, LP is used for a wide range of optimization
problems. The following snippet shows a sample of IBM's OPL:

```
float rawMaterial                     = 205;
{string} products                     = {"light","medium","heavy"};
float demand[products]                = [59,12,13];
{string} processes                    = {"1","2"};
float production[products][processes] = [[12,16],[1,7],[4,2]];
float consumption[processes]          = [25,30];
float cost[processes]                 = [300,400];

dvar float+ run[processes];

minimize sum (p in processes) cost[p] * run[p];

constraints {
  sum (p in processes) consumption[p] * run[p] <= rawMaterial;
  forall (q in products)
    sum (p in processes) production[q][p] * run[p] >= demand[q];
}
```

It describes a system of constraints which
could be solved by using an appropriate algorithm such as
Simplex Primal.


## What is HaskOPL
HaskPL is an educational attempt to design and implement
a EDSL in Haskell loosely resembling IBM's OPL syntax
and semantics.

## Examples

The aforementioned OPL code can be mapped to HaskPL as easy as:

``` Haskell
opl_refinery :: [Either OplType Ineq]
opl_refinery = 
    let rawMaterial = 205
        demand = [59, 12, 13]
        processes = [1, 2] 
        production = [[12,16], [1,7], [4,2]]
        consumption = [25, 30]
        run = [Odvar $ EVar "x", Odvar $ EVar "y"]
        cost = [300, 400]
    in
        eval_expression new_env $
            Minimize 
                (Sum ("p" `In` processes) 
                     ((Id "p" :+ Nil) :? cost :*
                      (Id "p" :+ Nil) :? run)) :|
            Constraints 
                (Sum ("p" `In` processes)
                     ((Id "p" :+ Nil) :? consumption :*
                      (Id "p" :+ Nil) :? run) `Lt` EDouble rawMaterial :|
                 Forall ("q" `In` [1,2,3])
                        (Sum ("p" `In` processes)
                             ((Id "q" :+ Id "p" :+ Nil) :? production :*
                              (Id "p" :+ Nil) :? run) `Gt` 
                              (Id "q" :+ Nil) :? demand))
``` 

In order to implement array subscriptions type safe, a special
notation has to be used.

    ((Id "p" :+ Nil) :? array)

denotes the p-th element in array.

    ((Id "line" :+ Id "column" :+ Nil) :? array)

denotes the column-th element on line line-th in array.
The latter is equivalent to the OPL snippet

    array[line][column]

## Usage

HaskOPL transformes the own EDSL into another EDSL
defined in the package Linear.Grammar from hackage.
The latter DSL is used to represent linear inequalities.
Furthermore it is used as input for Linear.Simplex.Primal
which is (a currently somewhat broken) implementation of the simplex
algorithm.

The above haskell code would generate the following output
which in turn could be fed into the simplexPrimal Funktion:

``` Haskell
[Left (Odvar (EAdd (ECoeff (EVar "y") (400 % 1)) (ECoeff (EVar "x") (300 % 1)))),
 Right (Lte 
    (LinExpr {exprVars = [
        LinVar {varName = "y", varCoeff = 30 % 1},
        LinVar {varName = "x", varCoeff = 25 % 1}], 
        exprConst = 0 % 1}) 
    (LinExpr {exprVars = [], exprConst = 205 % 1})),
 Right (Lte 
    (LinExpr {exprVars = [], exprConst = 59 % 1}) 
    (LinExpr {exprVars = [
        LinVar {varName = "y", varCoeff = 16 % 1},
        LinVar {varName = "x", varCoeff = 12 % 1}], 
        exprConst = 0 % 1})),
 Right (Lte 
    (LinExpr {exprVars = [], exprConst = 12 % 1}) 
    (LinExpr {exprVars = [
        LinVar {varName = "y", varCoeff = 7 % 1},
        LinVar {varName = "x", varCoeff = 1 % 1}], 
        exprConst = 0 % 1})),
 Right (Lte 
    (LinExpr {exprVars = [], exprConst = 13 % 1}) 
    (LinExpr {exprVars = [
        LinVar {varName = "y", varCoeff = 2 % 1},
        LinVar {varName = "x", varCoeff = 4 % 1}], 
        exprConst = 0 % 1}))]
```

To actually solve the equation system you can use the
pre-coded function called solve.

``` Haskell
solve $ opl_refinery
```

That produces:

``` Haskell
[("M",17050 % 13),
 ("x",67 % 26), -- solution
 ("y",35 % 26), -- for the system
 ("s0",2605 % 26),("s1",(-85) % 13),("s2",0 % 1),("s3",0 % 1)]
```

## Misc

Included in this repo are two Matlab files.
The first plots all constraints onto a 2D plane.
This is useful if you'd like to visualize the 
system of equations. The second matlab sourcefile
containts the linear system encoded in standard form
using matrices and vectors. Usually LP in standard form
are written as maximization problem, which explains
certain transformations.
