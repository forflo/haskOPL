# HaskOPL

## Background
OPL is a domain specific language for linear programming.
As you might now, LP is used for a wide range of optimization
problems. The following snippet shows a smaple of IBM's OPL

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

The example describes a system of inequality equations which
then can be solved by using an appropriate algorithm such as
Simplex Primal.


## What is HaskPL
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


