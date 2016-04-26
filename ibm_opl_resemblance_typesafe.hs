{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}

import Data.List
import Linear.Grammar
import Linear.Simplex.Primal

-- Numbers at the type level
data Peano = Zero | Successor Peano

-- Counting Vector Type. Type information contains current length
data Vector (peanoNum :: Peano) someType where
    Nil :: Vector Zero someType
    (:+) :: someType 
            -> Vector num someType 
            -> Vector (Successor num) someType
infixr 5 :+ 

data IterateCons peanoNum cons t where
    ZeroCons :: t -> IterateCons Zero cons t
    SuccessorCons :: cons (IterateCons p cons t) 
                     -> IterateCons (Successor p) cons t

-- Generate Num-th nested types
-- For example: Iterate (S (S Z)) [] Double => [[Double]]
type family Iterate (peanoNum :: Peano) constructor someType where
    Iterate Zero cons typ = typ
    Iterate (Successor pn) cons typ = 
        cons (Iterate pn cons typ)

-- DSL spec
data Statement =
      DecisionVector [LinAst]
    | Minimize Statement
    | Sum Iteration Expression
    | Forall Iteration Statement
    | Statement :| Statement
    | Constraints Statement
infixl 8 `Sum`
infixl 3 :|

data Iteration =
      String `In` [Double]
    | String `Ins` [String]

data Expression where
    EString :: String -> Expression
    EFloat :: Double -> Expression
    (:?) :: Vector n Expression -> Iterate (n) [] Double -> Expression
    (:*) :: Expression -> Expression -> Expression
    Lt :: Expression -> Expression -> Expression
    Gt :: Expression -> Expression -> Expression
    Id :: String -> Expression
infixr 5 `Lt`
infixr 5 `Gt`
infixr 6 :*
infixr 7 :?

test :: Statement
test = 
    let rawMaterial = 205
        products = ["light", "medium", "heavy"]
        demand = [59, 12, 13]
        processes = [1, 2] 
        production = [[12,16], [1,7], [4,2]]
        consumption = [25, 30]
        run = []
        cost = [300, 400]
    in  
        DecisionVector run :|
        Minimize 
            (Sum ("p" `In` processes) 
                 ((Id "p" :+ Nil) :? cost :*
                  (Id "p" :+ Nil) :? run)) :|
        Constraints 
            (Sum ("p" `In` processes)
                 ((Id "p" :+ Nil) :? consumption :*
                  (Id "p" :+ Nil) :? run `Lt` EFloat rawMaterial) :|
             Forall ("q" `Ins` products)
                    (Sum ("p" `In` processes)
                         ((Id "q" :+ Id "p" :+ Nil) :? production :*
                          (Id "p" :+ Nil) :? run `Gt` 
                          (Id "q" :+ Nil) :? demand)))

type Environment = (String -> Either String Double)

new_env :: Environment 
new_env = (\x -> Right 0)

update_env :: Environment -> Either String Double -> String -> Environment
update_env mapping dat id = 
    (\x -> if x == id then dat else mapping x)

--eval_stmt_sum :: Environment -> Iteration -> Expression -> Either LinAst Ineq
--eval_stmt_sum env (id `In` doubles) expr =
--    let len = length doubles
--    in  
--eval_stmt_sum env (id `Ins` strings) expr =
--
--eval_decvec :: [Double] -> [EVar]
--
--eval_statement :: Statement -> ([Ineq], [Ineq])
--eval_statement (DecisionVector dbl) = eval_decvec dbl
--eval_statement 
--
--eval_expression :: Expression -> Either Ineq undefined
--
--eval_stmt_constraints :: Statement -> [Ineq]
--eval_stmt_constraints (Sum iteration expression) = undefined
--eval_stmt_constraints (Forall iteration stmt) = undefined
--eval_stmt_constraints (sa :| sb) =
--    eval_stmt_constraints sa ++ eval_stmt_constraints sb
--eval_stmt_constraints (Contraints statement) = error "Nested Constraints not allowed!"
--eval_stmt_constraints (DecisionVector statement) = error "Decision vector cannot be specified here!"
--eval_stmt_constraints (Minimize statement) = error "Minimize cannot occure here!"
--
--eval_stmt_forall :: Statement -> [Ineq]
--eval_stmt_forall (Sum iteration expression) = undefined
--eval_stmt_forall _ = error "Forall can only contain a sum statement"

instance Show Statement where
    show (DecisionVector v) = show v
    show (Minimize s) = "(Minimize " ++ show s ++ ")"
    show (i `Sum` e) = "(" ++ show i ++ " `Sum` " ++ show e ++ ")"
    show (Forall i e) = "(Forall " ++ show i ++ show e ++ ")"
    show (sa :| sb) = "(" ++ show sa ++ show sb ++ ")"
    show (Constraints s) = "(Constraints " ++ show s  ++ ")"

instance Show Iteration where
    show (str `In` d) = "(" ++ show str ++ " `In` " ++ show d ++ ")"
    show (str `Ins` d) = "(" ++ show str ++ " `Ins` " ++ show d ++ ")"

instance Show Expression where
    show (EString s) = "(EString " ++ show s ++ ")"
    show (EFloat f) = "(EFloat " ++ show f ++ ")"
    show (Lt ea eb) = "(" ++ show ea ++ " `Lt` " ++ show eb ++ ")"
    show (Gt ea eb) = "(" ++ show ea ++ " `Gt` " ++ show eb ++ ")"
    show (ea :* eb) = "(" ++ show ea ++ " :* " ++ show eb ++ ")"
    show (Id s) = "(Id " ++ show s ++ ")"
    show (vec :? dbl) = "(" ++ show vec ++ " :? " ++ go vec dbl ++ ")"
        where go :: Vector n x -> Iterate n [] Double -> String
              go Nil a = show a
              go (_ :+ n) a = "[" ++ intercalate  "," (map (go n) a) ++ "]"
        

instance Show (Vector p Expression) where
    show (Nil) = "Nil"
    show (e :+ v) = "(" ++ show e ++ " :+ " ++ show v ++ ")"

