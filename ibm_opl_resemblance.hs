{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

import Data.List
import Data.Ratio
import Linear.Grammar
import Linear.Simplex.Primal
import GHC.Exts (IsString(..))

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
      DecisionVector [OplType]
    | Minimize Statement
    | Sum Iteration Expression
    | Forall Iteration Statement
    | Statement :| Statement
    | Constraints Statement
infixl 8 `Sum`
infixl 3 :|

data Iteration =
      String `In` [OplType]

data Expression where
    EString :: OplType -> Expression
    EDouble :: OplType -> Expression
    Id :: OplType  -> Expression
    (:?) :: Vector n Expression -> Iterate (n) [] OplType -> Expression
    (:*) :: Expression -> Expression -> Expression
    Lt :: Expression -> Expression -> Expression
    Gt :: Expression -> Expression -> Expression
infixr 5 `Lt`
infixr 5 `Gt`
infixr 6 :*
infixr 7 :?

data OplType = 
      OString String 
    | ONumber Rational 
    | Odvar LinAst
    deriving (Eq, Show)

instance IsString OplType where
    fromString string = OString string

instance Num OplType where
    fromInteger integer = ONumber (fromInteger integer)
    negate (ONumber num) = ONumber (negate num)
    abs (ONumber num) = ONumber (abs num)
    signum (ONumber num) = ONumber (signum num)
    (ONumber numa) + (ONumber numb) = ONumber $ numa + numb
    (ONumber numa) - (ONumber numb) = ONumber $ numa - numb
    (ONumber numa) * (ONumber numb) = ONumber $ numa * numb

test :: Statement
test = 
    let rawMaterial = 205
        products = ["light", "medium", "heavy"]
        demand = [59, 12, 13]
        processes = [1, 2] 
        production = [[12,16], [1,7], [4,2]]
        consumption = [25, 30]
        run = [Odvar $ EVar "x", Odvar $ EVar "y"]
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
                  (Id "p" :+ Nil) :? run `Lt` EDouble rawMaterial) :|
             Forall ("q" `In` products)
                    (Sum ("p" `In` processes)
                         ((Id "q" :+ Id "p" :+ Nil) :? production :*
                          (Id "p" :+ Nil) :? run `Gt` 
                          (Id "q" :+ Nil) :? demand)))

type Environment = (String -> OplType)

new_env :: Environment 
new_env = (\x -> 0)

update_env :: Environment -> OplType -> String -> Environment
update_env mapping dat id = 
    (\x -> if x == id then dat else mapping x)

eval_stmt_sum :: Environment -> Iteration -> Expression -> [Either OplType Ineq]
eval_stmt_sum env (id `In` list) expr =
    let len = length list
        evaler = map (\elem -> eval_expression (update_env env elem id)) list
    in  zipWith (\eval_fun expr -> eval_fun expr) evaler (replicate len expr)

--eval_decvec :: [Double] -> [EVar]
--
--eval_statement :: Statement -> ([Ineq], [Ineq])
--eval_statement (DecisionVector dbl) = eval_decvec dbl
--eval_statement 
--
eval_expression :: Environment -> Expression -> Either OplType Ineq
eval_expression env (EString str) = Left str
eval_expression env (EDouble dbl) = Left dbl
eval_expression env (Id id) = Left id
eval_expression env (vec :? arr) =  
    Left (go vec arr)
    where 
        go :: (Vector n Expression) -> Iterate n [] OplType -> OplType
        go Nil val = val
        go (index :+ rest) list = 
            let (ONumber idx) = 
                    case (index) of
                        (EString (OString string)) -> env string
                        (Id (OString string)) -> env string
                        _ -> error "False index type!"
            in  (map (go rest) list) !! fromIntegral (numerator idx)
    
eval_expression env (ea :* eb) = 
    let eva = eval_expression env ea
        evb = eval_expression env eb
        e = error $ "Type error in: " ++ show ea ++ " :* " ++ show eb
    in case (eva) of
        (Left (Odvar opl)) -> case (evb) of
            (Left (ONumber coeff)) -> Left (Odvar (opl .*. coeff))    
            (Right _) -> e
        (Left (ONumber coeff)) -> case (evb) of
            (Left (Odvar opl)) -> Left (Odvar (coeff.*. opl))    
            (Right _) -> e
        (Right _) -> e

eval_expression env (ea `Lt` eb) =
    let eva = eval_expression env ea
        evb = eval_expression env eb
        e = error $ "Type error in: " ++ show ea ++ " `Lt` " ++ show eb
    in case (eva) of
        (Left (Odvar oplA)) -> case (evb) of
            (Left (ONumber coeff)) -> Right (oplA .<=. ELit coeff)
            (Left (Odvar oplB)) -> Right (oplA .<=. oplB)
            _ -> e
        _ -> e

eval_expression env (ea `Gt` eb) =
    let eva = eval_expression env ea
        evb = eval_expression env eb
        e = error $ "Type error in: " ++ show ea ++ " `Gt` " ++ show eb
    in case (eva) of
        (Left (Odvar oplA)) -> case (evb) of
            (Left (ONumber coeff)) -> Right (oplA .=>. ELit coeff)
            (Left (Odvar oplB)) -> Right (oplA .=>. oplB)
            (Right x) -> e
        (Right _) -> e

eval_test :: [Either OplType Ineq]
eval_test = 
    let processes = [0, 1, 2, 3, 4, 5, 6, 7, 8] 
        cost = [0, 1, 2, 3, 4, 5, 6, 7, 8]
        run = map (Odvar . EVar . \x -> [x]) ['a' .. 'i'] 
        (Sum iter expr) = (Sum ("p" `In` processes)
                 ((Id "p" :+ Nil) :? cost :*
                  (Id "p" :+ Nil) :? run `Lt` EDouble 30))
    in eval_stmt_sum new_env iter expr
        
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

instance Show Expression where
    show (EString s) = "(EString " ++ show s ++ ")"
    show (EDouble f) = "(EFloat " ++ show f ++ ")"
    show (Lt ea eb) = "(" ++ show ea ++ " `Lt` " ++ show eb ++ ")"
    show (Gt ea eb) = "(" ++ show ea ++ " `Gt` " ++ show eb ++ ")"
    show (ea :* eb) = "(" ++ show ea ++ " :* " ++ show eb ++ ")"
    show (Id s) = "(Id " ++ show s ++ ")"
    show (vec :? dbl) = "(" ++ show vec ++ " :? " ++ go vec dbl ++ ")"
        where go :: Vector n x -> Iterate n [] OplType -> String
              go Nil a = show a
              go (_ :+ n) a = "[" ++ intercalate  "," (map (go n) a) ++ "]"

instance Show (Vector p Expression) where
    show (Nil) = "Nil"
    show (e :+ v) = "(" ++ show e ++ " :+ " ++ show v ++ ")"
