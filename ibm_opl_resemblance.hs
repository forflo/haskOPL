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

--
-- Counting vector type. Type information contains current length
--
data Peano = Zero | Successor Peano
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

-- 
-- Generate Num-th nested types
-- For example: Iterate (S (S Z)) [] Double => [[Double]]
-- 
type family Iterate (peanoNum :: Peano) constructor someType where
    Iterate Zero cons typ = typ
    Iterate (Successor pn) cons typ = 
        cons (Iterate pn cons typ)

data Expression where
    Constraints :: Expression -> Expression
    Minimize :: Expression -> Expression
    EString :: OplType -> Expression
    EDouble :: OplType -> Expression
    Sum :: Iteration -> Expression -> Expression
    Forall :: Iteration -> Expression -> Expression
    Id :: OplType  -> Expression
    Lt :: Expression -> Expression -> Expression
    Gt :: Expression -> Expression -> Expression
    (:|) :: Expression -> Expression -> Expression
    (:?) :: Vector n Expression 
        -> Iterate (n) [] OplType 
        -> Expression
    (:*) :: Expression -> Expression -> Expression
infixl 4 :|
infixl 5 `Sum`
infixr 6 `Lt`
infixr 6 `Gt`
infixr 7 :*
infixr 8 :?

data Iteration = String `In` [OplType]

--
-- Wrapper type for type safe overloading
--
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

-- 
-- Trivial show instance
-- Had to be written by hand because
-- of the usage of GADT's 
-- 
instance Show Iteration where
    show (str `In` d) = "(" ++ show str ++ " `In` " ++ show d ++ ")"

instance Show (Vector p Expression) where
    show (Nil) = "Nil"
    show (e :+ v) = "(" ++ show e ++ " :+ " ++ show v ++ ")"

instance Show Expression where
    show (Minimize s) = "(Minimize " ++ show s ++ ")"
    show (Forall i e) = "(Forall " ++ show i ++ show e ++ ")"
    show (sa :| sb) = "(" ++ show sa ++ " :| \n"++ show sb ++ ")"
    show (Constraints s) = "(Constraints " ++ show s  ++ ")"
    show (EString s) = "(EString " ++ show s ++ ")"
    show (i `Sum` e) = "(" ++ show i ++ " `Sum` " ++ show e ++ ")"
    show (EDouble f) = "(EFloat " ++ show f ++ ")"
    show (Lt ea eb) = "(" ++ show ea ++ " `Lt` " ++ show eb ++ ")"
    show (Gt ea eb) = "(" ++ show ea ++ " `Gt` " ++ show eb ++ ")"
    show (ea :* eb) = "(" ++ show ea ++ " :* " ++ show eb ++ ")"
    show (Id s) = "(Id " ++ show s ++ ")"
    show (vec :? dbl) = "(" ++ show vec ++ " :? " ++ go vec dbl ++ ")"
        where go :: Vector n x -> Iterate n [] OplType -> String
              go Nil a = show a
              go (_ :+ n) a = "[" ++ intercalate  ", " (map (go n) a) ++ "]"

--
-- Value lookup helper
--
type Environment = (String -> OplType)

new_env :: Environment 
new_env = (\x -> 0)

update_env :: Environment 
    -> OplType 
    -> String 
    -> Environment
update_env mapping dat id = 
    \x -> if x == id 
             then dat 
             else mapping x

-- 
-- Valuation functions
-- AKA the interpreter
-- 
eval_expression :: Environment 
    -> Expression 
    -> [Either OplType Ineq]

eval_expression env (Minimize expr) = 
    eval_expression env expr

eval_expression env (Constraints expression) =
    eval_expression env expression

eval_expression env (expA :| expB) = 
    eval_expression env expA ++ eval_expression env expB

eval_expression env (EString str) = 
    [Left str]

eval_expression env (EDouble dbl) = 
    [Left dbl]

eval_expression env (Id id) = 
    [Left id]

eval_expression env (Forall (id `In` list) exp) = 
    let len = length list
        makeNewEnv = \val -> update_env env val id
        evaler = map (eval_expression . makeNewEnv) list
        expres = replicate len exp
    in concat $ zipWith (\f e -> f e) evaler expres

eval_expression env (Sum (id `In` list) exp) = 
    let len = length list
        makeNewEnv = \val -> update_env env val id
        evaler = map (eval_expression . makeNewEnv) list
        expres = replicate len exp
        zips = concat $ zipWith ($) evaler expres
    in  [foldr (folder) (head zips) (tail zips)]
    where folder (Left (Odvar astA)) (Left (Odvar astB)) = 
              Left (Odvar $ astA .+. astB)
          folder _ _ = error "[folder] Wrong types!"

eval_expression env (vec :? arr) =  
    [Left (go vec arr)]
    where go :: (Vector n Expression) 
              -> Iterate n [] OplType 
              -> OplType
          go Nil val = val
          go (index :+ rest) list = 
              let (ONumber idx) = case (index) of
                      (EString (OString string)) -> env string
                      (Id (OString string)) -> env string
                      _ -> error "False index type!"
              in  (map (go rest) list) !! 
                  (fromIntegral (numerator idx) - 1)
    
eval_expression env (ea :* eb) = 
    let (eva:_) = eval_expression env ea
        (evb:_) = eval_expression env eb
        e = error $ "Type error in: " ++ 
            show ea ++ 
            " :* " ++ 
            show eb
    in case (eva) of
        (Left (Odvar opl)) -> case (evb) of
            (Left (ONumber coeff)) -> 
                [Left (Odvar (opl .*. coeff))]
            (Right _) -> e
        (Left (ONumber coeff)) -> case (evb) of
            (Left (Odvar opl)) -> 
                [Left (Odvar (coeff.*. opl))]
            (Right _) -> e
        (Right _) -> e

eval_expression env (ea `Lt` eb) =
    let (eva:_) = eval_expression env ea
        (evb:_) = eval_expression env eb
        e = error $ "Type error in: " ++ 
            show ea ++ 
            " `Lt` " ++ 
            show eb
    in case (eva) of
        (Left (Odvar oplA)) -> case (evb) of
            (Left (ONumber coeff)) -> 
                [Right (oplA .<=. ELit coeff)]
            (Left (Odvar oplB)) -> 
                [Right (oplA .<=. oplB)]
            _ -> e
        _ -> e

eval_expression env (ea `Gt` eb) =
    let (eva:_) = eval_expression env ea
        (evb:_) = eval_expression env eb
        e = error $ "Type error in: " ++ 
            show ea ++ 
            " `Gt` " ++ 
            show eb
    in case (eva) of
        (Left (Odvar oplA)) -> case (evb) of
            (Left (ONumber coeff)) 
                -> [Right (oplA .=>. ELit coeff)]
            (Left (Odvar oplB)) 
                -> [Right (oplA .=>. oplB)]
            (Right x) -> e
        (Right _) -> e

--
-- Does conversions necessary for usage with simplexPrimal
-- from the package Linear.Simplex.Primal
-- 
solve :: [Either OplType Ineq] -> [(String, Rational)]
solve list = 
    let constraints = map getRight $ filter isIneq list
        (Odvar objective) = (map getLeft $ filter (not . isIneq) list) !! 0
        stdConstraints = standardForm <$> constraints
        stdObj = standardForm $ (EVar "M" .==. objective)
    in simplexPrimal stdObj stdConstraints
    where isIneq (Right x) = True
          isIneq (Left x) = False
          getRight (Right x) = x
          getRight _ = error "Nonsense usage!"
          getLeft (Left x) = x
          getLeft _ = error "Nonsense usage!"

--------------
-- Examples --
--------------
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
            (Sum 
              ("p" `In` processes) 
              ((Id "p" :+ Nil) :? cost :*
               (Id "p" :+ Nil) :? run)) :|
          Constraints 
            (Sum ("p" `In` processes)
              ((Id "p" :+ Nil) :? consumption :*
               (Id "p" :+ Nil) :? run) 
               `Lt` EDouble rawMaterial :|
             Forall ("q" `In` [1,2,3])
               (Sum ("p" `In` processes)
                 ((Id "q" :+ Id "p" :+ Nil) :? production :*
                  (Id "p" :+ Nil) :? run) 
                  `Gt` (Id "q" :+ Nil) :? demand))

test_tree :: Expression
test_tree = 
    let rawMaterial = 205
        demand = [59, 12, 13]
        processes = [1, 2] 
        production = [[12,16], [1,7], [4,2]]
        consumption = [25, 30]
        run = [Odvar $ EVar "x", Odvar $ EVar "y"]
        cost = [300, 400]
    in
        Minimize 
            (Sum ("p" `In` processes) 
                 ((Id "p" :+ Nil) :? cost :*
                  (Id "p" :+ Nil) :? run)) :|
        Constraints 
            (Sum ("p" `In` processes)
                 ((Id "p" :+ Nil) :? consumption :*
                  (Id "p" :+ Nil) :? run `Lt` EDouble rawMaterial) :|
             Forall ("q" `In` [1,2,3])
                    (Sum ("p" `In` processes)
                         ((Id "q" :+ Id "p" :+ Nil) :? production :*
                          (Id "p" :+ Nil) :? run `Gt` 
                          (Id "q" :+ Nil) :? demand)))

eval_forall :: [Either OplType Ineq]
eval_forall = 
    let processes = [1, 2] 
        demand = [59, 12, 13]
        products = ["light", "medium", "heavy"]
        production = [[12,16], [1,7], [4,2]]
        cost = [300, 400]
        run = [Odvar $ EVar "x", Odvar $ EVar "y"]
        s = Forall ("q" `In` [1,2,3])
                   (Sum ("p" `In` processes)
                        ((Id "q" :+ Id "p" :+ Nil) :? production :* (Id "p" :+ Nil) :? run) 
                         `Gt` (Id "q" :+ Nil) :? demand)
    in eval_expression new_env s

eval_test_sum :: [Either OplType Ineq]
eval_test_sum =
    let processes = [1, 2, 3, 4] 
        rawMaterial = 205
        consumption = [25, 30, 35, 40]
        run = [Odvar $ EVar "x", Odvar $ EVar "y", Odvar $ EVar "z", Odvar $ EVar "a"]
        exp = (Sum ("p" `In` processes)
                 ((Id "p" :+ Nil) :? consumption :*
                  (Id "p" :+ Nil) :? run)) 
    in eval_expression new_env exp
