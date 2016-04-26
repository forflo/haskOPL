import Linear.Grammar
import Linear.Simplex.Primal

calc :: [(String, Rational)]
calc = 
    let light = (12 :: Rational) .*. EVar "x" .+. (16 :: Rational) .*. EVar "y" .=>. ELit (59)
        middle = (1 :: Rational) .*. EVar "x" .+. (7 :: Rational) .*. EVar "y" .=>. ELit (12)
        heavy = (4 :: Rational) .*. EVar "x" .+. (2 :: Rational) .*. EVar "y" .=>. ELit (13)
        consumption = (25 :: Rational) .*. EVar "x" .+. (30 :: Rational) .*. EVar "y" .<=. ELit 205 
        obj = (300 :: Rational) .*. EVar "x" .+. (400 :: Rational) .*. EVar "y" .==. EVar "M"
    in
        simplexPrimal (standardForm obj) (standardForm <$> [light, middle, heavy, consumption])

