import Utils
import Lexer
import Parser
import Data.Function (on)

-- x' := x \/ {x}

--  Sum c_i*w^B_i + y'
--  in orinigal CNF: B1 >= B2 >= ... >= Bk >= 0
--  here: B1 > B2 > .. > B(k - 1) > 0, Bk = 0, ck = y'
                  ---    beta      c    default (\in N)
data Ordinal = Ordinal [(Ordinal, Int)] Int deriving (Eq, Ord, Show)
-- [(Ordinal, Int)] Int =: [] x -> Finite, x; else -> Infinite                     

zero = Ordinal [] 0
omega = Ordinal [(Ordinal [] 1, 1)] 0

head' :: Ordinal -> (Ordinal, Int)
head' (Ordinal [] _) = error "head' on empty"
head' (Ordinal (h:_) _) = h

tail' :: Ordinal -> Ordinal
tail' (Ordinal [] _) = error "tail' on empty"
tail' (Ordinal (_:t) n) = Ordinal t n

cons' :: (Ordinal, Int) -> Ordinal -> Ordinal
cons' x (Ordinal ys yn) = Ordinal (x:ys) yn

-- highest power
hiPow :: Ordinal -> Ordinal
hiPow (Ordinal [] _) = zero
hiPow a = fst $ head' a

-- highest multiplier
hiMul :: Ordinal -> Int
hiMul (Ordinal [] n) = n
hiMul a = snd $ head' a



cantorNormalForm :: Expression -> Ordinal
cantorNormalForm (Number x) = Ordinal [] x
cantorNormalForm Omega = omega
cantorNormalForm (Call Add x y) = (add `on` cantorNormalForm) x y
cantorNormalForm (Call Mul x y) = (mul `on` cantorNormalForm) x y
cantorNormalForm (Call Pow x y) = (pow `on` cantorNormalForm) x y


add :: Ordinal -> Ordinal -> Ordinal
add (Ordinal non'empty@(_:_) a) (Ordinal [] b) = Ordinal non'empty $ a + b
add (Ordinal [] a) (Ordinal [] b) = Ordinal [] $ a + b
add (Ordinal [] _) a = a

add a b = let (ha, hb) = (hiPow a, hiPow b) in
  if ha <  hb then b else 
  if ha == hb
    then cons' (ha, hiMul a + hiMul b) $ tail' b
    else cons' (ha, hiMul a          ) $ add (tail' a) b


mul :: Ordinal -> Ordinal -> Ordinal
mul _ (Ordinal [] 0) = zero
mul (Ordinal [] 0) _ = zero
mul (Ordinal [] a) (Ordinal [] b) = Ordinal [] $ a * b

mul (Ordinal [] a) (Ordinal ne@(_:_) b) = Ordinal ne $ a * b
mul a (Ordinal [] b) = cons' (hiPow a, hiMul a * b            )         $ tail' a
mul a              b = cons' (add (hiPow a) (hiPow b), hiMul b) $ mul a $ tail' b


pow :: Ordinal -> Ordinal -> Ordinal
pow _ (Ordinal [] 0) = Ordinal [] 1
pow (Ordinal [] 0) _ = Ordinal [] 0
pow (Ordinal [] a) (Ordinal [] b) = Ordinal [] $ a ^ b
pow a (Ordinal [] 1) = a
pow a (Ordinal [] b) = mul a $ pow a $ Ordinal [] $ b - 1

-- a^(cw^B+b) = a^(cw^B) * a^b
pow (Ordinal [] a) (Ordinal ws b) = mul (Ordinal [(Ordinal ws 0, 1)] 0)
  $ Ordinal [] $ a ^ b
pow a (Ordinal ws b) = mul (Ordinal [(mul (hiPow a) $ Ordinal ws 0, 1)] 0) 
  $ pow a (Ordinal [] b)



check :: Equation -> Bool
check (Equation left right) = ((==) `on` cantorNormalForm) left right

toRussian True = "Равны"
toRussian False = "Не равны"
main = getLine >>= alexScanTokens ~> parseOrdinals ~> check ~> toRussian ~> putStrLn
-- (IO Str) (Str -> [Tokens]) ([Tokens] -> Equation) (Equation -> Bool) (Bool -> Str) (Str -> IO())
