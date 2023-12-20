import Lexer
import Parser

(~>) = flip (.)
  
cantorNormalForm = id

check :: Equation -> Bool
check (Equation left right) = cantorNormalForm left == cantorNormalForm right

toRussian True = "Равны"
toRussian False = "Не равны"
main = getLine >>= alexScanTokens ~> parseOrdinals ~> check ~> toRussian ~> putStrLn
-- (IO Str) (Str -> [Tokens]) ([Tokens] -> Equation) (Equation -> Bool) (Bool -> Str) (Str -> IO())

