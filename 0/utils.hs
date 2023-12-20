module Utils where
import Data.List (intercalate)

(~>) = flip (.)

join :: Show a => String -> [a] -> String
join sep a = intercalate sep $ map show a

