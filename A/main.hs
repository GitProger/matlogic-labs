import Lexer
import Parser
(~>) = flip (.)
main = getLine >>= alexScanTokens ~> parseProof ~> show ~> putStrLn
