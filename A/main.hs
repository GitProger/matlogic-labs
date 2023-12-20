import LocalUtils
import Lexer
import Parser
main = getLine >>= alexScanTokens ~> parseProof ~> show ~> putStrLn
