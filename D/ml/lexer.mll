{
open Parser;;
}

let whs = [' ' '\t' '\r' '\n' '\ ']
let var = ['A' - 'Z']+ ['A' - 'Z' '0' - '9' '\'']*

rule main = parse
        | whs      { main lexbuf }
        | var as v { VAR(v) }
        | "("      { LEFT_BR }
        | ")"      { RIGHT_BR }
        | "&"      { AND }
        | "->"     { IMPLY }
        | "!"      { NOT }
        | "|"      { OR }
        | ","      { COMMA }
        | "_|_"    { EMPTY }
        | eof      { EOF }  