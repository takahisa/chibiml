{
(*
 * Chibiml
 * Copyright (c) 2015-2016 Takahisa Watanabe <linerlock@outlook.com> All rights reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 *)
open Source
open Parser

let current_position lexbuf =
  let open Lexing in
  let p = Lexing.lexeme_start_p lexbuf in
  { name   = p.pos_fname;
    line   = p.pos_lnum;
    column = p.pos_cnum }
}

let whitespace = [' ' '\t' '\n' '\r']
let digit      = ['0'-'9']
let lower      = ['a'-'z']
let upper      = ['A'-'Z']
let alpha      = (lower | upper)
let ident      = (lower | "_") (alpha | "_" | digit)*

rule token = parse
| whitespace+
    { token lexbuf }
| "(*"
    { comment lexbuf;
      token lexbuf }
| eof
    { EOF (current_position lexbuf) }
| "+"
    { ADD (current_position lexbuf) }
| "-"
    { SUB (current_position lexbuf) }
| "*"
    { MUL (current_position lexbuf) }
| "/"
    { DIV (current_position lexbuf) }
| "="
    { EQ (current_position lexbuf) }
| "<>"
    { NE (current_position lexbuf) }
| "<"
    { LE (current_position lexbuf) }
| "<="
    { LE_EQ (current_position lexbuf) }
| ">"
    { GT (current_position lexbuf) }
| ">="
    { GT_EQ (current_position lexbuf) }
| "("
    { LPAREN (current_position lexbuf) }
| ")"
    { RPAREN (current_position lexbuf) }
| "->"
    { SINGLE_ARROW (current_position lexbuf) }
| "=>"
    { DOUBLE_ARROW (current_position lexbuf) }
| ","
    { COMMA (current_position lexbuf) }
| "|"
    { BAR (current_position lexbuf) }
| ":"
    { COL (current_position lexbuf) }
| ":"
    { COL_COL (current_position lexbuf) }
| "."
    { DOT (current_position lexbuf) }
| ";"
    { SEM (current_position lexbuf) }
| "()"
    { UNIT (current_position lexbuf) }
| "true"
    { TRUE (current_position lexbuf) }
| "false"
    { FALSE (current_position lexbuf) }
| "not"
    { NOT (current_position lexbuf) }
| "fun"
    { FUN (current_position lexbuf) }
| "let"
    { LET (current_position lexbuf) }
| "rec"
    { REC (current_position lexbuf) }
| "in"
    { IN (current_position lexbuf) }
| "if"
    { IF (current_position lexbuf) }
| "then"
    { THEN (current_position lexbuf) }
| "else"
    { ELSE (current_position lexbuf) }
| digit+
    { INT (int_of_string @@ Lexing.lexeme lexbuf, current_position lexbuf) }
| ident
    { VAR (Lexing.lexeme lexbuf, current_position lexbuf) }
| "'" ident
    { TYPE_VAR (Lexing.lexeme lexbuf, current_position lexbuf) }
| _
    { error ~message:(Printf.sprintf "unknown token %s" (Lexing.lexeme lexbuf))
                 ~at:(current_position lexbuf)
    }

and comment = parse
| eof
    { Printf.eprintf "warning: unterminated comment" }
| "(*"
    { comment lexbuf;
      comment lexbuf }
| "*)"
    { () }
| _
    { comment lexbuf }
