%{
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
open Syntax
open Type
open Source
open Source.Position
%}
%token <string * Source.position> VAR // "<identifier>"
%token <int * Source.position>    INT // "<integer>"
%token <Source.position> ADD          // "+"
%token <Source.position> SUB          // "-"
%token <Source.position> MUL          // "*"
%token <Source.position> DIV          // "/"
%token <Source.position> EQ           // "="
%token <Source.position> NE           // "<>"
%token <Source.position> LE           // "<"
%token <Source.position> LE_EQ        // "<="
%token <Source.position> GT           // ">"
%token <Source.position> GT_EQ        // ">="
%token <Source.position> COMMA        // ","
%token <Source.position> DOT          // "."
%token <Source.position> SEM          // ";"
%token <Source.position> COL          // ":"
%token <Source.position> COL_COL      // "::"
%token <Source.position> LPAREN       // "("
%token <Source.position> RPAREN       // ")"
%token <Source.position> LBRACKET     // "["
%token <Source.position> RBRACKET     // "]"
%token <Source.position> LBRACE       // "{"
%token <Source.position> RBRACE       // "{"
%token <Source.position> SINGLE_ARROW // "->"
%token <Source.position> DOUBLE_ARROW // "->"
%token <Source.position> BAR          // "|"
%token <Source.position> UNIT         // "()"
%token <Source.position> TRUE         // "true"
%token <Source.position> FALSE        // "false"
%token <Source.position> NOT          // "not"
%token <Source.position> FUN          // "fun"
%token <Source.position> LET          // "let"
%token <Source.position> REC          // "rec"
%token <Source.position> IN           // "in"
%token <Source.position> IF           // "if"
%token <Source.position> THEN         // "then"
%token <Source.position> ELSE         // "else"
%token <Source.position> EOF
%nonassoc BAR
%nonassoc IN ELSE
%left EQ NE GT GT_EQ LE LE_EQ
%right SINGLE_ARROW DOUBLE_ARROW
%right COL_COL
%left ADD SUB
%left MUL DIV
%nonassoc UNARY
%left VAR INT TRUE FALSE UNIT LBRACE LBRACKET LPAREN

%type <Syntax.tpe> tpe
%type <Syntax.exp> exp
%type <Syntax.exp> main
%start             main, tpe, exp
%%

main
  : exp EOF
    { $1 }
  ;

tpe
  : LPAREN tpe RPAREN
    { $2 }
  | tpe SINGLE_ARROW tpe
    { TyFun ($1, $3) @@@ at $1 }
  | VAR
    { match fst $1 with
      | "int"  -> TyInt @@@ snd $1
      | "bool" -> TyBool @@@ snd $1
      | "unit" -> TyUnit @@@ snd $1
      | s      -> failwith (Printf.sprintf "Error; unknown type '%s' (%d-%d)" s
                                (Parsing.symbol_start ())
	                            (Parsing.symbol_end ())) }
  ;

exp
  : term
    { $1 }
  | exp term
    { App ($1, $2) @@@ at $1 }
  | SUB exp %prec UNARY
    { Neg $2 @@@ $1 }
  | NOT exp %prec UNARY
    { Not $2 @@@ $1 }
  | exp ADD exp
    { Add ($1, $3) @@@ at $1 }
  | exp SUB exp
    { Sub ($1, $3) @@@ at $1 }
  | exp MUL exp
    { Mul ($1, $3) @@@ at $1 }
  | exp DIV exp
    { Div ($1, $3) @@@ at $1 }
  | exp EQ exp
    { Eq ($1, $3) @@@ at $1 }
  | exp NE exp
    { Ne ($1, $3) @@@ at $1 }
  | exp GT exp
    { Gt ($1, $3) @@@ at $1 }
  | exp LE exp
    { Le ($1, $3) @@@ at $1 }
  | exp GT_EQ exp
    { Not (Le ($1, $3) @@@ nowhere) @@@ nowhere }
  | exp LE_EQ exp
    { Not (Gt ($1, $3) @@@ nowhere) @@@ nowhere }
  | FUN parameter SINGLE_ARROW exp
    { Fun ($2, $4) @@@ $1 }
  | LET parameter EQ exp IN exp
    { Let ($2, $4, $6) @@@ $1 }
  | LET parameter parameter_list EQ exp IN exp
    { Let ($2, List.fold_right (fun param e -> Fun (param, e) @@@ nowhere) (List.rev $3) $5, $7) @@@ $1 }
  | LET REC parameter parameter_list EQ exp IN exp
    { LetRec ($3, List.rev $4, $6, $8) @@@ $1 }
  | LET REC parameter EQ exp IN exp
    { LetRec ($3, [], $5, $7) @@@ $1 }
  | IF exp THEN exp ELSE exp COL tpe
    { If ($2, $4, $6) @@@ $1 }
 | error
     { failwith (Printf.sprintf "parse error near characters %d-%d"
                                (Parsing.symbol_start ())
	                            (Parsing.symbol_end ())) }
 ;

lit
  : INT
    { Int (fst $1) @@@ snd $1 }
  | TRUE
    { Bool true @@@ $1 }
  | FALSE
    { Bool false @@@ $1 }
  | UNIT
    { Unit @@@ $1 }
  ;

term
  : LPAREN exp RPAREN
    { $2 }
  | VAR
    { Var (fst $1) @@@ snd $1 }
  | lit
    { Lit $1 @@@ at $1 }
  ;

parameter_list
  : parameter
     { $1 :: [] }
  | parameter_list parameter
     { $2 :: $1 }
  ;

parameter:
 | LPAREN VAR COL tpe RPAREN
     { (fst $2, $4) }
 | VAR
     { (fst $1, Type.gen_tpe_var ()) }
 ;
