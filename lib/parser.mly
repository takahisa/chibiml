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

type var = string
type exp  = exp' fragment
 and exp' =
   | Var       of var
   | Lit       of lit
   | Fun       of (var * tpe) * exp
   | Let       of (var * tpe) * exp * exp 
   | LetRec    of (var * tpe) * (var * tpe) list * exp * exp
   | If        of exp * exp * exp
   | App       of exp * exp
   | Add       of exp * exp
   | Sub       of exp * exp
   | Mul       of exp * exp
   | Div       of exp * exp
   | Gt        of exp * exp
   | Le        of exp * exp
   | Eq        of exp * exp
   | Ne        of exp * exp
   | Not       of exp
   | Neg       of exp

 and tpe  = tpe' fragment
 and tpe' =
   | TyVarName of var
   | TyVar     of int 
   | TyFun     of tpe * tpe
   | TyInt
   | TyBool
   | TyUnit
 and lit  = lit' fragment
 and lit' =
   | Int       of int
   | Bool      of bool
   | Unit

let rec g env t =
  match t.it with
  | TyVarName s0 when Env.mem s0 env ->
     (env, Type.TyVar (Env.lookup s0 env) @@@ nowhere)
  | TyVarName s0 ->
     let x0 = Type.gen_tyvar_sym () in
     let t0 = Type.TyVar x0 @@@ nowhere in
     (Env.extend s0 x0 env, t0)
  | TyFun (t00, t01) ->
     let (env0, t00') = g env t00 in
     let (env1, t01') = g env0 t01 in
     (env1, Type.TyFun (t00', t01') @@@ t.at)
  | TyVar x0 -> (env, Type.TyVar x0 @@@ t.at)
  | TyInt    -> (env, Type.TyInt @@@ t.at)
  | TyBool   -> (env, Type.TyBool @@@ t.at)
  | TyUnit   -> (env, Type.TyUnit @@@ t.at)

let rec f env e =
  match e.it with
  | Var x0 -> (env, Syntax.Var x0 @@@ e.at)
  | Lit l0 -> begin
      match l0.it with
      | Int  n0 -> (env, Syntax.Lit (Syntax.Int  n0 @@@ l0.at) @@@ e.at)
      | Bool b0 -> (env, Syntax.Lit (Syntax.Bool b0 @@@ l0.at) @@@ e.at)
      | Unit    -> (env, Syntax.Lit (Syntax.Unit    @@@ l0.at) @@@ e.at)
    end
  | Fun ((x0, t0), e0) ->
     let (env0, t0') = g env t0 in
     let (env1, e0') = f env0 e0 in
     (env1, Syntax.Fun ((x0, t0'), e0') @@@ e.at)
  | Let ((x0, t0), e0, e1) ->
     let (env0, t0') = g env t0 in
     let (env1, e0') = f env0 e0 in
     let (env2, e1') = f env1 e1 in
     (env2, Syntax.Let ((x0, t0'), e0', e1') @@@ e.at)
  | LetRec ((x0, t0), params, e0, e1) ->   
     let (env0, t0') = g env t0 in
     let (env1, params') = List.fold_left begin fun (env, params) -> fun (x, t) ->
       let (env', t') = g env t in
       (env', (x, t') :: params)
     end (env0, []) (List.rev params) in
     let (env2, e0') = f env1 e0 in
     let (env3, e1') = f env2 e1 in
     (env3, Syntax.LetRec ((x0, t0'), params', e0', e1') @@@ e.at)
  | If (e0, e1, e2) ->
     let (env0, e0') = f env e0 in
     let (env1, e1') = f env0 e1 in
     let (env2, e2') = f env1 e2 in
     (env2, Syntax.If (e0', e1', e2') @@@ e.at)
  | App (e0, e1) ->
     let (env0, e0') = f env e0 in
     let (env1, e1') = f env0 e1 in
     (env1, Syntax.App (e0', e1') @@@ e.at)
  | Add (e0, e1) ->
     let (env0, e0') = f env e0 in
     let (env1, e1') = f env0 e1 in
     (env1, Syntax.Add (e0', e1') @@@ e.at)
  | Sub (e0, e1) ->
     let (env0, e0') = f env e0 in
     let (env1, e1') = f env0 e1 in
     (env1, Syntax.Sub (e0', e1') @@@ e.at)
  | Mul (e0, e1) ->
     let (env0, e0') = f env e0 in
     let (env1, e1') = f env0 e1 in
     (env1, Syntax.Mul (e0', e1') @@@ e.at)
  | Div (e0, e1) ->
     let (env0, e0') = f env e0 in
     let (env1, e1') = f env0 e1 in
     (env1, Syntax.Div (e0', e1') @@@ e.at)
  | Eq (e0, e1) ->
     let (env0, e0') = f env e0 in
     let (env1, e1') = f env0 e1 in
     (env1, Syntax.Eq (e0', e1') @@@ e.at)
  | Ne (e0, e1) ->
     let (env0, e0') = f env e0 in
     let (env1, e1') = f env0 e1 in
     (env1, Syntax.Ne (e0', e1') @@@ e.at)
  | Gt (e0, e1) ->
     let (env0, e0') = f env e0 in
     let (env1, e1') = f env0 e1 in
     (env1, Syntax.Gt (e0', e1') @@@ e.at)
  | Le (e0, e1) ->
     let (env0, e0') = f env e0 in
     let (env1, e1') = f env0 e1 in
     (env1, Syntax.Le (e0', e1') @@@ e.at)
  | Not e0 ->
     let (env0, e0') = f env e0 in
     (env0, Syntax.Not e0' @@@ e.at)
  | Neg e0 ->
     let (env0, e0') = f env e0 in
     (env0, Syntax.Neg e0' @@@ e.at)

let f e =
 let (env0, e0) = f Env.empty e in
 let swp (a, b) = (b, a) in
 (Env.of_list @@ List.map swp (Env.to_list env0), e0)

let g t =
 let (env0, t0) = g Env.empty t in
 let swp (a, b) = (b, a) in
 (Env.of_list @@ List.map swp (Env.to_list env0), t0)
 
%}
%token <string * Source.position> VAR      // "<identifier>"
%token <string * Source.position> TYPE_VAR // "<identifier>"
%token <int * Source.position>    INT      // "<integer>"
%token <Source.position> ADD               // "+"
%token <Source.position> SUB               // "-"
%token <Source.position> MUL               // "*"
%token <Source.position> DIV               // "/"
%token <Source.position> EQ                // "="
%token <Source.position> NE                // "<>"
%token <Source.position> LE                // "<"
%token <Source.position> LE_EQ             // "<="
%token <Source.position> GT                // ">"
%token <Source.position> GT_EQ             // ">="
%token <Source.position> COMMA             // ","
%token <Source.position> DOT               // "."
%token <Source.position> SEM               // ";"
%token <Source.position> COL               // ":"
%token <Source.position> COL_COL           // "::"
%token <Source.position> LPAREN            // "("
%token <Source.position> RPAREN            // ")"
%token <Source.position> LBRACKET          // "["
%token <Source.position> RBRACKET          // "]"
%token <Source.position> LBRACE            // "{"
%token <Source.position> RBRACE            // "{"
%token <Source.position> SINGLE_ARROW      // "->"
%token <Source.position> DOUBLE_ARROW      // "->"
%token <Source.position> BAR               // "|"
%token <Source.position> UNIT              // "()"
%token <Source.position> TRUE              // "true"
%token <Source.position> FALSE             // "false"
%token <Source.position> NOT               // "not"
%token <Source.position> FUN               // "fun"
%token <Source.position> LET               // "let"
%token <Source.position> REC               // "rec"
%token <Source.position> IN                // "in"
%token <Source.position> IF                // "if"
%token <Source.position> THEN              // "then"
%token <Source.position> ELSE              // "else"
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

%type <(Type.var, string) Env.t * Syntax.tpe> tpe
%type <(Type.var, string) Env.t * Syntax.exp> exp
%type <(Type.var, string) Env.t * Syntax.exp> main
%start main, tpe, exp
%%

main
  : exp EOF
    { $1 }
  ;

tpe
  : tpe_ 
    { g $1 }
tpe_
  : LPAREN tpe_ RPAREN
    { $2 }
  | tpe_ SINGLE_ARROW tpe_
    { TyFun ($1, $3) @@@ at $1 }
  | TYPE_VAR
    { TyVarName (fst $1) @@@ snd $1 }
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
  : exp_
    { f $1 }
exp_
  : term_
    { $1 }
  | exp_ term_
    { App ($1, $2) @@@ at $1 }
  | SUB exp_ %prec UNARY
    { Neg $2 @@@ $1 }
  | NOT exp_ %prec UNARY
    { Not $2 @@@ $1 }
  | exp_ ADD exp_
    { Add ($1, $3) @@@ at $1 }
  | exp_ SUB exp_
    { Sub ($1, $3) @@@ at $1 }
  | exp_ MUL exp_
    { Mul ($1, $3) @@@ at $1 }
  | exp_ DIV exp_
    { Div ($1, $3) @@@ at $1 }
  | exp_ EQ exp_
    { Eq ($1, $3) @@@ at $1 }
  | exp_ NE exp_
    { Ne ($1, $3) @@@ at $1 }
  | exp_ GT exp_
    { Gt ($1, $3) @@@ at $1 }
  | exp_ LE exp_
    { Le ($1, $3) @@@ at $1 }
  | exp_ GT_EQ exp_
    { Not (Le ($1, $3) @@@ nowhere) @@@ nowhere }
  | exp_ LE_EQ exp_
    { Not (Gt ($1, $3) @@@ nowhere) @@@ nowhere }
  | FUN parameter SINGLE_ARROW exp_
    { Fun ($2, $4) @@@ $1 }
  | LET parameter EQ exp_ IN exp_
    { Let ($2, $4, $6) @@@ $1 }
  | LET parameter parameter_list EQ exp_ IN exp_
    { Let ($2, List.fold_right (fun param e -> Fun (param, e) @@@ nowhere) (List.rev $3) $5, $7) @@@ $1 }
  | LET REC VAR parameter_list COL tpe_ EQ exp_ IN exp_
    { LetRec ((fst $3, $6), List.rev $4, $8, $10) @@@ $1 }
  | LET REC parameter parameter_list EQ exp_ IN exp_
    { LetRec ($3, List.rev $4, $6, $8) @@@ $1 }
  | LET REC VAR COL tpe_ EQ exp_ IN exp_
    { LetRec ((fst $3, $5), [], $7, $9) @@@ $1 }
  | LET REC parameter EQ exp_ IN exp_
    { LetRec ($3, [], $5, $7) @@@ $1 }
  | IF exp_ THEN exp_ ELSE exp_
    { If ($2, $4, $6) @@@ $1 }
 | error
     { failwith (Printf.sprintf "parse error near characters %d-%d"
                                (Parsing.symbol_start ())
	                            (Parsing.symbol_end ())) }
 ;

lit_
  : INT
    { Int (fst $1) @@@ snd $1 }
  | TRUE
    { Bool true @@@ $1 }
  | FALSE
    { Bool false @@@ $1 }
  | UNIT
    { Unit @@@ $1 }
  ;

term_
  : LPAREN exp_ RPAREN
    { $2 }
  | VAR
    { Var (fst $1) @@@ snd $1 }
  | lit_
    { Lit $1 @@@ at $1 }
  ;

parameter_list
  : parameter
     { $1 :: [] }
  | parameter_list parameter
     { $2 :: $1 }
  ;

parameter:
 | LPAREN VAR COL tpe_ RPAREN
     { (fst $2, $4) }
 | VAR
     { (fst $1, TyVar (Fresh.f ()) @@@ nowhere) }
 ;
