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
type var = int
type def =
  | LetRec of var * var list * var list * exp
 and exp =
  | Var  of var
  | Lit  of lit
  | Let  of var * exp * exp
  | App  of var * exp
  | LetClosure of var * closure * exp
  | AppClosure of var * exp
  | If   of exp * exp * exp
  | Add  of exp * exp
  | Sub  of exp * exp
  | Mul  of exp * exp
  | Div  of exp * exp
  | Eq   of exp * exp
  | Ne   of exp * exp
  | Gt   of exp * exp
  | Le   of exp * exp
  | Not  of exp
  | Neg  of exp
 and lit =
  | Int  of int
  | Bool of bool
  | Unit
 and closure =
  | Closure of var * var list

let pp_lit = function
  | Int n0  -> string_of_int n0
  | Bool b0 -> string_of_bool b0
  | Unit    -> "()"

let rec pp_exp = function
  | Var x0 ->
    "_" ^ string_of_int x0
  | Lit v0 ->
    pp_lit v0
  | Let (x0, e0, e1) ->
    Printf.sprintf "let _%d = %s in %s" x0 (pp_exp e0) (pp_exp e1)
  | LetClosure (x0, Closure (x1, xs0), e0) ->
    Printf.sprintf "let _%d = make-closure(_%d, [%s]) in %s"
      x0 x1 (String.concat " " (List.map string_of_int xs0)) (pp_exp e0)
  | App (x0, e1) | AppClosure (x0, e1) ->
    Printf.sprintf "(_%d %s)" x0 (pp_exp e1)
  | If (e0, e1, e2) ->
    Printf.sprintf "(if %s then %s else %s)" (pp_exp e0) (pp_exp e1) (pp_exp e2)
  | Add (e0, e1) ->
    Printf.sprintf "(%s + %s)" (pp_exp e0) (pp_exp e1)
  | Sub (e0, e1) ->
    Printf.sprintf "(%s - %s)" (pp_exp e0) (pp_exp e1)
  | Mul (e0, e1) ->
    Printf.sprintf "(%s * %s)" (pp_exp e0) (pp_exp e1)
  | Div (e0, e1) ->
    Printf.sprintf "(%s / %s)" (pp_exp e0) (pp_exp e1)
  | Eq (e0, e1) ->
    Printf.sprintf "(%s = %s)" (pp_exp e0) (pp_exp e1)
  | Ne (e0, e1) ->
    Printf.sprintf "(%s <> %s)" (pp_exp e0) (pp_exp e1)
  | Gt (e0, e1) ->
    Printf.sprintf "(%s > %s)" (pp_exp e0) (pp_exp e1)
  | Le (e0, e1) ->
    Printf.sprintf "(%s < %s)" (pp_exp e0) (pp_exp e1)
  | Not e0 ->
    Printf.sprintf "(not %s)" (pp_exp e0)
  | Neg e0 ->
    Printf.sprintf "(- %s)" (pp_exp e0)

let rec pp_def = function
  | LetRec (x0, xs0, xs1, e0) ->
    Printf.sprintf "let rec _%d %s [%s] = %s;;"
      x0
      (String.concat " " (List.map string_of_int xs0))
      (String.concat " " (List.map string_of_int xs1))
      (pp_exp e0)
