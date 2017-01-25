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

type var  = int
type tpe  = ..
type exp  =
  | Var    of var
  | Int    of int
  | Bool   of bool
  | Unit
  | LetRec of var * var list * exp * exp
  | Let    of var * exp * exp
  | Fun    of var * exp
  | App    of exp * exp
  | Add    of exp * exp
  | Sub    of exp * exp
  | Mul    of exp * exp
  | Div    of exp * exp
  | Eq     of exp * exp
  | Ne     of exp * exp
  | Gt     of exp * exp
  | Le     of exp * exp
  | If     of exp * exp * exp
  | Not    of exp
  | Neg    of exp

let pp_var (x : int) : string =
  "_" ^ string_of_int x

let rec pp_tpe t =
  "<unknown>"
let rec pp_exp e =
  match e with
  | Var x0 ->
    pp_var x0
  | Int n0 ->
    string_of_int n0
  | Bool b0 ->
    string_of_bool b0
  | Unit ->
    "()"
  | LetRec (x0, xs0, e0, e1) ->
    Printf.sprintf "let rec %s %s = %s in %s"
      (pp_var x0) (String.concat " " @@ List.map pp_var xs0) (pp_exp e0) (pp_exp e1)
  | Let (x0, e0, e1) ->
    Printf.sprintf "let %s = %s in %s"
      (pp_var x0) (pp_exp e0) (pp_exp e1)
  | Fun (x0, e0) ->
    Printf.sprintf "(fun %s -> %s)"
      (pp_var x0) (pp_exp e0)
  | App (e0, e1) ->
    Printf.sprintf "(%s %s)"
      (pp_exp e0) (pp_exp e1)
  | Add (e0, e1) ->
    Printf.sprintf "(%s + %s)"
      (pp_exp e0) (pp_exp e1)
  | Sub (e0, e1) ->
    Printf.sprintf "(%s - %s)"
      (pp_exp e0) (pp_exp e1)
  | Mul (e0, e1) ->
    Printf.sprintf "(%s * %s)"
      (pp_exp e0) (pp_exp e1)
  | Div (e0, e1) ->
    Printf.sprintf "(%s / %s)"
      (pp_exp e0) (pp_exp e1)
  | Gt (e0, e1) ->
    Printf.sprintf "(%s > %s)"
      (pp_exp e0) (pp_exp e1)
  | Le (e0, e1) ->
    Printf.sprintf "(%s < %s)"
      (pp_exp e0) (pp_exp e1)
  | Eq (e0, e1) ->
    Printf.sprintf "(%s = %s)"
      (pp_exp e0) (pp_exp e1)
  | Ne (e0, e1) ->
    Printf.sprintf "(%s <> %s)"
      (pp_exp e0) (pp_exp e1)
  | If (e0, e1, e2) ->
    Printf.sprintf "(if %s then %s else %s)"
      (pp_exp e0) (pp_exp e1) (pp_exp e2)
  | Not e0 ->
    Printf.sprintf "(not %s)"
      (pp_exp e0)
  | Neg e0 ->
    Printf.sprintf "(- %s)"
      (pp_exp e0)

let rec f e =
  match e.it with
  | Alpha.Var x0 ->
    Var x0
  | Alpha.Int n0 ->
    Int n0
  | Alpha.Bool b0 ->
    Bool b0
  | Alpha.Unit ->
    Unit
  | Alpha.LetRec ((x0, _), xts0, e0, e1) ->
    LetRec (x0, List.map fst xts0, f e0, f e1)
  | Alpha.Let ((x0, _), e0, e1) ->
    Let (x0, f e0, f e1)
  | Alpha.Fun ((x0, _), e0) ->
    Fun (x0, f e0)
  | Alpha.App (e0, e1) ->
    App (f e0, f e1)
  | Alpha.Add (e0, e1) ->
    Add (f e0, f e1)
  | Alpha.Sub (e0, e1) ->
    Sub (f e0, f e1)
  | Alpha.Mul (e0, e1) ->
    Mul (f e0, f e1)
  | Alpha.Div (e0, e1) ->
    Div (f e0, f e1)
  | Alpha.Gt (e0, e1) ->
    Gt (f e0, f e1)
  | Alpha.Le (e0, e1) ->
    Le (f e0, f e1)
  | Alpha.Eq (e0, e1) ->
    Eq (f e0, f e1)
  | Alpha.Ne (e0, e1) ->
    Ne (f e0, f e1)
  | Alpha.GtEq (e0, e1) ->
    Not (Le (f e0, f e1))
  | Alpha.LeEq (e0, e1) ->
    Not (Gt (f e0, f e1))
  | Alpha.If (e0, e1, e2) ->
    If (f e0, f e1, f e2)
  | Alpha.Not e0 ->
    Not (f e0)
  | Alpha.Neg e0 ->
    Neg (f e0)
