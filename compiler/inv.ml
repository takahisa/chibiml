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
open Untyped

let rec inv_exp e (k: Cps.var) =
  match e with
  | Cps.LetRec (x0, x1, x2, e0, e1) ->
    let e0' = inv_exp e0 x2 in
    let e1' = inv_exp e1 k in
    LetRec (x0, x1, e0', e1')
  | Cps.Let (x0, v0, e1) ->
    let e0' = inv_term v0 in
    let e1' = inv_exp e1 k in
    Let (x0, e0', e1')
  | Cps.If (x0, e0, e1) ->
    let e0' = inv_exp e0 k in
    let e1' = inv_exp e1 k in
    If (Var x0, e0', e1')
  | Cps.App (x0, x1, Cps.Cont (x2, e0)) ->
    Let (x2, App (Var x0, Var x1), inv_exp e0 k)
  | Cps.Add (x0, x1, Cps.Cont (x2, e0)) ->
    Let (x2, Add (Var x0, Var x1), inv_exp e0 k)
  | Cps.Sub (x0, x1, Cps.Cont (x2, e0)) ->
    Let (x2, Sub (Var x0, Var x1), inv_exp e0 k)
  | Cps.Mul (x0, x1, Cps.Cont (x2, e0)) ->
    Let (x2, Mul (Var x0, Var x1), inv_exp e0 k)
  | Cps.Div (x0, x1, Cps.Cont (x2, e0)) ->
    Let (x2, Div (Var x0, Var x1), inv_exp e0 k)
  | Cps.Gt (x0, x1, Cps.Cont (x2, e0)) ->
    Let (x2, Gt (Var x0, Var x1), inv_exp e0 k)
  | Cps.Le (x0, x1, Cps.Cont (x2, e0)) ->
    Let (x2, Le (Var x0, Var x1), inv_exp e0 k)
  | Cps.Eq (x0, x1, Cps.Cont (x2, e0)) ->
    Let (x2, Eq (Var x0, Var x1), inv_exp e0 k)
  | Cps.Ne (x0, x1, Cps.Cont (x2, e0)) ->
    Let (x2, Ne (Var x0, Var x1), inv_exp e0 k)
  | Cps.Not (x0, Cps.Cont (x1, e0)) ->
    Let (x1, Not (Var x0), inv_exp e0 k)
  | Cps.Neg (x0, Cps.Cont (x1, e0)) ->
    Let (x1, Neg (Var x0), inv_exp e0 k)
  | Cps.Ret (x0, x1) when k = x0 ->
    Var x1
  | Cps.Ret (_, x0) | Cps.Var x0 ->
    Var x0

and inv_term = function
  | Cps.Fun (x0, x1, e0) ->
    Fun (x0, inv_exp e0 x1)
  | Cps.Int n0 ->
    Int n0
  | Cps.Bool b0 ->
    Bool b0
  | Cps.Unit ->
    Unit

and inv_cont = function
  | Cps.Cont (x0, e0) ->
    inv_exp e0 x0

let f cont =
  inv_cont cont

let pp_tpe = Untyped.pp_tpe
let pp_exp = Untyped.pp_exp
