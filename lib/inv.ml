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
  | Cps.LetRec (x0, xs0, x1, e0, e1) ->
    let e0' = inv_exp e0 x1 in
    let e1' = inv_exp e1 k in
    LetRec (x0, xs0, e0', e1')
  | Cps.Let (x0, Cps.Cont (x1, e0), e1) ->
    Let (x0, Fun (x1, inv_exp e k), inv_exp e1 k)
  | Cps.If (v0, e0, e1) ->
    If (inv_term v0, inv_exp e0 k, inv_exp e1 k)
  | Cps.App (v0, v1, Cps.Cont (x0, e0)) ->
    Let (x0, App (inv_term v0, inv_term v1), inv_exp e0 k)
  | Cps.Add (v0, v1, Cps.Cont (x0, e0)) ->
    Let (x0, Add (inv_term v0, inv_term v1), inv_exp e0 k)
  | Cps.Sub (v0, v1, Cps.Cont (x0, e0)) ->
    Let (x0, Sub (inv_term v0, inv_term v1), inv_exp e0 k)
  | Cps.Mul (v0, v1, Cps.Cont (x0, e0)) ->
    Let (x0, Mul (inv_term v0, inv_term v1), inv_exp e0 k)
  | Cps.Div (v0, v1, Cps.Cont (x0, e0)) ->
    Let (x0, Div (inv_term v0, inv_term v1), inv_exp e0 k)
  | Cps.Gt (v0, v1, Cps.Cont (x0, e0)) ->
    Let (x0, Gt (inv_term v0, inv_term v1), inv_exp e0 k)
  | Cps.Le (v0, v1, Cps.Cont (x0, e0)) ->
    Let (x0, Le (inv_term v0, inv_term v1), inv_exp e0 k)
  | Cps.Eq (v0, v1, Cps.Cont (x0, e0)) ->
    Let (x0, Eq (inv_term v0, inv_term v1), inv_exp e0 k)
  | Cps.Ne (v0, v1, Cps.Cont (x0, e0)) ->
    Let (x0, Ne (inv_term v0, inv_term v1), inv_exp e0 k)
  | Cps.Not (v0, Cps.Cont (x0, e0)) ->
    Let (x0, Not (inv_term v0), inv_exp e0 k)
  | Cps.Neg (v0, Cps.Cont (x0, e0)) ->
    Let (x0, Neg (inv_term v0), inv_exp e0 k)
  | Cps.Ret (x0, v0) when k = x0 ->
    inv_term v0
  | Cps.Ret (x0, v0) ->
    App (Var x0, inv_term v0)

and inv_term = function
  | Cps.Fun (x0, x1, e0) ->
    Fun (x0, inv_exp e0 x1)
  | Cps.Var x0 ->
    Var x0
  | Cps.Int n0 ->
    Int n0
  | Cps.Bool b0 ->
    Bool b0
  | Cps.Unit ->
    Unit

and inv_cont = function
  | Cps.Cont (x0, e0) -> inv_exp e0 x0

let f cont =
  inv_cont cont
