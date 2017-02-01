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
open Cps

let threshold_default = 15
let threshold =
  ref threshold_default

let rec size_exp = function
  | LetRec (_, _, _, e0, e1) | If (_, e0, e1) ->
    1 + size_exp e0 + size_exp e1
  | Let (_, v0, e0) ->
    1 + size_term v0 + size_exp e0
  | App (_, _, cont)
  | Add (_, _, cont)
  | Sub (_, _, cont)
  | Mul (_, _, cont)
  | Div (_, _, cont)
  | Gt (_, _, cont)
  | Le (_, _, cont)
  | Eq (_, _, cont)
  | Ne (_, _, cont)
  | Not (_, cont)
  | Neg (_, cont) ->
    1 + size_cont cont
  | _ ->
    1
and size_term = function
  | Fun (_, _, e0) ->
    1 + size_exp e0
  | _ ->
    1
and size_cont = function
  | Cont (_, e0) ->
    1 + size_exp e0
let size = size_exp

let rec inline_app (env: (var, (var * var * exp)) Env.t) = function
  | LetRec (x0, x1, x2, e0, e1) when size e0 < !threshold ->
    let env0 = if size e0 >= !threshold then env else Env.extend x0 (x1, x2, rename_exp Env.empty e0) env in
    let e0' = inline_app env0 e0 in
    let e1' = inline_app env0 e1 in
    LetRec (x0, x1, x2, e0', e1')
  | Let (x0, Fun (x1, x2, e0), e1) ->
    let env0 = if size e0 >= !threshold then env else Env.extend x0 (x1, x2, e0) env in
    let e0' = inline_app env e0 in
    let e1' = inline_app env0 e1 in
    Let (x0, Fun (x1, x2, e0'), e1')
  | Let (x0, v0, e0) ->
    Let (x0, v0, inline_app env e0)
  | If (x0, e0, e1) ->
    let e0' = inline_app env e0 in
    let e1' = inline_app env e1 in
    If (x0, e0', e1')
  | App (x0, x1, Cont (x2, e0)) when Env.mem x0 env ->
    let (x1', x2', e1) = Env.lookup x0 env in
    inline_ret (Env.singleton x2' (Cont (x2, e0)))
      (rename_exp (Env.singleton x1' x1) e1)
  | App (x0, x1, Cont (x2, e0)) ->
    App (x0, x1, Cont (x2, inline_app env e0))
  | Add (x0, x1, Cont (x2, e0)) ->
    Add (x0, x1, Cont (x2, inline_app env e0))
  | Sub (x0, x1, Cont (x2, e0)) ->
    Sub (x0, x1, Cont (x2, inline_app env e0))
  | Mul (x0, x1, Cont (x2, e0)) ->
    Mul (x0, x1, Cont (x2, inline_app env e0))
  | Div (x0, x1, Cont (x2, e0)) ->
    Div (x0, x1, Cont (x2, inline_app env e0))
  | Gt (x0, x1, Cont (x2, e0)) ->
    Gt (x0, x1, Cont (x2, inline_app env e0))
  | Le (x0, x1, Cont (x2, e0)) ->
    Le (x0, x1, Cont (x2, inline_app env e0))
  | Eq (x0, x1, Cont (x2, e0)) ->
    Eq (x0, x1, Cont (x2, inline_app env e0))
  | Ne (x0, x1, Cont (x2, e0)) ->
    Ne (x0, x1, Cont (x2, inline_app env e0))
  | Not (x0, Cont (x1, e0)) ->
    Not (x0, Cont (x1, inline_app env e0))
  | Neg (x0, Cont (x1, e0)) ->
    Neg (x0, Cont (x1, inline_app env e0))
  | e0 -> e0

and inline_ret (env: (var, cont) Env.t) = function
  | LetRec (x0, x1, x2, e0, e1) ->
    let e0' = inline_ret env e0 in
    let e1' = inline_ret env e1 in
    LetRec (x0, x1, x2, e0', e1')
  | Let (x0, v0, e0) ->
    Let (x0, v0, inline_ret env e0)
  | If (x0, e0, e1) ->
    let e0' = inline_ret env e0 in
    let e1' = inline_ret env e1 in
    If (x0, e0', e1')
  | Ret (x0, x1) when Env.mem x0 env ->
    let (Cont (x1', e0)) = Env.lookup x0 env in
    rename_exp (Env.singleton x1' x1) e0
  | App (x0, x1, Cont (x2, e0)) ->
    App (x0, x1, Cont (x2, inline_ret env e0))
  | Add (x0, x1, Cont (x2, e0)) ->
    Add (x0, x1, Cont (x2, inline_ret env e0))
  | Sub (x0, x1, Cont (x2, e0)) ->
    Sub (x0, x1, Cont (x2, inline_ret env e0))
  | Mul (x0, x1, Cont (x2, e0)) ->
    Mul (x0, x1, Cont (x2, inline_ret env e0))
  | Div (x0, x1, Cont (x2, e0)) ->
    Div (x0, x1, Cont (x2, inline_ret env e0))
  | Gt (x0, x1, Cont (x2, e0)) ->
    Gt (x0, x1, Cont (x2, inline_ret env e0))
  | Le (x0, x1, Cont (x2, e0)) ->
    Le (x0, x1, Cont (x2, inline_ret env e0))
  | Eq (x0, x1, Cont (x2, e0)) ->
    Eq (x0, x1, Cont (x2, inline_ret env e0))
  | Ne (x0, x1, Cont (x2, e0)) ->
    Ne (x0, x1, Cont (x2, inline_ret env e0))
  | Not (x0, Cont (x1, e0)) ->
    Not (x0, Cont (x1, inline_ret env e0))
  | Neg (x0, Cont (x1, e0)) ->
    Neg (x0, Cont (x1, inline_ret env e0))
  | e0 -> e0

let f (Cont (x0, e0)) =
  Cont (x0, inline_app Env.empty e0)
