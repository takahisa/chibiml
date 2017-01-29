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
open Cps

let const_b x env =
  try
    match Env.lookup x env with
    | Bool b0 -> Some b0
    | _       -> None
  with
    _ -> None

let const_i x env =
  try
    match Env.lookup x env with
    | Int n0 -> Some n0
    | _      -> None
  with
    _ -> None

let rec fold_exp env = function
  | LetRec (x0, xs0, x1, e0, e1) ->
    let e0' = fold_exp env e0 in
    let e1' = fold_exp env e1 in
    LetRec (x0, xs0, x1, e0', e1')
  | Let (x0, v0, e0) ->
    let v0' = fold_term env v0 in
    let e0' = fold_exp (Env.extend x0 v0' env) e0 in
    Let (x0, v0', e0')
  | If (x0, e0, e1) ->
    (match const_b x0 env with
     | Some true -> fold_exp env e0
     | Some _    -> fold_exp env e1
     | _ ->
       let e0' = fold_exp env e0 in
       let e1' = fold_exp env e1 in
       If (x0, e0', e1'))
  | Add (x0, x1, Cont (x2, e0)) ->
    (match const_i x0 env, const_i x1 env with
     | Some n0, Some n1 ->
       let v0' = Int (n0 + n1) in
       let e0' = fold_exp (Env.extend x2 v0' env) e0 in
       Let (x2, v0', e0')
     | _ ->
       Add (x0, x1, Cont (x2, fold_exp env e0)))
  | Sub (x0, x1, Cont (x2, e0)) ->
    (match const_i x0 env, const_i x1 env with
     | Some n0, Some n1 ->
       let v0' = Int (n0 - n1) in
       let e0' = fold_exp (Env.extend x2 v0' env) e0 in
       Let (x2, v0', e0')
     | _ ->
       Sub (x0, x1, Cont (x2, fold_exp env e0)))
  | Mul (x0, x1, Cont (x2, e0)) ->
    (match const_i x0 env, const_i x1 env with
     | Some n0, Some n1 ->
       let v0' = Int (n0 * n1) in
       let e0' = fold_exp (Env.extend x2 v0' env) e0 in
       Let (x2, v0', e0')
     | _ ->
       Mul (x0, x1, Cont (x2, fold_exp env e0)))
  | Div (x0, x1, Cont (x2, e0)) ->
    (match const_i x0 env, const_i x1 env with
     | Some n0, Some n1 ->
       let v0' = Int (n0 / n1) in
       let e0' = fold_exp (Env.extend x2 v0' env) e0 in
       Let (x2, v0', e0')
     | _ ->
       Div (x0, x1, Cont (x2, fold_exp env e0)))
  | Gt (x0, x1, Cont (x2, e0)) ->
    (match const_i x0 env, const_i x1 env with
     | Some n0, Some n1 ->
       let v0' = Bool (n0 > n1) in
       let e0' = fold_exp (Env.extend x2 v0' env) e0 in
       Let (x2, v0', e0')
     | _ ->
       Gt (x0, x1, Cont (x2, fold_exp env e0)))
  | Le (x0, x1, Cont (x2, e0)) ->
    (match const_i x0 env, const_i x1 env with
     | Some n0, Some n1 ->
       let v0' = Bool (n0 < n1) in
       let e0' = fold_exp (Env.extend x2 v0' env) e0 in
       Let (x2, v0', e0')
     | _ ->
       Le (x0, x1, Cont (x2, fold_exp env e0)))
  | Eq (x0, x1, Cont (x2, e0)) ->
    (match const_i x0 env, const_i x1 env with
     | Some n0, Some n1 ->
       let v0' = Bool (n0 = n1) in
       let e0' = fold_exp (Env.extend x2 v0' env) e0 in
       Let (x2, v0', e0')
     | _ ->
       Eq (x0, x1, Cont (x2, fold_exp env e0)))
  | Ne (x0, x1, Cont (x2, e0)) ->
    (match const_i x0 env, const_i x1 env with
     | Some n0, Some n1 ->
       fold_exp (Env.extend x2 (Bool (n0 <> n1)) env) e0
     | _ ->
       Ne (x0, x1, Cont (x2, fold_exp env e0)))
  | Not (x0, Cont (x1, e0)) ->
    (match const_b x0 env with
     | Some b0 ->
       let v0' = Bool (not b0) in
       let e0' = fold_exp (Env.extend x1 v0' env) e0 in
       Let (x1, v0', e0')
     | _ ->
       Not (x1, Cont (x1, fold_exp env e0)))
  | Neg (x0, Cont (x1, e0)) ->
    (match const_i x0 env with
     | Some n0 ->
       let v0' = Int (- n0) in
       let e0' = fold_exp (Env.extend x1 v0' env) e0 in
       Let (x1, v0', e0')
     | _ ->
       Neg (x0, Cont (x1, fold_exp env e0)))
  | e0 -> e0

and fold_term env = function
  | Fun (x0, x1, e0) ->
    Fun (x0, x1, fold_exp env e0)
  | v0 -> v0

and fold_cont env = function
  | Cont (x0, e0) ->
    Cont (x0, fold_exp env e0)

let f cont =
  fold_cont Env.empty cont
