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

let rec const_i env = function
  | Var x0 when Env.mem x0 env -> const_i env (Env.lookup x0 env)
  | Int n0 -> Some n0
  | _      -> None

let rec const_b env = function
  | Var x0 when Env.mem x0 env -> const_b env (Env.lookup x0 env)
  | Bool b0 -> Some b0
  | _       -> None

let rec fold_exp env = function
  | LetRec (x0, xs0, x1, e0, e1) ->
    let e0' = fold_exp env e0 in
    let e1' = fold_exp env e1 in
    LetRec (x0, xs0, x1, e0', e1')
  | Let (x0, Cont (x1, e0), e1) ->
    let e0' = fold_exp env e0 in
    let e1' = fold_exp env e1 in
    Let (x0, Cont (x1, e0'), e1')
  | If (v0, e0, e1) ->
    (match const_b env v0 with
     | Some b0 when b0 -> fold_exp env e0
     | Some _          -> fold_exp env e1
     | _ ->
       If (fold_term env v0, fold_exp env e0, fold_exp env e1))
  | App (v0, v1, Cont (x1, e0)) ->
    App (fold_term env v0, fold_term env v1, Cont (x1, fold_exp env e0))
  | Add (v0, v1, Cont (x0, e0)) ->
    (match const_i env v0, const_i env v1 with
     | Some n0, Some n1 ->
       fold_exp (Env.extend x0 (Int (n0 + n1)) env) e0
     | _ ->
       Add (fold_term env v0, fold_term env v1, Cont (x0, fold_exp env e0)))
  | Sub (v0, v1, Cont (x0, e0)) ->
    (match const_i env v0, const_i env v1 with
     | Some n0, Some n1 ->
       fold_exp (Env.extend x0 (Int (n0 - n1)) env) e0
     | _ ->
       Sub (fold_term env v0, fold_term env v1, Cont (x0, fold_exp env e0)))
  | Mul (v0, v1, Cont (x0, e0)) ->
    (match const_i env v0, const_i env v1 with
     | Some n0, Some n1 ->
       fold_exp (Env.extend x0 (Int (n0 * n1)) env) e0
     | _ ->
       Mul (v0, v1, Cont (x0, fold_exp env e0)))
  | Div (v0, v1, Cont (x0, e0)) ->
    (match const_i env v0, const_i env v1 with
     | Some n0, Some n1 ->
       fold_exp (Env.extend x0 (Int (n0 / n1)) env) e0
     | _ ->
       Div (fold_term env v0, fold_term env v1, Cont (x0, fold_exp env e0)))
  | Gt (v0, v1, Cont (x0, e0)) ->
    (match const_i env v0, const_i env v1 with
     | Some n0, Some n1 ->
       fold_exp (Env.extend x0 (Bool (n0 > n1)) env) e0
     | _ ->
       Gt (fold_term env v0, fold_term env v1, Cont (x0, fold_exp env e0)))
  | Le (v0, v1, Cont (x0, e0)) ->
    (match const_i env v0, const_i env v1 with
     | Some n0, Some n1 ->
       fold_exp (Env.extend x0 (Bool (n0 < n1)) env) e0
     | _ ->
       Le (fold_term env v0, fold_term env v1, Cont (x0, fold_exp env e0)))
  | Eq (v0, v1, Cont (x0, e0)) ->
    (match const_i env v0, const_i env v1 with
     | Some n0, Some n1 ->
       fold_exp (Env.extend x0 (Bool (n0 = n1)) env) e0
     | _ ->
       Eq (fold_term env v0, fold_term env v1, Cont (x0, fold_exp env e0)))
  | Ne (v0, v1, Cont (x0, e0)) ->
    (match const_i env v0, const_i env v1 with
     | Some n0, Some n1 ->
       fold_exp (Env.extend x0 (Bool (n0 <> n1)) env) e0
     | _ ->
       Ne (fold_term env v0, fold_term env v1, Cont (x0, fold_exp env e0)))
  | Not (v0, Cont (x0, e0)) ->
    (match const_b env v0 with
     | Some b0 ->
       fold_exp (Env.extend x0 (Bool (not b0)) env) e0
     | _ ->
       Not (v0, Cont (x0, fold_exp env e0)))
  | Neg (v0, Cont (x0, e0)) ->
    (match const_i env v0 with
     | Some n0 ->
       fold_exp (Env.extend x0 (Int (- n0)) env) e0
     | _ ->
       Neg (v0, Cont (x0, fold_exp env e0)))
  | Ret (x0, Fun (x1, x2, e0)) ->
    Ret (x0, Fun (x1, x2, fold_exp env e0))
  | Ret (x0, Var x1) when Env.mem x1 env ->
    Ret (x0, Env.lookup x1 env)
  | e -> e

and fold_term env = function
  | Fun (x0, x1, e0) ->
    Fun (x0, x1, fold_exp env e0)
  | Var x0 when Env.mem x0 env ->
    Env.lookup x0 env
  | v0 -> v0

and fold_cont env = function
  | Cont (x0, e0) -> Cont (x0, fold_exp env e0)

let f cont =
  fold_cont Env.empty cont
