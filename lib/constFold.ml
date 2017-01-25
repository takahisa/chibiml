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

let rec f env = function
  | LetRec (x0, xs0, x1, e0, e1) ->
    let e0' = f env e0 in
    let e1' = f env e1 in
    LetRec (x0, xs0, x1, e0', e1')
  | Let (x0, Cont (x1, e0), e1) ->
    let e0' = f env e0 in
    let e1' = f env e1 in
    Let (x0, Cont (x1, e0'), e1')
  | If (v0, e0, e1) ->
    (match const_b env v0 with
     | Some b0 when b0 -> f env e0
     | Some _          -> f env e1
     | _ ->
       If (v0, f env e0, f env e1))
  | App (v0, v1, Cont (x1, e0)) ->
    App (v0, v1, Cont (x1, f env e0))
  | Add (v0, v1, Cont (x1, e0)) ->
    (match const_i env v0, const_i env v1 with
     | Some n0, Some n1 ->
       let x0 = Fresh.f () in
       let v2 = Int (n0 + n1) in
       Let (x0, Cont (x1, f (Env.extend x1 v2 env) e0), Ret (x0, v2))
     | _ ->
       Add (v0, v1, Cont (x1, f env e0)))
  | Sub (v0, v1, Cont (x1, e0)) ->
    (match const_i env v0, const_i env v1 with
     | Some n0, Some n1 ->
       let x0 = Fresh.f () in
       let v2 = Int (n0 - n1) in
       Let (x0, Cont (x1, f (Env.extend x1 v0 env) e0), Ret (x0, v2))
     | _ ->
       Sub (v0, v1, Cont (x1, f env e0)))
  | Mul (v0, v1, Cont (x1, e0)) ->
    (match const_i env v0, const_i env v1 with
     | Some n0, Some n1 ->
       let x0 = Fresh.f () in
       let v2 = Int (n0 * n1) in
       Let (x0, Cont (x1, f (Env.extend x1 v0 env) e0), Ret (x0, v2))
     | _ ->
       Mul (v0, v1, Cont (x1, f env e0)))
  | Div (v0, v1, Cont (x1, e0)) ->
    (match const_i env v0, const_i env v1 with
     | Some n0, Some n1 ->
       let x0 = Fresh.f () in
       let v2 = Int (n0 / n1) in
       Let (x0, Cont (x1, f (Env.extend x1 v0 env) e0), Ret (x0, v2))
     | _ ->
       Div (v0, v1, Cont (x1, f env e0)))
  | Gt (v0, v1, Cont (x1, e0)) ->
    (match const_i env v0, const_i env v1 with
     | Some n0, Some n1 ->
       let x0 = Fresh.f () in
       let v0 = Bool (n0 > n1) in
       Let (x0, Cont (x1, f (Env.extend x1 v0 env) e0), Ret (x0, v0))
     | _ ->
       Gt (v0, v1, Cont (x1, f env e0)))
  | Le (v0, v1, Cont (x1, e0)) ->
    (match const_i env v0, const_i env v1 with
     | Some n0, Some n1 ->
       let x0 = Fresh.f () in
       let v2 = Bool (n0 < n1) in
       Let (x0, Cont (x1, f (Env.extend x1 v2 env) e0), Ret (x0, v2))
     | _ ->
       Le (v0, v1, Cont (x1, f env e0)))
  | Eq (v0, v1, Cont (x1, e0)) ->
    (match const_i env v0, const_i env v1 with
     | Some n0, Some n1 ->
       let x0 = Fresh.f () in
       let v0 = Bool (n0 = n1) in
       Let (x0, Cont (x1, f (Env.extend x1 v0 env) e0), Ret (x0, v0))
     | _ ->
       Eq (v0, v1, Cont (x1, f env e0)))
  | Ne (v0, v1, Cont (x1, e0)) ->
    (match const_i env v0, const_i env v1 with
     | Some n0, Some n1 ->
       let x0 = Fresh.f () in
       let v2 = Bool (n0 <> n1) in
       Let (x0, Cont (x1, f (Env.extend x1 v2 env) e0), Ret (x0, v2))
     | _ ->
       Ne (v0, v1, Cont (x1, f env e0)))
  | Not (v0, Cont (x1, e0)) ->
    (match const_b env v0 with
     | Some b0 ->
       let x0 = Fresh.f () in
       let v2 = Bool (not b0) in
       Let (x0, Cont (x1, f (Env.extend x1 v2 env) e0), Ret (x0, v2))
     | _ ->
       Not (v0, Cont (x1, f env e0)))
  | Neg (v0, Cont (x1, e0)) ->
    (match const_i env v0 with
     | Some b0 ->
       let x0 = Fresh.f () in
       let v2 = Int (- b0) in
       Let (x0, Cont (x1, f (Env.extend x1 v0 env) e0), Ret (x0, v2))
     | _ ->
       Neg (v0, Cont (x1, f env e0)))
  | Ret (x0, Fun (x1, x2, e0)) ->
    Ret (x0, Fun (x1, x2, f env e0))
  | e -> e

let f (Cont (x0, e0)) = Cont (x0, f Env.empty e0)
