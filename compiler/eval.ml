(*
 * Chibiml
 * Copyright (c) 2015-2020 Takahisa Watanabe <linerlock@outlook.com> All rights reserved.
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
open Alpha

module type S =
sig
  type exp
  type tpe
  type value
  val pp_exp: exp -> string
  val pp_tpe: tpe -> string
  val pp_value: value -> string
end

type var = Alpha.var
type exp = Alpha.exp
type tpe = Alpha.tpe
type value =
  | RecFunVal           of var * var * exp * (var, value) Env.t
  | RecFunVal_backpatch of var * var * exp * (var, value) Env.t ref
  | FunVal              of var * exp * (var, value) Env.t
  | IntVal              of int
  | BoolVal             of bool
  | UnitVal

let backpatch =
  ref false

let rec f env e k =
  match e.it with
  | Var x0 ->
    k @@ Env.lookup x0 env
  | Int n0 ->
    k @@ IntVal n0
  | Bool b0 ->
    k @@ BoolVal b0
  | Unit    ->
    k @@ UnitVal
  | Fun ((x0, _), e0) ->
    k @@ FunVal (x0, e0, env)
  | LetRec ((x0, _), [], e0, e1) | Let ((x0, _), e0, e1) ->
    f env e0 (fun v0 ->
        f (Env.extend x0 v0 env) e1 k)
  | LetRec ((x0, _), (x1, _) :: xts0, e0, e1) when !backpatch ->
    let e0' = List.fold_right (fun xt -> fun e -> Fun (xt, e) @@@ nowhere) xts0 e0 in
    let env0_ref = ref Env.empty in
    let env0 = Env.extend x0 (RecFunVal_backpatch (x0, x1, e0', env0_ref)) env in
    env0_ref := env0; f env0 e1 k
  | LetRec ((x0, _), (x1, _) :: xts0, e0, e1) ->
    let e0' = List.fold_right (fun xt -> fun e -> Fun (xt, e) @@@ nowhere) xts0 e0 in
    let env0 = Env.extend x0 (RecFunVal (x0, x1, e0', env)) env in
    f env0 e1 k
  | If (e0, e1, e2) ->
    f env e0 (fun v0 ->
        match v0 with
        | BoolVal true  -> f env e1 k
        | BoolVal false -> f env e2 k
        | _ -> error ~message:"invalid argument; boolean value expected" ~at:e0.at)
  | App (e0, e1) ->
    f env e1 (fun v1 ->
        f env e0 (fun v0 ->
            match v0 with
            | RecFunVal_backpatch (x0, x1, e0, env0_ref) ->
              let env0 = !env0_ref in
              let env1 = Env.extend x0 v0 env0 in
              let env2 = Env.extend x1 v1 env1 in
              f env2 e0 k
            | RecFunVal (x0, x1, e0, env0) ->
              let env1 = Env.extend x0 v0 env0 in
              let env2 = Env.extend x1 v1 env1 in
              f env2 e0 k
            | FunVal (x0, e0, env0) ->
              let env1 = Env.extend x0 v1 env0 in
              f env1 e0 k
            | _ ->
              error ~message:"invalid argument; function value expected" ~at:e0.at))
  | Add (e0, e1) | Sub (e0, e1) | Mul (e0, e1) | Div (e0, e1) ->
    f env e1 (fun v1 ->
        f env e0 (fun v0 ->
            match e.it, v0, v1 with
            | Add (_, _), IntVal n0, IntVal n1 -> k @@ IntVal (n0 + n1)
            | Sub (_, _), IntVal n0, IntVal n1 -> k @@ IntVal (n0 - n1)
            | Mul (_, _), IntVal n0, IntVal n1 -> k @@ IntVal (n0 * n1)
            | Div (_, _), IntVal n0, IntVal n1 -> k @@ IntVal (n0 / n1)
            | _ -> error ~message:"invalid argument; integer value expected." ~at:e0.at))
  | Gt (e0, e1) | GtEq (e0, e1) | Le (e0, e1) | LeEq (e0, e1) ->
    f env e1 (fun v1 ->
        f env e0 (fun v0 ->
            match e.it, v0, v1 with
            | Gt (_, _), IntVal n0, IntVal n1 -> k @@ BoolVal (n0 > n1)
            | Le (_, _), IntVal n0, IntVal n1 -> k @@ BoolVal (n0 < n1)
            | GtEq (_, _), IntVal n0, IntVal n1 -> k @@ BoolVal (n0 >= n1)
            | LeEq (_, _), IntVal n0, IntVal n1 -> k @@ BoolVal (n0 <= n1)
            | _ -> error ~message:"invalid argument; integer value expected." ~at:e0.at))
  | Eq (e0, e1) ->
    f env e1 (fun v1 ->
        f env e0 (fun v0 ->
            match v0, v1 with
            | IntVal n0, IntVal n1 -> k @@ BoolVal (n0 = n1)
            | BoolVal false, BoolVal false -> k @@ BoolVal false
            | BoolVal true,  BoolVal true  -> k @@ BoolVal true
            | UnitVal, UnitVal -> k @@ BoolVal true
            | _ -> error ~message:"invalid argument; function value cannot be specified" ~at:e.at))

  | Ne (e0, e1) ->
    f env (Not (Eq (e0, e1) @@@ nowhere) @@@ nowhere) k
  | Neg e0 ->
    f env e0 (function
        | IntVal n0 -> k @@ IntVal (-n0)
        | _ -> error ~message:"integer value expected." ~at:e0.at)
  | Not e0 ->
    f env e0 (function
        | BoolVal b0 -> k @@ BoolVal (not b0)
        | _ -> error ~message:"boolean value expected." ~at:e0.at)
let f env e = f env e (fun v0 -> v0)

let pp_exp = Alpha.pp_exp
let pp_tpe = Alpha.pp_tpe
let pp_value = function
  | RecFunVal (_, _, _, _)
  | RecFunVal_backpatch (_, _, _, _)
  | FunVal (_, _, _) ->
    "<fun>"
  | IntVal n0 ->
    string_of_int n0
  | BoolVal b0 ->
    string_of_bool b0
  | UnitVal ->
    "()"
