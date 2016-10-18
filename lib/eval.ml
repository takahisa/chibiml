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
open Config
open Source
open Source.Position
open Alpha

type value =
  | RecFunVal           of var * var * exp * (var, value) Env.t
  | RecFunVal_backpatch of var * var * exp * (var, value) Env.t ref
  | FunVal              of var * exp * (var, value) Env.t
  | IntVal              of int
  | BoolVal             of bool
  | UnitVal

let rec f env e k =
  match e.it with
  | Var y0 ->
    k @@ Env.lookup y0 env
  | Lit l0 -> begin
    match l0.it with
    | Int  n0 -> k @@ IntVal n0
    | Bool b0 -> k @@ BoolVal b0
    | Unit    -> k @@ UnitVal
    end
  | Fun ((y0, _), e0) ->
    k @@ FunVal (y0, e0, env)
  | LetRec ((y0, _), [], e0, e1) | Let ((y0, _), e0, e1) ->
    f env e0 (fun v0 ->
      f (Env.extend y0 v0 env) e1 k)
  | LetRec ((y0, _), (y1, _) :: yts0, e0, e1) when backpatch () ->
    let e0' = List.fold_left (fun e -> fun yt -> Fun (yt, e) @@@ nowhere) e0 (List.rev yts0) in
    let env0_ref = ref Env.empty in
    let env0 = Env.extend y0 (RecFunVal_backpatch (y0, y1, e0', env0_ref)) env in
    env0_ref := env0; f env0 e1 k
  | LetRec ((y0, _), (y1, _) :: yts0, e0, e1) ->
    let e0' = List.fold_left (fun e -> fun yt -> Fun (yt, e) @@@ nowhere) e0 (List.rev yts0) in
    let env0 = Env.extend y0 (RecFunVal (y0, y1, e0', env)) env in
    f env0 e1 k
  | If (e0, e1, e2) ->
    f env e0 (fun v0 ->
      match v0 with
      | BoolVal true  -> f env e1 k
      | BoolVal false -> f env e2 k
      | _ -> error "invalid argument; boolean value expected" e0.at)
  | App (e0, e1) ->
    f env e1 (fun v1 ->
      f env e0 (fun v0 ->
        match v0 with
        | RecFunVal_backpatch (y0, y1, e0, env0_ref) ->
          let env0 = !env0_ref in
          let env1 = Env.extend y0 v0 env0 in
          let env2 = Env.extend y1 v1 env1 in
          f env2 e0 k
        | RecFunVal (y0, y1, e0, env0) ->
          let env1 = Env.extend y0 v0 env0 in
          let env2 = Env.extend y1 v1 env1 in
          f env2 e0 k
        | FunVal (y0, e0, env0) ->
          let env1 = Env.extend y0 v1 env0 in
          f env1 e0 k
        | _ -> 
          error "invalid argument; function value expected" e0.at))
  | Add (e0, e1) | Sub (e0, e1) | Mul (e0, e1) | Div (e0, e1) ->
    f env e1 (fun v1 ->
      f env e0 (fun v0 ->
        match e0.it, v0, v1 with
        | Add (_, _), IntVal n0, IntVal n1 -> k @@ IntVal (n0 + n1)
        | Sub (_, _), IntVal n0, IntVal n1 -> k @@ IntVal (n0 - n1)
        | Mul (_, _), IntVal n0, IntVal n1 -> k @@ IntVal (n0 * n1)
        | Div (_, _), IntVal n0, IntVal n1 -> k @@ IntVal (n0 / n1)
        | _ -> error "invalid argument; integer value expected." e0.at))
  | Gt (e0, e1) | Le (e0, e1) ->
    f env e1 (fun v1 ->
      f env e0 (fun v0 ->
        match e0.it, v0, v1 with
        | Gt (_, _), IntVal n0, IntVal n1 -> k @@ BoolVal (n0 > n1)
        | Le (_, _), IntVal n0, IntVal n1 -> k @@ BoolVal (n0 < n1)
        | _ -> error "invalid argument; integer value expected." e0.at))
  | Eq (e0, e1) ->
    f env e1 (fun v1 ->
      f env e0 (fun v0 ->
        match v0, v1 with
        | IntVal n0, IntVal n1 -> k @@ BoolVal (n0 = n1)
        | BoolVal false, BoolVal false -> k @@ BoolVal false
        | BoolVal true,  BoolVal true  -> k @@ BoolVal true
        | UnitVal, UnitVal -> k @@ BoolVal true
        | _ -> error "invalid argument; function value cannot be specified" e.at))

  | Ne (e0, e1) ->
    f env (Not (Eq (e0, e1) @@@ nowhere) @@@ nowhere) k
  | Neg e0 ->
    f env e0 (function
      | IntVal n0 -> k @@ IntVal (-n0) 
      | _ -> error "integer value expected." e0.at)
  | Not e0 ->
    f env e0 (function 
      | BoolVal b0 -> k @@ BoolVal (not b0)
      | _ -> error "boolean value expected." e0.at)
let f env e = f env e (fun v0 -> v0)

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
