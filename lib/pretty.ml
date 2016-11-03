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
open Syntax
open Type
open Source
open Source.Position

let rec pp_tpe_var n =
  if n <= 25 then
    Printf.sprintf "'%c" (Char.chr (Char.code 'a' + n))
  else
    pp_tpe_var (n mod 26) ^ string_of_int (n / 26)

let rec pp_tpe env n t =
  match t.it with
  | TyInt ->
     (env, n, "int")
  | TyBool ->
     (env, n, "bool")
  | TyUnit ->
     (env, n, "unit")
  | TyVar x0 when Env.mem x0 env ->
     (env, n, pp_tpe_var (Env.lookup x0 env))
  | TyVar x0 ->
     let env0 = Env.extend x0 n env in
     (env0, n + 1, pp_tpe_var n)
  | TyFun (t00, t01) ->
     let (env0, n0, s0) = pp_tpe env n t00 in
     let (env1, n1, s1) = pp_tpe env0 n0 t01 in
     (env1, n1, Printf.sprintf "(%s -> %s)" s0 s1)

let rec pp_exp env n e =
  match e.it with
  | Var x0 ->
     (env, n, x0)
  | Lit v0 -> begin
     match v0.it with
     | Int  m0 -> (env, n, string_of_int m0)
     | Bool b0 -> (env, n, string_of_bool b0)
     | Unit    -> (env, n, "()")
    end
  | Fun ((x0, t0), e0) ->
     let (env0, n0, s0) = pp_tpe env n t0 in
     let (env1, n1, s1) = pp_exp env0 n0 e0 in
     (env1, n1, Printf.sprintf "(fun (%s : %s) -> %s)" x0 s0 s1)
  | Let ((x0, t0), e0, e1) ->
     let (env0, n0, s0) = pp_tpe env n t0 in
     let (env1, n1, s1) = pp_exp env0 n0 e0 in
     let (env2, n2, s2) = pp_exp env1 n1 e1 in
     (env2, n2, Printf.sprintf "let %s : %s = %s in %s" x0 s0 s1 s2)
  | Syntax.LetRec ((x0, t0), xts0, e0, e1) ->
     let (env0, n0, s0) = pp_tpe env n t0 in
     let (env1, n1, s1) = List.fold_right begin fun (x, t) -> fun (env, n, s) ->
         let (env', n', s') = pp_tpe env n t in
         (env', n', Printf.sprintf "(%s : %s) %s" x s' s)
     end xts0 (env0, n0, "") in
     let (env2, n2, s2) = pp_exp env1 n1 e0 in
     let (env3, n3, s3) = pp_exp env2 n2 e1 in
     (env3, n3, Printf.sprintf "let rec %s %s : %s = %s in %s" x0 s1 s0 s2 s3)
  | Syntax.If (e0, e1, e2) ->
     let (env0, n0, s0) = pp_exp env n e0 in
     let (env1, n1, s1) = pp_exp env0 n0 e1 in
     let (env2, n2, s2) = pp_exp env1 n1 e2 in
     (env2, n2, Printf.sprintf "(if %s then %s else %s)" s0 s1 s2) 
  | Syntax.App (e0, e1) ->
     let (env0, n0, s0) = pp_exp env n e0 in
     let (env1, n1, s1) = pp_exp env0 n0 e1 in
     (env1, n1, Printf.sprintf "(%s %s)" s0 s1)
  | Syntax.Add (e0, e1) ->
     let (env0, n0, s0) = pp_exp env n e0 in
     let (env1, n1, s1) = pp_exp env0 n0 e1 in
     (env1, n1, Printf.sprintf "(%s + %s)" s0 s1)
  | Syntax.Sub (e0, e1) ->
     let (env0, n0, s0) = pp_exp env n e0 in
     let (env1, n1, s1) = pp_exp env0 n0 e1 in
     (env1, n1, Printf.sprintf "(%s - %s)" s0 s1)
  | Syntax.Mul (e0, e1) ->
     let (env0, n0, s0) = pp_exp env n e0 in
     let (env1, n1, s1) = pp_exp env0 n0 e1 in
     (env1, n1, Printf.sprintf "(%s * %s)" s0 s1)
  | Syntax.Div (e0, e1) ->
     let (env0, n0, s0) = pp_exp env n e0 in
     let (env1, n1, s1) = pp_exp env0 n0 e1 in
     (env1, n1, Printf.sprintf "(%s / %s)" s0 s1)
  | Syntax.Eq (e0, e1) ->
     let (env0, n0, s0) = pp_exp env n e0 in
     let (env1, n1, s1) = pp_exp env0 n0 e1 in
     (env1, n1, Printf.sprintf "(%s = %s)" s0 s1)
  | Syntax.Ne (e0, e1) ->
     let (env0, n0, s0) = pp_exp env n e0 in
     let (env1, n1, s1) = pp_exp env0 n0 e1 in
     (env1, n1, Printf.sprintf "(%s <> %s)" s0 s1)
  | Syntax.Gt (e0, e1) ->
     let (env0, n0, s0) = pp_exp env n e0 in
     let (env1, n1, s1) = pp_exp env0 n0 e1 in
     (env1, n1, Printf.sprintf "(%s > %s)" s0 s1)
  | Syntax.Le (e0, e1) ->
     let (env0, n0, s0) = pp_exp env n e0 in
     let (env1, n1, s1) = pp_exp env0 n0 e1 in
     (env1, n1, Printf.sprintf "(%s < %s)" s0 s1)
  | Syntax.Neg e0 ->
     let (env0, n0, s0) = pp_exp env n e0 in
     (env0, n0, Printf.sprintf "(-%s)" s0)
  | Syntax.Not e0 ->
     let (env0, n0, s0) = pp_exp env n e0 in
     (env0, n0, Printf.sprintf "(not %s)" s0)

let pp_tpe t = let (_, _, s) = pp_tpe Env.empty 0 t in s
let pp_exp e = let (_, _, s) = pp_exp Env.empty 0 e in s
