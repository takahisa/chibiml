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
type exp  = exp' fragment
and exp' =
  | Var    of var
  | Int    of int
  | Bool   of bool
  | Unit
  | LetRec of (var * tpe) * (var * tpe) list * exp * exp
  | Let    of (var * tpe) * exp * exp
  | Fun    of (var * tpe) * exp
  | App    of exp * exp
  | Add    of exp * exp
  | Sub    of exp * exp
  | Mul    of exp * exp
  | Div    of exp * exp
  | Eq     of exp * exp
  | Ne     of exp * exp
  | Gt     of exp * exp
  | GtEq   of exp * exp
  | Le     of exp * exp
  | LeEq   of exp * exp
  | If     of exp * exp * exp
  | Not    of exp
  | Neg    of exp
and tpe  = tpe' fragment
and tpe' =
  | TyFun of tpe * tpe
  | TyVar of var
  | TyInt
  | TyBool
  | TyUnit

let rec pp_tpe_var n =
  if n <= 25 then
    Printf.sprintf "'%c" (Char.chr (Char.code 'a' + n))
  else
    pp_tpe_var (n mod 26) ^ string_of_int (n / 26)

let rec pp_tpe env n t =
  match t.it with
  | TyFun (t00, t01) ->
    let (env0, n0, s0) = pp_tpe env n t00 in
    let (env1, n1, s1) = pp_tpe env0 n0 t01 in
    (env1, n1, Printf.sprintf "(%s -> %s)" s0 s1)
  | TyVar x0 when Env.mem x0 env ->
    (env, n, pp_tpe_var (Env.lookup x0 env))
  | TyVar x0 ->
    let env0 = Env.extend x0 n env in
    (env0, n + 1, pp_tpe_var n)
  | TyInt ->
    (env, n, "int")
  | TyBool ->
    (env, n, "bool")
  | TyUnit ->
    (env, n, "unit")

let rec pp_exp env n e =
  match e.it with
  | Var x0 ->
    (env, n, "x" ^ string_of_int x0)
  | Int  m0 ->
    (env, n, string_of_int m0)
  | Bool b0 ->
    (env, n, string_of_bool b0)
  | Unit ->
    (env, n, "()")
  | LetRec ((x0, t0), xts0, e0, e1) ->
    let (env0, n0, s0) = pp_tpe env n t0 in
    let (env1, n1, s1) = List.fold_right begin fun (x, t) -> fun (env, n, s) ->
        let (env', n', s') = pp_tpe env n t in
        (env', n', Printf.sprintf "(x%d : %s) %s" x s' s)
      end xts0 (env0, n0, "") in
    let (env2, n2, s2) = pp_exp env1 n1 e0 in
    let (env3, n3, s3) = pp_exp env2 n2 e1 in
    (env3, n3, Printf.sprintf "let rec x%d %s : %s = %s in %s" x0 s1 s0 s2 s3)
  | Let ((x0, t0), e0, e1) ->
    let (env0, n0, s0) = pp_tpe env n t0 in
    let (env1, n1, s1) = pp_exp env0 n0 e0 in
    let (env2, n2, s2) = pp_exp env1 n1 e1 in
    (env2, n2, Printf.sprintf "let x%d : %s = %s in %s" x0 s0 s1 s2)
  | Fun ((x0, t0), e0) ->
    let (env0, n0, s0) = pp_tpe env n t0 in
    let (env1, n1, s1) = pp_exp env0 n0 e0 in
    (env1, n1, Printf.sprintf "(fun (x%d : %s) -> %s)" x0 s0 s1)
  | App (e0, e1) ->
    let (env0, n0, s0) = pp_exp env n e0 in
    let (env1, n1, s1) = pp_exp env0 n0 e1 in
    (env1, n1, Printf.sprintf "(%s %s)" s0 s1)
  | Add (e0, e1) ->
    let (env0, n0, s0) = pp_exp env n e0 in
    let (env1, n1, s1) = pp_exp env0 n0 e1 in
    (env1, n1, Printf.sprintf "(%s + %s)" s0 s1)
  | Sub (e0, e1) ->
    let (env0, n0, s0) = pp_exp env n e0 in
    let (env1, n1, s1) = pp_exp env0 n0 e1 in
    (env1, n1, Printf.sprintf "(%s - %s)" s0 s1)
  | Mul (e0, e1) ->
    let (env0, n0, s0) = pp_exp env n e0 in
    let (env1, n1, s1) = pp_exp env0 n0 e1 in
    (env1, n1, Printf.sprintf "(%s * %s)" s0 s1)
  | Div (e0, e1) ->
    let (env0, n0, s0) = pp_exp env n e0 in
    let (env1, n1, s1) = pp_exp env0 n0 e1 in
    (env1, n1, Printf.sprintf "(%s / %s)" s0 s1)
  | Eq (e0, e1) ->
    let (env0, n0, s0) = pp_exp env n e0 in
    let (env1, n1, s1) = pp_exp env0 n0 e1 in
    (env1, n1, Printf.sprintf "(%s = %s)" s0 s1)
  | Ne (e0, e1) ->
    let (env0, n0, s0) = pp_exp env n e0 in
    let (env1, n1, s1) = pp_exp env0 n0 e1 in
    (env1, n1, Printf.sprintf "(%s <> %s)" s0 s1)
  | Gt (e0, e1) ->
    let (env0, n0, s0) = pp_exp env n e0 in
    let (env1, n1, s1) = pp_exp env0 n0 e1 in
    (env1, n1, Printf.sprintf "(%s > %s)" s0 s1)
  | GtEq (e0, e1) ->
    let (env0, n0, s0) = pp_exp env n e0 in
    let (env1, n1, s1) = pp_exp env0 n0 e1 in
    (env1, n1, Printf.sprintf "(%s >= %s)" s0 s1)
  | Le (e0, e1) ->
    let (env0, n0, s0) = pp_exp env n e0 in
    let (env1, n1, s1) = pp_exp env0 n0 e1 in
    (env1, n1, Printf.sprintf "(%s < %s)" s0 s1)
  | LeEq (e0, e1) ->
    let (env0, n0, s0) = pp_exp env n e0 in
    let (env1, n1, s1) = pp_exp env0 n0 e1 in
    (env1, n1, Printf.sprintf "(%s <= %s)" s0 s1)
  | If (e0, e1, e2) ->
    let (env0, n0, s0) = pp_exp env n e0 in
    let (env1, n1, s1) = pp_exp env0 n0 e1 in
    let (env2, n2, s2) = pp_exp env1 n1 e2 in
    (env2, n2, Printf.sprintf "(if %s then %s else %s)" s0 s1 s2)
  | Neg e0 ->
    let (env0, n0, s0) = pp_exp env n e0 in
    (env0, n0, Printf.sprintf "(-%s)" s0)
  | Not e0 ->
    let (env0, n0, s0) = pp_exp env n e0 in
    (env0, n0, Printf.sprintf "(not %s)" s0)

let pp_exp e = let (_, _, s) = pp_exp Env.empty 0 e in s
let pp_tpe t = let (_, _, s) = pp_tpe Env.empty 0 t in s

let rec rename_tpe env t =
  match t.it with
  | Syntax.TyFun (t00, t01) ->
    let (env0, t00') = rename_tpe env t00 in
    let (env1, t01') = rename_tpe env0 t01 in
    (env1, TyFun (t00', t01') @@@ t.at)
  | Syntax.TyVar x0 when Env.mem x0 env ->
    (env, TyVar (Env.lookup x0 env) @@@ t.at)
  | Syntax.TyVar x0 ->
    let x0' = Fresh.f () in
    (Env.extend x0 x0' env, TyVar x0' @@@ t.at)
  | Syntax.TyInt ->
    (env, TyInt @@@ t.at)
  | Syntax.TyBool ->
    (env, TyBool @@@ t.at)
  | Syntax.TyUnit ->
    (env, TyUnit @@@ t.at)
let rename_tpe t = snd @@ rename_tpe Env.empty t

let rec rename_exp env e =
  match e.it with
  | Syntax.Var x0 when Env.mem x0 env ->
    Var (Env.lookup x0 env) @@@ e.at
  | Syntax.Var x0 ->
    error ~message:(Printf.sprintf "unbound variable %s" x0) ~at:e.at
  | Syntax.Int n0 ->
    Int n0 @@@ e.at
  | Syntax.Bool b0 ->
    Bool b0 @@@ e.at
  | Syntax.Unit ->
    Unit @@@ e.at
  | Syntax.Fun ((x0, t0), e0) ->
    let x0' = Fresh.f () in
    let t0' = rename_tpe t0 in
    Fun ((x0', t0'), rename_exp (Env.extend x0 x0' env) e0) @@@ e.at
  | Syntax.LetRec ((x0, t0), xts0, e0, e1) ->
    let xts0' = List.map (fun (_, t) -> Fresh.f (), rename_tpe t) xts0 in
    let x0' = Fresh.f () in
    let t0' = rename_tpe t0 in
    let env0 = Env.extend x0 x0' env in
    let env1 = List.fold_right begin fun ((x, _), (x', _)) -> fun env ->
        Env.extend x x' env
      end (List.combine xts0 xts0') env0 in
    let e0' = rename_exp env1 e0 in
    let e1' = rename_exp env0 e1 in
    LetRec ((x0', t0'), xts0', e0', e1') @@@ e.at
  | Syntax.Let ((x0, t0), e0, e1) ->
    let x0' = Fresh.f () in
    let t0' = rename_tpe t0 in
    let e0' = rename_exp env e0 in
    let e1' = rename_exp (Env.extend x0 x0' env) e1 in
    Let ((x0', t0'), e0', e1') @@@ e.at
  | Syntax.If (e0, e1, e2) ->
    let e0' = rename_exp env e0 in
    let e1' = rename_exp env e1 in
    let e2' = rename_exp env e2 in
    If (e0', e1', e2') @@@ e.at
  | Syntax.App (e0, e1) ->
    let e0' = rename_exp env e0 in
    let e1' = rename_exp env e1 in
    App (e0', e1') @@@ e.at
  | Syntax.Add (e0, e1) ->
    let e0' = rename_exp env e0 in
    let e1' = rename_exp env e1 in
    Add (e0', e1') @@@ e.at
  | Syntax.Sub (e0, e1) ->
    let e0' = rename_exp env e0 in
    let e1' = rename_exp env e1 in
    Sub (e0', e1') @@@ e.at
  | Syntax.Mul (e0, e1) ->
    let e0' = rename_exp env e0 in
    let e1' = rename_exp env e1 in
    Mul (e0', e1') @@@ e.at
  | Syntax.Div (e0, e1) ->
    let e0' = rename_exp env e0 in
    let e1' = rename_exp env e1 in
    Div (e0', e1') @@@ e.at
  | Syntax.Eq (e0, e1) ->
    let e0' = rename_exp env e0 in
    let e1' = rename_exp env e1 in
    Eq (e0', e1') @@@ e.at
  | Syntax.Ne (e0, e1) ->
    let e0' = rename_exp env e0 in
    let e1' = rename_exp env e1 in
    Ne (e0', e1') @@@ e.at
  | Syntax.Gt (e0, e1) ->
    let e0' = rename_exp env e0 in
    let e1' = rename_exp env e1 in
    Gt (e0', e1') @@@ e.at
  | Syntax.GtEq (e0, e1) ->
    let e0' = rename_exp env e0 in
    let e1' = rename_exp env e1 in
    GtEq (e0', e1') @@@ e.at
  | Syntax.Le (e0, e1) ->
    let e0' = rename_exp env e0 in
    let e1' = rename_exp env e1 in
    Le (e0', e1') @@@ e.at
  | Syntax.LeEq (e0, e1) ->
    let e0' = rename_exp env e0 in
    let e1' = rename_exp env e1 in
    LeEq (e0', e1') @@@ e.at
  | Syntax.Not e0 ->
    Not (rename_exp env e0) @@@ e.at
  | Syntax.Neg e0 ->
    Neg (rename_exp env e0) @@@ e.at
let rename_exp e = rename_exp Env.empty e

let f e =
  rename_exp e
