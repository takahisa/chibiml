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
module R = Refcount

type var = Cps.var
type tpe = Cps.tpe
type exp =
  | Var    of var
  | Int    of int
  | Bool   of bool
  | Unit
  | Fun    of var * exp
  | LetRec of var * var list * exp * exp
  | Let    of var * exp * exp
  | If     of exp * exp * exp
  | App    of exp * exp
  | Add    of exp * exp
  | Sub    of exp * exp
  | Mul    of exp * exp
  | Div    of exp * exp
  | Gt     of exp * exp
  | Le     of exp * exp
  | Eq     of exp * exp
  | Ne     of exp * exp
  | Not    of exp
  | Neg    of exp

let rec f sub = function
  | R.LetRec ((x0, n0), xs0, _, e0, e1) when (!n0 = 0) ->
    f sub e1
  | R.LetRec ((x0, n0), xs0, _, e0, e1) ->
    LetRec (x0, List.map fst xs0, f sub e0, f sub e1)
  | R.If (v0, e0, e1) ->
    If (g sub v0, f sub e0, f sub e1)
  | R.App (v0, v1, R.Cont ((x0, n0), e0)) when (!n0 <= 1) ->
    f (Env.extend x0 (App (g sub v0, g sub v1)) sub) e0
  | R.Add (v0, v1, R.Cont ((x0, n0), e0)) when (!n0 <= 1) ->
    f (Env.extend x0 (Add (g sub v0, g sub v1)) sub) e0
  | R.Sub (v0, v1, R.Cont ((x0, n0), e0)) when (!n0 <= 1) ->
    f (Env.extend x0 (Sub (g sub v0, g sub v1)) sub) e0
  | R.Mul (v0, v1, R.Cont ((x0, n0), e0)) when (!n0 <= 1) ->
    f (Env.extend x0 (Mul (g sub v0, g sub v1)) sub) e0
  | R.Div (v0, v1, R.Cont ((x0, n0), e0)) when (!n0 <= 1) ->
    f (Env.extend x0 (Div (g sub v0, g sub v1)) sub) e0
  | R.Gt (v0, v1, R.Cont ((x0, n0), e0)) when (!n0 <= 1) ->
    f (Env.extend x0 (Gt (g sub v0, g sub v1)) sub) e0
  | R.Le (v0, v1, R.Cont ((x0, n0), e0)) when (!n0 <= 1) ->
    f (Env.extend x0 (Le (g sub v0, g sub v1)) sub) e0
  | R.Eq (v0, v1, R.Cont ((x0, n0), e0)) when (!n0 <= 1) ->
    f (Env.extend x0 (Eq (g sub v0, g sub v1)) sub) e0
  | R.Ne (v0, v1, R.Cont ((x0, n0), e0)) when (!n0 <= 1) ->
    f (Env.extend x0 (Ne (g sub v0, g sub v1)) sub) e0
  | R.Not (v0, R.Cont ((x0, n0), e0)) when (!n0 <= 1) ->
    f (Env.extend x0 (Not (g sub v0)) sub) e0
  | R.Neg (v0, R.Cont ((x0, n0), e0)) when (!n0 <= 1) ->
    f (Env.extend x0 (Neg (g sub v0)) sub) e0
  | R.App (v0, v1, R.Cont ((x0, _), e0)) ->
    Let (x0, App (g sub v0, g sub v1), f sub e0)
  | R.Add (v0, v1, R.Cont ((x0, _), e0)) ->
    Let (x0, Add (g sub v0, g sub v1), f sub e0)
  | R.Sub (v0, v1, R.Cont ((x0, _), e0)) ->
    Let (x0, Sub (g sub v0, g sub v1), f sub e0)
  | R.Mul (v0, v1, R.Cont ((x0, _), e0)) ->
    Let (x0, Mul (g sub v0, g sub v1), f sub e0)
  | R.Div (v0, v1, R.Cont ((x0, _), e0)) ->
    Let (x0, Div (g sub v0, g sub v1), f sub e0)
  | R.Gt (v0, v1, R.Cont ((x0, _), e0)) ->
    Let (x0, Gt (g sub v0, g sub v1), f sub e0)
  | R.Le (v0, v1, R.Cont ((x0, _), e0)) ->
    Let (x0, Le (g sub v0, g sub v1), f sub e0)
  | R.Eq (v0, v1, R.Cont ((x0, _), e0)) ->
    Let (x0, Eq (g sub v0, g sub v1), f sub e0)
  | R.Ne (v0, v1, R.Cont ((x0, _), e0)) ->
    Let (x0, Ne (g sub v0, g sub v1), f sub e0)
  | R.Not (v0, R.Cont ((x0, _), e0)) ->
    Let (x0, Not (g sub v0), f sub e0)
  | R.Neg (v0, R.Cont ((x0, _), e0)) ->
    Let (x0, Neg (g sub v0), f sub e0)
  | R.Ret (_, v0) ->
    g sub v0

and g sub = function
  | R.Fun ((x0, _), _, e0) ->
    Fun (x0, f sub e0)
  | R.Var (x0, _) when Env.mem x0 sub ->
    Env.lookup x0 sub
  | R.Var (x0, _) ->
    Var x0
  | R.Int n0 ->
    Int n0
  | R.Bool b0 ->
    Bool b0
  | R.Unit ->
    Unit

let f cont =
  let (R.Cont (_, e0)) = (R.f cont) in
  f Env.empty e0
