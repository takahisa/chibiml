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
type var = Cps.var * int ref
type tpe = Cps.tpe
type exp =
  | LetRec of var * var list * var * exp * exp
  | Let    of var * cont * exp
  | If     of term * exp * exp
  | App    of term * term * cont
  | Add    of term * term * cont
  | Sub    of term * term * cont
  | Mul    of term * term * cont
  | Div    of term * term * cont
  | Gt     of term * term * cont
  | Le     of term * term * cont
  | Eq     of term * term * cont
  | Ne     of term * term * cont
  | Not    of term * cont
  | Neg    of term * cont
  | Ret    of var * term
and term =
  | Fun    of var * var * exp
  | Var    of var
  | Int    of int
  | Bool   of bool
  | Unit
and cont =
  | Cont   of var * exp

let counter x =
  (x, ref 0)

let rec f env = function
  | Cps.LetRec (x0, xs0, x1, e0, e1) ->
    let x0' = counter x0 in
    let x1' = counter x1 in
    let xs0' = List.map counter xs0 in
    let env0 = Env.extend x0 x0' env in
    let env1 = List.fold_right begin fun (x, n) -> fun env ->
        Env.extend x (x, n) env
      end (xs0' @ [x1']) env0 in
    let e0' = f env1 e0 in
    let e1' = f env0 e1 in
    LetRec (x0', xs0', x1', e0', e1')
  | Cps.Let (x0, Cps.Cont (x1, e0), e1) ->
    let x0' = counter x0 in
    let x1' = counter x1 in
    let e0' = f (Env.extend x1 x1' env) e0 in
    let e1' = f (Env.extend x0 x0' env) e1 in
    Let (x0', Cont (x1', e0'), e1')
  | Cps.If (v0, e0, e1) ->
    let v0' = g env v0 in
    let e0' = f env e0 in
    let e1' = f env e1 in
    If (v0', e0', e1')
  | Cps.App (v0, v1, Cps.Cont (x0, e0)) ->
    let v0' = g env v0 in
    let v1' = g env v1 in
    let x0' = counter x0 in
    let e0' = f (Env.extend x0 x0' env) e0 in
    App (v0', v1', Cont (x0', e0'))
  | Cps.Add (v0, v1, Cps.Cont (x0, e0)) ->
    let v0' = g env v0 in
    let v1' = g env v1 in
    let x0' = counter x0 in
    let e0' = f (Env.extend x0 x0' env) e0 in
    Add (v0', v1', Cont (x0', e0'))
  | Cps.Sub (v0, v1, Cps.Cont (x0, e0)) ->
    let v0' = g env v0 in
    let v1' = g env v1 in
    let x0' = counter x0 in
    let e0' = f (Env.extend x0 x0' env) e0 in
    Sub (v0', v1', Cont (x0', e0'))
  | Cps.Mul (v0, v1, Cps.Cont (x0, e0)) ->
    let v0' = g env v0 in
    let v1' = g env v1 in
    let x0' = counter x0 in
    let e0' = f (Env.extend x0 x0' env) e0 in
    Mul (v0', v1', Cont (x0', e0'))
  | Cps.Div (v0, v1, Cps.Cont (x0, e0)) ->
    let v0' = g env v0 in
    let v1' = g env v1 in
    let x0' = counter x0 in
    let e0' = f (Env.extend x0 x0' env) e0 in
    Div (v0', v1', Cont (x0', e0'))
  | Cps.Eq (v0, v1, Cps.Cont (x0, e0)) ->
    let v0' = g env v0 in
    let v1' = g env v1 in
    let x0' = counter x0 in
    let e0' = f (Env.extend x0 x0' env) e0 in
    Eq (v0', v1', Cont (x0', e0'))
  | Cps.Ne (v0, v1, Cps.Cont (x0, e0)) ->
    let v0' = g env v0 in
    let v1' = g env v1 in
    let x0' = counter x0 in
    let e0' = f (Env.extend x0 x0' env) e0 in
    Ne (v0', v1', Cont (x0', e0'))
  | Cps.Gt (v0, v1, Cps.Cont (x0, e0)) ->
    let v0' = g env v0 in
    let v1' = g env v1 in
    let x0' = counter x0 in
    let e0' = f (Env.extend x0 x0' env) e0 in
    Gt (v0', v1', Cont (x0', e0'))
  | Cps.Le (v0, v1, Cps.Cont (x0, e0)) ->
    let v0' = g env v0 in
    let v1' = g env v1 in
    let x0' = counter x0 in
    let e0' = f (Env.extend x0 x0' env) e0 in
    Le (v0', v1', Cont (x0', e0'))
  | Cps.Not (v0, Cps.Cont (x0, e0)) ->
    let v0' = g env v0 in
    let x0' = counter x0 in
    let e0' = f (Env.extend x0 x0' env) e0 in
    Not (v0', Cont (x0', e0'))
  | Cps.Neg (v0, Cps.Cont (x0, e0)) ->
    let v0' = g env v0 in
    let x0' = counter x0 in
    let e0' = f (Env.extend x0 x0' env) e0 in
    Neg (v0', Cont (x0', e0'))
  | Cps.Ret (x0, v0) ->
    let (_, n0) = Env.lookup x0 env in
    incr n0;
    let x0' = (x0, n0) in
    let v0' = g env v0 in
    Ret (x0', v0')

and g env = function
  | Cps.Fun (x0, x1, e0) ->
    let x0' = counter x0 in
    let x1' = counter x1 in
    let env0 = Env.extend x0 x0' env in
    let env1 = Env.extend x1 x1' env0 in
    let e0' = f env1 e0 in
    Fun (x0', x1', e0')
  | Cps.Var x0 ->
    let (_, n0) = Env.lookup x0 env in
    incr n0; Var (x0, n0)
  | Cps.Int n0 ->
    Int n0
  | Cps.Bool b0 ->
    Bool b0
  | Cps.Unit ->
    Unit

let f (Cps.Cont (x0, e0)) =
  let x0' = counter x0 in
  Cont (x0', f (Env.singleton x0 x0') e0)
