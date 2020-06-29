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
open Untyped

module S = Set.Make
    (struct
      type t = var
      let compare = Stdlib.compare
     end)

let rec fv = function
  | LetRec (x0, x1, e0, e1) ->
    S.union (S.diff (fv e0) (S.of_list [x0; x1])) (S.remove x0 (fv e1))
  | Let (x0, e0, e1) ->
    S.union (fv e0) (S.remove x0 (fv e1))
  | If (e0, e1, e2) ->
    List.fold_right S.union (List.map fv [e0; e1; e2]) S.empty
  | Fun (x0, e0) ->
    S.remove x0 (fv e0)
  | App (e0, e1)
  | Add (e0, e1)
  | Sub (e0, e1)
  | Mul (e0, e1)
  | Div (e0, e1)
  | Gt (e0, e1)
  | Le (e0, e1)
  | Eq (e0, e1)
  | Ne (e0, e1) ->
    S.union (fv e0) (fv e1)
  | Not e0
  | Neg e0 ->
    fv e0
  | Var x0 ->
    S.singleton x0
  | _ ->
    S.empty

let rec f env = function
  | Let (x0, ((Int _) as e0), e1)
  | Let (x0, ((Bool _) as e0), e1)
  | Let (x0, ((Unit) as e0), e1) ->
    f (Env.extend x0 e0 env) e1
  | Let (x0, e0, e1) ->
    let e0' = f env e0 in
    let e1' = f env e1 in
    if (S.mem x0 (fv e1')) then Let (x0, e0', e1') else e1'
  | LetRec (x0, x1, e0, e1) ->
    let e0' = f env e0 in
    let e1' = f env e1 in
    LetRec (x0, x1, e0', e1')
  | If (e0, e1, e2) ->
    let e0' = f env e0 in
    let e1' = f env e1 in
    let e2' = f env e2 in
    If (e0', e1', e2')
  | Fun (x0, e0) ->
    let e0' = f env e0 in
    Fun (x0, e0')
  | App (e0, e1) ->
    let e0' = f env e0 in
    let e1' = f env e1 in
    App (e0', e1')
  | Add (e0, e1) ->
    let e0' = f env e0 in
    let e1' = f env e1 in
    Add (e0', e1')
  | Sub (e0, e1) ->
    let e0' = f env e0 in
    let e1' = f env e1 in
    Sub (e0', e1')
  | Mul (e0, e1) ->
    let e0' = f env e0 in
    let e1' = f env e1 in
    Mul (e0', e1')
  | Div (e0, e1) ->
    let e0' = f env e0 in
    let e1' = f env e1 in
    Div (e0', e1')
  | Gt (e0, e1) ->
    let e0' = f env e0 in
    let e1' = f env e1 in
    Gt (e0', e1')
  | Le (e0, e1) ->
    let e0' = f env e0 in
    let e1' = f env e1 in
    Le (e0', e1')
  | Eq (e0, e1) ->
    let e0' = f env e0 in
    let e1' = f env e1 in
    Eq (e0', e1')
  | Ne (e0, e1) ->
    let e0' = f env e0 in
    let e1' = f env e1 in
    Ne (e0', e1')
  | Not e0 ->
    let e0' = f env e0 in
    Not e0'
  | Neg e0 ->
    let e0' = f env e0 in
    Neg e0'
  | Var x0 when Env.mem x0 env ->
    f env (Env.lookup x0 env)
  | e0 -> e0

let f = f Env.empty
