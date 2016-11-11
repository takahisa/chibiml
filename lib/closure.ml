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
open Source.Position
open Core

module S = Set.Make (struct
  type t = var
  let compare = (Pervasives.(-))
end)

let rec fv = function
  | Var x0 -> S.singleton x0
  | Lit _  -> S.empty
  | Add (e0, e1) | Sub (e0, e1)
  | Mul (e0, e1) | Div (e0, e1)
  | Gt (e0, e1) | Le (e0, e1)
  | Eq (e0, e1) | Ne (e0, e1) ->
    S.union (fv e0) (fv e1)
  | Not e0 | Neg e0 ->
    fv e0
  | If (e0, e1, e2) ->
    List.fold_right S.union (List.map fv [e0; e1; e2]) S.empty
  | App (x0, e0) | AppClosure (x0, e0) ->
    S.union (S.singleton x0) (fv e0)
  | Let (x0, e0, e1) ->
    S.union (fv e0) (S.remove x0 (fv e1))
  | LetClosure (x0, Closure (_, xs0), e1) ->
    S.diff (fv e1) (S.of_list (x0 :: xs0))

let toplevel : def list ref =
  ref []

let rec f known = function
  | Mnf.LetRec (x0, xs0, e0, e1) ->
    let toplevel' = !toplevel in
    let known' = S.add x0 known in
    let known' = 
      if S.is_empty (S.diff (fv (f known' e0)) (S.of_list xs0)) then
        (toplevel := toplevel'; known')
      else
        (toplevel := toplevel'; known)
    in
    let e0' = f known' e0 in
    let e1' = f known' e1 in
    let xs1 = S.elements (S.diff (fv e0') (S.of_list xs0)) in
    toplevel := LetRec (x0, xs0, xs1, e0') :: !toplevel;
    if (S.mem x0 (fv e1')) then 
      LetClosure (x0, Closure (x0, xs1), e1') 
    else
      e1'
  | Mnf.Let (x0, c0, e0) ->
    Let (x0, g known c0, f known e0)
  | Mnf.Ret v0 ->
    h known v0

and g known = function
  | Mnf.Term v0 -> 
    h known v0
  | Mnf.If (v0, e0, e1) ->
    If (h known v0, f known e0, f known e1)
  | Mnf.App (Mnf.Var x0, v1) when S.mem x0 known ->
    App (x0, h known v1)
  | Mnf.App (Mnf.Var x0, v1) ->
    AppClosure (x0, h known v1)
  | Mnf.App (v0, v1) ->
    let x0 = Fresh.f () in
    let x1 = Fresh.f () in
    f known (Mnf.Let (x0, Mnf.Term (v0),
            (Mnf.Let (x1, Mnf.App (Mnf.Var x0, v1),
             Mnf.Ret (Mnf.Var x1)))))
  | Mnf.Add (v0, v1) ->
    Add (h known v0, h known v1)
  | Mnf.Sub (v0, v1) ->
    Sub (h known v0, h known v1)
  | Mnf.Mul (v0, v1) ->
    Mul (h known v0, h known v1)
  | Mnf.Div (v0, v1) ->
    Div (h known v0, h known v1)
  | Mnf.Eq (v0, v1) ->
    Eq (h known v0, h known v1)
  | Mnf.Ne (v0, v1) ->
    Eq (h known v0, h known v1)
  | Mnf.Gt (v0, v1) ->
    Gt (h known v0, h known v1)
  | Mnf.Le (v0, v1) ->
    Le (h known v0, h known v1)
  | Mnf.Not v0 ->
    Not (h known v0)
  | Mnf.Neg v0 ->
    Neg (h known v0)

and h known = function
  | Mnf.Var x0 ->
    Var x0
  | Mnf.Int n0 ->
    Lit (Int n0)
  | Mnf.Bool b0 ->
    Lit (Bool b0)
  | Mnf.Unit ->
    Lit Unit
  | Mnf.Fun (x1, e0) ->
    let x0 = Fresh.f () in
    f known (Mnf.LetRec (x0, [x1], e0, Mnf.Ret (Mnf.Var x0)))
    
let f e =
  (toplevel := [];
   let e' = f S.empty e in
   let toplevel' = !toplevel in
   (List.rev toplevel', e'))
