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
open Type

type var  = int
type exp  = exp' fragment
 and exp' =
   | Var    of var
   | Lit    of lit
   | Fun    of (var * tpe) * exp
   | Let    of (var * tpe) * exp * exp 
   | LetRec of (var * tpe) * (var * tpe) list * exp * exp
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

 and tpe  = Type.tpe
 and tpe' = Type.tpe'

 and lit  = lit' fragment
 and lit' =
   | Int   of int
   | Bool  of bool
   | Unit

let rec f env e =
  match e.it with
  | Syntax.Var x0 when Env.mem x0 env ->
     Var (Env.lookup x0 env) @@@ e.at
  | Syntax.Var x0 ->
     error (Printf.sprintf "unbound variable %s" x0) e.at
  | Syntax.Lit l0 -> begin
      match l0.it with
      | Syntax.Int  n0  -> Lit (Int n0 @@@ l0.at) @@@ e.at
      | Syntax.Bool b0  -> Lit (Bool b0 @@@ l0.at) @@@ e.at
      | Syntax.Unit     -> Lit (Unit @@@ l0.at) @@@ e.at
    end
  | Syntax.Fun ((x0, t0), e0) ->
     let y0 = Fresh.f () in
     Fun ((y0, t0), f (Env.extend x0 y0 env) e0) @@@ e.at
  | Syntax.LetRec ((x0, t0), xts0, e0, e1) ->
     let yts0 = List.map (fun (_, t) -> Fresh.f (), t) xts0 in
     let y0 = Fresh.f () in
     let env0 = Env.extend x0 y0 env in
     let env1 = List.fold_right begin fun ((x, _), (y, _)) -> fun env ->
       Env.extend x y env
     end (List.combine xts0 yts0) env0 in
     let e0' = f env1 e0 in
     let e1' = f env0 e1 in
     LetRec ((y0, t0), yts0, e0', e1') @@@ e.at
  | Syntax.Let ((x0, t0), e0, e1) ->
     let y0 = Fresh.f () in
     let e0' = f env e0 in
     let e1' = f (Env.extend x0 y0 env) e1 in
     Let ((y0, t0), e0', e1') @@@ e.at
  | Syntax.If (e0, e1, e2) ->
     let e0' = f env e0 in
     let e1' = f env e1 in
     let e2' = f env e2 in
     If (e0', e1', e2') @@@ e.at
  | Syntax.App (e0, e1) ->
     let e0' = f env e0 in
     let e1' = f env e1 in
     App (e0', e1') @@@ e.at
  | Syntax.Add (e0, e1) ->
     let e0' = f env e0 in
     let e1' = f env e1 in
     Add (e0', e1') @@@ e.at
  | Syntax.Sub (e0, e1) ->
     let e0' = f env e0 in
     let e1' = f env e1 in
     Sub (e0', e1') @@@ e.at
  | Syntax.Mul (e0, e1) ->
     let e0' = f env e0 in
     let e1' = f env e1 in
     Mul (e0', e1') @@@ e.at
  | Syntax.Div (e0, e1) ->
     let e0' = f env e0 in
     let e1' = f env e1 in
     Div (e0', e1') @@@ e.at
  | Syntax.Eq (e0, e1) ->
     let e0' = f env e0 in
     let e1' = f env e1 in
     Eq (e0', e1') @@@ e.at
  | Syntax.Ne (e0, e1) ->
     let e0' = f env e0 in
     let e1' = f env e1 in
     Ne (e0', e1') @@@ e.at
  | Syntax.Gt (e0, e1) ->
     let e0' = f env e0 in
     let e1' = f env e1 in
     Gt (e0', e1') @@@ e.at
  | Syntax.Le (e0, e1) ->
     let e0' = f env e0 in
     let e1' = f env e1 in
     Le (e0', e1') @@@ e.at
  | Syntax.Not e0 ->
     Not (f env e0) @@@ e.at
  | Syntax.Neg e0 ->
     Neg (f env e0) @@@ e.at

let f = f Env.empty
