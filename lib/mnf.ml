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

type var = int
type exp =
  | LetRec of var * var list * exp * exp
  | Let    of var * comp * exp
  | Ret    of term
(* serious-term; i.e. computations *)
 and comp =
   | Term  of term
   | If    of term * exp * exp
   | App   of term * term 
   | Add   of term * term
   | Sub   of term * term
   | Mul   of term * term
   | Div   of term * term
   | Eq    of term * term
   | Ne    of term * term
   | Gt    of term * term
   | Le    of term * term
   | Not   of term
   | Neg   of term
(* trivial-term; i.e. values *)
 and term =
   | Var   of var
   | Int   of int
   | Bool  of bool
   | Unit
   | Fun   of var * exp

let ret v =
  Ret v

let rec f e k =
  match e.it with
  | Alpha.Var x0 ->
     k @@ Var x0
  | Alpha.Lit l0 -> begin
      match l0.it with
      | Alpha.Int n0  -> k @@ Int n0
      | Alpha.Bool b0 -> k @@ Bool b0
      | Alpha.Unit    -> k @@ Unit
    end
  | Alpha.If (e0, e1, e2) ->
     let y0 = Fresh.f () in
     f e0 (fun v0 ->
       Let (y0, If (v0, f e1 ret, f e2 ret), k (Var y0)))
  | Alpha.LetRec ((y0, _), yts0, e0, e1) ->
     let e0' = f e0 ret in
     let e1' = f e1 k in
     LetRec (y0, List.map fst yts0, e0', e1')
  | Alpha.Let ((y0, _), e0, e1) ->
     f e0 (fun v0 ->
      Let (y0, Term v0, f e1 k))
  | Alpha.Fun ((y0, _), e0) ->
     k @@ Fun (y0, f e0 ret)
  | Alpha.App (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let y0 = Fresh.f () in
        Let (y0, App (v0, v1), k (Var y0))))
  | Alpha.Add (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let y0 = Fresh.f () in
        Let (y0, Add (v0, v1), k (Var y0))))
  | Alpha.Sub (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let y0 = Fresh.f () in
        Let (y0, Sub (v0, v1), k (Var y0))))
  | Alpha.Mul (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let y0 = Fresh.f () in
        Let (y0, Mul (v0, v1), k (Var y0))))
  | Alpha.Div (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let y0 = Fresh.f () in
        Let (y0, Div (v0, v1), k (Var y0))))
  | Alpha.Eq (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let y0 = Fresh.f () in
        Let (y0, Eq (v0, v1), k (Var y0))))
  | Alpha.Ne (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let y0 = Fresh.f () in
        Let (y0, Ne (v0, v1), k (Var y0))))
  | Alpha.Gt (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let y0 = Fresh.f () in
        Let (y0, Gt (v0, v1), k (Var y0))))
  | Alpha.Le (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let y0 = Fresh.f () in
        Let (y0, Le (v0, v1), k (Var y0))))
  | Alpha.Not e0 ->
     let y0 = Fresh.f () in
     f e0 (fun v0 ->
        Let (y0, Not v0, k (Var y0)))
  | Alpha.Neg e0 ->
     let y0 = Fresh.f () in
     f e0 (fun v0 ->
        Let (y0, Neg v0, k (Var y0)))
let f e = f e ret
