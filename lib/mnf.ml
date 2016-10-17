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

type t =
  | Fix    of var * t * t
  | Let    of var * u * t
  | Ret    of v

 and u =
   | Val   of v
   | If    of v * t * t
   | App   of v * v 
   | Add   of v * v
   | Sub   of v * v
   | Mul   of v * v
   | Div   of v * v
   | Eq    of v * v
   | Ne    of v * v
   | Gt    of v * v
   | Le    of v * v
   | Not   of v
   | Neg   of v

  and v =
    | Var  of var
    | Int  of int
    | Bool of bool
    | Unit
    | Fun  of var * t

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
  | Alpha.LetRec ((y0, _), [], e0, e1) ->
     Fix (y0, f e0 ret, f e1 ret)
  | Alpha.LetRec (yt0, yts0, e0, e1) ->
     let e0' = List.fold_left begin fun e -> fun yt -> 
       Alpha.Fun (yt, e) @@@ nowhere
     end e0 (List.rev yts0) in
     f (Alpha.LetRec (yt0, [], e0', e1) @@@ nowhere) k
  | Alpha.Let ((y0, _), e0, e1) ->
     f e0 (fun v0 ->
      Let (y0, Val v0, f e1 ret))
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
