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
  | Var    of var
  | If     of var * exp * exp
  | LetRec of var * var list * var * exp * exp
  | Let    of var * term * exp
  | App    of var * var * cont
  | Add    of var * var * cont
  | Sub    of var * var * cont
  | Mul    of var * var * cont
  | Div    of var * var * cont
  | Gt     of var * var * cont
  | Le     of var * var * cont 
  | Eq     of var * var * cont
  | Ne     of var * var * cont 
  | Not    of var * cont
  | Neg    of var * cont  
  | Ret    of var * var

and term =
  | Lit    of lit
  | Fun    of var * var * exp

and cont =
  | Cont   of var * exp

and lit =
  | Int    of int
  | Bool   of bool
  | Unit

let rec f env e (k: var) =
  match e.it with
  | Alpha.Var y0 when Env.mem y0 env ->
    Ret (k, Env.lookup y0 env)
  | Alpha.Var y0 -> 
    Ret (k, y0)
  | Alpha.Lit l0 -> begin
    match l0.it with
    | Alpha.Int  n0 -> let y0 = Fresh.f () in Let (y0, Lit (Int  n0), Ret (k, y0))
    | Alpha.Bool b0 -> let y0 = Fresh.f () in Let (y0, Lit (Bool b0), Ret (k, y0))
    | Alpha.Unit    -> let y0 = Fresh.f () in Let (y0, Lit Unit,      Ret (k, y0))
    end
  | Alpha.Fun ((y0, _), e0) ->
    let y1 = Fresh.f () in
    let y2 = Fresh.f () in
    Let (y2, Fun (y0, y1, f env e0 y1), Ret (k, y2))
  | Alpha.LetRec ((y0, _), yts0, e0, e1) ->
    let y1 = Fresh.f () in
    LetRec (y0, List.map fst yts0, y1, f env e0 y1, f env e1 k)
  | Alpha.Let ((y0, _), e0, e1) ->
    g env e0 (fun y1 ->
      f (Env.extend y0 y1 env) e1 k)
  | Alpha.If (e0, e1, e2) ->
    g env e0 (fun y0 ->
      If (y0, f env e1 k, f env e2 k))
  | Alpha.App (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in App (y0, y1, Cont (y2, Ret (k, y2)))))
  | Alpha.Add (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in Add (y0, y1, Cont (y2, Ret (k, y2)))))
  | Alpha.Sub (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in Sub (y0, y1, Cont (y2, Ret (k, y2)))))
  | Alpha.Mul (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in Mul (y0, y1, Cont (y2, Ret (k, y2)))))
  | Alpha.Div (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in Div (y0, y1, Cont (y2, Ret (k, y2)))))
  | Alpha.Gt (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in Gt (y0, y1, Cont (y2, Ret (k, y2)))))
  | Alpha.Le (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in Le (y0, y1, Cont (y2, Ret (k, y2)))))
  | Alpha.Eq (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in Eq (y0, y1, Cont (y2, Ret (k, y2)))))
  | Alpha.Ne (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in Ne (y0, y1, Cont (y2, Ret (k, y2)))))
  | Alpha.Not e0 ->
    g env e0 (fun y0 ->
      let y1 = Fresh.f () in Not (y0, Cont (y1, Ret (k, y1))))
  | Alpha.Neg e0 ->
    g env e0 (fun y0 ->
      let y1 = Fresh.f () in Neg (y0, Cont (y1, Ret (k, y1))))

and g env e (k: var -> exp) =
  match e.it with
  | Alpha.Var x0 ->
    k @@ x0
  | Alpha.Lit l0 -> begin
    match l0.it with
    | Alpha.Int  n0 -> let y0 = Fresh.f () in Let (y0, Lit (Int  n0), k @@ y0)
    | Alpha.Bool b0 -> let y0 = Fresh.f () in Let (y0, Lit (Bool b0), k @@ y0)
    | Alpha.Unit    -> let y0 = Fresh.f () in Let (y0, Lit Unit,      k @@ y0)
    end
  | Alpha.Fun ((y0, _), e0) ->
    let y1 = Fresh.f () in
    let y2 = Fresh.f () in
    Let (y2, Fun (y0, y1, f env e0 y1), k @@ y2)
  | Alpha.LetRec ((y0, _), yts0, e0, e1) ->
    let y1 = Fresh.f () in
    LetRec (y0, List.map fst yts0, y1, f env e0 y1, g env e1 k)
  | Alpha.Let ((y0, _), e0, e1) ->
    g env e0 (fun y1 ->
      g (Env.extend y0 y1 env) e1 k)
  | Alpha.If (e0, e1, e2) ->
    g env e0 (fun y0 ->
      If (y0, g env e1 k, g env e2 k))
  | Alpha.App (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in App (y0, y1, Cont (y2, k @@ y2))))
  | Alpha.Add (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in Add (y0, y1, Cont (y2, k @@ y2))))
  | Alpha.Sub (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in Sub (y0, y1, Cont (y2, k @@ y2))))
  | Alpha.Mul (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in Mul (y0, y1, Cont (y2, k @@ y2))))
  | Alpha.Div (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in Div (y0, y1, Cont (y2, k @@ y2))))
  | Alpha.Gt (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in Gt (y0, y1, Cont (y2, k @@ y2))))
  | Alpha.Le (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in Le (y0, y1, Cont (y2, k @@ y2))))
  | Alpha.Eq (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in Eq (y0, y1, Cont (y2, k @@ y2))))
  | Alpha.Ne (e0, e1) ->
    g env e0 (fun y0 ->
      g env e1 (fun y1 ->
        let y2 = Fresh.f () in Ne (y0, y1, Cont (y2, k @@ y2))))
  | Alpha.Not e0 ->
    g env e0 (fun y0 ->
      let y1 = Fresh.f () in Not (y0, Cont (y1, k @@ y1)))
  | Alpha.Neg e0 ->
    g env e0 (fun y0 ->
      let y1 = Fresh.f () in Neg (y0, Cont (y1, k @@ y1)))

let f e = g Env.empty e (fun y0 -> Var y0)
