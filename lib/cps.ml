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
  | LetRec of var * var list * var * exp * exp
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
  | Var    of var
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
    Ret (k, Var y0)
  | Alpha.Lit l0 -> begin
    match l0.it with
    | Alpha.Int  n0 -> Ret (k, Lit (Int n0))
    | Alpha.Bool b0 -> Ret (k, Lit (Bool b0))
    | Alpha.Unit    -> Ret (k, Lit (Unit))
    end
  | Alpha.Fun ((y0, _), e0) ->
    let y1 = Fresh.f () in
    Ret (k, Fun (y0, y1, f env e0 y1))
  | Alpha.LetRec ((y0, _), yts0, e0, e1) ->
    let y1 = Fresh.f () in
    LetRec (y0, List.map fst yts0, y1, f env e0 y1, f env e1 k)
  | Alpha.Let ((y0, _), e0, e1) ->
    g env e0 (fun v0 ->
      f (Env.extend y0 v0 env) e1 k)
  | Alpha.If (e0, e1, e2) ->
    g env e0 (fun v0 ->
      If (v0, f env e1 k, f env e2 k))
  | Alpha.App (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in App (v0, v1, Cont (y0, Ret (k, Var y0)))))
  | Alpha.Add (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in Add (v0, v1, Cont (y0, Ret (k, Var y0)))))
  | Alpha.Sub (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in Sub (v0, v1, Cont (y0, Ret (k, Var y0)))))
  | Alpha.Mul (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in Mul (v0, v1, Cont (y0, Ret (k, Var y0)))))
  | Alpha.Div (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in Div (v0, v1, Cont (y0, Ret (k, Var y0)))))
  | Alpha.Gt (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in Gt (v0, v1, Cont (y0, Ret (k, Var y0)))))
  | Alpha.Le (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in Le (v0, v1, Cont (y0, Ret (k, Var y0)))))
  | Alpha.Eq (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in Eq (v0, v1, Cont (y0, Ret (k, Var y0)))))
  | Alpha.Ne (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in Ne (v0, v1, Cont (y0, Ret (k, Var y0)))))
  | Alpha.Not e0 ->
    g env e0 (fun v0 ->
      let y0 = Fresh.f () in Not (v0, Cont (y0, Ret (k, Var y0))))
  | Alpha.Neg e0 ->
    g env e0 (fun v0 ->
      let y0 = Fresh.f () in Neg (v0, Cont (y0, Ret (k, Var y0))))

and g env e (k: term -> exp) =
  match e.it with
  | Alpha.Var y0 when Env.mem y0 env ->
    k @@ Env.lookup y0 env
  | Alpha.Var y0 ->
    k @@ Var y0
  | Alpha.Lit l0 -> begin
    match l0.it with
    | Alpha.Int  n0 -> k @@ Lit (Int n0)
    | Alpha.Bool b0 -> k @@ Lit (Bool b0)
    | Alpha.Unit    -> k @@ Lit Unit
    end
  | Alpha.Fun ((y0, _), e0) ->
    let y1 = Fresh.f () in
    k @@ Fun (y0, y1, f env e0 y1)
  | Alpha.LetRec ((y0, _), yts0, e0, e1) ->
    let y1 = Fresh.f () in
    LetRec (y0, List.map fst yts0, y1, f env e0 y1, g env e1 k)
  | Alpha.Let ((y0, _), e0, e1) ->
    g env e0 (fun v0 ->
      g (Env.extend y0 v0 env) e1 k)
  | Alpha.If (e0, e1, e2) ->
    g env e0 (fun v0 ->
      If (v0, g env e1 k, g env e2 k))
  | Alpha.App (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in App (v0, v1, Cont (y0, k @@ Var y0))))
  | Alpha.Add (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in Add (v0, v1, Cont (y0, k @@ Var y0))))
  | Alpha.Sub (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in Sub (v0, v1, Cont (y0, k @@ Var y0))))
  | Alpha.Mul (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in Mul (v0, v1, Cont (y0, k @@ Var y0))))
  | Alpha.Div (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in Div (v0, v1, Cont (y0, k @@ Var y0))))
  | Alpha.Gt (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in Gt (v0, v1, Cont (y0, k @@ Var y0))))
  | Alpha.Le (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in Le (v0, v1, Cont (y0, k @@ Var y0))))
  | Alpha.Eq (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in Eq (v0, v1, Cont (y0, k @@ Var y0))))
  | Alpha.Ne (e0, e1) ->
    g env e0 (fun v0 ->
      g env e1 (fun v1 ->
        let y0 = Fresh.f () in Ne (v0, v1, Cont (y0, k @@ Var y0))))
  | Alpha.Not e0 ->
    g env e0 (fun v0 ->
      let y0 = Fresh.f () in Not (v0, Cont (y0, k @@ Var y0)))
  | Alpha.Neg e0 ->
    g env e0 (fun v0 ->
      let y0 = Fresh.f () in Neg (v0, Cont (y0, k @@ Var y0)))

let f e = let k = Fresh.f () in Cont(k, f Env.empty e k)
