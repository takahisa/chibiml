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

type var = Alpha.var
type tpe = Type.t
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
  | Fun    of var * var * exp
  | Var    of var
  | Int    of int
  | Bool   of bool
  | Unit
and cont =
  | Cont   of var * exp

let rec f env e (k: var) =
  match e.it with
  | Alpha.Var x0 when Env.mem x0 env ->
     Ret (k, Env.lookup x0 env)
  | Alpha.Var x0 ->
     Ret (k, Var x0)
  | Alpha.Int n0 ->
     Ret (k, Int n0)
  | Alpha.Bool b0 ->
     Ret (k, Bool b0)
  | Alpha.Unit ->
     Ret (k, Unit)
  | Alpha.Fun ((x0, _), e0) ->
     let x1 = Fresh.f () in
     Ret (k, Fun (x0, x1, f env e0 x1))
  | Alpha.LetRec ((x0, _), xts0, e0, e1) ->
     let x1 = Fresh.f () in
     LetRec (x0, List.map fst xts0, x1, f env e0 x1, f env e1 k)
  | Alpha.Let ((x0, _), e0, e1) ->
     g env e0 (fun v0 ->
       f (Env.extend x0 v0 env) e1 k)
  | Alpha.If (e0, e1, e2) ->
     g env e0 (fun v0 ->
       If (v0, f env e1 k, f env e2 k))
  | Alpha.App (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in App (v0, v1, Cont (x0, Ret (k, Var x0)))))
  | Alpha.Add (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in Add (v0, v1, Cont (x0, Ret (k, Var x0)))))
  | Alpha.Sub (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in Sub (v0, v1, Cont (x0, Ret (k, Var x0)))))
  | Alpha.Mul (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in Mul (v0, v1, Cont (x0, Ret (k, Var x0)))))
  | Alpha.Div (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in Div (v0, v1, Cont (x0, Ret (k, Var x0)))))
  | Alpha.Gt (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in Gt (v0, v1, Cont (x0, Ret (k, Var x0)))))
  | Alpha.Le (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in Le (v0, v1, Cont (x0, Ret (k, Var x0)))))
  | Alpha.Eq (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in Eq (v0, v1, Cont (x0, Ret (k, Var x0)))))
  | Alpha.Ne (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in Ne (v0, v1, Cont (x0, Ret (k, Var x0)))))
  | Alpha.Not e0 ->
     g env e0 (fun v0 ->
       let x0 = Fresh.f () in Not (v0, Cont (x0, Ret (k, Var x0))))
  | Alpha.Neg e0 ->
     g env e0 (fun v0 ->
       let x0 = Fresh.f () in Neg (v0, Cont (x0, Ret (k, Var x0))))
  | Alpha.GtEq (e0, e1) ->
     f env (Alpha.Not (Alpha.Le (e0, e1) @@@ nowhere) @@@ nowhere) k
  | Alpha.LeEq (e0, e1) ->
     f env (Alpha.Not (Alpha.Gt (e0, e1) @@@ nowhere) @@@ nowhere) k


and g env e (k: term -> exp) =
  match e.it with
  | Alpha.Var x0 when Env.mem x0 env ->
     k @@ Env.lookup x0 env
  | Alpha.Var x0 ->
     k @@ Var x0
  | Alpha.Int n0 ->
     k @@ Int n0
  | Alpha.Bool b0 ->
     k @@ Bool b0
  | Alpha.Unit ->
     k @@ Unit
  | Alpha.Fun ((x0, _), e0) ->
     let x1 = Fresh.f () in
     k @@ Fun (x0, x1, f env e0 x1)
  | Alpha.LetRec ((x0, _), xts0, e0, e1) ->
     let x1 = Fresh.f () in
     LetRec (x0, List.map fst xts0, x1, f env e0 x1, g env e1 k)
  | Alpha.Let ((x0, _), e0, e1) ->
     g env e0 (fun v0 ->
       g (Env.extend x0 v0 env) e1 k)
  | Alpha.If (e0, e1, e2) ->
     g env e0 (fun v0 ->
       If (v0, g env e1 k, g env e2 k))
  | Alpha.App (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in App (v0, v1, Cont (x0, k @@ Var x0))))
  | Alpha.Add (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in Add (v0, v1, Cont (x0, k @@ Var x0))))
  | Alpha.Sub (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in Sub (v0, v1, Cont (x0, k @@ Var x0))))
  | Alpha.Mul (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in Mul (v0, v1, Cont (x0, k @@ Var x0))))
  | Alpha.Div (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in Div (v0, v1, Cont (x0, k @@ Var x0))))
  | Alpha.Gt (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in Gt (v0, v1, Cont (x0, k @@ Var x0))))
  | Alpha.Le (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in Le (v0, v1, Cont (x0, k @@ Var x0))))
  | Alpha.Eq (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in Eq (v0, v1, Cont (x0, k @@ Var x0))))
  | Alpha.Ne (e0, e1) ->
     g env e0 (fun v0 ->
       g env e1 (fun v1 ->
         let x0 = Fresh.f () in Ne (v0, v1, Cont (x0, k @@ Var x0))))
  | Alpha.Not e0 ->
     g env e0 (fun v0 ->
       let x0 = Fresh.f () in Not (v0, Cont (x0, k @@ Var x0)))
  | Alpha.Neg e0 ->
     g env e0 (fun v0 ->
       let x0 = Fresh.f () in Neg (v0, Cont (x0, k @@ Var x0)))
  | Alpha.GtEq (e0, e1) ->
     g env (Alpha.Not (Alpha.Le (e0, e1) @@@ nowhere) @@@ nowhere) k
  | Alpha.LeEq (e0, e1) ->
     g env (Alpha.Not (Alpha.Gt (e0, e1) @@@ nowhere) @@@ nowhere) k

let f e = let k = Fresh.f () in Cont(k, f Env.empty e k)

let rec pp_tpe = Alpha.pp_tpe
let rec pp_exp = function
  | LetRec (x0, xs0, x1, e0, e1) ->
     Printf.sprintf "let rec _%d %s _%d = %s in %s"
       x0 (String.concat " " @@ List.map (fun n -> "_" ^ string_of_int n) xs0) x1 (pp_exp e0) (pp_exp e1)
  | If (v0, e0, e1) ->
     Printf.sprintf "(if %s then %s else %s)"
       (pp_term v0) (pp_exp e0) (pp_exp e1)
  | App (v0, v1, c0) ->
     Printf.sprintf "(%s %s) |> %s"
       (pp_term v0) (pp_term v1) (pp_cont c0)
  | Add (v0, v1, c0) ->
     Printf.sprintf "(%s + %s) |> %s"
       (pp_term v0) (pp_term v1) (pp_cont c0)
  | Sub (v0, v1, c0) ->
     Printf.sprintf "(%s - %s) |> %s"
       (pp_term v0) (pp_term v1) (pp_cont c0)
  | Mul (v0, v1, c0) ->
     Printf.sprintf "(%s * %s) |> %s"
       (pp_term v0) (pp_term v1) (pp_cont c0)
  | Div (v0, v1, c0) ->
     Printf.sprintf "(%s / %s) |> %s"
       (pp_term v0) (pp_term v1) (pp_cont c0)
  | Eq (v0, v1, c0) ->
     Printf.sprintf "(%s = %s) |> %s"
       (pp_term v0) (pp_term v1) (pp_cont c0)
  | Ne (v0, v1, c0) ->
     Printf.sprintf "(%s <> %s) |> %s"
       (pp_term v0) (pp_term v1) (pp_cont c0)
  | Gt (v0, v1, c0) ->
     Printf.sprintf "(%s > %s) |> %s"
       (pp_term v0) (pp_term v1) (pp_cont c0)
  | Le (v0, v1, c0) ->
     Printf.sprintf "(%s < %s) |> %s"
       (pp_term v0) (pp_term v1) (pp_cont c0)
  | Not (v0, c0) ->
     Printf.sprintf "(not %s) |> %s"
       (pp_term v0) (pp_cont c0)
  | Neg (v0, c0) ->
     Printf.sprintf "(- %s) |> %s"
       (pp_term v0) (pp_cont c0)
  | Ret (x0, v0) ->
     Printf.sprintf "_%d %s" x0 (pp_term v0)

and pp_term = function
  | Fun (x0, x1, e0) ->
     Printf.sprintf "(fun _%d _%d -> %s)"
       x0 x1 (pp_exp e0)
  | Var x0 ->
     "_" ^ (string_of_int x0)
  | Int n0 ->
     string_of_int n0
  | Bool b0 ->
     string_of_bool b0
  | Unit ->
     "()"

and pp_cont = function
  | Cont (x0, e0) ->
     Printf.sprintf "(fun _%d -> %s)"
       x0 (pp_exp e0)
