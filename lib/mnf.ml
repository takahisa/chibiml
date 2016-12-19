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
open Config
open Source
open Source.Position

type var = int
type exp =
  | LetRec              of var * var list * exp * exp
  | Let                 of var * comp * exp
  | Ret                 of term
(* serious-term; i.e. computations *)
 and comp =
  | Term                of term
  | If                  of term * exp * exp
  | App                 of term * term 
  | Add                 of term * term
  | Sub                 of term * term
  | Mul                 of term * term
  | Div                 of term * term
  | Eq                  of term * term
  | Ne                  of term * term
  | Gt                  of term * term
  | Le                  of term * term
  | Not                 of term
  | Neg                 of term
(* trivial-term; i.e. values *)
 and term =
  | Var                 of var
  | Int                 of int
  | Bool                of bool
  | Unit
  | Fun                 of var * exp

type value =
  | RecFunVal           of var * var * exp * (var, value) Env.t
  | RecFunVal_backpatch of var * var * exp * (var, value) Env.t ref
  | FunVal              of var * exp * (var, value) Env.t
  | IntVal              of int
  | BoolVal             of bool
  | UnitVal

let return v =
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
     let x0 = Fresh.f () in
     f e0 (fun v0 ->
       Let (x0, If (v0, f e1 return, f e2 return), k (Var x0)))
  | Alpha.LetRec ((x0, _), xts0, e0, e1) ->
     let e0' = f e0 return in
     let e1' = f e1 k in
     LetRec (x0, List.map fst xts0, e0', e1')
  | Alpha.Let ((x0, _), e0, e1) ->
     f e0 (fun v0 ->
      Let (x0, Term v0, f e1 k))
  | Alpha.Fun ((x0, _), e0) ->
     k @@ Fun (x0, f e0 return)
  | Alpha.App (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let x0 = Fresh.f () in
        Let (x0, App (v0, v1), k (Var x0))))
  | Alpha.Add (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let x0 = Fresh.f () in
        Let (x0, Add (v0, v1), k (Var x0))))
  | Alpha.Sub (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let x0 = Fresh.f () in
        Let (x0, Sub (v0, v1), k (Var x0))))
  | Alpha.Mul (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let x0 = Fresh.f () in
        Let (x0, Mul (v0, v1), k (Var x0))))
  | Alpha.Div (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let x0 = Fresh.f () in
        Let (x0, Div (v0, v1), k (Var x0))))
  | Alpha.Eq (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let x0 = Fresh.f () in
        Let (x0, Eq (v0, v1), k (Var x0))))
  | Alpha.Ne (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let x0 = Fresh.f () in
        Let (x0, Ne (v0, v1), k (Var x0))))
  | Alpha.Gt (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let x0 = Fresh.f () in
        Let (x0, Gt (v0, v1), k (Var x0))))
  | Alpha.Le (e0, e1) ->
     f e0 (fun v0 ->
      f e1 (fun v1 ->
        let x0 = Fresh.f () in
        Let (x0, Le (v0, v1), k (Var x0))))
  | Alpha.Not e0 ->
     let x0 = Fresh.f () in
     f e0 (fun v0 ->
        Let (x0, Not v0, k (Var x0)))
  | Alpha.Neg e0 ->
     let x0 = Fresh.f () in
     f e0 (fun v0 ->
        Let (x0, Neg v0, k (Var x0)))
let f e = f e return
    
let rec pp_exp = function
  | LetRec (x0, xs0, e0, e1) ->
    Printf.sprintf "let rec _%d %s = %s in %s" 
      x0 (String.concat " " (List.map (Printf.sprintf "_%d") xs0)) (pp_exp e0) (pp_exp e1)
  | Let (x0, c0, e1) ->
    Printf.sprintf "let _%d = %s in %s" x0 (pp_comp c0) (pp_exp e1)
  | Ret v0 ->
    pp_term v0

and pp_comp = function
  | Term v0 ->
    pp_term v0
  | If (v0, e0, e1) ->
    Printf.sprintf "(if %s then %s else %s)" (pp_term v0) (pp_exp e0) (pp_exp e1)
  | App (v0, v1) ->
    Printf.sprintf "(%s %s)" (pp_term v0) (pp_term v1)
  | Add (v0, v1) ->
    Printf.sprintf "(%s + %s)" (pp_term v0) (pp_term v1)
  | Sub (v0, v1) ->
    Printf.sprintf "(%s - %s)" (pp_term v0) (pp_term v1)
  | Mul (v0, v1) ->
    Printf.sprintf "(%s * %s)" (pp_term v0) (pp_term v1)
  | Div (v0, v1) ->
    Printf.sprintf "(%s / %s)" (pp_term v0) (pp_term v1)
  | Eq (v0, v1) ->
    Printf.sprintf "(%s = %s)" (pp_term v0) (pp_term v1)
  | Ne (v0, v1) ->
    Printf.sprintf "(%s <> %s)" (pp_term v0) (pp_term v1)
  | Gt (v0, v1) ->
    Printf.sprintf "(%s > %s)" (pp_term v0) (pp_term v1)
  | Le (v0, v1) ->
    Printf.sprintf "(%s < %s)" (pp_term v0) (pp_term v1)
  | Not v0 ->
    Printf.sprintf "(not %s)" (pp_term v0)
  | Neg v0 ->
    Printf.sprintf "(- %s)" (pp_term v0)

and pp_term = function
  | Var x0 -> 
    Printf.sprintf "_%d" x0
  | Int n0 -> 
    string_of_int n0
  | Bool b0 -> 
    string_of_bool b0
  | Unit    -> 
    "()"
  | Fun (x0, e0) ->
    Printf.sprintf "(fun _%d -> %s)" x0 (pp_exp e0)

let rec pp_value = function
  | RecFunVal (_, _, _, _) | RecFunVal_backpatch (_, _, _, _) | FunVal (_, _, _) ->
    "<fun>"
  | IntVal n0 ->
    string_of_int n0
  | BoolVal b0 ->
    string_of_bool b0
  | UnitVal ->
    "()"

