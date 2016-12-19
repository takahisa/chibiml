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

module rec Internal :
  sig
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
      | Var  of var
      | Int  of int
      | Bool of bool
      | Unit
      | Fun  of var * exp
                        
    include Syntax.S with type var := var
                      and type exp := exp
                                                    
  end = Internal
include Internal

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

let rec pp_tpe = function
  | _ ->  "<unknown>"           

module Intermediate =
  struct
    type var = int * int ref
    type exp =
      | LetRec of var * var list * exp * exp
      | Let    of var * comp * exp
      | Ret    of term
     (* serious-term; i.e. computations *)
     and comp =
       | Term   of term
       | If     of term * exp * exp
       | App    of term * term 
       | Add    of term * term
       | Sub    of term * term
       | Mul    of term * term
       | Div    of term * term
       | Eq     of term * term
       | Ne     of term * term
       | Gt     of term * term
       | Le     of term * term
       | Not    of term
       | Neg    of term
     (* trivial-term; i.e. values *)
     and term =
       | Var    of var
       | Int    of int
       | Bool   of bool
       | Unit
       | Fun    of var * exp
  end

module Elimination =
  struct
    module Syntax : Syntax.S with type var = Internal.var
                              and type exp = Internal.exp
                  = Internal

    let compile =                       
      let rec f env = function
        | LetRec (x0, xs0, e0, e1) ->
           let n0 = ref 0 in
           let xns0 = List.map (fun x -> (x, ref 0)) xs0 in
           let env0 = Env.extend x0 n0 env in
           let env1 = List.fold_right (fun (x, n) -> fun env -> Env.extend x n env) xns0 env0 in
           Intermediate.LetRec ((x0, n0), xns0, f env1 e0, f env0 e1)
        | Let (x0, c0, e0) ->
           let n0 = ref 0 in
           Intermediate.Let ((x0, n0), g env c0, f (Env.extend x0 n0 env) e0)
        | Ret v0 ->
           Intermediate.Ret (h env v0)             
      and g env = function
        | Term v0 -> 
           Intermediate.Term (h env v0)
        | If (v0, e0, e1) ->
           Intermediate.If (h env v0, f env e0, f env e1)
        | App (v0, v1) -> Intermediate.App (h env v0, h env v1)
        | Add (v0, v1) -> Intermediate.Add (h env v0, h env v1)
        | Sub (v0, v1) -> Intermediate.Sub (h env v0, h env v1)
        | Mul (v0, v1) -> Intermediate.Mul (h env v0, h env v1)
        | Div (v0, v1) -> Intermediate.Div (h env v0, h env v1)
        | Eq  (v0, v1) -> Intermediate.Eq  (h env v0, h env v1)
        | Ne  (v0, v1) -> Intermediate.Ne  (h env v0, h env v1)
        | Gt  (v0, v1) -> Intermediate.Gt  (h env v0, h env v1)
        | Le  (v0, v1) -> Intermediate.Le  (h env v0, h env v1)
        | Not v0 -> Intermediate.Not (h env v0)
        | Neg v0 -> Intermediate.Neg (h env v0)                   
      and h env = function
        | Var x0 ->
           let n0 = Env.lookup x0 env in
           incr n0; Intermediate.Var (x0, n0)
        | Fun (x0, e0) ->
           let n0 = ref 0 in
           Intermediate.Fun ((x0, n0), f (Env.extend x0 n0 env) e0)
        | Int  n0 -> Intermediate.Int n0
        | Bool b0 -> Intermediate.Bool b0
        | Unit    -> Intermediate.Unit
      in f Env.empty
           
    let eliminate =
      let rec f subst = function
        | Intermediate.LetRec ((x0, n0), xns0, e0, e1) when !n0 = 0 ->
           f subst e1
        | Intermediate.LetRec ((x0, n0), xns0, e0, e1) ->
           Elim.LetRec (x0, List.map fst xns0, f subst e0, f subst e1)
        | Intermediate.Let ((x0, n0), e0, e1) when !n0 = 0 ->
           f subst e1
        | Intermediate.Let ((x0, n0), c0, e0) when !n0 = 1 ->
           f (Env.extend x0 (g subst c0) subst) e0
        | Intermediate.Let ((x0, n0), c0, e0) ->
           Elim.Let (x0, g subst c0, f subst e0)
        | Intermediate.Ret v0 ->
           h subst v0
      and g subst = function
        | Intermediate.Term v0 -> 
           h subst v0
        | Intermediate.If (v0, e0, e1) ->
           Elim.If (h subst v0, f subst e0, f subst e1)
        | Intermediate.App (v0, v1) -> Elim.App (h subst v0, h subst v1)
        | Intermediate.Add (v0, v1) -> Elim.Add (h subst v0, h subst v1)
        | Intermediate.Sub (v0, v1) -> Elim.Sub (h subst v0, h subst v1)
        | Intermediate.Mul (v0, v1) -> Elim.Mul (h subst v0, h subst v1)
        | Intermediate.Div (v0, v1) -> Elim.Div (h subst v0, h subst v1)
        | Intermediate.Eq  (v0, v1) -> Elim.Eq  (h subst v0, h subst v1)
        | Intermediate.Ne  (v0, v1) -> Elim.Ne  (h subst v0, h subst v1)
        | Intermediate.Gt  (v0, v1) -> Elim.Gt  (h subst v0, h subst v1)
        | Intermediate.Le  (v0, v1) -> Elim.Le  (h subst v0, h subst v1)
        | Intermediate.Not v0 -> Elim.Not (h subst v0)
        | Intermediate.Neg v0 -> Elim.Neg (h subst v0)
      and h subst = function
        | Intermediate.Var (x0, _) when Env.mem x0 subst ->
           Env.lookup x0 subst
        | Intermediate.Var (x0, _) ->
           Elim.Var x0
        | Intermediate.Fun ((x0, _), e0) ->
           Elim.Fun (x0, f subst e0)
        | Intermediate.Int n0 ->
           Elim.Int n0
        | Intermediate.Bool b0 ->
           Elim.Bool b0
        | Intermediate.Unit ->
           Elim.Unit
      in f Env.empty

    let f e = eliminate (compile e)
  end
