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

module Intermediate =
  struct
    type var = int * int ref
    type exp =
      | LetRec               of var * var list * exp * exp
      | Let                  of var * comp * exp
      | Ret                  of term
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
                                        
    let rec f env = function
      | Mnf.LetRec (x0, xs0, e0, e1) ->
         let n0 = ref 0 in
         let xns0 = List.map (fun x -> (x, ref 0)) xs0 in
         let env0 = Env.extend x0 n0 env in
         let env1 = List.fold_right (fun (x, n) -> fun env -> Env.extend x n env) xns0 env0 in
         LetRec ((x0, n0), xns0, f env1 e0, f env0 e1)
      | Mnf.Let (x0, c0, e0) ->
         let n0 = ref 0 in
         Let ((x0, n0), g env c0, f (Env.extend x0 n0 env) e0)
      | Mnf.Ret v0 ->
         Ret (h env v0)
             
    and g env = function
      | Mnf.Term v0 -> 
         Term (h env v0)
      | Mnf.If (v0, e0, e1) ->
         If (h env v0, f env e0, f env e1)
      | Mnf.App (v0, v1) -> App (h env v0, h env v1)
      | Mnf.Add (v0, v1) -> Add (h env v0, h env v1)
      | Mnf.Sub (v0, v1) -> Sub (h env v0, h env v1)
      | Mnf.Mul (v0, v1) -> Mul (h env v0, h env v1)
      | Mnf.Div (v0, v1) -> Div (h env v0, h env v1)
      | Mnf.Eq  (v0, v1) -> Eq  (h env v0, h env v1)
      | Mnf.Ne  (v0, v1) -> Ne  (h env v0, h env v1)
      | Mnf.Gt  (v0, v1) -> Gt  (h env v0, h env v1)
      | Mnf.Le  (v0, v1) -> Le  (h env v0, h env v1)
      | Mnf.Not v0 -> Not (h env v0)
      | Mnf.Neg v0 -> Neg (h env v0)
                          
    and h env = function
      | Mnf.Var x0 ->
         let n0 = Env.lookup x0 env in
         incr n0; Var (x0, n0)
      | Mnf.Fun (x0, e0) ->
         let n0 = ref 0 in
         Fun ((x0, n0), f (Env.extend x0 n0 env) e0)
      | Mnf.Int  n0 -> Int n0
      | Mnf.Bool b0 -> Bool b0
      | Mnf.Unit    -> Unit
  end

type var  = int
type exp  =
  | Var    of var
  | Int    of int
  | Bool   of bool
  | Unit
  | Fun    of var * exp
  | Let    of var * exp * exp 
  | LetRec of var * var list * exp * exp
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

let just0 n = (!n = 0)
let just1 n = (!n = 1)

let rec f axn = function
  | Intermediate.LetRec ((x0, n0), xns0, e0, e1) when just0 n0 ->
    f axn e1
  | Intermediate.LetRec ((x0, n0), xns0, e0, e1) ->
    LetRec (x0, List.map fst xns0, f axn e0, f axn e1)
  | Intermediate.Let ((x0, n0), e0, e1) when just0 n0 ->
    f axn e1
  | Intermediate.Let ((x0, n0), c0, e0) when just1 n0 ->
    f (Env.extend x0 (g axn c0) axn) e0
  | Intermediate.Let ((x0, n0), c0, e0) ->
    Let (x0, g axn c0, f axn e0)
  | Intermediate.Ret v0 ->
    h axn v0

and g axn = function
  | Intermediate.Term v0 -> 
     h axn v0
  | Intermediate.If (v0, e0, e1) ->
     If (h axn v0, f axn e0, f axn e1)
  | Intermediate.App (v0, v1) -> App (h axn v0, h axn v1)
  | Intermediate.Add (v0, v1) -> Add (h axn v0, h axn v1)
  | Intermediate.Sub (v0, v1) -> Sub (h axn v0, h axn v1)
  | Intermediate.Mul (v0, v1) -> Mul (h axn v0, h axn v1)
  | Intermediate.Div (v0, v1) -> Div (h axn v0, h axn v1)
  | Intermediate.Eq  (v0, v1) -> Eq  (h axn v0, h axn v1)
  | Intermediate.Ne  (v0, v1) -> Ne  (h axn v0, h axn v1)
  | Intermediate.Gt  (v0, v1) -> Gt  (h axn v0, h axn v1)
  | Intermediate.Le  (v0, v1) -> Le  (h axn v0, h axn v1)
  | Intermediate.Not v0 -> Not (h axn v0)
  | Intermediate.Neg v0 -> Neg (h axn v0)
  
and h axn = function
  | Intermediate.Var (x0, _) when Env.mem x0 axn ->
    Env.lookup x0 axn
  | Intermediate.Var (x0, _) ->
    Var x0
  | Intermediate.Fun ((x0, _), e0) ->
    Fun (x0, f axn e0)
  | Intermediate.Int  n0 -> Int n0
  | Intermediate.Bool b0 -> Bool b0
  | Intermediate.Unit    -> Unit

let f e =
  f Env.empty (Intermediate.f Env.empty e)
