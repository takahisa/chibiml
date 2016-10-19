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
open Alpha

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

val f: Alpha.exp -> exp
