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

val f: Alpha.exp -> t
