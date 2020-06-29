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
type var = int
type tpe = ..
type exp =
  | Var    of var
  | Int    of int
  | Bool   of bool
  | Unit
  | LetRec of var * var * exp * exp
  | Let    of var * exp * exp
  | Fun    of var * exp
  | App    of exp * exp
  | Add    of exp * exp
  | Sub    of exp * exp
  | Mul    of exp * exp
  | Div    of exp * exp
  | Eq     of exp * exp
  | Ne     of exp * exp
  | Gt     of exp * exp
  | Le     of exp * exp
  | If     of exp * exp * exp
  | Not    of exp
  | Neg    of exp

include Syntax.S with type exp := exp
                  and type tpe := tpe

val f: Alpha.exp -> exp
