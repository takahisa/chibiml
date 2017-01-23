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
  | Let    of var * cont * exp
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

val f: Alpha.exp -> cont

include Syntax.S with type exp := exp
                  and type tpe := tpe

val pp_term: term -> string
val pp_cont: cont -> string
