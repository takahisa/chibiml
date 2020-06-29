(*
 * Chibiml
 * Copyright (c) 2015-2020 Takahisa Watanabe <takahisa.wt@gmail.com> All rights reserved.
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
module type S =
  sig
    type exp
    type tpe
    type value
    val pp_exp: exp -> string
    val pp_tpe: tpe -> string
    val pp_value: value -> string
  end

type var = Alpha.var
type exp = Alpha.exp
type tpe = Alpha.tpe
type value =
  | RecFunVal           of var * var * exp * (var, value) Env.t
  | RecFunVal_backpatch of var * var * exp * (var, value) Env.t ref
  | FunVal              of var * exp * (var, value) Env.t
  | IntVal              of int
  | BoolVal             of bool
  | UnitVal

val backpatch: bool ref

include S with type exp := exp
           and type tpe := tpe
           and type value := value

val f: (Alpha.var, value) Env.t -> exp -> value
