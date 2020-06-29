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
type instruction =
  | ZAM_Ldi        of int
  | ZAM_Ldb        of bool
  | ZAM_Closure    of instruction list
  | ZAM_Acc        of int
  | ZAM_App
  | ZAM_TailApp
  | ZAM_Mark
  | ZAM_Grab
  | ZAM_Ret
  | ZAM_Let
  | ZAM_End
  | ZAM_Test       of instruction list * instruction list
  | ZAM_Add
  | ZAM_Sub
  | ZAM_Mul
  | ZAM_Div
  | ZAM_Eq
  | ZAM_Gt
  | ZAM_Le
  | ZAM_Neg
  | ZAM_Not

type value =
  | ZAM_IntVal     of int
  | ZAM_BoolVal    of bool
  | ZAM_ClosureVal of instruction list * value list
  | ZAM_Epsilon

val compile: Untyped.exp -> instruction list
val run: instruction list -> value

val pp_instruction: instruction -> string
val pp_value: value -> string
