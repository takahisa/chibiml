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
  | CAM_Ldi        of int
  | CAM_Ldb        of bool
  | CAM_Closure    of instruction list
  | CAM_Acc        of int
  | CAM_App
  | CAM_Ret
  | CAM_Let
  | CAM_End
  | CAM_Test       of instruction list * instruction list
  | CAM_Add
  | CAM_Sub
  | CAM_Mul
  | CAM_Div
  | CAM_Eq
  | CAM_Gt
  | CAM_Le
  | CAM_Neg
  | CAM_Not

type value =
  | CAM_IntVal     of int
  | CAM_BoolVal    of bool
  | CAM_ClosureVal of instruction list * value list

val compile: Untyped.exp -> instruction list
val run: instruction list -> value

val pp_instruction: instruction -> string
val pp_value: value -> string
