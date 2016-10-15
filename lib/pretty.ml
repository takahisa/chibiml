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
open Syntax
open Type
open Source
open Source.Position

let rec pp_tpe t =
  match t.it with
  | TyVar x0 when x0 <= 25 ->
     Printf.sprintf "'%c" (Char.chr (Char.code 'a' + x0))
  | TyVar x0 ->
     "'ty" ^ string_of_int x0
  | TyInt ->
     "int"
  | TyBool ->
     "bool"
  | TyUnit ->
     "unit"
  | TyFun (t0, t1) ->
     Printf.sprintf "(%s -> %s)"
                    (pp_tpe t0)
                    (pp_tpe t1)

let rec pp_exp e =
  match e.it with
  | Var x0 -> x0
  | Lit l0 -> begin
      match l0.it with
      | Int n0     -> string_of_int n0
      | Bool true  -> "true"
      | Bool false -> "false"
      | Unit       -> "()"
    end
  | Fun (xt0, e0) ->
     Printf.sprintf "(fun %s -> %s)" (pp_parameter xt0) (pp_exp e0)
  | Let (xt0, e0, e1) ->
     Printf.sprintf "(let %s = %s in %s)"
                    (pp_parameter xt0)
                    (pp_exp e0)
                    (pp_exp e1)
  | LetRec (xt0, xts0, e0, e1) ->
     Printf.sprintf "(let rec %s %s = %s in %s)"
                    (pp_parameter xt0)
                    (pp_parameter_list xts0)
                    (pp_exp e0)
                    (pp_exp e1)
  | If (e0, e1, e2) ->
     Printf.sprintf "(if %s then %s else %s)"
                    (pp_exp e0)
                    (pp_exp e1)
                    (pp_exp e2)
  | App (e0, e1) ->
     Printf.sprintf "(%s %s)"
                    (pp_exp e0)
                    (pp_exp e1)
  | Add (e0, e1) ->
     Printf.sprintf "(%s + %s)"
                    (pp_exp e0)
                    (pp_exp e1)
  | Sub (e0, e1) ->
     Printf.sprintf "(%s - %s)"
                    (pp_exp e0)
                    (pp_exp e1)
  | Mul (e0, e1) ->
     Printf.sprintf "(%s * %s)"
                    (pp_exp e0)
                    (pp_exp e1)
  | Div (e0, e1) ->
     Printf.sprintf "(%s / %s)"
                    (pp_exp e0)
                    (pp_exp e1)
  | Eq (e0, e1) ->
     Printf.sprintf "(%s = %s)"
                    (pp_exp e0)
                    (pp_exp e1)
  | Ne (e0, e1) ->
     Printf.sprintf "(%s <> %s)"
                    (pp_exp e0)
                    (pp_exp e1)
  | Gt (e0, e1) ->
     Printf.sprintf "(%s > %s)"
                    (pp_exp e0)
                    (pp_exp e1)
  | Le (e0, e1) ->
     Printf.sprintf "(%s < %s)"
                    (pp_exp e0)
                    (pp_exp e1)
  | Neg e0 ->
     Printf.sprintf "(- %s)" (pp_exp e0)
  | Not e0 ->
     Printf.sprintf "(not %s)" (pp_exp e0)

and pp_parameter (x0, t0) =
  Printf.sprintf "(%s : %s)" x0 (pp_tpe t0)

and pp_parameter_list xts =
  String.concat " " @@ List.map pp_parameter xts
