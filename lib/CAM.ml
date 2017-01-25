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

let pp_instruction = function
  | CAM_Ldi n0            -> Printf.sprintf "ldi %d" n0
  | CAM_Ldb b0            -> Printf.sprintf "ldb %b" b0
  | CAM_Acc i0            -> Printf.sprintf "acc %d" i0
  | CAM_Closure _         -> "closure (..)"
  | CAM_App               -> "app"
  | CAM_Ret               -> "ret"
  | CAM_Let               -> "let"
  | CAM_End               -> "end"
  | CAM_Test (_, _)       -> "test (..)"
  | CAM_Add               -> "add"
  | CAM_Sub               -> "sub"
  | CAM_Mul               -> "mul"
  | CAM_Div               -> "div"
  | CAM_Eq                -> "eq"
  | CAM_Gt                -> "gt"
  | CAM_Le                -> "le"
  | CAM_Not               -> "not"
  | CAM_Neg               -> "neg"

let pp_value = function
  | CAM_IntVal n0         -> string_of_int n0
  | CAM_BoolVal b0        -> string_of_bool b0
  | CAM_ClosureVal (_, _) ->  "<fun>"

let rec address env x =
  match env with
  | []        -> error ~message:"no matching variable in environment." ~at:nowhere
  | y :: env' -> if (x = y) then 0 else 1 + address env' x

let rec compile env = function
  | Untyped.Var x0 ->
    [CAM_Acc (address env x0)]
  | Untyped.Int n0 ->
    [CAM_Ldi n0]
  | Untyped.Bool b0 ->
    [CAM_Ldb b0]
  | Untyped.Unit ->
    [CAM_Ldi 0]
  | Untyped.Fun (x0, e0) ->
    [CAM_Closure (compile (x0 :: Fresh.f () :: env) e0 @ [CAM_Ret])]
  | Untyped.LetRec (x0, x1 :: xs0, e0, e1) ->
    let e0' = List.fold_right (fun x -> fun e -> Untyped.Fun (x, e)) xs0 e0 in
    let env0 = x0 :: env in
    let env1 = x1 :: env0 in
    [CAM_Closure ((compile env1 e0') @ [CAM_Ret])] @ [CAM_Let] @ (compile env0 e1) @ [CAM_End]
  | Untyped.LetRec (x0, [], e0, e1) | Untyped.Let (x0, e0, e1) ->
    (compile env e0) @ [CAM_Let] @ (compile (x0 :: env) e1) @ [CAM_End]
  | Untyped.If (e0, e1, e2) ->
    (compile env e0) @ [CAM_Test ((compile env e1), (compile env e2))]
  | Untyped.App (e0, v1) ->
    (compile env v1) @ (compile env e0) @ [CAM_App]
  | Untyped.Add (e0, v1) ->
    (compile env v1) @ (compile env e0) @ [CAM_Add]
  | Untyped.Sub (e0, v1) ->
    (compile env v1) @ (compile env e0) @ [CAM_Sub]
  | Untyped.Mul (e0, v1) ->
    (compile env v1) @ (compile env e0) @ [CAM_Mul]
  | Untyped.Div (e0, v1) ->
    (compile env v1) @ (compile env e0) @ [CAM_Div]
  | Untyped.Eq (e0, v1) ->
    (compile env v1) @ (compile env e0) @ [CAM_Eq]
  | Untyped.Ne (e0, v1) ->
    (compile env v1) @ (compile env e0) @ [CAM_Eq; CAM_Not]
  | Untyped.Gt (e0, v1) ->
    (compile env v1) @ (compile env e0) @ [CAM_Gt]
  | Untyped.Le (e0, v1) ->
    (compile env v1) @ (compile env e0) @ [CAM_Le]
  | Untyped.Not e0 ->
    (compile env e0) @ [CAM_Not]
  | Untyped.Neg e0 ->
    (compile env e0) @ [CAM_Neg]
let compile e = compile [] e

let rec run = function
  | CAM_Ldi(n0) :: c0, e0, s0 ->
    let s1 = CAM_IntVal n0 :: s0 in
    run (c0, e0, s1)
  | CAM_Ldb(b0) :: c0, e0, s0 ->
    let s1 = CAM_BoolVal b0 :: s0 in
    run (c0, e0, s1)
  | CAM_Acc i0 :: c0, e0, s0 ->
    let s1 = List.nth e0 i0 :: s0 in
    run (c0, e0, s1)
  | CAM_Closure c1 :: c0, e0, s0 ->
    let s1 = CAM_ClosureVal (c1, e0) :: s0 in
    run (c0, e0, s1)
  | CAM_App :: c0, e0, CAM_ClosureVal(c1, e1) :: v0 :: s0 ->
    let e1 = v0 :: CAM_ClosureVal (c1, e1) :: e1 in
    let s1 = CAM_ClosureVal (c0, e0) :: s0 in
    run (c1, e1, s1)
  | CAM_Ret :: c0, e0, v0 :: CAM_ClosureVal (c1, e1) :: s0 ->
    let s1 = v0 :: s0 in
    run (c1, e1, s1)
  | CAM_Let :: c0, e0, v0 :: s0 ->
    let e1 = v0 :: e0 in
    run (c0, e1, s0)
  | CAM_End :: c0, _ :: e0, s0 ->
    run (c0, e0, s0)
  | CAM_Test(c1, c2) :: c0, e0, CAM_BoolVal(true) :: s0 ->
    run (c1 @ c0, e0, s0)
  | CAM_Test(c1, c2) :: c0, e0, CAM_BoolVal(false) :: s0 ->
    run (c2 @ c0, e0, s0)
  | CAM_Add :: c0, e0, CAM_IntVal(n0) :: CAM_IntVal(n1) :: s0 ->
    run (c0, e0, CAM_IntVal(n0 + n1) :: s0)
  | CAM_Sub :: c0, e0, CAM_IntVal(n0) :: CAM_IntVal(n1) :: s0 ->
    run (c0, e0, CAM_IntVal(n0 - n1) :: s0)
  | CAM_Mul :: c0, e0, CAM_IntVal(n0) :: CAM_IntVal(n1) :: s0 ->
    run (c0, e0, CAM_IntVal(n0 * n1) :: s0)
  | CAM_Div :: c0, e0, CAM_IntVal(n0) :: CAM_IntVal(n1) :: s0 ->
    run (c0, e0, CAM_IntVal(n0 / n1) :: s0)
  | CAM_Not :: c0, e0, CAM_BoolVal(b0) :: s0 ->
    run (c0, e0, CAM_BoolVal(not b0) :: s0)
  | CAM_Neg :: c0, e0, CAM_IntVal(n0) :: s0 ->
    run (c0, e0, CAM_IntVal(-n0) :: s0)
  | CAM_Eq :: c0, e0, CAM_ClosureVal (_, _) :: CAM_ClosureVal (_, _) :: s0 ->
    error ~message:"invalid argument; function value cannot be specified" ~at:nowhere
  | CAM_Eq :: c0, e0, v0 :: v1 :: s0 ->
    run (c0, e0, CAM_BoolVal (v0 = v1) :: s0)
  | CAM_Gt :: c0, e0, CAM_IntVal(n0) :: CAM_IntVal(n1) :: s0 ->
    run (c0, e0, CAM_BoolVal(n0 > n1) :: s0)
  | CAM_Le :: c0, e0, CAM_IntVal(n0) :: CAM_IntVal(n1) :: s0 ->
    run (c0, e0, CAM_BoolVal(n0 < n1) :: s0)
  | [], _, v0 :: [] ->
    v0
  | (code, env, stack) ->
    begin
      print_endline "<code>"; List.iter (fun c -> print_endline @@ pp_instruction c) code;
      print_endline "<env>"; List.iter (fun e -> print_endline @@ pp_value e) env;
      print_endline "<stack>"; List.iter (fun v -> print_endline @@ pp_value v) stack;
      error ~message:"virtual machine enter an illegal-state" ~at:nowhere
    end
let run c = run (c, [], [])
