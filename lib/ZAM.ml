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

let pp_instruction = function
  | ZAM_Ldi n0            -> Printf.sprintf "ldi %d" n0
  | ZAM_Ldb b0            -> Printf.sprintf "ldb %b" b0
  | ZAM_Acc i0            -> Printf.sprintf "acc %d" i0
  | ZAM_Closure _         -> "closure (..)"
  | ZAM_App               -> "app"
  | ZAM_TailApp           -> "app.tail"
  | ZAM_Mark              -> "mark"
  | ZAM_Grab              -> "grab"
  | ZAM_Ret               -> "ret"
  | ZAM_Let               -> "let"
  | ZAM_End               -> "end"
  | ZAM_Test (_, _)       -> "test (..)"
  | ZAM_Add               -> "add"
  | ZAM_Sub               -> "sub"
  | ZAM_Mul               -> "mul"
  | ZAM_Div               -> "div"
  | ZAM_Eq                -> "eq"
  | ZAM_Gt                -> "gt"
  | ZAM_Le                -> "le"
  | ZAM_Not               -> "not"
  | ZAM_Neg               -> "neg"

let pp_value = function
  | ZAM_IntVal n0         -> string_of_int n0
  | ZAM_BoolVal b0        -> string_of_bool b0
  | ZAM_ClosureVal (_, _) -> "<fun>"
  | ZAM_Epsilon           -> "<eps>"

let rec address env x =
  match env with
  | []        -> error ~message:"no matching variable in environment." ~at:nowhere
  | y :: env' -> if (x = y) then 0 else 1 + address env' x

let unknown () =
  error ~message:"unknown expression" ~at:nowhere

let compile e =
  let rec f env = function
    | Elim.Var x0 ->
      [ZAM_Acc (address env x0)]
    | Elim.Int n0 ->
      [ZAM_Ldi n0]
    | Elim.Bool b0 ->
      [ZAM_Ldb b0]
    | Elim.Unit ->
      [ZAM_Ldi 0]
    | Elim.If (e0, e1, e2) ->
      (f env e0) @ [ZAM_Test (f env e1, f env e2)]
    | Elim.LetRec (x0, x1 :: xs0, e0, e1) ->
      let e0' = List.fold_right (fun x -> fun e -> Elim.Fun (x, e)) xs0 e0 in
      let env0 = x0 :: env in
      let env1 = x1 :: env0 in
      [ZAM_Closure (g env1 e0'); ZAM_Let] @ (f env0 e1) @ [ZAM_End]
    | Elim.Let (x0, e0, e1) ->
      (f env e0) @ [ZAM_Let] @ (f env e1) @ [ZAM_End]
    | Elim.Fun (x0, e0) ->
      [ZAM_Closure (g (x0 :: Fresh.f () :: env) e0)]
    | Elim.App _ as e0 ->
      ZAM_Mark :: (h env e0) @ [ZAM_App]
    | Elim.Add (e0, e1) -> (f env e1) @ (f env e0) @ [ZAM_Add]
    | Elim.Sub (e0, e1) -> (f env e1) @ (f env e0) @ [ZAM_Sub]
    | Elim.Mul (e0, e1) -> (f env e1) @ (f env e0) @ [ZAM_Mul]
    | Elim.Div (e0, e1) -> (f env e1) @ (f env e0) @ [ZAM_Div]
    | Elim.Eq (e0, e1) -> (f env e1) @ (f env e0) @ [ZAM_Eq]
    | Elim.Ne (e0, e1) -> (f env e1) @ (f env e0) @ [ZAM_Eq; ZAM_Not]
    | Elim.Gt (e0, e1) -> (f env e1) @ (f env e0) @ [ZAM_Gt]
    | Elim.Le (e0, e1) -> (f env e1) @ (f env e0) @ [ZAM_Le]
    | Elim.Not e0 -> (f env e0) @ [ZAM_Not]
    | Elim.Neg e0 -> (f env e0) @ [ZAM_Neg]
    | _ ->
      unknown ()

  and g env = function
    | Elim.Var _ | Elim.Int _ | Elim.Bool _ | Elim.Unit
    | Elim.Add _ | Elim.Sub _ | Elim.Mul _ | Elim.Div _
    | Elim.Eq  _ | Elim.Ne  _ | Elim.Gt  _ | Elim.Le  _  as e0 ->
      (f env e0) @ [ZAM_Ret]
    | Elim.If (e0, e1, e2) ->
      (f env e0) @ [ZAM_Test (g env e1, g env e2)]
    | Elim.LetRec (x0, x1 :: xs0, e0, e1) ->
      let e0' = List.fold_right (fun x -> fun e -> Elim.Fun (x, e)) xs0 e0 in
      let env0 = x0 :: env in
      let env1 = x1 :: env0 in
      [ZAM_Closure (g env1 e0'); ZAM_Let] @ (g env0 e1)
    | Elim.Let (x0, e0, e1) ->
      (f env e0) @ [ZAM_Let] @ (g (x0 :: env) e1)
    | Elim.Fun (x0, e0) ->
      ZAM_Grab :: (g (x0 :: Fresh.f () :: env) e0)
    | Elim.App _ as e0 ->
      (h env e0) @ [ZAM_TailApp]
    | _ ->
      unknown ()

  and h env = function
    | Elim.App (e0, e1) -> begin
        match e0 with
        | Elim.App _ -> f env e1 @ h env e0
        | _          -> f env e1 @ f env e0
      end
    | _ ->
      unknown ()
  in
  f [] e

let rec run = function
  | ZAM_Ldi n0 :: c0, e0, vs0, rs0 ->
    let vs1 = ZAM_IntVal n0 :: vs0 in
    run (c0, e0, vs1, rs0)
  | ZAM_Ldb b0 :: c0, e0, vs0, rs0 ->
    let vs1 = ZAM_BoolVal b0 :: vs0 in
    run (c0, e0, vs1, rs0)
  | ZAM_Acc i0 :: c0, e0, vs0, rs0 ->
    let vs1 = List.nth e0 i0 :: vs0 in
    run (c0, e0, vs1, rs0)
  | ZAM_Closure c1 :: c0, e0, vs0, rs0 ->
    let vs1 = ZAM_ClosureVal (c1, e0) :: vs0 in
    run (c0, e0, vs1, rs0)
  | ZAM_Let :: c0, e0, v0 :: vs0, rs0 ->
    let e1 = v0 :: e0 in
    run (c0, e1, vs0, rs0)
  | ZAM_End :: c0, _ :: e0, vs0, rs0 ->
    run (c0, e0, vs0, rs0)
  | ZAM_Test (c1, c2) :: c0, e0, ZAM_BoolVal true :: vs0, rs0 ->
    run (c1 @ c0, e0, vs0, rs0)
  | ZAM_Test (c1, c2) :: c0, e0, ZAM_BoolVal false :: vs0, rs0 ->
    run (c2 @ c0, e0, vs0, rs0)
  | ZAM_Add :: c0, e0, ZAM_IntVal n0 :: ZAM_IntVal n1 :: vs0, rs0 ->
    let vs1 = ZAM_IntVal (n0 + n1) :: vs0 in
    run (c0, e0, vs1, rs0)
  | ZAM_Sub :: c0, e0, ZAM_IntVal n0 :: ZAM_IntVal n1 :: vs0, rs0 ->
    let vs1 = ZAM_IntVal (n0 - n1) :: vs0 in
    run (c0, e0, vs1, rs0)
  | ZAM_Mul :: c0, e0, ZAM_IntVal n0 :: ZAM_IntVal n1 :: vs0, rs0 ->
    let vs1 = ZAM_IntVal (n0 * n1) :: vs0 in
    run (c0, e0, vs1, rs0)
  | ZAM_Div :: c0, e0, ZAM_IntVal n0 :: ZAM_IntVal n1 :: vs0, rs0 ->
    let vs1 = ZAM_IntVal (n0 / n1) :: vs0 in
    run (c0, e0, vs1, rs0)
  | ZAM_Neg :: c0, e0, ZAM_IntVal n0 ::  vs0, rs0 ->
    let vs1 = ZAM_IntVal(-n0) :: vs0 in
    run (c0, e0, vs1, rs0)
  | ZAM_Not :: c0, e0, ZAM_BoolVal b0 :: vs0, rs0 ->
    let vs1 = ZAM_BoolVal (not b0) :: vs0 in
    run (c0, e0, vs1, rs0)
  | ZAM_Gt :: c0, e0, ZAM_IntVal n0 :: ZAM_IntVal n1 :: vs0, rs0 ->
    let vs1 = ZAM_BoolVal (n0 > n1) :: vs0 in
    run (c0, e0, vs1, rs0)
  | ZAM_Le :: c0, e0, ZAM_IntVal n0 :: ZAM_IntVal n1 :: vs0, rs0 ->
    let vs1 = ZAM_BoolVal (n0 < n1) :: vs0 in
    run (c0, e0, vs1, rs0)
  | ZAM_Eq :: c0, e0, v0 :: v1 :: vs0, rs0 ->
    let vs1 = ZAM_BoolVal (v0 = v1) :: vs0 in
    run (c0, e0, vs1, rs0)
  | ZAM_App :: c0, e0, ZAM_ClosureVal (c1, e1) :: v0 :: vs0, rs0 ->
    let e2 = v0 :: ZAM_ClosureVal (c1, e1) :: e1 in
    let rs1 = ZAM_ClosureVal (c0, e0) :: rs0 in
    run (c1, e2, vs0, rs1)
  | ZAM_TailApp :: c0, e0, ZAM_ClosureVal (c1, e1) :: v0 :: vs0, rs0 ->
    let e2 = v0 :: ZAM_ClosureVal (c1, e1) :: e1 in
    run (c1, e2, vs0, rs0)
  | ZAM_Mark :: c0, e0, vs0, rs0 ->
    let vs1 = ZAM_Epsilon :: vs0 in
    run (c0, e0, vs1, rs0)
  | ZAM_Grab :: c0, e0, ZAM_Epsilon :: vs0, ZAM_ClosureVal (c1, e1) :: rs0 ->
    let vs1 = ZAM_ClosureVal (c0, e0) :: vs0 in
    run (c1, e1, vs1, rs0)
  | ZAM_Grab :: c0, e0, v0 :: vs0, rs0 ->
    let e1 = v0 :: ZAM_ClosureVal (c0, e0) :: e0 in
    run (c0, e1, vs0, rs0)
  | ZAM_Ret :: c0, e0, v0 :: ZAM_Epsilon :: vs0, ZAM_ClosureVal(c1, e1) :: rs0 ->
    let vs1 = v0 :: vs0 in
    run (c1, e1, vs1, rs0)
  | ZAM_Ret :: c0, e0, ZAM_ClosureVal (c1, e1) :: v0 :: vs0, rs0 ->
    let e2 = v0 :: ZAM_ClosureVal (c1, e1) :: e1 in
    run (c1, e2, vs0, rs0)
  | [], _, v0 :: [], [] ->
    v0
  | _ ->
    error ~message:"virtual machine enter an illegal-state" ~at:nowhere
let run c = run (c, [], [], [])
