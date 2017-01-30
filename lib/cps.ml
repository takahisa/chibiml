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
  | LetRec of var * var * var * exp * exp
  | Let    of var * term * exp
  | If     of var * exp * exp
  | App    of var * var * cont
  | Add    of var * var * cont
  | Sub    of var * var * cont
  | Mul    of var * var * cont
  | Div    of var * var * cont
  | Gt     of var * var * cont
  | Le     of var * var * cont
  | Eq     of var * var * cont
  | Ne     of var * var * cont
  | Not    of var * cont
  | Neg    of var * cont
  | Ret    of var * var
  | Var    of var
and term =
  | Fun    of var * var * exp
  | Int    of int
  | Bool   of bool
  | Unit
and cont =
  | Cont   of var * exp

let gen_let v f =
  let x = Fresh.f () in Let (x, v, f x)

let gen_ret k x =
  Ret (k, x)

let gen_cont f =
  let x = Fresh.f () in Cont (x, f x)

let rec f env e (k: var) =
  match e.it with
  | Alpha.Var x0 when Env.mem x0 env ->
    Ret (k, Env.lookup x0 env)
  | Alpha.Var x0 ->
    Ret (k, x0)
  | Alpha.Int n0 ->
    gen_let (Int n0) (gen_ret k)
  | Alpha.Bool b0 ->
    gen_let (Bool b0) (gen_ret k)
  | Alpha.Unit ->
    gen_let Unit (gen_ret k)
  | Alpha.LetRec ((x0, _), (x1, _) :: xts0, e0, e1) ->
    let x2 = Fresh.f () in
    let e0' = f env begin
        List.fold_right (fun xt -> fun e -> Alpha.Fun (xt, e) @@@ nowhere) xts0 e0
      end x2 in
    let e1' = f env e1 k in
    LetRec (x0, x1, x2, e0', e1')
  | Alpha.LetRec ((x0, _), [], e0, e1) | Alpha.Let ((x0, _), e0, e1) ->
    g env e0 (fun x1 ->
        f (Env.extend x0 x1 env) e1 k)
  | Alpha.Fun ((x0, _), e0) ->
    let x1 = Fresh.f () in
    gen_let (Fun (x0, x1, f env e0 x1)) (gen_ret k)
  | Alpha.App (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            App (x0, x1, gen_cont (gen_ret k))))
  | Alpha.Add (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Add (x0, x1, gen_cont (gen_ret k))))
  | Alpha.Sub (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Sub (x0, x1, gen_cont (gen_ret k))))
  | Alpha.Mul (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Mul (x0, x1, gen_cont (gen_ret k))))
  | Alpha.Div (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Div (x0, x1, gen_cont (gen_ret k))))
  | Alpha.Gt (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Gt (x0, x1, gen_cont (gen_ret k))))
  | Alpha.Le (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Le (x0, x1, gen_cont (gen_ret k))))
  | Alpha.Eq (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Eq (x0, x1, gen_cont (gen_ret k))))
  | Alpha.Ne (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Ne (x0, x1, gen_cont (gen_ret k))))
  | Alpha.If (e0, e1, e2) ->
    g env e0 (fun x0 ->
        If (x0, f env e1 k, f env e2 k))
  | Alpha.Not e0 ->
    g env e0 (fun x0 ->
        Not (x0, gen_cont (gen_ret k)))
  | Alpha.Neg e0 ->
    g env e0 (fun x0 ->
        Neg (x0, gen_cont (gen_ret k)))
  | Alpha.GtEq (e0, e1) ->
    f env (Alpha.Not (Alpha.Le (e0, e1) @@@ nowhere) @@@ nowhere) k
  | Alpha.LeEq (e0, e1) ->
    f env (Alpha.Not (Alpha.Le (e0, e1) @@@ nowhere) @@@ nowhere) k

and g env e (k: var -> exp) =
  match e.it with
  | Alpha.Var x0 when Env.mem x0 env ->
    k @@ Env.lookup x0 env
  | Alpha.Var x0 ->
    k @@ x0
  | Alpha.Int n0 ->
    gen_let (Int n0) k
  | Alpha.Bool b0 ->
    gen_let (Bool b0) k
  | Alpha.Unit ->
    gen_let Unit k
  | Alpha.LetRec ((x0, _), (x1, _) :: xts0, e0, e1) ->
    let x2 = Fresh.f () in
    let e0' = f env begin
        List.fold_right (fun xt -> fun e -> Alpha.Fun (xt, e) @@@ nowhere) xts0 e0
      end x2 in
    let e1' = g env e1 k in
    LetRec (x0, x1, x2, e0', e1')
  | Alpha.LetRec ((x0, _), [], e0, e1) | Alpha.Let ((x0, _), e0, e1) ->
    g env e0 (fun x1 ->
        g (Env.extend x0 x1 env) e1 k)
  | Alpha.Fun ((x0, _), e0) ->
    let x1 = Fresh.f () in
    gen_let (Fun (x0, x1, f env e0 x1)) k
  | Alpha.App (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            App (x0, x1, gen_cont k)))
  | Alpha.Add (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Add (x0, x1, gen_cont k)))
  | Alpha.Sub (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Sub (x0, x1, gen_cont k)))
  | Alpha.Mul (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Mul (x0, x1, gen_cont k)))
  | Alpha.Div (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Div (x0, x1, gen_cont k)))
  | Alpha.Gt (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Gt (x0, x1, gen_cont k)))
  | Alpha.Le (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Le (x0, x1, gen_cont k)))
  | Alpha.Eq (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Eq (x0, x1, gen_cont k)))
  | Alpha.Ne (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Ne (x0, x1, gen_cont k)))
  | Alpha.If (e0, e1, e2) ->
    g env e0 (fun x0 ->
        let x1 = Fresh.f () in
        let x2 = Fresh.f () in
        gen_let (Fun (x1, x2, (k x1))) (fun x3 ->
            If (x0,
                g env e1 (fun x4 -> App (x3, x4, gen_cont (fun x5 -> Var x5))),
                g env e2 (fun x4 -> App (x3, x4, gen_cont (fun x5 -> Var x5))))))
  | Alpha.Not e0 ->
    g env e0 (fun x0 ->
        Not (x0, gen_cont k))
  | Alpha.Neg e0 ->
    g env e0 (fun x0 ->
        Neg (x0, gen_cont k))
  | Alpha.GtEq (e0, e1) ->
    g env (Alpha.Not (Alpha.Le (e0, e1) @@@ nowhere) @@@ nowhere) k
  | Alpha.LeEq (e0, e1) ->
    g env (Alpha.Not (Alpha.Le (e0, e1) @@@ nowhere) @@@ nowhere) k

let gen_let v f =
  let x = Fresh.f () in Let (x, v, f x)

let gen_ret k x =
  Ret (k, x)

let gen_cont f =
  let x = Fresh.f () in Cont (x, f x)

let rec f env e (k: var) =
  match e.it with
  | Alpha.Var x0 when Env.mem x0 env ->
    Ret (k, Env.lookup x0 env)
  | Alpha.Var x0 ->
    Ret (k, x0)
  | Alpha.Int n0 ->
    gen_let (Int n0) (gen_ret k)
  | Alpha.Bool b0 ->
    gen_let (Bool b0) (gen_ret k)
  | Alpha.Unit ->
    gen_let Unit (gen_ret k)
  | Alpha.LetRec ((x0, _), (x1, _) :: xts0, e0, e1) ->
    let x2 = Fresh.f () in
    let e0' = f env begin
        List.fold_right (fun xt -> fun e -> Alpha.Fun (xt, e) @@@ nowhere) xts0 e0
      end x2 in
    let e1' = f env e1 k in
    LetRec (x0, x1, x2, e0', e1')
  | Alpha.LetRec ((x0, _), [], e0, e1) | Alpha.Let ((x0, _), e0, e1) ->
    g env e0 (fun x1 ->
        f (Env.extend x0 x1 env) e1 k)
  | Alpha.Fun ((x0, _), e0) ->
    let x1 = Fresh.f () in
    gen_let (Fun (x0, x1, f env e0 x1)) (gen_ret k)
  | Alpha.App (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            App (x0, x1, gen_cont (gen_ret k))))
  | Alpha.Add (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Add (x0, x1, gen_cont (gen_ret k))))
  | Alpha.Sub (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Sub (x0, x1, gen_cont (gen_ret k))))
  | Alpha.Mul (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Mul (x0, x1, gen_cont (gen_ret k))))
  | Alpha.Div (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Div (x0, x1, gen_cont (gen_ret k))))
  | Alpha.Gt (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Gt (x0, x1, gen_cont (gen_ret k))))
  | Alpha.Le (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Le (x0, x1, gen_cont (gen_ret k))))
  | Alpha.Eq (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Eq (x0, x1, gen_cont (gen_ret k))))
  | Alpha.Ne (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Ne (x0, x1, gen_cont (gen_ret k))))
  | Alpha.If (e0, e1, e2) ->
    g env e0 (fun x0 ->
        If (x0, f env e1 k, f env e2 k))
  | Alpha.Not e0 ->
    g env e0 (fun x0 ->
        Not (x0, gen_cont (gen_ret k)))
  | Alpha.Neg e0 ->
    g env e0 (fun x0 ->
        Neg (x0, gen_cont (gen_ret k)))
  | Alpha.GtEq (e0, e1) ->
    f env (Alpha.Not (Alpha.Le (e0, e1) @@@ nowhere) @@@ nowhere) k
  | Alpha.LeEq (e0, e1) ->
    f env (Alpha.Not (Alpha.Le (e0, e1) @@@ nowhere) @@@ nowhere) k

and g env e (k: var -> exp) =
  match e.it with
  | Alpha.Var x0 when Env.mem x0 env ->
    k @@ Env.lookup x0 env
  | Alpha.Var x0 ->
    k @@ x0
  | Alpha.Int n0 ->
    gen_let (Int n0) k
  | Alpha.Bool b0 ->
    gen_let (Bool b0) k
  | Alpha.Unit ->
    gen_let Unit k
  | Alpha.LetRec ((x0, _), (x1, _) :: xts0, e0, e1) ->
    let x2 = Fresh.f () in
    let e0' = f env begin
        List.fold_right (fun xt -> fun e -> Alpha.Fun (xt, e) @@@ nowhere) xts0 e0
      end x2 in
    let e1' = g env e1 k in
    LetRec (x0, x1, x2, e0', e1')
  | Alpha.LetRec ((x0, _), [], e0, e1) | Alpha.Let ((x0, _), e0, e1) ->
    g env e0 (fun x1 ->
        g (Env.extend x0 x1 env) e1 k)
  | Alpha.Fun ((x0, _), e0) ->
    let x1 = Fresh.f () in
    gen_let (Fun (x0, x1, f env e0 x1)) k
  | Alpha.App (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            App (x0, x1, gen_cont k)))
  | Alpha.Add (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Add (x0, x1, gen_cont k)))
  | Alpha.Sub (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Sub (x0, x1, gen_cont k)))
  | Alpha.Mul (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Mul (x0, x1, gen_cont k)))
  | Alpha.Div (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Div (x0, x1, gen_cont k)))
  | Alpha.Gt (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Gt (x0, x1, gen_cont k)))
  | Alpha.Le (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Le (x0, x1, gen_cont k)))
  | Alpha.Eq (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Eq (x0, x1, gen_cont k)))
  | Alpha.Ne (e0, e1) ->
    g env e0 (fun x0 ->
        g env e1 (fun x1 ->
            Ne (x0, x1, gen_cont k)))
  | Alpha.If (e0, e1, e2) ->
    g env e0 (fun x0 ->
        let x1 = Fresh.f () in
        let x2 = Fresh.f () in
        gen_let (Fun (x1, x2, (k x1))) (fun x3 ->
            If (x0,
                g env e1 (fun x4 -> App (x3, x4, gen_cont (fun x5 -> Var x5))),
                g env e2 (fun x4 -> App (x3, x4, gen_cont (fun x5 -> Var x5))))))
  | Alpha.Not e0 ->
    g env e0 (fun x0 ->
        Not (x0, gen_cont k))
  | Alpha.Neg e0 ->
    g env e0 (fun x0 ->
        Neg (x0, gen_cont k))
  | Alpha.GtEq (e0, e1) ->
    g env (Alpha.Not (Alpha.Le (e0, e1) @@@ nowhere) @@@ nowhere) k
  | Alpha.LeEq (e0, e1) ->
    g env (Alpha.Not (Alpha.Le (e0, e1) @@@ nowhere) @@@ nowhere) k

let f e = let k = Fresh.f () in Cont(k, f Env.empty e k)

let rec pp_var = Printf.sprintf "_%d"
let rec pp_tpe = Alpha.pp_tpe
let rec pp_exp = function
  | LetRec (x0, x1, x2, e0, e1) ->
    Printf.sprintf "let rec %s %s %s = %s in %s"
      (pp_var x0) (pp_var x1) (pp_var x2) (pp_exp e0) (pp_exp e1)
  | Let (x0, v0, e0) ->
    Printf.sprintf "let %s = %s in %s"
      (pp_var x0) (pp_term v0) (pp_exp e0)
  | If (x0, e0, e1) ->
    Printf.sprintf "(if %s then %s else %s)"
      (pp_var x0) (pp_exp e0) (pp_exp e1)
  | App (x0, x1, c0) ->
    Printf.sprintf "(%s %s %s)"
      (pp_var x0) (pp_var x1) (pp_cont c0)
  | Add (x0, x1, c0) ->
    Printf.sprintf "%s (%s + %s)"
      (pp_cont c0) (pp_var x0) (pp_var x1)
  | Sub (x0, x1, c0) ->
    Printf.sprintf "%s (%s - %s)"
      (pp_cont c0) (pp_var x0) (pp_var x1)
  | Mul (x0, x1, c0) ->
    Printf.sprintf "%s (%s * %s)"
      (pp_cont c0) (pp_var x0) (pp_var x1)
  | Div (x0, x1, c0) ->
    Printf.sprintf "%s (%s / %s)"
      (pp_cont c0) (pp_var x0) (pp_var x1)
  | Eq (x0, x1, c0) ->
    Printf.sprintf "%s (%s = %s)"
      (pp_cont c0) (pp_var x0) (pp_var x1)
  | Ne (x0, x1, c0) ->
    Printf.sprintf "%s (%s <> %s)"
      (pp_cont c0) (pp_var x0) (pp_var x1)
  | Gt (x0, x1, c0) ->
    Printf.sprintf "%s (%s > %s)"
      (pp_cont c0) (pp_var x0) (pp_var x1)
  | Le (x0, x1, c0) ->
    Printf.sprintf "%s (%s < %s)"
      (pp_cont c0) (pp_var x0) (pp_var x1)
  | Not (x0, c0) ->
    Printf.sprintf "%s (not %s)"
      (pp_cont c0) (pp_var x0)
  | Neg (x0, c0) ->
    Printf.sprintf "%s (- %s)"
      (pp_cont c0) (pp_var x0)
  | Ret (x0, x1) ->
    Printf.sprintf "%s %s"
      (pp_var x0) (pp_var x1)
  | Var x0 ->
    pp_var x0

and pp_term = function
  | Fun (x0, x1, e0) ->
    Printf.sprintf "(fun %s %s -> %s)"
      (pp_var x0) (pp_var x1) (pp_exp e0)
  | Int n0 ->
    string_of_int n0
  | Bool b0 ->
    string_of_bool b0
  | Unit ->
    "()"

and pp_cont = function
  | Cont (x0, e0) ->
    Printf.sprintf "(fun %s -> %s)"
      (pp_var x0) (pp_exp e0)

let rename_var env x =
  if Env.mem x env then Env.lookup x env else x

let rec rename_exp env e =
  match e with
  | LetRec (x0, x1, x2, e0, e1) ->
    let x0' = Fresh.f () in
    let x1' = Fresh.f () in
    let x2' = Fresh.f () in
    let env0 = Env.extend x0 x0' env in
    let env1 = Env.extend x1 x1' env0 in
    let env2 = Env.extend x2 x2' env1 in
    let e0' = rename_exp env2 e0 in
    let e1' = rename_exp env0 e1 in
    LetRec (x0', x1', x2', e0', e1')
  | Let (x0, v0, e0) ->
    let x0' = Fresh.f () in
    let v0' = rename_term env v0 in
    let e0' = rename_exp (Env.extend x0 x0' env) e0 in
    Let (x0', v0', e0')
  | If (x0, e0, e1) ->
    let x0' = rename_var env x0 in
    let e0' = rename_exp env e0 in
    let e1' = rename_exp env e1 in
    If (x0', e0', e1')
  | App (x0, x1, Cont (x2, e0)) ->
    let x0' = rename_var env x0 in
    let x1' = rename_var env x1 in
    let x2' = Fresh.f () in
    let e0' = rename_exp (Env.extend x2 x2' env) e0 in
    App (x0', x1', Cont (x2', e0'))
  | Add (x0, x1, Cont (x2, e0)) ->
    let x0' = rename_var env x0 in
    let x1' = rename_var env x1 in
    let x2' = Fresh.f () in
    let e0' = rename_exp (Env.extend x2 x2' env) e0 in
    Add (x0', x1', Cont (x2', e0'))
  | Sub (x0, x1, Cont (x2, e0)) ->
    let x0' = rename_var env x0 in
    let x1' = rename_var env x1 in
    let x2' = Fresh.f () in
    let e0' = rename_exp (Env.extend x2 x2' env) e0 in
    Sub (x0', x1', Cont (x2', e0'))
  | Mul (x0, x1, Cont (x2, e0)) ->
    let x0' = rename_var env x0 in
    let x1' = rename_var env x1 in
    let x2' = Fresh.f () in
    let e0' = rename_exp (Env.extend x2 x2' env) e0 in
    Mul (x0', x1', Cont (x2', e0'))
  | Div (x0, x1, Cont (x2, e0)) ->
    let x0' = rename_var env x0 in
    let x1' = rename_var env x1 in
    let x2' = Fresh.f () in
    let e0' = rename_exp (Env.extend x2 x2' env) e0 in
    Div (x0', x1', Cont (x2', e0'))
  | Gt (x0, x1, Cont (x2, e0)) ->
    let x0' = rename_var env x0 in
    let x1' = rename_var env x1 in
    let x2' = Fresh.f () in
    let e0' = rename_exp (Env.extend x2 x2' env) e0 in
    Gt (x0', x1', Cont (x2', e0'))
  | Le (x0, x1, Cont (x2, e0)) ->
    let x0' = rename_var env x0 in
    let x1' = rename_var env x1 in
    let x2' = Fresh.f () in
    let e0' = rename_exp (Env.extend x2 x2' env) e0 in
    Le (x0', x1', Cont (x2', e0'))
  | Eq (x0, x1, Cont (x2, e0)) ->
    let x0' = rename_var env x0 in
    let x1' = rename_var env x1 in
    let x2' = Fresh.f () in
    let e0' = rename_exp (Env.extend x2 x2' env) e0 in
    Eq (x0', x1', Cont (x2', e0'))
  | Ne (x0, x1, Cont (x2, e0)) ->
    let x0' = rename_var env x0 in
    let x1' = rename_var env x1 in
    let x2' = Fresh.f () in
    let e0' = rename_exp (Env.extend x2 x2' env) e0 in
    Ne (x0', x1', Cont (x2', e0'))
  | Not (x0, Cont (x1, e0)) ->
    let x0' = rename_var env x0 in
    let x1' = Fresh.f () in
    let e0' = rename_exp (Env.extend x1 x1' env) e0 in
    Not (x0', Cont (x1', e0'))
  | Neg (x0, Cont (x1, e0)) ->
    let x0' = rename_var env x0 in
    let x1' = Fresh.f () in
    let e0' = rename_exp (Env.extend x1 x1' env) e0 in
    Neg (x0', Cont (x1', e0'))
  | Ret (x0, x1) ->
    let x0' = rename_var env x0 in
    let x1' = rename_var env x1 in
    Ret (x0', x1')
  | Var x0 ->
    Var (rename_var env x0)

and rename_term env = function
  | Fun (x0, x1, e0) ->
    let x0' = Fresh.f () in
    let x1' = Fresh.f () in
    let env0 = Env.extend x0 x0' env in
    let env1 = Env.extend x1 x1' env0 in
    let e0' = rename_exp env1 e0 in
    Fun (x0', x1', e0')
  | v0 -> v0

and rename_cont env = function
  | Cont (x0, e0) ->
    let x0' = Fresh.f () in
    let e0' = rename_exp (Env.extend x0 x0' env) e0 in
    Cont (x0', e0')
