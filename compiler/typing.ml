(*
 * Chibiml
 * Copyright (c) 2015-2020 Takahisa Watanabe <linerlock@outlook.com> All rights reserved.
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
open Type
open TypeScheme
open Alpha

let rec subst_tpe th t =
  match t.it with
  | TyVar x0 when List.mem_assoc x0 th ->
    subst_tpe th @@ List.assoc x0 th
  | TyFun (t00, t01) ->
    let t00' = subst_tpe th t00 in
    let t01' = subst_tpe th t01 in
    TyFun (t00', t01') @@@ t.at
  | _ -> t

let rec compose_substitution th1 th0 =
  let th0' = List.map (fun (id, t) -> (id, subst_tpe th1 t)) th0 in
  let th1' = List.fold_left begin fun th -> fun (x, t) ->
      if List.mem_assoc x th0 then th else (x, t) :: th
    end th0' th1 in th1'

let (@.) th1 th0 = compose_substitution th0 th1

let rename_tpe_scheme (TyScheme (xs0, t0)) =
  let xs1 = List.map (fun _ -> Fresh.f ()) xs0 in
  let th0 = List.fold_left compose_substitution [] @@
    List.map2 (fun x0 x1 -> [(x0, TyVar x1 @@@ nowhere)]) xs0 xs1 in
  TyScheme (xs1, subst_tpe th0 t0)

let subst_tpe_scheme th ts =
  let TyScheme (xs0, t0) = rename_tpe_scheme ts in
  TyScheme (xs0, subst_tpe th t0)

let subst_tpe_scheme_env th te =
  List.fold_left (fun te (id, ts) ->
      Env.extend id (subst_tpe_scheme th ts) te) Env.empty (Env.to_list te)

let subst_tpe_constraint th (t0, t1) =
  let t0' = subst_tpe th t0 in
  let t1' = subst_tpe th t1 in
  (t0', t1')

module S = Set.Make (struct
    type t = var
    let compare = Stdlib.compare
  end)

let rec fv_tpe t =
  match t.it with
  | TyFun (t00, t01) -> S.union (fv_tpe t00) (fv_tpe t01)
  | TyVar x0         -> S.singleton x0
  | _                -> S.empty

let fv_tpe_scheme (TyScheme (xs0, t0)) =
  S.diff (fv_tpe t0) @@ List.fold_left (fun s x -> S.union s @@ S.singleton x) S.empty xs0

let fv_tpe_scheme_env te =
  List.fold_left (fun fvs (_, ts) -> S.union fvs @@ fv_tpe_scheme ts) S.empty (Env.to_list te)

let closure t te =
  let xs0 = S.elements @@ S.diff (fv_tpe t) (fv_tpe_scheme_env te) in
  TyScheme (xs0, t)

let rec occur t0 t1 =
  t0 = t1 || (match it t0 with | TyFun (t00, t01) -> occur t00 t1 || occur t01 t1 | _ -> false)

let rec unify th = function
  | [] -> th
  | (t0, t1) :: cs -> begin
      match t0.it, t1.it with
      | (TyInt, TyInt) -> unify th cs
      | (TyBool, TyBool) -> unify th cs
      | (TyUnit, TyUnit) -> unify th cs
      | (TyFun (t00, t01), TyFun (t10, t11)) ->
        unify th @@ (t00, t10) :: (t01, t11) :: cs
      | (TyVar x0, TyVar x1) when x0 = x1 ->
        unify th cs
      | (TyVar x0, _) ->
        if occur t0 t1 then error ~message:(Printf.sprintf "infinite type (%s, %s)" (pp_tpe t0) (pp_tpe t1)) ~at:t0.at;
        unify ([(x0, t1)] @. th) @@ List.map (subst_tpe_constraint [(x0, t1)]) cs
      | (_, TyVar x1) ->
        if occur t0 t1 then error ~message:(Printf.sprintf "infinite type (%s, %s)" (pp_tpe t0) (pp_tpe t1)) ~at:t0.at;
        unify ([(x1, t0)] @. th) @@ List.map (subst_tpe_constraint [(x1, t0)]) cs
      | _ ->
        error ~message:(Printf.sprintf "unification error (%s, %s)" (pp_tpe t0) (pp_tpe t1)) ~at:t0.at
    end
let unify cs = unify [] cs

let rec f te e =
  match e.it with
  | Var x0 when Env.mem x0 te ->
    let (TyScheme (_, t0)) = rename_tpe_scheme (Env.lookup x0 te) in
    (te, [], t0)
  | Var x0 ->
    let t0 = Type.fresh () in
    let ts0 = TypeScheme.of_tpe t0 in
    let te0 = Env.extend x0 ts0 te in
    (te0, [], t0)
  | Int _ ->
    (te, [], TyInt @@@ nowhere)
  | Bool _ ->
    (te, [], TyBool @@@ nowhere)
  | Unit ->
    (te, [], TyUnit @@@ nowhere)
  | If (e0, e1, e2) ->
    let (te0, th0, t0) = f te e0 in
    let t0' = subst_tpe th0 t0 in
    let (te1, th1, t1) = f te0 e1 in
    let (te2, th2, t2) = f te1 e2 in
    let t3 = Type.fresh () in
    let th3 = unify [(t0', TyBool @@@ nowhere); (t1, t3); (t2, t3)] in
    let th4 = th0 @. th1 @. th2 @. th3 in
    let t3' = subst_tpe th4 t3 in
    let te3 = subst_tpe_scheme_env th4 te2 in
    (te3, th4, t3')
  | LetRec ((x0, t0), xts0, e0, e1) ->
    let ts0 = TypeScheme.of_tpe t0 in
    let te0 = Env.extend x0 ts0 te in
    let te1 = List.fold_right begin fun (x, t) -> fun te ->
        let ts = TypeScheme.of_tpe t in
        Env.extend x ts te
      end xts0 te0 in
    let (te2, th0, t1) = f te1 e0 in
    let t2 = List.fold_right begin fun (_, t00) -> fun t01 ->
        TyFun (t00, t01) @@@ nowhere
      end xts0 t1 in
    let th1 = unify [(t0, t2)] in
    let th2 = th0 @. th1 in
    let t0' = subst_tpe th2 t0 in
    let te3 = List.fold_right (fun (x, _) -> fun te -> Env.remove x te) xts0 te2 in
    let te4 = Env.remove x0 te3 in
    let te5 = Env.extend x0 (closure t0' te4) (subst_tpe_scheme_env th2 te4) in
    let (te6, th3, t3) = f te5 e1 in
    let th4 = th2 @. th3 in
    let te6 = subst_tpe_scheme_env th4 te5 in
    let t3' = subst_tpe th4 t3 in
    (te6, th4, t3')
  | Let ((x0, t0), e0, e1) ->
    let (te0, th0, t1) = f te e0 in
    let t1' = subst_tpe th0 t1 in
    let th1 = unify [(t0, t1')] in
    let th2 = th0 @. th1 in
    let te1 = subst_tpe_scheme_env th2 te0 in
    let te2 = Env.extend x0 (closure t1' te1) te1 in
    let (te3, th3, t2) = f te2 e1 in
    let th4 = th2 @. th3 in
    let te4 = subst_tpe_scheme_env th4 te3 in
    let t2' = subst_tpe th4 t2 in
    (te4, th4, t2')
  | Fun ((x0, t0), e0) ->
    let ts0 = TypeScheme.of_tpe t0 in
    let te0 = Env.extend x0 ts0 te in
    let (te1, th0, t1) = f te0 e0 in
    let t0' = subst_tpe th0 t0 in
    let t1' = subst_tpe th0 t1 in
    let te2 = Env.remove x0 (subst_tpe_scheme_env th0 te1) in
    (te2, th0, TyFun (t0', t1') @@@ nowhere)
  | App (e0, e1) ->
    let (te0, th0, t0) = f te e0 in
    let (te1, th1, t1) = f te0 e1 in
    let th2 = th0 @. th1 in
    let t0' = subst_tpe th2 t0 in
    let t1' = subst_tpe th2 t1 in
    let t2 = Type.fresh () in
    let th3 = unify [(t0', TyFun (t1', t2) @@@ nowhere)] in
    let th4 = th2 @. th3 in
    let te2 = subst_tpe_scheme_env th4 te1 in
    let t2' = subst_tpe th4 t2 in
    (te2, th4, t2')
  | Add (e0, e1) | Sub (e0, e1) | Mul (e0, e1) | Div (e0, e1) ->
    let (te0, th0, t0) = f te e0 in
    let (te1, th1, t1) = f te0 e1 in
    let th3 = th0 @. th1 in
    let t0' = subst_tpe th3 t0 in
    let t1' = subst_tpe th3 t1 in
    let th4 = unify [(t0', TyInt @@@ nowhere); (t1', TyInt @@@ nowhere)] in
    let th5 = th3 @. th4 in
    let te2 = subst_tpe_scheme_env th5 te1 in
    (te2, th5, TyInt @@@ nowhere)
  | Gt (e0, e1) | GtEq (e0, e1)
  | Le (e0, e1) | LeEq (e0, e1) ->
    let (te0, th0, t0) = f te e0 in
    let (te1, th1, t1) = f te0 e1 in
    let th3 = th0 @. th1 in
    let t0' = subst_tpe th3 t0 in
    let t1' = subst_tpe th3 t1 in
    let th4 = unify [(t0', TyInt @@@ nowhere); (t1', TyInt @@@ nowhere)] in
    let th5 = th3 @. th4 in
    let te2 = subst_tpe_scheme_env th5 te1 in
    (te2, th5, TyBool @@@ nowhere)
  | Eq (e0, e1) | Ne (e0, e1) ->
    let (te0, th0, t0) = f te e0 in
    let (te1, th1, t1) = f te0 e1 in
    let th3 = th0 @. th1 in
    let t0' = subst_tpe th3 t0 in
    let t1' = subst_tpe th3 t1 in
    let th4 = unify [(t0', t1')] in
    let th5 = th3 @. th4 in
    let te2 = subst_tpe_scheme_env th5 te1 in
    (te2, th5, TyBool @@@ nowhere)
  | Not e0 ->
    let (te0, th0, t0) = f te e0 in
    let t0' = subst_tpe th0 t0 in
    let th1 = unify [t0', TyBool @@@ nowhere] in
    let th2 = th0 @. th1 in
    let te1 = subst_tpe_scheme_env th2 te0 in
    (te1, th2, TyBool @@@ nowhere)
  | Neg e0 ->
    let (te0, th0, t0) = f te e0 in
    let t0' = subst_tpe th0 t0 in
    let th1 = unify [t0', TyInt @@@ nowhere] in
    let th2 = th0 @. th1 in
    let te1 = subst_tpe_scheme_env th2 te0 in
    (te1, th2, TyInt @@@ nowhere)
let f e =
  let (_, _, t0) = f Env.empty e in t0
