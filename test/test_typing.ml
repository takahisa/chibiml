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
open OUnit
open Source
open Source.Position
open Syntax
open Type
open Typing

let parse_exp s =
  snd @@ Parser.exp Lexer.token (Lexing.from_string s)

let parse_tpe s =
  snd @@ Parser.tpe Lexer.token (Lexing.from_string s)

let rec (<=>) t0 t1 =
  match t0.it, t1.it with
  | TyFun (t00, t01), TyFun (t10, t11) ->
     t00 <=> t10 || t10 <=> t11
  | TyVar x0, TyVar x1 -> 
     x0 = x1
  | TyInt, TyInt -> true
  | TyBool, TyBool -> true
  | TyUnit, TyUnit -> true
  | _ -> false
let (<=>) t0 t1 =
  let (_, _, t0') = rename_tyvar_tpe Env.empty 0 t0 in
  let (_, _, t1') = rename_tyvar_tpe Env.empty 0 t1 in
  t0' <=> t1'

let check s0 s1 =
  assert_equal true (Typing.f (parse_exp s0) <=> parse_tpe s1)

let testcase0 = "testcase0" >:: begin fun () ->
  check "1 + 2" "int"
end

let testcase1 = "testcase1" >:: begin fun () ->
  check "-2 * 2" "int"
end

let testcase2 = "testcase2" >:: begin fun () ->
  check "1 < 2" "bool"
end

let testcase3 = "testcase3" >:: begin fun () ->
  check "fun x -> x" "'a -> 'a"
end

let testcase4 = "testcase4" >:: begin fun () ->
  check "fun x -> fun y -> x" "'a -> 'b -> 'a"
end

let testcase5 = "testcase5" >:: begin fun () ->
  check "fun x -> fun y -> y" "'a -> 'b -> 'b"
end

let testcase6 = "testcase6" >:: begin fun () ->
  check "(fun x -> x + 1) 2 + (fun x -> x + -1) 3" "int"
end

let testcase7 = "testcase7" >:: begin fun () ->
  check "fun f -> fun g -> fun x -> g (f x)" "('a -> 'b) -> ('b -> 'c) -> 'a -> 'c"
end

let testcase8 = "testcase8" >:: begin fun () ->
  check "fun x -> fun y -> fun z -> x z (y z)" "('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c"
end

let testcase9 = "testcase9" >:: begin fun () ->
  check "fun x -> let y = x + 1 in x" "int -> int"
end

let testcase10 = "testcase10" >:: begin fun () ->
  check "fun x -> let y = x + 1 in y" "int -> int"
end

let testcase11 = "testcase11" >:: begin fun () ->
  check "fun b -> fun x -> if x b then x else (fun y -> b)" "bool -> (bool -> bool) -> bool -> bool"
end

let testcase12 = "testcase12" >:: begin fun () ->
  check "fun x -> if true then x else (if x then true else false)" "bool -> bool"
end

let testcase13 = "testcase13" >:: begin fun () ->
  check "fun x -> fun y -> if x then x else y" "bool -> bool -> bool"
end

let testcase14 = "testcase14" >:: begin fun () ->
  check "fun n -> (fun x -> x (fun y -> y)) (fun f -> f n)" "'a -> 'a"
end

let testcase15 = "testcase15" >:: begin fun () ->
  check "fun x -> fun y -> x y" "('a -> 'b) -> 'a -> 'b"
end

let testcase16 = "testcase16" >:: begin fun () ->
  check "fun x -> fun y -> x (y x)" "('a -> 'b) -> (('a -> 'b) -> 'a) -> 'b"
end

let testcase17 = "testcase17" >:: begin fun () ->
  check "fun x -> fun y -> x (y x) (y x)" "('a -> 'a -> 'b) -> (('a -> 'a -> 'b) -> 'a) -> 'b"
end

let testcase18 = "testcase18" >:: begin fun () ->
  check "fun x -> fun y -> fun z -> x (z x) (y (z x y))" 
    "((('a -> 'b) -> 'a) -> 'b -> 'c) -> ('a -> 'b) -> (((('a -> 'b) -> 'a) -> 'b -> 'c) -> ('a -> 'b) -> 'a) -> 'c"
end

let testcase19 = "testcase19" >:: begin fun () ->
  check "let id = fun x -> x in let f = fun y -> id (y id) in f" "(('a -> 'a) -> 'b) -> 'b"
end

let testcase20 = "testcase20" >:: begin fun () ->
  check "let k = fun x -> fun y -> x in let k1 = fun x -> fun y -> k (x k) in k1" 
    "(('a -> 'b -> 'a) -> 'c) -> 'd -> 'e -> 'c"
end

let testcase21 = "testcase21" >:: begin fun () ->
  check "let s = fun x -> fun y -> fun z -> x z (y z) in let s1 = fun x -> fun y -> fun z -> x s (z s) (y s (z s)) in s1" 
    "((('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c) -> 'd -> 'e -> 'f) -> ((('g -> 'h -> 'i) -> ('g -> 'h) -> 'g -> 'i) -> 'd -> 'e) -> ((('j -> 'k -> 'l) -> ('j -> 'k) -> 'j -> 'l) -> 'd) -> 'f"
end

let testcase22 = "testcase22" >:: begin fun () ->
  check "let g = fun h -> fun t -> fun f -> fun x -> f h (t f x) in g"
    "'a -> (('a -> 'b -> 'c) -> 'd -> 'b) -> ('a -> 'b -> 'c) -> 'd -> 'c"
end

let testcase23 = "testcase23" >:: begin fun () ->
  check "let s = fun x -> fun y -> fun z -> x z (y z) in let k = fun x -> fun y -> x in let k0 = fun x -> fun y -> x in s k k0"
    "'a -> 'a"
end

let testcase24 = "testcase24" >:: begin fun () ->
  check "let s = fun x -> fun y -> fun z -> x z (y z) in let k = fun x -> fun y -> x in s k k"
    "'a -> 'a"
end

let testcase25 = "testcase25" >:: begin fun () ->
  check "let s = fun x -> fun y -> fun z -> x z (y z) in let k0 = fun x -> fun y -> y in s k0 k0"
    "'a -> 'b -> 'b"
end

let testcase26 = "testcase26" >:: begin fun () ->
  check "fun x -> fun y -> fun z -> let b = x y z in if b then z y else y"
    "('a -> ('a -> 'a) -> bool) -> 'a -> ('a -> 'a) -> 'a"
end

let testcase27 = "testcase27" >:: begin fun () ->
  check "let pair = fun x1 -> fun x2 -> fun y -> y x1 x2 in let proj1 = fun p -> p (fun x1 -> fun x2 -> x1) in let proj2 = fun p -> p (fun x1 -> fun x2 -> x2) in proj1 (pair 1 100)"
    "int"
end

let testcase28 = "testcase28" >:: begin fun () ->
  check "let pair = fun x1 -> fun x2 -> fun y -> y x1 x2 in let proj1 = fun p -> p (fun x1 -> fun x2 -> x1) in let proj2 = fun p -> p (fun x1 -> fun x2 -> x2) in proj1 (proj2 (pair 10 (pair 20 30)))"
    "int"
end

let testcase29 = "testcase29" >:: begin fun () ->
  check "let f = fun x -> x in if f true then f 1 else f 2"
    "int"
end

let testcase30 = "testcase30" >:: begin fun () ->
  check "let f = fun x -> 3 in f true + f 4"
    "int"
end

let testcase31 = "testcase31" >:: begin fun () ->
  check "fun b -> let f = fun x -> x in let g = fun y -> y in if b then f g else g f"
    "bool -> 'a -> 'a"
end

let testcase32 = "testcase32" >:: begin fun () ->
  check "fun b -> fun f -> let g1 = fun x -> x f in let g2 = fun x -> x f in fun z -> if b then g1 z g2 else g2 z g1"
    "bool -> 'a -> ('a -> (('a -> 'b) -> 'b) -> 'c) -> 'c"
end

let testcase33 = "testcase33" >:: begin fun () ->
  check "let f = fun x -> 3 in f 1"
    "int"
end

let _ =
  run_test_tt_main begin
    "Typing" >::: [
      testcase0;
      testcase1;
      testcase2;
      testcase3;
      testcase4;
      testcase5;
      testcase6;
      testcase7;
      testcase8;
      testcase9;
      testcase10;
      testcase11;
      testcase12;
      testcase13;
      testcase14;
      testcase15;
      testcase16;
      testcase17;
      testcase18;
      testcase19;
      testcase20;
      testcase21;
      testcase22;
      testcase23;
      testcase24;
      testcase25;
      testcase26;
      testcase27;
      testcase28;
      testcase29;
      testcase30;
      testcase31;
      testcase32;
      testcase33
    ]
  end
