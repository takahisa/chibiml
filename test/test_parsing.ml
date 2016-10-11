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

let parse_exp s =
  Parser.exp Lexer.token (Lexing.from_string s)

let parse_tpe s =
  Parser.tpe Lexer.token (Lexing.from_string s)

let check e0 e1 =
  let s0 = show_exp e0 in
  let s1 = show_exp e1 in
  assert_equal s0 s1

let testcase0 = "testcase0" >:: begin fun () ->
  check (parse_exp "1") @@ 
    Lit (Int 1 @@@ nowhere) @@@ nowhere
end

let testcase1 = "testcase1" >:: begin fun () ->
  check (parse_exp "true") @@
    Lit (Bool true @@@ nowhere) @@@ nowhere
end

let testcase2 = "testcase2" >:: begin fun () ->
  check (parse_exp "false") @@ 
    Lit (Bool false @@@ nowhere) @@@ nowhere
end

let testcase3 = "testcase3" >:: begin fun () ->
  check (parse_exp "()") @@
    Lit (Unit @@@ nowhere) @@@ nowhere
end

let testcase4 = "testcase4" >:: begin fun () ->
  check (parse_exp "x0") @@ 
    Var "x0" @@@ nowhere
end

let testcase5 = "testcase5" >:: begin fun () ->
  gen_ty_sym_counter := 0;
  check (parse_exp "fun x0 -> true") @@ 
    Fun (("x0", TyVar 0 @@@ nowhere), Lit (Bool true @@@ nowhere) @@@ nowhere) @@@ nowhere
end

let testcase6 = "testcase6" >:: begin fun () ->
  gen_ty_sym_counter := 0;
  check (parse_exp "let x0 = true in x0") @@ 
    Let (("x0", TyVar 0 @@@ nowhere), Lit (Bool true @@@ nowhere) @@@ nowhere, Var "x0" @@@ nowhere) @@@ nowhere
end

let testcase7 = "testcase7" >:: begin fun () ->
  gen_ty_sym_counter := 0;
  check (parse_exp "let x0 x1 x2 x3 = true in x0") @@ 
    Let (("x0", TyVar 0 @@@ nowhere),
         Fun (("x1", TyVar 1 @@@ nowhere),
              Fun (("x2", TyVar 2 @@@ nowhere),
                   Fun (("x3", TyVar 3 @@@ nowhere), 
                        Lit (Bool true @@@ nowhere) @@@ nowhere)
                   @@@ nowhere) @@@ nowhere) @@@ nowhere,
         Var "x0" @@@ nowhere) @@@ nowhere
end

let testcase8 = "testcase8" >:: begin fun () ->
  gen_ty_sym_counter := 0;
  check (parse_exp "let rec f0 x1 x2 x3 = true in x0") @@ 
    LetRec (("f0", TyVar 0 @@@ nowhere),
         [("x1", TyVar 1 @@@ nowhere);
          ("x2", TyVar 2 @@@ nowhere);
          ("x3", TyVar 3 @@@ nowhere)],
         Lit (Bool true @@@ nowhere) @@@ nowhere,
         Var "x0" @@@ nowhere
    ) @@@ nowhere
end

let testcase9 = "testcase9" >:: begin fun () ->
  check (parse_exp "x0 x1") @@
    App (Var "x0" @@@ nowhere, Var "x1" @@@ nowhere) @@@ nowhere
end

let testcase10 = "testcase10" >:: begin fun () ->
  check (parse_exp "1 + 2") @@
    Add (Lit (Int 1 @@@ nowhere) @@@ nowhere, Lit (Int 2 @@@ nowhere) @@@ nowhere) @@@ nowhere
end

let testcase11 = "testcase11" >:: begin fun () ->
  check (parse_exp "1 - 2") @@
    Sub (Lit (Int 1 @@@ nowhere) @@@ nowhere, Lit (Int 2 @@@ nowhere) @@@ nowhere) @@@ nowhere
end

let testcase12 = "testcase12" >:: begin fun () ->
  check (parse_exp "1 * 2") @@
    Mul (Lit (Int 1 @@@ nowhere) @@@ nowhere, Lit (Int 2 @@@ nowhere) @@@ nowhere) @@@ nowhere
end

let testcase13 = "testcase13" >:: begin fun () ->
  check (parse_exp "1 / 2") @@
    Div (Lit (Int 1 @@@ nowhere) @@@ nowhere, Lit (Int 2 @@@ nowhere) @@@ nowhere) @@@ nowhere
end

let testcase14 = "testcase14" >:: begin fun () ->
  check (parse_exp "1 = 2") @@
    Eq (Lit (Int 1 @@@ nowhere) @@@ nowhere, Lit (Int 2 @@@ nowhere) @@@ nowhere) @@@ nowhere
end

let testcase15 = "testcase15" >:: begin fun () ->
  check (parse_exp "1 <> 2") @@
    Ne (Lit (Int 1 @@@ nowhere) @@@ nowhere, Lit (Int 2 @@@ nowhere) @@@ nowhere) @@@ nowhere
end

let testcase16 = "testcase16" >:: begin fun () ->
  check (parse_exp "1 > 2") @@
    Gt (Lit (Int 1 @@@ nowhere) @@@ nowhere, Lit (Int 2 @@@ nowhere) @@@ nowhere) @@@ nowhere
end

let testcase17 = "testcase17" >:: begin fun () ->
  check (parse_exp "1 < 2") @@
    Le (Lit (Int 1 @@@ nowhere) @@@ nowhere, Lit (Int 2 @@@ nowhere) @@@ nowhere) @@@ nowhere
end

let testcase18 = "testcase18" >:: begin fun () ->
  check (parse_exp "1 <= 2") @@
    Not (Gt (Lit (Int 1 @@@ nowhere) @@@ nowhere, Lit (Int 2 @@@ nowhere) @@@ nowhere) @@@ nowhere) @@@ nowhere
end

let testcase19 = "testcase19" >:: begin fun () ->
  check (parse_exp "1 >= 2") @@
    Not (Le (Lit (Int 1 @@@ nowhere) @@@ nowhere, Lit (Int 2 @@@ nowhere) @@@ nowhere) @@@ nowhere) @@@ nowhere
end

let testcase20 = "testcase20" >:: begin fun () ->
  check (parse_exp "-1") @@
    Neg (Lit (Int 1 @@@ nowhere) @@@ nowhere) @@@ nowhere
end

let testcase21 = "testcase21" >:: begin fun () ->
  check (parse_exp "not true") @@
    Not (Lit (Bool true @@@ nowhere) @@@ nowhere) @@@ nowhere
end

let _ =
  run_test_tt_main begin
    "Parsing" >::: [
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
      testcase21
    ]
  end
