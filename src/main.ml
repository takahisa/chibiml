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
open Sys

exception Quit of int

module type MODE = 
  sig
    type var = Syntax.var
    type exp = Syntax.exp
    type tpe = Syntax.tpe
    type value

    val f: exp -> (exp * tpe * value)
    val pp_exp: exp -> string
    val pp_tpe: tpe -> string
    val pp_value: value -> string
  end

module Default = 
  struct
    type var = Syntax.var
    type exp = Syntax.exp
    type tpe = Syntax.tpe
    type value = Eval.value
                   
    let f e =
      let t = Typing.f e in
      let v = Eval.f Env.empty (Alpha.f e) in
      (e, t, v)
        
    let pp_exp = Pretty.pp_exp (module Syntax)
    let pp_tpe = Pretty.pp_tpe (module Syntax)
    let pp_value = Eval.pp_value
  end

module CAM_Mode = 
  struct
    type var = Syntax.var
    type exp = Syntax.exp
    type tpe = Syntax.tpe
    type value = CAM.value
                   
    let f e =
      let t = Typing.f e in
      let v = CAM.run (CAM.compile (Elim.f (module Mnf.Elimination) (Mnf.f (Alpha.f e)))) in
      (e, t, v)
        
    let pp_exp = Pretty.pp_exp (module Syntax)
    let pp_tpe = Pretty.pp_tpe (module Syntax)
    let pp_value = CAM.pp_value
  end

module ZAM_Mode =
  struct
    type var = Syntax.var
    type exp = Syntax.exp
    type tpe = Syntax.tpe
    type value = ZAM.value

    let f e =
      let t = Typing.f e in
      let v = ZAM.run (ZAM.compile (Elim.f (module Mnf.Elimination) (Mnf.f (Alpha.f e)))) in
      (e, t, v)

    let pp_exp = Pretty.pp_exp (module Syntax)
    let pp_tpe = Pretty.pp_tpe (module Syntax)
    let pp_value = ZAM.pp_value
  end

let parse lexbuf =
  Parser.main Lexer.token lexbuf

let parse_file filepath =
  let ichannel = open_in filepath in
  try parse (Lexing.from_channel ichannel) with
    | e -> close_in ichannel; raise e

let rec repl (module M : MODE) () =
  print_string "# ";
  flush stdout;
  begin 
    try
      let line = read_line () in
      let (e0, t0, v0) = M.f (snd @@ parse (Lexing.from_string line)) in
      Printf.printf ": - %s = %s\n" (M.pp_tpe t0) (M.pp_value v0)
    with
      | Quit n -> print_newline (); raise (Quit n)
  end;
  repl (module M : MODE) ()
;;

let mode: (module MODE) ref =
  ref (module Default : MODE)

let _ =
  set_signal sigint (Signal_handle (fun n -> raise (Quit n)));
  set_signal sigusr1 (Signal_handle (fun n -> raise (Quit n)));
  let filepaths = ref [] in
  Arg.parse
    [("--cam", Arg.Unit (fun () -> mode := (module CAM_Mode : MODE)), "\t\tcompiling for CAM")
    ;("--zam", Arg.Unit (fun () -> mode := (module ZAM_Mode : MODE)), "\t\tcompiling for ZAM")
    ;("--cps", Arg.Unit (fun () -> assert(false)), "\t\tenable CPS-conversion")
    ;("--backpatch", Arg.Unit begin fun () -> 
        Config.backpatch_enabled := true
      end, "\t\tenable backpatch")
    ]
    (fun path -> filepaths := !filepaths @ path :: [])
    ("chibiml Copyright(c) 2014-2016 Takahisa Watanabe\n" ^
        "  usage: chibiml [<option>] <file0> <file1> ...\n");
  try
    let (module M : MODE) = !mode in
    if List.length !filepaths = 0 then
      repl (module M : MODE) ()
    else
      List.iter begin fun path -> 
        let (e0, t0, v0) = M.f (snd @@ parse_file path) in
        Printf.printf ": - %s = %s\n" (M.pp_tpe t0) (M.pp_value v0)
      end !filepaths
  with
    Quit n -> exit n;;
