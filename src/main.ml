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
exception Quit of int

let parse lexbuf =
  Parser.main Lexer.token lexbuf

let parse_file filepath =
  let ichannel = open_in filepath in
  try parse (Lexing.from_channel ichannel) with
  | e -> close_in ichannel; raise e

let iter_limit = ref 100
let iter f =
  let rec iter' f n =
    if n <= 0 then f else (fun x -> (iter' f (n - 1)) (f x))
  in iter' f !iter_limit

module type MODE =
sig
  include Eval.S
  val run: Syntax.exp -> (exp * tpe * value)
end

module Default_mode =
struct
  type exp = Alpha.exp
  type tpe = Alpha.tpe
  type value = Eval.value

  let run e =
    let e0 = Alpha.f e in
    let t0 = Typing.f e0 in
    let v0 = Eval.f Env.empty e0 in
    (e0, t0, v0)

  let pp_exp = Alpha.pp_exp
  let pp_tpe = Alpha.pp_tpe
  let pp_value = Eval.pp_value
end

module CAM_mode =
struct
  type exp = Alpha.exp
  type tpe = Alpha.tpe
  type value = CAM.value

  let optimize =
    iter (fun e -> ConstFold.f (Inline.f e))

  let run e =
    let e0 = Alpha.f e in
    let t0 = Typing.f e0 in
    print_endline @@ Untyped.pp_exp (Elim.f (Inv.f (optimize (Cps.f e0))));
    let v0 = CAM.run (CAM.compile (Elim.f (Inv.f (optimize (Cps.f e0))))) in
    (e0, t0, v0)

  let pp_exp = Alpha.pp_exp
  let pp_tpe = Alpha.pp_tpe
  let pp_value = CAM.pp_value
end

module ZAM_mode =
struct
  type exp = Alpha.exp
  type tpe = Alpha.tpe
  type value = ZAM.value

  let optimize =
    iter (fun e -> ConstFold.f (Inline.f e))

  let run e =
    let e0 = Alpha.f e in
    let t0 = Typing.f e0 in
    let v0 = ZAM.run (ZAM.compile (Elim.f (Inv.f (optimize (Cps.f e0))))) in
    (e0, t0, v0)

  let pp_exp = Alpha.pp_exp
  let pp_tpe = Alpha.pp_tpe
  let pp_value = ZAM.pp_value
end

let repl (module M : MODE) () =
  while true do
    print_string "# ";
    flush stdout;
    try
      let line = read_line () in
      let (_, t0, v0) = M.run @@ parse (Lexing.from_string line) in
      Printf.printf ": - %s = %s\n" (M.pp_tpe t0) (M.pp_value v0)
    with
    | Quit n -> print_newline (); raise (Quit n)
  done

let mode = ref (module Default_mode : MODE)
let _ =
  let open Sys in
  set_signal sigint (Signal_handle (fun n -> raise (Quit n)));
  set_signal sigusr1 (Signal_handle (fun n -> raise (Quit n)));
  let filepaths = ref [] in
  Arg.parse
    [("--cam", Arg.Unit (fun () -> mode := (module CAM_mode : MODE)), "compiling for CAM")
    ;("--zam", Arg.Unit (fun () -> mode := (module ZAM_mode : MODE)), "compiling for ZAM")
    ;("--inline", Arg.Int (fun n -> Inline.threshold := n), "maximum size of functions inlined")
    ;("-n", Arg.Int (fun n -> iter_limit := n), "maximum number of optimizations iterated")]
    (fun path -> filepaths := !filepaths @ path :: [])
    ("chibiml Copyright (c) 2014-2016 Takahisa Watanabe\n" ^
     "  usage: chibiml [<option>] <file0> <file1> ...\n");
  let (module M : MODE) = !mode in
  try
    match !filepaths with
    | [] -> repl (module M : MODE) ()
    | _  ->
      List.iter begin fun path ->
        let (_, t0, v0) = M.run @@ parse_file path in
        Printf.printf ": - %s = %s\n" (M.pp_tpe t0) (M.pp_value v0)
      end !filepaths
  with
  | Quit n -> exit n
;;
