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
type position = 
  { name: string; line: int; column: int }

type 'a fragment = 
  { it: 'a; at: position }
  
let (@@@) it at =
  { it = it; at = at }

let it fragment = fragment.it
let at fragment = fragment.at

let info message at =
  Printf.eprintf "[INFO] %s (at %d:%d)" message at.line at.column
    
let warn message at =
  Printf.eprintf "[WARN] %s (at %d:%d)" message at.line at.column
    
let error message at =
  failwith (Printf.sprintf "%s (at %d:%d)" message at.line at.column)

module Position = struct
  let nowhere : position =
    { name = "<nowhere>"; line = -1; column = -1 }
end
