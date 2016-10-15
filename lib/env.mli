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
type ('key, 'value) t = ('key * 'value) list

val empty: ('key, 'value) t

val singleton: 'key -> 'value -> ('key, 'value) t

val extend: 'key -> 'value -> ('key, 'value) t -> ('key, 'value) t

val append: ('key, 'value) t -> ('key, 'value) t -> ('key, 'value) t

val remove: 'key -> ('key, 'value) t -> ('key, 'value) t 

val mem: 'key -> ('key, 'value) t -> bool

val lookup: 'key -> ('key, 'value) t -> 'value

val of_list: ('key * 'value) list -> ('key, 'value) t
val to_list: ('key, 'value) t -> ('key * 'value) list
