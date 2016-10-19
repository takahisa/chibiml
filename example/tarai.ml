let rec tarai (x : int) = fun (y : int) -> fun (z : int) ->
  if x < y then
    y
  else if x = y then
    y
  else
    tarai (tarai (x - 1) y z) (tarai (y - 1) z x) (tarai  (z - 1) x y)
in
tarai 12 6 0
