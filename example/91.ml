let rec f n =
  if n > 100 then
    n - 10
  else
    f (f (n + 11))
in f 37
