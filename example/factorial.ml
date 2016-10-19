let rec factorial x =
  if x > 0 then
    factorial (x - 1) * x
  else
    1
in
factorial 10
