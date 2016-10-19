let rec even (x : int) =
  let rec odd (y : int) =
    if y > 0 then 
      even (y - 1) 
    else if x < 0 then 
      even (y + 1) 
    else
      false 
  in
  if x > 0 then 
    odd (x - 1)
  else if x < 0 then 
    odd (x + 1) 
  else
    true 
in
even 8027
