program test_if

begin
 
  if (l < 0)
    x := -10;
  else
    x := 10;

  if (l < 0)
    y := 0;
  else
    y := 100;

  if (l <0)
    t := -100;
  else
    t := -20;

  w := 0;
  z := 0;
  if (x = y)
    z := 1;
  else if (x <= y)
    z := -1;
  else if (x < t)
    w := 1;

end

