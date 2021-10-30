program test_ameliorations

begin

  if (l < 0)
    x := 1;
  else 
    x := 5;

  if (l < 0)
    y := 1;
  else 
    y := 5;

  z := 3;
  t := 3;
  u := 3;
  v := 1;
  w := 1;
  p := 2;

  if (x < y)
  {
    z := x;
    t := y;
  }

  if (x+3 < y)
    z := -1;

  if (x+2 < y)
    u := y - x;

  if (x+y <= 3)
  { 
     if (x+y >=2)
     {
       v := x;
       w := y;
       p := x+y;
     }
  }


end
