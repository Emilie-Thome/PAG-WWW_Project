program test_if_plus_complique

begin

  if (l < 0)
    x := 0;
  else 
    x := 8;

  if (l < 0)
    y := 1;
  else 
    y := 3;

  if (l < 0)
    z := -2;
  else
    z := 2;

  t1 := 12/y;
  t2 := t1 + z;
  if (x=12/y+z)
    t1 := x + y + z;
  else
    t2 := x + y + z;

end
