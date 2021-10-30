program Constant_Propagation_example

begin

  a := 5;
  b := 8;
  
  if (a > b)
    d := 2;

  if (e = f)
    g := 4;
  else
    g := 5;
  
  c := 3;
  while true do (
    a := 4;
    c := 4;
    b := a + c;
    c := 7 - a;
  )

end
