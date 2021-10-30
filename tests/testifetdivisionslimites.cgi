program test_divisions_aux_limites

begin

  if (i < 0)
    j := 1/i;
  if (i <= 0)
    j := 1/i;
  if (i < 6)
    j := 1/i;
  if (i > 0)
    j := 1/i;
  if (i > -2)
    j := 1/i;
  if (i > -2){
    if (i < 3)
	j := 1/i;
    }
end
