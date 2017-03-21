freeze;

intrinsic BestApproximation(x::FldRatElt, k::RngIntElt) -> FldRatElt
  {}
  // copied from the pr-code in c....
  if Abs(Denominator(x)) le k then
    return x;
  end if;

  p1 := 1;
  p0 := Floor(x);
  q1 := 0;
  q0 := 1;
  a := p0;
  while q0 le k do
    x -:= a;
    if x eq 0 then
      return p0/q0;
    end if;
    x := 1/x;
    if x lt k then
      a := Floor(x);
    else
      a := k;
    end if;
    p := a*p0 + p1;
    q := a*q0 + q1;
    p1 := p0;
    p0 := p;
    q1 := q0;
    q0 := q;
  end while;
  return p1/q1;
end intrinsic;  
