freeze;

intrinsic PellEquation(D::RngIntElt, c::RngIntElt) -> BoolElt, []
  {Solves x^2-Dy^2 = c}

  x, y := SquarefreeFactorization(D);

  K := QuadraticField(x);
  M := MaximalOrder(K);
  N := sub<M|[1, y*K.1]>;
  
  assert K.1^2 eq x;

  f, s := NormEquation(N, c : Exact:=true );
  if f then
    s := K!s[1];
    s := Eltseq(s);
    s[2] /:= y;
    assert s[1]^2-D*s[2]^2 eq c;
    return true, s;
  else
    return false, _;
  end if;
end intrinsic;

intrinsic PellEquation(D::RngIntElt) -> BoolElt, []
  {Solves x^2-Dy^2 = -1}

  return PellEquation(D, -1);
end intrinsic;

