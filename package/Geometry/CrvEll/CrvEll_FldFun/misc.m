freeze;

intrinsic IntegralModel(E::CrvEll[FldFunRat]) -> CrvEll, Map
{A model with integral coefficients of the elliptic curve E, 
defined over a rational function field}

  R := BaseRing(E);

  A := aInvariants(E);
  Insert(~A, 5, 0);

  s := R!1;
  repeat
    flag := true;
    for i := 1 to 6 do
      d := Denominator(s^i*A[i]);
      if d ne 1 then
        s *:= R!SquarefreePart(d);
        flag := false;
        break;
      end if;
    end for;
  until flag;

  F := EllipticCurve([s^i*A[i] : i in [1,2,3,4,6]]);

  m := map< E -> F | [s^2*E.1, s^3*E.2, E.3], 
                     [s^-2*F.1, s^-3*F.2, F.3] >;

  return F, m;
end intrinsic;

