freeze;

function _roots(f, R:Max := Infinity())
  assert Type(R) in {RngPad, FldPad};
  assert Type(CoefficientRing(f)) in {RngInt, FldRat};

  p := Prime(PrimeRing(R));
  assert IsPrime(p);

  IsInf := Type(Precision(R)) ne RngIntElt; 
  d_pr := R`DefaultPrecision;

  rt := [];
  Qx := PolynomialRing(Rationals());

  if Type(CoefficientRing(f)) eq RngInt and ISA(Type(R), Fld) then
    f := Qx!f;
  end if;
  lf := Factorisation(f);
  Max := Minimum(Max, Degree(f));
  for g in lf do
    if Degree(g[1]) eq 1 then
      r := -a/b where a,b := Explode(Eltseq(g[1]));
      if Valuation(r, p) lt 0 and not ISA(Type(R), Fld) then
        r := [];
      else
        r := [R!r];
      end if;
    elif Degree(g[1]) eq 0 then
//       error "";
//       constant polynomials are fine here - thay contain a partial
//       factorisation of the leading coefficient.
      r := [];
    else
      lc := LeadingCoefficient(g[1]);
      h := g[1];
      if ISA(Type(R), Fld) then
        h := h/lc;
        lc := 1;
      end if;
      d := Degree(h);
      vals := [Valuation(Coefficient(h,d-i), p)-Valuation(lc, p) : i in [1..d]];
      e := Floor(Min([ vals[i]/i : i in [1..d] ]));
      if (e gt 0 and Type(R) eq RngPad) or e cmpeq Infinity() then 
        e := 0; // don't scale
      end if;
      //1st scale the non-unit part.
      h1 := Evaluate(h, p^e*Qx.1) / p^(e*Degree(h));
      //2nd scale the unit part.
      h1 := h1/LeadingCoefficient(h1);
      v := Valuation(Discriminant(h1), p);
      if IsInf then 
        R`DefaultPrecision := Maximum(d_pr, v); 
      end if;
      r1 := Roots(Polynomial(R, h1) : IsSquarefree, Max := Max);
      r := [x[1]*p^e : x in r1 ];
      if not ISA(Type(R), Fld) then
        r := [x : x in r | Valuation(x) ge 0];
      end if;
      r := [R!x : x in r | x in R];
      if IsInf then
        R`DefaultPrecision := d_pr;
      end if;
    end if;
    for x in r do
      Append(~rt, <x, g[2]>);
    end for;
    if #rt ge Max then
      return rt[1..Max];
    end if;
  end for;
  return rt;
end function;

intrinsic Roots(f::RngUPolElt[RngInt], R::RngPad:Max := Infinity()) -> []
  {Given a univariate polynomial f over ring R, return the roots of f 
            (lying in R) as a sequence.}
  return _roots(f, R:Max := Max);
end intrinsic;

intrinsic Roots(f::RngUPolElt[RngInt], R::FldPad:Max := Infinity()) -> []
  {"} // "
  return _roots(f, R:Max := Max);
end intrinsic;

intrinsic Roots(f::RngUPolElt[FldRat], R::FldPad:Max := Infinity()) -> []
  {"} // "
  return _roots(f, R:Max := Max);
end intrinsic;

intrinsic Roots(f::RngUPolElt[FldRat], R::RngPad:Max := Infinity()) -> []
  {"} // "
  return _roots(f, R:Max := Max);
end intrinsic;


intrinsic HasRoot(f::RngUPolElt[RngInt], S::RngPad) -> BoolElt, RngElt
  {True iff f has a root in the extension ring R; if true, a root (in R) of
            f is also returned.}
  r :=  _roots(f, S:Max := 1);
  if r eq [] then
    return false, _;
  else
    return true, r[1][1];
  end if;
end intrinsic;

intrinsic HasRoot(f::RngUPolElt[RngInt], S::FldPad) -> BoolElt, RngElt
  {"} // "
  r :=  _roots(f, S:Max := 1);
  if r eq [] then
    return false, _;
  else
    return true, r[1][1];
  end if;
end intrinsic;

intrinsic HasRoot(f::RngUPolElt[FldRat], S::RngPad) -> BoolElt, RngElt
  {"} // "
  r :=  _roots(f, S:Max := 1);
  if r eq [] then
    return false, _;
  else
    return true, r[1][1];
  end if;
end intrinsic;

intrinsic HasRoot(f::RngUPolElt[FldRat], S::FldPad) -> BoolElt, RngElt
  {"} // "
  r :=  _roots(f, S:Max := 1);
  if r eq [] then
    return false, _;
  else
    return true, r[1][1];
  end if;
end intrinsic;

