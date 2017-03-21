freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Hyperbolic unit disc creation
// May 2006, John Voight
//
//////////////////////////////////////////////////////////////////////////////

//-------------
//
// Attribute declarations
//
//-------------

declare type SpcHydElt;
declare type SpcHyd [SpcHydElt];

declare attributes SpcHyd:
  center, rotation,
  prec, eps;
//  F, FtoRR;            // Base field and embedding into the real numbers

declare attributes SpcHydElt:
  complex_value,
  exact_value,    
  parent;

defaultprecision := Precision(RealField());

//-------------
//
// Printing
//
//-------------

intrinsic Print(D::SpcHyd, level::MonStgElt) {}
  printf "Hyperbolic unit disc"; end intrinsic;

intrinsic Print(x::SpcHydElt, level::MonStgElt) {}
  printf "%o", InternalValue(x); end intrinsic;

//-------------
//
// Unit disc creation.
//
//-------------

intrinsic InternalValue(x::SpcHydElt) -> RngElt
  {}

  if IsExact(x) then
    return x`exact_value;
  else
    return x`complex_value;
  end if;
end intrinsic;

intrinsic InternalValue(x::SpcHypElt) -> RngElt
  {}

  if IsExact(x) then
    return x`exact_value;
  else
    return x`complex_value;
  end if;
end intrinsic;

intrinsic UnitDisc(: Center := 9/10*UpperHalfPlane().1, Precision := 0, Rotation := 0) -> SpcHyd
  {The hyperbolic unit disc, mapped conformally to the upper half-plane
   by mapping 0 in D to Center, with given precision and rotation.}

  D := New(SpcHyd);
  H := UpperHalfPlane();
  ctr := H!Center;

  // require IsExact(Center) : "Center must be exact";
  D`center := ctr;
  D`rotation := Rotation;
  D`prec := Max(Precision, defaultprecision);
  epsmin := Max(4,Round(D`prec/10));
  D`eps := 10^(epsmin-D`prec);

  return D;
end intrinsic;

//-------------
//
// Coercion to SpcHydElt
//
//-------------

intrinsic 'eq'(D::SpcHyd,E::SpcHyd) -> BoolElt {} return true; end intrinsic;

intrinsic IsCoercible(D::SpcHyd, x::.) -> BoolElt, .
  {}

  if Type(x) eq SpcHydElt then
    return true, x;
  end if;

  zs := Coercions(D, x);
  if #zs gt 1 then
    return false, "More than one possible coercion; use Coercions instead";
  elif #zs eq 0 then
    return false, "Illegal coercion";
  else
    return true, zs[1];
  end if;
end intrinsic;

intrinsic Parent(x::SpcHydElt) -> SpcHyd
  {}
  return x`parent;
end intrinsic;

intrinsic Coercions(D::SpcHyd, x::.) -> SeqEnum
  {Returns a sequence of elements of the possible coercions of x into X.}

  case Type(x):
    when SpcHydElt:
      return [x];

    when FldComElt, FldReElt:
      prec := Precision(Parent(x));
      if Abs(x) gt 1+10^(Min(4,Round(prec/10))-prec) then 
        return [];
      end if;

      z := New(SpcHydElt);
      z`complex_value := ComplexField(D`prec)!x;
      z`parent := D;
      return [z];

    when FldRatElt, RngIntElt:
      if Abs(x) gt 1 then
        return [];
      end if;

      z := New(SpcHydElt);
      z`complex_value := ComplexField(D`prec)!x;
      z`exact_value := Rationals()!x;
      z`parent := D;
      return [z];

    when FldQuadElt, RngQuadElt, FldNumElt, RngOrdElt, FldCycElt, RngCycElt:
      f := MinimalPolynomial(x, Rationals());
      K := sub<Parent(x) | x>;
      if BaseField(K) ne Rationals() then
        K := AbsoluteField(K);
        SetKantPrecision(~K, D`prec);
      end if;

      xabs := K!x;
      conjs := Conjugates(xabs);

      zs := [];
      for xc in conjs do
        if Abs(xc) le 1+D`eps then
          z := New(SpcHydElt);
          z`complex_value := xc;
          z`exact_value := K!x;
          z`parent := D;
          Append(~zs, z);
        end if;
      end for;
      return zs;
  end case;
end intrinsic;
