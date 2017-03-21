freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Hyperbolic unit disc arithmetic
// May 2006, John Voight
//
//////////////////////////////////////////////////////////////////////////////

//-------------
//
// SpcHyd access
//
//-------------

intrinsic Center(D::SpcHyd) -> RngElt
  {Returns the element in the upper half-plane which maps to 0 in D.}

  return D`center;
end intrinsic;

intrinsic Rotation(D::SpcHyd) -> RngElt
  {Returns the rotation used in the disc.}

  return D`rotation;
end intrinsic;

intrinsic DiscToPlane(H::SpcHyp, z::SpcHydElt) -> SpcHypElt
  {Maps z in a unit disc to H.}

  zc := ComplexValue(z);
  ctr := ComplexValue(Center(Parent(z)) : Precision := Precision(zc));
  conjctr := ComplexConjugate(ctr);
  rot := Exp(-Parent(zc).1*Rotation(Parent(z)));
  return H!((conjctr*rot*zc-ctr)/(rot*zc-1));
end intrinsic;

intrinsic PlaneToDisc(D::SpcHyd, z::SpcHypElt) -> SpcHydElt
  {Maps z in an upper half-plane to D.}

  zc := ComplexValue(z);
  ctr := ComplexValue(Center(D) : Precision := Precision(zc));
  conjctr := ComplexConjugate(ctr);
  rot := Exp(Parent(zc).1*Rotation(D));
  return D!(rot*(zc-ctr)/(zc-conjctr));
end intrinsic;

intrinsic Matrix(g::GrpPSL2Elt, D::SpcHyd) -> AlgMatElt
  {Returns the matrix representation of g acting on the unit disc D.}

  if assigned g`MatrixD and g`MatrixDCenter eq Center(D) then
    return g`MatrixD;
  end if;
  RR := RealField(Parent(ComplexValue(Center(D))));
  M := Matrix(g : Precision := Precision(RR));
  ctr := ComplexValue(Center(D) : Precision:=Precision(RR), CheckInfinite:=false);
  rot := Exp(Parent(ctr).1*Rotation(D));
  Z0 := MatrixRing(ComplexField(RR), 2)![rot,-rot*ctr,1,-ComplexConjugate(ctr)];
  g`MatrixD := Z0*M*Z0^(-1);
  g`MatrixDCenter := Center(D);
  return g`MatrixD;
end intrinsic;

//-------------
//
// SpcHydElt access
//
//-------------

intrinsic IsExact(x::SpcHydElt) -> BoolElt, . 
  {Returns true (and the exact value of the argument) iff x is exact.}

  if assigned x`exact_value then
    return true, ExactValue(x);
  else
    return false, _;
  end if;
end intrinsic;  

intrinsic ExactValue(x::SpcHydElt) -> .
  {Returns the exact value of the argument; if it does not exist, returns an error.}

  require assigned x`exact_value : "Argument does not have an exact value";

  return x`exact_value;
end intrinsic;

//-------------
//
// Comparison
//
//-------------

intrinsic 'in'(x::., D::SpcHyd) -> BoolElt
  {}
  return Type(x) eq SpcHydElt;
end intrinsic;
 
intrinsic 'eq'(x::SpcHydElt, y::SpcHydElt) -> BoolElt
  {}
  if IsExact(x) and IsExact(y) and 
    IsCoercible(Parent(x`exact_value), y`exact_value) then
    return x`exact_value eq y`exact_value;
  else
    return IsWeaklyZero(x`complex_value - y`complex_value);
  end if;
end intrinsic;

//-------------
//
// Arithmetic
//
//-------------

intrinsic '*'(a::RngElt, x::SpcHydElt) -> RngElt
  {}

  if assigned x`exact_value and IsCoercible(Parent(x`exact_value), a) then
    return a*x`exact_value;
  else
    return a*x`complex_value;
  end if;
end intrinsic;

intrinsic '*'(x::SpcHydElt, a::RngElt) -> RngElt
  {}

  return a*x;
end intrinsic;

intrinsic '+'(x::SpcHydElt, y::RngElt) -> RngElt
  {}

  if assigned x`exact_value and IsCoercible(Parent(x`exact_value), y) then
    return x`exact_value + y;
  else
    return x`complex_value + y;
  end if;
end intrinsic;

intrinsic '+'(y::RngElt, x::SpcHydElt) -> RngElt
  {}

  return x+y;
end intrinsic;

intrinsic '+'(x::SpcHydElt, y::SpcHydElt) -> RngElt
  {}

  if assigned x`exact_value and assigned y`exact_value and
    IsCoercible(Parent(x`exact_value), y`exact_value) then
    return x`exact_value + y`exact_value;
  else 
    return x`complex_value + y`complex_value;
  end if;
end intrinsic;

intrinsic '-'(x::SpcHydElt) -> SpcHydElt
  {}

  z := New(SpcHydElt);
  z`complex_value := -x`complex_value;
  z`parent := x`parent;

  if assigned x`exact_value then
    z`exact_value := -x`exact_value;
  end if;
  return z;
end intrinsic;

intrinsic '-'(x::SpcHydElt, y::RngElt) -> RngElt
  {}

  return x+(-y);
end intrinsic;

intrinsic '-'(x::RngElt, y::SpcHydElt) -> RngElt
  {}

  return x+(-y);
end intrinsic;

intrinsic '-'(x::SpcHydElt, y::SpcHydElt) -> RngElt
  {}

  return (x)+(-y);
end intrinsic;

intrinsic '/'(x::SpcHydElt, a::RngElt) -> RngElt
  {}

  return (1/a)*x;
end intrinsic;

//-------------
//
// Action of PSL2
//
//-------------

intrinsic '*'(T::GrpPSL2Elt, x::SpcHydElt) -> SpcHydElt
  {Returns T(x), using the identification of the unit disc with the
   upper half-plane.}

  D := Parent(x);
  TD := Matrix(T, D);
  z := ComplexValue(x);
  return D!((TD[1,1]*z + TD[1,2])/(TD[2,1]*z + TD[2,2]));
end intrinsic;
