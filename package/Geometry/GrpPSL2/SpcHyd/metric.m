freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Hyperbolic length, volume, and angles for the unit disc
// May 2006, John Voight
//
//////////////////////////////////////////////////////////////////////////////

declare attributes GrpPSL2Elt: DIntersect;

//-------------
//
// Complex values of points in the unit disc.
//
//-------------

defaultprecision := Precision(RealField());

intrinsic SetPrecision(~z::SpcHydElt, prec::RngIntElt) 
  {Sets the complex precision of z to prec.}

  z`complex_value := ComplexValue(z : Precision := prec);
end intrinsic;

intrinsic ComplexValue(z::SpcHydElt : Precision := 0) -> FldComElt
  {The complex value of the argument.}

  require Type(Precision) eq RngIntElt and Precision ge 0 :
    "Parameter Precision must be a positive integer.";

  Precision := Max(Precision, defaultprecision);

  cmpx := z`complex_value;

  if RelativePrecision(cmpx) lt Precision then
    if IsExact(z) then
      z0 := z`exact_value;
      K := Parent(z0);
      if ISA(Type(K), FldNum) then
        if BaseField(K) cmpeq Rationals() then
          // Precision only set for absolute extensions
	  SetKantPrecision(K, Precision);
	  congs := Conjugates(z0);
	  _, i := Min([ Abs(congs[i] - cmpx) : i in [1..#congs] ]);
    	  z`complex_value := congs[i];
        else
          // The scalar field must be a number field over Q
	  L := ScalarField(Parent(z));
	  SetKantPrecision(L, Precision);
	  PC := PolynomialRing(ComplexField(Precision));
	  fcoeffs := Eltseq(MinimalPolynomial(z0));
	  f := PC![ Conjugates(c)[1] : c in fcoeffs ];
	  congs := [ rt[1] : rt in Roots(f) ];
	  _, i := Min([ Abs(congs[i] - cmpx) : i in [1..#congs] ]);
    	  z`complex_value := congs[i];
        end if;
      elif Type(K) in {FldRat} then
        z`complex_value := ComplexField(Precision)!z0;
      end if;
    end if;
    // assert RelativePrecision(z`complex_value) ge Precision;
  end if;

  return z`complex_value;
end intrinsic;

intrinsic Imaginary(z::SpcHydElt : Precision := 0) -> FldReElt 
  {The imaginary part of z.}

  return Im(ComplexValue(z : Precision := Precision));
end intrinsic;

intrinsic Real(z::SpcHydElt : Precision := 0) -> FldReElt
  {The real part of z.}

  return Re(ComplexValue(z : Precision := Precision));
end intrinsic;

intrinsic AbsoluteValue(z::SpcHydElt : Precision := 0) -> FldReElt
  {The absolute value of z.}

  return Abs(ComplexValue(z : Precision := Precision));
end intrinsic;

intrinsic Argument(z::SpcHydElt : Precision := 0) -> FldReElt
  {The argument of z.}

  return Argument(ComplexValue(z : Precision := Precision));
end intrinsic;


//-------------
//
// Hyperbolic distance and geodesics
//
//-------------

intrinsic Distance(z::SpcHydElt, w::SpcHydElt : Precision := 0) -> FldReElt
  {Returns the hyperbolic distance between z and w.}

  zc := ComplexValue(z : Precision := Precision);
  wc := ComplexValue(w : Precision := Precision);

  d := Abs(1-zc*Conjugate(wc)) - Abs(zc-wc);
  if d eq 0 then
    return Infinity();
  else
    return Log( (Abs(1-zc*Conjugate(wc)) + Abs(zc-wc))/d );
  end if;
end intrinsic;

intrinsic Geodesic(z::SpcHydElt, w::SpcHydElt : Precision := 0) -> RngElt, RngElt
  {Returns the center and radius of the geodesic containing z and w.}

  zc := ComplexValue(z : Precision := Precision);
  wc := ComplexValue(w : Precision := Precision);
  if Im(wc*Conjugate(zc)) eq 0 then
    return Infty, zc;
  else
    I := Parent(wc).1;
    ctr := ((Abs(wc)^2+1)*zc-(Abs(zc)^2+1)*wc)/(2*Im(wc*Conjugate(zc)))*I;
    rsq := (Re(zc)-Re(ctr))^2+(Im(zc)-Im(ctr))^2;
  end if;

  return ctr, SquareRoot(rsq);
end intrinsic;

//-------------
//
// Hyperbolic angle
//
//-------------

intrinsic TangentAngle(x::SpcHydElt, y::SpcHydElt : Precision := 0) -> FldReElt
  {The angle of the tangent at x of the geodescic from x to y.}

  c := Geodesic(x,y : Precision := Precision);

  xc := ComplexValue(x : Precision := Precision);
  yc := ComplexValue(y : Precision := Precision);

  pi := Pi(Parent(xc));
  if x eq UnitDisc()!0 then
    theta := Argument(yc);
  elif Type(c) eq Cat or Im(xc) eq Im(c) then
    theta := pi/2;
  else
    t := -(Re(xc)-Re(c))/(Im(xc)-Im(c));
    theta := Arctan(t);
  end if;
  return RealField()!theta;
end intrinsic;

intrinsic Angle(e1::[SpcHydElt], e2::[SpcHydElt] : Precision := 0) -> FldReElt
  {Given two sequences e1 = [z1,z2] and e2 = [z1,z3], returns
   the angle between the geodesics at z1.}

  require #e1 eq 2 and #e2 eq 2: "Arguments must have length 2";
  require e1[1] eq e2[1] : "Arguments must begin with the same element";

  theta1 := TangentAngle(e1[1], e1[2] : Precision := Precision);
  theta2 := TangentAngle(e2[1], e2[2] : Precision := Precision);
  theta := theta2-theta1;
  if theta lt 0 then
    theta := theta+Pi(Parent(theta));
  end if;
  return theta;
end intrinsic;

intrinsic InternalTangentAngle(c::FldComElt, zc::FldComElt) -> .
{The angle in the hyperbolic disk}

  if IsWeaklyZero(Im(zc)-Im(c)) then
    return Pi(RealField())/2;
    // Yeah yeah, this really should depend on the sign, but this is
    // taken care of below anyway.  User beware!
  end if;

  return Arctan(-(Re(zc)-Re(c))/(Im(zc)-Im(c)));
end intrinsic;

intrinsic InternalAngle(c1::FldComElt, r1::FldReElt, 
                        c2::FldComElt, r2::FldReElt, D::SpcHyd) -> .
{The angle in the hyperbolic disk}

  z := InternalIntersection(c1,r1,c2,r2,D);
  zc := ComplexValue(z);
  theta1 := Arctan(-(Re(zc)-Re(c1))/(Im(zc)-Im(c1)));
  theta2 := Arctan(-(Re(zc)-Re(c2))/(Im(zc)-Im(c2)));
  theta := theta2-theta1;
  if theta lt 0 then
    theta := theta+Pi(Parent(theta));
  end if;
  return theta;
end intrinsic;

//-------------
//
// Hyperbolic volume
//
//-------------

intrinsic ArithmeticVolume(P::[SpcHydElt] : Precision := 0) -> FldReElt
  {The volume of the convex region specified the sequence of elements of
   the unit disc.  The volume is normalized "arithmetic" volume,
   so the usual volume is divided by 2*pi; this gives an ideal triangle
   volume 1/2.}

  Precision := Max(Precision, defaultprecision);
  n := #P;
  ind := func< i | ((i-1) mod n) + 1 >;
  pi := Pi(RealField(Precision));

  angles := [ Angle([P[ind(i)],P[ind(i+1)]],[P[ind(i)],P[ind(i-1)]]
	               : Precision := Precision) : i in [1..n] ];
  for i := 1 to #angles do
    if angles[i] gt pi then
      angles[i] -:= pi;
    elif angles[i] lt 0 then
      angles[i] +:= pi;
    end if;
  end for;
// print [t/pi : t in angles];

  return (n-2)/2-(&+angles)/(2*pi);
end intrinsic;

//-------------
//
// Intersection
//
//-------------

intrinsic InternalIntersection(c1::FldComElt, r1::FldReElt, 
                               c2::RngElt, r2::RngElt, D::SpcHyd) -> .
  {Intersection of geodesics in the hyperbolic disk}

  c := c2-c1;
  CC<I> := Parent(c);
  eps := D`eps;

  etheta := Exp(I*Argument(c));
  c /:= etheta;
  x := (c^2+r1^2-r2^2)/(2*c);
  if Re(r1^2-x^2) lt -eps then
    return [];
  end if;
  if Abs(r1^2-x^2) lt eps then
    z := x;
  else
    z := x+I*SquareRoot(r1^2-x^2);
  end if;
  zs := [z, ComplexConjugate(z)];
  zs := [z*etheta + c1 : z in zs];
  zs := [D!z : z in zs | IsCoercible(D,z)];

  if #zs eq 1 or (#zs eq 2 and Abs(zs[1]-zs[2]) lt eps) then
    return zs[1];
  elif #zs eq 0 then
    return [];
  else
    if Argument(zs[2]) lt Argument(zs[1]) then
      zs := [zs[2], zs[1]];
    end if;
    if Argument(zs[1]) lt 0 and Argument(zs[2]) gt 0
      and Abs(Argument(zs[2])-Argument(zs[1])) gt Pi(RealField()) then // Case of overlap
      zs := [zs[2], zs[1]];
    end if;
    return zs;
  end if;
end intrinsic;

intrinsic GeodesicsIntersection(x1::[SpcHydElt], x2::[SpcHydElt]) -> .
  {Returns the intersection in the unit disc of the two geodesics x1, x2,
   where x and y are specified by their end points.  If more than
   one intersection exists, returns a sequence.}

  c1, r1 := Geodesic(x1[1], x1[2]);
  c2, r2 := Geodesic(x2[1], x2[2]);
  return InternalIntersection(c1,r1,c2,r2, Parent(x1[1]));
end intrinsic;

intrinsic BoundaryIntersection(x::[SpcHydElt]) -> SeqEnum[FldComElt]
  {Computes the intersection of the geodesic x with the boundary
   of the unit disc.}
 
  c, r := Geodesic(x[1], x[2]);
  zs := InternalIntersection(c, r, 0, 1, Parent(x[1]));
  return zs;
end intrinsic;

intrinsic BoundaryIntersection(gamma::GrpPSL2Elt, D::SpcHyd) -> .
  {Returns the intersection of the isometric circle of gamma with
   the boundary of the unit disc D.}

  if assigned gamma`DIntersect then
    return gamma`DIntersect;
  end if;
  
  c, r := IsometricCircle(gamma, D);
  zs := InternalIntersection(c, r, 0, 1, D);
  gamma`DIntersect := zs;
  return zs;
end intrinsic;
