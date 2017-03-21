freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Hyperbolic length, volume, and angles for the upper half-plane
// November 2001, David Kohel
// February 2006, John Voight
//
//////////////////////////////////////////////////////////////////////////////

//-------------
//
// Complex values of points in upper half-plane.
//
//-------------

defaultprecision := Precision(RealField());

intrinsic ComplexValue(z::SpcHypElt : Precision := 0, MaxValue := 600, CheckInfinite:=true) -> FldComElt
  {Returns the given element of the upper half plane as a complex number.}

  require Type(Precision) eq RngIntElt and Precision ge 0 :
    "Parameter Precision must be a positive integer.";
  Precision := Max(Precision, defaultprecision);

  cmpx := z`complex_value;
  // The coercion Parent(z)!Infinity() takes time, which is why 
  // I added this vararg to turn the check off   --- Steve
  if CheckInfinite and z eq Parent(z)!Infinity() then 
    return ComplexField(Precision)![MaxValue,MaxValue]; 
  end if;

  if RelativePrecision(cmpx) lt Precision then
    if IsExact(z) then
       z0 := z`exact_value;
       K := Parent(z0);
       if Type(K) in {FldQuad,FldCyc,FldNum} then
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
       elif Type(K) eq SetCsp then
          z`complex_value := ComplexField(Precision)!Rationals()!Eltseq(z0);
       end if;
    end if;
  end if;
  return z`complex_value;
end intrinsic;

intrinsic Imaginary(z::SpcHypElt : Precision := 0, MaxValue := 600) -> FldReElt 
  {The imaginary part of z.}

  return Im(ComplexValue(z : Precision := Precision, MaxValue := MaxValue));
end intrinsic;

intrinsic Real(z::SpcHypElt : Precision := 0, MaxValue := 600) -> FldReElt
  {The real part of z.}

  return Re(ComplexValue(z : Precision := Precision, MaxValue := MaxValue));
end intrinsic;

intrinsic AbsoluteValue(z::SpcHypElt : Precision := 0) -> FldReElt
  {The absolute value of z.}

  return Sqrt(Real(z : Precision := Precision)^2+
              Imaginary(z : Precision := Precision)^2);
end intrinsic;

//-------------
//
// Hyperbolic angles
//
//-------------

intrinsic Angle(e1::[SpcHypElt], e2::[SpcHypElt] : Precision := 0) -> FldReElt
  {Given two sequences e1 = [z1,z2] and e2 = [z1,z3], returns
   the angle between the geodesics at z1.}

  require #e1 eq 2 and #e2 eq 2: "Arguments must have length 2.";
  require Universe(e1) eq Universe(e2):
    "Arguments must have the same universe.";
  require e1[1] eq e2[1] :
    "Arguments must begin with the same element.";

  return TangentAngle(e1[1],e1[2] : Precision := Precision)
         - TangentAngle(e2[1],e2[2] : Precision := Precision);
end intrinsic;

// Cuspidal midpoint forming equal angles with each of x and y.

function CuspidalMidpoint(x,y : Precision := 0)
  eps := 10^(2-Max(Precision,defaultprecision));
  x1 := Re(x : Precision := Precision);
  x2 := Re(y : Precision := Precision);
  if Abs(x1-x2) lt eps then 
    return x1; 
  end if;
  y1 := Im(x : Precision := Precision);
  y2 := Im(y : Precision := Precision);
  return ((x1^2-x2^2)+(y1^2-y2^2))/(2*(x1-x2));
end function;

intrinsic TangentAngle(x::SpcHypElt, y::SpcHypElt : Precision := 0) -> FldReElt
  {The angle of the tangent at x of the geodescic from x to y.}

  require Type(Precision) eq RngIntElt and Precision ge 0 :
    "Parameter Precision must be a positive integer.";
  require x ne y : "Arguments must be distinct points.";

  Precision := Max(Precision, defaultprecision);
  pi := Pi(RealField(Precision));
  if IsInfinite(x) then
    return -pi/2;
  elif IsReal(x) or IsInfinite(y) then
	  return pi/2;
  end if;

  x0 := CuspidalMidpoint(x,y : Precision := Precision);
  x1 := Re(x : Precision := Precision);
  x2 := Re(y : Precision := Precision);
  y1 := Im(x : Precision := Precision);
  y2 := Im(y : Precision := Precision);
  eps := 10^(2-Precision);

  if (x1^2+y1^2) gt eps and Abs(x1-x0) lt 10*eps^2 then
    if y2 gt y1 then
	    theta1 := pi/2;
    else
      theta1 := -pi/2;
    end if;
  else 
    theta1 := Arctan(y1/(x1-x0));
	  if theta1 lt 0 then theta1 +:= pi; end if;
  end if;

  theta1 +:= -Sign(x2-x1)*pi/2;
  return theta1;
end intrinsic;

//-------------
//
// Hyperbolic distance
//
//-------------

intrinsic Distance(x::SpcHypElt, y::SpcHypElt : Precision := 0) -> FldReElt
  {The hyperbolic distance between the points x and y in the upper half plane.}
  require Type(Precision) eq RngIntElt and Precision ge 0 :
        "Parameter Precision must be a positive integer.";

  Precision := Max(Precision, defaultprecision);
  if x eq y then
	  return RealField()!0;
  elif IsCusp(x) or IsCusp(y) then
	  return Infinity();
  end if;

  RR := RealField(Precision);
  pi := Pi(RR);
  x0 := CuspidalMidpoint(x,y : Precision := Precision);
  x1 := Re(x : Precision := Precision);
  x2 := Re(y : Precision := Precision);
  y1 := Im(x : Precision := Precision);
  y2 := Im(y : Precision := Precision);
  eps := 10^(2-Precision);
  if Abs(x1-x2) lt eps then
    return Abs(Log(Abs(y1/y2)));
  elif (x1^2+y1^2) gt eps and Abs(x1-x0) lt 10*eps^2 then
	  theta1 := pi/2;
  else 
	  theta1 := Arctan(y1/(x1-x0));
	  if theta1 lt 0 then theta1 +:= pi; end if;
  end if;
  if (x2^2+y2^2) gt eps and Abs(x2-x0) lt 10*eps^2 then
	  theta2 := pi/2;
  else 
	  theta2 := Arctan(y2/(x2-x0));
	  if theta2 lt 0 then theta2 +:= pi; end if;
  end if;

  return Abs(Log(Abs(Tan(theta1/2)/Tan(theta2/2))));
end intrinsic;

//-------------
//
// Hyperbolic volume
//
//-------------

intrinsic ArithmeticVolume(P::[SpcHypElt] : Precision := 0) -> FldReElt
  {The volume of the convex region specified the sequence of elements of
   the upper half-plane.  The volume is normalized "arithmetic" volume,
   so the usual volume is divided by 2*pi; this gives an ideal triangle
   volume 1/2.}

  Precision := Max(Precision, defaultprecision);
  n := #P;
  if P[1] eq P[n] then  // expecting distinct points
     P := Remove(P,n); n -:= 1; end if; 
  ind := func< i | ((i-1) mod n) + 1 >;
  pi := Pi(RealField(Precision));

  angles := [ AbsoluteValue(
                 Angle([Universe(P)| P[ind(i)],P[ind(i+1)]],
                       [Universe(P)| P[ind(i)],P[ind(i-1)]]
	               : Precision := Precision)) : i in [1..n] ];

  // print [t/pi : t in angles];

  return (n-2)/2 - (&+angles)/(2*pi);
end intrinsic;
