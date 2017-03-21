freeze;

/*
  Functions and intrinsics which apply to all classical groups
  
  linear
  symplectic
  unitary
  orthogonal

  $Id: generic.m 51202 2015-10-02 04:07:00Z don $

  Don Taylor
  16 August 2011
*/


// This returns \prod_{j=1}^s(1-t^j)^{-1} up to degree m
TruncatedEulerProduct := function(t,s,m)
// t must be an indeterminate in a polynomial ring.
  P := Parent(t);
  f := P!1;
  if m eq 0 then return f; end if;
  for j := 1 to Min(m,s) do
    f *:= &+[P| t^(j*i) : i in [0..(m div j)]];
  end for;
  c := Rank(P) eq 1 select Coefficients(f) else Coefficients(f,t);
  return &+[c[i+1]*t^i : i in [0..Min(#c-1,m)]];
end function;

// The number of conjugacy classes in GL(n,q) as a polynomial in q
NclassesGL := function(n)
  P<t,qq> := PolynomialRing(Integers(),2);
  gf := P!0;
  for r := 0 to n do
    term := 0;
    for s := 0 to n do
      h := r*(s+1)+(s*(s+1) div 2);
      if h gt n then break; end if;
      term +:= (-1)^s*t^h*TruncatedEulerProduct(t,s,n-h);
    end for;
    gf +:= qq^r*term;
  end for;
  // Could use UnivariatePolynomial but I want q to be named.
  _<q> := PolynomialRing(Integers());
  return Evaluate(Coefficient(gf,t,n),[1,q]);
end function;

// This version is several orders of magnitude slower!
/*
NclassesGLalt := function(n)
  P<t,qq> := PolynomialRing(Integers(),2);
  f := P!1;
  for r := 1 to n do
    f *:= 1+(qq-1)*&+[P| qq^(i-1)*t^(i*r) : i in [1..n div r]];
  end for;
  Q := PolynomialRing(Integers()); q := Q.1;
  return Evaluate(Coefficient(f,t,n),[1,q]);
end function;
*/

// The number of conjugacy classes in U(n,q) as a polynomial in q
NclassesU := function(n)
  P<t,qq> := PolynomialRing(Integers(),2);
  gf := P!0;
  for r := 0 to n do
    term := 0;
    for s := 0 to n do
      h := s*(s+1) div 2;
      if h gt n then break; end if;
      term +:= t^h*TruncatedEulerProduct(t,s,n-h);
    end for;
    gf +:= qq^r*t^r*term*TruncatedEulerProduct(t,r,n-r);
  end for;
  _<q> := PolynomialRing(Integers()); 
  return Evaluate(Coefficient(gf,t,n),[1,q]);
end function;

/*
NclassesUalt := function(n)
  P<t,qq> := PolynomialRing(Integers(),2);
  f := P!1;
  for r := 1 to n do
    f *:= 1+(qq+1)*&+[P| qq^(i-1)*t^(i*r) : i in [1..n div r]];
  end for;
  Q := PolynomialRing(Integers()); q := Q.1;
  return Evaluate(Coefficient(f,t,n),[1,q]);
end function;
*/

NclassesCU := function(n)
  f := NclassesU(n);
  P<q> := Parent(f);
  return f*(q-1);
end function;



NclassesSpOdd := function(n);
  d := n div 2;
  P<t,qq> := PolynomialRing(Integers(),2);
  gf := P!0;
  for r := 0 to d do
    gf +:= qq^r * t^(2*r) * Evaluate(TruncatedEulerProduct(t,r,n-2*r),[t^2,1]);
  end for;
  gf *:= &*[ (1+t^(2*k))^4 : k in [1..d]];
  _<q> := PolynomialRing(Integers());
  return Evaluate(Coefficient(gf,t,n),[1,q]);
end function;

chi := function(nu)
    P := PolynomialRing(Integers()); x := P.1;
    val := P!0;
    if nu eq -1 then
        val := P!0;
    elif nu eq 0 then
        val := P!1;
    elif IsEven(nu) then
        mu := nu div 2;
        psi := $$(nu-1);
        val := psi + x^mu*(1+x^mu)*(psi+(1-x^(nu-1))*$$(nu-3));
    elif IsOdd(nu) then
        val := $$(nu-1) + x^nu * $$(nu-2);
    else
        error "Internal error in chi(nu)";
    end if;
    return val;
end function;


NclassesSpEven := function(n);
  d := n div 2;
  P<t,qq> := PolynomialRing(Integers(),2);
  gf := P!0;
  for r := 0 to d do
    gf +:= qq^r * t^(2*r) * Evaluate(TruncatedEulerProduct(t,r,n-2*r),[t^2,1]);
  end for;
  g := chi(n+2);
  cf := Coefficients(g)[1..d+1];
  gf *:= &+[ cf[i]*t^(2*(i-1)) : i in [1..d+1]];
  _<q> := PolynomialRing(Integers());
  return Evaluate(Coefficient(gf,t,n),[1,q]);
end function;


intrinsic Nclasses( type::MonStgElt, n::RngIntElt ) -> RngUPolElt
{ The number of conjugacy classes of a finite classical group of the 
given type as a polynomial in q }
  case type:
  when "linear":
    return NclassesGL(n);
  when "unitary":
    return NclassesU(n);
  when "symplecticOdd":
    require IsEven(n) : "dimension must be even";
    return NclassesSpOdd(n);
  when "symplecticEven":
    require IsEven(n) : "dimension must be even";
    return NclassesSpEven(n);
  when "conformalUnitary":
    return NclassesCU(n);
  else
    error "available types: linear, unitary, symplecticOdd, symplecticEven and conformalUnitary";
  end case;
end intrinsic;

intrinsic CheckNclassesGL(n::RngIntElt, q::RngIntElt, u::RngIntElt) -> BoolElt
{}
    return Evaluate(Nclasses("linear",n), q) lt u;
end intrinsic;
