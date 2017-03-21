freeze;

intrinsic Norm(f::RngUPolElt) -> RngUPolElt
{The Norm of a polynomial over the base ring/field
of its coefficient ring/field}

    P := Parent(f);
    Khat := CoefficientRing(P);
    K := BaseRing(Khat);
    P2<x, y> := PolynomialRing(K, 2);
    g := &+[
        MultivariatePolynomial(
            P2, PolynomialRing(K) ! Eltseq(Coefficients(f)[i]), 2
        ) * x^(i - 1) : i in [1..#Coefficients(f)]
    ];
    chi := UnivariatePolynomial(
    Resultant(
        MultivariatePolynomial(P2, Polynomial(K, DefiningPolynomial(Khat)), 2),
        g,
        2
    ));

    return chi;
    
end intrinsic;

intrinsic Reverse(f::RngUPolElt) -> RngUPolElt
{The polynomial obtained from f by reversing its coefficients}

    return Parent(f) ! Reverse(Eltseq(f));

end intrinsic;

intrinsic Polynomial(Q::[RngElt]) -> RngUPolElt
{Return the polynomial whose coefficients are given by Q}
    require not IsNull(Q): "Argument 1 must be non-null";
  R := Universe(Q);
  c, f := IsCoercible(PolynomialRing(R), Q);
  require c : "Argument 2 is not coercible to a polynomial over argument 1";
  return f;
end intrinsic;  

intrinsic Polynomial(R::Rng, Q::[RngElt]) -> RngUPolElt
{Return the polynomial over R whose coefficients are given by Q}
  c, f := IsCoercible(PolynomialRing(R), Q);
  require c : "Argument 2 is not coercible to a polynomial over argument 1";
  return f;
end intrinsic;

intrinsic Polynomial(R::Rng, f::RngUPolElt) -> RngUPolElt
{Return the polynomial over R obtained by coercing the coefficients of
f into R}
  c, f := IsCoercible(PolynomialRing(R), f);
  require c : "Argument 2 is not coercible over argument 1";
  return f;
end intrinsic;  

intrinsic CoefficientRing(f::RngUPolElt) -> Rng
{Return coefficient ring of f}
  return CoefficientRing(Parent(f));
end intrinsic;  

intrinsic '/'(I::RngUPol, J::RngUPol) -> RngUPolRes
{The quotient ring I/J}
    require BaseRing(I) eq BaseRing(J): "Incompatible arguments";
    return quo<I | J>;
end intrinsic;

intrinsic XGCD(Q::[RngUPolElt]) -> RngUPolElt, SeqEnum
{Return the GCD of polynomials in Q, together with the
sequence of cofactors.}

    require #Q gt 0: "Sequence argument 1 must be non-empty";
    P := Universe(Q);
    require IsField(BaseRing(P)): "Base ring must be a field";

    f := Q[1];
    G := Normalize(f);
    C := [P | IsZero(f) select 0 else 1/LeadingCoefficient(f)];

    for i in [2 .. #Q] do
	 G, a, b := XGCD(G, Q[i]);
	 C := [a*c: c in C];
	 Append(~C, b);
    end for;

    return G, C;
end intrinsic;

intrinsic ChangeRing(f::RngUPolElt, S::Rng) -> RngUPolElt
{Return the polynomial over S obtained by coercing the coefficients of
f into S}
  l, g := IsCoercible(PolynomialRing(S), f);
  require l: "Polynomial is not coercible"; return g; end intrinsic;  

intrinsic ChangeRing(f::RngMPolElt, S::Rng) -> RngMPolElt
{Return the polynomial over S obtained by coercing the coefficients
 of f into S}
  l, g := IsCoercible(PolynomialRing(S,Rank(Parent(f))), f);
  require l: "Polynomial is not coercible"; return g; end intrinsic;  

// similar to FactorisationToInteger:
intrinsic FactorisationToPolynomial( Q::SeqEnum ) -> RngUPolElt
{Given the factorisation sequence Q of a polynomial, 
return the polynomial}
  C := Universe(Q);
  require Category(C) eq SetCart and NumberOfComponents(C) eq 2 and
    ISA(Category(Component(C,1)),RngUPol) and Category(Component(C,2)) eq RngInt :
    "Not the factorisation sequence of a polynomial";
  return &*[ f[1]^f[2] : f in Q ];
end intrinsic;

intrinsic Facpol( Q::SeqEnum ) -> RngUPolElt
{Given the factorisation sequence Q of a polynomial, 
return the polynomial}
  C := Universe(Q);
  require Category(C) eq SetCart and NumberOfComponents(C) eq 2 and
    ISA(Category(Component(C,1)),RngUPol) and Category(Component(C,2)) eq RngInt :
    "Not the factorisation sequence of a polynomial";
  return &*[ f[1]^f[2] : f in Q ];
end intrinsic;

// We consider a polynomial to be cyclotomic if it is irreducible and
// its root is a root of unity (eg, every irred over a finite field is cyclotomic).
// also returns the order of the root of p
intrinsic IsCyclotomicPolynomial( p::RngUPolElt ) -> BoolElt, RngIntElt
{True iff p is a cyclotomic polynomial}
  if not IsIrreducible( p ) then  return false, _;  end if;
  if Degree( p ) eq 1 then
    P:= Parent( p ); X:=P.1;
    if p eq X-1 then  return true, 1;
    elif p eq X+1 then  return true, 2;
    else  return false,_;
    end if;
  end if;
  F<x> := NumberField( p );
  return IsRootOfUnity( x );
end intrinsic;
 
intrinsic MinimalCoefficientDegree(f::RngUPolElt) -> RngUPolElt
{The degree of the minimal subfield in which the coefficients of f
lie (over a finite field)}

    require Type(BaseRing(Parent(f))) eq FldFin:
	"Polynomial must be over a finite field";

    return LCM([Degree(MinimalPolynomial(c)): c in Coefficients(f)]);

end intrinsic;

intrinsic CanChangeRing(f::RngUPolElt, S) -> BoolElt, RngUPolElt
{True iff it is possible to coerce the coefficients of f to S; if
so, return also the resulting polynomial};

    l, Q := CanChangeUniverse(Eltseq(f), S);
    if l then
	return true, PolynomialRing(S) ! Q;
    else
	return false, _;
    end if;

end intrinsic;

intrinsic Degree(R::RngUPolRes) -> RngIntElt
{The degree of the modulus of the quotient ring R}

    return Degree(Modulus(R));
end intrinsic;

intrinsic JacobiSymbol(a::RngUPolElt, b::RngUPolElt) -> RngIntElt
{The Jacobi symbol (a/b) for two polynomials a,b in F_q[x]}
  require Parent(a) eq Parent(b):
    "The polynomials must be in the same polynomial ring";
  F:= BaseRing(Parent(a));
  require IsField(F) and IsFinite(F) and IsOdd(Characteristic(F)):
    "Only polynomials over finite fields of odd characteristic are supported";
  require Degree(b) ge 1: "The second polynomial must have degree at least 1";
  a:= a mod b;
  if GCD(a,b) ne 1 then return 0; end if;

  s:= 1;
  Fswap:= #F mod 4 eq 3;
  while Degree(a) ne 0 do
    if Fswap and IsOdd(Degree(a)) and IsOdd(Degree(b)) then s := -s; end if;
    if IsOdd(Degree(b)) and not IsSquare(LeadingCoefficient(a)) then s := -s; end if;
    if IsOdd(Degree(a)) and not IsSquare(LeadingCoefficient(b)) then s := -s; end if;
    tmp:= b; b:= a; a:= tmp mod a;
  end while;
  if IsOdd(Degree(b)) and not IsSquare(F ! a) then s:= -s; end if;
 
  return s;
end intrinsic;

intrinsic PowerSumsOfRoots(f::RngUPolElt, n::RngIntElt) -> SeqEnum
{ Sequence containing the sums of the 1st, 2nd,.., nth powers of the roots
  of monic polynomial f }

    d := Degree(f);
    require IsMonic(f) and (d gt 0) : "First argument must be a monic polynomial of positive degree";
    require n gt 0 : "Second argument must be a positive integer";

    cs := Reverse(Prune(Coefficients(f)));
    pseq := [-cs[1]];
    for r in [2..Min(d,n)] do
	Append(~pseq,-((r*cs[r]) + &+[cs[i]*pseq[r-i] : i in [1..r-1]]));
    end for;
    for r in [d+1..n] do
	Append(~pseq,-&+[cs[i]*pseq[r-i] : i in [1..d]]);
    end for;
    return pseq;

end intrinsic;

intrinsic PowerSumOfRoots(f::RngUPolElt, n::RngIntElt) -> RngElt
{ The sum of the nth powers of the roots of monic polynomial f }

    d := Degree(f);
    require IsMonic(f) and (d gt 0) : "First argument must be a monic polynomial of positive degree";
    require n gt 0 : "Second argument must be a positive integer";

    return PowerSumsOfRoots(f,n)[n];

end intrinsic;
     
