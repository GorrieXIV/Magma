freeze;

intrinsic IsInertial(g::RngUPolElt) -> BoolElt
{Returns true if the polynomial g is inertial.}

    L := CoefficientRing(Parent(g));
    require Type(L) in {RngPadRes, RngPadResExt, RngPad, FldPad, RngSerPow, RngSerLaur, RngSerExt}:
			"Coefficient ring must be a local ring or field";

    if Degree(g) le 1 then
	return false;
    end if;

    // Cannot use IsField() for this test since:
    //
    //   IsField(pAdicRing(p, 1));
    //
    // returns true

    if Type(L) in {FldPad, RngSerLaur} or 
                        (Type(L) eq RngSerExt and IsField(L)) then
	L := Integers(L);
    end if;

    R, m := ResidueClassField(L);
    P := PolynomialRing(R);
    m := hom<Parent(g) -> P | Coercion(CoefficientRing(g), L)*m*Coercion(R, P), P.1>;
    return IsIrreducible(m(g)); 
end intrinsic;

intrinsic IsEisenstein(g::RngUPolElt) -> BoolElt
{Returns true if the polynomial g is Eisenstein.}

    L := CoefficientRing(Parent(g));
    require Type(L) in {RngPadRes, RngPadResExt, RngPad, FldPad, RngSerPow, RngSerLaur, RngSerExt}:
			"Coefficient ring must be a local ring or field";

    if not IsUnit(LeadingCoefficient(g)) then
	return false;
    end if;

    if Valuation(TrailingCoefficient(g)) ne 1 then
	return false;
    end if;

    for i in [1 .. Degree(g) - 1] do
	if Valuation(Coefficient(g, i)) lt 1 then
	    return false;
	end if;
    end for;

    return true;
end intrinsic;

intrinsic ShiftValuation(f::RngUPolElt[FldPad], n::RngIntElt) -> RngUPolElt
{Returns f * pi^n, where pi is the uniformizing element.}
    return elt<Parent(f) | [ShiftValuation(x, n) : x in Eltseq(f)]>;
end intrinsic;

intrinsic ShiftValuation(f::RngUPolElt[RngPad], n::RngIntElt) -> RngUPolElt
{Returns f * pi^n, where pi is the uniformizing element.}
    return elt<Parent(f) | [ShiftValuation(x, n) : x in Eltseq(f)]>;
end intrinsic;

intrinsic ShiftValuation(f::RngUPolElt[RngPadRes], n::RngIntElt) -> RngUPolElt
{Returns f * pi^n, where pi is the uniformizing element.}
    return elt<Parent(f) | [ShiftValuation(x, n) : x in Eltseq(f)]>;
end intrinsic;

intrinsic ShiftValuation(f::RngUPolElt[RngPadResExt], n::RngIntElt) -> RngUPolElt
{Returns f * pi^n, where pi is the uniformizing element.}
    return elt<Parent(f) | [ShiftValuation(x, n) : x in Eltseq(f)]>;
end intrinsic;

intrinsic ShiftValuation(~f::RngUPolElt[FldPad], n::RngIntElt)
{Returns f * pi^n, where pi is the uniformizing element.}
    f := elt<Parent(f) | [ShiftValuation(x, n) : x in Eltseq(f)]>;
end intrinsic;

intrinsic ShiftValuation(~f::RngUPolElt[RngPad], n::RngIntElt)
{Returns f * pi^n, where pi is the uniformizing element.}
    f := elt<Parent(f) | [ShiftValuation(x, n) : x in Eltseq(f)]>;
end intrinsic;

intrinsic ShiftValuation(~f::RngUPolElt[RngPadRes], n::RngIntElt)
{Returns f * pi^n, where pi is the uniformizing element.}
    f := elt<Parent(f) | [ShiftValuation(x, n) : x in Eltseq(f)]>;
end intrinsic;

intrinsic ShiftValuation(~f::RngUPolElt[RngPadResExt], n::RngIntElt)
{Returns f * pi^n, where pi is the uniformizing element.}
    f := elt<Parent(f) | [ShiftValuation(x, n) : x in Eltseq(f)]>;
end intrinsic;

intrinsic InternalValuationsOfRoots(f::RngUPolElt) -> .
{Returns the valuations of roots, in increasing order.}
    return Sort([x[1]: x in ValuationsOfRoots(f)]);
end intrinsic;


intrinsic Basis(K::FldPad) -> []
  {The basis of the field over its coefficient field}
  n := Degree(K);
  return [K!Eltseq(m[i]) : i in [1..n]] 
     where m := IdentityMatrix(Integers(), n);
end intrinsic;

intrinsic Basis(R::RngPad) -> []
  {The basis of the ring over its coefficient ring}
  n := Degree(R);
  return [R!Eltseq(m[i]) : i in [1..n]] 
     where m := IdentityMatrix(Integers(), n);
end intrinsic;


intrinsic RelativeBasis(K::FldPad, k::FldPad) -> []
  {The k-basis of K, compatible with repeated Eltseq}
  B := Basis(K);
  if CoefficientRing(K) eq k then
    return B;
  else
    b := RelativeBasis(CoefficientRing(K), k);
    return [i*j : j in b, i in B];
  end if;
end intrinsic;

intrinsic AbsoluteBasis(K::FldPad) -> []
  {A Qp basis for K}
  return RelativeBasis(K, PrimeField(K));
end intrinsic;

intrinsic NormalBasisGenerator(K::FldPad) -> FldPadElt, RngIntElt
  {For a normal field K, computes a generator for a normal basis as well
    as the valuation of the index of the Z_p submodule generated by it in the ring of integers}
  A, mA := AutomorphismGroup(K);  
  repeat
    a := Random(Integers(K));
    b := [a@(x@mA) : x in A];
    b := Matrix(Integers(PrimeField(K)), [Flat(x) : x in b]);
    b := EchelonForm(b);
  until forall{x : x in [1..Ncols(b)] | not IsWeaklyZero(b[x][x])};
  return K!a, &+ [ Valuation(b[x][x]) : x in [1..Ncols(b)]], Maximum([ Valuation(b[x][x]) : x in [1..Ncols(b)]]);;
end intrinsic;    

intrinsic Flat(a::RngPadElt) -> []
  {The coefficients of the element over the prime ring}
  a := Eltseq(a);
  while Universe(a) ne PrimeRing(Universe(a)) do
    a := &cat [Eltseq(x) : x in a];
  end while;
  return a;
end intrinsic;  

intrinsic Flat(a::RngPadResElt) -> []
  {The coefficients of the element over the prime ring}
  return [a];
end intrinsic;

intrinsic Flat(a::RngPadResExtElt) -> []
  {"} // "
  return &cat [ Flat(x) : x in Eltseq(a)];
end intrinsic;

intrinsic Flat(a::FldPadElt) -> []
  {The coefficients of the element over the prime field.}
  a := Eltseq(a);
  while Universe(a) ne PrimeField(Universe(a)) do
    a := &cat [Eltseq(x) : x in a];
  end while;
  return a;
end intrinsic;  

intrinsic AbsoluteMinimalPolynomial(x::FldPadElt) -> RngUPolElt
  {The minimal polynomial of x over the prime field}
  return MinimalPolynomial(x, PrimeField(Parent(x)));
end intrinsic;

intrinsic Generators(K::FldPad) -> []
  {Algebra (field) generators over the prime field.}
  g := [];
  R := K;
  repeat
    Append(~g, K!R.1);
    R := BaseRing(R);
  until PrimeField(K) cmpeq R;
  return g;
end intrinsic;

intrinsic RelativeBasis(R::RngPad, S::RngPad) -> []
  {An S-basis for R}
  R`DefaultPrecision;
  if S cmpeq CoefficientRing(R) then
    return Basis(R);
  end if;
  B := RelativeBasis(CoefficientRing(R), S);
  return [b*s : b in B, s in Basis(R)];
end intrinsic;

intrinsic AbsoluteDegree(F::FldPad) -> RngIntElt
  {The degree over the prime field}
  return Degree(F, PrimeField(F));
end intrinsic;

intrinsic IsRamified(F::FldPad) -> BoolElt
{Whether the F is a ramified extension of its base field};
    return RamificationIndex(F) gt 1;
end intrinsic;

intrinsic IsTotallyRamified(F::FldPad) -> BoolElt
{Whether the ramification index of F is equal to the degree of F};
    return RamificationIndex(F) eq Degree(F);
end intrinsic;

intrinsic IsUnramified(F::FldPad) -> BoolElt
{Whether F is a unramified extension of its base field};
    return RamificationDegree(F) eq 1;
end intrinsic;

intrinsic IsTamelyRamified(F::FldPad) -> BoolElt
{Whether F is not wildly ramified};
    return not IsWildlyRamified(F);
end intrinsic;

intrinsic IsWildlyRamified(F::FldPad) -> BoolElt
{Whether F is a wildly ramified extension of its base field};
    return RamificationDegree(F) mod Prime(F) eq 0;
end intrinsic;

intrinsic IsRamified(R::RngPad) -> BoolElt
{Whether R is a ramified extension of its base field};
    return RamificationIndex(R) gt 1;
end intrinsic;

intrinsic IsTotallyRamified(R::RngPad) -> BoolElt
{Whether the ramification index of R is equal to the degree of R};
    return RamificationIndex(R) eq Degree(R);
end intrinsic;

intrinsic IsUnramified(R::RngPad) -> BoolElt
{Whether R is an unramified extension of its base field};
    return RamificationDegree(R) eq 1;
end intrinsic;

intrinsic IsTamelyRamified(R::RngPad) -> BoolElt
{Whether R is not wildly ramified};
    return not IsWildlyRamified(R);
end intrinsic;

intrinsic IsWildlyRamified(R::RngPad) -> BoolElt
{Whether R is a wildly ramified extension of its base field};
    return RamificationDegree(R) mod Prime(R) eq 0;
end intrinsic;

intrinsic IsRamified(R::RngPadRes) -> BoolElt
{Whether R is a ramified extension of its base field};
    return RamificationIndex(R) gt 1;
end intrinsic;

intrinsic IsTotallyRamified(R::RngPadRes) -> BoolElt
{Whether the ramification index of R is equal to the degree of R};
    return RamificationIndex(R) eq Degree(R);
end intrinsic;

intrinsic IsUnramified(R::RngPadRes) -> BoolElt
{Whether R is an unramified extension of its base field};
    return RamificationDegree(R) eq 1;
end intrinsic;

intrinsic IsTamelyRamified(R::RngPadRes) -> BoolElt
{Whether R is not wildly ramified};
    return not IsWildlyRamified(R);
end intrinsic;

intrinsic IsWildlyRamified(R::RngPadRes) -> BoolElt
{Whether R is a wildly ramified extension of its base field};
    return RamificationDegree(R) mod Prime(R) eq 0;
end intrinsic;

intrinsic IsRamified(R::RngPadResExt) -> BoolElt
{Whether R is a ramified extension of its base field};
    return RamificationIndex(R) gt 1;
end intrinsic;

intrinsic IsTotallyRamified(R::RngPadResExt) -> BoolElt
{Whether the ramification index of R is equal to the degree of R};
    return RamificationIndex(R) eq Degree(R);
end intrinsic;

intrinsic IsUnramified(R::RngPadResExt) -> BoolElt
{Whether R is an unramified extension of its base field};
    return RamificationDegree(R) eq 1;
end intrinsic;

intrinsic IsTamelyRamified(R::RngPadResExt) -> BoolElt
{Whether R is not wildly ramified};
    return not IsWildlyRamified(R);
end intrinsic;

intrinsic IsWildlyRamified(R::RngPadResExt) -> BoolElt
{Whether R is a wildly ramified extension of its base field};
    return RamificationDegree(R) mod Prime(R) eq 0;
end intrinsic;




intrinsic FrobeniusAutomorphism(R::RngPad) -> Map
  {The Frobenius of R}
  return map<R->R | x :-> GaloisImage(x, 1), y:->GaloisImage(y, -1)>;  
end intrinsic;

intrinsic FrobeniusAutomorphism(R::FldPad) -> Map
  {"} // "
  return map<R->R | x :-> GaloisImage(x, 1), y:->GaloisImage(y, -1)>;  
end intrinsic;

intrinsic FrobeniusAutomorphism(R::RngPadRes) -> Map
  {"} // "
  return map<R->R | x :-> GaloisImage(x, 1), y:->GaloisImage(y, -1)>;  
end intrinsic;

intrinsic FrobeniusAutomorphism(R::RngPadResExt) -> Map
  {"} // "
  return map<R->R | x :-> GaloisImage(x, 1), y:->GaloisImage(y, -1)>;  
end intrinsic;

intrinsic FrobeniusMap(R::RngPad) -> Map
  {"} // "
  return map<R->R | x :-> GaloisImage(x, 1), y:->GaloisImage(y, -1)>;  
end intrinsic;

intrinsic FrobeniusMap(R::FldPad) -> Map
  {"} // "
  return map<R->R | x :-> GaloisImage(x, 1), y:->GaloisImage(y, -1)>;  
end intrinsic;

intrinsic FrobeniusMap(R::RngPadRes) -> Map
  {"} // "
  return map<R->R | x :-> GaloisImage(x, 1), y:->GaloisImage(y, -1)>;  
end intrinsic;

intrinsic FrobeniusMap(R::RngPadResExt) -> Map
  {"} // "
  return map<R->R | x :-> GaloisImage(x, 1), y:->GaloisImage(y, -1)>;  
end intrinsic;

intrinsic FrobeniusAutomorphism(R::RngPad, i::RngIntElt) -> Map
  {The i-th power of the Frobenius of R}
  return map<R->R | x :-> GaloisImage(x, i), y:->GaloisImage(y, -i)>;  
end intrinsic;

intrinsic FrobeniusAutomorphism(R::FldPad, i::RngIntElt) -> Map
  {"} // "
  return map<R->R | x :-> GaloisImage(x, i), y:->GaloisImage(y, -i)>;  
end intrinsic;

intrinsic FrobeniusAutomorphism(R::RngPadRes, i::RngIntElt) -> Map
  {"} // "
  return map<R->R | x :-> GaloisImage(x, i), y:->GaloisImage(y, -i)>;  
end intrinsic;

intrinsic FrobeniusAutomorphism(R::RngPadResExt, i::RngIntElt) -> Map
  {"} // "
  return map<R->R | x :-> GaloisImage(x, i), y:->GaloisImage(y, -i)>;  
end intrinsic;

intrinsic FrobeniusMap(R::RngPad, i::RngIntElt) -> Map
  {"} // "
  return map<R->R | x :-> GaloisImage(x, i), y:->GaloisImage(y, -i)>;  
end intrinsic;

intrinsic FrobeniusMap(R::FldPad, i::RngIntElt) -> Map
  {"} // "
  return map<R->R | x :-> GaloisImage(x, i), y:->GaloisImage(y, -i)>;  
end intrinsic;
intrinsic FrobeniusMap(R::RngPadRes, i::RngIntElt) -> Map
  {"} // "
  return map<R->R | x :-> GaloisImage(x, i), y:->GaloisImage(y, -i)>;  
end intrinsic;
intrinsic FrobeniusMap(R::RngPadResExt, i::RngIntElt) -> Map
  {"} // "
  return map<R->R | x :-> GaloisImage(x, i), y:->GaloisImage(y, -i)>;  
end intrinsic;

intrinsic FrobeniusImage(x::RngPadElt) -> RngPadElt
  {The image of x under the Frobenius}
  return GaloisImage(x, 1);
end intrinsic;

intrinsic FrobeniusImage(x::FldPadElt) -> FldPadElt
  {"} // "
  return GaloisImage(x, 1);
end intrinsic;

intrinsic FrobeniusImage(x::RngPadResElt) -> RngPadResElt
  {"} // "
  return GaloisImage(x, 1);
end intrinsic;

intrinsic FrobeniusImage(x::RngPadResExtElt) -> RngPadResExtElt
  {"} // "
  return GaloisImage(x, 1);
end intrinsic;

intrinsic FrobeniusImage(x::RngPadElt, i::RngIntElt) -> RngPadElt
  {The image of x under the i-th power of the Frobenius}
   return GaloisImage(x, i);
end intrinsic;

intrinsic FrobeniusImage(x::FldPadElt, i::RngIntElt) -> FldPadElt
  {"} // "
   return GaloisImage(x, i);
end intrinsic;
intrinsic FrobeniusImage(x::RngPadResElt, i::RngIntElt) -> RngPadResElt
  {"} // "
   return GaloisImage(x, i);
end intrinsic;
intrinsic FrobeniusImage(x::RngPadResExtElt, i::RngIntElt) -> RngPadResExtElt
  {"} // "
   return GaloisImage(x, i);
end intrinsic;

intrinsic VerschiebungMap(R::RngPad) -> Map
  {The Verschiebungs map for R unramified}
  require IsUnramified(R): "Verschiebung is only defined for unramified rings";
  p := UniformizingElement(BaseRing(R));
  return map<R ->R | x:->GaloisImage(p*x, -1)>;
end intrinsic;

intrinsic VerschiebungMap(R::FldPad) -> Map
  {"} // "
  require IsUnramified(R): "Verschiebung is only defined for unramified rings";
  p := UniformizingElement(BaseRing(R));
  return map<R ->R | x:->GaloisImage(p*x, -1)>;
end intrinsic;

intrinsic VerschiebungMap(R::RngPadRes) -> Map
  {"} // "
  require IsUnramified(R): "Verschiebung is only defined for unramified rings";
  p := UniformizingElement(BaseRing(R));
  return map<R ->R | x:->GaloisImage(p*x, -1)>;
end intrinsic;

intrinsic VerschiebungMap(R::RngPadResExt) -> Map
  {"} // "
  require IsUnramified(R): "Verschiebung is only defined for unramified rings";
  p := UniformizingElement(BaseRing(R));
  return map<R ->R | x:->GaloisImage(p*x, -1)>;
end intrinsic;

intrinsic VerschiebungImage(x::RngPadElt) -> RngPadElt
  {The image of x under the Verschiebung map}
  R := Parent(x);
  require IsUnramified(R): "Verschiebung is only defined for unramified rings";
  p := UniformizingElement(BaseRing(R));
  return GaloisImage(p*x, -1);
end intrinsic;
    
intrinsic VerschiebungImage(x::FldPadElt) -> FldPadElt
  {"} // "
  R := Parent(x);
  require IsUnramified(R): "Verschiebung is only defined for unramified rings";
  p := UniformizingElement(BaseRing(R));
  return GaloisImage(p*x, -1);
end intrinsic;
     
intrinsic VerschiebungImage(x::RngPadResElt) -> RngPadResElt
  {"} // "
  R := Parent(x);
  require IsUnramified(R): "Verschiebung is only defined for unramified rings";
  p := UniformizingElement(BaseRing(R));
  return GaloisImage(p*x, -1);
end intrinsic;
    
 
intrinsic VerschiebungImage(x::RngPadResExtElt) -> RngPadResExtElt
  {"} // "
  R := Parent(x);
  require IsUnramified(R): "Verschiebung is only defined for unramified rings";
  p := UniformizingElement(BaseRing(R));
  return GaloisImage(p*x, -1);
end intrinsic;
    

intrinsic SetPrecision(K::FldPad, n::RngIntElt)
  {Sets the precision of K to n and ensures that the precision of the coefficient ring is adjusted as well}

  e := RamificationDegree(K, PrimeField(K));
  if Precision(K) eq Infinity() then
    K`DefaultPrecision := n;
  else
    return;
  end if;
  R := CoefficientRing(K);
  repeat
    R`DefaultPrecision := (K`DefaultPrecision + e-1) div e
                                 where e := RamificationDegree(K, R);
    R := CoefficientRing(R);
  until R eq PrimeField(R);
  R`DefaultPrecision := (K`DefaultPrecision + e-1) div e
                                 where e := RamificationDegree(K, R);

end intrinsic;

intrinsic SetPrecision(K::RngPad, n::RngIntElt)
  {"} // "

  if Precision(K) ne Infinity() then
    return;
  end if;
  e := RamificationDegree(K, PrimeRing(K));
  K`DefaultPrecision := n;
  R := CoefficientRing(K);
  repeat
    R`DefaultPrecision := (K`DefaultPrecision + e-1) div e
                                 where e := RamificationDegree(K, R);
    R := CoefficientRing(R);
  until R eq PrimeRing(R);
  R`DefaultPrecision := (K`DefaultPrecision + e-1) div e
                                 where e := RamificationDegree(K, R);

end intrinsic;

/************************************************************************/
Z:=Integers();
function dwork_it(x,K) return InternalDworkGamma(K!x); end function;
/*
 p:=Prime(K); pr:=Precision(K)+Valuation(x)+1; n:=pr; u:=(n div p);
 while n-u lt pr do n:=pr+u;
  u:=&+[n div (p^e) : e in [1..Ilog(p,n)]]; end while; pr:=n;
 K:=pAdicField(p,pr);
 r:=K!1; x:=K!Z!x; A:=[K!0: i in [1..p]]; A[1]:=r; r2:=r;
 for u in [1..(p-1)] do A[u+1]:=A[u]/u; end for;
 for u in [1..(pr-1)] do A[1]:=(A[1]+A[p])/(u*p);
  for v in [1..(p-1)] do A[v+1]:=(A[v]+A[v+1])/(v+u*p); end for;
  r2:=r2*(x+u-1); r:=r+r2*A[1]*p^u; end for; return -r; end function;
*/

function external_dwork(x,K) "EXTERNAL DWORK";
 p:=Prime(K); pr:=Precision(K)+Valuation(x)+1;
 gb:=2*(pr div p); printf "Prime %o prec %o guardbits %o\n",p,pr,gb;
 R:=pAdicQuotientRing(p,pr+gb);
 r:=R!1; x:=R!Z!x; A:=[R!0: i in [1..p]]; r2:=r; r:=r*p^gb; A[1]:=r;
 for u in [1..(p-1)] do A[u+1]:=A[u] div u; end for;
 for e in [1..(pr+gb-1)] do A[1]:=(A[1]+A[p]) div e;
  for v in [1..(p-1)] do A[v+1]:=(A[v]+p*A[v+1]) div (v+e*p); end for;
  r2:=r2*(x+e-1); r:=r+r2*A[1]; end for; r:=r div (p^gb); return -r;
 end function;

function padic_gamma_dwork(x,K) p:=Prime(K); u:=(Integers()!x) mod p;
 // r:=external_dwork((x-u)/p,K);
 pr:=Precision(K); R:=pAdicQuotientRing(p,pr);
 r:=R!InternalNewDwork(Z!((x-u)/p),p,pr);
 if u mod 2 eq 0 then r:=-r; end if;
 r:=r*&*[Parent(r)|Parent(r)!(x-u+i) : i in [1..(u-1)]];
 return Parent(x)!Z!r; end function;

function padic_gamma_morita(n,K) p:=Prime(K); // "MORITA";
 R:=pAdicQuotientRing(p,Precision(K)); // do everything in R
 return Z!((-1)^n*&*[R | R!i : i in [1..(n-1)] | i mod p ne 0]); end function;

function padic_gamma(x) assert Valuation(x) ge 0; K:=Parent(x);
 p:=Prime(K); v:=AbsolutePrecision(x);
 o:=v; if p eq 2 and o eq 2 then o:=1; end if; O:=pAdicField(p,o);
 if p eq 2 then v:=v+1; end if; L:=pAdicField(p,v); x:=ChangePrecision(L!x,v);
 a:=Z!x; if a lt 0 then a:=a+p^v; end if;
 b:=Z!(-x); if b lt 0 then b:=b+p^v; end if;
 if a gt p*v and b gt p*v then return O!padic_gamma_dwork(x,L); end if;
 if b lt a then return O!((-1)^(1+b+(b div p))/padic_gamma_morita(b+1,L));
 else return O!padic_gamma_morita(a,L); end if; end function;

intrinsic Gamma(x::FldPadElt) -> FldPadElt
{Compute the p-adic Gamma function}
 require Valuation(x) ge 0: "Must have nonnegative valuation";
 require Degree(Parent(x)) eq 1: "Must be over Qp, not an extension";
 K:=pAdicField(Prime(Parent(x)),AbsolutePrecision(x));
 return K!padic_gamma(x); end intrinsic;

intrinsic Gamma(x::RngPadElt) -> RngPadElt
{Compute the p-adic Gamma function}
 require Degree(Parent(x)) eq 1: "Must be over Qp, not an extension";
 K:=pAdicField(Prime(Parent(x)),AbsolutePrecision(x));
 return K!Gamma(FieldOfFractions(Parent(x))!x); end intrinsic;
