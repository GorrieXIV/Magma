
freeze;

Z:=Integers(); Q:=Rationals();

import "identify_t1.m" : identify_t1;

intrinsic KroneckerCharacter(D::FldRatElt) -> GrpDrchElt
{The Kronecker character (D/n)}
 require D ne 0: "Cannot have KroneckerCharacter of 0";
 return KroneckerCharacter(Numerator(D)*Denominator(D)); end intrinsic;

intrinsic IdentifyKroneckerCharacter(chi::GrpDrchElt) -> RngIntElt
{Given a real Dirichlet character (over Q), identify it as a Kronecker char }
 chi:=AssociatedPrimitiveCharacter(chi);
 require Order(chi) le 2: "Must be quadratic";
 if Order(chi) eq 1 then return 1; end if; C:=Conductor(chi);
 return chi eq KroneckerCharacter(C) select C else -C; end intrinsic;

intrinsic ArtinRepresentationQuadratic(d::RngQZElt) -> ArtRep
{Return the Artin representation corresponding to the character given by d}
 require d ne 0: "Discriminant cannot be 0";
 if IsSquare(d) then return ArtinRepresentations(Rationals())[1]; end if;
 x:=PolynomialRing(Rationals()).1;
 return ArtinRepresentations(NumberField(x^2-d))[2]; end intrinsic;

////////////////////////////////////////////////////////////////////////

ArtRepQuad:=ArtinRepresentationQuadratic;

function perm_char(F) // permutation character of an algebra
 return &+[PermutationCharacter(NumberField(f[1])) : f in Factorization(F)];
 end function;

function get_art_rep(X,t)
 if #X`Glist eq 3 then a:=-X`Glist[1]; b:=-X`Glist[2]; e:=Gcd(a,b);
  M:=MValue(X); u:=1/M/t; if a lt 0 then a:=-a; b:=-b; u:=1/u; end if;
  x:=PolynomialRing(Rationals()).1; // above: swap of alpha/beta
  return Minimize(perm_char(x^a*(1-x)^b-u)-perm_char(x^e-u)); end if;
 H:=Twist(X);
 if #H`Glist eq 3 then M:=MValue(H);
  if IsOdd(#X`alpha) then u:=t; tw:=-M; else u:=t; tw:=M; end if;
  _,tw:=Valuation(tw,2); tw:=Numerator(tw)*Denominator(tw);
  tw:=Sign(tw)*&*[Z|f[1]^(f[2] mod 2) : f in Factorization(tw)];
  return Minimize(ArtinRepresentation(H,u)*ArtRepQuad(tw*t)); end if;
 // non-Belyi case(s)
 if X`Glist eq [* 1,-2,-3,-4,8 *] then x:=PolynomialRing(Rationals()).1;
  M:=MValue(X); u:=1/M/t; psi:=perm_char(u^3*x^6*(1-u*x^2)-64*u);
  chi:=perm_char(x^3*(1-x)-64*u); return Minimize(psi-chi); end if;
 if X`Glist eq [* -1,2,3,4,-8 *] then
  return get_art_rep(SwapAlphaBeta(X),1/t); end if;
 if H`Glist eq [* 1,-2,-3,-4,8 *] then u:=t; tw:=MValue(H);
  _,tw:=Valuation(tw,2); tw:=Numerator(tw)*Denominator(tw);
  tw:=Sign(tw)*&*[Z|f[1]^(f[2] mod 2) : f in Factorization(tw)];
  return Minimize(ArtinRepresentation(H,u)*ArtRepQuad(tw*t)); end if;
 if H`Glist eq [* -1,2,3,4,-8 *] then
  return get_art_rep(SwapAlphaBeta(X),1/t); end if;
 return false; end function;

procedure art_rep_check(R,H,t) P:=PrimesInInterval(2,100);
 Q:=Set(P) diff Set(PrimeDivisors(Numerator(t)));
 Q:=Set(Q) diff Set(PrimeDivisors(Denominator(t)));
 if t ne 1 then Q:=Set(Q) diff Set(PrimeDivisors(Numerator(t-1))); end if;
 Q:=Set(Q) diff
    Set(PrimeDivisors(LCM([Denominator(x) : x in H`alpha cat H`beta])));
 Q:=Sort(SetToSequence(Q));
 A:=[EulerFactor(H,t,p) : p in Q]; B:=[EulerFactor(R,p : R:=Z) : p in Q];
 assert A eq B; end procedure;

intrinsic ArtinRepresentation(X::HypGeomData,t::RngQZElt:Check:=true)->ArtRep
{Given a weight 0 hypergeometric motive specialised at t, return the
 corresponding Artin representation (if known). Checks primes up to 100.}
 require t ne 0 and t ne 1: "t must be neither 0 nor 1"; t:=Rationals()!t;
 require X`weight eq 0: "Hypergeometric motive must be weight 0";
 A:=get_art_rep(X,t); // Minimize?
 if Type(A) eq BoolElt then
  require false: "Hypergeometric data not known as an Artin rep"; end if;
 if Check then art_rep_check(A,X,t); end if; return A; end intrinsic;

////////////////////////////////////////////////////////////////////////

AEC:=AssociativeArray(); EC:=EllipticCurve;
AEC[[[2,2],[1,1]]]:=func<a|EC([1,a,a,0,0])>;
AEC[[[3],[1,1]]]:=func<a|EC([1,0,a,0,0])>;
AEC[[[4],[1,1]]]:=func<a|EC([1,0,0,a,0])>;
AEC[[[6],[1,1]]]:=func<a|EC([1,0,0,0,-a])>;
AEC[[[2,2],[3]]]:=func<a|EC([0,-a,-a,0,0])>;
AEC[[[2,2],[4]]]:=func<a|EC([0,-a,0,a,0])>;
AEC[[[2,2],[6]]]:=func<a|EC([0,-a/4,0,a/2,-a/4])>;
AEC[[[3],[4]]]:=func<a|EC([0,0,-a,-a,0])>;
AEC[[[3],[6]]]:=func<a|EC([0,0,0,-3*a,4*a+a^2/4])>;;
AEC[[[4],[6]]]:=func<a|EC([0,0,0,-a,a])>;

function hypergeom_crvell_deg2(X,t) U:=[X`cycA,X`cycB]; V:=[X`cycB,X`cycA];
 if IsDefined(AEC,U) then return AEC[U](1/X`Mvalue/t); end if;
 if IsDefined(AEC,V) then return AEC[V](X`Mvalue*t); end if;
 assert false; end function;

function ec_gen(X,t) F:=Parent(t); P:=PolynomialRing(F); y:=P.1;
 _,d:=IsPrimitive(X); H:=PrimitiveData(X);
 U:=[H`cycA,H`cycB]; V:=[H`cycB,H`cycA];
 if IsDefined(AEC,U) then u:=1/(X`Mvalue*t); FAC:=Factorization(y^d-u);
  if F cmpeq Q then Ks:=[* ext<F|f[1] : DoLinearExtension> : f in FAC *];
  else Ks:=[* ext<F|f[1]> : f in FAC *]; end if;
  Vs:=[* Degree(K) eq 1 select -Coefficient(DefiningPolynomial(K),0)
                         else K.1 : K in Ks *];
  Es:=[* AEC[U](e) : e in Vs *];
 else IsDefined(AEC,V); u:=X`Mvalue*t; FAC:=Factorization(y^d-u);
  if F cmpeq Q then Ks:=[* ext<F|f[1] : DoLinearExtension> : f in FAC *];
  else Ks:=[* ext<F|f[1]> : f in FAC *]; end if;
  Vs:=[* Degree(K) eq 1 select -Coefficient(DefiningPolynomial(K),0)
                         else K.1 : K in Ks *];
  Es:=[* AEC[V](e) : e in Vs *]; end if;
 assert assigned Es; return #Es eq 1 select Es[1] else Es; end function;

procedure check_ec(C,H,t) P:=PrimesInInterval(2,50); // curtail deg in Euler?
 if Type(C) ne List then C:=[* C *]; end if; // hack
 Q:=Set(P) diff Set(PrimeDivisors(Numerator(t)));
 Q:=Set(Q) diff Set(PrimeDivisors(Denominator(t)));
 if t ne 1 then Q:=Set(Q) diff Set(PrimeDivisors(Numerator(t-1))); end if;
 Q:=Set(Q) diff
    Set(PrimeDivisors(LCM([Denominator(x) : x in H`alpha cat H`beta])));
 Q:=Sort(SetToSequence(Q));
 A:=[EulerFactor(H,t,p) : p in Q]; B:=[&*[EulerFactor(c,p) : c in C] : p in Q];
 assert A eq B; end procedure;

intrinsic EllipticCurve(X::HypGeomData,t::RngQZElt : Check:=false) -> CrvEll
{Given suitable hypergeometric data (of weight 1 and imprimitivity=degree/2),
 return the associated elliptic curve specialized at t.
 Returns a list of curves when the algebra splits.}
 require t ne 0 and t ne 1: "t must be neither 0 nor 1"; t:=Rationals()!t;
 require Weight(X) eq 1: "Weight must be 1"; _,g:=IsPrimitive(X);
 require Degree(X) eq 2*g: "Imprimitivity must be half the degree";
 if Degree(X) eq 2 and Weight(X) eq 1 then E:=hypergeom_crvell_deg2(X,t);
 else E:=ec_gen(X,t); end if; if Check then check_ec(E,X,t); end if;
 return E; end intrinsic;

intrinsic EllipticCurve(X::HypGeomData) -> CrvEll
{Given suitable hypergeometric data (of weight 1 and imprimitivity=degree/2),
 return the associated elliptic curve (over a function field).}
 require Weight(X) eq 1: "Weight must be 1"; _,g:=IsPrimitive(X);
 require Degree(X) eq 2*g: "Imprimitivity must be half the degree";
 if Degree(X) eq 2 and Weight(X) eq 1 then
  return hypergeom_crvell_deg2(X,FunctionField(Rationals()).1); end if;
 return ec_gen(X,FunctionField(Rationals()).1); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic HyperellipticCurve(S::SeqEnum) -> CrvHyp
{Given a sequence of coefficients, construct a hyperelliptic curve}
 return HyperellipticCurve(Polynomial(Reverse(S))); end intrinsic;

procedure check_hc(C,H,t) P:=PrimesInInterval(2,50);
 Q:=Set(P) diff Set(PrimeDivisors(Numerator(t)));
 Q:=Set(Q) diff Set(PrimeDivisors(Denominator(t)));
 if t ne 1 then Q:=Set(Q) diff Set(PrimeDivisors(Numerator(t-1))); end if;
 Q:=Set(Q) diff
    Set(PrimeDivisors(LCM([Denominator(x) : x in H`alpha cat H`beta])));
 Q:=Sort(SetToSequence(Q));
 A:=[EulerFactor(H,t,p) : p in Q]; B:=[EulerFactor(C,p) : p in Q];
 assert A eq B; end procedure;

procedure mf_elt_check(f,H,t) P:=PrimesInInterval(2,100);
 Q:=Set(P) diff Set(PrimeDivisors(Numerator(t)));
 Q:=Set(Q) diff Set(PrimeDivisors(Denominator(t)));
 if t ne 1 then Q:=Set(Q) diff Set(PrimeDivisors(Numerator(t-1))); end if;
 Q:=Set(Q) diff
    Set(PrimeDivisors(LCM([Denominator(x) : x in H`alpha cat H`beta])));
 Q:=Sort(SetToSequence(Q));
 L:=LSeries(f); B:=[EulerFactor(L,p) : p in Q];
 A:=[EulerFactor(H,t,p) : p in Q]; assert A eq B; end procedure;

AHC:=AssociativeArray(); HC:=HyperellipticCurve;

AHC[[[3,6],[1,1,4]]]:=func<a|HC([1,2,1,0,0,0,-4*a])>;
AHC[[[5],[1,1,4]]]:=func<a|HC([1,2,1,0,0,-4*a,-4*a])>;
AHC[[[8],[1,1,3]]]:=func<a|HC([4,1,0,0,4*a,0])>;
AHC[[[5],[1,1,3]]]:=func<a|HC([1,2,1,0,0,4*a,0])>;
AHC[[[4,4],[1,1,3]]]:=func<a|HC([4,1,8*a,0,4*a^2,0])>;
AHC[[[2,2,4],[1,1,3]]]:=func<a|HC([1,2,1,0,4*a,4*a,0])>;
AHC[[[5],[1,1,2,2]]]:=func<a|HC([4,1,0,-2*a,0,a^2])>;
AHC[[[3,4],[1,1,2,2]]]:=func<a|HC([4,1,-4*a,-2*a,0,a^2])>;
AHC[[[5],[8]]]:=func<a|HC([1,4,0,0,0,-4*a,0])>;
AHC[[[5],[3,6]]]:=func<a|HC([1,0,0,0,0,-4*a,4*a])>;
AHC[[[5],[2,2,6]]]:=func<a|HC([4,0,0,-4*a,0,a^2])>;
AHC[[[3,3],[2,2,6]]]:=func<a|HC([1,4,0,-2*a,-4*a,0,a^2])>;
AHC[[[4,4],[5]]]:=func<a|HC([4,0,-8*a,0,4*a^2,a^2])>;
AHC[[[3,4],[5]]]:=func<a|HC([4,0,-4*a,0,0,a^2])>;
AHC[[[2,2,4],[5]]]:=func<a|HC([1,0,0,0,-4*a,4*a,0])>;
AHC[[[3,3],[5]]]:=func<a|HC([1,4,0,-2*a,0,0,a^2])>;
AHC[[[3,3],[2,2,4]]]:=func<a|HC([1,0,0,2*a,-4*a,0,a^2])>;
AHC[[[3,3],[1,1,2,2]]]:=func<a|HC([1,2,1,2*a,-2*a,0,a^2 ])>;
AHC[[[8],[1,1,4]]]:=func<a|HC([4,1,0,0,-16*a,-4*a])>;
AHC[[[4,6],[1,1,3]]]:=func<a|HC([4/a,0,-16,1,0,-4*a])>;
AHC[[[2,2,6],[1,1,3]]]:=func<a|HC([4,1,0,16*a,4*a,0])>;
AHC[[[5],[10]]]:=func<a|HC([1,2,0,0,0,a/8,a/4])>;

ATC:=AssociativeArray();
ATC[[[2,2,4],[3,6]]]:=func<t|-t>;
ATC[[[2,2,4],[10]]]:=func<t|-5*t>;
ATC[[[2,2,6],[8]]]:=func<t|-3*t>;
ATC[[[2,2,6],[10]]]:=func<t|-15*t>;
ATC[[[4,4],[2,2,6]]]:=func<t|-3*t>;
ATC[[[2,2,6],[1,1,4]]]:=func<t|3*t>;
ATC[[[10],[1,1,2,2]]]:=func<t|5*t>;
ATC[[[4,6],[1,1,2,2]]]:=func<t|3*t>;
ATC[[[8],[10]]]:=func<t|5*t>;
ATC[[[3,6],[10]]]:=func<t|5*t>;
ATC[[[10],[1,1,3]]]:=func<t|-15*t>;
ATC[[[6,6],[1,1,3]]]:=func<t|-3*t>;
ATC[[[4,4],[10]]]:=func<t|5*t>;
ATC[[[4,6],[10]]]:=func<t|15*t>;
ATC[[[10],[1,1,4]]]:=func<t|-5*t>;
ATC[[[6,6],[10]]]:=func<t|5*t>;
ATC[[[6,6],[1,1,4]]]:=func<t|-t>;
ATC[[[6,6],[1,1,2,2]]]:=func<t|t>;
ATC[[[2,2,4],[8]]]:=func<t|-t>;
ATC[[[3,4],[2,2,6]]]:=func<t|-t>;

function hyperell_curve(X,t) U:=[X`cycA,X`cycB]; V:=[X`cycB,X`cycA];
 if IsDefined(AHC,U) then return AHC[U](1/X`Mvalue/t); end if;
 if IsDefined(AHC,V) then return AHC[V](X`Mvalue*t); end if;
 if IsDefined(ATC,U) then
  return QuadraticTwist(hyperell_curve(Twist(X),t),ATC[U](t)); end if;
 if IsDefined(ATC,V) then
  return QuadraticTwist(hyperell_curve(Twist(X),t),ATC[V](t)); end if;
 return false; end function;

intrinsic HyperellipticCurve(H::HypGeomData) -> CrvHyp
{Given suitable hypergeometric data, return the associated
 hyperelliptic curve (over a function field). If not known, return false.}
 require Degree(H) eq 4 and Weight(H) eq 1: "Degree must be 4 and weight 1";
 t:=FunctionField(Rationals()).1; return hyperell_curve(H,t); end intrinsic;

intrinsic HyperellipticCurve
  (H::HypGeomData,t::RngQZElt : Check:=true) -> CrvHyp
{Given suitable hypergeometric data, return the associated
 hyperelliptic curve at t. If not known, return false.}
 require Degree(H) eq 4 and Weight(H) eq 1: "Degree must be 4 and weight 1";
 require t ne 0 and t ne 1: "t must be neither 0 nor 1"; t:=Rationals()!t;
 C:=hyperell_curve(H,t); if Type(C) eq BoolElt then return false; end if;
 if Check then check_hc(C,H,t); end if; return C; end intrinsic;

function identify_it(H,t)
 if t eq 1 then return identify_t1(H); end if;
 if Weight(H) gt 1 then return false; end if;
 if Weight(H) eq 0 then return get_art_rep(H,t); end if; // Minimize?
 if Weight(H) eq 1 then _,g:=IsPrimitive(H);
  if 2*g eq Degree(H) then return EllipticCurve(H,t); end if;
  if Degree(H) ne 4 then return false; end if;
  T:=HyperellipticCurve(H,t); return T; end if; end function;

intrinsic Identify(H::HypGeomData,t::RngQZElt : Check:=false) -> Any
{Try to identify hypergeometric data at a given t as an associated object.
 Returns false if unable.}
 require t ne 0: "t must not be 0"; t:=Rationals()!t; O:=identify_it(H,t);
 if Type(O) eq BoolElt then return false; end if;
 if not Check then return O; end if; 
 if Type(O) eq CrvEll then check_ec(O,H,t); end if;
 if Type(O) eq CrvHyp then check_hc(O,H,t); end if;
 if Type(O) eq ArtRep then art_rep_check(O,H,t); end if;
 if Type(O) eq ModFrmElt then mf_elt_check(O,H,t); end if;
 return O; end intrinsic;

////////////////////////////////////////////////////////////////////////

function hgm_curve(X,t) G:=[x: x in GammaList(X)];
 F:=FieldOfFractions(Parent(t)); A:=AffineSpace(F,2); x:=A.1; y:=A.2;
 u:=1/(MValue(X)*t); if #G gt 6 then return false; end if;
 if #G eq 4 then
  if Sign(G[4]) ne Sign(G[1]) then G:=[Abs(x) : x in G]; assert G[4] gt 0;
   f:=x^G[1]*y^G[2]*(1-x-y)^G[3]-u; return Curve(A,f); end if;
  G:=[Abs(x) : x in G]; f:=x^G[4]*(1-x)^G[1]-y^G[3]*(1-y)^G[2]*u;
  return Curve(A,f); end if;
 for i in [1..5],j in [i+1..5] do
  if G[i]+G[j]+G[#G] eq 0 then ei:=G[i]; ej:=G[j];
   a:=Abs(G[i]); b:=Abs(G[j]); s1:=Sign(G[#G]);
   Exclude(~G,ei); Exclude(~G,ej); Exclude(~G,G[#G]);
   c:=Abs(G[1]); d:=Abs(G[2]); s2:=Sign(G[3]);
   if s1 eq -1 then assert s2 eq +1;
    f:=x^c*(1-x)^d-y^a*(1-y)^b*u; return Curve(A,f); end if;
   if s2 eq -1 then
    f:=x^a*(1-x)^b-y^c*(1-y)^d*u; return Curve(A,f); end if;
   f:=x^a*(1-x)^b*y^c*(1-y)^d-u; return Curve(A,f); end if; end for;
 return false; end function;

function canonical_scheme(X,t)
 G:=X`Glist; Gn:=[-x : x in G | x lt 0]; Gp:=[x : x in G | x gt 0];
 A:=AffineSpace(Parent(t),#Gp+#Gn);
 f1:=&+[A.i : i in [1..#Gn]]-1; f2:=&+[A.(#Gn+i) : i in [1..#Gp]]-1;
 f3:=&*[A.i^Gn[i] : i in [1..#Gn]]-
     &*[A.(#Gn+i)^Gp[i] : i in [1..#Gp]]/MValue(X)/t;
 return Scheme(A,[f1,f2,f3]); end function;

intrinsic CanonicalCurve(X::HypGeomData) -> Crv
{Returns a canonical plane curve (possibly reducible) associated to 
 the given hypergeometric data, or false if this is not possible}
 return hgm_curve(X,FunctionField(Rationals()).1); end intrinsic;

intrinsic CanonicalCurve(X::HypGeomData,t::RngQZElt) -> Crv
{Returns a canonical plane curve (possibly reducible) associated to 
 the given hypergeometric data specialised at t,
 or false if this is not possible}
 return hgm_curve(X,Rationals()!t); end intrinsic;

intrinsic CanonicalScheme(X::HypGeomData) -> Sch
{The canonical scheme associated to given hypergeometric data,
 returned over a function field}
 return canonical_scheme(X,FunctionField(Rationals()).1); end intrinsic;

intrinsic CanonicalScheme(X::HypGeomData,t::RngQZElt) -> Sch
{The canonical scheme associated to given hypergeometric data,
  specialized at a rational t.}
 return canonical_scheme(X,Rationals()!t); end intrinsic;
