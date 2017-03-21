
freeze;

declare type JacketMot;
declare attributes JacketMot: POS,NEG,m,MULT,deg,wt,tot_real,K,oo,HS,ew;
declare attributes JacketMot: t,rho,tate;

PSR:=PowerSeriesRing; FRAC:=FractionalPart;
Z:=Integers(); Q:=Rationals();

function element(q,A,u,m,G) A:=[FRAC(u*q*a) : a in A];
 e:=&+[G|G.(Z!(m*a)) : a in A]; return e; end function;

function mul(x,u,m,G) E:=Eltseq(x);
 POS:=&cat[[i/m : j in [1..E[i]] | E[i] gt 0] : i in [1..m-1]];
 NEG:=&cat[[i/m : j in [1..-E[i]] | E[i] lt 0] : i in [1..m-1]];
 return element(1,POS,u,m,G)-element(1,NEG,u,m,G); end function;
 
function get_scale(e1,e2,m,G)
 for u in [1..m] do if Gcd(u,m) ne 1 then continue; end if;
  if mul(e2[1],u,m,G) ne e1[1] then continue; end if;
  if e1[2] eq FRAC(e2[2]*u) then return u; end if; end for; assert false;
 end function;
 
function jacket_mot_ef(J,p : deg:=J`deg) assert J`m ne 1; // triv case
 f:=1; q:=p; while q mod J`m ne 1 do q:=q*p; f:=f+1; end while; // f-value
 m:=J`m; G:=FreeAbelianGroup(m);
 FULL:={<element(1,J`POS,u,m,G)-element(1,J`NEG,u,m,G),FRAC(J`rho*u)> :
        u in [1..m] | Gcd(u,m) eq 1}; assert #FULL eq J`deg;
 ORBITS:={{<mul(x[1],p^e,m,G),FRAC(x[2]*p^e)> : e in [1..f]} : x in FULL};
 REPS:={Random(o) : o in ORBITS}; // FULL,ORBITS,REPS;
 v:=J`deg div #ORBITS; S:=[<&+[mul(o[1],p^e,m,G) : e in [1..f]],
                            FRAC(&+[o[2]*p^e : e in [1..f]])> : o in REPS];
 // if Set(S) eq {<G!0,0>} then x:=PolynomialRing(Z).1; return 1-x^v; end if;
 E:=<element(1,J`POS,1,m,G)-element(1,J`NEG,1,m,G),FRAC(J`rho)>;
 E:=<&+[mul(E[1],p^e,m,G) : e in [1..f]],FRAC(&+[E[2]*p^e : e in [1..f]])>;
 S:=[<s[1],s[2],get_scale(<s[1],s[2]>,E,m,G)> : s in S];
 if v gt deg then return PSR(Z,deg+1)!1,_; end if;
 prec:=Ceiling(Log(2*Binomial(J`deg,J`deg div 2)*p^J`ew+1)/Log(p));
 if v eq J`deg then prec:=p eq 2 select 2 else 1; end if;
 if p eq 2 then prec:=prec+1; end if; // 2-adic gamma loses precision
 // printf "At prime %o, f is %o, internal deg is %o, prec is %o\n",p,f,v,prec;
 Kp:=pAdicField(p,prec); PR:=PolynomialRing(Kp); y:=PR.1;
 Tt:=Kp!TeichmuellerLift(GF(p)!J`t,pAdicQuotientRing(p,prec));
 G:=[Gamma(Kp!s/m) : s in [1..m-1]]; RES:=[]; sc:=f div v;
 // should use duplication and reflection formula for Gamma here
 for s in S do E:=Eltseq(s[1]); u:=Z!((&+[E[i]*i : i in [1..m-1]])/m/sc); // s;
  r:=(-p)^u*&*[Kp|G[i]^(E[i] div sc): i in [1..m-1] | E[i] ne 0];
  if J`rho ne 0 then r:=r*Tt^(Z!((q-1)*s[2])); end if; // Kummer twist
  RES cat:=[<s[3],r>]; end for; // RES has roots and scalings
 ROO:=[-r[2] : r in RES]; // Newton formula with roots has negation
 W:=[&+[&*[Kp|ROO[u] : u in U] : U in Subsets({1..#ROO},k)] : k in [0..#ROO]];
 F:=Polynomial([p^z*(Z!(a/p^z)) where z:=Valuation(a): a in W]); // Magma bug
 return Evaluate(F,Parent(F).1^v),Sort(RES); end function;

function FIX(f) C:=Coefficients(f);
 if not &and[IsCoercible(Integers(),c) : c in C] then return f; end if;
 C:=ChangeUniverse(C,Integers());
 if Type(f) eq RngUPolElt then return Polynomial(C); end if;
 assert Type(f) eq RngSerPowElt;
 PSR:=PowerSeriesRing(Integers(),AbsolutePrecision(f));
 return PSR!C; end function;

intrinsic EulerFactor
(J::JacketMot,p::RngIntElt : Degree:=J`deg,Roots:=false) -> .
{The Euler factor of a Jacket motive at a prime p}
 require IsPrime(p): "p must be prime";
 require Gcd(p,J`m) eq 1: "p must be coprime to the denominators";
 require Valuation(J`t,p) eq 0: "v_p(t) must be 0";
 if #J`POS+#J`NEG eq 0 and J`rho eq 0 then
  return Polynomial([1,-p^(-J`tate)]); end if;
 f,roots:=jacket_mot_ef(J,p : deg:=Degree); // should end up as Euler/K
 // probably impossible with p-adic method...
 if J`tate ne 0 then
  if BaseRing(Parent(f)) eq Z and Type(f) eq RngUPolElt then
   f:=ChangeRing(f,Q); end if;
  if BaseRing(Parent(f)) eq Z and Type(f) eq RngSerPowElt then
   f:=PowerSeriesRing(Q,AbsolutePrecision(f))!f; end if;
  f:=Evaluate(f,p^(-J`tate)*Parent(f).1); end if;
 if Roots then roots:=[<r[1],p^(-J`tate)*r[2]> : r in roots];
  return FIX(f),roots; else return FIX(f); end if; end intrinsic;

intrinsic ComplexEvaluation
(J::JacketMot,P::RngOrdIdl : Precision:=GetPrecision(0.5)) -> FldComElt
{Given a Jacket motive and an ideal of prime norm in the field of definition,
 compute the complex evaluation at such an ideal}
 require NumberField(Order(P)) eq J`K: "Ideal must be in field";
 require IsPrime(P): "Ideal must be prime";
// require J`t eq 1: "Must be Jacobi motive for now (t=1)";
 p:=Norm(P); require IsPrime(p): "Ideal must have prime norm"; // odd !
 require Gcd(p,J`m) eq 1: "p must be a good prime";
 require Valuation(J`t,p) eq 0: "v_p(t) must be 0";
 m:=J`m; K:=CyclotomicField(m);
 S:=[s[1] : s in Subfields(K,Degree(J`K)) | IsIsomorphic(s[1],J`K)][1];
 P:=Factorization(Integers(K)!!P)[1][1];
 x:=PolynomialRing(Rationals()).1; roo:=[r[1] : r in Roots(x^m-1,GF(p))];
 _,mp:=ResidueClassField(P); g:=mp(K.1); A:=AssociativeArray(GF(p));
 C:=ComplexField(Precision); zetam:=Exp(2*Pi(C)*C.1/m);
 for u in [1..m] do A[g^u]:=zetam^u; end for;
 zetap:=Exp(2*Pi(C)*C.1/p); res:=C!1.0;
 // inefficient, both not using J`POS multiplicity, and linear method to boot
 for q in J`POS do a:=Z!(q*m); e:=(a*((p-1) div m));
  res*:=-&+[A[(GF(p)!u)^e]*zetap^u : u in [1..p-1]]; end for;
 for q in J`NEG do a:=Z!(q*m); e:=(a*((p-1) div m));
  res/:=-&+[A[(GF(p)!u)^e]*zetap^u : u in [1..p-1]]; end for;
 return Norm(P)^(-J`tate)*res*A[J`t^(Z!(J`rho*(p-1)))]; end intrinsic;
 
////////////////////////////////////////////////////////////////////////

PRZ:=PolynomialRing(Z);
intrinsic LSeries(J::JacketMot :
 Precision:=GetPrecision(0.5),BadPrimes:=[],PoleOrder:=0) -> LSer
{The L-series of a Jacket motive}
 if #J`POS+#J`NEG eq 0 and J`rho eq 0 then
  L:=RiemannZeta(: Precision:=Precision);
  if J`tate ne 0 then L:=Translate(L,-J`tate); end if; return L; end if;
 BAD:=AssociativeArray(); for b in BadPrimes do BAD[b[1]]:=b; end for;
 Sm:=PrimeDivisors(J`m);
 Sn:=PrimeDivisors(Numerator(J`t)); Sd:=PrimeDivisors(Denominator(J`t));
 require Set(Sm cat Sn cat Sd) subset Keys(BAD):
  "BadPrimes should have one entry for each prime dividing t or m";
 C:=&*[Z|b[1]^b[2] : b in BadPrimes];
 function f(p,d) if p in Keys(BAD) then return PRZ!BAD[p][3]; end if;
  return EulerFactor(J,p : Degree:=d); end function;
 S:=<"L-function for ",J>;
 L:=LSeries(J`HS,C,f : Parent:=J,Name:=S,Precision:=Precision);
 if PoleOrder ne 0 then assert IsEven(Weight(J));
  return L/Translate(RiemannZeta(),Weight(J) div 2)^PoleOrder; end if;
 return L; end intrinsic;

intrinsic KummerTwist(J::JacketMot,t::RngQZElt,rho::RngQZElt) -> JacketMot
{The Kummer twist by t^rho of a Jacket motive}
 return J*JacketMotive([],[],t,rho,0); end intrinsic;

intrinsic TateTwist(J::JacketMot,k::RngIntElt) -> JacketMot
{The Tate twist by k of a Jacket motive}
 return JacketMotive(J`POS,J`NEG,J`t,J`rho,J`tate+k); end intrinsic;

intrinsic HodgeStructure(J::JacketMot) -> HodgeStruc
{The Hodge structure of a Jacket sum motive}
 return J`HS; end intrinsic;

intrinsic HodgeVector(J::JacketMot) -> HodgeStruc, RngIntElt
{The Hodge vector of a Jacket sum motive, and the effective Tate twist}
 return HodgeVector(J`HS); end intrinsic;

intrinsic Weight(J::JacketMot) -> RngIntElt
{The weight of a Jacket motive}
 return J`wt; end intrinsic;

intrinsic EffectiveHodgeStructure(J::JacketMot) -> HodgeStruc
{The effective Hodge structure of a Jacket motive}
 return EffectiveHodgeStructure(J`HS); end intrinsic;

intrinsic EffectiveWeight(J::JacketMot) -> RngIntElt
{The effective weight of a Jacket motive}
 return Weight(EffectiveHodgeStructure(J)); end intrinsic;

intrinsic Field(J::JacketMot) -> FldNum
{The field for the Grossencharacter associated to a Jacket motive}
 return J`K; end intrinsic;
 
intrinsic '/'(z::RngIntElt,J::JacketMot) -> JacketMot
{The reciprocal of a Jacket motive (z must be 1)}
 require z eq 1: "z must be 1";
 return JacketMotive(J`NEG,J`POS,J`t,-J`rho,-J`tate); end intrinsic;

intrinsic '*'(J1::JacketMot,J2::JacketMot) -> JacketMot
{The tensor product of two Jacket motives, removing any cancelling parts}
 a:=Numerator(J1`rho); b:=Denominator(J1`rho);
 c:=Numerator(J2`rho); d:=Denominator(J2`rho);
 return JacketMotive(J1`POS cat J2`POS,J1`NEG cat J2`NEG,
                     J1`t^(a*d)*J2`t^(b*c),1/(b*d),J1`tate+J2`tate);
 end intrinsic;

intrinsic '/'(J1::JacketMot,J2::JacketMot) -> JacketMot
{The tensor quotient of two Jacket motives, removing any cancelling parts}
 return J1*(1/J2); end intrinsic;

intrinsic '^'(J::JacketMot,z::RngIntElt) -> JacketMot
{The z-fold tensor product of a Jacket motive}
 if z eq 0 then return JacobiMotive([]); end if;
 if z lt 0 then z:=-z; J:=1/J; end if;
 K:=J; for i in [2..z] do K:=K*J; end for; return K; end intrinsic;

intrinsic 'eq'(J1::JacketMot,J2::JacketMot) -> BoolElt
{Whether two Jacobi motives are equal (same POS/NEG, t^rho, and j)}
 return J1`POS eq J2`POS and J1`NEG eq J2`NEG
   and J1`t eq J2`t and J1`rho eq J2`rho and J1`tate eq J2`tate; end intrinsic;

intrinsic 'ne'(J1::JacketMot,J2::JacketMot) -> BoolElt
{Whether two Jacobi motives are not equal (same POS/NEG, t^rho, and j)}
 return not (J1 eq J2); end intrinsic;

intrinsic Scale(J::JacketMot,q::RngQZElt) -> JacketMot
{The scaling of a Jacket motive by a rational (invertible mod m)}
 require IsCoercible(Integers(J`m),q): "q has common denominator with m";
 require IsInvertible(Integers(J`m)!q): "q must be invertible mod m";
 q:=Integers()!Integers(J`m)!q;
 return JacketMotive([x*q : x in J`POS],[x*q : x in J`NEG],J`t,J`rho*q,J`tate);
 end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic Print(J::JacketMot,lvl::MonStgElt) {}
 if J`tate ne 0 then printf "Tate twist by %o of the ",J`tate; end if;
 if #J`POS+#J`NEG eq 0 then printf "Unital Jacobi motive";
  if J`rho ne 0 then printf " with Kummer twisting parameters (t,rho)=(%o,%o)",
                            J`t,J`rho; end if; return; end if;
 printf "Jacobi motive given by ";
 S:=Sort(SetToSequence(Set(J`POS))); f:=false;
 for s in S do m:=Multiplicity(J`POS,s);
  if f then printf "+"; else f:=true; end if;
  if m eq 1 then printf "[%o]",s; else printf "%o*[%o]",m,s; end if; end for;
 S:=Sort(SetToSequence(Set(J`NEG)));
 for s in S do m:=Multiplicity(J`NEG,s);
  if m eq 1 then printf "-[%o]",s; else printf "-%o*[%o]",m,s; end if; end for;
 if J`rho ne 0 then
  printf " with Kummer twisting parameters (t,rho)=(%o,%o)",J`t,J`rho; end if;
 end intrinsic;

declare attributes FldRat: JKF;
function known_isomorphic(K) // ugly way to make sure only one field copy
 if not assigned Q`JKF then X:=Rationals(); X`JKF:={}; end if;
 for u in Q`JKF do if IsIsomorphic(u,K) then return u; end if; end for;
 X:=Rationals(); X`JKF join:={K}; return K; end function;

// for each IP of K, find IP(K.1) = sigma_u(K.1) for sigma_u : z -> z^u
function oo_permute(K,m,MULT,STAB,oo)
 if IsTotallyReal(K) then return oo; end if;
 Cm:=CyclotomicField(m); zm:=Cm.1; S:=Subfields(Cm,Degree(K)); O:=[];
 KK:=[s[1] : s in S | IsIsomorphic(s[1],K)][1]; // obtain K as "subfield" of Cm
 zK1:=Cm!KK!K.1; IP:=InfinitePlaces(K); ANS:=[]; ooCm:=InfinitePlaces(Cm);
 for j in [t : t in [1..m] | Gcd(t,m) eq 1] do
  if j in &cat O then continue; end if;
   O cat:=[[Integers(m)!j*s : s in STAB]]; end for; assert #O eq #oo;
 for i in [1..#IP] do ev:=Evaluate(K.1,IP[i]);
  A:=[Evaluate(zK1,u) : u in ooCm];
  A cat:=Reverse([ComplexConjugate(x) : x in A]);
  _,w:=Min([Norm(a-ev) : a in A]);
  g:=[t : t in [1..m] | Gcd(t,m) eq 1][w]; u:=0;
  for o in [1..#oo] do if g in O[o] then u:=o; end if; end for;
  assert u ne 0; ANS[i]:=oo[u]; ANS[2*#IP+1-i]:=oo[2*#IP+1-u]; end for;
 return ANS; end function;
 
function OddPart(x) return x div 2^Valuation(x,2); end function;
function init_jacket_mot(POS,NEG,t,rho,tate) rho:=FRAC(rho);
 Nt:=Numerator(t); Dt:=Denominator(t);
 if t eq 1 then rho:=0; // reduce t
 elif t eq -1 then rho:=rho*OddPart(Denominator(rho));
 else F:=Factorization(Nt) cat Factorization(Dt);
      g:=Gcd([f[2] : f in F]); if t lt 0 then g:=OddPart(g); end if;
      rho:=rho*g; t:=Z!Root(Nt,g)/Z!Root(Dt,g); end if;
 rho:=FRAC(rho); if rho eq 0 then t:=1; end if;
 Nt:=Numerator(t); Dt:=Denominator(t);
 N:=Sign(t)*&*[Z|f[1]^(f[2] mod Denominator(rho)) : f in Factorization(Nt)];
 D:=&*[Z|f[1]^(f[2] mod Denominator(rho)) : f in Factorization(Dt)];
 t:=N/D; // rho:=1/Denominator(rho); if rho eq 1 then rho:=0; end if;
 m:=LCM([Denominator(x) : x in POS cat NEG cat [rho]]);
 S1:=<Sort(POS),Sort(NEG),rho>; S:=[S1]; MULT:=[1]; STAB:=[1];
 for i in [i : i in [2..m-1] | Gcd(i,m) eq 1] do
  e:=<Sort([FRAC(x*i) : x in POS]),Sort([FRAC(x*i) : x in NEG]),FRAC(i*rho)>;
  if e eq S1 then STAB:=STAB cat [i]; end if;
  if e in S then continue; end if; MULT cat:=[i]; S cat:=[e]; end for;
 Sn:=<Sort([FRAC(-x) : x in POS]),Sort([FRAC(-x) : x in NEG]),FRAC(-rho)>;
 y:=ext<Q|>.1; Qy:=ext<Q| y-1 : DoLinearExtension>; // compute defining field
 M:=MaximalOrder(Qy); G,mp:=RayClassGroup(m*M,[1]);
 _,q:=quo<G|[(s*M)@@mp : s in STAB]>;
 K:=AbsoluteField(NumberField(AbelianExtension(Inverse(q)*mp))); wt:=#POS-#NEG;
 K:=OptimizedRepresentation(K); deg:=#MULT; assert Degree(K) eq deg;
 K:=known_isomorphic(K); // geh, don't remake number fields!
 oo:=[Z!(&+[Q|FRAC(-x*Z!((Integers(m)!i)^(-1))) : x in POS]
	-&+[Q|FRAC(-x*Z!((Integers(m)!i)^(-1))) : x in NEG]) : i in MULT];
 // want to know which inf place corresponds to z -> z^i in K for i in MULT 
 if S1 eq Sn then assert Set(oo) eq {wt/2}; // totally real case
  eps:=((t lt 0 and rho eq 1/2) select 1 else 0)+(wt div 2);
  HS:=deg*HodgeStructure([<wt div 2,wt div 2,eps mod 2>]); // guess...
 else HS:=HodgeStructure([<oo[i],wt-oo[i],i gt (#oo div 2) select 1 else 0> :
                          i in [1..#oo]]); end if;
 HS:=TateTwist(HS,tate); oo:=oo_permute(K,m,MULT,STAB,oo);
 SORT:=Sort(oo); ew:=Max([i*wt/2-&+SORT[1..i] : i in [1..#oo]]);
 if S1 eq Sn then oo:=[x-2*tate : x in oo];
 else oo:=[x-tate : x in oo]; end if;
 ///////////////////////////////////
 J:=New(JacketMot); J`POS:=Sort(POS); J`NEG:=Sort(NEG);
 J`m:=m; J`wt:=wt-2*tate; J`HS:=HS;
 J`MULT:=MULT; J`deg:=deg; J`tot_real:=S1 eq Sn; J`K:=K; J`oo:=oo;
 J`ew:=ew; J`tate:=tate; J`t:=t; J`rho:=rho; return J; end function;

intrinsic JacobiMotive
(A::SeqEnum[RngQZElt]:Kummer:=[1,0],Tate:=0,Weight:=false)-> JacketMot
{The Jacobi sum motive corresponding to rational sequence A and empty B,
 with Kummer and Tate twists as varargs}
 return JacobiMotive(A,[] : Kummer:=Kummer, Tate:=Tate, Weight:=Weight);
 end intrinsic;

GetWeight:=Weight;
intrinsic JacobiMotive
(A::SeqEnum[RngQZElt],B::SeqEnum[RngQZElt] :
 Kummer:=[1,0],Tate:=0,Weight:=false)-> JacketMot
{The Jacobi sum motive corresponding to rational sequences A and B,
 with Kummer and Tate twists as varargs}
 J:=JacketMotive(A,B,Kummer[1],Kummer[2],Tate);
 if Type(Weight) eq RngIntElt then require Tate eq 0: "Tate ne 0 with Weight?";
  w:=GetWeight(J); require IsEven(w-Weight): "Weight given is wrong parity";
  return TateTwist(J,(w-Weight) div 2); end if;
 if Weight then tw:=EffectiveWeight(J)-GetWeight(J);
  return TateTwist(J,tw div 2); end if; return J; end intrinsic;

intrinsic JacketMotive
(A::SeqEnum[RngQZElt],B::SeqEnum[RngQZElt],
 t::RngQZElt,rho::RngQZElt,j::RngIntElt) -> JacketMot
{The Jacket motive corresponding to rational sequences A and B,
 the Kummer power t^rho, and the Tate twist by j}
 require t ne 0: "t cannot be 0";
 A:=[Q|FRAC(x) : x in A]; B:=[Q|FRAC(x) : x in B];
 A:=[Q|x : x in A | x ne 0]; B:=[Q|x : x in B | x ne 0];
 require IsCoercible(Z,&+A-&+B): "Sum of A minus sum of B is not in Z";
 for x in Set(A) meet Set(B) do m:=Min(Multiplicity(A,x),Multiplicity(B,x));
  for i in [1..m] do Exclude(~A,x); Exclude(~B,x); end for; end for;
 return init_jacket_mot(A,B,t,rho,j); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic Grossencharacter(J::JacketMot : Check:=true) -> GrossenChar
{Given a Jacobi motive, return the associated Hecke Grossencharacter}
// require J`t eq 1: "Must be a Jacobi motive (t=1) for now";
 BAD:=PrimeDivisors(J`m*Numerator(J`t)*Denominator(J`t));
 _,tw:=EffectiveHodgeStructure(J); J:=TateTwist(J,-tw);
 N:=&*[Z | p : p in PrimeDivisors(Numerator(J`t)) | true or Gcd(p,J`m) eq 1];
 D:=&*[Z | p : p in PrimeDivisors(Denominator(J`t)) | true or Gcd(p,J`m eq 1)];
 I:=J`m^2*N*D*Integers(J`K); // Weil upper bound, could improve sometimes?
 if IsOdd(J`m) and IsPrime(J`m) and J`t eq 1 then // odd prime case, no Kummer!
  I:=Ideal(Decomposition(J`K,J`m)[1][1])^2; end if;
 if J`m eq 4 and J`t eq 1 then I:=4*Integers(J`K); end if; // another spec case
 // in reality, could special-case all small J`m ...
 if J`tot_real then oo:=[i : i in [1..Degree(J`K)]];
  if not 1 in [e[3] : e in HodgeStructure(J)`A] then oo:=[]; end if;
  G:=HeckeCharacterGroup(I,oo); psi:=TateTwist(G.0,0);
 else ootype:=[[J`oo[i],J`wt-J`oo[i]] : i in [1..#J`oo div 2]];
  G:=HeckeCharacterGroup(I); psi:=Grossencharacter(G.0,ootype); end if;
  // this is a typical Magma mess
  // as the oo-type order for J`K needs to be carefully determined
 o:=Exponent(TorsionUnitGroup(J`K));
 S:=TargetRestriction(G,CyclotomicField(o));
  // DATA:=[* <p^2,1> : p in PrimesUpTo(100) | Gcd(p,&*BAD) eq 1 *]; det^2 = 1
 DATA:=[* *]; _,S:=HeckeCharacter(S,DATA : RequireGenerators:=false);
 prec:=30+2*(Degree(J`K)*Weight(psi)); // primelim of 10^4
 DATA:=[* *]; q:=2; u:=S.0; U:=S; pi:=Pi(RealField(prec));
 while #S ne 1 do // HACK, skip if S.0 is only element
  b,p,f:=IsPrimePower(q); q:=q+1; if not b then continue; end if;
  Ps:=[Ideal(d[1]) : d in Decomposition(J`K,p)];
  if Norm(Ps[1]) ne p^f or Gcd(&*BAD,p) ne 1 then continue; end if;
  printf "At prime power %o, last kernel was size %o\n",q-1,#U;
  f1:=EulerFactor(J,p); v:=Degree(J`K)/#Ps;
  f2:=Polynomial([Coefficient(f1,e) : e in [0..Degree(f1) by v]]);
  roo:=[r[1] : r in Roots(f2,ComplexField(prec))];
  for P in Ps do ev:='@'(P,psi : Precision:=prec); Q:=[];
   for r in roo do z:=Log(ev*r)/2/pi;
    if Abs(Real(z)) gt 10^(-prec/2) then continue; end if;
    appr:=BestApproximation(Imaginary(z),1000*o^2);
    if o mod Denominator(appr) ne 0 then continue; end if;
    Q:=Q cat [FractionalPart(appr)]; end for;
    if #Q eq 0 then "Warning, nothing found, wrong oo-type?"; continue; end if;
   if #Set(Q) gt 1 then // maybe check a full orbit of conjugates exists?
    if Degree(J`K) ne #Ps then continue; end if; // split prime
    r:=1/ComplexEvaluation(J,P : Precision:=prec); z:=Log(ev*r)/2/pi;
    appr:=BestApproximation(Imaginary(z),1000*o^2); // hopefully this works...
    assert o mod Denominator(appr) eq 0; Q:=[FractionalPart(appr)]; end if;
   DATA cat:=[* <P,-Integers(Denominator(Q[1]))!Numerator(Q[1])> *]; end for;
  u,U:=HeckeCharacter(S,DATA : RequireGenerators:=false);
  if #U eq 1 then break; end if; end while;
 if J`tot_real then ans:=AssociatedPrimitiveCharacter(psi*u);
 else ans:=AssociatedPrimitiveGrossencharacter(psi*u); end if;
 if not Check then return TateTwist(ans,tw); end if;
 P:=[p : p in PrimesUpTo(100) | Gcd(p,&*BAD) eq 1];
 assert &and[EulerFactor(ans,p : Integral) eq EulerFactor(J,p) : p in P];
 return TateTwist(ans,tw); end intrinsic;

/*

> J:=JacobiMotive([2/3,2/3],[1/3]); J;  
> Grossencharacter(J);

> J:=JacobiMotive([1/2,3/4],[1/4]); J;
> Grossencharacter(J);

> J:=JacobiMotive([5/8,7/8],[1/2]); J;
> Grossencharacter(J);

> J:=JacobiMotive([1/7,2/7,4/7],[]); J;
> Grossencharacter(J);

> J:=JacobiMotive([1/4,1/4,1/2,1/2,1/2],[]); J;
> Grossencharacter(J);

> J:=JacobiMotive([1/3,1/3,1/3],[]); J; // Hodge [2,1]
> Grossencharacter(J);

> J:=JacobiMotive([1/5,1/5,3/5],[]); J;
> Grossencharacter(J);

> J:=JacobiMotive([1/5,1/5,1/5,1/5,1/5],[]); J;
> Grossencharacter(J);

> J:=JacobiMotive([],[1/5,1/5,1/5,1/5,1/5]); J;
> Grossencharacter(J);

> J:=JacobiMotive([1/8,1/8,1/8,1/8,1/2],[]); J;
> Grossencharacter(J);

> J:=JacobiMotive([1/3,1/3,1/3,1/3,1/3,1/3],[]); J; // [4,2]
> Grossencharacter(J);

> J:=JacobiMotive([1/3,1/3,1/3,1/3,1/3,1/3,1/3,1/3,1/3],[]); J;
> Grossencharacter(J);

> J:=JacobiMotive([1/3,1/3,1/3],[])^6; J; // [12,6], triv char
> Grossencharacter(J);

> J:=JacobiMotive([1/8,1/8,3/4],[]); J;
> Grossencharacter(J);

> J:=JacobiMotive([1/8,1/4,5/8],[]); J; // 5-stable, Q(i)
> Grossencharacter(J);

> J:=JacobiMotive([1/8,3/8,1/2],[]); J; // 3-stable, Q(sqrt(-2))
> Grossencharacter(J);

> J:=JacobiMotive([1/12,5/12,1/2],[]); J; // 5-stable, Q(i)
> Grossencharacter(J);

> J:=JacobiMotive([1/11,3/11,4/11,5/11,9/11],[]); J;
> Grossencharacter(J);

> J:=JacobiMotive([1/19,4/19,5/19,6/19,7/19,9/19,11/19,16/19,17/19],[]); J;
> Grossencharacter(J);

> J:=JacobiMotive([3/5,3/5],[1/5]); J;
> Grossencharacter(J);

> J:=JacobiMotive([1/5,4/5],[]); J; // hecke char over Q(sqrt(5))
> Grossencharacter(J);

> J:=JacobiMotive([1/5,4/5],[2/5,3/5]); J; // zeta func of Q(sqrt(5))
> Grossencharacter(J);

> J:=JacobiMotive([1/5,4/5,2/5,3/5],[]); J; // Kronecker(5)
> Grossencharacter(J);

> J:=JacobiMotive([1/8,2/8,3/8,4/8,5/8],[7/8]); J;
> Grossencharacter(J);

> J:=JacobiMotive([1/8,3/8,5/8,7/8],[]); J; // Kronecker(8)
> Grossencharacter(J);

> J:=JacobiMotive([1/8,3/8,5/8,7/8],[1/2,1/2]); J; // Kronecker(-8)
> Grossencharacter(J);

> J:=JacobiMotive([1/8,3/8,5/8,7/8],[1/4,3/4]); J; // Kronecker(-4)
> Grossencharacter(J);

> J:=JacobiMotive([1/9,2/9],[1/3]); J; // matches grossenchar norm 81
> Grossencharacter(J);

> J:=JacobiMotive([1/9,8/9],[1/3,2/3]); J; // zeta of real subfield Q(z9)
> Grossencharacter(J);

> J:=JacobiMotive([1/4,1/4,1/4,1/4],[1/2,1/2]); // FRV Ex 1
> Grossencharacter(J);

> J:=JacobiMotive([1/12,5/12,1/4,1/4],[1/2,1/2]); // FRV Ex 2
> Grossencharacter(J);

> J:=JacobiMotive([1/8,1/8,3/8,7/8],[1/2]);
> Grossencharacter(J);

> J:=JacobiMotive([1/8,1/8,3/8,7/8,1/2],[]);
> Grossencharacter(J);

> J:=JacobiMotive([1/13,3/13,9/13],[]); // quartic field, disc 13^3
> Grossencharacter(J);

> J:=JacobiMotive([1/17,4/17,16/17,64/17],[]); // quartic field
> Grossencharacter(J);

> J:=JacobiMotive([1/8,1/4,1/2],[3/8,5/8,7/8]); // (0,2)+(1,1,0)+(1,1,1)
> Grossencharacter(J);

> J:=JacobiMotive([2/3,2/3],[1/3] : Kummer:=[2,1/3]); // cubic twist by 2
> Grossencharacter(J);

> J:=JacobiMotive([2/3,2/3],[1/3] : Kummer:=[2,1/2]); // quad twist by 2
> Grossencharacter(J);

> J:=JacobiMotive([1/2,3/4],[1/4] : Kummer:=[5,1/4]); // quartic twist by 5
> Grossencharacter(J);

> J:=JacobiMotive([],[] : Kummer:=[2,1/2]); // Kronecker(8)
> Grossencharacter(J);

> J:=JacobiMotive([],[] : Kummer:=[2,1/3]); // Artin Q(2^(1/3))
> Grossencharacter(J);

> J:=JacobiMotive([1/5,4/5],[] : Kummer:=[5,1/5],Tate:=1);
> Grossencharacter(J);

> J:=JacobiMotive([1/5,4/5],[] : Kummer:=[5,2/5],Tate:=1);
> Grossencharacter(J);

> J:=JacobiMotive([3/5,3/5],[1/5]); // much slower than previous two
> K:=KummerTwist(J,5,1/5);
> Grossencharacter(K);

> J:=JacobiMotive([3/5,3/5],[1/5]);
> K:=KummerTwist(J,5,2/5);
> Grossencharacter(K);

> J:=JacobiMotive([3/5,3/5],[1/5]);
> K:=KummerTwist(J,5,3/5);
> Grossencharacter(K);

> J:=JacobiMotive([3/5,3/5],[1/5]);
> K:=KummerTwist(J,5,4/5);
> Grossencharacter(K);

> n:=5; J:=JacobiMotive([1/n : i in [1..n]]); Grossencharacter(J);
> n:=8; J:=JacobiMotive([1/n : i in [1..n]]); Grossencharacter(J);
> n:=12; J:=JacobiMotive([1/n : i in [1..n]]); Grossencharacter(J);
> n:=16; J:=JacobiMotive([1/n : i in [1..n]]); Grossencharacter(J);
> n:=24; J:=JacobiMotive([1/n : i in [1..n]]); Grossencharacter(J);
> n:=30; J:=JacobiMotive([1/n : i in [1..n]]); Grossencharacter(J);

> J:=JacobiMotive([1/16,1/16,7/8]);
> Grossencharacter(J);

> J:=JacobiMotive([1/16,2/16,3/16,4/16,5/16,11/16,13/16,9/16]); // 9-stable
> Grossencharacter(J);

> J:=JacobiMotive([1/16,3/16,9/16,11/16,1/2]); // 3,9-stable
> Grossencharacter(J); // kind of hard to screw up oo-places though (conj)

*/
