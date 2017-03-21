
freeze;

declare type HypGeomData;
declare attributes HypGeomData: alpha,beta,alpha_poly,beta_poly;
declare attributes HypGeomData: AN,AD,BN,BD,cycA,cycB,Mvalue,dvalue,fps;
declare attributes HypGeomData: bad,char,Garray,Glist;
declare attributes HypGeomData: hodge,weight;
declare attributes HypGeomData: common,common_ab;
declare attributes HypGeomData: print_type;

Z:=Integers(); Q:=Rationals();

intrinsic Print(X::HypGeomData,level::MonStgElt) {}
 if X`print_type eq "alpha_beta" then
  printf "Hypergeometric data given by %o and %o",X`alpha,X`beta;
  if #X`common_ab ne 0 then printf " and common %o",X`common_ab; end if;end if;
 if X`print_type eq "cyclotomic" then
  printf "Hypergeometric data given by %o and %o",X`cycA,X`cycB;
  if #X`common_ab ne 0 then printf " and common %o",X`common; end if; end if;
 end intrinsic;

intrinsic Weight(X::HypGeomData) -> RngIntElt
{The weight of X} return X`weight; end intrinsic;

intrinsic Degree(X::HypGeomData) -> RngIntElt
{Return the degree of given hypergeometric data}
 return Max(#X`alpha,#X`beta); end intrinsic;

intrinsic DefiningPolynomials(X::HypGeomData) -> RngUPolElt, RngUPolElt
{The polynomials (products of cyclotomics) that define X}
 return X`alpha_poly,X`beta_poly; end intrinsic;

intrinsic CyclotomicData(X::HypGeomData) -> SeqEnum, SeqEnum
{The cyclotomic data for X} return X`cycA,X`cycB; end intrinsic;

intrinsic AlphaBetaData(X::HypGeomData) -> SeqEnum, SeqEnum
{The alpha-beta data for X} return X`alpha,X`beta; end intrinsic;

intrinsic MValue(X::HypGeomData) -> FldRatElt
{The scaling parameter M associated to X} return X`Mvalue; end intrinsic;

intrinsic GammaList(X::HypGeomData) -> List
{The list of gamma corresponding to X} return X`Glist; end intrinsic;

intrinsic GammaArray(X::HypGeomData) -> SeqEnum
{The array of gamma corresponding to X} return X`Garray; end intrinsic;

intrinsic IsPrimitive(X::HypGeomData) -> BoolElt, RngIntElt
{Whether the given hypergeometric data is primitive}
 g:=Gcd([x : x in X`Glist]); return g eq 1,g; end intrinsic;

intrinsic PrimitiveData(X::HypGeomData) -> HypGeomData
{Return the primitivization of X}
 b,g:=IsPrimitive(X); if b then return X; end if;
 return HypergeometricData([* x div g : x in X`Glist *]); end intrinsic;

intrinsic 'eq'(X::HypGeomData,Y::HypGeomData) -> BoolElt
{Whether two instances of hypergeometric data are equal}
 return X`alpha eq Y`alpha and X`beta eq Y`beta; end intrinsic;

intrinsic 'ne'(X::HypGeomData,Y::HypGeomData) -> BoolElt
{Whether two instances of hypergeometric data are equal}
 return not (X eq Y); end intrinsic;

////////////////////////////////////////////////////////////////////////

function getGlist(G) X:=[];
 for i in [1..#G] do X:=X cat[Sign(G[i])*i : j in [1..Abs(G[i])]]; end for;
 return SequenceToList(X); end function;

function hgm_init(ALPHA,BETA,print_type) ALPHA:=Sort(ALPHA); BETA:=Sort(BETA);
 X:=New(HypGeomData); X`alpha:=ALPHA; X`beta:=BETA; X`print_type:=print_type;
 X`AN:=[Numerator(x) : x in ALPHA]; X`AD:=[Denominator(x) : x in ALPHA];
 X`BN:=[Numerator(x) : x in BETA]; X`BD:=[Denominator(x) : x in BETA];
 if #X`AD+#X`BD ne 0 then X`bad:=LCM(X`AD cat X`BD); else X`bad:=1; end if;
 S:=[<x,0> : x in ALPHA] cat [<1-x,1> : x in BETA]; Sort(~S);
 s:=0; t:=FunctionField(Rationals()).1; f:=Parent(t)!0; N:=#ALPHA+#BETA;
 if #ALPHA ge #BETA then
  for i in [1..N] do if S[i][2] eq 0 then f:=f+t^s; s:=s+1;
                      else s:=s-1; end if; end for;
  X`hodge:=f; X`weight:=Degree(Numerator(X`hodge));
  X`dvalue:=Degree(Denominator(X`hodge));
 else X`hodge:=0; wt:=Max(#ALPHA,#BETA)-1;
      m:=Multiplicity(ALPHA cat BETA,0)-1;
      if wt mod 2 ne m mod 2 then wt:=wt-1; end if;
      X`weight:=wt; X`dvalue:=(wt-m) div 2;  end if;
 AD:=Multiset([Denominator(x) : x in ALPHA]);
 X`cycA:=Sort(&cat[[a : i in [1..Multiplicity(AD,a) div EulerPhi(a)]]
		   : a in Set(AD)]);
 BD:=Multiset([Denominator(x) : x in BETA]);
 X`cycB:=Sort(&cat[[b : i in [1..Multiplicity(BD,b) div EulerPhi(b)]]
		   : b in Set(BD)]);
 P:=PolynomialRing(Rationals()); Z:=Integers();
 X`alpha_poly:=&*[P|CyclotomicPolynomial(a) : a in X`cycA];
 X`beta_poly:=&*[P|CyclotomicPolynomial(b) : b in X`cycB];
 if #ALPHA+#BETA eq 0 then G:=[];
 else G:=[0:i in [1..Max(X`AD cat X`BD)]]; end if;
 for a in X`cycA do for d in Divisors(a) do // could multiset this
  u:=a div d; G[d]:=G[d]+MoebiusMu(u); end for; end for;
 for b in X`cycB do for d in Divisors(b) do // could multiset this
  u:=b div d; G[d]:=G[d]-MoebiusMu(u); end for; end for;
 if #ALPHA eq #BETA then assert &+[Z|G[i]*i : i in [1..#G]] eq 0; end if;
 if #ALPHA+#BETA eq 0 then X`Garray:=[];
 else X`Garray:=G[1..Max([d : d in [1..#G] | G[d] ne 0])]; end if;
 X`Glist:=getGlist(X`Garray);
 spin:=func<N|&*[d^(d*MoebiusMu(N div d)) : d in Divisors(N)]>;
 X`Mvalue:=&*[Z|spin(x) : x in X`cycA]/&*[Z|spin(y) : y in X`cycB];
 X`fps:=[FractionalPart(-x) : x in X`beta] cat [Q|1 : x in X`alpha | x eq 0];
 X`char:=P!1; T:=P.1;
 if X`weight mod 2 eq 0 then // not sure of this when ALPHA and BETA unequal
  if #ALPHA eq 0 then ALPHA:=[Integers()|]; end if;
  ARR:=IsCoercible(Integers(),&+ALPHA) select X`cycA else X`cycB;
  X`char:=(-T)^(ARR eq X`cycA select 0 else 1)*(1-T)* // handle A/B swap
          &*[P|Discriminant(CyclotomicPolynomial(d)) : d in ARR]; end if;
 X`common_ab:=[]; X`common:=[]; return X; end function;

intrinsic Twist(X::HypGeomData : AlphaBetaNormalize:=false) -> HypGeomData
{The twist of X determined by shifting all alpha and beta by 1/2}
 if Degree(X) eq 0 then return X; end if;
 A:=[FractionalPart(x+1/2) : x in X`alpha cat X`common_ab]; pt:=X`print_type;
 B:=[FractionalPart(x+1/2) : x in X`beta cat X`common_ab]; Sort(~A); Sort(~B);
 b:=#X`alpha eq #X`beta;
 if not AlphaBetaNormalize or B[1] lt A[1] then
  return HypergeometricData(A,B : Print:=pt,SameSize:=b);
 else return HypergeometricData(B,A : Print:=pt,SameSize:=b); end if;
 end intrinsic;

intrinsic HypergeometricData
(f::RngUPolElt,g::RngUPolElt :
 Print:="cyclotomic",SameSize:=true) -> HypGeomData
{The hypergeometric data given by cyclomtomic polynomial products}
 require not SameSize or Degree(f) eq Degree(g): "Degrees must be equal";
 if BaseRing(Parent(f)) eq Z then f:=ChangeRing(f,Q); end if;
 if BaseRing(Parent(g)) eq Z then g:=ChangeRing(g,Q); end if;
 require BaseRing(Parent(f)) eq Q: "f must be defined over Q";
 require BaseRing(Parent(g)) eq Q: "g must be defined over Q";
 F:=Factorization(f); ALPHA:=[];
 require &and[IsCyclotomicPolynomial(h[1]) : h in F]: "f must be cyclotomic";
 for h in F do for j in [1..h[2]] do _,d:=IsCyclotomicPolynomial(h[1]);
  ALPHA cat:=[Q!(x/d) : x in [1..d] | Gcd(x,d) eq 1]; end for; end for;
 G:=Factorization(g); BETA:=[];
 require &and[IsCyclotomicPolynomial(h[1]) : h in G]: "g must be cyclotomic";
 for h in G do for j in [1..h[2]] do _,d:=IsCyclotomicPolynomial(h[1]);
  BETA cat:=[Q!(x/d) : x in [0..d-1] | Gcd(x,d) eq 1]; end for; end for;
 return HypergeometricData(ALPHA,BETA : Print:=Print,SameSize:=SameSize);
 end intrinsic;

intrinsic HypergeometricData(F::SeqEnum[RngIntElt],G::SeqEnum[RngIntElt] :
			     Print:="cyclotomic",SameSize:=true) -> HypGeomData
{The hypergeometric data given by integer sequences corresponding to
 cyclotomic polynomials}
 require &and[x gt 0 : x in F cat G]: "Integers must be positive";
 if #F eq 0 and #G eq 0 then return hgm_init([],[],Print); end if;
 f:=&*[PolynomialRing(Integers())|CyclotomicPolynomial(f) : f in F];
 g:=&*[PolynomialRing(Integers())|CyclotomicPolynomial(g) : g in G];
 require not SameSize or Degree(f) eq Degree(g): "Sequences not same degree?";
 return HypergeometricData(f,g : Print:=Print,SameSize:=SameSize);
 end intrinsic;

intrinsic HypergeometricData
(ALPHA::SeqEnum,BETA::SeqEnum :
 Print:="cyclotomic",SameSize:=true) -> HypGeomData
{The hypergeometric data given by alphas and betas (rationals)}
 if #ALPHA eq 0 then ALPHA:=[Q|]; end if;
 if #BETA eq 0 then BETA:=[Q|]; end if;
 if Universe(ALPHA) eq Z then ALPHA:=ChangeUniverse(ALPHA,Q); end if;
 if Universe(BETA) eq Z then BETA:=ChangeUniverse(BETA,Q); end if;
 require Universe(ALPHA) eq Rationals(): "ALPHA must be in rationals";
 require Universe(BETA) eq Rationals(): "BETA must be in rationals";
 require not SameSize or #ALPHA eq #BETA: "ALPHA and BETA must be same size";
 ALPHA:=Sort([(Numerator(x) mod Denominator(x))/Denominator(x) : x in ALPHA]);
 BETA:=Sort([(Numerator(x) mod Denominator(x))/Denominator(x) : x in BETA]);
 AD:=[Denominator(x) : x in ALPHA]; BD:=[Denominator(x) : x in BETA];
 for d in AD do if d eq 1 or d eq 2 then continue; end if;
  MS:=Multiset([Numerator(x) : x in ALPHA | Denominator(x) eq d]); S:=Set(MS);
  require #S eq EulerPhi(d): "ALPHA must have all conjugates mod",d;
  m:=Multiplicity(MS,1);
  for s in S do require Multiplicity(MS,s) eq m:
	          "ALPHA has unequal conjugates mod",d; end for; end for;
 for d in BD do if d eq 1 or d eq 2 then continue; end if;
  MS:=Multiset([Numerator(x) : x in BETA | Denominator(x) eq d]); S:=Set(MS);
  require #S eq EulerPhi(d): "BETA must have all conjugates mod",d;
  m:=Multiplicity(MS,1);
  for s in S do require Multiplicity(MS,s) eq m:
	          "BETA has unequal conjugates mod",d; end for; end for;
 COMMON:=Multiset(ALPHA) meet Multiset(BETA);
 CD:=Multiset([Denominator(x) : x in COMMON]);
 C:=Sort(&cat[[a:i in [1..Multiplicity(CD,a) div EulerPhi(a)]]:a in Set(CD)]);
 ALPHA:=Sort([a : a in Multiset(ALPHA) diff COMMON]);
 BETA:=Sort([a : a in Multiset(BETA) diff COMMON]);
 H:=hgm_init(ALPHA,BETA,Print);
 H`common_ab:=&cat[[i/c : i in [1..c] | Gcd(i,c) eq 1] : c in C]; H`common:=C;
 return H; end intrinsic;

intrinsic HypergeometricData(GAMMA::SeqEnum[RngIntElt] :
			     Print:="cyclotomic",SameSize:=true) -> HypGeomData
{The hypergeometric data given by an array of gammas}
 if #GAMMA eq 0 then return HypergeometricData([],[]); end if;
 require not SameSize or &+[GAMMA[x]*x : x in [1..#GAMMA]] eq 0:
  "The sum of xG[x] must be 0"; T:=FunctionField(Rationals()).1;
 prod:=&*[(T^v-1)^GAMMA[v] : v in [1..#GAMMA] | GAMMA[v] ne 0];
 return HypergeometricData
 (Numerator(prod),Denominator(prod) : Print:=Print,SameSize:=SameSize);
 end intrinsic;

intrinsic HypergeometricData
(GAMMA::List : Print:="cyclotomic",SameSize:=true) -> HypGeomData
{The hypergeometric data given by a list of gammas}
 if #GAMMA eq 0 then return HypergeometricData([],[]); end if;
 require &and[IsCoercible(Z,x) : x in GAMMA]: "GAMMA must have integers";
 GAMMA:=[Z!x : x in GAMMA];  require not 0 in GAMMA: "GAMMA has 0 in it?";
 require not SameSize or &+GAMMA eq 0: "Sum must be 0";
 m:=Max([Abs(x) : x in GAMMA]); G:=[0 : i in [1..m]];
 for u in GAMMA do G[Abs(u)]:=G[Abs(u)]+Sign(u); end for;
return HypergeometricData(G : Print:=Print,SameSize:=SameSize); end intrinsic;

intrinsic HypergeometricData
(INPUT::SeqEnum[SeqEnum] : Print:="cyclotomic",SameSize:=true) -> HypGeomData
{The hypergeometric derived from an arrays of 2 arrays}
 require #INPUT eq 2: "Must have two arrays";
 return HypergeometricData
 (INPUT[1],INPUT[2] : Print:=Print,SameSize:=SameSize); end intrinsic;

intrinsic SwapAlphaBeta(H::HypGeomData) -> HypGeomData
{Given a hypergeometric datum, swap the alpha and beta}
 return HypergeometricData
 (H`beta,H`alpha : Print:=H`print_type,SameSize:=#H`alpha eq #H`beta);
 end intrinsic;

////////////////////////////////////////////////////////////////////////

function ppart(A,B,p) vp:=Valuation;
 A:=&cat[[p^v : i in [1..EulerPhi(n div p^v)]] where v:=vp(n,p) : n in A];
 B:=&cat[[p^v : i in [1..EulerPhi(n div p^v)]] where v:=vp(n,p) : n in B];
 return <p,Sort(A),Sort(B)>; end function;

intrinsic pParts(H::HypGeomData) -> List
{Given hypergeometric data, return the list of p-parts}
return [* pPart(H,p) : p in PrimeFactors(H`bad) *]; end intrinsic;

intrinsic pPart(H::HypGeomData,p::RngIntElt) -> Tup
{Given hypergeometric data and a prime p, return the p-part}
 require IsPrime(p): "p must be prime";
 return ppart(H`cycA,H`cycB,p); end intrinsic;

function coprime_fracs(n)
 return [k/n : k in [0..n-1] | Gcd(k,n) eq 1]; end function;

function direct_weight(ALPHA,BETA)
 S:=[<x,0> : x in ALPHA] cat [<1-x,1> : x in BETA]; Sort(~S);
 s:=0; t:=FunctionField(Rationals()).1; f:=Parent(t)!0;
 for i in [1..2*#ALPHA] do
  if S[i][2] eq 0 then f:=f+t^s; s:=s+1; else s:=s-1; end if; end for;
 return Degree(Numerator(f)); end function;

function mysort(A)
 f:=func<x,y|(x[2] lt y[2] or (x[2] eq y[2] and x[1] lt y[1]))
 	      select -1 else 1>; B:=Sort(A,f); return B; end function;

function IsTwistMinimal(x) y:=[[FractionalPart(u+1/2) : u in a] : a in x];
 xd:=Reverse(Sort([Denominator(a) : a in x[1] cat x[2]]));
 yd:=Reverse(Sort([Denominator(a) : a in y[1] cat y[2]]));
 if xd lt yd then return true; end if; if xd gt yd then return false; end if;
 x:=[Sort(u) : u in x]; y:=[Sort(u) : u in y];
 if x[1] lt x[2] then x:=[x[2],x[1]]; end if;
 if y[1] lt y[2] then y:=[y[2],y[1]]; end if; return x le y; end function;

function to_cyclo(X) PHI:=[]; A:=X;
 while #A ne 0 do a:=A[1]; m:=Multiplicity(A,a); d:=Denominator(a);
  PHI cat:=[d : i in [1..m]];
  for i in [1..m],x in coprime_fracs(d) do Exclude(~A,x); end for; end while;
 return Sort(PHI); end function;

function primitivity_index(A,B)
 if Universe(A) ne Z then A:=to_cyclo(A); B:=to_cyclo(B); end if;
 G:=[0 : i in [1..Max(A cat B)]];
 for v in A,d in Divisors(v) do G[d]:=G[d]+MoebiusMu(v div d); end for;
 for v in B,d in Divisors(v) do G[d]:=G[d]-MoebiusMu(v div d); end for;
 g:=Gcd([x : x in getGlist(G)]); return g; end function;

intrinsic PossibleHypergeometricData
(d::RngIntElt : Weight:=false,TwistMinimal:=false,pParts:=[* *],
                CyclotomicData:=false,Primitive:=0) -> SeqEnum
{Given a degree d (and weight w), generate the possible hypergeometric data}
 require d ge 1: "Degree must be positive"; w:=Weight;
 require Weight cmpeq false or (Type(w) eq RngIntElt and w ge 0 and w lt d):
 "Weight must be a nonnegative integer and less than degree";
 pr:=Primitive; if Type(pr) eq BoolElt then pr:=pr select 1 else 0; end if;
 require Type(pr) eq RngIntElt and pr ge 0: "Primitivity must be integer >=0";
 if IsOdd(d) and Type(w) eq RngIntElt and IsOdd(w) then return []; end if;
 if pr gt 1 and d mod pr ne 0 then return []; end if;
 // for pr>1, should generate prim data for degree d/pr, and then enlarge it
 E:=[EulerPhiInverse(i) : i in [1..d]]; A:={}; R:=[];
 for P in Partitions(d) do if &or[#E[p] eq 0 : p in P] then continue; end if;
  C:=CartesianProduct([Integers(#E[p]) : p in P]);
  for c in C do
   A join:={Sort(&cat[coprime_fracs(E[P[i]][1+Z!c[i]]) : i in [1..#c]])};
    end for; end for;
 for a in A,b in A do if b[1] ge a[1] then continue; end if;
  if #(Set(a) meet Set(b)) ne 0 then continue; end if; R cat:=[[a,b]]; end for;
 if Type(w) eq BoolElt then X:=Sort(R);
 else X:=Sort([r : r in R | direct_weight(r[1],r[2]) eq w]); end if;
 if TwistMinimal then X:=[x : x in X | IsTwistMinimal(x)]; end if;
 for pp in pParts do Y:=[]; A:=Sort(pp[2]); B:=Sort(pp[3]);
  for x in X do U:=ppart(to_cyclo(x[1]),to_cyclo(x[2]),pp[1]);
   if U[2] eq A and U[3] eq B then Y:=Y cat [x]; continue; end if;
   if U[3] eq A and U[2] eq B then Y:=Y cat [x]; continue; end if; end for;
  X:=Y; end for;
 if CyclotomicData then X:=[[to_cyclo(x[1]),to_cyclo(x[2])] : x in X]; end if;
 if pr ne 0 then X:=[x : x in X | primitivity_index(x[1],x[2]) eq pr]; end if;
 return X; end intrinsic;

intrinsic PossibleHypergeometricData2
(d::RngIntElt : Weight:=false,TwistMinimal:=false,
                CyclotomicData:=false,Primitive:=0) -> SeqEnum
{Given a degree d (and weight w), generate the possible hypergeometric data}
 require d ge 1: "Degree must be positive"; w:=Weight;
 require Weight cmpeq false or (Type(w) eq RngIntElt and w ge 0 and w lt d):
 "Weight must be a nonnegative integer and less than degree";
 pr:=Primitive; if Type(pr) eq BoolElt then pr:=pr select 1 else 0; end if;
 require Type(pr) eq RngIntElt and pr ge 0: "Primitivity must be integer >=0";
 if IsOdd(d) and Type(w) eq RngIntElt and IsOdd(w) then return []; end if;
 if pr gt 1 and d mod pr ne 0 then return []; end if;
 // for pr>1, should generate prim data for degree d/pr, and then enlarge it
 E:=[EulerPhiInverse(i) : i in [1..d]]; A:={}; R:=[];
 for P in Partitions(d) do if &or[#E[p] eq 0 : p in P] then continue; end if;
  C:=CartesianProduct([Integers(#E[p]) : p in P]);
  for c in C do A join:={Sort([E[P[i]][1+Z!c[i]] : i in [1..#c]])}; end for;
  end for;
 for a in A,b in A do if b[1] ne 1 and b[#b] le a[#a] then continue; end if;
  if a[1] eq 1 then continue; end if;
  if #(Set(a) meet Set(b)) ne 0 then continue; end if; R cat:=[[a,b]]; end for;
 if Type(w) eq BoolElt then X:=Sort(R);
 else X:=Sort([r : r in R | direct_weight(r[1],r[2]) eq w]); end if;
 if TwistMinimal then X:=[x : x in X | IsTwistMinimal(x)]; end if;
 if CyclotomicData then X:=[[to_cyclo(x[1]),to_cyclo(x[2])] : x in X]; end if;
 if pr ne 0 then X:=[x : x in X | primitivity_index(x[1],x[2]) eq pr]; end if;
 return X; end intrinsic;
