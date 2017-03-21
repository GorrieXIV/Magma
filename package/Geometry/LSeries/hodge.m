
freeze;

declare type HodgeStruc;
declare attributes HodgeStruc: A,w,phv;
// probably not the best data structure, particularly when A is large

RS:=func<s|&cat([x: x in Eltseq(Sprint(s)) | (x ne " ") and (x ne "\n")])>;
intrinsic Print(HS::HodgeStruc,level::MonStgElt) {}
 if #HS`A eq 0 then printf "Empty Hodge structure"; return; end if;
 printf "Hodge structure of weight %o given by",HS`w; MS:=Multiset(HS`A);
 if HS`phv then printf " Hodge vector %o",RS(HodgeVector(HS)); return; end if;
 for u in Sort([x : x in Set(MS)]) do if u[1] gt u[2] then continue; end if;
  m:=Multiplicity(MS,u); S:=(m gt 1) select IntegerToString(m)*"*" else "";
  if u[1] eq u[2] then printf " %o<%o,%o,%o>",S,u[1],u[1],u[3];
  else printf " %o<%o,%o>",S,u[1],u[2]; end if; end for; end intrinsic;

Z:=Integers();
intrinsic HodgeStructure(E::.:PrintHodgeVector:=false,PHV:=false) -> HodgeStruc
{Create a Hodge structure from a suitable input (sequence, list, tuple)}
 require Type(E) in {SeqEnum,List,SetEnum,Tup}: "Bad type in HodgeStructure";
 if #E eq 0 then N:=New(HodgeStruc); N`w:=0; N`A:=[]; return N; end if;
 require &and[Type(x) in {SeqEnum,List,SetEnum,Tup} : x in E]:
 "Bad entries in subtype in HodgeStructure";
 require &and[#x ge 2 : x in E]: "Each HS part must have at least 2 entries";
 require #{e[1]+e[2] : e in E} eq 1: "Weight must be constant";
 w:=E[1][1]+E[1][2]; A:=[];
 for e in E do A cat:=[<e[1],e[2],e[1] eq e[2] select e[3] else 2>]; end for;
 for e in A do
  require Type(e[1]) eq RngIntElt and Type(e[2]) eq RngIntElt and
   Type(e[3]) eq RngIntElt: "Hodge entries must be integers"; end for;
 for e in A do
  require e[1] ne e[2] or e[3] ne 2: "Undefined Hodge index"; end for;
 for e in A do
  require e[1] eq e[2] or e[3] eq 2: "Bad Hodge index"; end for; U:=A;
 while #U ne 0 do u:=U[1];
  Remove(~U,1); if u[1] eq u[2] then continue; end if;
  i:=Index(U,<u[2],u[1],2>); require i ne 0: "Hodge data are not symmetric";
  Remove(~U,i); end while;
 N:=New(HodgeStruc); N`A:=A; N`w:=w; N`phv:=PrintHodgeVector or PHV;
 return N; end intrinsic; 

function hodge_struc(wt,gamma) assert Type(wt) eq RngIntElt; assert wt ge 0;
 G:=SequenceToMultiset(ChangeUniverse(gamma,Integers())); t:=1; H:=[];
 while true do if 2*t le 2-wt then break; end if; // t,G,H;
  m:=Multiplicity(G,t); n:=Multiplicity(G,t-1);
  if n lt m then return false,_; end if;
  for i in [1..m] do Exclude(~G,t); Exclude(~G,t-1); end for;
  H cat:=[<wt-1+t,1-t,2> : i in [1..m]];
  H cat:=[<1-t,wt-1+t,2> : i in [1..m]]; t:=t-1; end while;
 if wt mod 2 eq 0 then e:=1-(wt div 2);
  m:=Multiplicity(G,e); for i in [1..m] do Exclude(~G,e); end for;
  H cat:=[<wt div 2,wt div 2,1> : i in [1..m]]; e:=-(wt div 2);
  m:=Multiplicity(G,e); for i in [1..m] do Exclude(~G,e); end for;
  H cat:=[<wt div 2,wt div 2,0> : i in [1..m]]; end if;
 if #G ne 0 then return false,_; end if;
 Sort(~H); return true,H; end function; // doesn't need wt>=0, but convenient?

intrinsic HodgeStructure(wt::RngIntElt,GAMMA::SeqEnum :
			 PrintHodgeVector:=false,PHV:=false) -> HodgeStruc
{Given a motivic weight and suitable gamma shifts, return the Hodge structure}
 require &and[Type(g) eq RngIntElt : g in GAMMA]: "Gamma shifts must be in Z";
 if wt lt 0 then sh:=2*Ceiling(Abs(wt/2)); GAMMA:=[g-(sh div 2) : g in GAMMA];
 else sh:=0; end if;
 b,S:=hodge_struc(wt+sh,GAMMA); require b: "GAMMA is not a Hodge structure";
 return TateTwist(HodgeStructure(S : PHV:=PrintHodgeVector or PHV),(sh div 2));
 end intrinsic;

intrinsic HasHodgeStructure(L::LSer : PrintHodgeVector:=false,PHV:=false)
 -> BoolElt,HodgeStruc
{Determine whether an L-series has a Hodge structure, and if so return it}
 wt:=MotivicWeight(L); GAMMA:=L`gamma;
 if wt lt 0 then sh:=2*Ceiling(Abs(wt/2)); GAMMA:=[g-(sh div 2) : g in GAMMA];
 else sh:=0; end if; b,H:=hodge_struc(wt+sh,GAMMA);
 if b then return b,TateTwist(HodgeStructure(H : PHV:=PrintHodgeVector or PHV),
			      (sh div 2)); end if; return false; end intrinsic;

intrinsic HodgeStructure(L::LSer : PrintHodgeVector:=false,PHV:=false)
 -> HodgeStruc
{Return the Hodge structure of an L-series (assuming it has one)}
 wt:=MotivicWeight(L); GAMMA:=L`gamma;
 if wt lt 0 then sh:=2*Ceiling(Abs(wt/2)); GAMMA:=[g-(sh div 2) : g in GAMMA];
 else sh:=0; end if; b,H:=hodge_struc(wt+sh,GAMMA);
 require b: "L-series does not seem to have a Hodge structure?!";
 return TateTwist(HodgeStructure(H : PHV:=PrintHodgeVector or PHV),(sh div 2));
 end intrinsic;

intrinsic Eltseq(HS::HodgeStruc) -> SeqEnum
{Given a Hodge structure, return the underlying eltseq}
return HS`A; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic '+'(H1::HodgeStruc,H2::HodgeStruc) -> HodgeStruc {}
 if IsEmpty(H1) then return H2; end if;
 if IsEmpty(H2) then return H1; end if;
 require H1`w eq H2`w: "Hodge structures must have same weight";
 return HodgeStructure(H1`A cat H2`A : PHV:=H1`phv or H2`phv); end intrinsic;

intrinsic '-'(H1::HodgeStruc,H2::HodgeStruc) -> HodgeStruc {}
 if IsEmpty(H2) then return H1; end if;
 require not IsEmpty(H1): "Cannot subtract from empty HodgeStruc";
 require H1`w eq H2`w: "Hodge structures must have same weight";
 S1:=Multiset(H1`A); S2:=Multiset(H2`A); 
 require S2 subset S1: "Second Hodge structure not contained in first";
 return HodgeStructure([x : x in S1 diff S2] : PHV:=H1`phv or H2`phv);
 end intrinsic;

function tens_prod_HS(HS1,HS2) H:=[];
 for h1 in HS1, h2 in HS2 do e:=2; v1:=h1[1]+h2[1]; v2:=h1[2]+h2[2];
  if v1 eq v2 then // unsure about some of this
   if h1[1] gt h1[2] then e:=1; elif h1[1] lt h1[2] then e:=0;
   else e:=(h1[3]+h2[3]) mod 2; end if; end if; H cat:=[<v1,v2,e>]; end for;
 return H; end function;

intrinsic '*'(H1::HodgeStruc,H2::HodgeStruc) -> HodgeStruc
{Tensor product of Hodge structures}
 if IsEmpty(H1) or IsEmpty(H2) then return HodgeStructure([]); end if;
 return HodgeStructure(tens_prod_HS(H1`A,H2`A) : PHV:=H1`phv or H2`phv);
 end intrinsic;

intrinsic TensorProduct(H1::HodgeStruc,H2::HodgeStruc) -> HodgeStruc
{Tensor product of Hodge structures} return H1*H2; end intrinsic;

intrinsic '*'(m::RngIntElt,H::HodgeStruc) -> HodgeStruc {}
 require m ge 0: "Multiplicand must be nonnegative";
 if m eq 0 or IsEmpty(H) then return HodgeStructure([]); end if;
 return &+[H : i in [1..m]]; end intrinsic;

intrinsic '^'(H::HodgeStruc,m::RngIntElt) -> HodgeStruc
{Iterated tensor product of a Hodge structure}
 if m eq 0 then return HodgeStructure([<0,0,0>] : PHV:=H`phv); end if;
 if m lt 0 then return 1/(H^(-m)); end if;
 return &*[H : i in [1..m]]; end intrinsic;

intrinsic Dual(H::HodgeStruc) -> HodgeStruc
{Dual of a Hodge structure, ie negate all (p,q)}
 return HodgeStructure([<-a[1],-a[2],a[3]> : a in H`A] : PHV:=H`phv);
 end intrinsic;

/*
intrinsic '/'(m::RngIntElt,H::HodgeStruc) -> HodgeStruc
{Inverse (dual) of a Hodge structure (numerator must be 1): negate all (p,q)}
 require m eq 1: "Numerator must be 1";
 return HodgeStructure([<-a[1],-a[2],a[3]> : a in H`A]); end intrinsic;

intrinsic '/'(H1::HodgeStruc,H2::HodgeStruc) -> HodgeStruc
{Tensor product of H1 with inverse of H2}
 return H1*(1/H2); end intrinsic;
*/

////////////////////////////////////////////////////////////////////////

intrinsic Determinant(H::HodgeStruc) -> HodgeStruc
{The determinant of a Hodge structure}
 if IsEmpty(H) then return HodgeStructure([<0,0,0>] : PHV:=H`phv); end if;
 eps:=&+[(x[1] eq x[2]) select x[3] else IsOdd(H`w) select 0 else 1 :
          x in H`A | x[1] ge x[2]];
 o:=(H`w*#H`A) div 2; return HodgeStructure([<o,o,eps mod 2>] : PHV:=H`phv);
 end intrinsic;

function hs_dim2_pp(HS,m) A:=HS`A; // (p,p,e1) and (p,p,e2) case // mth sympow
 HS:=[&+([<A[1][1],A[1][2],A[1][3]> : i in [1..j]] cat 
 	 [<A[2][1],A[2][2],A[2][3]> : i in [1..m-j]]) : j in [0..m]];
 HS:=[<h[1],h[2],h[3] mod 2> : h in HS]; return HodgeStructure(HS);
 end function;

function hs_dim2_pq(HS,m) A:=HS`A; wt:=A[1][1]+A[1][2]; //(p,q) // mth sympow
 HS:=[&+([<A[1][1],A[1][2],A[1][3]> : i in [1..j]] cat 
         [<A[2][1],A[2][2],A[2][3]> : i in [1..m-j]]) : j in [0..m]];
 HS:=[<h[1],h[2],h[3] mod 2> : h in HS]; 
 if IsOdd(wt) and m mod 4 eq 2 then // hopefully correct with m?
  Exclude(~HS,<(m*wt) div 2,(m*wt) div 2,0>);
  HS cat:=[<(m*wt) div 2,(m*wt) div 2,1>]; end if;
 return HodgeStructure(HS); end function;

function hs_dim2(HS,m) A:=HS`A; // sympow
 if A[1][1] eq A[1][2] then return hs_dim2_pp(HS,m);
 else return hs_dim2_pq(HS,m); end if; end function;

function sumsets(m,w) if w eq 1 then return [[m]]; end if;
 if m eq 0 then return [[0 : i in [1..w]]]; end if;
 if w eq 2 then return [[i,m-i] : i in [0..m]]; end if;
 return &cat[[[i] cat e : e in sumsets(m-i,w-1)] : i in [0..m]]; end function;

function split_up(HS) A:=HS`A; B:=[];
 while #A ne 0 do e:=A[1]; Exclude(~A,e);
  if e[1] ne e[2] then z:=<e[2],e[1],2>; Exclude(~A,z);
   B cat:=[HodgeStructure([e,z])];
  elif e in A then Exclude(~A,e); B cat:=[HodgeStructure([e,e])];
  else z:=<e[1],e[2],1-e[3]>;
   if z in A then Exclude(~A,z); B cat:=[HodgeStructure([e,z])];
   else B cat:=[HodgeStructure([e])]; end if; end if; end while;
 return B; end function;

function hs_sympow(HS,m) A:=HS`A;
 if m eq 0 then return HodgeStructure([<0,0,0>] : PHV:=HS`phv); end if;
 if #A eq 1 then return HS^m; end if;
 if #A eq 2 then return hs_dim2(HS,m); end if;
 S:=split_up(HS); P:=sumsets(m,#S);
 return &+[&*[hs_sympow(S[i],p[i]) : i in [1..#S]] : p in P]; end function;

intrinsic SymmetricPower(HS::HodgeStruc,m::RngIntElt) -> HodgeStruc
{Given a Hodge structure, compute its mth symmetric power}
 require m ge 0: "Power must be nonnegative";
 return hs_sympow(HS,m); end intrinsic;

intrinsic AlternatingSquare(HS::HodgeStruc) -> HodgeStruc
{Given a Hodge structure, compute its alternating square}
 return HS*HS-hs_sympow(HS,2); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic TateTwist(H::HodgeStruc,k::RngIntElt) -> HodgeStruc
{Given a Hodge structure, twist it by k (reduce weight by 2k)}
 if not assigned H`phv then H`phv:=false; end if;
 return HodgeStructure([<h[1]-k,h[2]-k,h[3]> : h in H`A] :
		       PHV:=H`phv); end intrinsic;

intrinsic EffectiveHodgeStructure(H::HodgeStruc) -> HodgeStruc, RngIntElt
{Given a Hodge structure, translate it so that all the H^(p,q) have
 p,q nonnegative, with at least one equal to zero}
 if IsEmpty(H) then return H,0; end if;
 m:=Min([a[1] : a in H`A]); return TateTwist(H,m),-m; end intrinsic;

intrinsic HodgeVector(H::HodgeStruc) -> SeqEnum,RngIntElt
{Given a Hodge structure, compute its Hodge vector (and Tate shift)}
 H,m:=EffectiveHodgeStructure(H); w:=Weight(H); A:=[a[1] : a in H`A];
 v:=[Multiplicity(A,i) : i in [0..w]]; return v,m; end intrinsic;

intrinsic 'eq'(H1::HodgeStruc,H2::HodgeStruc) -> HodgeStruc {}
 if IsEmpty(H1) or IsEmpty(H2) then return IsEmpty(H2) and IsEmpty(H1); end if;
 if H1`w ne H2`w then return false; end if;
 return Sort(H1`A) eq Sort(H2`A); end intrinsic;

intrinsic IsEmpty(H::HodgeStruc) -> BoolElt {} return #H`A eq 0; end intrinsic;

function gamma_factors(wt,HS) G:=[]; // wt is unused?
 for h in HS do if h[1] lt h[2] then continue; end if;
  if h[1] eq h[2] then G cat:=[-h[2]+h[3]]; continue; end if;
  G cat:=[-h[2],-h[2]+1]; end for; Sort(~G); return G; end function;

intrinsic GammaFactors(H::HodgeStruc) -> SeqEnum
{Given a Hodge structure, return its Gamma factors (shifts)}
 return gamma_factors(H`w,H`A); end intrinsic;

intrinsic GammaShifts(H::HodgeStruc) -> SeqEnum
{Given a Hodge structure, return its Gamma shifts (factors)}
 return gamma_factors(H`w,H`A); end intrinsic;

intrinsic Degree(H::HodgeStruc) -> RngIntElt
{Given a Hodge structure, return its degree} return #H`A; end intrinsic;

intrinsic Weight(H::HodgeStruc) -> SeqEnum
{Given a Hodge structure, return its weight} return H`w; end intrinsic;

intrinsic RootNumber(H::HodgeStruc) -> FldCycElt
{Given a Hodge structure, compute the root number at infinity}
 C:=CyclotomicField(4); zeta4:=C.1; if #H`A eq 0 then return C!1; end if;
 u:=&+[Z|h[2]-h[1]+1 : h in H`A | h[1] lt h[2]]; // recip of Deligne
 v:=&+[Z|h[3] : h in H`A | h[1] eq h[2]]; return 1/zeta4^(u+v); end intrinsic;

function critical_points(w,S)
 P:=[s[1] : s in S | s[1] lt s[2]];
 Q:=[s[3] eq 1 select s[1]-1 else s[1] : s in S | s[1] eq s[2]];
 if #P eq 0 then assert IsEven(w);
  if w/2 in Q and w/2-1 in Q then return []; end if;
  if w/2 in Q then A:=[(w div 2)-1..-100 by -2];
  else A:=[(w div 2)..-100 by -2]; end if;
  return Sort(SetToSequence(Set(A cat [w+1-a : a in A]))); end if;
 A:=[s : s in [(Max(P)+1)..((w+1) div 2)]];
 if #Q ne 0 then A:=SetToSequence(Set(A) diff {Max(Q)..0 by -2}); end if;
 return Sort(SetToSequence(Set(A cat [w+1-s : s in A]))); end function;

intrinsic CriticalPoints(L::LSer) -> SeqEnum
{Given an L-series with a Hodge structure, return the critical points}
 b,S:=HasHodgeStructure(L); require b: "L-series has no Hodge structure?!";
 return critical_points(S`w,S`A); end intrinsic;

intrinsic CriticalPoints(H::HodgeStruc) -> SeqEnum
{Given a Hodge structure, return the critical points of an associated L-series}
 return critical_points(H`w,H`A); end intrinsic;

intrinsic ImaginaryTwist(H::HodgeStruc) -> HodgeStruc
{Twist a Hodge structure by the nontrivial weight 0 Hodge structure}
 return H*HodgeStructure([<0,0,1>]); end intrinsic;
