
freeze;

declare type GrpDrchNFElt;
declare type GrpDrchNF [GrpDrchNFElt];

import "grossenchar.m" : simple_pullback;

/****************************************************************/
//   MARK'S CODE FOR Dirichlet Characters OVER number fields    //
/****************************************************************/

// TO DO: &and --> forall (faster)

procedure dump_abelian(G) printf "Abelian Group ";
 if #G eq 1 then printf "of order 1";
 else printf "isomorphic to"; A:=AbelianInvariants(G);
  for i in [1..#A] do if i gt 1 then printf " +"; end if;
   printf " Z/%o",A[i]; end for;
  printf " given as";
  for i in [1..Ngens(G)] do if i gt 1 then printf " +"; end if;
   printf " Z/%o",Order(G.i); end for;
 end if; end procedure;

function RayResidueRingN(I,oo)  R,m:=RayResidueRing(I,oo);
 if Order(R) gt 1 and Order(R.1) eq 1 then
  A:=AbelianGroup([Order(R.i) : i in [2..Ngens(R)]]);
  m2:=hom<A->R|[R.(i+1) : i in [1..Ngens(A)]]>; return A,m2*m; end if;
 return R,m; end function;

////////////////////////////////////////////////////////////////////////

declare attributes GrpDrchNF:
 Name,NF,Modulus,AbGrp,Pairing,TargetRing,CycloOrder,
 ResidueMap,ooReal,Labels,supergroup,issubgroup,inclmap;
declare attributes GrpDrchNFElt:
 Parent,Element,decomp,components,Zeta,ZetaOrder;

intrinsic Ngens(G::GrpDrchNF) -> RngIntElt 
{The number of generators for G.}
 return Ngens(G`AbGrp); end intrinsic;

intrinsic AssignNames(~G::GrpDrchNF, S::[MonStgElt])
{Assign names to the generators for G.}
 require #S eq Ngens(G`AbGrp) : "Argument 2 must have length", Ngens(G);
 G`Labels := S; end intrinsic;

intrinsic Name(G::GrpDrchNF,i::RngIntElt) -> GrpDrchNFElt
{The ith generator.}
 require i ge 1 : "Argument 2 must be positive";
 require i le Ngens(G) : "Argument 2 can be at most", Ngens(G); return G.i;
 end intrinsic;

intrinsic PrintNamed(G::GrpDrchNF,level::MonStgElt,name::MonStgElt)
{Print Dirichlet character group}
 dump_abelian(G`AbGrp); printf "\n"; oo:=G`ooReal;
 if G`issubgroup then printf "Subgroup "; else printf "Group "; end if;
 if name ne "$" then G`Name:=name;
  printf "of Dirichlet characters %o of modulus of norm %o",
          name,Norm(G`Modulus);
 else printf "of Dirichlet characters of modulus of norm %o",
              Norm(G`Modulus); end if;
 if #oo ne 0 then printf " and infinite places %o",oo; end if;
 printf " over %o mapping to %o",G`NF,G`TargetRing; end intrinsic;

intrinsic Print(G::GrpDrchNF,level::MonStgElt)
{Print Dirichlet character group}
 name:="$"; dump_abelian(G`AbGrp); printf "\n"; oo:=G`ooReal;
 if G`issubgroup then printf "Subgroup "; else printf "Group "; end if;
 if name ne "$" then G`Name:=name;
  printf "of Dirichlet characters %o of modulus of norm %o",
          name,Norm(G`Modulus);
 else printf "of Dirichlet characters of modulus of norm %o",
              Norm(G`Modulus); end if;
 if #oo ne 0 then printf " and infinite places %o",oo; end if;
 printf " over %o mapping to %o",G`NF,G`TargetRing; end intrinsic;

intrinsic Print(e::GrpDrchNFElt,level::MonStgElt) {Print Dirichlet character}
 G:=e`Parent; S:=Eltseq(G`AbGrp!(e`Element));
 if not assigned(G`Name) then NAME:="$"; else NAME:=G`Name; end if;
 I:=[i : i in [1..#S] | S[i] ne 0];
 if Degree(G`NF) eq 1 and Order(e) eq 2 then
  d:=IdentifyKroneckerCharacter(DirichletCharacterOverQ(e));
  printf "Kronecker character %o over QNF",d; return; end if;
 if #I eq 0 then printf "1";
 elif assigned G`Labels then
      for i in [1..#I] do if i ne 1 then printf "*"; end if;
       printf "%o",G`Labels[I[i]];
       if S[I[i]] ne 1 then printf "^%o",S[I[i]]; end if; end for;
 else for i in [1..#I] do if i ne 1 then printf "*"; end if;
       printf "%o.%o",NAME,I[i]; if S[I[i]] ne 1 then printf "^%o",S[I[i]];
        end if; end for; end if; end intrinsic;

intrinsic Parent(x::GrpDrchNFElt) -> GrpDrchNF {Parent}
 return x`Parent; end intrinsic;

intrinsic 'in'(e::.,G::GrpDrchNF) -> BoolElt {in}
 if Type(e) ne GrpDrchNFElt then return false; end if;
 if e`Parent`supergroup ne G`supergroup then return false; end if;
 return G`supergroup`AbGrp!e`Parent`AbGrp!e`Element in G`AbGrp; end intrinsic;

intrinsic SubConstr
 (G::GrpDrchNF,E::SeqEnum[GrpDrchNFElt]) -> GrpDrchNF, Map {sub}
 if #E gt 0 and E[1]`Parent ne G then
  return "Elements on RHS must be in DirichletGroup",_; end if;
 S:=New(GrpDrchNF); S`NF:=G`NF;
 S`Modulus:=G`Modulus; S`ooReal:=G`ooReal; S`ResidueMap:=G`ResidueMap;
 S`supergroup:=G`supergroup; S`issubgroup:=true;
 S`AbGrp,mp:=sub<G`supergroup`AbGrp|
                [G`supergroup`AbGrp!Eltseq(G`supergroup!x) : x in E]>;
 if #S`AbGrp eq #G`AbGrp then // try to fix Z/2 x Z/3 vs Z/6 equality prob
  S`AbGrp:=G`AbGrp; mp:=map<S`AbGrp->G`AbGrp|x:->x>; end if;
 e:=Exponent(S`AbGrp); S`CycloOrder:=e;
 if e lt 2^30 then S`TargetRing:=CyclotomicField(e : Sparse:=(e ge 10^3));
 else S`TargetRing:="a large Cyclotomic ring"; end if;
 S`inclmap:=map<S->G|x:->G!Eltseq(G`AbGrp!mp(S`AbGrp!x`Element))>;
 return S,S`inclmap; end intrinsic;

intrinsic Elements(G::GrpDrchNF) -> SeqEnum 
{A sequence containing the elements of G.}
 return [G!Eltseq(x) : x in G`AbGrp]; end intrinsic;

intrinsic Generators(G::GrpDrchNF) -> Set 
{A set containing the generators for G.}
 return {G.i : i in [1..Ngens(G)]}; end intrinsic;

intrinsic '+'(G::GrpDrchNF,H::GrpDrchNF) -> GrpDrchNF {Add}
 require G`NF cmpeq H`NF and G`Modulus cmpeq H`Modulus
  and G`ooReal eq H`ooReal: "Groups must have same modulus to add them";
 GS:=G`supergroup`AbGrp; HS:=H`supergroup`AbGrp; T:=H`supergroup;
 S:=sub<T|[T!Eltseq(GS!x) : x in Generators(G`AbGrp)] cat
          [T!Eltseq(HS!x) : x in Generators(H`AbGrp)]>;
 return S; end intrinsic;

intrinsic 'meet'(G::GrpDrchNF,H::GrpDrchNF) -> GrpDrchNF {meet}
 require G`NF cmpeq H`NF and G`Modulus cmpeq H`Modulus
  and G`ooReal eq H`ooReal: "Groups need same modulus to intersect them";
 GS:=G`supergroup`AbGrp; HS:=H`supergroup`AbGrp; T:=H`supergroup;
 if #GS eq 1 then return sub<G|[]>; end if;
 i:=iso<GS->HS|[<GS.i,HS.i> : i in [1..Ngens(GS)]]>;
 S:=sub<H|[H!T!Eltseq(HS!g) : g in Generators(i(G`AbGrp) meet H`AbGrp)]>;
 return S; end intrinsic;

intrinsic 'eq'(G::GrpDrchNF,H::GrpDrchNF) -> BoolElt {eq}
 if G`NF cmpne H`NF or G`Modulus cmpne H`Modulus
                    or G`ooReal ne H`ooReal then return false; end if;
 GS:=G`supergroup`AbGrp; HS:=H`supergroup`AbGrp;
 if #GS eq 1 then return #HS eq 1; end if;
 i:=iso<GS->HS|[<GS.i,HS.i> : i in [1..Ngens(GS)]]>;
 return i(G`AbGrp) eq H`AbGrp; end intrinsic;

intrinsic 'subset'(G::GrpDrchNF,H::GrpDrchNF) -> BoolElt {subset}
 if G`NF cmpne H`NF or G`Modulus cmpne H`Modulus
                    or G`ooReal ne H`ooReal then return false; end if;
 GS:=G`supergroup`AbGrp; HS:=H`supergroup`AbGrp;
 if #GS eq 1 then return true; end if;
 i:=iso<GS->HS|[<GS.i,HS.i> : i in [1..Ngens(GS)]]>;
 return i(G`AbGrp) subset H`AbGrp; end intrinsic;

intrinsic 'eq'(x::GrpDrchNFElt,y::GrpDrchNFElt) -> BoolElt {eq}
 if x`Parent`supergroup ne y`Parent`supergroup then return false; end if;
 return Eltseq((x`Parent`supergroup)!x) eq Eltseq((y`Parent`supergroup)!y);
 end intrinsic;

intrinsic IsCoercible(G::GrpDrchNF,e::.) -> BoolElt,GrpDrchNFElt {Coerce}
 if Type(e) eq GrpDrchNFElt then P:=e`Parent;
  if G eq P then return true,G!Eltseq(e); end if; // hopefully same intern rep
  // geh, I have seen this fail with Z/3 x Z/2 versus Z/6 !
  // should not ask for sub<G|[psi]>!psi when the sub<> is already G
  if P`issubgroup then
   return IsCoercible
    (G,P`supergroup!Eltseq(P`supergroup`AbGrp!P`AbGrp!e`Element)); end if;
  if G`supergroup eq e`Parent then
   b,chi:=IsCoercible(G`AbGrp,e`Parent`AbGrp!e`Element);
   if b then return true,G!Eltseq(chi); end if; end if; end if;
 if Type(e) eq RngIntElt and e eq 1 then return true,G.0; end if;
 if Type(e) eq SeqEnum then x:=New(GrpDrchNFElt);
  x`Parent:=G; x`Element:=Eltseq((G`AbGrp)!e); return true,x; end if;
 return false,"Illegal coercion"; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic '.'(G::GrpDrchNF,i::RngIntElt) -> GrpDrchNFElt {element}
 require i ge 0: "Argument 2 must be nonnegative";
 require i le Ngens(G`AbGrp): "Argument 2 can be at most",Ngens(G`AbGrp);
 x:=New(GrpDrchNFElt);
 x`Parent:=G; x`Element:=Eltseq((G`AbGrp).i); return x; end intrinsic;

intrinsic '^'(e::GrpDrchNFElt,i::RngIntElt) -> GrpDrchNFElt {Power}
 x:=New(GrpDrchNFElt); x`Parent:=e`Parent; G:=x`Parent;
 x`Element:=Eltseq(G`AbGrp![i*a : a in e`Element]); return x; end intrinsic;

intrinsic '*'(x::GrpDrchNFElt,y::GrpDrchNFElt) -> GrpDrchNFElt {Multiply}
 A:=x`Parent; B:=y`Parent; I:=A`Modulus; J:=B`Modulus;
 require A`NF eq B`NF: "Characters must be over same number field";
 if I eq J and A`ooReal eq B`ooReal then
  if not A`issubgroup and not B`issubgroup then
   G:=x`Parent`AbGrp; z:=New(GrpDrchNFElt); z`Parent:=x`Parent;
   z`Element:=Eltseq((G!x`Element)+(G!y`Element)); return z;
  else z:=(A`supergroup!x)*(B`supergroup!y);
   if A subset B then return B!z; elif B subset A then return A!z;
   else return z; end if; end if;
 else oo:=Sort(SetToSequence(Set(A`ooReal) join Set(B`ooReal)));
  L:=DirichletGroup(LCM(I,J),oo); return Extend(x,L)*Extend(y,L); end if;
 end intrinsic;

intrinsic '/'(x::GrpDrchNFElt,y::GrpDrchNFElt) -> GrpDrchNFElt {Divide}
 require x`Parent`NF eq y`Parent`NF: "Characters must be in same number field";
 return x*y^(-1); end intrinsic;

intrinsic '/'(e::RngIntElt,y::GrpDrchNFElt) -> GrpDrchNFElt {"} //"
 require e eq 1: "Must have 1 as the numerator"; return y^(-1); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic '#'(G::GrpDrchNF) -> RngInt {The order of G.} return #G`AbGrp; end intrinsic;

intrinsic AbelianGroup(G::GrpDrchNF) -> GrpAb,Map
{Returns an abstract AbelianGroup for the group of Dirichlet characters}
 A:=G`AbGrp; return A,map<A->G|x:->G!Eltseq(x)>; end intrinsic;

intrinsic Eltseq(e::GrpDrchNFElt) -> SeqEnum {For internal use.} 
 return e`Element; end intrinsic;

intrinsic Domain(chi::GrpDrchNFElt) -> FldNum
{Returns the domain of a Dirichlet character}
 return chi`Parent`NF; end intrinsic;

intrinsic Domain(G::GrpDrchNF) -> FldNum
{Returns the domain of a Dirichlet character group}
 return G`NF; end intrinsic;

intrinsic Codomain(chi::GrpDrchNFElt) -> FldNum
{Returns the codomain of a Dirichlet character}
 if assigned chi`Zeta then return Parent(chi`Zeta); end if;
 return TargetRing(Parent(chi)); end intrinsic;

intrinsic TargetRing(chi::GrpDrchNFElt) -> FldNum
{Returns the codomain of a Dirichlet character}
 if assigned chi`Zeta then return Parent(chi`Zeta); end if;
 return TargetRing(Parent(chi)); end intrinsic;

intrinsic TargetRing(G::GrpDrchNF) -> FldNum
{Returns the (default) ring of values, for the Dirichlet character group G}
 require Type(G`TargetRing) ne MonStgElt:
  "Target ring is too big to represent as a cyclotomic ring";
 return G`TargetRing; end intrinsic;

intrinsic Modulus(chi::GrpDrchNFElt) -> RngOrdIdl, SeqEnum
{Returns the modulus of a Dirichlet character as an ideal and real places}
 return chi`Parent`Modulus,chi`Parent`ooReal; end intrinsic;

intrinsic Modulus(G::GrpDrchNF) -> RngOrdIdl, SeqEnum
{Returns the modulus of a Dirichlet character group}
 return G`Modulus,G`ooReal; end intrinsic;

intrinsic UnitTrivialSubgroup(G::GrpDrchNF) -> GrpDrchNF
{Given a group of Dirichlet characters, return the subgroup that
 is trivial on the units of the field.}
 K:=NumberField(Order(G`Modulus)); U,umap:=UnitGroup(K);
 im:=<<umap(u),Integers(1)!0> : u in Generators(U)>;
 _,KER:=DirichletCharacter(G`Modulus,G`ooReal,im : RequireGenerators:=false);
 return KER meet G; end intrinsic;

Z:=Integers();

intrinsic IsTrivialOnUnits(e::GrpDrchNFElt) -> BoolElt
{Returns whether a Dirichlet character is trivial on the units}
 G:=e`Parent; U,umap:=UnitGroup(G`NF);
 return &and[0 eq Z!'@'(umap(u),e : Raw) : u in Generators(U)]; end intrinsic;

intrinsic TotallyUnitTrivialSubgroup(G::GrpDrchNF) -> GrpDrchNF
{Given a group of Dirichlet characters, return the subgroup that
 is everywhere locally trivial on the units of the field}
 K:=NumberField(Order(G`Modulus)); U,umap:=UnitGroup(K);
 im:=<<umap(u),Integers(1)!0> : u in Generators(U)>;
 for f in Factorization(G`Modulus) do D:=DirichletGroup(f[1]^f[2]);
  _,K:=DirichletCharacter(D,im : RequireGenerators:=false);
  G:=Extend(K,G) meet G; end for;
 for e in G`ooReal do
  _,K:=DirichletCharacter(1*Integers(K),[e],im : RequireGenerators:=false);
  G:=Extend(K,G) meet G; end for; return G; end intrinsic;

intrinsic IsIdentity(e::GrpDrchNFElt) -> BoolElt
{True iff e is the trivial character}
 return &and[x eq 0: x in Eltseq(e)]; end intrinsic;

intrinsic IsTrivial(e::GrpDrchNFElt) -> BoolElt {"}//"
 return &and[x eq 0: x in Eltseq(e)]; end intrinsic;

intrinsic IsOdd(e::GrpDrchNFElt) -> BoolElt
{True iff the Dirichlet character e satisfies e(-1)=-1}
 return e(-1) eq -1; end intrinsic;

intrinsic IsEven(e::GrpDrchNFElt) -> BoolElt
{True iff the Dirichlet character e satisfies e(-1)=+1}
 return e(-1) eq 1; end intrinsic;

intrinsic IsTotallyEven(chi::GrpDrchNFElt) -> BoolElt
{For a Dirichlet character chi, this is true if and only if 
 every character in Decomposition(chi) is even.}
return &and[ IsEven(chi_p) : chi_p in Decomposition(chi)]; end intrinsic;

////////////////////////////////////////////////////////////////////////

function prime_power_primitive(chi)
 D:=chi`Parent; if D`ooReal ne [] then return chi; end if;
 if IsTrivial(chi) then return chi; end if;
 I:=D`Modulus; P,f:=Explode(Factorization(I)[1]);
 if f eq 1 then return chi; end if;
 Zm:=RModule(Z,Degree(D`NF)); v:=f-1; K:=NumberField(Order(P));
 Pf:=P^f; Sf:=sub<Zm|[Eltseq(x) : x in Basis(Pf)]>;
 while v gt 0 do Pv:=P^v; Sv:=sub<Zm|[Eltseq(x) : x in Basis(Pv)]>;
  Q,m:=quo<Sv|Sf>;
  reps:=[1+K!Order(P)!Eltseq(Zm!(g @@ m)) : g in Generators(Q)];
  if not &and[0 eq Z!'@'(r,chi : Raw) : r in reps] then break; end if;
  v:=v-1; Sf:=Sv; end while;
 R,mp:=RayResidueRing(P^(v+1));
 data:=<<mp(r),'@'(mp(r),chi : Raw)> : r in Generators(R)>;
 return DirichletCharacter(P^(v+1),data); end function;

intrinsic Conductor(e::GrpDrchNFElt) -> RngOrdIdl, SeqEnum
{Conductor of a Dirichlet character, as an ideal and sequence of real places}
 D:=Decomposition(e); D:=[* x : x in D | not IsTrivial(x) *];
 O:=1*IntegerRing(e`Parent`NF);
 return &*[Parent(O) | x`Parent`Modulus : x in D | ModulusIsFinite(x)],
        &cat[x`Parent`ooReal : x in D | not ModulusIsFinite(x)]; end intrinsic;

function Ioo_extend(chi,H) rj:=H`ResidueMap; RJ:=Domain(rj);
 reps:=[rj(RJ.i) : i in [1..Ngens(RJ)]];
 data:=<<r,'@'(r,chi : Raw)> : r in reps>;
 D:=chi`Parent; ri:=D`ResidueMap; RI:=Domain(ri); HS:=H`supergroup;
 h:=hom<RJ->RI|[reps[i] @@ ri : i in [1..Ngens(RJ)]]>;
 // KER:=Kernel(h); // K:=sub<HS|[HS!Eltseq(RJ!k) : k in Generators(KER)]>;
 ret:=DirichletCharacter(H,data); return ret; end function;

function Ioo_restrict(chi,H) G:=chi`Parent; J:=G`Modulus; oo2:=G`ooReal;
 I:=H`Modulus; oo:=H`ooReal; mI:=H`ResidueMap; RI:=Domain(mI); Z:=Integers();
 reps:=[mI(RI.i) : i in [1..Ngens(RI)]]; // need reps that are 1 in Joo2/Ioo
 if #H eq 1 then return H.0; end if; // this can't happen ?!
 rs:=[CRT([r,1],[I,J/I]) : r in reps]; oodiff:=[x : x in oo2 | not x in oo];
 rs:=[CRT(J,oo2,rs[i],
	  [x in oo select Sign(RealEmbeddings(reps[i])[x]) else 1 : x in oo2])
	 : i in [1..#rs]];
 data:=<<r,'@'(r,chi : Raw)> : r in rs>;
 return DirichletCharacter(H,data); end function;

////////////////////////////////////////////////////////////////////////

intrinsic Extend(chi::GrpDrchNFElt,I::RngOrdIdl) -> GrpDrchNFElt
{Given a Dirichlet character and a modulus, extend the character}
 return Extend(chi,DirichletGroup(I)); end intrinsic;

intrinsic Extend(chi::GrpDrchNFElt,I::RngOrdIdl,oo::SeqEnum[RngIntElt])
 -> GrpDrchNFElt
{Given a Dirichlet character and a modulus with real places, extend the char}
 return Extend(chi,DirichletGroup(I,oo)); end intrinsic;

intrinsic Extend(chi::GrpDrchNFElt,G::GrpDrchNF) -> GrpDrchNFElt
{Extend the given Dirichlet character to the given Dirichlet group}
 H:=chi`Parent; I:=G`Modulus; J:=H`Modulus;
 require G`NF eq H`NF: "Moduli must be in same number field";
 require I subset J:
  "The modulus of the new group must be divisible by that of the old";
 require H`ooReal subset G`ooReal:
 "Infinite places of the new group must contain those of the old";
 if H`issubgroup then chi:=H`supergroup!chi; end if;
 return Ioo_extend(chi,G); end intrinsic;

intrinsic Extend(D::GrpDrchNF,I::RngOrdIdl) -> GrpDrchNF
{Given a group of Dirichlet characters and a modulus,
 extend the group to that modulus}
 return Extend(D,DirichletGroup(I,[])); end intrinsic;

intrinsic Extend(D::GrpDrchNF,I::RngOrdIdl,oo::SeqEnum[RngIntElt]) -> GrpDrchNF
{Given a group of Dirichlet characters and a modulus and real places,
 extend the group to that modulus}
 return Extend(D,DirichletGroup(I,oo)); end intrinsic;

intrinsic Extend(D::GrpDrchNF,T::GrpDrchNF) -> GrpDrchNF
{Given two groups of Dirichlet characters, extend the first to the modulus
 of the second, intersecting with the second group}
 if #D eq 1 then return sub<T|[T.0]>; end if;
 return &+[sub<T|[e]> where e:=Extend(psi,T) : psi in Generators(D)];
 end intrinsic;

intrinsic Restrict(chi::GrpDrchNFElt,G::GrpDrchNF) -> GrpDrchNFElt
{Restrict the given Dirichlet character to the given Dirichlet group}
 H:=chi`Parent; I:=G`Modulus; J:=H`Modulus;
 require G`NF eq H`NF: "Moduli must be in same number field";
 require J subset I:
 "Modulus of the restriction group must divide that of the character";
 if H`issubgroup then chi:=H`supergroup!chi; end if;
 C,ooC:=Conductor(chi);
 require I subset C:
  "Conductor of the character must divide the modulus of the given group";
 require G`ooReal subset H`ooReal:
 "Infinite places of the group must be contained in those of the character";
 require ooC subset G`ooReal:
 "Infinite places of the conductor must be contained in those of the group";
 return &*[G | Extend(x,G) : x in Decomposition(chi) |
	     I subset Modulus(x) and x`Parent`ooReal subset G`ooReal];
 end intrinsic;

intrinsic Restrict(chi::GrpDrchNFElt,I::RngOrdIdl) -> GrpDrchNFElt
{Restrict the given Dirichlet character to the given modulus}
 return Restrict(chi,DirichletGroup(I,[])); end intrinsic;

intrinsic Restrict(chi::GrpDrchNFElt,I::RngOrdIdl,oo::SeqEnum[RngIntElt])
 -> GrpDrchNFElt
{Restrict the given Dirichlet character to the given modulus and real places}
 return Restrict(chi,DirichletGroup(I,oo)); end intrinsic;

intrinsic Restrict(D::GrpDrchNF,I::RngOrdIdl) -> GrpDrchNF
{Given a group of Dirichlet characters and a modulus,
 restrict the group to that modulus}
 return Restrict(D,DirichletGroup(I,[])); end intrinsic;

intrinsic Restrict(D::GrpDrchNF,I::RngOrdIdl,oo::SeqEnum[RngIntElt])
 -> GrpDrchNF
{Given a group of Dirichlet characters and a modulus and real places,
 restrict the group to that modulus}
 return Restrict(D,DirichletGroup(I,oo)); end intrinsic;

intrinsic Restrict(D::GrpDrchNF,T::GrpDrchNF) -> GrpDrchNF
{Given two groups of Dirichlet characters, restrict the first
 to the modulus of the second, intersecting with the second group}
 if #D eq 1 then return sub<T|[]>; end if;
 return sub<T|[Restrict(chi,T) : chi in Generators(D)]>; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic Decomposition(chi::GrpDrchNFElt) -> List
{Decomposition of a given Dirichlet character as a
 product of characters at prime power moduli and real places}
 if assigned chi`decomp then return chi`decomp; end if; DG:=DirichletGroup;
 G:=chi`Parent; F:=Factorization(G`Modulus); L:=[* *]; oo:=G`ooReal;
 if G`issubgroup then CHI:=G`supergroup!chi; else CHI:=chi; end if;
 for f in F do r:=Ioo_restrict(CHI,DG(f[1]^f[2],[]));
                  Append(~L,prime_power_primitive(r)); end for;
 for e in oo do
  Append(~L,Ioo_restrict(CHI,DG(1*IntegerRing(G`NF),[e]))); end for;
 chi`decomp:=L; CHI`decomp:=L; return L; end intrinsic;

intrinsic Components(chi::GrpDrchNFElt) -> Assoc
{Given a Dirichlet character, return its components as an associative array
 indexed by ramified places}
 if assigned chi`components then return chi`components; end if;
 K:=chi`Parent`NF; D:=Decomposition(chi); A:=AssociativeArray();
 for d in D do
  if not ModulusIsFinite(d) then A[InfinitePlaces(K)[d`Parent`ooReal[1]]]:=d;
  else A[Place(Factorization(d`Parent`Modulus)[1][1])]:=d; end if; end for;
 chi`components:=A; return A; end intrinsic;

intrinsic Component(chi::GrpDrchNFElt,P::RngOrdIdl) -> GrpDrchNFElt
{Given a Dirichlet character, return its component at P (a prime ideal)}
 require IsPrime(P): "P must be prime"; K:=chi`Parent`NF;
 require K eq NumberField(Order(P)):
 "chi and P must be defined over same number field";
 C:=Components(chi); P:=Place(P);
 if not P in Keys(C) then return DirichletGroup(1*Integers(K)).0; end if;
 return C[P]; end intrinsic;

intrinsic Component(chi::GrpDrchNFElt,oo::RngIntElt) -> GrpDrchNFElt
{Given a Dirichlet character, return its component at an infinite place}
 K:=chi`Parent`NF; IP:=InfinitePlaces(K); C:=Components(chi);
 require oo ge 1 and oo le #IP: "Invalid infinite place specified"; P:=IP[oo];
 if not P in Keys(C) then return DirichletGroup(1*Integers(K)).0; end if;
 return C[P]; end intrinsic;

intrinsic Component(chi::GrpDrchNFElt,p::PlcNumElt) -> GrpDrchNFElt
{Given a Dirichlet character, return its component at a given place}
 K:=chi`Parent`NF; C:=Components(chi);
 require K eq NumberField(p): "chi and p must be defined over same NF";
 if not p in Keys(C) then return DirichletGroup(1*Integers(K)).0; end if;
 return C[p]; end intrinsic;

intrinsic AssociatedPrimitiveCharacter(chi::GrpDrchNFElt) -> GrpDrchNFElt
{The primitive character corresponding to the given Dirichlet character}
 D:=Decomposition(chi); D:=[* x : x in D | not IsTrivial(x) *];
 O:=1*IntegerRing(chi`Parent`NF);
 M:=&*[Parent(O) | x`Parent`Modulus : x in D | ModulusIsFinite(x)];
 oo:=&cat[x`Parent`ooReal : x in D | not ModulusIsFinite(x)];
 G:=DirichletGroup(M,oo); if #D eq 0 then return G.0; end if;
 return &*[Extend(x,G) : x in D]; end intrinsic;

intrinsic ModulusIsFinite(chi::GrpDrchNFElt) -> BoolElt
{Whether the modulus of a Dirichlet character contains only finite places}
 return #chi`Parent`ooReal eq 0; end intrinsic;

intrinsic ModulusIsFinite(G::GrpDrchNF) -> BoolElt
{Whether the modulus of a Dirichlet group contains only finite places}
 return #G`ooReal eq 0; end intrinsic;

intrinsic IsPrimitive(chi::GrpDrchNFElt) -> BoolElt
{Returns whether a Dirichlet character is primitive}
 C,ooC:=Conductor(chi);
 return C eq Modulus(chi) and ooC eq chi`Parent`ooReal; end intrinsic;

intrinsic TargetRestriction(D::GrpDrchNF,K::FldCyc) -> GrpDrchNF
{The subgroup of a given Dirichlet group whose range of values is in K}
 c:=CyclotomicOrder(K); if IsOdd(c) then c:=2*c; end if;
 return sub<D|[D.i^(o div Gcd(o,c)) where o:=Order(D.i): i in [1..Ngens(D)]]>;
 end intrinsic;

intrinsic One(G::GrpDrchNF) -> GrpDrchNFElt
{Returns the identity element of a Dirichlet group}
 return G.0; end intrinsic;

intrinsic Id(G::GrpDrchNF) -> GrpDrchNFElt
{Returns the identity element of a Dirichlet group}
 return G.0; end intrinsic;

intrinsic Order(chi::GrpDrchNFElt) -> RngIntElt
{Returns the order of a Dirichlet character}
 return Order(chi`Parent`AbGrp!Eltseq(chi)); end intrinsic;

intrinsic Random(G::GrpDrchNF) -> GrpDrchNFElt
{Returns a random Dirichlet character of a Dirichlet group}
 return G!Eltseq(Random(G`AbGrp)); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic DirichletGroup(I::RngOrdIdl : Target:=0) -> GrpDrchNF
{Returns the dual character group for (O/I)^*}
 return DirichletGroup(I,[] : Target:=Target); end intrinsic;

intrinsic
 DirichletGroup(I::RngOrdIdl,oo::SeqEnum[RngIntElt] : Target:=0) -> GrpDrchNF
{Returns the dual character group for (O/Ioo)^*}
 require IsAbsoluteField(NumberField(Order(I))):
   "The ideal must be over an absolute field (over Q)";
 K:=NumberField(Order(I)); r,c:=Signature(K);
 require &and[ii ge 1 and ii le r : ii in oo]:
 "Given real places are not compatible with the number field";
 G:=New(GrpDrchNF); G`supergroup:=G; G`issubgroup:=false;
 if true then MO:=MaximalOrder(K); _:=ClassGroup(MO); _:=IndependentUnits(MO);
  SetOrderUnitsAreFundamental(MO); end if;
 G`Modulus:=I; G`ooReal:=oo; G`NF:=NumberField(Order(I));
 R,G`ResidueMap:=RayResidueRingN(I,oo);
 G`AbGrp,G`Pairing:=Dual(R : UseSameGroup); m:=Modulus(Codomain(G`Pairing));
 if m lt 2^30 then K:=CyclotomicField(m : Sparse:=(m gt 10^3));
  G`TargetRing:=K; AssignNames(~K,["zeta_"*IntegerToString(m)]);
 else G`TargetRing:="a large Cyclotomic ring"; end if; G`CycloOrder:=m;
 if Target cmpne 0 then G:=TargetRestriction(G,Target); end if;
 return G; end intrinsic;

intrinsic '@'(e::RngIntElt,chi::GrpDrchNFElt : Raw:=false) -> RngElt {eval}
 return '@'(chi`Parent`NF!e,chi : Raw:=Raw); end intrinsic;

intrinsic '@'(e::FldRatElt,chi::GrpDrchNFElt : Raw:=false) -> RngElt {"} //"
 return '@'(chi`Parent`NF!e,chi : Raw:=Raw); end intrinsic;

intrinsic '@'(e::RngOrdElt,chi::GrpDrchNFElt : Raw:=false) -> RngElt {"} //"
 K:=chi`Parent`NF; return '@'(K!e,chi : Raw:=Raw); end intrinsic;

intrinsic '@'(e::FldNumElt,chi::GrpDrchNFElt : Raw:=false) -> RngElt {"} //"
 G:=chi`Parent; K:=Parent(e); O:=IntegerRing(K);
 if G`issubgroup then return '@'(e,G`supergroup!chi : Raw:=Raw); end if;
 require K eq G`NF: "Element must be compatible with the character";
 if Numerator(Norm(Gcd(e*O,G`Modulus))) ne 1 then return 0; end if;
 require Numerator(Norm(Gcd((1/e)*O,G`Modulus))) eq 1:
  "The element must be invertible modulo the ideal";
 u:=G`Pairing((G`NF!e) @@ G`ResidueMap,(G`AbGrp)!(chi`Element));
 if Raw then return u; end if;
 m:=Modulus(Parent(u)); r:=Integers()!u; g:=Gcd(m,r);
 if assigned chi`Zeta then return chi`Zeta^((r*chi`ZetaOrder) div m); end if;
 return CyclotomicField(m div g).1^(r div g); end intrinsic;

intrinsic SetTargetRing(~chi::GrpDrchNFElt,e::RngElt)
{Given a Dirichlet character and a root of unity in a ring,
 modify the Dirichlet character to take values in this ring.}
 b,o:=IsRootOfUnity(e); require b: "Ring element must be root of unity";
 c:=Order(chi); require o mod c eq 0: "Order(chi) must divide Order(ring elt)";
 chi`Zeta:=e; chi`ZetaOrder:=o; return; end intrinsic;
// hmm, this doesn't change the target ring of the Parent...

////////////////////////////////////////////////////////////////////////

function cyclo_to_Zm(x) // baby steps giant steps
 if x eq 1 then return Integers(1)!0; end if;
 if x eq -1 then return Integers(2)!1; end if;
 if Type(x) ne FldCycElt then error "Field of image not cyclotomic"; end if;
 K:=Parent(x); r:=CyclotomicOrder(K);
 if IsOdd(r) then r:=2*r; K:=CyclotomicField(r); end if; e:=K.1; x:=K!x;
 s:=Ceiling(Sqrt(r)); B:=[K|x/e^i : i in [1..s]]; G:=[K|e^(s*j) : j in [1..s]];
 S:=Set(B) meet Set(G);
 if #S eq 0 then error "Cyclotomic image is not finite order?"; end if;
 w:=Random(S); wb:=Index(B,w); wg:=Index(G,w);
 return Integers(r)!(s*wg+wb); end function;

intrinsic DirichletCharacter(I::RngOrdIdl,L::List : RequireGenerators:=true)
 -> GrpDrchNFElt, GrpDrchNF
  { Given an ideal for the modulus (possibly with oo-information)
    or a DirichletCharacterGroup (GrpDrchNF), and a list/tuple of
    <FldNumElt,Integers(m)!r> tuples, return a Dirichlet character
    corresponding to this information.
   The second element of any pair can also be a torsion unit of a cyclotomic
   field. If RequireGenerators is not true, then the given elements need not
   generate the RayResidueRing, and a subgroup of characters that are 1 on all
   given preimages is also returned.}
 return DirichletCharacter
   (I,<b : b in L> : RequireGenerators:=RequireGenerators); end intrinsic;

intrinsic DirichletCharacter(I::RngOrdIdl,B::Tup : RequireGenerators:=true)
  -> GrpDrchNFElt, GrpDrchNF {"} //"
 G:=DirichletGroup(I,[]); RG:=RequireGenerators;
 return DirichletCharacter(G,B : RequireGenerators:=RG); end intrinsic;

intrinsic DirichletCharacter
(I::RngOrdIdl,oo::SeqEnum[RngIntElt],L::List : RequireGenerators:=true)
  -> GrpDrchNFElt, GrpDrchNF {"} //"
 return DirichletCharacter
    (I,oo,<b : b in L> : RequireGenerators:=RequireGenerators); end intrinsic;

intrinsic DirichletCharacter
(I::RngOrdIdl,oo::SeqEnum[RngIntElt],B::Tup : RequireGenerators:=true)
  -> GrpDrchNFElt, GrpDrchNF {"} //"
 G:=DirichletGroup(I,oo); RG:=RequireGenerators;
 return DirichletCharacter(G,B : RequireGenerators:=RG); end intrinsic;

 intrinsic DirichletCharacter(DG::GrpDrchNF,L::List : RequireGenerators:=true)
  -> GrpDrchNFElt, GrpDrchNF {"} //"
 return DirichletCharacter
   (DG,<b : b in L> : RequireGenerators:=RequireGenerators); end intrinsic;

intrinsic DirichletCharacter(DG::GrpDrchNF,B::Tup : RequireGenerators:=true)
  -> GrpDrchNFElt, GrpDrchNF {"} //"
 if DG`issubgroup then RG:=RequireGenerators;
  r,K:=DirichletCharacter(DG`supergroup,B : RequireGenerators:=RG);
  require r in DG: "Data not compatible with given Dirichlet subgroup";
  return DG!r,DG meet K; end if;
 require &and[IsCoercible(Codomain(DG`ResidueMap),b[1]) : b in B]:
  "Elements in tuples must be in the same number field as the character";
 rm:=DG`ResidueMap; RR:=Domain(rm); Bg:=[b[1] @@ rm: b in B]; S:=sub<RR|Bg>;
 require not RequireGenerators or S eq RR:
  "Given elements do not generate RayResidueRing";
 if #B eq 0 then return DG.0,DG; end if;
 C:=<<b[1],Type(b[2]) ne RngIntResElt select // cyclo switch
           cyclo_to_Zm(b[2]) else b[2]> : b in B>; B:=C;
 Bi:=<b[2] : b in B>; Bi:=<<Modulus(Parent(b)),Z!b> : b in Bi>;
 Bi:=<<(b[1] div g),(b[2] div g) where g:=Gcd(b[1],b[2])> : b in Bi>;
 MOD:=DG`CycloOrder;
 require &and[MOD mod b[1] eq 0 : b in Bi]:
  "Cyclotomic elements do not have compatible degrees";
 Bi:=[Integers(MOD)!(b[2]*(MOD div b[1])) : b in Bi];
 DS,ic:=DirectSum([AbelianGroup([MOD]) : i in [1..#B]]);
 h:=hom<DG`AbGrp->DS|
        [&+[ic[i](Domain(ic[i])![Z!DG`Pairing(Bg[i],RR.j)]) : i in [1..#B]]
	  : j in [1..Ngens(RR)]]>; // use of RR is a cheat -- should DG`AbGrp
 t:=&+[ic[i](Domain(ic[i])![Z!Bi[i]]) : i in [1..#B]];
 b,e:=HasPreimage(t,h); require b: "Given elements/images are not consistent";
 e:=simple_pullback(t,h); assert h(e) eq t;
 return DG!Eltseq(e),
        sub<DG|[DG!Eltseq(DG`AbGrp!k) : k in Generators(Kernel(h))]>;
 end intrinsic;

intrinsic CentralCharacter(chi::GrpDrchNFElt) -> GrpDrchNFElt
{Given a Dirichlet character, compute its central character down to Q}
 n:=Norm(Modulus(Parent(chi)));
 Q:=NumberField(Polynomial([-1,1]) : DoLinearExtension);
 G:=DirichletGroup(n*IntegerRing(Q),[1]); // just include oo
 mI:=G`ResidueMap; RI:=Domain(mI); reps:=[mI(RI.i) : i in [1..Ngens(RI)]];
 ch:=DirichletCharacter(G,<<r,'@'(r,chi : Raw)> : r in reps>);
 ch:=AssociatedPrimitiveCharacter(ch);
 return sub<Parent(ch)|[ch]>!ch; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic DirichletCharacterOverQ(chi::GrpDrchNFElt) -> GrpDrchElt
{Given a Dirichlet character defined over Q as a number field,
 return the corresponding character defined over Q as the rationals}
 require Degree(Parent(chi)`NF) eq 1: "Must be a Dirichlet character over Q";
 _,oo:=Conductor(chi); require #oo eq 0: "Conductor at oo must be trivial";
 G:=DirichletGroup(Norm(Modulus(chi)),CyclotomicField(Order(chi)));
 V:=[chi(n) : n in UnitGenerators(G)];
 return DirichletCharacterFromValuesOnUnitGenerators(G,V); end intrinsic;

function fixedQasNF() return CyclotomicField(1); end function;

intrinsic DirichletCharacterOverNF(chi::GrpDrchElt) -> GrpDrchNFElt
{Given a Dirichlet character defined over Q, return the corresponding
character defined over Q as a number field (namely the first cyclotomic field)}
 G:=DirichletGroup(Modulus(chi)*Integers(fixedQasNF()),[]);
 mI:=G`ResidueMap; RI:=Domain(mI); reps:=[mI(RI.i) : i in [1..Ngens(RI)]];
 ch:=DirichletCharacter(G,<<r,chi(Integers()!r)> : r in reps>);
 return sub<Parent(ch)|[ch]>!ch; end intrinsic;

intrinsic DirichletCharacterOverNF(chi::GrpDrchElt,K::FldNum) -> GrpDrchNFElt
{Given a Dirichlet character defined over Q, return the corresponding
 character defined over K, which is a copy of Q as a number field}
 require Degree(K) eq 1: "K must be a linear extension of the rationals";
 G:=DirichletGroup(Modulus(chi)*Integers(K),[]);
 mI:=G`ResidueMap; RI:=Domain(mI); reps:=[mI(RI.i) : i in [1..Ngens(RI)]];
 ch:=DirichletCharacter(G,<<r,chi(Integers()!r)> : r in reps>);
 return sub<Parent(ch)|[ch]>!ch; end intrinsic;
