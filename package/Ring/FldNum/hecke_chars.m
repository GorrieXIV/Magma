
freeze;

/****************************************************************/
// Hecke Characters OVER number fields
/****************************************************************/

declare type GrpHeckeElt;
declare type GrpHecke [GrpHeckeElt];

import "dirichlet_chars.m" : dump_abelian, Ioo_extend, cyclo_to_Zm;
import "grossenchar.m" : simple_pullback;

////////////////////////////////////////////////////////////////////////
//                AND NOW FOR HECKE CHARACTERS (ON IDEALS)            //
////////////////////////////////////////////////////////////////////////

declare attributes GrpHecke:
 Name,NF,Modulus,AbGrp,Pairing,TargetRing,CycloOrder,
 rcgmap,ooReal,Labels,supergroup,issubgroup,inclmap;
declare attributes GrpHeckeElt: Parent,Element,cond,dr,ooC,Zeta,ZetaOrder;

Z:=Integers();

intrinsic AssignNames(~G::GrpHecke, S::[MonStgElt])
{Assign names to the generators of G.}
 require #S eq Ngens(G`AbGrp) : "Argument 2 must have length", Ngens(G`AbGrp);
 G`Labels := S; end intrinsic;

intrinsic Name(G::GrpHecke,i::RngIntElt) -> GrpHeckeElt
{The ith generator.}
 require i ge 1 : "Argument 2 must be positive";
 require i le Ngens(G) : "Argument 2 can be at most", Ngens(G); return G.i;
 end intrinsic;

intrinsic Ngens(G::GrpHecke) -> RngIntElt {Ngens}
 return Ngens(G`AbGrp); end intrinsic;

intrinsic PrintNamed(G::GrpHecke,level::MonStgElt,name::MonStgElt)
{Print Hecke character group}
 dump_abelian(G`AbGrp); printf "\n"; oo:=G`ooReal;
 if G`issubgroup then printf "Subgroup "; else printf "Group "; end if;
 if name ne "$" then G`Name:=name;
  printf "of Hecke characters %o of modulus of norm %o",
          name,Norm(G`Modulus);
 else printf "of Hecke characters of modulus of norm %o",
              Norm(G`Modulus); end if;
 if #oo ne 0 then printf " and infinite places %o",oo; end if;
 printf " over %o mapping to %o",G`NF,G`TargetRing; end intrinsic;

intrinsic Print(G::GrpHecke,level::MonStgElt) {Print Hecke character}
 name:="$"; dump_abelian(G`AbGrp); printf "\n"; oo:=G`ooReal;
 if G`issubgroup then printf "Subgroup "; else printf "Group "; end if;
 if name ne "$" then G`Name:=name;
  printf "of Hecke characters %o of modulus of norm %o",
          name,Norm(G`Modulus);
 else printf "of Hecke characters of modulus of norm %o",
              Norm(G`Modulus); end if;
 if #oo ne 0 then printf " and infinite places %o",oo; end if;
 printf " over %o mapping to %o",G`NF,G`TargetRing; end intrinsic;

intrinsic PrintNamed(psi::GrpHeckeElt,level::MonStgElt,name::MonStgElt)
{Print Hecke character}
 G:=psi`Parent; S:=Eltseq(G`AbGrp!(psi`Element));
 if not assigned(G`Name) then NAME:="$"; else NAME:=G`Name; end if;
 I:=[i : i in [1..#S] | S[i] ne 0];
 if #I eq 0 then printf "1";
 elif assigned G`Labels then
      for i in [1..#I] do if i ne 1 then printf "*"; end if;
       printf "%o",G`Labels[I[i]];
       if S[I[i]] ne 1 then printf "^%o",S[I[i]]; end if; end for;
 else for i in [1..#I] do if i ne 1 then printf "*"; end if;
       printf "%o.%o",NAME,I[i]; if S[I[i]] ne 1 then printf "^%o",S[I[i]];
        end if; end for; end if; end intrinsic;

intrinsic Print(psi::GrpHeckeElt,level::MonStgElt) {Print Hecke character}
 name:="$"; G:=psi`Parent; S:=Eltseq(G`AbGrp!(psi`Element));
 if not assigned(G`Name) then NAME:="$"; else NAME:=G`Name; end if;
 I:=[i : i in [1..#S] | S[i] ne 0];
 if #I eq 0 then printf "1";
 elif assigned G`Labels then
      for i in [1..#I] do if i ne 1 then printf "*"; end if;
       printf "%o",G`Labels[I[i]];
       if S[I[i]] ne 1 then printf "^%o",S[I[i]]; end if; end for;
 else for i in [1..#I] do if i ne 1 then printf "*"; end if;
       printf "%o.%o",NAME,I[i]; if S[I[i]] ne 1 then printf "^%o",S[I[i]];
        end if; end for; end if; end intrinsic;

intrinsic Parent(psi::GrpHeckeElt) -> GrpHecke {Parent}
 return psi`Parent; end intrinsic;

intrinsic 'in'(e::.,G::GrpHecke) -> BoolElt {in}
 if Type(e) ne GrpHeckeElt then return false; end if;
 if e`Parent`supergroup ne G`supergroup then return false; end if;
 return G`supergroup`AbGrp!e`Parent`AbGrp!e`Element in G`AbGrp; end intrinsic;

intrinsic SubConstr
 (G::GrpHecke,E::SeqEnum[GrpHeckeElt]) -> GrpHecke, Map {sub}
 if #E gt 0 and E[1]`Parent ne G then
 return "Elements on RHS must be in HeckeGroup",_; end if;
 S:=New(GrpHecke); S`NF:=G`NF;
 S`Modulus:=G`Modulus; S`ooReal:=G`ooReal; S`rcgmap:=G`rcgmap;
 S`supergroup:=G`supergroup; S`issubgroup:=true;
 S`AbGrp,mp:=sub<G`supergroup`AbGrp|
                 [G`supergroup`AbGrp!Eltseq(G`supergroup!x) : x in E]>;
 if #S`AbGrp eq #G`AbGrp then // try to fix Z/2 x Z/3 vs Z/6 equality prob
  S`AbGrp:=G`AbGrp; mp:=map<S`AbGrp->G`AbGrp|x:->x>; end if;
 e:=Exponent(S`AbGrp); S`CycloOrder:=e;
 if e lt 2^30 then S`TargetRing:=CyclotomicField(e : Sparse:=(e ge 10^3));
 else S`TargetRing:="a large Cyclotomic ring"; end if;
 S`inclmap:=map<S->G|x:->G!Eltseq(G`AbGrp!mp(S`AbGrp!x`Element))>;
 return S,S`inclmap;  end intrinsic;

intrinsic Elements(G::GrpHecke) -> SeqEnum {Elements}
 return [G!Eltseq(x) : x in G`AbGrp]; end intrinsic;

intrinsic Generators(G::GrpHecke) -> Set {Generators}
 return {G.i : i in [1..Ngens(G)]}; end intrinsic;

intrinsic '+'(G::GrpHecke,H::GrpHecke) -> GrpHecke {Add}
 require G`NF cmpeq H`NF and G`Modulus cmpeq H`Modulus
  and G`ooReal eq H`ooReal: "Groups must have same modulus to add them";
 GS:=G`supergroup`AbGrp; HS:=H`supergroup`AbGrp; T:=H`supergroup;
// i:=iso<GS->HS|[<GS.i,HS.i> : i in [1..Ngens(GS)]]>; // unnecessary here
 S:=sub<T|[T!Eltseq(GS!x) : x in Generators(G`AbGrp)] cat
          [T!Eltseq(HS!x) : x in Generators(H`AbGrp)]>;
 return S; end intrinsic;

intrinsic 'meet'(G::GrpHecke,H::GrpHecke) -> GrpHecke {meet}
 require G`NF cmpeq H`NF and G`Modulus cmpeq H`Modulus
  and G`ooReal eq H`ooReal: "Groups need same modulus to intersect them";
 GS:=G`supergroup`AbGrp; HS:=H`supergroup`AbGrp; T:=H`supergroup;
 if #GS eq 1 then return sub<G|[]>; end if;
 i:=iso<GS->HS|[<GS.i,HS.i> : i in [1..Ngens(GS)]]>;
 S:=sub<H|[H!T!Eltseq(HS!g) : g in Generators(i(G`AbGrp) meet H`AbGrp)]>;
 return S; end intrinsic;

intrinsic 'eq'(G::GrpHecke,H::GrpHecke) -> BoolElt {eq}
 if G`NF cmpne H`NF or G`Modulus cmpne H`Modulus
                    or G`ooReal ne H`ooReal then return false; end if;
 GS:=G`supergroup`AbGrp; HS:=H`supergroup`AbGrp;
 if #GS eq 1 then return #HS eq 1; end if;
 i:=iso<GS->HS|[<GS.i,HS.i> : i in [1..Ngens(GS)]]>;
 return i(G`AbGrp) eq H`AbGrp; end intrinsic;

intrinsic 'subset'(G::GrpHecke,H::GrpHecke) -> BoolElt {subset}
 if G`NF cmpne H`NF or G`Modulus cmpne H`Modulus
                    or G`ooReal ne H`ooReal then return false; end if;
 GS:=G`supergroup`AbGrp; HS:=H`supergroup`AbGrp;
 if #GS eq 1 then return true; end if;
 i:=iso<GS->HS|[<GS.i,HS.i> : i in [1..Ngens(GS)]]>;
 return i(G`AbGrp) subset H`AbGrp; end intrinsic;

intrinsic 'eq'(x::GrpHeckeElt,y::GrpHeckeElt) -> BoolElt {eq}
 if x`Parent`supergroup ne y`Parent`supergroup then return false; end if;
 return Eltseq((x`Parent`supergroup)!x) eq Eltseq((y`Parent`supergroup)!y);
 end intrinsic;

intrinsic IsCoercible(G::GrpHecke,e::.) -> BoolElt, GrpHeckeElt {Coerce}
 if Type(e) eq GrpHeckeElt then P:=e`Parent;
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
 if Type(e) eq SeqEnum then x:=New(GrpHeckeElt);
  x`Parent:=G; x`Element:=Eltseq((G`AbGrp)!e); return true,x; end if;
 return false,"Illegal coercion"; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic '.'(G::GrpHecke,i::RngIntElt) -> GrpHeckeElt {element}
 require i ge 0: "Argument 2 must be nonnegative";
 require i le Ngens(G`AbGrp): "Argument 2 can be at most",Ngens(G`AbGrp);
 x:=New(GrpHeckeElt);
 x`Parent:=G; x`Element:=Eltseq((G`AbGrp).i); return x; end intrinsic;

intrinsic '^'(psi::GrpHeckeElt,i::RngIntElt) -> GrpHeckeElt {Power}
 x:=New(GrpHeckeElt); x`Parent:=psi`Parent; G:=x`Parent;
 x`Element:=Eltseq(G`AbGrp![i*a : a in psi`Element]); return x; end intrinsic;

intrinsic '*'(chi::GrpDrchNFElt,psi::GrpHeckeElt) -> GrpHeckeElt {Multiply}
 require chi`Parent`NF eq psi`Parent`NF: "Chars must be over same field";
 require IsTrivialOnUnits(chi): "Dirichlet character must be unit-trivial";
 return HeckeLift(chi)*psi; end intrinsic;

intrinsic '*'(psi::GrpHeckeElt,chi::GrpDrchNFElt) -> GrpHeckeElt {"} //"
 require chi`Parent`NF eq psi`Parent`NF: "Chars must be over same field";
 require IsTrivialOnUnits(chi): "Dirichlet character must be unit-trivial";
 return HeckeLift(chi)*psi; end intrinsic;

intrinsic '*'(x::GrpHeckeElt,y::GrpHeckeElt) -> GrpHeckeElt {"} //"
 A:=x`Parent; B:=y`Parent; I:=A`Modulus; J:=B`Modulus;
 require A`NF eq B`NF: "Characters must be over same number field";
 if I eq J and A`ooReal eq B`ooReal then
  if not A`issubgroup and not B`issubgroup then
   G:=x`Parent`AbGrp; z:=New(GrpHeckeElt); z`Parent:=x`Parent;
   z`Element:=Eltseq((G!x`Element)+(G!y`Element)); return z;
  else z:=(A`supergroup!x)*(B`supergroup!y);
   if A subset B then return B!z; elif B subset A then return A!z;
   else return z; end if; end if;
 else oo:=Sort(SetToSequence(Set(A`ooReal) join Set(B`ooReal)));
  L:=HeckeCharacterGroup(LCM(I,J),oo); return Extend(x,L)*Extend(y,L); end if;
  end intrinsic;

intrinsic '/'(chi::GrpDrchNFElt,psi::GrpHeckeElt) -> GrpHeckeElt {Divide}
 require chi`Parent`NF eq psi`Parent`NF: "Chars must be over same field";
 require IsTrivialOnUnits(chi): "Dirichlet character must be unit-trivial";
 return HeckeLift(chi)/psi; end intrinsic;

intrinsic '/'(psi::GrpHeckeElt,chi::GrpDrchNFElt) -> GrpHeckeElt {"} //"
 require chi`Parent`NF eq psi`Parent`NF: "Chars must be over same field";
 require IsTrivialOnUnits(chi): "Dirichlet character must be unit-trivial";
 return psi/HeckeLift(chi); end intrinsic;

intrinsic '/'(x::GrpHeckeElt,y::GrpHeckeElt) -> GrpHeckeElt {"} //"
 require x`Parent`NF eq y`Parent`NF: "Characters must be over same field";
 return x*y^(-1); end intrinsic;

intrinsic '/'(e::RngIntElt,y::GrpHeckeElt) -> GrpHeckeElt {"} //"
 require e eq 1: "Must have 1 as the numerator"; return y^(-1); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic '#'(G::GrpHecke) -> RngInt {Order} return #G`AbGrp; end intrinsic;

intrinsic AbelianGroup(G::GrpHecke) -> GrpAb,Map
{Returns an abstract AbelianGroup for the group of Hecke characters}
 A:=G`AbGrp; return A,map<A->G|x:->G!Eltseq(x)>; end intrinsic;

intrinsic Eltseq(psi::GrpHeckeElt) -> SeqEnum {Eltseq}
 return psi`Element; end intrinsic;

intrinsic Domain(psi::GrpHeckeElt) -> PowIdl
{Returns the domain of a Hecke character}
 return Codomain(psi`Parent`rcgmap); end intrinsic;

intrinsic Domain(G::GrpHecke) -> PowIdl
{Returns the domain of a Hecke character group}
 return Codomain(G`rcgmap); end intrinsic;

intrinsic Modulus(psi::GrpHeckeElt) -> RngOrdIdl, SeqEnum
{Returns the modulus of a Hecke character}
 return psi`Parent`Modulus,psi`Parent`ooReal; end intrinsic;

intrinsic Modulus(G::GrpHecke) -> RngOrdIdl, SeqEnum
{Returns the modulus of a Hecke character group}
 return G`Modulus,G`ooReal; end intrinsic;

intrinsic IsTrivial(psi::GrpHeckeElt) -> BoolElt
{Returns whether a Hecke character is trivial}
 return &and[e eq 0: e in Eltseq(psi)]; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic HeckeCharacterGroup(I::RngOrdIdl,oo::SeqEnum[RngIntElt] : Target:=0)
 -> GrpHecke
{Character group on ideals (rather than K-elements),
 and is the Dual of RayClassGroup}
 require IsAbsoluteField(NumberField(Order(I))):
   "The ideal must be over an absolute field (over Q)";
 K:=NumberField(Order(I)); r,c:=Signature(K);
 require &and[ii ge 1 and ii le r : ii in oo]:
 "Given real places are not compatible with the number field";
 H:=New(GrpHecke); H`Modulus:=I; H`ooReal:=oo; H`NF:=K;
 H`supergroup:=H; H`issubgroup:=false;
 MO:=MaximalOrder(H`NF); _:=ClassGroup(MO); _:=IndependentUnits(MO);
 SetOrderUnitsAreFundamental(MO); RCG,H`rcgmap:=RayClassGroup(I,oo);
 H`AbGrp,H`Pairing:=Dual(RCG : UseSameGroup); m:=Modulus(Codomain(H`Pairing));
 H`CycloOrder:=m;
 if m lt 2^30 then K:=CyclotomicField(m : Sparse:=(m gt 10^3));
  AssignNames(~K,["zeta_"*IntegerToString(m)]); H`TargetRing:=K;
 else H`TargetRing:="a large Cyclotomic ring"; end if;
 if Target cmpne 0 then H:=TargetRestriction(H,Target); end if;
 return H; end intrinsic;

intrinsic HeckeCharacterGroup(I::RngOrdIdl : Target:=0) -> GrpHecke {"} //"
 return HeckeCharacterGroup(I,[] : Target:=Target); end intrinsic;

intrinsic '@'(e::RngIntElt,psi::GrpHeckeElt : Raw:=false) -> RngElt {eval}
 K:=psi`Parent`NF; return '@'(e*IntegerRing(K),psi : Raw:=Raw); end intrinsic;

intrinsic '@'(e::FldRatElt,psi::GrpHeckeElt : Raw:=false) -> RngElt {"} //"
 K:=psi`Parent`NF; return '@'(e*IntegerRing(K),psi : Raw:=Raw); end intrinsic;

intrinsic '@'(e::RngOrdElt,psi::GrpHeckeElt : Raw:=false) -> RngElt {"} //"
 K:=psi`Parent`NF; return '@'(K!e,psi : Raw:=Raw); end intrinsic;

intrinsic '@'(e::FldNumElt,psi::GrpHeckeElt : Raw:=false) -> RngElt {"} //"
 H:=psi`Parent; K:=Parent(e);
 require K eq H`NF: "Element must be compatible with the character";
 return '@'(e*IntegerRing(K),psi : Raw:=Raw); end intrinsic;

intrinsic '@'(J::RngOrdFracIdl,psi::GrpHeckeElt : Raw:=false) -> RngElt {"}//"
 H:=psi`Parent; F:=H`NF; I:=H`Modulus; K:=NumberField(Order(J));
 if H`issubgroup then return '@'(J,H`supergroup!psi : Raw:=Raw); end if;
 require K eq F: "The ideal must be compatible with the character";
 if Numerator(Norm(Gcd(J,I))) ne 1 then return 0; end if; d:=Denominator(J);
 require Numerator(Norm(Gcd(J^(-1),I))) eq 1:
  "Ideal cannot have negative valuation at primes in the modulus";
 u:=H`Pairing(J@@H`rcgmap,(H`AbGrp)!(psi`Element));
 if Raw then return u; end if;
 m:=Modulus(Parent(u)); r:=Integers()!u; g:=Gcd(m,r);
 if assigned psi`Zeta then return psi`Zeta^((r*psi`ZetaOrder) div m); end if;
 return CyclotomicField(m div g).1^(r div g); end intrinsic;

intrinsic SetTargetRing(~psi::GrpHeckeElt,e::RngElt)
{Given a Hecke character and a root of unity in a ring,
 modify the Hecke character to take values in this ring.}
 b,o:=IsRootOfUnity(e); require b: "Ring element must be root of unity";
 c:=Order(psi); require o mod c eq 0: "Order(chi) must divide Order(ring elt)";
 q:=o div c; psi`Zeta:=e; psi`ZetaOrder:=o; return; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic HeckeLift(chi::GrpDrchNFElt) -> GrpHeckeElt, GrpHecke
{Lift a Dirichlet character that is trivial on units to a Hecke character}
 require IsTrivialOnUnits(chi): "Dirichlet character must be trivial on units";
 D:=chi`Parent; H:=HeckeCharacterGroup(D`Modulus,D`ooReal);
 mp:=D`ResidueMap; O:=IntegerRing(D`NF);
 data:=<<mp(g)*O,'@'(mp(g),chi : Raw)> : g in Generators(Domain(mp))>;
 return HeckeCharacter(H,data : RequireGenerators:=false); end intrinsic;

intrinsic DirichletRestriction(psi::GrpHeckeElt) -> GrpDrchNFElt
{Restrict a Hecke character to a Dirichlet character}
 if assigned psi`dr then return psi`dr; end if;
 H:=psi`Parent; D:=DirichletGroup(H`Modulus,H`ooReal); mp:=D`ResidueMap;
 data:=<<mp(g),'@'(mp(g),psi : Raw)> : g in Generators(Domain(mp))>;
 psi`dr:=DirichletCharacter(D,data); return psi`dr; end intrinsic;

intrinsic Conductor(psi::GrpHeckeElt) ->  RngOrdIdl, SeqEnum
{Conductor of a Hecke character}
 if assigned psi`cond then return psi`cond,psi`ooC; end if;
 psi`cond,psi`ooC:=Conductor(DirichletRestriction(psi));
 return psi`cond,psi`ooC; end intrinsic;

intrinsic IsPrimitive(psi::GrpHeckeElt) -> BoolElt
{Whether a Hecke character is primitive} // need to check oo ?
 C,ooC:=Conductor(psi);
 return C eq Modulus(psi) and ooC eq psi`Parent`ooReal; end intrinsic;

intrinsic HilbertCharacterSubgroup(H::GrpHecke) -> GrpHecke, Map
{The subgroup of Hecke characters induced by class group characters,
 and an inclusion map into the given group}
 D:=DirichletGroup(H`Modulus,H`ooReal); mp:=D`ResidueMap;
 data:=<<mp(g)*IntegerRing(H`NF),Integers(1)!0> : g in Generators(Domain(mp))>;
 _,K:=HeckeCharacter(H,data : RequireGenerators:=false);
 return K,K`inclmap; end intrinsic;

intrinsic TargetRestriction(H::GrpHecke,K::FldCyc) -> GrpHecke
{The subgroup of a given Hecke group whose range of values is in K}
 c:=CyclotomicOrder(K); if IsOdd(c) then c:=2*c; end if;
 return sub<H|[H.i^(o div Gcd(o,c)) where o:=Order(H.i): i in [1..Ngens(H)]]>;
 end intrinsic;

intrinsic One(G::GrpHecke) -> GrpHeckeElt
{Returns the identity element of a Hecke group}
 return G.0; end intrinsic;

intrinsic Id(G::GrpHecke) -> GrpHeckeElt
{Returns the identity element of a Hecke group}
 return G.0; end intrinsic;

intrinsic Order(psi::GrpHeckeElt) -> RngIntElt
{Returns the order of a Hecke character}
 return Order(psi`Parent`AbGrp!Eltseq(psi)); end intrinsic;

intrinsic Random(G::GrpHecke) -> GrpHeckeElt
{Returns a random Hecke character of a Hecke group}
 return G!Eltseq(Random(G`AbGrp)); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic Extend(psi::GrpHeckeElt,H::GrpHecke) -> GrpHeckeElt
{Extend a Hecke character to the given Hecke group}
 P:=psi`Parent; require P`NF eq H`NF: "Moduli must be in same number field";
 I:=H`Modulus; J:=P`Modulus; HS:=H`supergroup;
 require I subset J:
  "The modulus of the new group must be divisible by that of the old";
 require P`ooReal subset H`ooReal:
 "Infinite places of the new group must contain those of the old";
 chi:=Ioo_extend(DirichletRestriction(psi),DirichletGroup(H`Modulus,H`ooReal));
 mp:=chi`Parent`ResidueMap; O:=IntegerRing(H`NF); mp2:=H`rcgmap;
 d1:=[* <mp(g)*O,'@'(mp(g),chi : Raw)> : g in Generators(Domain(mp)) *];
 d2:=[* <mp2(g),'@'(mp2(g),psi : Raw)> : g in Generators(Domain(mp2)) *];
 ri:=psi`Parent`rcgmap; RI:=Domain(ri); rj:=mp2; RJ:=Domain(rj);
 h:=InducedMap(H`rcgmap,P`rcgmap, // use InducedMap() ?
               map<Codomain(H`rcgmap)->Codomain(P`rcgmap)|x:->x>,
	       LCM(Minimum(I),Minimum(J))); // KER:=Kernel(h);
// h:=hom<RJ->RI|[rj(RJ.i) @@ ri : i in [1..Ngens(RJ)]]>; KER:=Kernel(h);
// K:=sub<HS|[HS!Eltseq(RJ!k) : k in Generators(KER)]> meet H; // what is this?
 ret:=HeckeCharacter(H,<v : v in d1 cat d2> : RequireGenerators:=false);
 return ret; end intrinsic;

intrinsic Extend(psi::GrpHeckeElt,I::RngOrdIdl) -> GrpHeckeElt
{Given a Hecke character and a modulus, extend to that modulus}
 return Extend(psi,HeckeCharacterGroup(I)); end intrinsic;

intrinsic Extend(psi::GrpHeckeElt,I::RngOrdIdl,oo::SeqEnum[RngIntElt])
 -> GrpHeckeElt
{Given a Hecke character and a modulus with real places, extend the character}
 return Extend(psi,HeckeCharacterGroup(I,oo)); end intrinsic;

intrinsic Extend(H::GrpHecke,I::RngOrdIdl) -> GrpHecke
{Given a group of Hecke characters and a modulus,
 extend the group to that modulus}
 return Extend(H,HeckeCharacterGroup(I,[])); end intrinsic;

intrinsic Extend(H::GrpHecke,I::RngOrdIdl,oo::SeqEnum[RngIntElt]) -> GrpHecke
{Given a group of Hecke characters and a modulus and real places,
 extend the group to that modulus}
 return Extend(H,HeckeCharacterGroup(I,oo)); end intrinsic;

intrinsic Extend(H::GrpHecke,T::GrpHecke) -> GrpHecke
{Given two groups of Hecke characters, extend the first to the modulus
 of the second, intersecting with the second group}
 if #H eq 1 then return sub<T|[T.0]>; end if;
 return &+[sub<T|[e]> where e:=Extend(psi,T) : psi in Generators(H)];
 end intrinsic;

intrinsic Restrict(psi::GrpHeckeElt,H::GrpHecke) -> GrpHeckeElt
{Restrict a Hecke character to the given Hecke group}
 P:=psi`Parent; require P`NF eq H`NF: "Moduli must be in same number field";
 require H`ooReal subset P`ooReal:
 "Infinite places of the group must be contained in those of the character";
 I:=H`Modulus; J:=P`Modulus;
 require J subset I:
 "Modulus of restriction group must divide that of character";
 C,ooC:=Conductor(psi);
 require I subset C:
 "Conductor of the character must divide the modulus of the given group";
 require ooC subset P`ooReal:
 "Infinite places of the conductor must be contained in those of the group";
 mp:=P`rcgmap; // want gens that are coprime to psi, come for free from P
 data:=<<mp(g),'@'(mp(g),psi : Raw)> : g in Generators(Domain(mp))>;
 ret:=HeckeCharacter(H,data); return ret; end intrinsic;

intrinsic Restrict(psi::GrpHeckeElt,I::RngOrdIdl) -> GrpHeckeElt
{Restrict a hecke character to given modulus}
 return Restrict(psi,HeckeCharacterGroup(I)); end intrinsic;

intrinsic Restrict(psi::GrpHeckeElt,I::RngOrdIdl,oo::SeqEnum[RngIntElt])
 -> GrpHeckeElt
{Restrict a hecke character to given modulus and real places}
 return Restrict(psi,HeckeCharacterGroup(I,oo)); end intrinsic;

intrinsic AssociatedPrimitiveCharacter(psi::GrpHeckeElt) -> GrpHeckeElt
{The primitive character associated to the given Hecke character}
 C,ooC:=Conductor(psi);
 return Restrict(psi,HeckeCharacterGroup(C,ooC)); end intrinsic;

intrinsic Restrict(H::GrpHecke,I::RngOrdIdl) -> GrpHecke
{Given a group of Hecke characters and a modulus,
 restrict the group to that modulus}
 return Restrict(H,HeckeCharacterGroup(I,[])); end intrinsic;

intrinsic Restrict(H::GrpHecke,I::RngOrdIdl,oo::SeqEnum[RngIntElt]) -> GrpHecke
{Given a group of Hecke characters and a modulus and real places,
 restrict the group to that modulus}
 return Restrict(H,HeckeCharacterGroup(I,oo)); end intrinsic;

intrinsic Restrict(H::GrpHecke,T::GrpHecke) -> GrpHecke
{Given two groups of Hecke characters, restrict the first
 to the modulus of the second, intersecting with the second group}
 if #H eq 1 then return sub<T|[]>; end if;
 return sub<T|[Restrict(psi,T) : psi in Generators(H)]>; end intrinsic;

////////////////////////////////////////////////////////////////////////

declare attributes GrpHeckeElt : components;

intrinsic Components(psi::GrpHeckeElt) -> Assoc
{Given a Hecke character, return the components of its Dirichlet restriction,
 as an associative array indexed by ramified places}
 if assigned psi`components then return psi`components; end if;
 K:=psi`Parent`NF; D:=Decomposition(DirichletRestriction(psi));
 A:=AssociativeArray();
 for d in D do
  if not ModulusIsFinite(d) then A[InfinitePlaces(K)[d`Parent`ooReal[1]]]:=d;
  else A[Place(Factorization(d`Parent`Modulus)[1][1])]:=d; end if; end for;
 psi`components:=A; return A; end intrinsic;

intrinsic Component(psi::GrpHeckeElt,P::RngOrdIdl) -> GrpDrchNFElt
{Given a Hecke character, return its Dirichlet component at P (a prime ideal)}
 require IsPrime(P): "P must be prime"; K:=psi`Parent`NF;
 require K eq NumberField(Order(P)):
 "chi and P must be defined over same number field";
 C:=Components(psi); P:=Place(P);
 if not P in Keys(C) then return DirichletGroup(1*Integers(K)).0; end if;
 return C[P]; end intrinsic;

intrinsic Component(psi::GrpHeckeElt,oo::RngIntElt) -> GrpDrchNFElt
{Given a Hecke character, return its Dirichlet component at an infinite place}
 K:=psi`Parent`NF; IP:=InfinitePlaces(K); C:=Components(psi);
 require oo ge 1 and oo le #IP: "Invalid infinite place specified"; P:=IP[oo];
 if not P in Keys(C) then return DirichletGroup(1*Integers(K)).0; end if;
 return C[P]; end intrinsic;

intrinsic Component(psi::GrpHeckeElt,p::PlcNumElt) -> GrpDrchNFElt
{Given a Hecke character, return its Dirichlet component at a given place}
 K:=psi`Parent`NF; C:=Components(psi);
 require K eq NumberField(p): "psi and p must be defined over same NF";
 if not p in Keys(C) then return DirichletGroup(1*Integers(K)).0; end if;
 return C[p]; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic HeckeCharacter(I::RngOrdIdl,L::List : RequireGenerators:=true)
 -> GrpHeckeElt, GrpHecke
{ Given an ideal for the modulus (possibly with oo-information)
  or a HeckeCharacterGroup, and a list/tuple of <RngOrdIdl,Integers(m)!r>
  tuples, return a Hecke character corresponding to this information.
  The second element of any pair can also be a torsion unit of a cyclotomic
  field. If RequireGenerators is not true, then the given elements need not
  generate the RayClassGroup, and a subgroup of characters that are 1 on all
  given preimages is also returned.}
 return HeckeCharacter(I,<b : b in L> : RequireGenerators:=RequireGenerators);
 end intrinsic;

intrinsic HeckeCharacter(I::RngOrdIdl,B::Tup : RequireGenerators:=true)
 -> GrpHeckeElt, GrpHecke {"} //"
 G:=HeckeCharacterGroup(I,[]); RG:=RequireGenerators;
 return HeckeCharacter(G,B : RequireGenerators:=RG); end intrinsic;

intrinsic HeckeCharacter
(I::RngOrdIdl,oo::SeqEnum[RngIntElt],L::List : RequireGenerators:=true)
  -> GrpHeckeElt, GrpHecke {"} //"
 return HeckeCharacter(I,oo,<b : b in L> :
		       RequireGenerators:=RequireGenerators); end intrinsic;

intrinsic HeckeCharacter
(I::RngOrdIdl,oo::SeqEnum[RngIntElt],B::Tup : RequireGenerators:=true)
  -> GrpHeckeElt, GrpHecke {"} //"
 G:=HeckeCharacterGroup(I,oo); RG:=RequireGenerators;
 return HeckeCharacter(G,B : RequireGenerators:=RG); end intrinsic;

intrinsic HeckeCharacter(HG::GrpHecke,L::List : RequireGenerators:=true)
  -> GrpHeckeElt, GrpHecke {"} //"
 return HeckeCharacter(HG,<b : b in L>:
		       RequireGenerators:=RequireGenerators); end intrinsic;

intrinsic HeckeCharacter(HG::GrpHecke,B::Tup : RequireGenerators:=true)
 -> GrpHeckeElt, GrpHecke {"} //"
 if HG`issubgroup then
  r,K:=HeckeCharacter(HG`supergroup,B : RequireGenerators:=RequireGenerators);
  require r in HG: "Data not compatible with given Hecke subgroup";
  return HG!r,HG meet K; end if;
 require &and[IsCoercible(Codomain(HG`rcgmap),b[1]) : b in B]:
  "Elements in tuples must be ideals of same number field as the character";
 rcgm:=HG`rcgmap; RCG:=Domain(rcgm); Bg:=[b[1]@@rcgm: b in B]; S:=sub<RCG|Bg>;
 require not RequireGenerators or S eq RCG:
  "Given elements do not generate RayClassGroup";
 if #B eq 0 then return HG.0,HG; end if;
 C:=<<b[1],Type(b[2]) ne RngIntResElt select // cyclo switch 
           cyclo_to_Zm(b[2]) else b[2]> : b in B>; B:=C;
 Bi:=<b[2] : b in B>; Bi:=<<Modulus(Parent(b)),Z!b> : b in Bi>;
 Bi:=<<(b[1] div g),(b[2] div g) where g:=Gcd(b[1],b[2])> : b in Bi>;
 MOD:=HG`CycloOrder;
 require &and[MOD mod b[1] eq 0 : b in Bi]:
  "Cyclotomic elements do not have compatible degrees";
 Bi:=[Integers(MOD)!(b[2]*(MOD div b[1])) : b in Bi];
 DS,ic:=DirectSum([AbelianGroup([MOD]) : i in [1..#B]]);
 h:=hom<HG`AbGrp->DS|
        [&+[ic[i](Domain(ic[i])![Z!HG`Pairing(Bg[i],RCG.j)]) : i in [1..#B]]
	  : j in [1..Ngens(RCG)]]>; // use of RCG is a cheat -- should HG`AbGrp
 t:=&+[ic[i](Domain(ic[i])![Z!Bi[i]]) : i in [1..#B]];
 b,e:=HasPreimage(t,h); require b: "Given elements/images are not consistent";
 e:=simple_pullback(t,h); assert h(e) eq t;
 return HG!Eltseq(e),
        sub<HG|[HG!Eltseq(HG`AbGrp!k) : k in Generators(Kernel(h))]>;;
 end intrinsic;

intrinsic CentralCharacter(psi::GrpHeckeElt) -> GrpDrchNFElt
{Given a Hecke character, compute its central Dirichlet character down to Q}
 n:=Norm(Modulus(Parent(psi)));
 Q:=NumberField(Polynomial([-1,1]) : DoLinearExtension);
 G:=DirichletGroup(n*IntegerRing(Q),[1]); // just include oo
 mI:=G`ResidueMap; RI:=Domain(mI); reps:=[mI(RI.i) : i in [1..Ngens(RI)]];
 ch:=DirichletCharacter(G,<<r,'@'(r,psi : Raw)> : r in reps>);
 ch:=AssociatedPrimitiveCharacter(ch);
 return sub<Parent(ch)|[ch]>!ch; end intrinsic;

////////////////////////////////////////////////////////////////////////

function norm_induction(G,chi) mp:=G`rcgmap; // psi(a)=chi(Norm(a)), psi in G
 B:=<<mp(e),'@'(Norm(mp(e)),chi : Raw)> : e in Generators(Domain(G`rcgmap))>;
 psi:=HeckeCharacter(G,B); return psi; end function;
 // what should the modulus of psi be? // choose large, and AssociatedPrimitive

function norm_induction_nf(K,chi) // psi(a)=chi(Norm(a)), psi "minimal"? 
 I:=Conductor(chi)*Integers(K); oo:=[i : i in [1..Signature(K)]];
 G:=HeckeCharacterGroup(I,oo);
 psi:=norm_induction(G,DirichletCharacterOverNF(chi));
 return AssociatedPrimitiveCharacter(psi); end function;

intrinsic NormInduction(K::FldNum,chi::GrpDrchElt) -> GrpHeckeElt
{Given a number field K and a Dirichlet character chi over Q, induce chi
 to K, that is, psi(a)=chi(Norm(a)), and psi should be of minimal modulus}
 return norm_induction_nf(K,chi); end intrinsic;

function quadratic_char(e) // given e in K, yield Hecke char of K(sqrt(e))
 assert not IsSquare(e); K:=Parent(e); O:=Integers(K); I:=e*O;
 D:=Discriminant(Integers(ext<K|Polynomial([-e,0,1])>));
 G:=HeckeCharacterGroup(D,[i : i in [1..#RealPlaces(K)]]);
 S:=TargetRestriction(G,CyclotomicField(2)); DATA:=[* *]; p:=2; KER:=[];
 while #KER ne 1 do p:=NextPrime(p); // need to skip 2, squares are different
  if Gcd(p,Norm(D)*Discriminant(O)) ne 1 then continue; end if;
  for f in Factorization(p*O) do P:=f[1];
   if Degree(P) ne 1 then continue; end if; // guess this is safe
   R,mp:=ResidueClassField(P); // P is not above 2, so OK I guess
   if mp(e) eq 0 then continue; end if; // could have P^2 dividing e
   b:=IsSquare(mp(e)); DATA cat:=[* <P,b select 1 else -1> *];
   psi,KER:=HeckeCharacter(S,DATA : RequireGenerators:=false);
   if #KER eq 1 then break; end if; end for; end while;
 assert D eq Conductor(psi); psi:=AssociatedPrimitiveCharacter(psi);
 return sub<Parent(psi)|[psi]>!psi; end function;
 // Don't have to worry about Hilbert chars, as covered by genus theory?

intrinsic QuadraticCharacter(e::FldNumElt) -> GrpHeckeElt
{Given a nonzero field element, return the associated quadratic character}
 require e ne 0: "Field element cannot be zero";
 require IsAbsoluteField(Parent(e)): "Field must be absolute";
 if IsSquare(e) then psi:=HeckeCharacterGroup(1*Integers(Parent(e))).0;
                     return sub<Parent(psi)|[psi]>!psi; end if;
 return quadratic_char(e); end intrinsic;

/*
 K:=NumberField(x^3+x+1);
 QuadraticCharacter(173+K.1);
*/
