freeze;

// Functions to compute between Hecke character groups and abelian extensions

////////////////////////////////////////////////////////////////////////

function fixedQasNF() return CyclotomicField(1); end function; // dreaded hack

function fldab_to_hecke(A) // NormGroup idea due to Claus, supposedly is fast
 K:=BaseField(A); if Type(K) eq FldRat then K:=fixedQasNF(); end if;
 assert IsAbsoluteField(K); B:=0;
 if Degree(A) eq 1 then
  G:=HeckeCharacterGroup(1*Integers(K)); return sub<G|[G.0]>; end if;
 phi:=NormGroup(A); I:=AbelianInvariants(Domain(phi)); N,oo:=Conductor(A);
 while true do B:=B+100; P:=PrimesUpTo(B,K);
  G:=HeckeCharacterGroup(1*Integers(K),oo); G:=sub<G|[G.0]>; KER:=1;
  DATA:=[* [* *] : i in [1..#I] *];
  P:=[p : p in P | AbsoluteNorm(Gcd(N,p)) eq 1];
  for p in P do E:=[x : x in Eltseq(p@@phi)];
   r:=[CyclotomicField(I[i]).1^E[i] : i in [1..#I]];
   for i in [1..#I] do DATA[i]:=DATA[i] cat [*<p,r[i]>*]; end for; end for;
  for i in [1..#I] do
   psi,k:=HeckeCharacter(N,oo,<d : d in DATA[i]> : RequireGenerators:=false);
   psi:=AssociatedPrimitiveCharacter(psi); KER:=KER*#k;
   m1:=Modulus(Parent(psi)); m2:=Modulus(G); m:=Lcm(m1,m2);
   G:=Extend(G,m,oo)+Extend(sub<Parent(psi)|[psi]>,m,oo); end for;
  if KER ne 1 then continue; end if; assert #G eq Degree(A); return G;
 end while; end function;

intrinsic HeckeCharacterGroup(A::FldAb) -> GrpHecke
{Given an abelian extension, return the corresponding Hecke character group}
 require Type(BaseField(A)) eq FldRat or IsAbsoluteField(BaseField(A)):
  "Base field must be absolute"; return fldab_to_hecke(A); end intrinsic;

intrinsic HeckeCharacterGroup(A::FldNum) -> GrpHecke
{Given an abelian number field extension (possibly relative),
 return the corresponding Hecke character group}
 require Type(BaseField(A)) eq FldRat or IsAbsoluteField(BaseField(A)):
  "Base field must be absolute";
 require IsAbelian(A): "Field must be abelian";
 return HeckeCharacterGroup(AbelianExtension(A)); end intrinsic;

function heckechar_fldab(psi) // essentially from Claus
 K:=psi`Parent`NF; o:=Order(psi); Z:=Integers(); assert IsAbsoluteField(K);
 C,oo:=Conductor(psi); ZK:=Integers(K); LIM:=0; P:=[];
 R,mR:=RayClassGroup(C,oo); Q,mQ:=quo<R|o*R>;
 while true do LIM:=LIM+100; P:=[p : p in PrimesUpTo(LIM,K : coprime_to:=C)];
  mult:=Characteristic(Parent('@'(Random(P),psi:Raw))) div o;
  h:=[<p@@mR@mQ, GG![(Z!'@'(p,psi:Raw)) div mult]> : p in P]
      where GG:=AbelianGroup([o]); F:=FreeAbelianGroup(#h);
  m1:=hom<F -> Parent(h[1][1]) | [h[i][1] : i in [1..#h]]>;
  m2:=hom<F -> Parent(h[1][2]) | [h[i][2] : i in [1..#h]]>; hh:=Inverse(m1)*m2;
  K:=Kernel(hh); q,mq:=quo<Q|K>; if #q eq o then break; end if; end while;
 return AbelianExtension(Inverse(mq)*Inverse(mQ)*mR); end function;

APC:=AssociatedPrimitiveCharacter;

function sign_character()
 return DirichletGroup(1*Integers(fixedQasNF()),[1]).1; end function;

function dirchar_fldab(chi) chi:=DirichletCharacterOverNF(chi);
 if not IsTrivialOnUnits(chi) then chi:=chi*sign_character(); end if;
 psi:=APC(HeckeLift(chi)); return heckechar_fldab(psi); end function;

intrinsic AbelianExtension(chi::GrpDrchElt) -> FldAb
{Given a Dirichlet character over Q, return the corresponding Abelian field}
 if IsTrivial(chi) then return AbelianExtension(fixedQasNF()); end if;
 A:=dirchar_fldab(APC(chi)); return A; end intrinsic;

intrinsic AbelianExtension(chi::GrpDrchNFElt) -> FldAb
{Given a Dirichlet character over Q as a number field,
 return the corresponding Abelian field}
 require IsAbsoluteField(chi`Parent`NF): "Base field must be absolute";
 require Degree(Parent(chi)`NF) eq 1: "Must be a Dirichlet character over Q";
 if IsTrivial(chi) then
  K:=ext<chi`Parent`NF|Polynomial([-1,1]) : DoLinearExtension>;
  return AbelianExtension(K); end if;
 A:=dirchar_fldab(APC(DirichletCharacterOverQ(chi)));
 return A; end intrinsic;

intrinsic AbelianExtension(psi::GrpHeckeElt) -> FldAb
{Given a Hecke character over an absolute field,
 return the corresponding Abelian extension}
 require IsAbsoluteField(psi`Parent`NF): "Base field must be absolute";
 if IsTrivial(psi) then
  K:=ext<psi`Parent`NF|Polynomial([-1,1]) : DoLinearExtension>;
  return AbelianExtension(K); end if;
 return heckechar_fldab(APC(psi)); end intrinsic;

intrinsic AbelianExtension(G::GrpHecke) -> FldAb
{Given a group of Hecke characters over an absolute field,
 return the corresponding Abelian extension}
 require IsAbsoluteField(G`NF): "Base field must be absolute";
 if #G eq 1 then K:=ext<G`NF|Polynomial([-1,1]) : DoLinearExtension>;
  return AbelianExtension(K); end if;
 AG:=AbelianGroup(AbelianInvariants(G`AbGrp)); _,m:=IsIsomorphic(AG,G`AbGrp);
 return &*[heckechar_fldab(APC(G!Eltseq(m(g)))) : g in Generators(AG)];
 end intrinsic;

