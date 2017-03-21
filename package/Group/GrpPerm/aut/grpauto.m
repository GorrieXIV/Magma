freeze;

intrinsic FPGroup(A :: GrpAuto) -> GrpFP, Map
{A finitely presented group F isomorphic to A, and isomorphism F->A}
local m, im, P, F, phi, psi;

   if assigned A`FpGroup then
     return A`FpGroup[1], A`FpGroup[2];
   end if;

   m, P, _ := ClassAction(A);
   F, phi := FPGroup(P);

   psi := hom< F->A | [ F.i @ phi @@ m : i in [1..Ngens(F)]] >;
   A`FpGroup := <F, psi>;
   return F, psi;

end intrinsic;

intrinsic OuterFPGroup(A :: GrpAuto) -> GrpFP, Map
{A finitely presented group O isomorphic to A/Inner(A), and
 natural epimorphism A`FpGroup->O
}
local G, m, P, Y, F, phi, FtoP, x;

   if  assigned A`OuterFpGroup then
     return A`OuterFpGroup[1], A`OuterFpGroup[2];
   end if;

   G := Group(A);
   F, phi := FPGroup(A);
   m, P, Y := ClassAction(A);

   // Find images in F of inner automorphisms of G via P.
   inners := [];

   FtoP := hom< F->P | [phi(F.i)@m : i in [1..Ngens(F)] ]>; 
   for g in Generators(G) do
     x := P![Position(Y,g^-1*y*g) : y in Y ];
     Append(~inners,x @@ FtoP);
   end for;
  
   Q, p := quo< F | inners >;
   A`OuterFpGroup := < Q,p >;
   return Q, p;

end intrinsic;

IsConjugateUnderSubgroup := function(S,g,h)
//THIS IS NO LONGER NEEDED SINCE IsConjugate now works for matrix groups
/* g and h should be elements of a group G and S a subgroup of G.
 * Test if g and h are conjugate under S and if so, return conjugating
 * element.
 * Note - for permutation groups we can just apply IsConjugate.
 */
  local G, H, con, x, C, M, T;
  G := Parent(g);
  H := sub<G|S,g,h>;
  con,x := IsConjugate(H,g,h);
  if not con then
    return false, _;
  end if;
  if x in S then
    return con, x;
  end if;
 
  M := S meet Centraliser(H,g);
  T := RightTransversal(S,M);
  for t in T do if g^t eq h then
    return true, t;
  end if; end for; 
  return false, _;

end function;

intrinsic IsInnerAutomorphism(a :: GrpAutoElt) -> BoolElt, GrpPermElt
{Decide whether a is inner and if so also return a corresponding
 conjugating element of A`Group
}

  local G, A, C, yes, el, g, y;
  A := Parent(a);
  if not assigned A`Group then
    error "Underlying group of automorphism group is not known";
   end if;
  G:=A`Group;
  C:=G;
  y:=Id(G);
  for g in [G.i : i in [1..Ngens(G)]] do
//IsConjugate now works properly for matrix groups
//    if Category(G) eq GrpPerm then
    yes, el := IsConjugate(C,g^y,g@a);
//    else
//      yes, el := IsConjugateUnderSubgroup(C,g^y,g@a);
//    end if;
    if not yes then
      return false, _;
    end if;
    y := y*el;
    C := Centraliser(C,g@a);
  end for;
 
  return true, y;
end intrinsic;

intrinsic IsInner(a :: GrpAutoElt) -> BoolElt, GrpPermElt
{Decide whether a is inner and if so also return a corresponding
 conjugating element of A`Group
}
  return IsInnerAutomorphism(a);
end intrinsic;

intrinsic CharacteristicSeries(A :: GrpAuto) -> SeqEnum
{The characteristic series of A`Group (from top down) used to compute A. }

  local G, L;

  if assigned A`CharacteristicSeries then
    return A`CharacteristicSeries;
  end if;

  if not assigned A`Group then
    error "Underlying group of automorphism group is not known";
  end if;

  G:=A`Group;
  L := ElementaryAbelianSeriesCanonical(G);
  if G ne L[1] then L := [G] cat L; end if;

  A`CharacteristicSeries := L;
  return L;

end intrinsic;

intrinsic PCGroup(A :: GrpAuto) -> GrpPC, Map
{A PCGroup P isomorphic to A, and isomorphism A->P}
local m, im, P, F, phi, psi;

   error if assigned A`Soluble and A`Soluble eq false, "Automorphism group is not soluble.";

   if assigned A`PCGroup then
     return A`PCGroup[1], A`PCGroup[2];
   end if;

   G := A`Group;
   if IsPrimePower(#G) and IsConditioned(G) then
     b, phi_A, R_A := PCGroupAutomorphismGroupPGroup(A);
     error if not b, "Automorphism group is not soluble.";
     return R_A, phi_A;
   end if;

   // NOTE!! If group is large and A`FpGroup is known, then we should
   // perhaps be using the soluble quotient rather than the ClassAction
   // here!!!

   m, P := ClassAction(A);
   error if not IsSoluble(P), "Automorphism group is not soluble.";
   F, phi := PCGroup(P);
   A`PCGroup := <F, m*phi>;

   return A`PCGroup[1], A`PCGroup[2];

end intrinsic;
