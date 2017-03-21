freeze;

intrinsic Holomorph(G :: GrpPerm, A :: GrpAuto) -> GrpPerm, HomGrp, HomGrp
{The holomorph of group G using group of automorphisms A}
/* Compute the holomorph of group G using group of automorphisms A.
 * Return P,map1,map2, where P is a GrpPerm isomorphic to Holomorph(G),
 * map1:G->P and map2:P->A are the associated maps.
 * Generators of G come first in P, then generators of A.
 * P has degree |G|, with G as regular normal subgroup, A as stabiliser
 * of 1.
 */
local o, Gelts, gens, P, map1, map2;

  if Group(A) cmpne G then
    error "Second argument is not a group of automorphisms of the first";
  end if;
  o := #G;
  Gelts := [ g : g in G ];
  gens := [];
  //first generators for right regular action of G in Gelts
  for i in [1..Ngens(G)] do
    Append(~gens, [ Position(Gelts, Gelts[k]*G.i) : k in [1..o] ] );
  end for;
  //now generators for action of A
  for i in [1..Ngens(A)] do
    Append(~gens, [ Position(Gelts, Gelts[k]@A.i) : k in [1..o] ] );
  end for;
  P := sub < Sym(o) | gens >;
  map1 := hom< G->P | [P.i : i in [1..Ngens(G)]] >;
  map2 := hom< P->A |
          [Id(A) : i in [1..Ngens(G)]] cat [A.i : i in [1..Ngens(A)]] >;
  return P,map1,map2;
end intrinsic;

intrinsic Holomorph(G :: GrpMat, A :: GrpAuto) -> GrpPerm, HomGrp, HomGrp
{The holomorph of group G using group of automorphisms A}
/* Compute the holomorph of group G using group of automorphisms A.
 * Return P,map1,map2, where P is a GrpPerm isomorphic to Holomorph(G),
 * map1:G->P and map2:P->A are the associated maps.
 * Generators of G come first in P, then generators of A.
 * P has degree |G|, with G as regular normal subgroup, A as stabiliser
 * of 1.
 */
local o, Gelts, gens, P, map1, map2;

  if Group(A) cmpne G then
    error "Second argument is not a group of automorphisms of the first";
  end if;
  o := #G;
  Gelts := [ g : g in G ];
  gens := [];
  //first generators for right regular action of G in Gelts
  for i in [1..Ngens(G)] do
    Append(~gens, [ Position(Gelts, Gelts[k]*G.i) : k in [1..o] ] );
  end for;
  //now generators for action of A
  for i in [1..Ngens(A)] do
    Append(~gens, [ Position(Gelts, Gelts[k]@A.i) : k in [1..o] ] );
  end for;
  P := sub < Sym(o) | gens >;
  map1 := hom< G->P | [P.i : i in [1..Ngens(G)]] >;
  map2 := hom< P->A |
          [Id(A) : i in [1..Ngens(G)]] cat [A.i : i in [1..Ngens(A)]] >;
  return P,map1,map2;
end intrinsic;

intrinsic Holomorph(G :: GrpPC, A :: GrpAuto) -> GrpPerm, HomGrp, HomGrp
{The holomorph of group G using group of automorphisms A}
/* Compute the holomorph of group G using group of automorphisms A.
 * Return P,map1,map2, where P is a GrpPerm isomorphic to Holomorph(G),
 * map1:G->P and map2:P->A are the associated maps.
 * Generators of G come first in P, then generators of A.
 * P has degree |G|, with G as regular normal subgroup, A as stabiliser
 * of 1.
 */
local o, Gelts, gens, P, map1, map2;

  if Group(A) cmpne G then
    error "Second argument is not a group of automorphisms of the first";
  end if;
  o := #G;
  Gelts := [ g : g in G ];
  gens := [];
  //first generators for right regular action of G in Gelts
  for i in [1..NPCgens(G)] do
    Append(~gens, [ Position(Gelts, Gelts[k]*G.i) : k in [1..o] ] );
  end for;
  //now generators for action of A
  for i in [1..Ngens(A)] do
    Append(~gens, [ Position(Gelts, Gelts[k]@A.i) : k in [1..o] ] );
  end for;
  P := sub < Sym(o) | gens >;
  map1 := hom< G->P | [gens[i] : i in [1..NPCgens(G)]] >;
  map2 := hom< P->A |
          [Id(A) : i in [1..NPCgens(G)]] cat [A.i : i in [1..Ngens(A)]] >;
  return P,map1,map2;
end intrinsic;

intrinsic Holomorph(`GrpFP, G :: Grp, A :: GrpAuto) -> GrpFP, HomGrp, HomGrp
{The holomorph of group G using group of automorphisms A}
/* Compute the holomorph of group using group of automorphisms A.
 * Return H,map1,map2, where H is an GrpFP isomorphic to Holomorph(G),
 * map1:G->H and map2:H->A are the associated maps.
 * Generators of G come first in H, then generators of A.
 */
local FG, FGtoG, FA, ngg, nga, H, FGtoH, FAtoH, map1, map2;

  if Group(A) cmpne G then
    error "Second argument is not a group of automorphisms of the first";
  end if;
  FG, FGtoG := FPGroup(G);
  FA := FPGroup(A); 
  ngg:=Ngens(FG);
  nga:=Ngens(FA);
  H:=FreeGroup(ngg+nga);
  FGtoH:=hom<FG->H | [H.i : i in [1..ngg] ]>;
  FAtoH:=hom<FA->H | [H.(ngg+i) : i in [1..nga] ]>;
  Hrels :=
       [r @ FGtoH : r in Relations(FG)] cat [r @ FAtoH : r in Relations(FA)];
  /* We also want relations for action of FA on FG */
  for i in [1..ngg] do for j in [1..nga] do
    Append(~Hrels, H.i^H.(j+ngg) = (G.i @ A.j) @@ FGtoG @ FGtoH);
  end for; end for;
  H := quo<H|Hrels>;
  map1 := hom< G->H | [H.i : i in [1..Ngens(FG)]] >;
  map2 := hom< H->A |
          [Id(A) : i in [1..Ngens(FG)]] cat [A.i : i in [1..Ngens(A)]] >;
  return H,map1,map2;
end intrinsic;

intrinsic Holomorph(G :: GrpPerm :Print:=0,SmallModAut:=1000,
         SmallOuterAutGroup:=20000, SmallSubOutGp:=100000,
         VerySmallModAut:=1, PrintSearchCount:=1000, 
         SmallSimpleFactor:=5000) -> GrpPerm, HomGrp, HomGrp
{The holomorph of group G}
/* Compute the holomorph of group G.
 * Return P,map1,map2, where P is a GrpPerm isomorphic to Holomorph(G),
 * map1:G->P and map2:P->A = Automorphism(G) are the associated maps.
 * Generators of G come first in P, then generators of Aut(G).
 * P has degree |G|, with G as regular normal subgroup, A as stabiliser
 * of 1.
 */
local A, o, Gelts, gens, P, map1, map2;

  A := AutomorphismGroup(G:Print:=Print,SmallModAut:=SmallModAut,
         SmallOuterAutGroup:=SmallOuterAutGroup,
         SmallSubOutGp:=SmallSubOutGp,
         VerySmallModAut:=VerySmallModAut,
         PrintSearchCount:=PrintSearchCount, 
         SmallSimpleFactor:=SmallSimpleFactor);
  o := #G;
  Gelts := [ g : g in G ];
  gens := [];
  //first generators for right regular action of G in Gelts
  for i in [1..Ngens(G)] do
    Append(~gens, [ Position(Gelts, Gelts[k]*G.i) : k in [1..o] ] );
  end for;
  //now generators for action of A
  for i in [1..Ngens(A)] do
    Append(~gens, [ Position(Gelts, Gelts[k]@A.i) : k in [1..o] ] );
  end for;
  P := sub < Sym(o) | gens >;
  map1 := hom< G->P | [P.i : i in [1..Ngens(G)]] >;
  map2 := hom< P->A |
          [Id(A) : i in [1..Ngens(G)]] cat [A.i : i in [1..Ngens(A)]] >;
  return P,map1,map2;
end intrinsic;

intrinsic Holomorph(G :: GrpMat :Print:=0,SmallModAut:=1000,
         SmallOuterAutGroup:=20000, SmallSubOutGp:=100000,
         VerySmallModAut:=1, PrintSearchCount:=1000, 
         SmallSimpleFactor:=5000) -> GrpPerm, HomGrp, HomGrp
{The holomorph of group G}
/* Compute the holomorph of group G.
 * Return P,map1,map2, where P is a GrpPerm isomorphic to Holomorph(G),
 * map1:G->P and map2:P->A = Automorphism(G) are the associated maps.
 * Generators of G come first in P, then generators of Aut(G).
 * P has degree |G|, with G as regular normal subgroup, A as stabiliser
 * of 1.
 */
local A, o, Gelts, gens, P, map1, map2;

  A := AutomorphismGroup(G:Print:=Print,SmallModAut:=SmallModAut,
         SmallOuterAutGroup:=SmallOuterAutGroup,
         SmallSubOutGp:=SmallSubOutGp,
         VerySmallModAut:=VerySmallModAut,
         PrintSearchCount:=PrintSearchCount, 
         SmallSimpleFactor:=SmallSimpleFactor);
  o := #G;
  Gelts := [ g : g in G ];
  gens := [];
  //first generators for right regular action of G in Gelts
  for i in [1..Ngens(G)] do
    Append(~gens, [ Position(Gelts, Gelts[k]*G.i) : k in [1..o] ] );
  end for;
  //now generators for action of A
  for i in [1..Ngens(A)] do
    Append(~gens, [ Position(Gelts, Gelts[k]@A.i) : k in [1..o] ] );
  end for;
  P := sub < Sym(o) | gens >;
  map1 := hom< G->P | [P.i : i in [1..Ngens(G)]] >;
  map2 := hom< P->A |
          [Id(A) : i in [1..Ngens(G)]] cat [A.i : i in [1..Ngens(A)]] >;
  return P,map1,map2;
end intrinsic;

intrinsic Holomorph(G :: GrpPC) -> GrpPerm, HomGrp, HomGrp
{The holomorph of group G}
/* Compute the holomorph of group G.
 * Return P,map1,map2, where P is a GrpPerm isomorphic to Holomorph(G),
 * map1:G->P and map2:P->A = Automorphism(G) are the associated maps.
 * Generators of G come first in P, then generators of Aut(G).
 * P has degree |G|, with G as regular normal subgroup, A as stabiliser
 * of 1.
 */
local A, o, Gelts, gens, P, map1, map2;

  A := AutomorphismGroup(G);
  o := #G;
  Gelts := [ g : g in G ];
  gens := [];
  //first generators for right regular action of G in Gelts
  for i in [1..NPCgens(G)] do
    Append(~gens, [ Position(Gelts, Gelts[k]*G.i) : k in [1..o] ] );
  end for;
  //now generators for action of A
  for i in [1..Ngens(A)] do
    Append(~gens, [ Position(Gelts, Gelts[k]@A.i) : k in [1..o] ] );
  end for;
  P := sub < Sym(o) | gens >;
  map1 := hom< G->P | [gens[i] : i in [1..NPCgens(G)]] >;
  map2 := hom< P->A |
          [Id(A) : i in [1..NPCgens(G)]] cat [A.i : i in [1..Ngens(A)]] >;
  return P,map1,map2;
end intrinsic;

intrinsic Holomorph(`GrpFP, G :: GrpPerm :Print:=0,SmallModAut:=1000,
         SmallOuterAutGroup:=20000, SmallSubOutGp:=100000,
         VerySmallModAut:=1, PrintSearchCount:=1000, 
         SmallSimpleFactor:=5000) -> GrpFP, HomGrp, HomGrp
{The holomorph of group G}
/* Compute the holomorph of group G as an FPGroup on |G| points.
 * Return H,map1,map2, where H is an GrpFP isomorphic to Holomorph(G),
 * map1:G->H and map2:H->A = Automorphism(G) are the associated maps.
 * Generators of G come first in H, then generators of Aut(G).
 */
local A, FG, FGtoG, FA, ngg, nga, H, FGtoH, FAtoH, map1, map2;

  A := AutomorphismGroup(G:Print:=Print,SmallModAut:=SmallModAut,
         SmallOuterAutGroup:=SmallOuterAutGroup,
         SmallSubOutGp:=SmallSubOutGp,
         VerySmallModAut:=VerySmallModAut,
         PrintSearchCount:=PrintSearchCount, 
         SmallSimpleFactor:=SmallSimpleFactor);
  FG, FGtoG := FPGroup(G);
  FA := FPGroup(A); 
  ngg:=Ngens(FG);
  nga:=Ngens(FA);
  H:=FreeGroup(ngg+nga);
  FGtoH:=hom<FG->H | [H.i : i in [1..ngg] ]>;
  FAtoH:=hom<FA->H | [H.(ngg+i) : i in [1..nga] ]>;
  Hrels :=
       [r @ FGtoH : r in Relations(FG)] cat [r @ FAtoH : r in Relations(FA)];
  /* We also want relations for action of FA on FG */
  for i in [1..ngg] do for j in [1..nga] do
    Append(~Hrels, H.i^H.(j+ngg) = (G.i @ A.j) @@ FGtoG @ FGtoH);
  end for; end for;
  H := quo<H|Hrels>;
  map1 := hom< G->H | [H.i : i in [1..Ngens(G)]] >;
  map2 := hom< H->A |
          [Id(A) : i in [1..Ngens(G)]] cat [A.i : i in [1..Ngens(A)]] >;
  return H,map1,map2;
end intrinsic;

intrinsic Holomorph(`GrpFP, G :: GrpMat :Print:=0,SmallModAut:=1000,
         SmallOuterAutGroup:=20000, SmallSubOutGp:=100000,
         VerySmallModAut:=1, PrintSearchCount:=1000, 
         SmallSimpleFactor:=5000) -> GrpFP, HomGrp, HomGrp
{The holomorph of group G}
/* Compute the holomorph of group G as an FPGroup on |G| points.
 * Return H,map1,map2, where H is an GrpFP isomorphic to Holomorph(G),
 * map1:G->H and map2:H->A = Automorphism(G) are the associated maps.
 * Generators of G come first in H, then generators of Aut(G).
 */
local A, FG, FGtoG, FA, ngg, nga, H, FGtoH, FAtoH, map1, map2;

  A := AutomorphismGroup(G:Print:=Print,SmallModAut:=SmallModAut,
         SmallOuterAutGroup:=SmallOuterAutGroup,
         SmallSubOutGp:=SmallSubOutGp,
         VerySmallModAut:=VerySmallModAut,
         PrintSearchCount:=PrintSearchCount, 
         SmallSimpleFactor:=SmallSimpleFactor);
  FG, FGtoG := FPGroup(G);
  FA := FPGroup(A); 
  ngg:=Ngens(FG);
  nga:=Ngens(FA);
  H:=FreeGroup(ngg+nga);
  FGtoH:=hom<FG->H | [H.i : i in [1..ngg] ]>;
  FAtoH:=hom<FA->H | [H.(ngg+i) : i in [1..nga] ]>;
  Hrels :=
       [r @ FGtoH : r in Relations(FG)] cat [r @ FAtoH : r in Relations(FA)];
  /* We also want relations for action of FA on FG */
  for i in [1..ngg] do for j in [1..nga] do
    Append(~Hrels, H.i^H.(j+ngg) = (G.i @ A.j) @@ FGtoG @ FGtoH);
  end for; end for;
  H := quo<H|Hrels>;
  map1 := hom< G->H | [H.i : i in [1..Ngens(G)]] >;
  map2 := hom< H->A |
          [Id(A) : i in [1..Ngens(G)]] cat [A.i : i in [1..Ngens(A)]] >;
  return H,map1,map2;
end intrinsic;

intrinsic Holomorph(`GrpFP, G :: GrpPC) -> GrpFP, HomGrp, HomGrp
{The holomorph of group G}
/* Compute the holomorph of group G as an FPGroup on |G| points.
 * Return H,map1,map2, where H is an GrpFP isomorphic to Holomorph(G),
 * map1:G->H and map2:H->A = Automorphism(G) are the associated maps.
 * Generators of G come first in H, then generators of Aut(G).
 */
local A, FG, FGtoG, FA, ngg, nga, H, FGtoH, FAtoH, map1, map2;

  A := AutomorphismGroup(G);
  FG, FGtoG := FPGroup(G);
  FA := FPGroup(A); 
  ngg:=Ngens(FG);
  nga:=Ngens(FA);
  H:=FreeGroup(ngg+nga);
  FGtoH:=hom<FG->H | [H.i : i in [1..ngg] ]>;
  FAtoH:=hom<FA->H | [H.(ngg+i) : i in [1..nga] ]>;
  Hrels :=
       [r @ FGtoH : r in Relations(FG)] cat [r @ FAtoH : r in Relations(FA)];
  /* We also want relations for action of FA on FG */
  for i in [1..ngg] do for j in [1..nga] do
    Append(~Hrels, H.i^H.(j+ngg) = (G.i @ A.j) @@ FGtoG @ FGtoH);
  end for; end for;
  H := quo<H|Hrels>;
  map1 := hom< G->H | [H.i : i in [1..Ngens(FG)]] >;
  map2 := hom< H->A |
          [Id(A) : i in [1..Ngens(FG)]] cat [A.i : i in [1..Ngens(A)]] >;
  return H,map1,map2;
end intrinsic;
