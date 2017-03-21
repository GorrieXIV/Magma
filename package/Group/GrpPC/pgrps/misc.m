freeze;

import "autos.m":  ExtendAutomorphisms, ExtendToSubgroup;
import "generate.m": InitialSegmentSubgroup;
import "aut.m": SetupMaps;

/* set up generating sets for p-central series of group having
   pc-presentation constructed by pQuotient; use this function
   (not pCentralSeries) to ensure that generators
   for subgroups in the series are the standard
   pc-generators, not different ones computed by Magma */
MypCentralSeries := function (G, p)
  if #G eq 1 then return [G]; end if;
  ranks := [0] cat pRanks (G);
  class := pClass (G); n := NPCgens (G);
  return [sub < G | [G.i: i in [ranks[c] + 1..n]]>: c in [1..class + 1]];
end function;

DefiningParameters := function (G)
   p := FactoredOrder (G)[1][1];
   return p, Ngens (G);
end function;

/* vector to integer sequence */
VectorToInt := function (v)
   r := Eltseq(v);
   ChangeUniverse(~r, Integers());
   return r;
end function;

/* has the value been constant for a certain number of steps? */
IsFixed := function (value : NmrRepeats := 5)
   if #value lt NmrRepeats then return false; end if;
   return #{value[i] : i in [#value .. #value - NmrRepeats + 1 by -1]} eq 1;
end function;

/* bubble sort sequences x and length in parallel according to
   increasing order on length */
procedure BubbleSort (~x, ~y)
   l := [1..#x];
   ParallelSort(~x, ~l);
   y := y[l];
end procedure;

/* number of k-dimensional spaces in an n-dimensional
   space defined over GF (p) */
NmrSpaces := function (p, n, k)
   if k eq 0 then return 1; end if;
   pn := p^n; pk := p^k;
   powers := [p^i : i in [0..k - 1]];
   x := &*[(pn - powers[i]): i in [1..k]];
   y := &*[(pk - powers[i]): i in [1..k]];
   return x div y;
end function;

/* order of GL (n, p) */
OrderGL := function (n, p)
   if n eq 0 then return 1; end if;
   factor := p^n;
   return &*[(factor - p^i): i in [0..n - 1]];
end function;

/* return dual space of U */
DualSpace := function (U)
   F := BaseRing (U);
   d := Degree (U);
   B := Basis (U);
   n := #B;
   K := KMatrixSpace (F, n, d);
   S := K!&cat[Eltseq (B[i]): i in [1..n]];
   return NullSpace (Transpose (S));
end function;

RandomSubspace := function (p, d, k)
   V := VectorSpace (GF (p), d);
   return sub < V | [Random (V): i in [1..k]]>;
end function;

RandomSubgroup := function (P, X, n)
   return sub < P | [Random (X): i in [1..n]]>;
end function;

SubmoduleToSubspace := function (M, S)
   d := Dimension (M);
   F := BaseRing (M);
   basis := [Eltseq (M!S.i): i in [1..Dimension (S)]];
   return sub < VectorSpace (F, d) | basis >;
end function;

/* B is a submodule of M, a G-module for section <level> of the
   lower p-central series  of G; rewrite B as a subspace of this section */
SubspaceToSubgroup := function (G, M, B, level: Subgroup := [])
   r := [0] cat pRanks (G);
   if Subgroup cmpeq [] then
      S := sub < G | [G.i : i in [r[level]+1..r[level + 1]]]>;
   else
      S := Subgroup;
   end if;
   if B cmpeq [] then return sub < S | >; end if;
   B := Basis (B);
   Z := Integers ();
   B := [ChangeUniverse (Eltseq (M!b), Z) : b in B];
   return sub <S | B>;
end function;

SubgroupToSubspace := function (G, H)
   p, d := DefiningParameters (G);
   V := VectorSpace (GF (p), d);
   S := sub < V | [Eltseq (G!H.i): i in [1..NPCgens (H)]]>;
   return S;
end function;

DescribeChar := function (G, level, T)
   p := FactoredOrder (G)[1][1];
   P := MypCentralSeries (G, p);
   S := P[level];
   VS := VectorSpace (GF (p), NPCgens (S));
   return sub < VS | [Eltseq (S! T.i) : i in [1..NPCgens (T)]]>;
end function;

/* S is a subgroup of F, a characteristic subgroup
   of the p-multiplicator; write down the basis of S wrt F */
BasisCharSubgroup := function (F, S)
   p := DefiningParameters (F);
   V := VectorSpace (GF (p), NPCgens (F));
   return sub <V | [Eltseq (F!S.i): i in [1..NPCgens (S)]]>;
end function;

/* top / bottom is section of M; write down preimage in M */
FactorToSubspace := function (M, top, bottom)
    Q, phi := quo < top | bottom >;
    F := BaseRing (M);
    d := Dimension (M);
    V := VectorSpace (F, d);
    return sub < V | [Eltseq (M! Q.i @@ phi): i in [1..Dimension (Q)]]>;
end function;

/* p-multiplicator of p-group P */
Multiplicator := function (P)
   c := pClass (P);
   return sub < P | [P.i : i in [1..NPCgens (P)] | WeightClass (P.i) eq c]>;
end function;

/* P is p-covering group of G; return nucleus of G */
Nucleus := function (P, G)
   defns := pQuotientDefinitions(P);
   N := sub < P | >;
   q := NPCgens (P);
   n := NPCgens (G);
   class := pClass (G);
   for i in [n + 1..q] do
       defn := defns[i];
       u := defn[1]; v := defn[2]; wt := 0;
       if u gt 0 and v gt 0 then
          wt := PCClass (G.u) + PCClass (G.v);
       elif u gt 0 and v eq 0 then
           wt := PCClass (G.u) + 1;
       end if;
       if wt gt class then N := sub < P | N, P.i >; end if;
   end for;
   return N;
end function;

intrinsic pCoveringGroup (H :: GrpPC : Exponent := 0) -> GrpPC, SeqEnum,
                                                 GrpPCpQuotientProc
{The p-covering group of H; if Exponent is non-zero, then
 enforce the corresponding exponent law for the p-cover of H}

   p, d := DefiningParameters (H);
   exponent := Exponent;

   PQ := pQuotientProcess (H, p, pClass (H): Print := 0);
   pCoveringGroup (~PQ);

   if Exponent ne 0 then
      ExponentLaw (~PQ : Exponent := exponent);
      EliminateRedundancy (~PQ: Update := false);
   end if;

   a, _, c := ExtractGroup (PQ);
   return a, c, PQ;

end intrinsic;

/* p-covering group of group stored in pQuotient process */
pCoverFunction := function (PQ)
   PQ1 := PQ;

   pCoveringGroup (~PQ1);
   P := ExtractGroup (PQ1);

   NextClass (~PQ);
   K, theta := ExtractGroup (PQ);

   return P, K, PQ, theta, PQ1;
end function;

intrinsic AllowableSubgroup (P:: GrpPC, G :: GrpPC) -> ModTupFld, Map, GrpPC
{construct subspace for allowable subgroup of P whose quotient is G}

   p, d := DefiningParameters (G);
   phi := hom < P -> G | [ G.i : i in [1..d]] : Check := false >;
   K := Kernel (phi);
   M := Multiplicator (P);
   V := VectorSpace (GF (p), NPCgens (M));
   return sub <V | [Eltseq (M!K.i) : i in [1..NPCgens (K)]]>, phi, K;

end intrinsic;

/*
intrinsic ExteriorSquare (G :: GrpMat) -> GrpMat, SeqEnum
{return exterior square representation of G and commutator basis for space}

   d, K := BasicParameters (G);
   p := #K;
   require IsPrime (p): "Field must be prime field";

   F := FreeGroup (d);

   H, theta, defs := pQuotient (F, p, 1: Print := 0);
   H`definitions := defs;

   P, defs := pCoveringGroup (H);
   P`definitions := defs;

   M := Multiplicator (P);
   Auts := SetupMaps (H, [G.i: i in [1..Ngens (G)]], [], 1);
   Auts`Autos := ExtendAutomorphisms (P, Auts`Autos, M);

   m := Binomial (d, 2);
   C := sub < M | [M.i : i in [1..m]]>;

   ExtendToSubgroup (P, C, ~Auts`Autos);
   A := [Auts`Autos[i]`extension : i in [1..#Auts`Autos]];

   return sub < GL (m, p) | A >, [defs[i] : i in [d + 1..d + m]];

end intrinsic;
*/

intrinsic OrbitsOfSpaces (G:: GrpMat, k:: RngIntElt) -> SeqEnum
{lengths of orbits and orbit representatives of all k-dimensional
 subspaces of natural vector space under action of matrix group G
 defined over prime field}

   requirerange k, 0, Degree (G);
   F := BaseRing (G);
   p := #F;
   error if not IsPrime (p), "G must be defined over prime field";
   d := Degree (G);
   D, Offset, degree := DefinitionSets (p, d, d, k);
   if Ngens (G) gt 0 then
      A := [Transpose(G.i) : i in [1..Ngens (G)]];
   else
       A := [Identity (G)];
   end if;
   O := ConstructOrbitsInternal (A, D, Offset);
   L := [LabelToMatrixInternal (O[i][2], D, Offset, p, d): i in [1..#O]];

   RepToSpace := function (U)
        return sub < VectorSpace (BaseRing (Parent (U)), Ncols (U)) |
                            [Eltseq (U[i]): i in [1..Nrows (U)]]>;
   end function;

   return [<O[i][1], RepToSpace (L[i])>: i in [1..#O]];

end intrinsic;
