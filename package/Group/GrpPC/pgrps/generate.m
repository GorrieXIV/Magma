freeze;

import "misc.m": DefiningParameters, OrderGL,
                 Multiplicator, Nucleus;
import "autos.m": ExtendAutomorphisms, ExtendToSubgroup;
import "cf.m": OrbitStabiliser, SchreierVectorToMap;
import "centrals.m": CentralAutomorphisms;
import "parameters.m": AutRF;
import "aut.m": RestrictStabiliser, SetupMaps;
import "char-spaces.m": CharSpaces;

declare verbose GeneratepGroups, 2;

ConstructOrbit := ConstructOneOrbitInternal;

/* nuclear rank of K */
MyNuclearRank := function (K : Exponent := 0)
   if Exponent gt 0 then
      pCover := pCoveringGroup (K : Exponent := Exponent);
      return NPCgens (Nucleus (pCover, K));
   else
      return NuclearRank (K);
   end if;
end function;

intrinsic DefinitionSets (p:: RngIntElt, m:: RngIntElt, n::RngIntElt,
                   s:: RngIntElt: Fixed := 0) -> SeqEnum, SeqEnum, RngIntElt
{return s-step definition sets and offsets of dimension n in vector space
 of dimension m, where we must retain the first Fixed basis elements}

   S := {i : i in [1..n]};
   Fixed := {1..Fixed};
   S diff:= Fixed;
   D := Subsets (S, s - #Fixed);
   D := {Fixed join d : d in D};
   DefSets := [ Sort (SetToSequence (x)) : x in D ];
   Sort (~DefSets);
   DefSets := {@ {@ i : i in d @} : d in DefSets @};

   degree := 0; Offset := [];
   for d in DefSets do
      available := 0;
      for i in [1..s] do
         available +:= #[x : x in [d[i]+1..m] | x notin d];
      end for;
      // printf "defset = %o no of available is %o\n", d, available;
      degree +:= p^available;
      Append (~Offset, degree);
   end for;

   vprint GeneratepGroups, 2: "Number of subspaces is ", degree;
   return DefSets, Offset, degree;

end intrinsic;

function TraceWord (pos, Schreier, Backptr)
   word := [];
   while Schreier[pos] ne 0 do
      Append (~word, Schreier[pos]);
      pos := Backptr[pos];
   end while;
   return word;
end function;

MatrixColumn := function (A, i)
   return [A[j][i] :  j in [1..Nrows (A)]];
end function;

LabelToSubgroup := function (P, M, label, DefSets, Offset:
                             MatrixOnly := false)
   p := DefiningParameters (M);
   q := NPCGenerators (M);
   S, DS := LabelToMatrixInternal (label, DefSets, Offset, p, q);
   if MatrixOnly then return S, _; end if;

   // n := NPCGenerators (H);
   n := pRanks (P)[pClass (P) - 1];
   Sub := []; Sub1 := [];
   Z := Integers ();
   for i in [1..q] do
      if i in DS then continue; end if;
      col := MatrixColumn (S, i);
      if #col gt 0 then
         w := &*[M.DS[j]^(Z!-col[j]) : j in [1..#col]] * M.i;
         e := Eltseq (P!w);
         w1 := [<i, e[i]>: i in [1..#e] | e[i] gt 0];
         // w1 := [<n + DS[j],(Z!-col[j])> : j in [1..#col]] cat [<n + i, 1>];
      else
         w := M.i; w1 := [<n + i, 1>];
      end if;
      Append (~Sub, w);
      Append (~Sub1, w1);
   end for;

   return S, Sub, Sub1;
end function;

/* factor group defined by Auts`PQ by U */
FactorSubgroup := function (Auts, U)
   PQ := Auts`PQ;

   if #U ne 0 then
      for u in U do
         _ := Collect (PQ, u); EcheloniseWord (~PQ);
      end for;
      EliminateRedundancy (~PQ: Update := false);
   end if;
   K := ExtractGroup (PQ);

   return PQ, K;
end function;

ProcessSubgroup := function (P, Chars, C, Auts, M, N, s, complete:
                             MaxAuts := false, Exponent := 0, All := false)
   H := Auts`K;
   p, d := DefiningParameters (H);

   ExtendToSubgroup (P, C, ~Auts`Autos);
   ExtendToSubgroup (P, C, ~Auts`pAutos);
   A := [Auts`Autos[i]`extension : i in [1..#Auts`Autos]];
   A cat:= [Auts`pAutos[i]`extension : i in [1..#Auts`pAutos]];
   A := [MatrixAlgebra (GF (p), Nrows (A[1])) ! a : a in A];
   /* stabiliser may be trivial */
   if #A eq 0 then
      A := [Identity (MatrixAlgebra (GF (p), NPCgens (C)))];
   end if;

   q := NPCgens (M); r := NPCgens (N);

   name := Auts`Identifier;

   DefSets, Offset, degree := DefinitionSets (p, q, r, s: Fixed := P`fixed);
   O := ConstructOrbitsInternal (A, DefSets, Offset);
   vprint GeneratepGroups, 2: "Number of orbits is ", #O;

   RCG := [];
   for i in [1..#O] do

      // revision for Charles Sims Jan 22, 2013
      if MaxAuts eq true and O[i][1] gt 1 then continue; end if;

      label := (O[i][2]);
      vprint GeneratepGroups, 2: "Length of orbit is ", O[i][1];
      vprint GeneratepGroups, 2: "Process label ", label;

      _, Usub, U := LabelToSubgroup (P, M, label, DefSets, Offset);
      // vprint GeneratepGroups, 2: "U is ", U;
      // vprint GeneratepGroups, 2: "Usub is ", Usub;

      PQ, K := FactorSubgroup (Auts, U);

      terminal := MyNuclearRank (K : Exponent := Exponent) eq 0;

      if complete and All eq false and terminal then
         continue;
      end if;

      S, phi, U := AllowableSubgroup (P, K);

      if complete and All eq true and terminal then
         Stab := rec <AutRF | Autos:= [], pAutos := []>;
      elif O[i][1] gt 1 then
         Stab := OrbitStabiliser (P, M, U, H, H, Auts, Chars : Isom := true);
      else
         Stab := rec <AutRF | Autos:= Auts`Autos, pAutos := Auts`pAutos>;
      end if;

      A := RestrictStabiliser (P, phi, K, Stab`Autos);
      B := RestrictStabiliser (P, phi, K, Stab`pAutos);
      K`fixed := s;
      K`stepSize := P`stepSize;
      A := rec <AutRF | P := K, K := H, Autos := A, pAutos := B,
                        Identifier := name, PQ := PQ,
                        Order := Auts`Order div O[i][1]>;
      Append (~RCG, A);
   end for;

   if complete then Total := #O; else Total := 0; end if;
   return RCG, Total;
end function;

StepRange := function (P, sub, k)
   C := sub;
   q := NPCGenerators (C);

   r := Minimum (q, P`nuclearRank);
   if q lt P`nuclearRank then
      lower := Maximum (P`fixed, P`stepSize + q - P`nuclearRank);
   else
      lower := P`stepSize;
   end if;

   upper := Minimum (P`stepSize, q);

   return lower, upper, C;
end function;

/* write down subspaces corresponding to submodule lattice elements */
LatticeToSubspaces := function (G, L)
   d := Degree (G);
   F := BaseRing (G);
   V := VectorSpace (F, d);
   S := []; dim := [];
   for i in [1..#L] do
      B := Morphism (L!i);
      Base := [V!B[i]: i in [1..Dimension(Domain(B))]];
      S[i] := sub <V | Base>;
      dim[i] := Dimension (S[i]);
   end for;
   return dim, S;
end function;

/* construct the submodule lattice for module describing
   action of automorphism on p-multiplicator; choose smallest
   characteristic subspace which contains fixed */
CharSubspace := function (G, P, fixed, Auts)
   p, d := DefiningParameters (G);
   S := Multiplicator (P);
   E1 := ExtendAutomorphisms (P, Auts`Autos, S);
   E2 := ExtendAutomorphisms (P, Auts`pAutos, S);
   E := [E1[i]`extension: i in [1..#E1]] cat [E2[i]`extension: i in [1..#E2]];
   m := NPCgens (S);
   A := sub <GL(m, p) | E>;
   M := GModule (A);

   /* limit number of submodules constructed */
   L := SubmoduleLattice (M: Limit := 1000);

   F := GF (p);
   V := VectorSpace (F, m);
   Fixed := sub <V | [V.i: i in [1..fixed]]>;
   dims, spaces := LatticeToSubspaces (A, L);
   index := [j : j in [1..#dims] | Fixed subset spaces[j]
                                   and dims[j] gt Dimension (Fixed)];
   min, pos := Minimum ([dims[j] : j in index]);
   Space := spaces[index[pos]];
   return sub <S | [s : s in Basis (Space)]>;
end function;

/* k-initial segment subgroup of M; if Lattice is true,
   then use SubmoduleLattice machinery to obtain useful
   characteristic subspace of M under action of Auts;
   this costs additional time, hence it's not the default */
InitialSegmentSubgroup := function (H, P, M, Auts, k, s: Lattice := false)

   if Lattice and k ge s then
      Space := CharSubspace (H, P, P`fixed, Auts);
      return Space;
   end if;

   Autos := [alpha`map : alpha in Auts`Autos];
   Autos cat:= [alpha`map : alpha in Auts`pAutos];

   q := NPCGenerators (M);

   max := Maximum (k, q);
   for index in [k + 1..max] do
      S := sub <M | [M.i : i in [1..index]]>;
      if forall {alpha : alpha in Autos | alpha (S) eq S} then
         return S;
      end if;
   end for;

   return M;

end function;

/* P is p-covering group of H; Auts describe automorphisms of H */
CharSubgroup := function (P, H, Chars, Auts, s : CharRank := 0,
                     MaxAuts := false, Id := 0, All := false, Exponent := 0)
   M := Multiplicator (P);
   p, d := DefiningParameters (M);
   N := Nucleus (P, H);
   assert N subset M;
   P`nuclearRank := NPCGenerators (N);
   P`multiplicatorRank := NPCGenerators (M);

   Auts`Autos := ExtendAutomorphisms (P, Auts`Autos, M);
   Auts`pAutos := ExtendAutomorphisms (P, Auts`pAutos, M);
   if not assigned Auts`Identifier then Auts`Identifier := "G"; end if;
   name := Auts`Identifier;

   vprintf GeneratepGroups, 2:
         "M has rank %o, N has rank %o\n", NPCgens (M), NPCgens (N);

   /* compute a chain through N */
   k := P`fixed;
k := Maximum (CharRank, P`fixed);
// "CHARRANK is ", CharRank;
   sub := InitialSegmentSubgroup (H, P, M, Auts, k, s);

   lower, upper, C := StepRange (P, sub, k + 1);

   vprint GeneratepGroups, 2: "Initial segment subgroup has rank ", NPCgens (C);

   RN := C meet N;
   RM := C meet M;

   complete := C eq M;

   Total := 0;
   RCG := [];
   for s1 in [Maximum (lower, 0)..upper] do
      L, total := ProcessSubgroup (P, Chars, C, Auts, RM, RN, s1, complete :
                     MaxAuts := MaxAuts, Exponent := Exponent, All := All);
      for i in [1..#L] do
         L[i]`complete := complete;
         if complete then
            CA := CentralAutomorphisms (L[i]`P, L[i]`pAutos);
            L[i]`pAutos cat:= CA;
            L[i]`Order *:= p^#CA;
            L[i]`K := L[i]`P;
            L[i]`Capable := MyNuclearRank (L[i]`K : Exponent := Exponent) gt 0;
            L[i]`Identifier := name cat "-#" cat
              IntegerToString (s) cat ";" cat IntegerToString (Id + #RCG + i);
            delete L[i]`P;
            if assigned L[i]`PQ then delete L[i]`PQ; end if;
         end if;
      end for;
      Total +:= total;
      RCG cat:= L;
   end for;

   return RCG, Total;
end function;

/* process step size s */
OneStepSize := function (P, Chars, Auts, s: CharRank := 0, MaxAuts := false,
   All := false, Exponent := 0, Fixed := 0)

   H := Auts`K;

   if #Nucleus (P, H) eq 1 then return [], 0; end if;

   /* at entry no fixed generators */
   P`fixed := Fixed;
   P`stepSize := s;

   List, Total := CharSubgroup (P, H, Chars, Auts, s: CharRank := CharRank,
                     MaxAuts := MaxAuts, All := All, Exponent := Exponent);
   if #List eq 0 then return List, Total; end if;

   i := 0;
   repeat
      i +:= 1;
      Auts := List[i];
      if Auts`complete eq false then
         P := Auts`P; H := Auts`K;
         L, total := CharSubgroup (P, H, Chars, Auts, s: Id := Total,
                      CharRank := CharRank, MaxAuts := MaxAuts,
                      Exponent := Exponent, All := All);
         List cat:= L;
         Total +:= total;
      end if;
   until i ge #List;

   return [x : x in List | x`complete eq true], Total;
end function;

NextStep := function (Auts, s: All := false)
   K := Auts`K;
   p, d := DefiningParameters (K);
   H := K;
   P, _, PQ := pCoveringGroup (H);

   M := Multiplicator (P);
   N := Nucleus (P, H);
   Auts`Autos := ExtendAutomorphisms (P, Auts`Autos, M);
   Auts`pAutos := ExtendAutomorphisms (P, Auts`pAutos, M);

   A := [Auts`Autos[i]`extension : i in [1..#Auts`Autos]];
   A cat:= [Auts`pAutos[i]`extension : i in [1..#Auts`pAutos]];
   A := [MatrixAlgebra (GF (p), Nrows (A[1])) ! a : a in A];

   q := NPCgens (M); r := NPCgens (N);
   if assigned P`fixed eq false then P`fixed := 0; end if;
   DefSets, Offset, degree := DefinitionSets (p, q, r, s: Fixed := P`fixed);
   vprint GeneratepGroups, 2: "Degree of perm group is ", degree;
   PermGp := ConstructPermsInternal (A, DefSets, Offset);

   Descendant := [];
   O := Orbits (PermGp);
   vprint GeneratepGroups, 2: "Number of orbits is ", #O;

   for i in [1..#O] do
      label := Minimum (O[i]);
      // "process label ", label;
      _, U := LabelToSubgroup (P, M, label, DefSets, Offset);
      K := quo < P | U >;
      K := pQuotient (K, p, pClass (K): Print := 0);

      capable :=  NuclearRank (K) eq 0 select false else true;
      if All eq false and capable eq false then continue; end if;

      S, phi, U := AllowableSubgroup (P, K);
      Chars := CharSpaces (H);
      Stab := OrbitStabiliser (P, M, U, H, H, Auts, Chars : Isom := true);
      A := RestrictStabiliser (P, phi, K, Stab`Autos);
      B := RestrictStabiliser (P, phi, K, Stab`pAutos);

      D := CentralAutomorphisms (K, B);
      Append (~Descendant,
               rec <AutRF | K := K, Autos := A, pAutos := B cat D,
                            Capable := capable, Order := Stab`Order * p^#D>);
   end for;

   return Descendant;
end function;

OneClass := function (Auts: StepSizes := [], OrderBound := 0, All := false,
                      MaxAuts := false, CharRank := 0, Exponent := 0)
   K := Auts`K;
   n := NPCGenerators (K);

   P, _, PQ := pCoveringGroup (K : Exponent := Exponent);
   Auts`PQ := PQ;

   p := DefiningParameters (K);
   class := pClass (K);
   N := Nucleus (P, K);
   r := NPCgens (N);

   if #StepSizes eq 0 then
      StepSizes := [1..r];
   else
      StepSizes := [x : x in StepSizes | x ge 1 and x le r];
   end if;
   if #StepSizes eq 0 then return [], 0; end if;

   if OrderBound gt 0 then
      if n ge OrderBound then return [], 0; end if;
      OrderBound := OrderBound - n;
      StepSizes := [x : x in StepSizes | x ge 1 and x le
                    Minimum (OrderBound, Maximum (StepSizes))];
      if #StepSizes eq 0 then return [], 0; end if;
   end if;

   vprint GeneratepGroups, 2: "Valid step sizes are ", StepSizes;

   Total := 0;
   List := [];

   Chars := CharSpaces (K);

   for s in StepSizes do
      L, total := OneStepSize (P, Chars, Auts, s : CharRank := CharRank,
                     MaxAuts := MaxAuts, All := All, Exponent := Exponent);
      if #L ne 0 then
         vprintf GeneratepGroups:
         "# of immediate descendants of %o of order %o^%o is %o / %o\n",
         Auts`Identifier, p, n + s, total, #[x : x in L | x`Capable eq true];
         List cat:= L;
      else
         vprintf GeneratepGroups:
         "# of immediate descendants of %o of order %o^%o is %o / %o\n",
         Auts`Identifier, p, n + s, total, 0;
      end if;
      Total +:= total;
   end for;

   return List, Total;
end function;

MyDescendants := function (Auts: ClassBound := 0, OrderBound := 0,
   MaxAuts := false, CharRank := 0, Exponent := 0, StepSizes := [], All := false)

   K := Auts`K; c := pClass (K) + 1;

   p := DefiningParameters (K);
   assert Exponent mod p eq 0;

   if not assigned Auts`Identifier then
      Auts`Identifier := IntegerToString (p) cat "^" cat
                         IntegerToString (NPCgens (K));
   end if;

   if ClassBound ne 0 and ClassBound lt c then
      return [], 0;
   else
      c := ClassBound;
   end if;

   List, Total := OneClass (Auts: OrderBound := OrderBound,CharRank := CharRank,
      MaxAuts := MaxAuts, Exponent := Exponent, StepSizes := StepSizes, All := All);
/*
   vprintf GeneratepGroups:
         "# of immediate descendants of %o is %o / %o\n\n",
   Auts`Identifier, Total, #[x : x in List | x`Capable eq true];
*/

   index := 1;
   while index le #List do
      Auts := List[index]; K := Auts`K;
      if pClass (K) lt c then
         if Auts`Capable eq true then
            L, total := OneClass (List[index]: OrderBound := OrderBound,
            CharRank := CharRank, MaxAuts := MaxAuts,
            Exponent := Exponent, StepSizes := StepSizes, All := All);
/*
            vprintf GeneratepGroups:
            "# of immediate descendants of %o is %o / %o\n\n",
            Auts`Identifier, Total, #[x : x in L | x`Capable eq true];
*/
            List cat:= L;
            Total +:= total;
         end if;
      else
         return List, Total;
      end if;
      index +:= 1;
   end while;

   return List, Total;
end function;

intrinsic Descendants (G:: GrpPC, ClassBound :: RngIntElt : OrderBound := 0,
    MaxAuts := false, CharRank := 0, Exponent := 0, StepSizes := [],
    All := true) -> SeqEnum, RngIntElt
{Construct descendants of p-group having p-class at most ClassBound,
 and order at most p^OrderBound; if Exponent is non-zero, generate
 descendants of G satisfying this exponent law; if StepSizes is supplied,
 then construct descendants of order p^(n + s) of a group of order p^n,
 only for s in StepSizes; by default, all descendants of G are returned;
 if MaxAuts is true, then construct maximally automorphic descendants;
 if All = false, only capable ones are returned; also return total
 number of descendants}

   require IsPrimePower (#G): "Argument must have prime-power order";
   requirege OrderBound, 0;
   requirege ClassBound, pClass (G) + 1;
   require forall {s : s in StepSizes | s gt 0}:
           "StepSizes must be positive";

   G := ConditionedGroup(G);
   if NuclearRank (G) eq 0 then return [], 0; end if;

   p := FactoredOrder (G)[1][1];
   require Exponent mod p eq 0: "Exponent must be divisible by ", p;

   if not assigned G`Automorphisms then
      A := AutomorphismGroupPGroup (G);
   end if;

   Auts := G`Automorphisms;

   StepSizes := SetToSequence (Set (StepSizes));
   L, Total := MyDescendants (Auts: CharRank := CharRank, MaxAuts := MaxAuts,
                    ClassBound := ClassBound, OrderBound := OrderBound,
                    Exponent := Exponent, StepSizes := StepSizes, All := All);
   M := [L[i]`K: i in [1..#L]];
   for i in [1..#L] do
      if MyNuclearRank (M[i]: Exponent := Exponent) gt 0 then
         M[i]`Automorphisms := L[i];
      end if;
   end for;

   return M, Total;

end intrinsic;

intrinsic Descendants (G:: GrpPC : OrderBound := 0, Exponent := 0,
          CharRank := 0, MaxAuts := false,
          StepSizes := [], All := true) -> SeqEnum, RngIntElt
{Construct descendants of p-group having p-class one larger than G,
 and order at most p^OrderBound; if Exponent is non-zero, generate
 descendants of G satisfying this exponent law; if StepSizes is supplied,
 then construct descendants of order p^(n + s) of a group of order p^n,
 only for s in StepSizes; by default, all descendants of G are returned;
 if MaxAuts is true, then construct maximally automorphic descendants;
 if All = false, only capable ones are returned;
 also return total number of descendants}

   return Descendants (G, pClass (G) + 1 : OrderBound := OrderBound,
          CharRank := CharRank, MaxAuts := MaxAuts,
              Exponent := Exponent, StepSizes := StepSizes, All := All);
end intrinsic;

/* K is d-generator p-group; set up GL (d, p) */
InitialiseMaps := function (K)
   p, d := DefiningParameters (K);
   G := GL (d, p);
   B := [G.i : i in [1..Ngens (G)]];
   P := [];
   order := OrderGL (d, p);

   return SetupMaps (K, B, P, order);
end function;

intrinsic GeneratepGroups (p:: RngIntElt, d:: RngIntElt, c:: RngIntElt:
     MaxAuts := false, OrderBound := 0, Exponent := 0, StepSizes := [], All := true)
 -> SeqEnum, RngIntElt
{Generate tree of d-generator p-class <= c p-groups of order at
 most p^OrderBound; if Exponent is non-zero, generate groups satisfying
 this exponent law; if StepSizes is supplied, then construct extensions
 of order p^(n + s) of a group of order p^n only for s in StepSizes;
 by default, all groups satisfying these properties are returned;
 if MaxAuts is true, then construct maximally automorphic descendants;
 if All = false, only capable ones are returned;
 also return total number of groups}

   require IsPrime (p): "Argument 1 is not a prime";
   requirege d, 1;
   requirege c, 1;
   requirege OrderBound, 0;
   require Exponent mod p eq 0: "Exponent must be divisible by", p;
   require forall {s : s in StepSizes | s gt 0}:
           "StepSizes must be positive";

   StepSizes := SetToSequence (Set (StepSizes));

   F := FreeGroup (d);

   K := pQuotient (F, p, 1: Print := 0);
   p, d := DefiningParameters (K);

   Auts := InitialiseMaps (K);
   Auts`Identifier := IntegerToString (p) cat "^" cat
                      IntegerToString (NPCgens (K));

   L, Total := MyDescendants (Auts: ClassBound := c, OrderBound := OrderBound,
      MaxAuts := MaxAuts, Exponent := Exponent, StepSizes := StepSizes, All := All);

   M := [L[i]`K: i in [1..#L]];
   for i in [1..#L] do
      // if NuclearRank (M[i]) gt 0 then
      if MyNuclearRank (M[i]: Exponent := Exponent) gt 0 then
         M[i]`Automorphisms := L[i];
      end if;
   end for;

   return [K] cat M, 1 + Total;

end intrinsic;

/*
Test := function (p, d, s)
   F := FreeGroup (d);

   K, theta, defs := pQuotient (F, p, 1: Print := 0);
   K`definitions := defs;
   p, d := DefiningParameters (K);

   Auts := InitialiseMaps (K);
   L := OneStepSize (Auts, s);
   return L;

end function;
*/

LeastNonmember := function (Orbits, degree)
   entry := 1;
   repeat
      if exists {i : i in [1..#Orbits] | entry in Orbits[i]} then
         entry +:= 1;
      else
         return entry;
      end if;
   until entry gt degree;
   return entry;
end function;

FindRCG := function (p, d, s: SubgroupLabel := 1, NmrOrbits := 0,
                              Process := true)
   OrbitRecord := recformat <Reps: SeqEnum, Lengths: SeqEnum,
                   StepSize: RngIntElt, Fixed: RngIntElt>;

   F := FreeGroup (d);

   K := pQuotient (F, p, 1: Print := 0);
   p, d := DefiningParameters (K);

   Auts := InitialiseMaps (K);

   H := K;

   P, _, PQ := pCoveringGroup (H);
   Auts`PQ := PQ;

   /* at entry no fixed generators */
   P`fixed := 0;
   P`stepSize := s;

   M := Multiplicator (P);
   p, d := DefiningParameters (M);
   N := Nucleus (P, H);
   P`nuclearRank := NPCGenerators (N);
   P`multiplicatorRank := NPCGenerators (M);

   Auts`Autos := ExtendAutomorphisms (P, Auts`Autos, M);
   Auts`pAutos := ExtendAutomorphisms (P, Auts`pAutos, M);

   vprintf GeneratepGroups, 2:
         "M has rank %o, N has rank %o\n", NPCgens (M), NPCgens (N);

   k := P`fixed;
   sub := InitialSegmentSubgroup (M, Auts, k);
   vprintf GeneratepGroups, 2:
         "Initial segment subgroup has rank  %o\n", NPCGenerators (sub);

   C := sub;
   RN := C meet N;
   r := NPCGenerators (RN);
   RM := C meet M;
   q := NPCGenerators (RM);

   lower, upper, C := StepRange (P, sub, k + 1);

   pPowers := [p^i : i in [0..s * q]];

   ExtendToSubgroup (P, C, ~Auts`Autos);
   ExtendToSubgroup (P, C, ~Auts`pAutos);
   A := [Auts`Autos[i]`extension : i in [1..#Auts`Autos]];
   A cat:= [Auts`pAutos[i]`extension : i in [1..#Auts`pAutos]];
   A := [MatrixAlgebra (GF (p), Nrows (A[1])) ! a : a in A];

   RCG := [];
   Results := [];
   for s1 in [Maximum (lower, 0)..upper] do

      DefSets, Offset, degree := DefinitionSets (p, q, r, s1: Fixed := P`fixed);
      vprintf GeneratepGroups, 2: "\nDegree is %o\n", degree;
      label := SubgroupLabel;
      Orbits := [];
      repeat
         if s1 gt 0 then
            S, Usub, U := LabelToSubgroup (P, RM, label, DefSets, Offset);
t := Cputime ();
            orbit := ConstructOrbit (P, H, RM, S, A, DefSets, Offset, pPowers);
"Length of orbit is ", #orbit;
printf "time to construct orbit is %o\n", Cputime (t);
         else
//          Usub := RM;
            Usub := [M.i : i in [1..NPCGenerators (RM)]];
            n := NPCGenerators (H);
            U := [[<n + i, 1>] : i in [1..NPCGenerators (RM)]];
            orbit := {@ 1 @};
         end if;

         if Process eq true then
            PQ1, K := FactorSubgroup (Auts, U);
            // "back from FactorSubgroup ";
            S, phi, U := AllowableSubgroup (P, K);
            // Stab := AutosOrbitStabiliser (P, U, H, H, Auts);
            Chars := CharSpaces (H);
            Stab := OrbitStabiliser (P, M, U, H, H, Auts, Chars);
            AA := RestrictStabiliser (P, phi, K, Stab`Autos);
            BB := RestrictStabiliser (P, phi, K, Stab`pAutos);
            K`fixed := s1;
            K`stepSize := P`stepSize;
            Append (~RCG, rec <AutRF | P := K, K := H, Autos := AA,
                          PQ := PQ1, pAutos := BB, complete := false,
                          Order := Auts`Order div #orbit>);
         end if;

         Append (~Orbits, orbit);
         label := LeastNonmember (Orbits, degree);
         length := &+[#Orbits[i] : i in [1..#Orbits]];
         vprintf GeneratepGroups, 2:
             "\nNumber of subgroups processed is %o\n\n", length;

      until length eq degree or NmrOrbits eq #Orbits;

      if Process eq false then
         Reps := [Minimum (Orbits[i]): i in [1..#Orbits]];
         Lengths := [#Orbits[i]: i in [1..#Orbits]];
         Append (~Results, rec < OrbitRecord |
                  Reps := Reps, Lengths := Lengths, StepSize := s1>);
      end if;

   end for;

   if Process then
      return RCG, degree, DefSets, Offset;
   else
      return Results, degree, DefSets, Offset, label;
   end if;
end function;

CompleteList := function (p, d, s)
   List, degree := FindRCG (p, d, s);
   vprintf GeneratepGroups: "# of RCG is %o\n", #List;

   i := 0;
   repeat
      i +:= 1;
      Auts := List[i];
      if Auts`complete eq false then
         P := Auts`P; H := Auts`K;
         L := CharSubgroup (P, H, Auts, s);
         vprintf GeneratepGroups: "# of descendants is %o\n\n\n", #L;
         List cat:= L;
      end if;
   until i ge #List;

   return [x : x in List | x`complete eq true];
end function;

RandomRCG := function (p, d, s: SubgroupLabel := 1, NmrOrbits := 0,
                              Process := true)
   F := FreeGroup (d);

   K := pQuotient (F, p, 1: Print := 0);
   p, d := DefiningParameters (K);

   Auts := InitialiseMaps (K);

   H := K;

   P, PQ := pCoveringGroup (H);
   Auts`PQ := PQ;

   /* at entry no fixed generators */
   P`fixed := 0;
   P`stepSize := s;

   M := Multiplicator (P);
   p, d := DefiningParameters (M);
   N := Nucleus (P, H);
   P`nuclearRank := NPCGenerators (N);
   P`multiplicatorRank := NPCGenerators (M);

   Auts`Autos := ExtendAutomorphisms (P, Auts`Autos, M);
   Auts`pAutos := ExtendAutomorphisms (P, Auts`pAutos, M);

   vprintf GeneratepGroups: "M has rank %o, N has rank %o\n",
           NPCgens (M), NPCgens (N);

   k := P`fixed;
   sub := InitialSegmentSubgroup (M, Auts, k);
   vprintf GeneratepGroups:
       "Initial segment subgroup has rank %o\n", NPCGenerators (sub);

   C := sub;
   RN := C meet N;
   r := NPCGenerators (RN);
   RM := C meet M;
   q := NPCGenerators (RM);

   lower, upper, C := StepRange (P, sub, k + 1);
   assert s in [lower..upper];

   pPowers := [p^i : i in [0..s * q]];

   ExtendToSubgroup (P, C, ~Auts`Autos);
   ExtendToSubgroup (P, C, ~Auts`pAutos);
   A := [Auts`Autos[i]`extension : i in [1..#Auts`Autos]];
   A cat:= [Auts`pAutos[i]`extension : i in [1..#Auts`pAutos]];
   A := [MatrixAlgebra (GF (p), Nrows (A[1])) ! a : a in A];

   RCG := [];
   Results := [];
   Reps := [];
   Lengths := [];

   s1 := s;

   DefSets, Offset, degree := DefinitionSets (p, q, r, s1: Fixed := P`fixed);
   vprintf GeneratepGroups: "\nDegree is %o\n", degree;

   label := SubgroupLabel;
   Orbits := [];
   repeat
      if s1 gt 0 then
         S, U := LabelToSubgroup (H, RM, label, DefSets, Offset);
t := Cputime ();
         orbit := ConstructOrbit (P, H, RM, S, A, DefSets, Offset, pPowers);
"#orbit is ", #orbit;
printf "time to construct orbit is %o\n", Cputime () - t;
      else
         U := RM;
         orbit := {@ 1 @};
      end if;

      label := Minimum (orbit);
      if label in Reps then
         print "We knew that already";
      else
         PrintFileMagma ("DETAILS", orbit);
         Append (~Reps, label);
         Append (~Lengths, #orbit);
         total := &+Lengths;
         vprintf GeneratepGroups: "Reps is %o\n", Reps;
         vprintf GeneratepGroups: "Lengths is %o\n", Lengths;
         vprintf GeneratepGroups:
              "Number of subgroups processed is %o\n\n", total;
      end if;
      if total lt degree then
         repeat
            label := Random ([1..degree]);
         until not (label in Reps);
         // printf "\nNow process label %o\n", label;
      end if;

   until total eq degree or NmrOrbits eq #Reps;

   return Reps, Lengths;
end function;
