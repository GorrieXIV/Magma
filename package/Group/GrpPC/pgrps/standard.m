freeze;

import "misc.m": DefiningParameters, pCoverFunction,
                 Multiplicator, Nucleus;
import "autos.m": MatrixToAutomorphism, ExtendAutomorphisms,
                  ExtendToSubgroup;
import "generate.m": TraceWord, InitialSegmentSubgroup,
                     LabelToSubgroup, FactorSubgroup, InitialiseMaps;
import "cf.m": OrbitStabiliser, SchreierVectorToAutGroup;
import "centrals.m": CentralAutomorphisms;
import "parameters.m": AutRF, RF, NHITS;
import "approximate.m": BirthdayParadox;
import "aut.m": RestrictStabiliser;
import "char-spaces.m": CharSpaces;

declare verbose Standard, 2;

ConstructOrbit := ConstructOneOrbitInternal;

/* Type for caching orbits */
declare type _IsIsomorphicPGroupsConstructOneOrbitCache;
declare attributes _IsIsomorphicPGroupsConstructOneOrbitCache : orbits, learning, fail;
orbitCacheRF := recformat< inputValues : UserProgram, outputValues : UserProgram >;

/* g is an element of a pc-group; rewrite as element
   of FP-group D where we map G.i -> D.(i + offset) */
ConvertWord := function (offset, g, D)
   w := Eltseq (g);
   return  &cat [[offset + i : j in [1..w[i]]] : i in [1..#w]];
end function;

NewPresentation := function (F, G, RCG, standard, nK, classK)
   p, d := DefiningParameters (G);

   /* new generators needed */
   images := [standard (RCG.i) : i in [1..d]];
   images := [Eltseq  (x) : x in images];
   images := [[x[i] : i in [1..nK]] : x in images];
   index := &join{{j : j in [1..nK] | images[i][j] gt 0} : i in [1..d]};
   index := SetToSequence (index);
   Sort (~index);
   vprintf Standard, 2: "New generators needed are %o\n", index;
   new := #index;

   m := Ngens (F);

   /* apply Tietze transformation to existing relations */
   ImF := FreeGroup (new + m);
   // gamma := hom < F -> ImF | [<F.i, ImF.(new + i)>: i in [1..m]]>;
   gamma := hom < F -> ImF | [ImF.(new + i): i in [1..m]]>;
   Rels := Relations (F);
   for r in Rels do
      ImF := AddRelation (ImF, gamma (r));
   end for;

   /* renumbering for new generators */
   nmr := 0;
   number := [];
   for i in index do
      nmr +:= 1;
      number[i] := nmr;
   end for;
   vprintf Standard, 2: "Renumbering for %o is %o\n", index, number;

   /* add new relations */
   for i in [1..#images] do
      L := [new + i];
      R := ConvertWord (0, images[i], ImF);
      R := [number [R[j]] : j in [1..#R]];
      ImF := AddRelation (ImF, L = R);
   end for;

   /* add definitions */

   rem := [x : x in index | x gt d];
   if #rem gt 0 then
      K, phi := pQuotient (F, p, classK: Print := 0);
      p, d := DefiningParameters (K);
      Words := SLPGroup(d);
      wordMap := hom<K->Words|[<K.i,Words.i>: i in [1..d]]>;
      preGens := [(K.i)@@phi: i in [1..d]];
      Rem := [Eltseq (Evaluate(wordMap(K.rem[i]),preGens)) : i in [1..#rem]];
      NewRem := [];
      for rem in Rem do
          copy := rem;
          for j in [1..#rem] do
             if rem[j] lt 0 then
                abs := Abs (rem[j]);
                copy[j] := -number[abs];
             else
                copy[j] := number[rem[j]];
             end if;
          end for;
          Append (~NewRem, copy);
      end for;
      Rem := NewRem;

      for i in [1..#Rem] do
         L := [d + i];
         R := Rem[i];
         vprintf Standard, 2: "For definitions L, R are %o and %o\n", L, R;
         ImF := AddRelation (ImF, L = R);
      end for;
   end if;

   return ImF;
end function;

intrinsic SubgroupToMatrix (P::GrpPC, M::GrpPC, K::GrpPC, H::GrpPC :
                            Relative := -1) -> ModMatFldElt
{P is p-covering group of H; M is relative multiplicator; K is
 class c quotient; H is class c - 1 quotient;
 if Relative is non-negative, then it is the relative step size;
 otherwise step size is log of #K div #H;
 return matrix of (relative) allowable subgroup from P to K}

   p, d := DefiningParameters (H);

   D := pQuotientDefinitions(P);
   DK := pQuotientDefinitions(K);
   if Relative ge 0 then
      s := Relative;
   else
      s := Ilog (p, #K div #H);
   end if;
   n := NPCGenerators (H);

   m := NPCGenerators (M);
   DS := [Position (D, DK[i]): i in [n + 1..n + s]];

   q := NPCGenerators (M);
   R := RMatrixSpace (GF (p), s, q);
   S := Zero (R);
   for i in [1..s] do
      S[i][DS[i] - n] := 1;
   end for;

   DP := pQuotientDefinitions(P);

   D := [D[i]: i in [1..n + m]];
   for y in DK do Exclude (~D, y); end for;

   for r in D do
      col := Position (DP, r) - n;
      u := r[1]; v := r[2];
      rel := v eq 0 select K.u^p else (K.u, K.v);
      e := Eltseq (rel);
      e := [e[i] : i in [n + 1..n + s]];
      for j in [1..s] do
         S[j][col] := e[j];
      end for;
   end for;

   return S;

end intrinsic;

/* P is p-covering group of H, class c - 1; K is class c quotient */
ProcessCharSubgroup := function (G, P, K, H, Chars, Auts, F : SubgroupRank := 0, OrbitCache := 0)
   p, d := DefiningParameters (H);
   classK := pClass (K);
   nK := NPCGenerators (K);

   M := Multiplicator (P);
   q := NPCGenerators (M);
   P`multiplicatorRank := q;
   N := Nucleus (P, H);
   P`nuclearRank := NPCGenerators (N);

   /* automorphism action on M */
   Auts`Autos := ExtendAutomorphisms (P, Auts`Autos, M);
   Auts`pAutos := ExtendAutomorphisms (P, Auts`pAutos, M);

   vprintf Standard: "M has rank %o, N has rank %o\n", NPCgens (M), NPCgens (N);

   /* allowable subgroup factored from P to give K */
   S, phi, U := AllowableSubgroup (P, K);

   q := Maximum (P`fixed, SubgroupRank);
   repeat
      C := InitialSegmentSubgroup (H, P, M, Auts, q, q + 1);
      /* relative p-multiplicator and nucleus */
      RN := C meet N;
      RM := C meet M;
      RU := C meet U;
      q := NPCGenerators (RM);
   until #RU gt 1 or RM eq M;

   rankC := NPCgens (C);
   vprint Standard: "Rank of characteristic subgroup is ", rankC;

   complete := C eq M;
   u := NPCGenerators (RU);
   s := q - u;

   /* automorphism action on characteristic subgroup C */
   ExtendToSubgroup (P, C, ~Auts`Autos);
   ExtendToSubgroup (P, C, ~Auts`pAutos);
   A := [Auts`Autos[i]`extension : i in [1..#Auts`Autos]];
   A cat:= [Auts`pAutos[i]`extension : i in [1..#Auts`pAutos]];
   A := [MatrixAlgebra (GF (p), rankC) ! a : a in A];
   /* stabiliser may be trivial */
   if #A eq 0 then
      A := [Identity (MatrixAlgebra (GF (p), NPCgens (C)))];
   end if;

   pPowers := [p^i : i in [0..s * q]];
   r := NPCgens (RN);
   DefSets, Offset, degree := DefinitionSets (p, q, r, s: Fixed := P`fixed);

   /* matrix for allowable subgroup U */
   S := SubgroupToMatrix (P, RM, K, H: Relative := s);

   EstimateOrbit := false;
   if EstimateOrbit eq true then
      /* orbit of U under action of automorphisms */
      space := sub <VectorSpace (GF (p), Ncols (S)) | [S[i]: i in [1..Nrows (S)]]>;

      lb, ub, estimate := BirthdayParadox (space, sub <GL(rankC, p)|A>, NHITS);
      vprint Standard: "Estimated length of orbit of allowable subgroup is ",
                  lb, ub, estimate;
   end if;

   /* Has the orbit already been constructed? */
   preComputed := false;
   preComputedOrbitCorrection := false;
   preComputedOrbitCorrectionMap := 0;

   /* OrbitCache is either 0 or an object of type _IsIsomorphicPGroupsConstructOneOrbitCache */
   if Type(OrbitCache) eq _IsIsomorphicPGroupsConstructOneOrbitCache and not OrbitCache`learning then
      for o in OrbitCache`orbits do
         o_A, o_S, o_DefSets, o_Offset, o_OrderOfP := o`inputValues();

         /* compare to the current orbit computation */
         if o_A cmpeq A and o_DefSets cmpeq DefSets and o_Offset cmpeq Offset and o_OrderOfP cmpeq #P then
            orbit, SC, BP, Stab, cached_P := o`outputValues();
            if o_S eq S then
               /* The subspaces are the same, no orbit correction map needed */
            else
               /* The subspaces are different, need to amend mappings to include
                  S -> cached_S too */
               matrixLabel := MatrixToLabelInternal(S, DefSets, Offset, pPowers);
               pos := Position(orbit, matrixLabel);
               if pos eq 0 then
                  /* This means not isomorphic */
                  OrbitCache`fail := true;
                  /* Must return 5 dummy values */
                  return 0, 0, 0, 0, 0;
               end if;

               /* Find the necessary mapping to send S to the cached value of S */
               word := TraceWord (pos, SC, BP);
               vprintf Standard, 2:"Word is %o\n", word;
               maps := [Auts`Autos[i]`map : i in [1..#Auts`Autos]]
                       cat [Auts`pAutos[i]`map : i in [1..#Auts`pAutos]];
               gamma := SchreierVectorToAutGroup (P, maps);
               inverse := [-x: x in word]; Reverse (~inverse);

               preComputedOrbitCorrection := true;
               preComputedOrbitCorrectionMap := gamma(inverse);
            end if;

            preComputed := true;
            vprint Standard :  "Using orbit cache, length: ", #orbit;
            break;
         end if;
      end for;
   end if;

   if not preComputed then
      orbit, SC, BP := ConstructOrbit (A, S, DefSets, Offset: Trace := true);

      if Type(OrbitCache) eq _IsIsomorphicPGroupsConstructOneOrbitCache and OrbitCache`learning then
            Append(~OrbitCache`orbits,
               rec< orbitCacheRF |
                  inputValues  := func< | A, S, DefSets, Offset, #P >
               >
            );
      end if;
   end if;

   vprint Standard: "Length of orbit of allowable subgroup is ", #orbit;

   /* choose orbit representative */
   label, pos := Minimum (orbit);

   /* is U the orbit representative? */
   identity := pos eq 1;

   /* if we have a precomputed orbit correction then must move things around */
   if preComputedOrbitCorrection then identity := false; end if;

   vprintf Standard:"Label is %o and orbit representative is %o\n",
                  orbit[1], label;

   /* if U is not the orbit representative, then standard map is not identity;
      write down new presentation for G and standard presentation for K */
   if identity eq false then
      /* find standard map from allowable subgroup U to orbit representative */
      word := TraceWord (pos, SC, BP);
      vprintf Standard, 2:"Word is %o\n", word;
      maps := [Auts`Autos[i]`map : i in [1..#Auts`Autos]]
              cat [Auts`pAutos[i]`map : i in [1..#Auts`pAutos]];
      gamma := SchreierVectorToAutGroup (P, maps);
      inverse := [-x: x in word]; Reverse (~inverse);
      result := gamma (inverse);
      vprintf Standard, 2: "Result is %o\n", [result (P.i) : i in [1..d]];

      /* Check if we need to apply the correction due to using a cached orbit */
      if preComputedOrbitCorrection then
         result := preComputedOrbitCorrectionMap^-1 * result;
      end if;

      StandardMap := [ rec < RF | map := result > ];
      ExtendToSubgroup (P, C, ~StandardMap);
   end if;

   /* factor orbit representative to give standard presentation for class c */
   S, Usub, U := LabelToSubgroup (P, RM, label, DefSets, Offset);

   PQ, RCG := FactorSubgroup (Auts, U);
   _, phi, U := AllowableSubgroup (P, RCG);

   if identity eq false then
      /* construct new presentation for G */
      StandardMap := RestrictStabiliser (P, phi, RCG, StandardMap);
      standard := StandardMap[1]`map;
      vprintf Standard, 2: "Standard map is %o\n",
                            [standard (RCG.i) : i in [1..d]];
      ImG := NewPresentation (F, G, RCG, standard, nK, classK);
      class := pClass (G);
      PQK := pQuotientProcess (ImG, p, classK: Print := 0);
      K := ExtractGroup (PQK);
      if class gt classK then
         NextClass (~PQK, class);
         G := ExtractGroup (PQK);
      end if;
   end if;

   if not preComputed then
      /* construct stabiliser of orbit representative */
      if #orbit gt 1 then
         Stab := OrbitStabiliser (P, M, U, H, H, Auts, Chars : Isom := true);
      else
         Stab := rec <AutRF | Autos:= Auts`Autos, pAutos := Auts`pAutos>;
      end if;

      /* Are we supposed to be caching this data? */
      if Type(OrbitCache) eq _IsIsomorphicPGroupsConstructOneOrbitCache and OrbitCache`learning then
         OrbitCache`orbits[#OrbitCache`orbits]`outputValues := func< | orbit, SC, BP, Stab, P >;
      end if;
   else
      /* The maps in Stab are for the pre computed group P which should be exactly the same
         as this group P, but Magma needs persuading that they are in fact the same */
      if IsIdenticalPresentation(cached_P, P) then
         P_to_cached_P := iso < P -> cached_P | [ cached_P.i : i in [1..NPCgens(cached_P)] ] >;
         Stab := rec < AutRF | Autos := [ rec < RF | map := P_to_cached_P * a`map * P_to_cached_P^-1 > : a in Stab`Autos ],
                              pAutos := [ rec < RF | map := P_to_cached_P * a`map * P_to_cached_P^-1 > : a in Stab`pAutos ]>;
      else
         //error "Cache failure";
         /* At this point it would be good to go back and see if we have used the wrong cached item (since.
            the Ps don't match!!) */
         if #orbit gt 1 then
            Stab := OrbitStabiliser (P, M, U, H, H, Auts, Chars : Isom := true);
         else
            Stab := rec <AutRF | Autos:= Auts`Autos, pAutos := Auts`pAutos>;
         end if;
      end if;
   end if;

   assert phi (P) eq RCG;
   A := RestrictStabiliser (P, phi, RCG, Stab`Autos);
   B := RestrictStabiliser (P, phi, RCG, Stab`pAutos);
   C := complete select CentralAutomorphisms (RCG, B) else [];

   Auts := rec <AutRF | Autos := A, pAutos := B cat C,
                        Order := p^(#C) * Auts`Order div #orbit>;

   if identity then ImG := F; end if;

   if complete then RCG`fixed := 0;     Auts`K := RCG;
               else RCG`fixed := q - u; Auts`K := RCG; Auts`PQ := PQ; end if;

   return Auts, G, K, ImG, complete;
end function;

/* G p-group; H class c - 1 standard;
   K initially class c non-standard; at end K is class c standard */
Standard := function (G, c : StartClass := 2, Auts := [], F := [], OrbitCache := 0)
   if c lt 2 then error "Class ", c, " must be at least 2"; end if;

   p := DefiningParameters (G);

   if Type (Auts) eq Rec and assigned (Auts`PQ) then
      PQ := Auts`PQ;
   else
      PQ := pQuotientProcess (G, p, Maximum (c - 1, 1): Print := 0);
   end if;

   if c le StartClass then
      H := ExtractGroup (PQ);
      if Type (Auts) eq SeqEnum and #Auts eq 0 then
         if c eq 2 then
            vprint Standard: "Setup class 2 Autos";
            Auts := InitialiseMaps (H);
         else
            vprint Standard: "Compute Autos for class", c - 1;
            AG := AutomorphismGroupPGroup (H);
            Auts := H`Automorphisms;
         end if;
      else
         "Supplied Autos";
      end if;
      F := FPGroup (G);
   end if;

   if not assigned Auts`PQ then Auts`PQ := PQ; end if;

   H := Auts`K;

   /* psi is homomorphism from G to class c quotient K */
   P, K, PQ, psi, PCoverPQ := pCoverFunction (PQ);

   P`stepSize := Ilog (p, #K div #H);
   P`fixed := 0;

   Auts`PQ := PCoverPQ;
   Chars := CharSpaces (H);
   repeat
      Auts, G, K, F, complete := ProcessCharSubgroup (G, P, K, H,
                                                      Chars, Auts, F : OrbitCache := OrbitCache);
      /* Check the fail attribute used in isomorphism testing */
      if OrbitCache cmpne 0 and OrbitCache`fail then return 0, 0, 0, 0; end if;
      if assigned Auts`K then P := Auts`K; end if;
   until complete eq true;

   return Auts, G, K, F;
end function;

intrinsic StandardPresentation (G:: GrpPC : StartClass := 1) -> GrpPC, Map
{return standard presentation H for G and map from G to H; if StartClass
 is k (default 1), then commence standardisation from class k onwards}

   require IsPrimePower (#G): "Argument must be group of prime-power order";

   p := DefiningParameters (G);

   class := pClass (G);
   H, tau := pQuotient (G, p, class + 1: Print := 0);

   class := pClass (H);
   if StartClass lt 2 then StartClass := 2; end if;
   if class eq 1 or StartClass gt class then return H, tau; end if;

   if pClass (H) eq 1 then return H, tau; end if;

   S := H; A := []; Q := [];
   for c in [Maximum (2, StartClass)..class] do
      vprint Standard: "\nNow construct standard presentation for class ", c;
      A, S, K, Q := Standard (S, c: StartClass := StartClass, Auts := A, F := Q);
      if #K eq #G then break; end if;
   end for;

   /* now set up isomorphism from H to S */
   T, alpha := pQuotient (Q, p, class: Print := 0);
   n := NPCGenerators (H); m := Ngens (Q);
   images := [alpha (Q.i) : i in [m - n + 1 .. m]];
   phi := hom <H -> T | images>;

   return T, tau * phi;

end intrinsic;

intrinsic IsIsomorphicPGroups (G:: GrpPC, H :: GrpPC) -> BoolElt, Map, GrpPC
{return true, a map from G to H, and the isomorphism class representative if the
 p-groups G and H are isomorphic; otherwise false}

   require IsPrimePower (#G) and IsPrimePower (#H):
      "Both arguments must have prime-power order";

   if #G ne #H then return false, _; end if;

   p, d := DefiningParameters (G);
   ph, dh := DefiningParameters (H);

   if p ne ph or d ne dh then return false, _; end if;

   class := pClass (G);
   if class ne pClass (H) then return false, _; end if;

   if IsIdenticalPresentation (G, H) or class eq 1 then
      return true, hom <G -> H | [H.i : i in [1..NPCgens (H)]]>, G;
   end if;

   X, delta := pQuotient (G, p, class : Print := 0);
   Y, gamma := pQuotient (H, p, class : Print := 0);

   if IsIdenticalPresentation (X, Y) then
      /* an identity homorphism from S to T */
      id := hom < X -> Y | [Y.i : i in [1..NPCgens (Y)]]>;
      images := [id (delta (G.i)) @@ gamma : i in [1..NPCgens (G)]];
      return true, hom < G -> H | images >, X;
   end if;

   S := X; T := Y;
   A := []; Q := [];
   B := []; R := [];

   /* Setup the orbit caching object */
   OrbitCache := New(_IsIsomorphicPGroupsConstructOneOrbitCache);

   for c in [2..class] do
      vprint Standard: "\nNow construct standard presentation for class ", c;
      /* init orbit cache */
      OrbitCache`orbits := [ ]; OrbitCache`learning := true; OrbitCache`fail := false;
      A, S, K, Q := Standard (S, c: Auts := A, F := Q, OrbitCache := OrbitCache);
      OrbitCache`learning := false;
      B, T, L, R := Standard (T, c: Auts := B, F := R, OrbitCache := OrbitCache);
      if OrbitCache`fail or not IsIdenticalPresentation (K, L) then
         vprint Standard: "Standard presentations differ at class ", c;
         return false, _, _;
      end if;
   end for;

   /* now set up isomorphism from G to S */
   S, alpha := pQuotient (Q, p, class: Print := 0);
   n := NPCGenerators (G); m := Ngens (Q);
   phi := hom <X -> S | [alpha (Q.i) : i in [m - n + 1 .. m]]>;
   phi := delta * phi;

   /* now set up isomorphism from H to T */
   T, beta  := pQuotient (R, p, class: Print := 0);
   n := NPCGenerators (H); m := Ngens (R);
   tau := hom <Y -> T | [beta (R.i): i in [m - n + 1 .. m]]>;
   tau := gamma * tau;

   /* an identity homorphism from S to T */
   id := hom < S -> T | [T.i : i in [1..NPCgens (T)]]>;

   /* construct mapping from G -> H */
   images := [id (phi (G.i)) @@ tau : i in [1..NPCgens (T)]];
   return true, hom < G -> H | images >, S;

end intrinsic;
