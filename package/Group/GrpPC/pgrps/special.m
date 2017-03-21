freeze;

/* g is an element of a pc-group; rewrite as element
   of FP-group D where we map G.i -> D.(i + offset) */
ConvertWord := function (offset, g, D)
   w := Eltseq (g);
   return  &cat [[offset + i : j in [1..w[i]]] : i in [1..#w]];
end function;

TietzeTransform := function (w, Images, Inverses)
   letters := Eltseq (w);
   image := [];
   for l in letters do
      if l lt 0 then
         image cat:= Inverses[Abs (-l)];
      elif l gt 0 then
         image cat:= Images[l];
      end if;
   end for;

   return image;
end function;

ModifyRelations := function (F, Images, Inverses)
   ImF := FreeGroup (Ngens (F));
   Rels := Relations (F);
   for relation in Rels do
      l := LHS (relation);
      L := TietzeTransform (l, Images, Inverses);
      r := RHS (relation);
      R := TietzeTransform (r, Images, Inverses);
      ImF := AddRelation (ImF, L = R);
   end for;

   return ImF;
end function;

/* phi : G -> H */
MapRelations := function (G, H, phi, standard)
   F, fpmap := FPGroup (G);
   p, d := DefiningParameters (G);
   n := NPCGenerators (H);
   Images := [((standard (H.i)) @@ phi) @@ fpmap : i in [1..n]];
   Images cat:= [F.i : i in [n + 1..Ngens (F)]];
   Inverses := [Images[i]^-1 : i in [1..#Images]];
   Images := [Eltseq (Images[i]) : i in [1..#Images]];
   Inverses := [Eltseq (Inverses[i]) : i in [1..#Inverses]];
   ImF := ModifyRelations (F, Images, Inverses);
   return ImF, Images;
end function;

NewPresentation := function (F, G, K, standard, nK)
   n := NPCGenerators (K);
   p, d := DefiningParameters (G);

   /* new generators needed */
   images := [standard (K.i) : i in [1..d]];
   images := [Eltseq  (x) : x in images];
   images := [[x[i] : i in [1..nK]] : x in images];
   index := &join{{j : j in [1..nK] | images[i][j] gt 0} : i in [1..d]};
   index := SetToSequence (index);
   Sort (~index);
   printf "New generators needed are %o\n", index;
   new := #index;

   m := Ngens (F);
   ImF := FreeGroup (new + m);

   /* apply Tietze transformation to existing relations */
   Rels := Relations (F);
   Images := [[new + i]: i in [1..m]];
   Inverses := [[-new - i] : i in [1..m]];
   for relation in Rels do
      l := LHS (relation);
      L := TietzeTransform (l, Images, Inverses);
      r := RHS (relation);
      R := TietzeTransform (r, Images, Inverses);
      ImF := AddRelation (ImF, L = R);
   end for;

   /* renumbering for new generators */
   nmr := 0;
   thetaimages := [];
   number := [];
   for i in index do
      nmr +:= 1;
      number[i] := nmr;
      Append (~thetaimages, <F.i, ImF.nmr>);
   end for;
   printf "Renumbering for %o is %o\n", index, number;
thetaimages;

   /* add new relations */
   for i in [1..#images] do
printf "images is %o\n", images[i];
      L := [new + i];
      R := ConvertWord (0, images[i], ImF);
printf "FIRST L, R are %o and %o\n", L, R;
      R := [number [R[j]] : j in [1..#R]];
printf "NOW L, R are %o and %o\n", L, R;
      ImF := AddRelation (ImF, L = R);
   end for;

   /* add definitions */

   rem := [x : x in index | x gt d];
   if #rem gt 0 then
      print "rem is ", rem;
      K, phi := pQuotient (F, p, 0: Print := 1);
      Rem := [Eltseq (K.rem[i] @@ phi) : i in [1..#rem]];
      p, d := DefiningParameters (K);
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
         printf "FOR defns L, R are %o and %o\n", L, R;
         ImF := AddRelation (ImF, L = R);
      end for;
   end if;

   return ImF;

end function;

/* P is p-covering group of H; M is relative multiplicator;
   K is class c quotient; H is class c - 1 quotient;
   write down matrix of allowable subgroup from P to K */
SubgroupToMatrix := function (P, M, K, H : Relative := -1)
   p, d := DefiningParameters (H);

   D := pQuotientDefinitions(P);
   DK := pQuotientDefinitions(K);
   if Relative ge 0 then
      s := Relative;
   else
      s := Ilog (p, #K div #H);
   end if;
print "s is ", s;
   n := NPCGenerators (H);

   m := NPCGenerators (M);
   DS := [Position (D, DK[i]): i in [n + 1..n + s]];

   q := NPCGenerators (M);
   R := RMatrixSpace (GF (p), s, q);
   S := Zero (R);
   for i in [1..s] do
      S[i][DS[i] - n] := 1;
   end for;

"S is ", S;
   DP := pQuotientDefinitions(P);

   D := [D[i]: i in [1..n + m]];
   for y in DK do Exclude (~D, y); end for;
print "D is now ", D;

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

   "S is ", S;
   return S;
end function;

/* P is p-covering group of H, class c - 1; K is class c quotient */
ProcessCharSubgroup := function (G, P, K, H, Auts, F : SubgroupRank := 0)
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

   printf "M has rank %o, N has rank %o\n", NPCgens (M), NPCgens (N);

   /* allowable subgroup factored from P to give K */
   S, phi, U := AllowableSubgroup (P, K);

   q := Maximum (P`fixed, SubgroupRank);
   repeat
      C := InitialSegmentSubgroup (M, Auts, q);
      "rank of sub is ", NPCgens (C);
      /* relative p-multiplicator and nucleus */
      RN := C meet N;
      RM := C meet M;
      RU := C meet U;
      q := NPCGenerators (RM);
   until #RU gt 1 or RM eq M;

   "finally rank of sub is ", NPCgens (C);

   complete := C eq M;
   u := NPCGenerators (RU);
   s := q - u;

   /* automorphism action on characteristic subgroup C */
   ExtendToSubgroup (P, C, ~Auts`Autos);
   ExtendToSubgroup (P, C, ~Auts`pAutos);
   A := [Auts`Autos[i]`extension : i in [1..#Auts`Autos]];
   A cat:= [Auts`pAutos[i]`extension : i in [1..#Auts`pAutos]];
   A := [MatrixAlgebra (GF (p), Nrows (A[1])) ! a : a in A];

   pPowers := [p^i : i in [0..s * q]];
   r := NPCgens (RN);
   DefSets, Offset, degree := DefinitionSets (p, q, r, s: Fixed := P`fixed);
   printf "\nDegree is %o\n\n", degree;

   /* matrix for allowable subgroup U */
   S := SubgroupToMatrix (P, RM, K, H: Relative := s);

/*
AA := sub <GL(Nrows (A[1]), p) | A >;
   lb, ub, b := BirthdayParadox (S, AA, 16: MAXSIZE := 10^5);
"estimates are ", lb, ub, b;
*/

   /* orbit of U under action of automorphisms */
time orbit, SC, BP := ConstructOrbit (P, K, RM, S, A, DefSets, Offset, pPowers:
                                      Trace := true);
// print "orbit is ", orbit;
   print "# of orbit is ", #orbit;
// print "SC is ", SC;
// print "BP is ", BP;

   /* choose orbit representative */
   label, pos := Minimum(orbit);

   /* is U the orbit representative? */
   identity := label eq orbit[1];

printf "non-standard is %o and orbit rep is %o\n", orbit[1], label;

   /* if U is not the orbit representative, then standard map is not identity;
      write down new presentation for G and standard presentation for K */

   if identity eq false then
      /* find standard map from allowable subgroup U to orbit representative */
      word := TraceWord (pos, SC, BP);
      printf "\n\nword is %o\n\n", word;
      maps := [Auts`Autos[i]`map : i in [1..#Auts`Autos]]
              cat [Auts`pAutos[i]`map : i in [1..#Auts`pAutos]];
      inverses := [];
      SchreierVectorToMap (word, maps, ~inverses, ~result);
      result := PowHom (result, -1);
      printf "result is %o\n", [result (P.i) : i in [1..d]];
      StandardMap := [rec < RF | map := result>];
      ExtendToSubgroup (P, C, ~StandardMap);
   end if;

   /* now factor orbit representative to give standard
      presentation for class c */
   if s gt 0 then
      S, Usub, U := LabelToSubgroup (P, H, RM, label, DefSets, Offset);
   else
      Usub := [M.i : i in [1..NPCGenerators (RM)]];
      n := NPCGenerators (H);
      U := [[<n + i, 1>] : i in [1..NPCGenerators (RM)]];
   end if;

   PQ, RCG := FactorSubgroup (Auts, U);
   _, phi, U := AllowableSubgroup (P, RCG);

   if identity eq false then
      /* construct new presentation for G */
      StandardMap := RestrictStabiliser (P, phi, RCG, StandardMap);
      standard := StandardMap[1]`map;
      printf "standard is %o\n", [standard (RCG.i) : i in [1..d]];
      ImG := NewPresentation (F, G, RCG, standard, nK);
      class := pClass (G);
      PQK := pQuotientProcess (ImG, p, classK: Print := 1);
      K := pQuotient (ImG, p, classK: Print := 1);
      // K, _, defs := ExtractGroup (PQK);
      if class gt classK then
         NextClass (~PQK, class);
         G := pQuotient (ImG, p, class: Print := 1);
      end if;
      // G, _, defs := ExtractGroup (PQK);
      // G`definitions := defs;
   end if;

   "HERE WE ARE AFTER IDENTITY = FALSE";

   /* construct stabiliser of orbit representative */
//   Stab := AutosOrbitStabiliser (P, U, H, H, Auts);
   Chars := CharSpaces (H);
   Stab := OrbitStabiliser (P, M, U, H, H, Auts, Chars);
   "HERE WE ARE AFTER DETERMINING STAB";
"stab is ", Stab;
assert phi (P) eq RCG;
   A := RestrictStabiliser (P, phi, RCG, Stab`Autos);
   B := RestrictStabiliser (P, phi, RCG, Stab`pAutos);
   // C := complete select CentralAutomorphisms (RCG) else [];
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
Standard := function (G, c : Auts := [], F := [])
   if c lt 1 then error "Class ", c, " must be at least 1"; end if;

   p, d := DefiningParameters (G);

   if Type (Auts) eq Rec and assigned (Auts`PQ) then
      PQ := Auts`PQ;
   else
      PQ := pQuotientProcess (G, p, Maximum (c - 1, 1): Print := 1);
   end if;

   if c le 2 then
      H := ExtractGroup (PQ);
//      a, b := OverGroups (H);
//      Auts := StabiliserOverGroups (H, H, a, b);
      Auts := InitialiseMaps (H);
      F := FPGroup (G);
   end if;

   if c eq 1 then return Auts, G, H; end if;

   if not assigned Auts`PQ then Auts`PQ := PQ; end if;

   H := Auts`K;

   /* psi is homomorphism from G to class c quotient K */
   P, K, PQ, psi, PCoverPQ := pCoverFunction (PQ);
   P`stepSize := Ilog (p, #K div #H);
   P`fixed := 0;

   Auts`PQ := PCoverPQ;
   repeat
      Auts, G, K, F, complete := ProcessCharSubgroup (G, P, K, H, Auts, F);
      if assigned Auts`K then P := Auts`K; end if;
   until complete eq true;

   return Auts, G, F;
end function;

ConstructStandard := function (G: ClassBound := 0)
   p, d := DefiningParameters (G);

   S := G;
   if ClassBound eq 0 then
      class := pClass (S);
   else
      class := ClassBound;
   end if;

   A := []; Q := [];

   if pClass (S) eq 1 then return S, IdentityHomomorphism (S), _; end if;

   for c in [2..class] do
      A, S, Q := Standard (S, c: Auts := A, F := Q);
   end for;

   /* now set up isomorphism from G to S */
   T, alpha := pQuotient (Q, p, class: Print := 1);
//   assert IsIdenticalPresentation (T, S);

   n := NPCGenerators (G); m := Ngens (Q);
   images := [alpha (Q.i) : i in [m - n + 1 .. m]];
   phi := hom < G -> T | images : Check := false>;
   return T, phi, A, Q, S;
end function;
