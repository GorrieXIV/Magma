freeze;

import "misc.m": DefiningParameters, DualSpace, SubspaceToSubgroup,
          pCoverFunction, Multiplicator, OrderGL;
import "char-spaces.m": CharSpaces;
import "parameters.m": SMALLORDER, AutRF, RF;
import "autos.m": MatrixToAutomorphism, ActionOnFactor, ExtendAutomorphisms;
import "cf.m": OrbitStabiliser;
import "canonical.m": BaseForMatrixGroup;
import "centrals.m": CentralAutomorphisms;
import "stab-of-spaces.m": MyStabiliserOfSpaces;

/* points for projective action of elementary abelian group G */
PGLPoints := function (G)
   p, d := DefiningParameters (G);
   a, b := PGL (d, p);
   return b, {@ G ! x: x in b @};
end function;

/* H elementary abelian */
SpecialMinimalSubgroups := function (H)
   assert IsElementaryAbelian (H);
   points, E := PGLPoints (H);
   return [sub < H | x> : x in E], points;
end function;

/* H elementary abelian */
SpecialMaximalSubgroups := function (H: points := [])
   assert IsElementaryAbelian (H);
   if #points eq 0 then
      points, E := PGLPoints (H);
   end if;
   d := Degree (Rep (points));
   F := BaseRing (Parent (Rep (points)));
   V := VectorSpace (F, d);
   spaces := [DualSpace (sub < V | point >): point in points];
   E := [SubspaceToSubgroup (H, V, s, 0: Subgroup := H): s in spaces];
   return E, points;
end function;

/* S is normal subgroup of G; phi is natural homomorphism
   from G to G / S; H is a characteristic subgroup of G / S;
   determine its minimal subgroups and take preimages in G */
MyMinimalSubgroups := function (G, H, S, phi)
   points, E := PGLPoints (H);
   return [sub < G | x @@ phi, S >: x in E], points, E;
end function;

/* phi: G -> G / S = Q; H is characteristic subgroup of G/S;
   determine its maximal subgroups and take preimages in G */
MyMaximalSubgroups := function (G, H, S, phi, points, Q, c)
   d := Degree (Rep(points));
   F := BaseRing (Parent (Rep(points)));
   V := VectorSpace (F, d);
   spaces := [DualSpace (sub < V | point >): point in points];
   E := [SubspaceToSubgroup (Q, V, s, c: Subgroup := H): s in spaces];
   return [sub < G | x @@ phi, S >: x in E], spaces, E;
end function;

/* compute fingerprint for subgroup U  of G */
FingerprintSubgroup := function (G, U)
   p := FactoredOrder (G)[1][1];

   D := DerivedSeries (U);
   id := < #Centraliser (G, U), [NPCGenerators (d): d in D],
            Exponent (U), pRanks (U),
            AbelianInvariants (Centre (quo < G | U>)),
            AbelianInvariants (Centre(U)), #CommutatorSubgroup (G, U) >;

   if Order (U) gt SMALLORDER then
      Append (~id, 0);
      Append (~id, {});
      return id;
   end if;

   cl := Classes (U);

   Append (~id, #cl);
   Append (~id, {x[1] : x in cl});

   return id;
/*
   E := {x : x in U};
   cl := [];
   repeat
      x := Random (E);
      orb := x^G;
      Append (~cl, Rep (orb));
      E diff:= orb;
   until #E eq 0;

   Append (~id, #cl);
   l := [Order (x) : x in cl];
   Sort (~l);
   Append (~id, l);
   return id;
*/
end function;

/* M is a collection of subgroups of G;
   partition M under certain fingerprints */
PartitionSubgroups := function (G, M)
   parts := [];
   Values := {@ @};
   for i in [1..#M] do
      v := FingerprintSubgroup (G, M[i]);
      pos := Index (Values, v);
      if pos eq 0 then
         Append (~parts, {i});
         Include (~Values, v);
      else
         Include (~parts[pos], i);
      end if;
   end for;

   return parts;
end function;

/* write down projective action of matrix group M on supplied set of points */
PGLAction := function (M, points)
   if Type (M) eq GrpMat then
      M := [M.i: i in [1..Ngens (M)]];
   end if;

   /* projective action of m on point */
   ActionImage := function (m, point)
      image := point^m;
      d := Depth (image);
      return image[d]^-1 * image;
   end function;

   A := [[Position (points, ActionImage (M[i], point)): point in points]:
                                                       i in [1..#M]];
   return sub <Sym (#points) | A>;
end function;

/* write down kernel of G <= GL (d, q) -> PGL (d, q) */
KernelPGL := function (G)
   K := [];

   F := BaseRing (G);
   if #F eq 2 then return K; end if;

   d := Degree (G);
   p := Characteristic (F);

   omega := PrimitiveElement (F);
   fac := Factorisation (p - 1);
   identity := Identity (MatrixAlgebra (F, d));
   for i in [1..#fac] do
      a := fac[i][1];
      b := fac[i][2];
      for j in [1..b] do
         images := identity;
         for k in [1..d] do images[k][k] := omega; end for;
         Append (~K, images);
         omega := omega^a;
      end for;
   end for;

   return [GL (d, F) ! K[i] : i in [1..#K]];
end function;

/* try to find a small generating set for a group U */
SmallGeneratingSet := function (U)
   n := Ngens (U);
   d := 2; c := 0; NmrTrials := 10;

   while d lt n do
      L := sub < U | [Random (U): i in [1..d]]>;
      if #L eq #U then
         vprint AutomorphismGroup, 2:
             "Size of generating set is now ", Ngens (L);
         return L;
      end if;
      c +:= 1;
      if c eq NmrTrials then c := 0; d +:= 1; end if;
   end while;

   return U;
end function;

/* map from Y to X; write down image of elements of S */
SubgroupPreimage := function (X, Y, S)
   theta := hom< Y -> X | [ X.i : i in [1..Ngens(X)] ] >;
   return [s @ theta: s in S];
end function;

/* write down a description of the stabiliser in Mat
   of the partition, parts, of points */
StabiliserOverGroups := function (G, parts, points: Mat := [])
   p, d := DefiningParameters (G);

   /* Magma treats GL(1, 2) as a group with zero generators */
   if p eq 2 and d eq 1 then
      return [[1]];
      // return sub < GL (d, p) | >;
   end if;

   if Mat cmpeq [] then
      M := GL (d, p);
   else
      M := Mat;
   end if;

   P := PGLAction (M, points);

   assert Ngens (P) eq Ngens (M);

   S := SmallGeneratingSet (Stabiliser (P, parts));

   if Ngens (S) eq 0 then return [Identity (M)], 1, [Identity (S)]; end if;

   Perms := [S.i : i in [1..Ngens (S)]];
   Mats := SubgroupPreimage (M, P, Perms);

   return Mats, #S, Perms;
end function;

/* phi is hom from P to K; Stab is sequence of
   automorphisms of P; restrict to act on K */
RestrictStabiliser := function (P, phi, K, Stab)
   _, d := DefiningParameters (K);

   for i in [1..#Stab] do
      alpha := Stab[i]`map;
      Stab[i]`map := hom < K -> K | [ P.j : j in [1..d] ] @ alpha @ phi : Check := false >;
      delete Stab[i]`extension;
   end for;

   return Stab;
end function;

/* set up automorphisms corresponding to non-p part */
NonPGroupMaps := function (H, B: Faithful := true, Perms := [])
   p, d := DefiningParameters (H);

   if Faithful eq true then
      if Perms eq [] then
         _, points := PGL (d, p);
         perms := PGLAction (B, points);
         assert Ngens (perms) eq #B;
         perms := [perms.i: i in [1..Ngens (perms)]];
      else
         perms := Perms;
      end if;
      Autos := [rec <RF | map := MatrixToAutomorphism (H, B[i]),
                type := "general", perm := perms[i]>: i in [1..#B]];
   else
      Autos := [rec <RF | map := MatrixToAutomorphism (H, B[i]),
                type := "general">: i in [1..#B]];
   end if;

   return Autos;
end function;

procedure PermRep (P, ~Autos)
   p, d := DefiningParameters (P);
   A := ActionOnFactor (P, P, FrattiniSubgroup (P), Autos);

   _, points := PGL (d, p);
   perms := PGLAction (A, points);
   assert Ngens (perms) eq #Autos;
   perms := [perms.i: i in [1..Ngens (perms)]];
   for i in [1..#perms] do
       Autos[i]`perm := perms[i];
  end for;
end procedure;

/* P describes p-subgroup of GL(d, p); set up corresponding automorphisms */
PGroupMaps := function (H, P: Faithful := false)
   p, d := DefiningParameters (H);
   if Faithful then
      _, points := PGL (d, p);
      perms := PGLAction (P, points);
      assert Ngens (perms) eq #P;
      perms := [perms.i: i in [1..Ngens (perms)]];
      return [rec < RF | map := MatrixToAutomorphism (H, P[i]),
                         perm := perms[i],
                         type := "p-automorphism"> :
                         i in [1..#P]];
   else
      return [rec < RF | map := MatrixToAutomorphism (H, P[i]),
                         type := "p-automorphism"> :
                         i in [1..#P]];
   end if;
end function;

/* H is group; B is block part of GL; P is p-part of P;
   order is order of subgroup of GL generatored by B and P */
SetupMaps := function (H, B, P, order: Faithful := false, Perms := [])
   faithful := Faithful; perms := Perms;
   Autos := NonPGroupMaps (H, B: Faithful := faithful, Perms := perms);
   pAutos := PGroupMaps (H, P: Faithful := faithful);
   return rec <AutRF | K := H, Autos := Autos, pAutos := pAutos,
                       Order := order>;
end function;

/* does the stored order agree with the order of the perm group generated
   by the automorphisms in their action on the underlying group? */
VerifyOrder := function (Auts)
   K := Auts`K;

   E :=  {@ x : x in K @};

   gens := [Auts`Autos[i]`map: i in [1..#Auts`Autos]] cat
           [Auts`pAutos[i]`map: i in [1..#Auts`pAutos]];

   perms := [[Position (E, alpha (x)): x in E] : alpha in gens];

   P :=  sub < Sym (#K) | perms>;

   ZQ := quo < K | Centre (K)>;
   if #P ne Auts`Order * #ZQ then
   //   error "Error: In VerifyOrder";
     "Error: In VerifyOrder";
      return false, P;
   end if;

   return true, P;
end function;

/* compute the automorphism group of the class c quotient of G;
   Auts describes the aut gp of the class c - 1 quotient;
   Data is used to supply start information for class 1;
   Chars is a list of known characteristic spaces */
ProcessClass := function (G, Auts, c:
                          Data := [], Chars := {@ @}, Verify := false)
   verify := Verify;

   p, d := DefiningParameters (G);

   C := Chars;

   if c eq 2 then
      /* H is class c - 1 p-quotient of G */
      PQ := pQuotientProcess (G, p, c - 1: Print := 0);
      H := ExtractGroup (PQ);
   else
      PQ := Auts`PQ;
      H := Auts`K;
   end if;

   /* compute p-covering group P of H and class c quotient K of G */
   P, K, PQ, theta := pCoverFunction (PQ);

   M := Multiplicator (P);
   /* identify allowable subgroup */
   Space, phi, U := AllowableSubgroup (P, K);

   if #Data ne 0 then
      B := Data[1]; Pgp := Data[2]; order := Data[3];
      Auts := SetupMaps (H, B, Pgp, order);
   end if;

   Auts`Autos := ExtendAutomorphisms (P, Auts`Autos, M);
   Auts`pAutos := ExtendAutomorphisms (P, Auts`pAutos, M);

   Stab, NewChars, Subgroup := OrbitStabiliser (P, M, U, G,
                                            H, Auts, C: Verify := verify);
   if Type (Stab) ne Rec then
      vprint AutomorphismGroup, 2: "About to start Class 2 again";
      /* we are going back to class 2 */
      C join:= NewChars;
      B := Subgroup[1]; Pgp := Subgroup[2]; order := Subgroup[3];
      Pgp := BaseForMatrixGroup (Pgp);
      return $$ (G, [], 2: Data := <B, Pgp, order>, Chars := C);
   end if;

   if verify then
      vprint AutomorphismGroup, 2: "Verify computed stabiliser";
      result := [x`map (U) eq U: x in Stab`Autos cat Stab`pAutos];
      if #result gt 0 then assert Set (result) eq {true}; end if;
   end if;

   A := RestrictStabiliser (P, phi, K, Stab`Autos);
   B := RestrictStabiliser (P, phi, K, Stab`pAutos);
   D := CentralAutomorphisms (K, B);
   vprint AutomorphismGroup: "Number of central automorphisms is ", #D;
   Auts := rec <AutRF | K := K, Autos := A, pAutos := B cat D,
                        PQ := PQ, Order := Stab`Order * p^#D>;
   return Auts, C, theta;
end function;

/* inner automorphisms of G */
InnerAutomorphisms := function (G)
   if IsAbelian (G) then return []; end if;
   return [ [ G.i ^ g : i in [1..NPCgens(G)] ] : g in Generators(G) ];
end function;

procedure ConvertAutos (K, theta, theta_inv, G, ~Autos)
   A := [];

   G_theta := Isetseq(PCGenerators(G)) @ theta;

   for alpha in Autos do
      a := alpha;
      a`map := hom < G -> G | G_theta @ alpha`map @ theta_inv : Check := false >;
      Append (~A, a);
   end for;

   Autos := A;
end procedure;

/* theta is hom from G to K; Auts are automorphisms of K; rewrite
   these as automorphisms of G and set up automorphism group */
ConvertAutomorphisms := function (G, Auts, theta)
   K := Auts`K;

   A := Codomain(theta);
   B := Domain(theta);
   theta_inv := hom < A -> B | [ A.i : i in [1..NPCgens(A)] ] @@ theta : Check := false >;

   ConvertAutos (K, theta, theta_inv, G, ~Auts`Autos);
   ConvertAutos (K, theta, theta_inv, G, ~Auts`pAutos);

   Auts`K := G;

   return Auts;
end function;

/* set up automorphism group and record values of attributes */
SetupAutomorphismGroup := function (Auts)
   G := Auts`K;
   gens := Isetseq(PCGenerators(G));
   nonp := [gens @ alpha`map : alpha in Auts`Autos];
   pautos := [gens @ alpha`map : alpha in Auts`pAutos];
   inner := InnerAutomorphisms (G);

   A := AutomorphismGroup (G, gens, nonp cat pautos cat inner);
   A`OuterOrder := Auts`Order;
   A`Order := Auts`Order * Floor(#G / #Centre (G));;
   A`InnerGenerators := [A | A.i: i in [1 + #nonp + #pautos..Ngens (A)]];
   A`Group := G;
   if #nonp eq 0 then A`Soluble := true; end if;
   return A;
end function;

/* compute the automorphism group of G;
   Chars is a list of known characteristic subgroups of G */
intrinsic AutomorphismGroupPGroup (G:: GrpPC : CharacteristicSubgroups := [])
    -> GrpAuto
{Compute the automorphism group of G; CharacteristicSubgroups is a sequence
 of known characteristic subgroups of G}

   require IsPrimePower (#G): "Argument must be group of prime-power order";

   if assigned G`Automorphisms then
      return SetupAutomorphismGroup (G`Automorphisms);
   end if;

   p, d := DefiningParameters (G);

   class := pClass (G);
   if class eq 1 then
      H, theta := pQuotient (G, p, 1);
      A := GL (d, p);
      A := SetupMaps (H, [A.i : i in [1..Ngens (A)]], [], OrderGL(d, p));
      A := ConvertAutomorphisms (G, A, theta);
      G`Automorphisms := A;
      return SetupAutomorphismGroup (A);
   end if;

   /* various pieces of the code assume that the pc-presentation
      has the properties that a pcp constructed by pQuotient has;
      in particular that successive pc-generators span sucessive
      subgroups of the lower p-central series;
      hence we construct such a presentation for the input group */
   I := G;
   G, gamma := pQuotient (I, p, pClass (G));

   C := [gamma (x): x in CharacteristicSubgroups];
   C := CharSpaces (G : Known := C);
   vprint AutomorphismGroup: "Number of characteristic spaces found is ", #C;
   D := {x[1] : x in C | x[2] eq 1};
   B, Pgp, order := MyStabiliserOfSpaces (D);
   Pgp := BaseForMatrixGroup (Pgp);

   vprint AutomorphismGroup:
        "Order after CharSpaces is ", Factorisation (order);
   vprint AutomorphismGroup:
        "Unipotent group after CharSpaces has order ", <p,#Pgp>;
   vprint AutomorphismGroup:
        "Construct automorphism group for class 2 quotient";
   Auts, C, theta := ProcessClass (G, [], 2:
                                   Data := <B, Pgp, order>, Chars := C);
   i := 3;
   while i le class and #Auts`K lt #G do
      vprint AutomorphismGroup:
          "\nConstruct automorphism group for class ", i," quotient";
      Auts, C, theta := ProcessClass (G, Auts, i: Chars := C);
      i := pClass (Auts`K) + 1;
   end while;

   delete Auts`PQ;

   /* compute map from I to Auts`K */
   delta := gamma * theta;
   Auts := ConvertAutomorphisms (I, Auts, delta);

   I`Automorphisms := Auts;

   return SetupAutomorphismGroup (Auts);

end intrinsic;

intrinsic AutomorphismGroupPGroup2 (G:: GrpPC, C:: SeqEnum) -> GrpAuto
{Compute the automorphism group of G; C is a sequence of known
 characteristic subgroups of G}

   return AutomorphismGroupPGroup (G: CharacteristicSubgroups := C);

end intrinsic;
