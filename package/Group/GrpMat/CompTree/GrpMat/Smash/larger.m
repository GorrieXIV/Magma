freeze;

/* random sequence of length n in the integers [0..q - 1] */

RandomCombinations := function (q, n)

   return [Random([0..q - 1]) : i in [1..n]];

end function;

/* return the e x e blocks of g */

MatrixBlocks := function (g, e) 

   F := BaseRing (Parent (g));
   d := Nrows (g);
   g := MatrixAlgebra (F, d) ! g;
   MA := MatrixAlgebra (F, e);
   B := []; 
   for i in [1..d div e] do
      for j in [1..d div e] do
         Append (~B, 
            MA ! ExtractBlock (g, e * (i - 1) + 1, e * (j - 1) + 1, e, e));
      end for;
   end for;
   return B;

end function;

/* choose an isomorphism C --> C^q */

SelectIsomorphism := function (G, t, e)

   NmrTries := 20; NmrElements := 100; 

   PG := RandomProcess (G);
   count2 := 0; 
   repeat 
      count2 +:= 1;
      g := Random (PG);
      g := t * g * t^-1;
 
      B := MatrixBlocks (g, e); n := #B;
      P := Parent (Rep (B));
      F := BaseRing (P); q := #F;

      count := 0; found := false;
      repeat
         b := RandomCombinations (q, n);
         C := &+[b[i] * B[i]: i in [1..n]];
         f := CharacteristicPolynomial (C);
         found := IsIrreducible (f);
         count +:= 1;
      until found or count eq NmrTries;
   until found or count2 eq NmrElements;

   if found eq false then error "error in SelectIsomorphism"; end if;

   // "C is ", C; "f is ", f;

   /* write f over the larger field */
   f := PolynomialAlgebra (GF(q^e)) ! f;

   /* some root of f */
   alpha := Roots (f)[1][1];
   // "alpha is ", alpha;

   return C, alpha;

end function;

/* rewrite matrix g given as element of GL (d, 	q) 
   as element of GL(d / e, q^e) */

RewriteOverLargerField := function (g, C, alpha, e)

   B := MatrixBlocks (g, e);

   P := Parent (Rep (B));
   F := BaseRing (P);
   d := Nrows (g);
   q := #F;

   VC := [Eltseq (C^i) : i in [0..e - 1]];
   KA := KMatrixSpace (F, #VC, #VC[1]);
   A := KA!&cat (VC);
   // "A is ", A;

   Alpha := [];
   VB := [Eltseq (B[i]) : i in [1..#B]];

   KB := VectorSpace (F, #VB[1]);
   // "KB is ", KB;
   Coeffs := [];
   for j in [1..#VB] do
      IsSoln, Coeffs := IsConsistent (A, KB ! VB[j]);
      if IsSoln eq false then 
         "Error in RewriteOverLargerField"; 
	 return false;
      end if;
      Coeffs := Eltseq (Coeffs);
      Alpha[j] := &+[Coeffs[k] * alpha^(k - 1): k in [1..e]];
   end for;

   return GL (d div e, q^e) ! Alpha;

end function;
   
/* C is the centralising matrix obtained from IsSemiLinear */

RewriteGroupOverLargerField := function (G, C, e)
   J, t := JordanForm (C);
   C, alpha := SelectIsomorphism (G, t, e);
   d := Degree (G); 
   q := #BaseRing (G);

   H := sub < GL (d div e, q^e) | 
            [RewriteOverLargerField (t * G.i * t^-1, C, alpha, e) : 
                       i in [1..Ngens (G)]]> ; 
   return H, C, alpha, t;
end function;

KernelOfHom := function (G, e, Auto)
   
   q := #BaseRing (G); 

   /* explicit homomorphism from G to cyclic group of order e */
   image := [];
   for i in [1..Ngens (G)] do
      if exists (j) {j : j in [0..e - 1] | q^j - Auto[i] mod q^e eq 0} then 
         image[i] := j;
      end if;
   end for;

   E := CyclicGroup (GrpAb, e);
   // phi := hom < G -> E | image >;

   phi := [E!image[i] : i in [1..#image]];
   n, a := XGCD (image cat [e]);

   g := &*[G.i^a[i] : i in [1..Ngens (G)]];

   /* generators of kernel as normal subgroup */
   H := sub < G | [G.i * g^(-image[i] div n) : i in [1..Ngens(G)]]>;

   /* add in conjugates to generate kernel as subgroup */
   K := sub < G | g^(e div n), 
                [H.i^(g^u) : i in [1..Ngens (H)], u in [0..e - 1]]>;
   return K, phi, E;

end function;

/* G is defined over K; we have proved that G is semilinear; 
   process the output of IsSemiLinear -- e is degree of the 
   extension field of K over which G is semilinear; 

   construct kernel of the homomorphism into the Galois group of 
   extension field over K; this kernel centralises the matrix 
   CentralisingMatrix (G); 

   return the kernel, which is absolutely reducible over the 
   larger field, the cyclic group E of order e, and a list of 
   the images of the generators of G in E */

intrinsic WriteOverLargerField (G::GrpMat) -> GrpMat, GrpAb, SeqEnum
{Return kernel for homomorphism of semilinear G into cyclic group C
 over base field; also return the cyclic group C and list of 
 images in C of generators of G}

   if not (IsSemiLinear (G) cmpeq true and
       IsAbsolutelyIrreducible(G) cmpeq true)
   then 
      error "G must both absolutely irreducible and semilinear";
   end if;

   e := DegreeOfFieldExtension (G); 
   C := CentralisingMatrix (G);
   Autos := FrobeniusAutomorphisms (G); 
   K, phi, E := KernelOfHom (G, e, Autos);
   return K, E, phi;

end intrinsic;
