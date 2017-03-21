freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: complements.m
   DESC: complements, i.e., Poincare Reducibility thm

   Creation: 06/16/03 -- initial creation

   2004-10-24 (WAS) -- changed modular degree function to be much simpler, and
                       compute what it claims to compute (instead of something
                       that usually is correct.)
      
 ***************************************************************************/

/*
HANDBOOK_TITLE: Orthogonal Complements
*/

import "endo_alg.m":
   Basis_for_EndomorphismMatrixAlgebra_of_SimpleAbVar;

import "homology.m":
   AllModularSymbolsSpacesAreFull,
   Create_ModAbVarHomol_Subspace,
   RationalIntersectionPairing;

import "linalg.m":
   MatrixFromColumns,
   MatrixFromRows;

import "modabvar.m":
   Create_ModAbVar, 
   Verbose;

import "morphisms.m":
   Create_MapModAbVar,
   Create_MapModAbVar_MultiplyToMorphism,
   Create_MapModAbVar_PossiblyUpToIsogeny;

import "rings.m":
   QQ,
   CommonBaseRing;

forward
   CanUseIntersectionPairing,
   ComplementsAreGuaranteedOrthogonal,
   Compute_ModularDegree,
   FindHomologyComplementUsingDecomposition,
   FindHomologyComplementUsingIntersectionPairing,
   FindHomologyDecompositionOfSubspaceUsingDecomposition,
   HomologyComplementOfImage;

// If you change the following to true, also change the default
// in the two funcitons Complement and ComplementOfImage below.
USE_INT_PAIRING_BY_DEFAULT := false;   

function ComplementsAreGuaranteedOrthogonal(A)

   assert Type(A) eq ModAbVar;
   if assigned A`only_maximal_newform_blocks and A`only_maximal_newform_blocks then
      return true;
   end if;
   if USE_INT_PAIRING_BY_DEFAULT and
           CanUseIntersectionPairing(Homology(Domain(ModularParameterization(A)))) then
      return true;
   end if;
   return false;
end function;

function CanUseIntersectionPairing(H)
   assert Type(H) eq ModAbVarHomol;
   assert assigned H`modsym;
   for M in H`modsym do
      if not IsTrivial(DirichletCharacter(M)) or Weight(M) ne 2 then 
         return false; 
      end if;
   end for;
   return true;
end function;


/***************************************************************************

  << Complements >>

 ***************************************************************************/

intrinsic Complement(A::ModAbVar : IntPairing  := false) 
       -> ModAbVar, MapModAbVar
{The complement of the image of A under the first embedding of A
(the first map in the sequence Embeddings(A)).}
   return ComplementOfImage(Embeddings(A)[1] : IntPairing := IntPairing);
end intrinsic;



intrinsic ComplementOfImage(phi::MapModAbVar : IntPairing := false)  
       -> ModAbVar, MapModAbVar
{Given a morphism phi:A->B of abelian varieties, return an abelian variety C
such that phi(A) + C = B and such that phi(A) meet C is finite};
   Verbose("ComplementOfImage", Sprintf("Computing the complement of the image of %o", phi),"");
   if IntPairing then
      require CanUseIntersectionPairing(Homology(Codomain(ModularEmbedding(Codomain(phi))))):
       "Optional parameter IntPairing set but no algorithm currently implemented "*
       "to compute intersection pairing in this generality.";
   end if;

   A := Domain(phi);
   B := Codomain(phi);
   HB := Homology(B);
   e := ModularEmbedding(B);
   e_mat := Matrix(e);
   V := Image(e_mat);
   Je := Codomain(e);

   Wcomp := HomologyComplementOfImage(phi, IntPairing);
   Cvs := Wcomp meet V;

   // Now pull basis of Cvs back to B using e.  The result
   // is a basis for H_1(C,Q) embedded in H_1(B,Q).
   C_basis := [Solution(e_mat,b) : b in Basis(Cvs)];
   if #C_basis eq 0 then
      C := ZeroSubvariety(Codomain(phi));
      return C, Hom(C,Codomain(phi))!0;
   end if;
   C_to_B := RMatrixSpace(QQ, Dimension(Cvs), Dimension(HB))!C_basis;
   C_in_B := VectorSpaceWithBasis(C_basis);
   HC, embed_matrix := Create_ModAbVarHomol_Subspace(HB, C_in_B);

   // rational homology matrix of projection from B onto C:
   Ccomp_basis := Basis(Image(Matrix(phi)));
   XCCcomp  := MatrixAlgebra(QQ,Dimension(HB))!(C_basis cat Ccomp_basis);
   to_CCcomp := XCCcomp^(-1);
   // take only the first #C_basis columns of to_CCcomp, in order to get
   // a matrix that defines map to C wrt to Basis(C).
   to_CCcomp := Transpose(to_CCcomp);
   B_to_C := Transpose(RMatrixSpace(QQ,#C_basis,Dimension(HB))![to_CCcomp[i] : i in [1..#C_basis]]);

   name := "";
   K := FieldOfDefinition(phi);
   R := CommonBaseRing([Domain(phi),Codomain(phi)]);

   // Compute modular parameterization data.
   C_to_Je := C_to_B*e_mat;   
   Jp_to_B := ModularParameterization(B);
   Jp := Domain(Jp_to_B);   // Note: Je = Jp, by definition of data for B.
   Jp_to_C := Matrix(Jp_to_B) * B_to_C;
   J := <Je, C_to_Je, Jp_to_C>;

   // Finally make C.
   C := Create_ModAbVar(name, HC, K, R, J);
   C_to_B_morphism := Create_MapModAbVar(C, B, C_to_B, K);
   AssertEmbedding(~C,C_to_B_morphism);
   return C, C_to_B_morphism;
end intrinsic;

/***************************************************************************

  << Dual Abelian Variety >>

 ***************************************************************************/

intrinsic ModularPolarization(A::ModAbVar) -> MapModAbVar
{The polarization on A induced by pullback of the theta divisor.}
   t, dual := IsDualComputable(A);
   require t : dual;
   return NaturalMap(A,dual);
end intrinsic;

// TODO: The algorithms for computing dual could be greatly refined */

intrinsic IsDualComputable(A::ModAbVar) -> BoolElt, ModAbVar
{True if know how to compute the dual of A, and the dual.}
   Verbose("IsDualComputable", Sprintf("Attempting to compute the dual of A=%o",A),"");
   if assigned A`is_selfdual and A`is_selfdual then
      return true, A;
   end if;
   if Dimension(A) le 1 then
      return true, A;
   end if;
   e := ModularEmbedding(A);
   if not IsInjective(e) then
      return false, "The modular embedding of argument 1 must be injective.";
   end if;
   if not AllModularSymbolsSpacesAreFull(Homology(Codomain(ModularEmbedding(A)))) then
      return false, "Algorithm to compute dual not programmed in this case. (The "*
         " problem is that one of the modular symbols spaces used to define argument "*
         " is not the full cuspidal subspace.";
   end if;
   e := ModularEmbedding(A); 
   J := Codomain(e);
   // TODO: Better algorithm here. 
   if not assigned J`is_selfdual or not J`is_selfdual then
      return false, "Unable to compute the dual of argument 1.";
   end if;
   if IsIsomorphism(e) then
      return true, A;
   end if;
   if not IsInjective(e) then
      return false, "The modular embedding must be injective.";
   end if;
   IntPairing := true;
   if ComplementsAreGuaranteedOrthogonal(A) then
      IntPairing := false;
   end if;
   C, i := ComplementOfImage(e : IntPairing := IntPairing);
   Adual := Codomain(e)/C;
   return true, Adual;
end intrinsic;

intrinsic Dual(A::ModAbVar) -> ModAbVar
{The dual abelian variety of A.}
   t, adual := IsDualComputable(A);
   require t : adual;
   return adual;
end intrinsic;




/***************************************************************************

  << Intersection Pairing >>

 ***************************************************************************/


intrinsic IntersectionPairing(H::ModAbVarHomol) -> AlgMatElt
{The intersection pairing matrix on the basis for the rational homology of H.}
   Verbose("IntersectionPairing", 
     Sprintf("Computing the intersection pairing on the homology %o.", H), "");
   require assigned H`modsym : "Argument 1 must be associated to modular symbols.";
   require CanUseIntersectionPairing(H) : 
    "No algorithm currently implemented for computing intersection pairing in this context.";
   modsym := H`modsym;
   I := IntersectionPairing(modsym[1]);
   for i in [2..#modsym] do 
      I := DirectSum(I, IntersectionPairing(modsym[i]));
   end for;
   return I;   
end intrinsic;

intrinsic IntersectionPairing(A::ModAbVar) -> AlgMatElt
{The intersection pairing matrix on the basis for the rational homology of H, pulled
back using the modular embedding.}
   Verbose("IntersectionPairing", 
     Sprintf("The intersection pairing on the rational homology of A=%o.", A), "");
   if IsAttachedToModularSymbols(A) then
      return IntersectionPairing(Homology(A));
   end if;
   e := ModularEmbedding(A);
   require CanUseIntersectionPairing(Homology(Codomain(e))) : 
    "No algorithm currently implemented for computing intersection pairing in this context.";
   I := IntersectionPairing(Codomain(e));
   M := Matrix(e);
   return M*I*Transpose(M);
end intrinsic;

intrinsic IntersectionPairingIntegral(A::ModAbVar) -> AlgMatElt
{The intersection pairing matrix on the basis for the integral homology of H, 
pulled back using the modular embedding.}
   Verbose("IntersectionPairingIntegral", 
     Sprintf("The intersection pairing on the integral homology of A=%o.", A), "");
   require CanUseIntersectionPairing(Homology(Codomain(ModularEmbedding(A)))) : 
    "No algorithm currently implemented for computing intersection pairing in this context.";
   L := IntegralHomology(A);
   M := RMatrixSpace(QQ,Dimension(L),Dimension(L))!&cat[Eltseq(b) : b in Basis(L)];
   return M*IntersectionPairing(A)*Transpose(M);
end intrinsic;


/***************************************************************************

  << Projections >>

 ***************************************************************************/

intrinsic ProjectionOnto(A::ModAbVar : IntPairing := false) -> MapModAbVar
{The projection map from A to the first of its 'Embeddings'.}
   return ProjectionOntoImage(Embeddings(A)[1] : IntPairing := IntPairing);
end intrinsic;

intrinsic ProjectionOntoImage(phi::MapModAbVar : IntPairing := false) -> MapModAbVar
{Given a morphism phi: A -> B, return a projection onto phi(A) as 
an element of the endomorphism ring tensor Q.}
   Verbose("ProjectionOntoImage", 
     Sprintf("Computing projection morphism onto image of phi=%o",phi), "");
   if IntPairing then
      require CanUseIntersectionPairing(Homology(Codomain(ModularEmbedding(Codomain(phi))))):
       "Optional parameter IntPairing set but no algorithm currently implemented "*
       "to compute intersection pairing in this generality.";
   end if;
    
   B := Codomain(phi);
   W := HomologyComplementOfImage(phi, IntPairing);
   W_basis := Basis(W);
   C := Image(Matrix(phi));  // C = phi(A).
   C_basis := Basis(C);
   n := Dimension(Homology(B));
   C_mat  := MatrixAlgebra(QQ,n)!(C_basis cat W_basis);
   Cinv := C_mat^(-1);
   C_mat  := RMatrixSpace(QQ,#C_basis,n)!C_basis;
   PI := MatrixFromColumns(Cinv,[1..#C_basis])*C_mat;  
   pi := Create_MapModAbVar_PossiblyUpToIsogeny(B, B, PI, FieldOfDefinition(phi));
   pi`name := "pi";
   return pi;
end intrinsic;


/***************************************************************************

  << Left and Right Inverses >>

 ***************************************************************************/

intrinsic RightInverseMorphism(phi::MapModAbVar : 
     IntPairing := false) -> MapModAbVar
{A minimal-degree homomorphism psi:B --> A such that phi*psi:A --> A is 
 multiplication by an integer, where phi:A --> B is a homomorphism of 
 abelian varieties with finite kernel.}
   Verbose("RightInverseMorphism", 
        Sprintf("Computing an almost-right-inverse morphism to phi=%o.",phi),"");
   require Degree(phi) ne 0 : "Argument 1 must have finite kernel.";
   psi, d := RightInverse(phi  : IntPairing := IntPairing);
   f := d*psi;
   assert IsInteger(phi*psi);
   delete f`only_up_to_isogeny;
   return f;

end intrinsic;

intrinsic RightInverse(phi::MapModAbVar : IntPairing := false) -> 
   MapModAbVar, RngIntElt
 {A map psi:B --> A in the category of abelian varieties
 up to isogeny such that phi*psi:A --> A is the identity map.  
 Here phi:A --> B is a homomorphism of abelian varieties with finite kernel.}
   Verbose("RightInverse", 
        Sprintf("Computing a right inverse to phi=%o.",phi),"");

   A := Domain(phi);
   B := Codomain(phi);
   if IsIsogeny(phi) then
      return Create_MapModAbVar_PossiblyUpToIsogeny(
         B,A,Matrix(phi)^(-1),FieldOfDefinition(phi));
   end if;

   require Degree(phi) ne 0 : "Argument 1 must have finite kernel.";

   /* ALGORITHM: Compute projection matrix from H_1(B,Q) 
      to H_1(phi(A),Q).
      Since phi is injective on homology, this will in 
      fact define a map from H_1(B,Q) to H_1(A,Q) that
      is a section to phi.  
    */
   C, C_to_B := ComplementOfImage(phi : IntPairing := IntPairing);   
   phiA_basis := Rows(phi);
   comp_basis := Rows(C_to_B);
   X := MatrixAlgebra(QQ, Dimension(Homology(B)))!(phiA_basis cat comp_basis);
   Y := X^(-1);
   B_to_A := MatrixFromColumns(Y,[1..#phiA_basis]);
   K := FieldOfDefinition(phi);

   return Create_MapModAbVar_PossiblyUpToIsogeny(B, A, B_to_A, K);
end intrinsic;


intrinsic LeftInverseMorphism(phi::MapModAbVar : IntPairing := false) 
   -> MapModAbVar
{A homomorphism psi:B --> A of minimal degree such that psi*phi is multiplication 
by an integer, where phi:A --> B is a surjective homomorphism.}
   Verbose("LeftInverseMorphism", 
        Sprintf("Computing an almost-left-inverse morphism to phi=%o.",phi),"");

   require IsSurjective(phi) : "Argument 1 must be surjective.";
   psi, d := LeftInverse(phi : IntPairing := IntPairing);
   f := d*psi;
   delete f`only_up_to_isogeny;
   return f;
end intrinsic;

intrinsic LeftInverse(phi::MapModAbVar : IntPairing := false)
   -> MapModAbVar, RngIntElt
{A homomorphism psi:B --> A of minimal degree in the category of abelian
varieties up to isogeny such that psi*phi is the identity map on B. Here
phi:A --> B is a surjective homomorphism.}
   Verbose("RightInverse", 
        Sprintf("Computing a left inverse to phi=%o.",phi),"");
   B, i := ConnectedKernel(phi);
   C, j := ComplementOfImage(i : IntPairing := IntPairing);
   h := j*phi;  // this is an isogeny from C to Codomain(phi), so has an inverse.
   hinv, d := Inverse(h);    // this goes from Codomain(phi) to C.
                             // composing with C --> Domain(phi), gives answer.
   return hinv*j, d;
end intrinsic;


/***************************************************************************

  << Congruence Computations >>


 ***************************************************************************/

intrinsic CongruenceModulus(A::ModAbVar) -> RngIntElt
{If A is attached to a newform, this returns the congruence
modulus of the newform};
   t, Af := IsAttachedToNewform(A);
   require t : "Argument 1 must be attached to a newform.";
   return CongruenceModulus(ModularSymbols(Af)[1]);
end intrinsic;


intrinsic ModularDegree(A::ModAbVar) -> RngIntElt
{The modular degree of A, which is the square root of the 
 degree of ModularPolarization(A).}
   if not assigned A`modular_degree then 
      d := Degree(ModularPolarization(A)); 
      if Sign(A) eq 0 and Weights(A) eq {2} then 
         t, s := IsSquare(d); 
         if not t then 
            error "Bug in ModularDegree"; 
         end if; 
         d := s; 
      end if; 
      A`modular_degree := d; 
   end if; 
   return A`modular_degree; 
end intrinsic;



function FindHomologyComplementUsingIntersectionPairing(H, V)
   Verbose("FindHomologyComplementUsingIntersectionPairing",Sprintf("H=%o, V=%o",H,V),"");
   assert Type(H) eq ModAbVarHomol;
   assert Type(V) eq ModTupFld;  
   assert Degree(V) eq Dimension(H);
   assert assigned H`modsym;
   modsym := H`modsym;
   if not (H`sign eq 0 and &and[IsTrivial(DirichletCharacter(M)) : M in modsym]) then
      return false;
   end if;
   BV := RMatrixSpace(QQ,Dimension(V),Degree(V))!Basis(V);
   I := IntersectionPairing(H);
   return Kernel(I*Transpose(BV));
end function;

function FindHomologyComplementUsingDecomposition(J, V)
   Verbose("FindHomologyComplementUsingDecomposition",Sprintf("J=%o, V=%o",J,V),"");
/* V is a subspace of the rational homology of the modular symbols
   modular abelian variety J.   We assume that V DOES arises
   from an abelian variety.  This complement is *not* canonical.  */
   assert Type(J) eq ModAbVar;
   assert Type(V) eq ModTupFld;
   /* Algorithm: 
       We wish to compute a complement of V in the rational homology of J
       using complete information about simple abelian subvarieties of J, 
       gathered together by isogeny class.   Let a "cluster" C be a maximal 
       collection of images in the rational homology of J of mutually 
       isogenous abelian varieties whose product injects into J.   
       A "cluster image" is a homomorphic image of C in J, so then 
       a cluster image is determined by an nxn matrix, where n=#C.

       (1) Compute a complete collection of clusters.

       (2) For each cluster C:
               If the intersection is nonzero, we must find a cluster 
               image X such that (V meet &+C) + X = &+C and 
               V meet X = 0.  The following algorithm must work
               because V is assumed attached to an abelian variety,
               so for any C[i] either V meet C[i] = 0 or V 
               contains C[i], since C[i] corresponds to a simple 
               abelian variety.   Here's the algorithm:
                    Let X = 0.
                    For each i = 1, ..., #C, if X+C[i]
                    intersects trivially with V replace
                    X by X + C[i]; otherwise, do nothing.

               Proof:  After performing the algorithm we have
               X.  Let S = X + V.   Each C[i] that we didn't 
               include in X must intersect nontrivially with S,
               since already X+C[i] intersects nontrivially 
               with V and X doesn't intersect with V.   
               Since S corresponds to an abelian variety, each 
               C[i] must be contained in S.  Thus S = &+C, 
               as required.
   */

   Z := RationalHomology(J);
   assert V subset Z;

   W := sub<Z|Z!0>;
   data := [];
   for D in Factorization(J) do
      C := [Image(Matrix(phi)) : phi in D[2]];
      S := &+C;
      /*
      // TO DO: The following is probably a better way to get S (not checked or tested though!)
      // If we know that the 'domain' of Matrix(phi) is always the whole space,
      // then we could even use RowSpace instead of Image
      if #C eq 1 then 
         S := C[1];
      else
         BigM := VerticalJoin([ Matrix(phi) : phi in D[2] ]);
         S_new := Image(BigM);
         assert S eq S_new; 
      end if;
      */
      VS := V meet S;
      assert Dimension(VS) mod Dimension(C[1]) eq 0;  
      if Dimension(VS) eq 0 then
         W := W + S;
         Append(~data, [1..#C]);
      else
         r := Dimension(S) - Dimension(VS);
         X := sub<Z|Z!0>;
         dataC := [];
         for i in [1..#C] do 
            XC := X+C[i];
            if Dimension((XC) meet V) eq 0 then
               X := XC;
               Append(~dataC,i);
            end if;
         end for;
         W := W+X;
         Append(~data, dataC);
      end if;
   end for;
   return W, data;
end function;

function HomologyComplementOfImage(phi, IntPairing)
   Verbose("HomologyComplementOfImage", Sprintf("phi=%o",phi),"");
   A := Domain(phi);
   B := Codomain(phi);
   HB := Homology(B);
   e := ModularEmbedding(B);
   e_mat := Matrix(e);
   Je := Codomain(e);
   HJ := Homology(Je); 
   W := Image(Matrix(phi)*e_mat);
   V := Image(e_mat);

   if IntPairing and CanUseIntersectionPairing(Homology(Je)) then
      Wcomp := FindHomologyComplementUsingIntersectionPairing(Homology(Je), W);
   else
      Wcomp := FindHomologyComplementUsingDecomposition(Je, W);
   end if;
   return Wcomp;
end function;

function FindHomologyDecompositionOfSubspaceUsingDecomposition(J, V)
   Verbose("FindHomologyDecompositionOfSubspaceUsingDecomposition", 
            Sprintf("J=%o, V=%o", J, V),"");
/* V is a subspace of the rational homology of the modular symbols
   modular abelian variety J.   This function either
     (1) Prove that V in fact does not correspond to an abelian 
         subvariety of J (and returns empty list), or
     (2) Provides an explicit representation of V as a direct sum of 
         subspace corresponding to isogeny simple subvarieties of J
         (and returns the list of those subvarieties along with embeddings).
   It also returns true if only maximal newform orbits are contained in V, i.e., 
   if A_f is contained in V then as large a space of A_f's is in V as possible,
   so, e.g., the general non-intersection pairing complement algorithm in 
   this file is guaranteed to give orthogonal complements.
*/
   assert Type(J) eq ModAbVar;
   assert Type(V) eq ModTupFld;

   /* Algorithm: 
       We wish to decompose V using complete information about 
       simple abelian subvarieties of J, gathered together by 
       isogeny class.   Let a "cluster" be the rational homology 
       of a simple abelian variety C and a collection of injective maps
       phi_i from H(C) to the rational homology H(J), such that the
       images of the phi_i are linearly disjoint and they are maximal 
       in that their sum corresponds to an abelian variety D that 
       shares no isogeny component with J/D.  Let psi_j be a basis for
       the endomorphism algebra of C.  Let {fi} be the set of all 
       products psi_j*phi_i.   It is easy to see that every map 
       from H(C) into H(J) that is induced by a morphism of abelian 
       varieties is a Q-linear combination of the fi. 

       Assume V is a subspace of H(J) coming from an abelian variety A.
       Then V is isomorphic to a direct sum of images of C and the maps
       from C to these factors are induced by abelian variety morphisms,
       so they are Q-linear combinations of the fi defined above.  Our
       goal is to find these Q-linear combinations.

       (1) Compute a complete collection of clusters.

       (2) For each cluster:
               (a) Let v be a nonzero element of H(C).
               (b) Compute f1(v),...,fr(v) for r the number of maps.
               (c) Let W be the subspace of H(J) generated by the fi(v).  
                   (The subspace W may or may not be maximal, depending
                    on how big the endomorphism ring of C is.  Never maximal
                    if base field is Q -- then always have the full dimension.)
               (d) Find a basis for the intersection of V and W.
               (e) Write each element vj of this basis in terms of the fi(v).
               (f) If vj = sum ai*fi(v), then vj is in (sum ai*fi)(C).
                   If V really does correspond to an abelian variety, then
                   since C corresponds to a simple abelian variety, we must
                   have that (sum ai*fi)(C) is contained in V.
               (g) Using each vj, we find a list of homomorphisms 
                              phi_j = sum aij*fi
                   such that the images of the phi_j either
                        * provide a direct sum decomposition of V, or
                        * aren't equal to V -- in which case V does not
                          correspond to an abelian variety.
            
       (3) Question: Can we get the abelian variety *generated by V* using
                     a process like the one above?   The abelian variety generated
                     by V is by definition the smallest vector subspace of H(J)
                     that contains V and corresponds to an abelian variety.
                     
   */
   HJ := RationalHomology(J);
   assert V subset HJ;
   DV := [* *];    // abelian varieties corresponding to decomposition of V.
   ZZ := sub<V|0>;
   full_only := true;
   SUM := ZeroSubvariety(J);
   for D in Factorization(J) do
      EndC := Basis_for_EndomorphismMatrixAlgebra_of_SimpleAbVar(D[1]);
      F  := [psi*Matrix(phi) : phi in D[2], psi in EndC];
      C  := RationalHomology(D[1]);
      v  := C.1;
      fv := [v*f : f in F];
      W  := VectorSpaceWithBasis(fv);
      VW := V meet W;
      B  := [Coordinates(W, b) : b in Basis(VW)];
      PHI := [];
      Z := sub<V|V!0>;
      for x in B do 
         Phi := &+[x[i]*Matrix(F[i]) : i in [1..#x]];
         ImPhi := Image(Phi);
         if not (ImPhi subset Z) then
            Z := Z + ImPhi;
            Append(~PHI, Phi);
         end if;
      end for;
      ZZ +:= Z;
      if not (ZZ subset V) then
         return [* *], true;  // not an abelian variety!!
      end if;
      Verbose("FindHomologyDecompositionOfSubspaceUsingDecomposition","", 
        Sprintf("Found dimension %o subspace of dimension %o space so far.",
                  Dimension(ZZ),Dimension(V)));
      if #PHI ne 0 then
         Append(~DV, <D[1], PHI>);
         if #PHI ne #D[2] then
            full_only := false;
         end if;
         for phi in PHI do 
            psi := Hom(D[1],J, true)!phi;
            SUM := SUM + Image(ClearDenominator(psi));
         end for;
      end if;
   end for;
   if ZZ ne V then
      return [* *], ZeroSubvariety(J), false;
   end if;
   return DV, SUM, full_only;
end function;




