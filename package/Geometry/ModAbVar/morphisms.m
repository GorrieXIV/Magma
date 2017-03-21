freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: homs.m
   DESC: Basic MapModAbVar functionality.

   

 ***************************************************************************/

/* 
  HANDBOOK_TITLE: Homomorphisms 

*/


import "homology.m": 
   BasisChange_Lattice_to_Rational,
   BasisChange_Rational_to_Lattice,
   Create_ModAbVarHomol,
   Create_ModAbVarHomol_Quotient,
   Create_ModAbVarHomol_Subspace,
   HomologyDimension;

import "linalg.m": 
   EvaluatePolynomial,
   IsMatrix,
   MakeLattice,
   RestrictMatrix,
   RestrictMatrixDomain;

import "modabvar.m": 
   Create_ModAbVar,
   ShortDesc, 
   Verbose;

import "rings.m": 
   QQ, RR, ZZ,
   CommonBaseRing,
   CommonFieldOfDefinition,
   IsDefnField,
   OverRing;

forward 
   Copy_MapModAbVar,
   Create_MapModAbVar,
   Create_MapModAbVar_MultiplyToMorphism,
   Create_MapModAbVar_Name,
   Create_MapModAbVar_PossiblyUpToIsogeny,
   KernelOfIsogeny,
   MatrixOnLattices,
   Name,
   SetName;


declare type MapModAbVar;

declare attributes MapModAbVar:
   domain,
   codomain,
   matrix, 
   field_of_definition,
   degree,
   name,

   is_isogeny,
   has_finite_kernel,
   hecke_operator,  // if this is the hecke operator Tn, then this attribute is set to n.
                    // used to make computation of, e.g., charpolys more efficient.
   charpoly,   // characteristic polynomial
   minpoly,    // minimal polynomial
   factored_charpoly, // factorization of characteristic polynomial
   parent,
   denominator,
   only_up_to_isogeny;  // true if this morphism is only 
                   // a morphism in ab vars up to isogeny.

function Create_MapModAbVar(domain, codomain, matrix, field)
   assert Type(domain) eq ModAbVar;
   assert Type(codomain) eq ModAbVar;
   assert Type(matrix) in {ModMatFldElt, AlgMatElt};
   assert IsDefnField(field);

   if BaseRing(domain) ne BaseRing(codomain) then
      print "BUG - these should be equal:";
      print "domain = ", domain;
      print "codomain = ", codomain;
   end if;
   assert BaseRing(domain) cmpeq BaseRing(codomain);

   assert Nrows(matrix) eq Dimension(Homology(domain));
   assert Ncols(matrix) eq Dimension(Homology(codomain));
   phi := New(MapModAbVar);
   phi`domain   := domain;
   phi`codomain := codomain;
   phi`matrix   := matrix;
   assert IsField(field);
   phi`field_of_definition    := field;
   phi`name := "";  // default -- rarely used.
   phi`parent := Hom(domain, codomain);
   return phi;
end function;

function Copy_MapModAbVar(f)
   assert Type(f) eq MapModAbVar;
   g := New(MapModAbVar);
   if assigned f`domain then g`domain := f`domain; end if;
   if assigned f`codomain then g`codomain := f`codomain; end if;
   if assigned f`matrix then g`matrix := f`matrix; end if;
   if assigned f`field_of_definition then g`field_of_definition := f`field_of_definition; end if;
   if assigned f`degree then g`degree := f`degree; end if;
   if assigned f`name then g`name := f`name; end if;
   if assigned f`is_isogeny then g`is_isogeny := f`is_isogeny; end if;
   if assigned f`has_finite_kernel then g`has_finite_kernel := f`has_finite_kernel; end if;
   if assigned f`hecke_operator then g`hecke_operator := f`hecke_operator; end if;
   if assigned f`parent then g`parent := f`parent; end if;
   if assigned f`only_up_to_isogeny then g`only_up_to_isogeny := f`only_up_to_isogeny; end if;      
   return g;   
end function;



function Create_MapModAbVar_Name(domain, codomain, matrix, field, name)
   assert Type(domain) eq ModAbVar;
   assert Type(codomain) eq ModAbVar;
   assert Type(matrix) in {ModMatFldElt, AlgMatElt};
   assert IsDefnField(field);
   assert Type(name) eq MonStgElt;
   assert Nrows(matrix) eq Dimension(Homology(domain));
   assert Ncols(matrix) eq Dimension(Homology(codomain));
   phi := Create_MapModAbVar(domain, codomain, matrix, field);
   SetName(phi,name);
   return phi;
end function;

function Create_MapModAbVar_MultiplyToMorphism(domain, codomain, matrix, field)
   // This is exactly the same as Create_MapModAbVar, except that matrix
   // is not *assumed* to send H_1(A,Z) into H_1(B,Z), where A = domain, B = codomain.
   // We multiply matrix by the smallest integer d so that H_1(A,Z) is sent
   // into H_1(B,Z) by d*matrix.    We do this by finding the matrix of
   // the transformation wrt to bases for H_1(*,Z) and finding the LCM of the
   // denominators of this matrix.
   assert Type(domain) eq ModAbVar;
   assert Type(codomain) eq ModAbVar;
   assert Type(matrix) in {ModMatFldElt, AlgMatElt};
   assert Nrows(matrix) eq Dimension(Homology(domain));
   assert Ncols(matrix) eq Dimension(Homology(codomain));
   assert IsDefnField(field);
   
   HA := Homology(domain);
   HB := Homology(codomain);
   AZ := Lattice(HA);
   BZ := Lattice(HB);
   V := VectorSpace(HA);
   mat := MatrixOnLattices(HA, HB, matrix);
   d := LCM([ZZ|Denominator(x) : x in Eltseq(mat)]);
   phi := Create_MapModAbVar(domain, codomain, d*matrix, field);
   return phi, d;
end function;

function Create_MapModAbVar_PossiblyUpToIsogeny(domain, codomain, matrix, field)
   assert Type(domain) eq ModAbVar;
   assert Type(codomain) eq ModAbVar;
   assert Type(matrix) in {ModMatFldElt, AlgMatElt};
   assert Nrows(matrix) eq Dimension(Homology(domain));
   assert Ncols(matrix) eq Dimension(Homology(codomain));
   assert IsDefnField(field);
   
   phi, d := Create_MapModAbVar_MultiplyToMorphism(domain, codomain, matrix, field);
   phi`only_up_to_isogeny := Matrix(phi) ne matrix;
   if d ne 1 then
      phi`matrix := (1/d)*phi`matrix;
      phi`parent := BaseExtend(Hom(domain,codomain),QQ);
   end if;
   return phi, d;
end function;


function MatrixOnLattices(H1, H2, M)
   // Given a matrix M that defines a map from H1(Q) to H2(Q) in
   // terms of the rational basis, this returns a matrix that defines
   // the same map, but in terms of the basis for Lattice(H1(Q)) and Lattice(H2(Q)).
   // The resulting matrix is OVER Q, not over Z.  This is important because
   // this function is used in normalizing matrices that don't preserve lattice
   // so that they do preserve lattice. 
   assert Type(H1) eq ModAbVarHomol;
   assert Type(H2) eq ModAbVarHomol;
   assert IsMatrix(M);
   assert Nrows(M) eq Dimension(H1);
   assert Ncols(M) eq Dimension(H2);
   Z := BasisChange_Lattice_to_Rational(H1) * M * BasisChange_Rational_to_Lattice(H2);
   return Z;
end function;

/***************************************************************************

  << Creation >>

 ***************************************************************************/

intrinsic nIsogeny(A::ModAbVar, n::RngIntElt) -> MapModAbVar
{The multiplication by n isogeny on A.}
   Verbose("nIsogeny", "", Sprintf("Creating %o-isogeny on %o.", n,A));
   K := FieldOfDefinition(A);
   d := Dimension(RationalHomology(A));
   mat := MatrixAlgebra(QQ,d)!n;
   H := Create_MapModAbVar(A, A, mat, K);
   return H;
end intrinsic;

intrinsic nIsogeny(A::ModAbVar, n::FldRatElt) -> MapModAbVar
{The multiplication by n isogeny on A.}
   Verbose("nIsogeny", Sprintf("Creating %o-isogeny on %o.", n,A),"");
   K := FieldOfDefinition(A);
   d := Dimension(RationalHomology(A));
   mat := MatrixAlgebra(QQ,d)!n;
   H := Create_MapModAbVar(A, A, mat, K);
   return H;
end intrinsic;

intrinsic IdentityMap(A::ModAbVar) -> MapModAbVar
{The identity homomorphism from A to A.}
   return nIsogeny(A,1);
end intrinsic;

intrinsic ZeroMap(A::ModAbVar) -> MapModAbVar
{The zero homomorphism from A to A.}
   return nIsogeny(A,0);
end intrinsic;



/***************************************************************************

  << Restriction, Evaluation, and Other Manipulations >>

 ***************************************************************************/

intrinsic Evaluate(f::RngUPolElt, phi::MapModAbVar) -> MapModAbVar
{The endomorphism f(phi) of A, where f is a univariant polynomial
and phi is an endomorphism of a modular abelian variety A.}
   require Domain(phi) eq Codomain(phi) : "Argument 1 must be an endomorphism.";
   require Type(BaseRing(Parent(f))) in {FldRat, RngInt} : 
     "Argument 1 must a polynomial over the integer ring or rational field.";
   Verbose("Evaluate", Sprintf("Computing f(phi), where f=%o and phi=%o",
            f,phi),"");
   mat := Matrix(phi);
   mat := MatrixAlgebra(QQ,Nrows(mat))!mat;
   matrix := EvaluatePolynomial(f,mat);
   return Create_MapModAbVar(Domain(phi),Codomain(phi),matrix,FieldOfDefinition(phi));   
end intrinsic;

intrinsic DivideOutIntegers(phi::MapModAbVar) -> MapModAbVar, RngIntElt
{If phi:A \to B is a homomorphism of abelian varieties, find the largest integer n
such that psi=(1/n)*phi is also a homomorphism from A to B and return psi and n.}
   Verbose("DivideOutIntegers", "",
        Sprintf("Computing n such that n*phi is a homomorphism, where phi=%o.",phi));
   M := IntegralMatrix(phi);
   if IsZero(M) then
      return phi, 1;
   end if;
   n := GCD(Eltseq(M));
   if n eq 1 then
      return phi, 1;
   end if;
   return (1/n)*phi, n;
end intrinsic;

intrinsic SurjectivePart(phi::MapModAbVar) -> MapModAbVar
{Given a homomorphism phi:A\to B of abelian varieties
return the surjective homomorphism pi:A-> phi(A) induced by phi.}
   require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";
   C, _, pi := Image(phi);
   return pi;
end intrinsic;

function CanRestrictEndomorphism(phi, i)
   Verbose("CanRestrictEndomorphism", 
            Sprintf("Trying to restricting phi to image of i:%o->%o, where phi=%o.", 
            Domain(i), Codomain(i), phi), "");

   if not IsMorphism(phi) then 
      return false, "Argument 1 must be a morphism of abelian varieties.";
   end if;
   if not IsEndomorphism(phi) then
      return false, "Argument 1 must be an endomorphism.";
   end if;
  
   V := RationalHomology(Codomain(i));
   W := Image(Matrix(i));
   matrix := RestrictMatrix(Matrix(phi), W);
   if Type(matrix) eq BoolElt then
      return false,
       "Argument 1 does not leave the image of argument 2 invariant, so the "*
       "restriction is not defined.";
   end if;

   K := CommonFieldOfDefinition([* i, phi *]);
   return true, Create_MapModAbVar(Domain(i), Domain(i), matrix, K);
end function;

intrinsic RestrictEndomorphism(phi::MapModAbVar, A::ModAbVar) -> MapModAbVar
{The restriction of phi to an endomorphism of A, if this obviously makes sense.}
   require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";
   require IsEndomorphism(phi) : "Argument 1 must be an endomorphism.";

   if Domain(phi) eq A then
      return phi;
   end if;
   e := ModularEmbedding(A);
   if Codomain(e) eq Domain(phi) then
      t, x := CanRestrictEndomorphism(phi, e);
      if not t then
         require t : x;
      end if;
      return x;
   end if;

   require false : "Not able to make sense of the restriction.  "*
         "Try calling with the second argument a map.";
end intrinsic;

intrinsic RestrictEndomorphism(phi::MapModAbVar, i::MapModAbVar) -> MapModAbVar
{Given an endomorphism phi of an abelian variety A and i:B
-> A an injective morphism of abelian varieties such that i(B) is
invariant under phi, return the endomorphism psi of
B induced by phi.  }
   t, x := CanRestrictEndomorphism(phi, i);
   if not t then
      require t : x;
   end if;
   return x;
end intrinsic;

intrinsic Restriction(phi::MapModAbVar, A::ModAbVar) -> MapModAbVar
{The restriction of phi to a morphism from A to the codomain of phi. }
   Verbose("Restriction", 
            Sprintf("Restricting phi to A, where phi=%o and A=%o.", phi, A), "");
   require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";
   if Domain(phi) eq A then
      return A;
   end if;

   e := ModularEmbedding(A);
   if Codomain(e) eq Domain(phi) then
      return RestrictionToImage(phi, e);  
   end if;
   require false : "Not able to make sense of the restriction.  "*
         "Try calling with the second argument a map.";

end intrinsic;

intrinsic RestrictionToImage(phi::MapModAbVar, i::MapModAbVar) -> MapModAbVar
{Given morphisms i:A -> D and phi:D-> B of abelian varieties, 
return the restriction of phi to the image of i.  }
   Verbose("RestrictionToImage", 
            Sprintf("Restricting phi to image(i), where phi=%o and i=%o.", phi, i), "");
   require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";
   require Domain(phi) eq Codomain(i) :
            "The domain of argument 1 must be the codomain of argument 2.";

   D, D_to_B, A_to_D := Image(i);
   return D_to_B*phi;

end intrinsic;

intrinsic UniversalPropertyOfCokernel(pi::MapModAbVar, f::MapModAbVar)
             -> MapModAbVar
{Given pi:B -> C, the cokernel of a morphism and f:B -> D, a morphism whose 
kernel contains the kernel of pi, return
the unique morphism psi:C ->D such that pi*psi = f}
   Verbose("UniversalPropertyOfCokernel",
            Sprintf("Finding map induced by universal property of cokernel, where f=%o and pi=%o",f,pi), "");
   require IsMorphism(pi) : "Argument 1 must be a morphism of abelian varieties.";
   require Domain(pi) eq Domain(f) : "Arguments 1 and 2 must have the same domain.";
   require IsSurjective(pi) : "Argument 1 must be surjective.";
   
   /* Since this universal property is preserved under the H_1(--,Q)
      functor (i.e. go to rational homology), we find the matrix of psi
      using the characterization of kernel of Q-vector spaces.   Since matrix
      of psi is uniquely determined there, it must be the right matrix. */

   t, X := IsConsistent(Transpose(Matrix(pi)),Transpose(Matrix(f)));
   require t : "It is not even the case that the connected component " *
               "of ker(f) contains the connected component of ker(pi).";
   //X := Solution(Transpose(Matrix(pi)),Transpose(Matrix(f)))
   PSI := Transpose(X);
   K := CommonFieldOfDefinition([* pi, f *]);
   psi := Create_MapModAbVar(Codomain(pi),Codomain(f), PSI,K);

   assert pi*psi eq f;

   return psi;
end intrinsic;

/***************************************************************************

  << Kernels >>

 ***************************************************************************/

intrinsic ConnectedKernel(phi::MapModAbVar) -> ModAbVar, MapModAbVar
{The connected component C of ker(phi) and a morphism from C to the
domain of phi.}
   Verbose("ConnectedKernel", 
       Sprintf("Computing connected component of kernel of phi=%o",phi), "");
   require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";
   V := Kernel(Matrix(phi));
   H,embed_matrix := Create_ModAbVarHomol_Subspace(Homology(Domain(phi)),V);
   name := "";
   K := FieldOfDefinition(phi);
   R := FieldOfDefinition(phi);
   e := ModularEmbedding(Domain(phi));
   J := <Codomain(e), embed_matrix*Matrix(e), false>;
   C := Create_ModAbVar(name, H, K, BaseRing(Domain(phi)), J);
   i := Create_MapModAbVar(C, Domain(phi), embed_matrix, K);
   AssertEmbedding(~C,i);
   return C, i;
end intrinsic;

intrinsic Kernel(phi::MapModAbVar) -> 
                          ModAbVarSubGrp, ModAbVar, MapModAbVar
{A finite subgroup G of A (the domain of phi), an abelian variety C
such that ker(phi) equals f(C)+G, and an injective map f from C to A.}
   Verbose("Kernel", 
       Sprintf("Computing kernel of phi=%o",phi), "");

   require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";
   K,i := ConnectedKernel(phi);
   if Dimension(K) gt 0 then
      C,pi := Cokernel(i);
      psi  := UniversalPropertyOfCokernel(pi, phi);
      psi  := SurjectivePart(psi);
      G    := KernelOfIsogeny(psi);
      return G@@pi, K, i;              //  lifting looses field of definition info.
   else 
      psi  := SurjectivePart(phi);    
      return KernelOfIsogeny(psi), K, i;   // retains field of definition info.
   end if;

end intrinsic;

intrinsic ComponentGroupOfKernel(phi::MapModAbVar) -> ModAbVarSubGrp
{Component group of ker(phi).}
   Verbose("ComponentGroupOfKKernel", 
       Sprintf("Computing component group of kernel of phi=%o",phi), "");
   require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";
   K,i := ConnectedKernel(phi);
   if Dimension(K) gt 0 then
      C,pi := Cokernel(i);
      psi  := UniversalPropertyOfCokernel(pi, phi);
      psi  := SurjectivePart(psi);
      G    := KernelOfIsogeny(psi);
      return G;
   else 
      psi  := SurjectivePart(phi);    
      G := KernelOfIsogeny(psi);
      return G;
   end if;
end intrinsic;

function KernelOfIsogeny(psi)
   assert Type(psi) eq MapModAbVar;
//{The kernel of the isogeny psi.}
   /* Suppose psi : A\to B is an isogeny.
     (a) Compute generators gi for torsion group coker(H_1(A,Z)-->H_1(B,Z)).
     (b) Lift these generators to elements of H_1(A,Q) using psi.
     (c) These generate the component group.
    */
   assert IsIsogeny(psi);
   d := Degree(psi);
   assert d ne 0;
   if d eq 1 then
      return ZeroSubgroup(Domain(psi));
   end if;
   H1B := IntegralHomology(Codomain(psi));
   PSI := Matrix(psi);
   H1AQ := RationalHomology(Domain(psi));
   imH1A := MakeLattice([(H1AQ!b)*PSI : b in Basis(IntegralHomology(Domain(psi)))]);
   Q,pi := H1B/imH1A;
   PSI_inv := PSI^(-1);
   H1BQ := RationalHomology(Codomain(psi));
   V := VectorSpaceWithBasis([H1AQ!b : b in Basis(IntegralHomology(Domain(psi)))]);
// SAFE TO DELETE -- TODO
//   gens := [Domain(psi)!Coordinates(V,((H1BQ!(x@@pi))*PSI_inv)) : x in Generators(Q)];
   gens := [Domain(psi)!((H1BQ!(x@@pi))*PSI_inv) : x in Generators(Q)];
   H := Subgroup(gens);   
   H`field_of_definition := FieldOfDefinition(psi);
   return H;
end function;


/***************************************************************************

  << Images >>

 ***************************************************************************/
intrinsic '@'(A::ModAbVar, phi::MapModAbVar) -> ModAbVar
{The image of A under phi, if this makes sense, i.e., if A is
the domain of phi, or A has dimension 0, or one of the embeddings
of A has codomain equal to the domain of phi.}
   Verbose("@", 
     Sprintf("Computing phi(A), where phi=%o and A=%o.", phi,A),"");
   if Domain(phi) eq A then
      phiA,_,_ := Image(phi);
      return phiA;
   end if;
   if Dimension(A) eq 0 then
      return ZeroSubvariety(Codomain(phi));
   end if;
   for e in Embeddings(A) do
      if Domain(phi) eq Codomain(e) then
         phiA,_,_ := Image(e*phi);
         return phiA;
      end if;
   end for;
   require false : "Argument 1 not defined on argument 2.";
end intrinsic;

intrinsic '@'(G::ModAbVarSubGrp, phi::MapModAbVar) -> ModAbVarSubGrp
{The image of G under phi, if this makes sense.  If A is the
ambient variety of G, then this makes sense if A is
the domain of phi, or A has dimension 0, or one of the embeddings
of A has codomain equal to the domain of phi.}
   Verbose("@", 
     Sprintf("Computing phi(G), where phi=%o and G=%o.", phi,G),"");
   A := AmbientVariety(G);
   if Domain(phi) eq A then
      H := Subgroup([phi(g) : g in Generators(G)]);
      H`field_of_definition := 
           CommonFieldOfDefinition([* phi, G *]);
      return H;
   end if;
   if #G eq 1 then
      return ZeroSubgroup(Codomain(phi));
   end if;
   for e in Embeddings(A) do 
      if Domain(phi) eq Codomain(e) then
         psi := e*phi;
         return psi(G);
      end if;
   end for;
   require false : "No way to make sense of evaluation of morphism.";
end intrinsic;

intrinsic '@@'(G::ModAbVarSubGrp, phi::MapModAbVar) -> ModAbVarSubGrp
{A finite group who image under phi is equal to G, if possible.  If 
phi has finite kernel, then this is the exact inverse image of G under
phi.  If not, then this is a group generated by a choice of torsion 
inverse image for each generator of G, which may not be canonical.}
   Verbose("@@", 
     Sprintf("Computing a finite group H such that phi(H) = G, where phi=%o and G=%o.", phi,G),"");
   
   require Codomain(phi) eq AmbientVariety(G) : 
         "The codomain of phi must be the ambient variety of argument 1.";
   if Ngens(G) eq 0 then
      return ZeroSubgroup(Domain(phi));
   end if;
   H := Subgroup([x@@phi : x in Generators(G)]);
   // The following guarantees that we return the full inverse image
   // in the case when phi has finite kernel.
   if HasFiniteKernel(phi) then  
      H := H + ComponentGroupOfKernel(phi);
   end if;
   return H;
end intrinsic;

intrinsic Image(phi::MapModAbVar) -> ModAbVar, MapModAbVar, MapModAbVar
{The image C of phi, which is a modular abelian subvariety contained in the codomain
of phi, a morphism from C to the codomain of phi, and a surjective
morphism from the domain of phi to C.}
   Verbose("Image", 
     Sprintf("Computing the image of phi=%o.", phi),"");
   require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";

   // A = domain(phi), B = codomain(phi) in notation below
   mat_phi := Matrix(phi);
   V := Image(mat_phi);
   H, embed_matrix :=
          Create_ModAbVarHomol_Subspace(Homology(Codomain(phi)), V);

   A_to_C := RMatrixSpace(QQ, Nrows(mat_phi), Dimension(V))!
                   &cat[Coordinates(V, mat_phi[i]) : i in [1..Nrows(mat_phi)]];

   name := "";
   K := FieldOfDefinition(phi);
   R := OverRing([* K, BaseRing(Domain(phi)), BaseRing(Codomain(phi)) *]);

   phi_e := ModularEmbedding(Codomain(phi));
   Je := Codomain(phi_e);
   Je_matrix := embed_matrix*Matrix(phi_e);
   J := <Je, Je_matrix, false>;

   C := Create_ModAbVar(name, H, K, R, J);

   C_to_B_morph := Create_MapModAbVar(C, Codomain(phi), embed_matrix, K);
   A_to_C_morph := Create_MapModAbVar(Domain(phi), C, A_to_C, K);
 
   AssertEmbedding(~C, C_to_B_morph);
   if FieldOfDefinition(phi) cmpeq QQ and BaseRing(C) cmpeq QQ 
           and assigned Domain(phi)`conductor and HasFiniteKernel(phi) then
      C`conductor := Domain(phi)`conductor;
   end if;

   return C, C_to_B_morph, A_to_C_morph;
end intrinsic;


/***************************************************************************

  << Cokernels >>


EXAMPLES
We compute a 2-dimensional quotient of the 3-dimensional abelian
variety $J_0(33)$ using the Hecke operator $T_2$ and the {\tt Cokernel}
command.  
\begincode
> J := JZero(33);
> T := HeckeOperator(J,2);
> Factorization(CharacteristicPolynomial(T));
[
    <x - 1, 2>,
    <x + 2, 4>
]
> phi := T + 2;
> A, pi := Cokernel(phi);
> A;
Modular abelian variety of dimension 2 and level 3*11 over Q
> pi;
Homomorphism from JZero(33) to modular abelian variety of dimension 
2 (not printing 6x4 matrix)
\endcode

 ***************************************************************************/

intrinsic Cokernel(phi::MapModAbVar) -> ModAbVar, MapModAbVar   
{The cokernel of phi and a morphism from the codomain of phi to the cokernel.}
   Verbose("Cokernel", 
     Sprintf("Computing the cokernel of phi=%o.", phi),"");
   require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";
   B := Codomain(phi);
   W := Image(Matrix(phi));
   V := VectorSpace(Homology(B));
   Q,_,quo_matrix := V/W;
   if Dimension(Q) eq 0 then
      C := ZeroModularAbelianVariety();
      C := ChangeRing(C,BaseRing(B));
      return C, Hom(B,C)!0;
   end if;
   piB := ModularParameterization(B);
   J := Domain(piB);
   J_to_C := Matrix(piB)*quo_matrix;
   
   HC := Create_ModAbVarHomol_Quotient(Homology(B), quo_matrix);
   name := ""; 
   K := FieldOfDefinition(phi);
   R := BaseRing(B);
   C := Create_ModAbVar(name, HC, K, R, <J, false, J_to_C>);
   B_to_C := Create_MapModAbVar(B, C, quo_matrix, K);

   return C, B_to_C;
end intrinsic;


/***************************************************************************

  << Matrix Structure >>

 ***************************************************************************/

intrinsic Eltseq(phi::MapModAbVar) -> SeqEnum
{The Eltseq of the underlying matrix that defines phi.}
   return Eltseq(Matrix(phi));
end intrinsic;

intrinsic IntegralMatrix(phi::MapModAbVar) -> ModMatRngElt
{The matrix which defines phi, written with respect to integral homology.}
   Z := MatrixOnLattices(Homology(Domain(phi)), Homology(Codomain(phi)), Matrix(phi));
   t, mat := IsCoercible(RMatrixSpace(ZZ, Nrows(Z), Ncols(Z)),Z);
   require t : "Argument 1 must be a morphism of abelian varieties.";
   return mat;
end intrinsic;


intrinsic IntegralMatrixOverQ(phi::MapModAbVar) -> ModMatFldElt
{The matrix which defines phi, written with respect to integral homology.}
   Z := MatrixOnLattices(Homology(Domain(phi)), Homology(Codomain(phi)), Matrix(phi));
   return Z;
end intrinsic;

intrinsic RealMatrix(phi::MapModAbVar) ->  ModMatFldElt
{The matrix which defines phi, written with respect to real homology.}
   M := Matrix(phi);
   return RMatrixSpace(RR, Nrows(M), Ncols(M))!M;
end intrinsic;

intrinsic Matrix(phi::MapModAbVar) -> ModMatFldElt
{The matrix on chosen basis of rational homology that defines phi.}
   return phi`matrix;
end intrinsic;

intrinsic Rows(phi::MapModAbVar) -> SeqEnum
{The sequence rows of the matrix that defines phi.}
   return [Matrix(phi)[i] : i in [1..Nrows(Matrix(phi))]];
end intrinsic;

intrinsic Nrows(phi::MapModAbVar) -> RngIntElt
{The number of rows of the matrix that defines phi.  }
   return Nrows(Matrix(phi));
end intrinsic;

intrinsic Ncols(phi::MapModAbVar) -> RngIntElt
{The number of columns of the matrix that defines phi.  }
   return Ncols(Matrix(phi));
end intrinsic;



/***************************************************************************

  << Arithmetic >>

 ***************************************************************************/

intrinsic Inverse(phi::MapModAbVar) -> MapModAbVar, RngIntElt
{The inverse of phi and an integer d such that d*phi^-1 is a
morphism of abelian varieties.  }
   Verbose("Inverse", Sprintf("Computing the inverse of phi=%o.",phi),"");
   require IsIsogeny(phi) : "Argument 1 must be an isogeny.";
   matrix := Matrix(phi)^(-1);
   domain := Codomain(phi);
   codomain := Domain(phi);
   field := FieldOfDefinition(phi);
   psi,d := Create_MapModAbVar_PossiblyUpToIsogeny(domain, codomain, matrix, field);
   return psi, d;
end intrinsic;

intrinsic '*'(phi::MapModAbVar, psi::MapModAbVar) -> MapModAbVar
{The composition of the homomorphism phi and psi.}
   require Codomain(phi) eq Domain(psi) : "Codomain of argument 1 must equal domain of argument 2.";
   matrix := Matrix(phi)*Matrix(psi);
   K := CommonFieldOfDefinition([* phi, psi *]);
   return Create_MapModAbVar(Domain(phi),Codomain(psi),matrix,K);
end intrinsic;

intrinsic '+'(phi::MapModAbVar, psi::AlgMatElt) -> AlgMatElt
{The sum of the matrix that defines phi and the matrix psi. }
   require Nrows(phi) eq Nrows(psi) and Ncols(phi) eq Ncols(psi) and BaseRing(Parent(psi)) cmpeq QQ : 
           "Arguments 1 and 2 are incompatible.";
   return Matrix(phi)+psi;
end intrinsic;

intrinsic '+'(phi::MapModAbVar, psi::ModMatFldElt) -> ModMatFldElt
{The sum of the matrix that defines phi and the matrix psi. }
   require Nrows(phi) eq Nrows(psi) and Ncols(phi) eq Ncols(psi) and BaseRing(Parent(psi)) cmpeq QQ : 
           "Arguments 1 and 2 are incompatible.";
   return Matrix(phi)+psi;
end intrinsic;

intrinsic '+'(psi::AlgMatElt, phi::MapModAbVar) -> AlgMatElt
{The sum of the matrix psi and the matrix that defines phi.}
   require Nrows(phi) eq Nrows(psi) and Ncols(phi) eq Ncols(psi) and BaseRing(Parent(psi)) cmpeq QQ : 
           "Arguments 1 and 2 are incompatible.";
   return Matrix(phi)+psi;
end intrinsic;

intrinsic '+'(psi::ModMatFldElt, phi::MapModAbVar) -> ModMatFldElt
{The sum of the matrix psi and the matrix that defines phi.}
   require Nrows(phi) eq Nrows(psi) and Ncols(phi) eq Ncols(psi) and BaseRing(Parent(psi)) cmpeq QQ : 
           "Arguments 1 and 2 are incompatible.";
   return Matrix(phi)+psi;
end intrinsic;

intrinsic '-'(phi::MapModAbVar, psi::AlgMatElt) -> AlgMatElt
{The difference of the matrix that defines phi and the matrix psi. }
   require Nrows(phi) eq Nrows(psi) and Ncols(phi) eq Ncols(psi) and BaseRing(Parent(psi)) cmpeq QQ : 
           "Arguments 1 and 2 are incompatible.";
   return Matrix(phi)-psi;
end intrinsic;

intrinsic '-'(phi::MapModAbVar, psi::ModMatFldElt) -> ModMatFldElt
{The difference of the matrix that defines phi and the matrix psi. }
   require Nrows(phi) eq Nrows(psi) and Ncols(phi) eq Ncols(psi) and BaseRing(Parent(psi)) cmpeq QQ : 
           "Arguments 1 and 2 are incompatible.";
   return Matrix(phi)-psi;
end intrinsic;

intrinsic '-'(psi::AlgMatElt, phi::MapModAbVar) -> AlgMatElt
{The difference of the matrix psi and the matrix that defines phi.}
   require Nrows(phi) eq Nrows(psi) and Ncols(phi) eq Ncols(psi) and BaseRing(Parent(psi)) cmpeq QQ : 
           "Arguments 1 and 2 are incompatible.";
   return Matrix(psi)-phi;
end intrinsic;

intrinsic '-'(psi::ModMatFldElt, phi::MapModAbVar) -> ModMatFldElt
{The difference of the matrix psi and the matrix that defines phi.}
   require Nrows(phi) eq Nrows(psi) and Ncols(phi) eq Ncols(psi) and BaseRing(Parent(psi)) cmpeq QQ : 
           "Arguments 1 and 2 are incompatible.";
   return Matrix(psi)-phi;
end intrinsic;

intrinsic '*'(phi::MapModAbVar, psi::AlgMatElt) -> AlgMatElt
{The product of the matrix that defines phi and the matrix psi. }
   require Ncols(phi) eq Nrows(psi) and BaseRing(Parent(psi)) cmpeq QQ : 
           "Arguments 1 and 2 are incompatible.";
   return Matrix(phi)*psi;
end intrinsic;

intrinsic '*'(phi::MapModAbVar, psi::ModMatFldElt) -> ModMatFldElt
{The product of the matrix that defines phi and the matrix psi. }
   require Ncols(phi) eq Nrows(psi) and BaseRing(Parent(psi)) cmpeq QQ : 
           "Arguments 1 and 2 are incompatible.";
   return Matrix(phi)*psi;
end intrinsic;


intrinsic '*'(psi::AlgMatElt, phi::MapModAbVar) -> AlgMatElt
{The product of the matrix psi and the matrix that defines phi.}
   require Ncols(psi) eq Nrows(phi) and BaseRing(Parent(psi)) cmpeq QQ : 
           "Arguments 1 and 2 are incompatible.";
   return Matrix(phi)*psi;
end intrinsic;

intrinsic '*'(psi::ModMatFldElt, phi::MapModAbVar) -> ModMatFldElt
{The product of the matrix psi and the matrix that defines phi.}
   require Ncols(psi) eq Nrows(phi) and BaseRing(Parent(phi)) cmpeq QQ : 
           "Arguments 1 and 2 are incompatible.";
   return Matrix(phi)*psi;
end intrinsic;


intrinsic '*'(a::RngIntElt, phi::MapModAbVar) -> MapModAbVar
{The product of the integer a times the homomorphism phi.}
   matrix := a*Matrix(phi);
   return Create_MapModAbVar(Domain(phi),Codomain(phi),matrix,FieldOfDefinition(phi));
end intrinsic;

intrinsic '*'(a::FldRatElt, phi::MapModAbVar) -> MapModAbVar
{The product of the rational number a times the homomorphism phi.  }
   matrix := a*Matrix(phi);
   psi := Create_MapModAbVar_PossiblyUpToIsogeny(Domain(phi),
                        Codomain(phi),matrix,FieldOfDefinition(phi));
   return psi;
end intrinsic;

intrinsic '^'(phi::MapModAbVar, n::RngIntElt) -> MapModAbVar
{The n-fold composition phi^n of the endomorphism phi with itself.  If n=-1,
then this is the inverse of phi, in which case 
phi must be an isogeny or there is an error.}
   if n eq 1 then
      return phi;
   end if;
   if n lt 0 then
      mat := Matrix(phi);
      ALG := MatrixAlgebra(QQ,Nrows(mat))!Eltseq(mat);
      require IsInvertible(ALG) : "Argument 1 must be invertible.";
   end if;
   if n eq -1 then
      return Create_MapModAbVar_PossiblyUpToIsogeny(Codomain(phi),
                        Domain(phi),Matrix(phi)^(-1),FieldOfDefinition(phi));
   end if;
   require Domain(phi) eq Codomain(phi) : "Argument 1 must be an endomorphism.";
   return Create_MapModAbVar_PossiblyUpToIsogeny(Domain(phi),
                        Domain(phi),Matrix(phi)^n,FieldOfDefinition(phi));
end intrinsic;

intrinsic '+'(phi::MapModAbVar, psi::MapModAbVar) -> MapModAbVar
{The sum of the homomorphism phi and psi.}
   require Domain(phi) eq Domain(psi) : "Domain of argument 1 must equal domain of argument 2.";
   require Codomain(phi) eq Codomain(psi) : "Codomains of argument 1 must equal codomain of argument 2.";
   matrix := Matrix(phi) + Matrix(psi);
   K := CommonFieldOfDefinition([* phi, psi *]);
   return Create_MapModAbVar(Domain(phi),Codomain(phi),matrix,K);
end intrinsic;

intrinsic '-'(phi::MapModAbVar, psi::MapModAbVar) -> MapModAbVar
{The difference of the homomorphism phi and psi.}
   require Domain(phi) eq Domain(psi) : "Domain of argument 1 must equal domain of argument 2.";
   require Codomain(phi) eq Codomain(psi) : "Codomains of argument 1 must equal codomain of argument 2.";
   return phi + (-1)*psi;
end intrinsic;

intrinsic '-'(phi::MapModAbVar, n::RngIntElt) -> MapModAbVar
{The difference of the endomorphism phi and the endomorphism multiplication-by-n.}
   require IsEndomorphism(phi) : "Argument 1 must be an endomorphism.";
   return phi + (-n);
end intrinsic;

intrinsic '+'(phi::MapModAbVar, n::RngIntElt) -> MapModAbVar
{The sum of the endomorphism phi and the endomorphism multiplication-by-n.}
   require IsEndomorphism(phi) : "Argument 1 must be an endomorphism.";
   return phi + nIsogeny(Domain(phi),n);
end intrinsic;

intrinsic '-'(n::RngIntElt, phi::MapModAbVar) -> MapModAbVar
{The difference of the endomorphism multiplication-by-n and the endomorphism phi.}
   require IsEndomorphism(phi) : "Argument 1 must be an endomorphism.";
   return n + (-1*phi);
end intrinsic;

intrinsic '+'(n::RngIntElt, phi::MapModAbVar) -> MapModAbVar
{The sum of the endomorphism multiplication-by-n and the endomorphism phi.}
   require IsEndomorphism(phi) : "Argument 1 must be an endomorphism.";
   return phi + nIsogeny(Domain(phi),n);
end intrinsic;

intrinsic '-'(phi::MapModAbVar, n::FldRatElt) -> MapModAbVar
{The difference of the endomorphism phi and the endomorphism 
multiplication-by-n.}
   require IsEndomorphism(phi) : "Argument 1 must be an endomorphism.";
   return phi + (-n);
end intrinsic;


intrinsic '-'(n::FldRatElt, phi::MapModAbVar) -> MapModAbVar
{The difference of multiplication-by-n and the endomorphism phi.}
   require IsEndomorphism(phi) : "Argument 1 must be an endomorphism.";
   return n + (-1*phi);
end intrinsic;

intrinsic '+'(n::FldRatElt, phi::MapModAbVar) -> MapModAbVar
{The sum of multiplication by the rational number n and the endomorphism phi.}
   require IsEndomorphism(phi) : "Argument 1 must be an endomorphism.";
   return phi + n*IdentityMap(Domain(phi));
end intrinsic;


/***************************************************************************

  << Polynomials >>

 ***************************************************************************/

intrinsic CharacteristicPolynomial(phi::MapModAbVar) -> RngUPolElt
{The characteristic polynomial of the endomorphism phi.  }
//   require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";
   require IsEndomorphism(phi) : "Argument 1 must be an endomorphism.";

   if not assigned phi`charpoly then
      Verbose("CharacteristicPolynomial", 
         Sprintf("Computing the characteristic polynomial of phi=%o", phi),"");
      if IsEndomorphism(phi) and IsAttachedToModularSymbols(Domain(phi)) then
         t, n := IsHeckeOperator(phi);
         if t then
            phi`charpoly := HeckePolynomial(Domain(phi),n);
         end if;
      end if;
      if not assigned phi`charpoly then
         phi`charpoly := CharacteristicPolynomial(Matrix(phi)); 
      end if;
   end if;
   return phi`charpoly;
end intrinsic;

intrinsic MinimalPolynomial(phi::MapModAbVar) -> RngUPolElt
{The minimal polynomial of the endomorphism phi.  }

//   require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";
   require IsEndomorphism(phi) : "Argument 1 must be an endomorphism.";

   if not assigned phi`minpoly then
      Verbose("MinimalPolynomial", 
         Sprintf("Computing the minimal polynomial of phi=%o", phi),"");
      if IsEndomorphism(phi) and IsAttachedToModularSymbols(Domain(phi)) then
         t, n := IsHeckeOperator(phi);
         if t then
            phi`minpoly := MinimalHeckePolynomial(Domain(phi),n);
         end if;
      end if;
      if not assigned phi`minpoly then
         phi`minpoly := MinimalPolynomial(Matrix(phi)); 
      end if;
   end if;
   return phi`minpoly;
end intrinsic;


intrinsic FactoredCharacteristicPolynomial(phi::MapModAbVar) -> RngUPolElt
{The factorization of the characteristic polynomial of the endomorphism phi.}
   //require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";
   require IsEndomorphism(phi) : "Argument 1 must be an endomorphism.";
   if not assigned phi`factored_charpoly then
      Verbose("FactoredCharacteristicPolynomial", 
         Sprintf("Computing the factored characteristic polynomial of phi=%o", phi),"");
      if IsEndomorphism(phi) and IsAttachedToModularSymbols(Domain(phi)) then
         t, n := IsHeckeOperator(phi);
         if t then
            phi`factored_charpoly := 
             FactoredHeckePolynomial(Domain(phi),n);
         end if;
      end if;
      if not assigned phi`factored_charpoly then
         phi`factored_charpoly := 
              Factorization(CharacteristicPolynomial(Matrix(phi)));
      end if;
   end if;
   return phi`factored_charpoly;
end intrinsic;


/***************************************************************************

  << Invariants >>

 ***************************************************************************/

intrinsic Rank(phi::MapModAbVar) -> RngIntElt
{The dimension of the kernel of phi.}
   Verbose("Rank",
         Sprintf("Computing the rank of phi=%o", phi),"");
   mat := Matrix(phi);
   r := Rank(mat);
   return r div (Sign(Domain(phi)) eq 0 select 2 else 1);
end intrinsic;

intrinsic Nullity(phi::MapModAbVar) -> RngIntElt
{The dimension of the kernel of phi.}
   Verbose("Nullity",
         Sprintf("Computing the nullity of phi=%o", phi),"");
   mat := Matrix(phi);
   n := Nrows(mat) - Rank(mat);
   return n div (Sign(Domain(phi)) eq 0 select 2 else 1);
end intrinsic;

intrinsic ClearDenominator(phi::MapModAbVar) -> MapModAbVar
{Morphism n*phi with n positive and minimal.}
   return Denominator(phi)*phi;
end intrinsic;

intrinsic Denominator(phi::MapModAbVar) -> RngIntElt
{The smallest positive integer n such that n*phi is a homomorphism. } 
   if not assigned phi`denominator then
      if Nrows(phi) eq 0 or Ncols(phi) eq 0 then
         phi`denominator := 1;
      else
         Z := MatrixOnLattices(Homology(Domain(phi)), Homology(Codomain(phi)), Matrix(phi));
         phi`denominator := LCM([Denominator(a) : a in Eltseq(Z)]);
      end if;
   end if;
   return phi`denominator;
end intrinsic;

intrinsic Trace(phi::MapModAbVar) -> FldRatElt
{The trace of a matrix that defines phi.}
   require Domain(phi) eq Codomain(phi) : "Argument 1 must be an endomorphism.";
   return Trace(Matrix(phi));
end intrinsic;

intrinsic Degree(phi::MapModAbVar) -> RngIntElt
{The degree of the morphism phi.  }
   require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";

   if not assigned phi`degree then
      Verbose("Degree",
         Sprintf("Computing the degree of phi=%o", phi),"");
      M := Matrix(phi);
      if Rank(M) eq Nrows(M) then
         MZ := IntegralMatrix(phi);
         phi`degree := &*  ElementaryDivisors(MZ); 
      else
         phi`degree := 0;
      end if;
   end if;
   return phi`degree;
end intrinsic;

intrinsic Domain(phi::MapModAbVar) -> ModAbVar
{The domain of phi.}
   return phi`domain;
end intrinsic;

intrinsic Codomain(phi::MapModAbVar) -> ModAbVar
{The codomain of phi.}
   return phi`codomain;
end intrinsic;

intrinsic FieldOfDefinition(phi::MapModAbVar) -> ModAbVar
{A field of definition of phi.}
   return phi`field_of_definition;
end intrinsic;

function Name(phi)
   // A short string that describes phi.
   assert Type(phi) eq MapModAbVar;
   return phi`name;
end function;

procedure SetName(phi, name) 
   // Set the name of phi.
   assert Type(phi) eq MapModAbVar;
   assert Type(name) eq MonStgElt;
   phi`name := name;
end procedure;


/***************************************************************************

  << Predicates >>


 ***************************************************************************/

intrinsic IsMorphism(phi::MapModAbVar) -> BoolElt
{True if and only if phi is a morphism in the category of abelian
varieties.}
   return Denominator(phi) eq 1;
end intrinsic;

intrinsic 'in'(phi::MapModAbVar, X::List) -> BoolElt
{True if phi is one of the homomorphisms in the list X of homomorphisms.}
   return &or [phi eq psi : psi in X];
end intrinsic; 

intrinsic 'eq'(phi::MapModAbVar, psi::MapModAbVar) -> BoolElt
{True if the two homomorphisms phi and psi are equal.}
   if Parent(phi) ne Parent(psi) then
      return false;
   end if;
   return Matrix(phi) eq Matrix(psi);
end intrinsic;

intrinsic 'eq'(phi::MapModAbVar, n::RngIntElt) -> BoolElt
{True if phi is equal to multiplication by the integer n.}
   t, y := IsCoercible(Parent(phi),n);
   require t : "Arguments 1 and 2 are not comparable.";
   return y eq phi;
end intrinsic;

intrinsic 'eq'(n::RngIntElt, phi::MapModAbVar) -> BoolElt
{True if phi is equal to multiplication by the integer n.}
   t, y := IsCoercible(Parent(phi),n);
   require t : "Arguments 1 and 2 are not comparable.";
   return y eq phi;
end intrinsic;


intrinsic IsEndomorphism(phi::MapModAbVar) -> BoolElt
{True if phi is an endomorphism, i.e., the domain and codomain of phi are equal.}
   return Domain(phi) eq Codomain(phi);
end intrinsic;

intrinsic IsHeckeOperator(phi::MapModAbVar) -> BoolElt, RngIntElt
{If phi was computed using the HeckeOperator command, then true and 
the parameter n passed to the HeckeOperator command when creating phi.  
Otherwise false and 0.}
   if assigned phi`hecke_operator then
      return true, phi`hecke_operator;
   else
      return false, 0;
   end if;
end intrinsic;

intrinsic HasFiniteKernel(phi::MapModAbVar) -> BoolElt
{True if the kernel of the homomorphism phi is finite.} 
   require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";
   if not assigned phi`has_finite_kernel then
      phi`has_finite_kernel := Rank(Matrix(phi)) eq Nrows(Matrix(phi));
   end if;
   return phi`has_finite_kernel;
end intrinsic;

intrinsic IsInjective(phi::MapModAbVar) -> BoolElt
{True if phi is an injective homomorphism.}
   require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";
   if not HasFiniteKernel(phi) then
      return false;
   end if;
   return #KernelOfIsogeny(SurjectivePart(phi)) eq 1;
end intrinsic;

intrinsic IsOptimal(phi::MapModAbVar) -> BoolElt
{True if phi is an optimal quotient map, i.e., phi is
surjective and has connected kernel.}
   return IsSurjective(phi) and #ComponentGroupOfKernel(phi) eq 1;
end intrinsic;

intrinsic IsIsomorphism(phi::MapModAbVar) -> BoolElt
{True if phi is an isomorphism of abelian varieties.}
   return IsInjective(phi) and IsSurjective(phi);
end intrinsic;

intrinsic IsIsogeny(phi::MapModAbVar) -> BoolElt
{True if phi is a surjective homomorphism with finite kernel.  }
   require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";
   if not assigned phi`is_isogeny then
      mat := Matrix(phi);
      
      phi`is_isogeny :=  Nrows(mat) eq Ncols(mat) and
                         Determinant(mat) ne 0;
   end if;
   return phi`is_isogeny;
end intrinsic;

intrinsic IsZero(phi::MapModAbVar) -> BoolElt
{True if phi is the zero morphism.}
   return IsZero(Matrix(phi));
end intrinsic;

intrinsic IsInteger(phi::MapModAbVar) -> BoolElt, RngIntElt
{True if phi is multiplication by n for some integer n.  
If true, returns that n as well.  If false, returns false
and the second return value is not defined.}
   require IsMorphism(phi) : "Argument 1 must be a morphism of abelian varieties.";
   if not IsEndomorphism(phi) then
      return false, _;
   end if;
   if Dimension(Domain(phi)) eq 0 then
      return true, 1;
   end if;
   n := ZZ!Matrix(phi)[1,1];
   if phi eq nIsogeny(Domain(phi),Integers()!n) then
      return true, n;
   else
      return false, _;
   end if;
end intrinsic;

intrinsic IsSurjective(phi::MapModAbVar) -> BoolElt
{True if the homomorphism phi is surjective.}
   return Dimension(Homology(Codomain(phi))) eq Dimension(RowSpace(Matrix(phi)));
end intrinsic;

intrinsic OnlyUpToIsogeny(phi::MapModAbVar) -> BoolElt
{Return true if phi is a homomorphism in the category of abelian varieties only up to isogeny.} 
   return assigned phi`only_up_to_isogeny and phi`only_up_to_isogeny;
end intrinsic;



intrinsic Parent(phi::MapModAbVar) -> HomModAbVar
{}
   return phi`parent;
end intrinsic;

intrinsic Print(phi::MapModAbVar, level::MonStgElt)
{}
   show_matrix := Nrows(phi) lt 5 and Ncols(phi) lt 30;
   printf "Homomorphism %o%ofrom %o to %o%o", 
           phi`name, 
           phi`name ne "" select " " else "",
           ShortDesc(Domain(phi)), 
           ShortDesc(Codomain(phi)), 
           (Denominator(phi) ne 1) select Sprintf(" (up to isogeny) on integral homology by:\n%o", 
                    show_matrix select IntegralMatrixOverQ(phi) else Sprintf(" (not printing %ox%o matrix)",Nrows(phi),Ncols(phi))
                                ) else 
                   show_matrix select Sprintf(
        " given on integral homology by:\n%o",IntegralMatrix(phi)) else 
           Sprintf(" (not printing %ox%o matrix)",Nrows(phi),Ncols(phi));
end intrinsic;

