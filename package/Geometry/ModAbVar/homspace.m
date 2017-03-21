freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: homespace.m
   DESC: Basic HomModAbVar functionality.

   Creation: 06/16/03 -- initial creation
      
 ***************************************************************************/

/*
HANDBOOK_TITLE: Endomorphism Algebras and Hom Spaces
*/

import "endo_alg.m":
   Basis_for_EndomorphismMatrixAlgebra_of_Af,
   Basis_For_Hecke_Algebra_Over_Q,
   Basis_For_Hecke_Algebra_Over_Z,
   Is_Full_EndAf_Commutative;

import "homology.m":
   BasisChange_Lattice_to_Rational,
   BasisChange_Rational_to_Lattice;

import "linalg.m":
   DiscriminantMatAlgZ,
   Intersect_Vector_Space_With_Lattice,
   MakeLattice,
   MatrixLatticeBasis,
   SaturateWithRespectToBasis,
   VerticallyStackMatrices;

import "modabvar.m":
   InCreation,
   ShortDesc,
   Verbose;

import "morphisms.m":
   Copy_MapModAbVar,
   Create_MapModAbVar,
   Create_MapModAbVar_MultiplyToMorphism,
   MatrixOnLattices;

import "rings.m":
   Qbar, QQ, ZZ, 
   OverField;

forward 
   Basis_Change_Matrix_From_Isogeny_Decomposition,
   Basis_For_HomAB_Tensor_Q,
   Basis_Of_Saturation_From_Over_Q,
   Copy_HomModAbVar,
   Create_HomModAbVar,
   Create_Matrix,
   Decide_If_Commutative,
   Decide_If_Ring,
   Homspace_Tensor_Q_On_Isogeny_Decompositions,
   MatrixDimensions,
   Name,
   SetName,
   RandomHom, 
   formatricesthatareabasisforEnd;


declare type HomModAbVar [MapModAbVar];

declare attributes HomModAbVar:
   domain,
   codomain,
   lattice,
   vector_space,
   discriminant,
   field_of_definition,
   is_over_q,    
   is_ring,
   is_commutative,
   is_saturated,
   is_full,
   is_hecke_algebra,
   basis,
   rmatrixspace,
   hom_tensor_q,   // store pointer to this, so if user ever asks we have it
                   // already (it is needed for many computations before tensoring)
   name;

function Copy_HomModAbVar(H)
   assert Type(H) eq HomModAbVar;
   H2 := New(HomModAbVar);   
   // template:  if assigned H` then H2` := H`; end if;
   if assigned H`domain then H2`domain := H`domain; end if;
   if assigned H`codomain then H2`codomain := H`codomain; end if;
   if assigned H`field_of_definition then H2`field_of_definition := H`field_of_definition; end if;
   if assigned H`discriminant then H2`discriminant := H`discriminant; end if;
   if assigned H`is_over_q then H2`is_over_q := H`is_over_q; end if;
   if assigned H`is_ring then H2`is_ring := H`is_ring; end if;
   if assigned H`is_full then H2`is_full := H`is_full; end if;
   if assigned H`is_saturated then H2`is_saturated := H`is_saturated; end if;
   if assigned H`is_commutative then H2`is_commutative := H`is_commutative; end if;
   if assigned H`is_hecke_algebra then H2`is_hecke_algebra := H`is_hecke_algebra; end if;
   if assigned H`basis then H2`basis := H`basis; end if;
   if assigned H`rmatrixspace then H2`rmatrixspace := H`rmatrixspace; end if;
   if assigned H`hom_tensor_q then H2`hom_tensor_q := H`hom_tensor_q; end if;
   if assigned H`name then H2`name := H`name; end if;
   return H2;
end function;

function MatrixDimensions(H)
   return Dimension(Homology(Domain(H))), Dimension(Homology(Codomain(H)));
end function;

function Create_HomModAbVar(A, B, type, gens, is_basis, is_over_q)

   assert Type(A) eq ModAbVar;
   assert Type(B) eq ModAbVar;
   assert Type(type) eq MonStgElt;
   assert Type(gens) in {SeqEnum, BoolElt};
   assert Type(is_basis) eq BoolElt;
   assert Type(is_over_q) eq BoolElt;   
   assert BaseRing(A) cmpeq BaseRing(B);

   Verbose("Create_HomModAbVar", Sprintf("Creating Hom(A,B)%o, where A=%o and B=%o.",
           is_over_q select " over Q" else "", A, B), "");

   H := New(HomModAbVar);   
   H`domain := A;
   H`codomain := B;
   H`field_of_definition := FieldOfFractions(BaseRing(A));
   H`is_over_q := is_over_q;
   H`name := "";
   if type eq "Full" then
      H`is_full := true;
      H`is_saturated := true;
   elif type eq "Hecke" then
      assert A eq B;
      H`is_hecke_algebra := true;
      H`is_commutative := true;
      if IsAttachedToModularSymbols(A) then
         H`is_ring := true;
      end if;
   end if;
   if Type(gens) eq SeqEnum then
      if not is_basis and #gens gt 0 then
         m := Nrows(gens[1]); n := Ncols(gens[1]);
         if is_over_q then
            gens := Basis(sub<RMatrixSpace(QQ,m,n) | [Matrix(g) : g in gens]>);
         else
            gens := MatrixLatticeBasis([Matrix(g) : g in gens]);
         end if;
      else
         gens := [Matrix(g) : g in gens];
      end if; 
      H`basis := [Hom(A,B) | Create_MapModAbVar(A,B,g,H`field_of_definition) 
                                : g in gens];
      for i in [1..#H`basis] do
         (H`basis[i])`parent := H;
      end for;
   end if;
   return H;
end function;


/***************************************************************************

  << Creation >>

 ***************************************************************************/

intrinsic Hom(A::ModAbVar, B::ModAbVar, overQ::BoolElt) -> HomModAbVar
{Group of homomorphisms from A to B, or vector space generated by
homomorphisms from A to B if overQ is true.}
   require BaseRing(A) cmpeq BaseRing(B) : 
     "The base rings of A and B must be the same.";
   if not InCreation(A) and not InCreation(B) and A eq B then
      if overQ then
         if not assigned A`endomorphism_algebra then
            A`endomorphism_algebra := Create_HomModAbVar(A, B, "Full", false, false, overQ);
         end if;
         return A`endomorphism_algebra;
      else
         if not assigned A`endomorphism_ring then
            A`endomorphism_ring := Create_HomModAbVar(A, B, "Full", false, false, overQ);
         end if;
         // an optimization
         if not assigned A`hecke_algebra and BaseRing(A) cmpeq QQ and
                assigned A`is_simple and A`is_simple then
            A`hecke_algebra := A`endomorphism_ring;
         end if;
                      
         return A`endomorphism_ring;
      end if;
   end if;      
   return Create_HomModAbVar(A, B, "Full", false, false, overQ);
end intrinsic;

intrinsic Hom(A::ModAbVar, B::ModAbVar) -> HomModAbVar
{Group of homomorphisms from A to B.}
   require BaseRing(A) cmpeq BaseRing(B) : 
     "The base rings of A and B must be the same.";
   return Hom(A,B,false);
end intrinsic;

intrinsic End(A::ModAbVar) -> HomModAbVar
{The endomorphism ring of A.}
   return Create_HomModAbVar(A, A, "Full", false, false, false);
end intrinsic;

intrinsic End(A::ModAbVar, overQ::BoolElt) -> HomModAbVar
{If overQ is false, the endomorphism ring, and if it is true,
the endomorphism algebra.}
   return Create_HomModAbVar(A, A, "Full", false, false, overQ);
end intrinsic;

intrinsic BaseExtend(H::HomModAbVar, R::Rng) -> HomModAbVar
{The space H \tensor R, where R is the rational numbers or integers.}
   if R cmpeq ZZ then
      return H;
   end if;
   require R cmpeq QQ : "Argument 2 must be either Z or Q.";
   if assigned H`is_over_q and H`is_over_q then
      return H;
   end if;
   if not assigned H`hom_tensor_q then
      H2 := Copy_HomModAbVar(H);
      H2`is_over_q := true;
      if assigned H2`name then
         H2`name := H2`name*"_Q";
      end if;
      H`hom_tensor_q := H2;
   end if;
   return H`hom_tensor_q;
end intrinsic;

intrinsic HeckeAlgebra(A::ModAbVar) -> HomModAbVar
{The Hecke algebra associated to A.  }
   if not assigned A`hecke_algebra then
      Verbose("HeckeAlgebra",  Sprintf("Computing Hecke algebra of %o.", A),"");
      if A`name ne "" then
         name := Sprintf("HeckeAlg(%o)",A`name);
      else
         name := "";
      end if;
      if not IsAttachedToModularSymbols(A) then // pull back from modular embedding.
         e  := ModularEmbedding(A);
         J  := Codomain(e);
         TT := HeckeAlgebra(J);
         pi := ModularParameterization(A);
         TA := Pullback(e,TT,pi);
      else
         TA := Create_HomModAbVar(A, A, "Hecke", false, false, false);
      end if;
      SetName(TA,name);
      A`hecke_algebra := TA;
      // optimization
      if not assigned A`endomorphism_ring and BaseRing(A) cmpeq QQ and 
                IsSimple(A) then
         A`endomorphism_ring := A`hecke_algebra;
      end if;
   end if;
   return A`hecke_algebra;
end intrinsic;



/***************************************************************************

  << Subgroups  and Subrings >>

 ***************************************************************************/

intrinsic Subgroup(X::[MapModAbVar], overQ::BoolElt : IsBasis := false) -> HomModAbVar
{Group of homomorphisms generated by elements of X.  If the parameter
IsBasis is true, then we assume the elements of X are a basis for their
span.}
   Verbose("Subgroup", 
      Sprintf("Computing subgroup generated by %o", X),"");
   if #X eq 0 then
      return End(ZeroModularAbelianVariety(), overQ);
   end if;
   return Create_HomModAbVar(Domain(X[1]),Codomain(X[1]),"Other",
                X, IsBasis, overQ);
end intrinsic;

intrinsic Subring(X::[MapModAbVar], overQ::BoolElt) -> HomModAbVar
{The ring of endomorphisms generated by elements in X.}
   Verbose("Subring", 
      Sprintf("Computing subring generated by %o", X),"");
   if #X eq 0 then
      return End(ZeroModularAbelianVariety(), overQ);
   end if;
   require IsEndomorphism(X[1]) : "Argument 1 must be a sequence of endomorphisms.";
   return RingGeneratedBy(Subgroup(X,overQ));
end intrinsic;

intrinsic Subring(phi::MapModAbVar) -> HomModAbVar
{The ring of endomorphisms generated by elements in phi.}
   R := Subring([phi]);
   return R;
end intrinsic;

intrinsic RingGeneratedBy(H::HomModAbVar) -> HomModAbVar
{The ring of endomorphisms generated by the endomorphisms in H.}
   Verbose("RingGeneratedBy", 
      Sprintf("Computing ringer generated by elements of %o.",H),"");
   require Domain(H) eq Codomain(H) : "Argument 1 must be a group of endomorphisms.";
   if Rank(H) eq 0 then
      return H;
   end if;
   A := Domain(H);
   if Rank(H) gt 1 then
      Alg := MatrixAlgebra(H);
      basis := Basis(Alg);
   else
      phi := H.1;
      mat := MatrixAlgebra(QQ, Nrows(phi))!Matrix(phi);
      basis := [mat];
      f := MinimalPolynomial(phi);
      if Coefficient(f,Degree(f)) ne 1 then
         require false : "Minimal polynomial not monic, so ring not finitely generated.";
      end if;
      for n in [2..Degree(f)] do 
         Append(~basis, basis[#basis]*mat);
      end for;
   end if;
   X := [Create_MapModAbVar(A, A, g, QQ) : g in basis];
   H2 := Subgroup(X, IsOverQ(H) : IsBasis := true);
   H2`is_ring := true;
   if Rank(H) le 1 then
      H2`is_commutative := true;
   end if;
   return H2;
end intrinsic;

intrinsic Saturation(H::HomModAbVar) -> HomModAbVar
{The saturation of H in all homomorphisms.  }
   Verbose("RingGeneratedBy", 
      Sprintf("Computing ringer generated by elements of %o.",H),"");
   if assigned H`is_saturated then
      return H;
   end if;
   B := Basis_Of_Saturation_From_Over_Q(H`domain, H`codomain, Generators(H));
   if B eq Generators(H) or (&and[b in H : b in B]) then
      H`is_saturated := true;
      return H;
   else
      H`is_saturated := false;
   end if;
   H2 := Copy_HomModAbVar(H);
   if assigned H`basis then
      H2`basis := B;
   end if;
   if Name(H) ne "" then
      H2`name := Sprintf("Sat(%o)",Name(H));
   end if;
   H2`is_saturated := true;
   return H2;
end intrinsic;


intrinsic Subgroup(X::[MapModAbVar]) -> HomModAbVar
{Group of homomorphisms from A to B generated by elements of X.}
   return Subgroup(X,false);
end intrinsic;

intrinsic Subring(X::[MapModAbVar]) -> HomModAbVar
{Ring of endomorphisms of an abelian variety generated by elements of X.}
   return Subring(X,false);
end intrinsic;

/***************************************************************************

  << Pullback and Pushforward of Hom Spaces >>

 
 ***************************************************************************/

intrinsic Pullback(phi::MapModAbVar, H::HomModAbVar, psi::MapModAbVar) -> HomModAbVar
{Suppose H is a space of homomorphism A --> B and
phi:C-->A and psi:B-->D.  Then this intrinsic computes and
returns the ring of homomorphisms of A of the form 
phi*f*psi, where f is in H.}
   B := Basis(H);
   A := Domain(phi);
   D := Codomain(psi);
   return Subgroup([Hom(A,D)| phi*f*psi : f in Basis(H)],IsOverQ(H));
end intrinsic;

intrinsic Pullback(H::HomModAbVar, phi::MapModAbVar) -> HomModAbVar
{Given a space of homomorphism H in Hom(A,B) and a morphism phi:B-->C, compute
the image of H in Hom(A,C) via the map that sends f to f*phi.}
   require Domain(phi) eq Codomain(H) : 
     "The codomain of argument 1 must equal the domain of argument 2.";
   B := Basis(H);
   A := Domain(H); B := Codomain(phi);
   return Subgroup([Hom(A,B) | f*phi : f in Basis(H)],IsOverQ(H));
end intrinsic;

intrinsic Pullback(phi::MapModAbVar, H::HomModAbVar) -> HomModAbVar
{Given a space of homomorphism H in Hom(A,B) and a morphism phi:C-->A, compute
the image of H in Hom(C,B) via the map that sends f to phi*f.}
   require Domain(H) eq Codomain(phi) : 
     "The domain of argument 1 must equal the codomain of argument 2.";
   B := Basis(H);
   C := Domain(phi);
   B := Codomain(H);
   return Subgroup([Hom(C,B)|phi*f : f in Basis(H)],IsOverQ(H));
end intrinsic;




/***************************************************************************

  << Arithmetic >>


 ***************************************************************************/
intrinsic 'meet'(H1::HomModAbVar, H2::HomModAbVar) -> HomModAbVar
{The intersection of H_1 and H_2, where H_1 and H_2 are assumed
to both be subgroups of Hom(A,B), for abelian varieties A and B.}
   Verbose("meet", Sprintf("Intersecting %o and %o.", H1, H2),"");

   require Domain(H1) eq Domain(H2) : "Arguments 1 and must have the same domain.";
   require Codomain(H1) eq Codomain(H2): "Arguments 1 and must have the same codomain.";
   require FieldOfDefinition(H1) eq FieldOfDefinition(H2) : 
             "Arguments 1 and must have the same field of definition.";
  
   K := FieldOfDefinition(H1);
   if IsOverQ(H1) and IsOverQ(H2) then
      B := Basis(VectorSpace(H1) meet VectorSpace(H2));
   elif IsOverQ(H1) then
      B := Basis(Intersect_Vector_Space_With_Lattice(VectorSpace(H1), Lattice(H2)));
   elif IsOverQ(H2) then
      B := Basis(Intersect_Vector_Space_With_Lattice(VectorSpace(H2), Lattice(H1)));
   else 
      B := Basis(Lattice(H1) meet Lattice(H2));
   end if;
   M := RMatrixSpace(QQ,Dimension(Homology(Domain(H1))),
                        Dimension(Homology(Codomain(H1))));
   G := [Create_MapModAbVar(Domain(H1),Codomain(H1),M!Eltseq(T),K) : T in B];
   return Subgroup(G,IsOverQ(H1) and IsOverQ(H2));
end intrinsic;

intrinsic '+'(H1::HomModAbVar, H2::HomModAbVar) -> HomModAbVar
{The subgroup generated by H_1 and H_2, where H_1 and H_2 are assumed
to both be subgroups of Hom(A,B), for abelian varieties A and B.}
   Verbose("+", Sprintf("Summing %o and %o.", H1, H2),"");
   require Domain(H1) eq Domain(H2) : "Arguments 1 and must have the same domain.";
   require Codomain(H1) eq Codomain(H2): "Arguments 1 and must have the same codomain.";
   if IsOverQ(H1) or IsOverQ(H2) then
      V := VectorSpace(H1) + VectorSpace(H2);
   else
      V := Lattice(H1) + Lattice(H2);
   end if;
   H := Hom(Domain(H1),Codomain(H1));
   Gens := [H!Eltseq(b) : b in Basis(V)];
   return Subgroup(Gens, IsOverQ(H1) or IsOverQ(H2));

end intrinsic;

/***************************************************************************

  << Quotients >>

 ***************************************************************************/

intrinsic Quotient(H2::HomModAbVar, H1::HomModAbVar) -> GrpAb, Map, Map
{The abelian group quotient H_2/H_1, a map from H_2 to this quotient, 
and a lifting map from this quotient to H_2.}
   Verbose("Quotient", Sprintf("Quotient of %o by %o.", H1, H2),"");
   require H1 subset H2 : "Argument 2 must be a subset of argument 1.";
   if Dimension(H2) eq 0 then
      G := AbelianGroup([]);
      f := hom<H2 -> G  | x :-> G!0>;
      g := hom<G  -> H2 | x :-> H2!0>;
      return G, f, g;
   end if;
   if IsOverQ(H1) and IsOverQ(H2) then
      V1 := VectorSpace(H1);
      V2 := VectorSpace(H2);
      G,pi := V2/V1;
      f := hom<H2 -> G | x :-> pi(V2!Eltseq(x)) >;
      g := hom<G -> H2 | x :-> H2!Eltseq(x@@pi) >;
      return G, f, g;
   end if;
   L1 := Lattice(H1);
   L2 := Lattice(H2);
   G,pi := L2/L1;
   f := hom<H2 -> G | x :-> pi(L2!Eltseq(x)) >;
   g := hom<G -> H2 | x :-> H2!Eltseq(x@@pi) >;
   return G, f, g;
end intrinsic;

intrinsic '/'(H2::HomModAbVar, H1::HomModAbVar) -> GrpAb, Map, Map
{The abelian group quotient H_2/H_1, a map from H_2 to this quotient, 
and a lifting map from this quotient to H_2.}
   require H1 subset H2 : "Argument 2 must be a subset of argument 1.";
   return Quotient(H2,H1);
end intrinsic;


intrinsic Index(H2::HomModAbVar, H1::HomModAbVar) -> RngIntElt
{The index of H_1 in H_2, where H_1 and H_2 are both subgroups
of Hom(A,B), for abelian varieties A and B.  }
   Verbose("Index", Sprintf("Index of %o in %o.", H1, H2),"");

   require Domain(H1) eq Domain(H2) : "Arguments 1 and must have the same domain.";
   require Codomain(H1) eq Codomain(H2): "Arguments 1 and must have the same codomain.";
   if not (H1 subset H2) then
      H12 := H1 + H2;
      // TODO: This is simple to code, but might be quite slow?!
      n1 := Index(H12,H1);
      n2 := Index(H12,H2);
      require n2 ne 0 : 
        "Argument 1 must have finite index in the sum of the two arguments.";
      return n1 / n2;
   end if;

   if Dimension(H2) eq 0 then
      return 1;
   end if;
   if Dimension(H1) lt Dimension(H2) then
      return 0;
   end if;
   if IsOverQ(H1) and IsOverQ(H2) then
      if H1 eq H2 then
         return 1;
      else
         return 0;
      end if;
   end if;
   if IsOverQ(H2) then
      return 0;
   end if;
   return #(Lattice(H2)/Lattice(H1));
end intrinsic;



/***************************************************************************

  << Invariants >>

 ***************************************************************************/

function Name(H) 
   // A short string that describes A.
   assert Type(H) eq HomModAbVar;
   if not assigned H`name then
      if Name(H`domain) ne "" and Name(H`codomain) ne "" then
         if H`domain eq H`codomain then
            name := Sprintf("End(%o)",Name(H`domain));
         else
            name := Sprintf("Hom(%o,%o)",
                        Name(H`domain),Name(H`codomain)); 
         end if;
      else
         name := "";
      end if;
      H`name := name;
   end if;
   return H`name;
end function;

procedure SetName(H, name)
   // Set the name of A.
   assert Type(H) eq HomModAbVar;
   assert Type(name) eq MonStgElt;
   H`name := name;
end procedure;


intrinsic FieldOfDefinition(H::HomModAbVar) -> ModAbVar
{A field over which all homomorphisms in H are defined.}
   return H`field_of_definition;
end intrinsic;

intrinsic Domain(H::HomModAbVar) -> ModAbVar
{The domain of the homomorphisms in H.}
   return H`domain;
end intrinsic;

intrinsic Codomain(H::HomModAbVar) -> ModAbVar
{The codomain of the homomorphisms in H.}
   return H`codomain;
end intrinsic;

intrinsic Discriminant(H::HomModAbVar) -> FldRatElt, AlgMatElt 
{The discriminant of H with respect to the trace pairing matrix.  }

   require Domain(H) eq Codomain(H) : "Argument 1 must have the same
   domain and codomain.";

   if not assigned H`discriminant then
      Verbose("Discriminant", Sprintf("Discriminant of %o.", H),"");
      if IsOverQ(H) then
         D, mat := Discriminant(Hom(Domain(H),Codomain(H)) meet H);
      else
         n := Dimension(H);
         mat := MatrixAlgebra(ZZ,n)![Trace(H.i*H.j) : i in [1..n], j in [1..n]];
         D := Determinant(mat);
      end if;
      H`discriminant := <D, mat>;
   end if;
   return Explode(H`discriminant);
end intrinsic;


/***************************************************************************

  << Structural Invariants >>

 ***************************************************************************/

intrinsic Dimension(H::HomModAbVar) -> RngIntElt
{The rank of H as a Z-module or Q-vector space.}
   return #Generators(H);
end intrinsic;

intrinsic Rank(H::HomModAbVar) -> RngIntElt
{The rank of H as a Z-module or Q-vector space.}
   return Dimension(H);
end intrinsic;

intrinsic Ngens(H::HomModAbVar) -> RngIntElt
{The number of generators of H.}
   return Dimension(H);
end intrinsic;

intrinsic '.'(H::HomModAbVar, i::RngIntElt) -> MapModAbVar
{The ith generator of H.}
   requirege i,1;
   require i le Ngens(H) : "Argument 1 must be at most", Ngens(H);
    
   return Basis(H)[i];
end intrinsic;

intrinsic Generators(H::HomModAbVar) -> SeqEnum
{A basis for H.}
   return Basis(H);
end intrinsic;

intrinsic Basis(H::HomModAbVar) -> SeqEnum
{A basis for H.}
   require Characteristic(BaseRing(Domain(H))) eq 0 : "Argument 1 must "*
      "be a hom space for abelian varieties in characteristic 0.";
   if not assigned H`basis then
      Verbose("Basis", Sprintf("Computing basis of %o.", H),"");
      A := Domain(H);  B := Codomain(H);
      if not IsOverQ(H) then  
         if assigned H`is_saturated and H`is_saturated then
            H`basis := Basis_Of_Saturation_From_Over_Q(
                                 Domain(H),Codomain(H),Generators(BaseExtend(H,QQ)));
         elif assigned H`is_hecke_algebra and H`is_hecke_algebra then
            assert IsAttachedToModularSymbols(A);
            H`basis := Basis_For_Hecke_Algebra_Over_Z(A);
         else  
            assert false;   // ut oh -- programming error -- unknown type!
         end if;
      else 
         if assigned H`is_hecke_algebra and H`is_hecke_algebra then
            H`basis := Basis_For_Hecke_Algebra_Over_Q(A);
         elif assigned H`is_full and H`is_full then
            H`basis := Basis_For_HomAB_Tensor_Q(A,B);
         else  
            assert false;   // ut oh -- programming error 
         end if;      
      end if;
   end if;
   assert #H`basis eq 0 or Type(H`basis[1]) eq MapModAbVar;
   return H`basis;
end intrinsic;



/***************************************************************************

  << Matrix and Module Structure >>

 ***************************************************************************/

intrinsic MatrixAlgebra(H::HomModAbVar) -> AlgMat
{The matrix algebra generated by the underlying matrices of all elements
in H, acting on homology.}
   Verbose("MatrixAlgebra", Sprintf("Computing matrix algebra of %o.", H),"");
   require Dimension(Domain(H)) eq Dimension(Codomain(H)) : 
     "Argument 1 must be contained in a ring of endomorphisms.";
    matspace := MatrixAlgebra(IsOverQ(H) select QQ else ZZ,
          Dimension(Homology(Domain(H))));
     alg := sub<matspace|[matspace!Eltseq(IntegralMatrixOverQ(x)) : x in Basis(H)]>;
   return alg;
end intrinsic;

intrinsic RModuleWithAction(H::HomModAbVar) -> ModED
{A module over H equipped with the action of H, where
H must be a ring of endomorphism.}
   require Domain(H) eq Codomain(H) :
     "Argument 1 must be contained in a ring of endomorphisms.";
   return RModule(MatrixAlgebra(H));
end intrinsic;

intrinsic RModuleWithAction(H::HomModAbVar, p::RngIntElt) -> ModED
{A module over H tensor F_p equipped with the action of H tensor F_p, where
H must be a ring of endomorphism that has not been tensored with Q.}
   Verbose("RModuleWithAction", Sprintf("Computing R-module with action of %o.", H),"");
   require Domain(H) eq Codomain(H) : 
     "Argument 1 must be contained in a ring of endomorphisms.";
   require not IsOverQ(H) : "Argument 1 must not be over Q.";
   matspace := MatrixAlgebra(GF(p), Dimension(Homology(Domain(H))));
   alg := sub<matspace|[matspace!Eltseq(IntegralMatrix(x)) : x in Basis(H)]>;
   return RModule(alg);
end intrinsic;

intrinsic RMatrixSpace(H::HomModAbVar) -> ModMatFld
{Matrix space whose basis are the generators for H.}
   if not assigned H`rmatrixspace then
      Verbose("RMatrixSpace", Sprintf("Computing RMatrixSpace of %o.", H),"");
      R := IsOverQ(H) select QQ else ZZ;
      M := RMatrixSpace(R, 
            Dimension(Homology(Domain(H))),Dimension(Homology(Codomain(H))));
      H`rmatrixspace := RMatrixSpaceWithBasis(
                  [M|M!Eltseq(phi) : phi in Generators(H)]);
   end if;
   return H`rmatrixspace;  
end intrinsic;

intrinsic Lattice(H::HomModAbVar) -> Lat
{A lattice with basis obtained from the components of the matrices of a 
basis for H.}
   require not IsOverQ(H) : 
       "Argument 1 must not have been tensored with the rational field.";
   if not assigned H`lattice then
      Verbose("Lattice", "Creating lattice associated to H.","");
      m,n  := MatrixDimensions(H);
      B := [VectorSpace(QQ, m*n) | Eltseq(g) : g in Generators(H)];
      H`lattice := MakeLattice(B);
   end if;
   return H`lattice;
end intrinsic;

intrinsic VectorSpace(H::HomModAbVar) -> ModTupFld
{A vector space with basis obtained from the components of the matrices of a 
basis for H.}
   if not assigned H`vector_space then
      Verbose("VectorSpace", "Creating vector space associated to H.",""); 
      m,n  := MatrixDimensions(H);
      V := VectorSpace(QQ, m*n) ;
      B := [V | Eltseq(g) : g in Generators(BaseExtend(H,QQ))];
      V := VectorSpaceWithBasis(B);
      H`vector_space := V;
   end if;
   return H`vector_space;
end intrinsic;




/***************************************************************************

  << Predicates >>


 ***************************************************************************/

intrinsic 'eq'(H1::HomModAbVar, H2::HomModAbVar) -> BoolElt
{True if H_1 and H_2 are equal.}
   if Domain(H1) ne Domain(H2) then
      return false;
   end if;
   if Codomain(H1) ne Codomain(H2) then
      return false;
   end if;
   if IsOverQ(H1) and (not IsOverQ(H2)) then
      return false;
   end if;
   if IsOverQ(H2) and (not IsOverQ(H1)) then
      return false;
   end if;
   if FieldOfDefinition(H1) cmpne FieldOfDefinition(H2) then
      return false;
   end if;

   if assigned H1`is_full and H1`is_full and assigned H2`is_full and H2`is_full then
      return true;
   end if;
   if assigned H1`is_hecke_algebra and H1`is_hecke_algebra and 
      assigned H2`is_hecke_algebra and H2`is_hecke_algebra then
      return true;
   end if;
   
   if not IsOverQ(H1) then
      return Lattice(H1) eq Lattice(H2);
   end if;
   return VectorSpace(H1) eq VectorSpace(H2);
end intrinsic;

intrinsic 'subset'(H1::HomModAbVar, H2::HomModAbVar) -> BoolElt
{True if H_1 and H_2 are both subgroups of a common Hom(A,B), and
in addition H_1 is a subset of H_2.}
   if Domain(H1) ne Domain(H2) then
      return false;
   end if;
   if Codomain(H1) ne Codomain(H2) then
      return false;
   end if;
   if IsOverQ(H1) and (not IsOverQ(H2)) then
      return false;
   end if;
   if FieldOfDefinition(H1) cmpne FieldOfDefinition(H2) then
      return false;
   end if;

   if assigned H2`is_full and H2`is_full then
      return true;
   end if;
   
   if not IsOverQ(H1) then
      return Lattice(H1) subset Lattice(H2);
   end if;
   return VectorSpace(H1) subset VectorSpace(H2);
end intrinsic;


intrinsic IsField(H::HomModAbVar) -> BoolElt, Fld, Map, Map
{True if H is a field, and if 
so returns that field, a map from the field to H, and a map
from H to the field.}
   Verbose("IsField", Sprintf("Determining whether the homspace %o is a field.",H),"");
   if not IsOverQ(H) then
      return false, 0, 0, 0;
   end if;
   if not IsRing(H) then
      return false, 0, 0, 0;
   end if;
   if not IsCommutative(H) then 
      return false, 0, 0, 0;
   end if;

   A := Domain(H);
   if not IsSimple(A) then
      return false, 0, 0, 0;
   end if;

   // Now we know it is a field.  Let's build it using the primitive element theorem.
   f := PolynomialRing(QQ)!0;
   while Degree(f) lt Dimension(H) do
      phi := RandomHom(H);
      f := MinimalPolynomial(phi);
   end while;
   R := PolynomialRing(QQ);
   K := NumberField(f);
   // Now figure out explicit maps.  One direction is easy and one is harder.
   K_to_H := hom<K -> H | x :-> Evaluate(R!Eltseq(x),phi) >; 

   V := VectorSpace(QQ,Nrows(phi)*Ncols(phi));
   W := VectorSpaceWithBasis([V!Eltseq(phi^i) : i in [0..Dimension(H)-1]]);
   H_to_K := hom<H -> K | x :->  K!Eltseq(Coordinates(W,V!Eltseq(x)))>;

   return true, K, K_to_H, H_to_K;

end intrinsic;

intrinsic IsSaturated(H::HomModAbVar) -> BoolElt
{True if H is equal to its saturation, i.e., the
quotient of the ambient Hom(A,B) by H is torsion free.}
   if not assigned H`is_saturated then
      Verbose("IsSaturated", 
          Sprintf("Determining whether the homspace %o is saturated.",H),"");
      if IsOverQ(H) then
         H`is_saturated := true;
      else
         H2 := Saturation(H);
         if not assigned H`is_saturated then
            H`is_saturated := H eq H2;
         end if;
      end if;
   end if;
   return H`is_saturated;
end intrinsic;

intrinsic IsOverQ(H::HomModAbVar) -> HomModAbVar
{True if H is a Q-vector space instead of just a Z-module, i.e., a space
of homomorphisms up to isogeny.}
   return H`is_over_q;
end intrinsic;

intrinsic IsHeckeAlgebra(H::HomModAbVar) -> BoolElt
{True if H was constructed using the HeckeAlgebra command.  }
   return assigned H`is_hecke_algebra and H`is_hecke_algebra;
end intrinsic;

intrinsic IsRing(H::HomModAbVar) -> BoolElt
{True if H is a ring.  (Note that a ring does not
have to contain unity.)}
   if not assigned H`is_ring then
      H`is_ring := Decide_If_Ring(H);
   end if;
   return H`is_ring;
end intrinsic;

intrinsic IsCommutative(H::HomModAbVar) -> BoolElt
{True if and only if H is a commutative ring.}
   require IsRing(H) : "Argument 1 must be a ring.";
   if not assigned H`is_commutative then
      H`is_commutative := Decide_If_Commutative(H);
   end if; 
   return H`is_commutative;
end intrinsic;




/***************************************************************************

  << Random Element >>

 ***************************************************************************/


function RandomHom(H)
//A random element of H
   RANGE := 9;
   return &+[Random(-RANGE, RANGE) * H.i : i in [1..Ngens(H)]];
end function;

/////////////////////////////////////////////////////////////////////////////
// FUNCTIONS
/////////////////////////////////////////////////////////////////////////////

function Decide_If_Ring(H)
   assert Type(H) eq HomModAbVar;
   if Domain(H) ne Codomain(H) then
      return false;
   end if;
   if (assigned H`is_full and H`is_full) or 
      (assigned H`is_hecke_algebra and H`is_hecke_algebra) then
      return true;
   end if;
   B := Basis(H);
   for g1 in B do
      for g2 in B do
         if not (g1*g2 in H) then
            return false;
         end if;
         if not (g2*g1 in H) then
            return false;
         end if;
      end for;
   end for;            
   return true;
end function;

function Decide_If_Commutative(H)
   assert Type(H) eq HomModAbVar; 
   assert IsRing(H);
   if assigned H`is_hecke_algebra and H`is_hecke_algebra then
      return true;
   end if;

   if assigned H`is_full and H`is_full then  
      A := Domain(H);
      if IsAttachedToNewform(A) then // base case for a recursion
         return Is_Full_EndAf_Commutative(A);
      end if;
      for D in Factorization(A) do
         if #D[2] gt 1 then
            return false;
         elif not Is_Full_EndAf_Commutative(D[1]) then
            return false;
         end if;
      end for;
   end if;

   // generic type:
   B := Basis(H);
   for g1 in B do
      for g2 in B do
         if not (Matrix(g1)*Matrix(g2) eq Matrix(g2)*Matrix(g1)) then
            return false;
         end if;
      end for;
   end for;            
   return true;
end function;




intrinsic Print(H::HomModAbVar, level::MonStgElt)
{}
   printf "%o%oGroup of homomorphisms from %o to %o %o",
          Name(H), Name(H) eq "" select "" else ": ",
          ShortDesc(Domain(H)), ShortDesc(Codomain(H)),
          IsOverQ(H) select "in the category of abelian varieties up to isogeny " else "";
end intrinsic;


intrinsic IsCoercible(H::HomModAbVar, x::.) -> BoolElt, MapModAbVar
{Coerce x into H.}
   m := Dimension(Homology(Domain(H)));
   n := Dimension(Homology(Codomain(H)));
   case Type(x):
      when MapModAbVar:
         if Domain(Parent(x)) eq Domain(H) and 
            Codomain(Parent(x)) eq Codomain(H) then
            if assigned H`is_full and H`is_full then            
               if not IsOverQ(H) and Denominator(x) ne 1 then
                  return false, "Can't coerce into homspace because of denominator.";
               end if;
               z := Copy_MapModAbVar(x);
               z`parent := H;
               return true, z;
            end if;
            if Parent(x) eq H then   // this test is too slow!!!
               x`parent := H;    // weird, but MAGMA wants this (?)
               return true, x;
            end if;
            t, phi := IsCoercible(H, Matrix(x));
            if not t then
               return false, "Incompatible coercion.";
            else
               return true, phi;
            end if;
         end if;
      when RngIntElt, FldRatElt:
         if x eq 0 then
            return true, H!RMatrixSpace(ZZ, m, n)!0;            
         end if;
         if Domain(H) ne Codomain(H) then
            return false, "Domain and range must be the same.";
         end if;
         phi := nIsogeny(Domain(H),x);
         phi`parent := H;
         return true, phi;
      else: 
         M := RMatrixSpace(BaseExtend(H,QQ));
         t, matrix := IsCoercible(M, x);
         if not t then
            return false, "Cannot coerce element into endomorphism ring.";
         end if;
         if not IsOverQ(H) then
            c := Coordinates(M, matrix);
            if LCM([ZZ|Denominator(x) : x in c]) ne 1 then
               return false, "Matrix is only in endomorphism ring tensor Q.";
            end if;
         end if;
         K := Type(x) in {RngIntElt, FldRatElt} select QQ else FieldOfDefinition(H);

/*       phi := Create_MapModAbVar_MultiplyToMorphism(Domain(H), Codomain(H), 
                                   matrix, K);
         if Matrix(phi) ne matrix then
            phi`only_tensor_q := true;
         end if;
*/
/*         if not IsOverQ(H) then    // the following shouldn't happen because of above check.
            if OnlyUpToIsogeny(phi) then  // denominators found!
               return false, "Matrix is only in endomorphism ring tensor Q.";
            end if;
         end if;
*/
         phi := Create_MapModAbVar(Domain(H), Codomain(H),  matrix, K);
         phi`parent := H;
         return true, phi;
   end case;      
   return false, "Illegal coercion";
end intrinsic;




intrinsic 'in'(phi::MapModAbVar, H::HomModAbVar) -> BoolElt
{}
   if Parent(phi) eq H then 
      return true;       
   end if;
   if not (Domain(Parent(phi)) eq Domain(H) and Codomain(Parent(phi)) eq Codomain(H)) then
      return false;
   end if;
   if assigned H`is_full and H`is_full then            
      if not IsOverQ(H) and Denominator(H) ne 1 then
         return false;
      end if;
      return true;
   end if;
   if IsOverQ(H) then
      V := VectorSpace(H);
   else
      V := Lattice(H);
   end if;
   return IsCoercible(V, Eltseq(Matrix(phi)));
end intrinsic;


/*************************************************************

 Computation of a basis for Hom_0(A,B) = Hom(A,B)tensorQ.

 *************************************************************/

function Basis_Change_Matrix_From_Isogeny_Decomposition(DA)
/* A change of matrix from the natural basis for the direct sum of the 
   factors in an isogeny decomposition to the the abelian variety that
   was decomposed. */
   assert Type(DA) eq List;

   X := [* *];
   for D in DA do 
      for phi in D[2] do
         Append(~X,Matrix(phi));
      end for;
   end for;
   return VerticallyStackMatrices(X);
end function;

function Homspace_Tensor_Q_On_Isogeny_Decompositions(DA, DB)
/* Given isogeny decompositions A and B of modular abelian varieties, compute 
   generators for the Q-vector space of isogenies from  sum DA to sum DB. */
   Verbose("Homspace_Tensor_Q_On_Isogeny_Decompositions","",
    Sprintf("DA=%o, DB=%o",DA,DB));
   assert Type(DA) eq List;
   assert Type(DB) eq List;
   if #DA eq 0 or #DB eq 0 then
      return [];
   end if;

   /* Each matrix in the endomorphism ring is m x n, where m is the sum of the dimensions 
      of the newform factors in DA and likewise for DB. */

   m := &+[ZZ|Dimension(Homology(A[1]))*#A[2] : A in DA];
   n := &+[ZZ|Dimension(Homology(B[1]))*#B[2] : B in DB];
   Matrix_Space := RMatrixSpace(QQ,m,n);

   /* It will be useful to have functions to easily make big matrices by 
      thinking of them as smaller ones: */
   A_block_sizes := [ZZ|Dimension(Homology(A[1]))*#A[2] : A in DA];
   B_block_sizes := [ZZ|Dimension(Homology(B[1]))*#B[2] : B in DB];

   A_block_sums := [1, 1+A_block_sizes[1]]; 
   for i in [2..#A_block_sizes] do   
      Append(~A_block_sums,A_block_sums[i]+A_block_sizes[i]);
   end for;
   B_block_sums := [1, 1+B_block_sizes[1]]; 
   for i in [2..#B_block_sizes] do   
      Append(~B_block_sums,B_block_sums[i]+B_block_sizes[i]);
   end for;

   function Create_Matrix(i,r, j,s, T)
      // i=i-th block of A, r=r-th factor in i-th block.
      // j=j-th block of B, s=s-th factor in j-th block.
      // creates matrix that is composition
      /*   
         prod A_k -->  r-th factor (A_i x... x A_i) -- T --> s-th factor (B_j x ... x B_j) ---> prod B_k
      */
      M := Matrix_Space!0;
      x := A_block_sums[i] + (r-1)*Dimension(Homology(DA[i][1])) ;
      y := B_block_sums[j] + (s-1)*Dimension(Homology(DB[j][1])) ;

      for r in [1..Nrows(T)] do
         for c in [1..Ncols(T)] do
            M[x+r-1,y+c-1] := T[r,c];
         end for;
      end for;
      return M;
   end function;

   G := [];  // sequence of generators, which we build up as we find them.

   /* For each A isogeny class in DA, we check if that isogeny class occurs as a DB.
      If so, we ask another function for matrices that are a basis for End(A).  We
      then create corresponding generators in Hom space.   Note that we have a five-level
      nested for loop below.  The complexity of this in general could be nasty. */
   for i in [1..#DA] do A := DA[i][1]; phiA := DA[i][2];
      for j in [1..#DB] do B := DB[j][1]; phiB := DB[j][2];
         if IsIsogenous(A, B) then  // found one
            E   := Basis_for_EndomorphismMatrixAlgebra_of_Af(A); // only compute since we end up needing it
            iso := NaturalMap(A, B);  
            // These are the "elements" for the block of the matrix corresponding to Hom(A^*,B^*).
            F := [e*iso : e in E];
            for r in [1..#phiA] do      
               for s in [1..#phiB] do   
                  for T in F do 
                     g := Create_Matrix(i,r, j,s, T); 
                     Append(~G, g);
                  end for;
               end for;
            end for;

            break; // no need to consider any other B, since they are all
                   // guaranteed non-isogenous
         end if;
      end for;       
   end for;
 
   return G;
   
end function;

//   



function Basis_For_HomAB_Tensor_Q(A, B)
   Verbose("Basis_For_HomAB_Tensor_Q","",
            Sprintf("A=%o, B=%o",A,B));
   assert Type(A) eq ModAbVar;
   assert Type(B) eq ModAbVar;

   Verbose("Basis_For_HomAB_Tensor_Q", Sprintf("A = %o, B = %o",A,B), "");

   DA := Factorization(A);
   DB := Factorization(B);

   Hom_DA_to_DB := Homspace_Tensor_Q_On_Isogeny_Decompositions(DA, DB);
   DA_to_A      := Basis_Change_Matrix_From_Isogeny_Decomposition(DA);
   if A eq B then
      DB_to_B   := DA_to_A;
   else
      DB_to_B   := Basis_Change_Matrix_From_Isogeny_Decomposition(DB);
   end if;
     
   A_to_DA := DA_to_A^(-1);
   return [Hom(A,B,true) | Create_MapModAbVar(A,B,
                                        A_to_DA * T * DB_to_B, 
           BaseRing(A)) : T in Hom_DA_to_DB];
end function;


function Basis_Of_Saturation_From_Over_Q(A,B, X)
   Verbose("Basis_Of_Saturation_From_Over_Q","",
            Sprintf("A=%o, B=%o, X=%o",A,B,X));

   assert Type(A) eq ModAbVar;
   assert Type(B) eq ModAbVar;
   assert Type(X) eq SeqEnum;

   if IsVerbose("ModAbVar") then
      Verbose("Basis_Of_Saturation_From_Over_Q", 
            Sprintf("of Hom(A,B), where A = %o, B = %o",A,B),
            Sprintf(", basis = %o",[Matrix(x) : x in X]));
   end if;

   if #X eq 0 then
      return X;
   end if;
   m := Nrows(X[1]);
   n := Ncols(X[1]);
   
   // Find intersection of Q-space spanned by X with all integer matrices.
   V  := VectorSpace(QQ, m*n);
   C1 := BasisChange_Lattice_to_Rational(Homology(A));
   C2 := BasisChange_Rational_to_Lattice(Homology(B));
   
   VX := sub<V|[V!Eltseq(C1*Matrix(x)*C2) : x in X]>;
   Y  := Basis(RMatrixSpace(ZZ,m,n));
   MmnZ := [V!Eltseq(x) : x in Y];
   MmnQ := RMatrixSpace(QQ,m,n);
   L := [MmnQ!Eltseq(x) : x in Basis(SaturateWithRespectToBasis(VX,MmnZ))];

   C1 := BasisChange_Rational_to_Lattice(Homology(A));
   C2 := BasisChange_Lattice_to_Rational(Homology(B));

   L := [Hom(A,B)|Create_MapModAbVar(A,B,C1*T*C2,BaseRing(A)) : T in L];

   return L;

end function;


