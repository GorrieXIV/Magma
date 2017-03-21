freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: subgrp.m
   DESC: Basic ModAbVarSubGrp functionality.
         These are finitely generated subgroups of modular abelian varieties.

   Creation: 06/16/03 -- initial creation
      
 ***************************************************************************/

/*
HANDBOOK_TITLE: Subgroups of Modular Abelian Varieties
*/

import "elt.m":
   IsOverQ,
   PutInCommonParent ;

import "homology.m":
   Create_ModAbVarHomol;

import "linalg.m":
   Intersect_Vector_Space_With_Lattice,
   MakeLattice;

import "misc.m":
   FactorPrint,
   OddPart;

import "modabvar.m":
   Create_ModAbVar,
   Verbose;

import "morphisms.m":
   Create_MapModAbVar;

import "rings.m":
   QQ,
   CommonFieldOfDefinition,
   OverField;

forward
   ComputeGroupStructure,
   Create_ModAbVarSubGrp,
   Name,
   SetName;

declare type ModAbVarSubGrp;

declare attributes ModAbVarSubGrp:
   abgroup,                       // an abelian group isomorphic to this object
   from_abgroup,                  // isomorphism from this group to abelian group
   to_abgroup,                    // isomorphism from abelian group to this group
   field_of_definition,           
   ambient_variety,               // where the points of this group law.
   generators,                    // modular abelian variety elements that generate the group
   over_Q,                        // all generators are in rational homology, so we
                                  // can compute group structure, etc. 
   name;


/***************************************************************************

  << Creation >>

 ***************************************************************************/

intrinsic nTorsionSubgroup(A::ModAbVar, n::RngIntElt) -> ModAbVarSubGrp
{The kernel A[n] of the multiplication by n isogeny on A.}
   Verbose("nTorsionSubgroup", 
      Sprintf("Computing %o-torsion subgroup of A=%o.",n,A),"");
   return Kernel(nIsogeny(A,n));
end intrinsic;

intrinsic nTorsionSubgroup(G::ModAbVarSubGrp, n::RngIntElt) -> ModAbVarSubGrp
{The kernel G[n] of the multiplication by n homomorphism on G.}
   /* TODO:
     "Using stupid possibly very slow but simple algorithm in
     nTorsionSubgroup(G::ModAbVarSubGrp, n::RngIntElt) ->
     ModAbVarSubGrp"; */

   Verbose("nTorsionSubgroup", 
      Sprintf("Computing %o-torsion subgroup of G=%o.",n,G),"");
   An := nTorsionSubgroup(AmbientVariety(G),n);
   return An meet G;

end intrinsic;


intrinsic ApproximateByTorsionGroup(G::ModAbVarSubGrp : Cutoff := 10^3) 
         -> ModAbVarSubGrp
{The subgroup generated by torsion approximations of a
set of generators of G.}
   Verbose("ApproximateByTorsionGroup",
      Sprintf("Approximating G=%o by exact torsion subgroup.",G),"");
   generators := [ApproximateByTorsionPoint(x : Cutoff := Cutoff) : 
                    x in Generators(G)];
   return Subgroup(generators);
end intrinsic;

intrinsic ZeroSubgroup(A::ModAbVar) -> ModAbVarSubGrp
{The zero subgroup of the abelian variety A.}
   G := New(ModAbVarSubGrp);
   G`field_of_definition := QQ;
   G`ambient_variety := A;
   G`generators := [];
   G`over_Q := true;
   G`name := "{ 0 }";
   ComputeGroupStructure(G);
   return G;  
end intrinsic;

intrinsic Subgroup(X::[ModAbVarElt]) -> ModAbVarSubGrp
{The subgroup of A generated by 
the nonempty sequence X of elements of a modular abelian variety.}
   Verbose("Subgroup",
      Sprintf("Creating finitely generated subgroup of abelian variety generated by %o.",X),"");
   return Create_ModAbVarSubGrp(X);
end intrinsic;


/***************************************************************************

  << Elements >>

 ***************************************************************************/

intrinsic Elements(G::ModAbVarSubGrp) -> SeqEnum
{Sequence of all elements of the finite subgroup G of a modular
abelian variety.}
   Verbose("Elements",
      Sprintf("Creating sequence of all elements of G=%o.",G),"");
   require assigned G`abgroup : "Group structure of argument 1 not known.";
   return [G`from_abgroup(x) : x in G`abgroup];
end intrinsic;

intrinsic Ngens(G::ModAbVarSubGrp) -> RngIntElt
{The number generators of G.}
   return #G`generators;
end intrinsic;

intrinsic Generators(G::ModAbVarSubGrp) -> SeqEnum
{Sequence of generators of G.  These correspond to generators for the
underlying abelian group.}
   return G`generators;
end intrinsic;

intrinsic '.'(G::ModAbVarSubGrp, i::RngIntElt) -> ModAbVarElt
{The i-th generator of G.}
   requirege i,1;
   require i le #G`generators : "Argument 2 must be between 1 and", #G`generators;
   return G`generators[i];
end intrinsic;



/***************************************************************************

  << Arithmetic >>

 ***************************************************************************/

intrinsic Quotient(A::ModAbVar, G::ModAbVarSubGrp) -> ModAbVar, MapModAbVar
{Quotient of the abelian variety A by the finite subgroup G, the
isogeny A -> A/G and an isogeny A/G -> A, such that composition of the
two isogenies is multiplication by the exponent of G.}
   Verbose("Quotient",
      Sprintf("Computing quotient A/G, where A=%o and G=%o.",A,G),"");

   require IsFinite(G) : "Argument 1 must be finite.";
   require A eq AmbientVariety(G) : "Argument 1 must equal the ambient variety of argument 2.";
   return Quotient(G);
end intrinsic;


intrinsic Quotient(G::ModAbVarSubGrp) -> ModAbVar, MapModAbVar, MapModAbVar
{The quotient A/G, where A is the ambient variety of G, an isogeny
from A to A/G with kernel G, and an isogeny from A/G to A such that
the composition of the two isogenies is multiplication by the exponent
of G.}
   Verbose("Quotient",
      Sprintf("Computing quotient A/G, where G=%o.",G),"");
   require IsFinite(G) : "Argument 1 must be finite.";
   L := Lattice(G);
   H := Create_ModAbVarHomol(L);
   A := AmbientVariety(G);
   if Name(G) ne "" and Name(A) ne "" then
      name := Sprintf("%o/%o", Name(A), Name(G));
   else   
      name := "";
   end if;
   K := CommonFieldOfDefinition([* A, G *]);
   R := OverField([* K, BaseRing(A) *]);
   em := ModularEmbedding(A);
   pi := ModularParameterization(A);

   A_to_Q := MatrixAlgebra(QQ,Dimension(H))!1;
   Q_to_A := MatrixAlgebra(QQ,Dimension(H))!Exponent(G);
   J_K := BaseExtend(Codomain(em),K);
   J := <J_K, Q_to_A*Matrix(em), Matrix(pi)*A_to_Q>;

   Q := Create_ModAbVar(name, H, K, R, J);

   A_K := BaseExtend(A,K);
   f := Create_MapModAbVar(A_K, Q, A_to_Q, K);
   g := Create_MapModAbVar(Q, A_K, Q_to_A, K);
   return Q, f, g;
end intrinsic;

intrinsic '/'(A::ModAbVar, G::ModAbVarSubGrp) -> ModAbVar,
MapModAbVar, MapModAbVar
{The quotient A/G, the isogeny A\to A/G with kernel G,
and an isogeny A/G\to A.}
   if A eq AmbientVariety(G) then
      return Quotient(G);
   end if;
   if not IsFinite(G) then
      require false : "Argument 2 must be finite.";
   end if;
   t, E := FindCommonEmbeddings([AmbientVariety(G), A]);   
   require t : "Not enough embeddings known to intersect arguments 1 and 2.";
   return A/(G meet A);
end intrinsic;

intrinsic '+'(G1::ModAbVarSubGrp, G2::ModAbVarSubGrp) -> ModAbVarSubGrp
{The sum of the subgroups groups G_1 and G_2 of abelian varieties A_1
and A_2.  If A_1 is not equal to A_2, then G_1 and G_2 are replaced by
their image in a common abelian variety.}
   Verbose("+", Sprintf("Computing sum of subgroups %o and %o.", G1, G2),"");
   A1 := AmbientVariety(G1);
   A2 := AmbientVariety(G2);
   if A1 eq A2 then
      return Subgroup(Generators(G1) cat Generators(G2));
   end if;
   E, _ := CommonModularStructure([A1, A2]);
   return E[1](G1) + E[2](G2);
end intrinsic;

intrinsic 'meet'(G1::ModAbVarSubGrp, G2::ModAbVarSubGrp) -> ModAbVarSubGrp
{The intersection of the finite subgroups G_1 and G_2 of an abelian
variety.  If their ambient varieties are not equal, G_1 and G_2 are replaced by
their image in a common abelian variety.}
   Verbose("meet", Sprintf("Computing intersection of subgroups %o and %o.", G1, G2),"");
   /* Algorithm:
        Let L be the integral homology of the ambient variety.
         (1) Compute L1 := L + reps for generators of G1.
         (2) Compute L2 := L + reps for generators of G2
         (3) Compute L12 := L1 meet L2
         (4) Compute generators for the finite quotient L12 / L.
         (5) Lifts of these generators generator G1 meet G2.
    */
   require G1`over_Q and G2`over_Q : "Arguments 1 and 2 must be torsion groups.";
   if AmbientVariety(G1) eq AmbientVariety(G2) then
      L := IntegralHomology(AmbientVariety(G1));
      L1 := Lattice(G1);
      L2 := Lattice(G2);
      L12 := L1 meet L2;
      Q, pi := L12/L;
      gens := [AmbientVariety(G1)!(g@@pi) : g in Generators(Q)];
      if #gens eq 0 then
         return ZeroSubgroup(AmbientVariety(G1));
      end if;
      return Subgroup(gens);
   end if;
   t, E := FindCommonEmbeddings([AmbientVariety(G1), AmbientVariety(G2)]);
   require t : "Not enough embeddings known to intersect arguments 1 and 2.";
   for phi in E do 
      if not IsInjective(phi) then
         require false : "Not enough injective embeddings known to intersect.";
      end if;
   end for;
   return E[1](G1) meet E[2](G2);
end intrinsic;

intrinsic 'meet'(G::ModAbVarSubGrp, A::ModAbVar) -> ModAbVarSubGrp
{The intersection of the finite subgroup G of an abelian variety
B with the abelian variety A.  If A is not equal to B, then G and A
are replaced by their image in a common abelian variety.}
   Verbose("meet", Sprintf("Computing intersection of G and A, where G=%o and A=%o.", G, A),"");
   if A eq AmbientVariety(G) then
      return G;
   end if;
   require G`over_Q : "Arguments 1 must be a torsion group.";   
   t, E := FindCommonEmbeddings([AmbientVariety(G), A]);   
   require t : "Not enough embeddings known to intersect arguments 1 and 2.";
   G := E[1](G);
   e := E[2];
   J := Codomain(e);
   B := Image(e);
   V := VectorSpaceWithBasis(Rows(e));
   LGV := Intersect_Vector_Space_With_Lattice(V, Lattice(G));
   LJ  := IntegralHomology(Codomain(e));
// AKS, 23/6/06; seems necessary:
if Type(LGV) ne Lat then
    LGV := Lattice(LGV);
end if;
   Q,pi := LGV/(LJ meet LGV);
   H := Subgroup([A!Coordinates(V,V!x@@pi) : x in Q]);
   H`field_of_definition := CommonFieldOfDefinition([* G, A *]);
   return H;
end intrinsic;

intrinsic 'meet'(A::ModAbVar, G::ModAbVarSubGrp) -> ModAbVarSubGrp
{The intersection of the finite subgroup G of an abelian variety
B with the abelian variety A.  If A is not equal to B, then G and A
are replaced by their image in a common abelian variety.}
   return G meet A;
end intrinsic;

/***************************************************************************

  << Underlying Abelian Group and Lattice >>
 
 ***************************************************************************/

intrinsic AbelianGroup(G::ModAbVarSubGrp) -> GrpAb, Map, Map
{An abstract abelian group H isomorphic to G, a map from H to G,
and a map from G to H.}
   /* TODO */
   require G`over_Q : "Argument 1 contains elements that we are not sure lie in the "*
                      "rational homology, and William Stein has not implemented an "*
                      "algorithm for computing the group structure in this case (because"*
                      "he doesn't know one).";
   if not assigned G`abgroup then
      ComputeGroupStructure(G);
   end if;
   require assigned G`abgroup : "Don't know how to compute group structure of argument 1.";
   return G`abgroup, G`from_abgroup,G`to_abgroup;
end intrinsic;

intrinsic Lattice(G::ModAbVarSubGrp) -> Lat
{Given a finite torsion subgroup G with ambient abelian variety A
where G is generated by elements of H_1(A,Q)/H_1(A,Z), return the lattice
generated by the coset representatives of H_1(A, Z)}
   Verbose("Lattice", Sprintf("The lattice in rational homology associated to G=%o.",G), "");
   require G`over_Q : "Argument 2 must be generated by elements of rational homology.";
   A := AmbientVariety(G);
   L := IntegralHomology(A);
   M := MakeLattice([Element(g) : g in Generators(G)]);
   if Dimension(M) eq 0 then
      return L;
   end if;
   return M+L;
end intrinsic;



/***************************************************************************

  << Invariants >>

 ***************************************************************************/


function Name(G)
   // A short string that describes G.
   assert Type(G) eq ModAbVarSubGrp;
   return G`name;
end function;

procedure SetName(G, name)
   // Set the short string that describes G.
   assert Type(name) eq MonStgElt;
   G`name := name;
end procedure;

intrinsic '#'(G::ModAbVarSubGrp) -> RngIntElt
{The number of elements in G.}
   return #AbelianGroup(G);
end intrinsic;

intrinsic Order(G::ModAbVarSubGrp) -> RngIntElt
{The number of elements in G.}
   return #G;
end intrinsic;

intrinsic Exponent(G::ModAbVarSubGrp) -> RngIntElt
{An integer that kills G.  We assume G is finite.}
   require IsFinite(G) : "Argument 1 must be finite.";
   return Exponent(AbelianGroup(G));
end intrinsic;

intrinsic Invariants(G::ModAbVarSubGrp) -> SeqEnum
{Invariants of G as a finite abelian group.}
   if not assigned G`abgroup then
      ComputeGroupStructure(G);
   end if;
   require assigned G`abgroup : "Don't know how to compute group structure of argument 1.";
   return Invariants(AbelianGroup(G));
end intrinsic;


intrinsic FieldOfDefinition(G::ModAbVarSubGrp) -> Fld
{A field over which the group G is defined (this is not guaranteed
to be minimal!).}
   return G`field_of_definition;
end intrinsic;

intrinsic AmbientVariety(G::ModAbVarSubGrp) -> ModAbVar
{Abelian variety that contains G.}
   return G`ambient_variety;
end intrinsic;

                      
/***************************************************************************

  << Predicates and Comparisons >>

 ***************************************************************************/
intrinsic 'eq'(G1::ModAbVarSubGrp, G2::ModAbVarSubGrp) -> BoolElt
{True if G_1 equals G_2.}
   if AmbientVariety(G1) eq AmbientVariety(G2) then
      if Ngens(G1) ne Ngens(G2) then
         return false;
      end if;
      same_gens := true;
      for i in [1..Ngens(G1)] do
         if Generators(G1)[i] ne Generators(G2)[i] then
            same_gens := false;
            break;
         end if;
      end for;
      if same_gens then
         return true;
      end if;
   end if;

   // Check if we can use "meet" to decide equality.
   t, E := FindCommonEmbeddings([AmbientVariety(G1), AmbientVariety(G2)]);
   require t : "Not enough embeddings known to intersect arguments 1 and 2.";
   for phi in E do 
      if not IsInjective(phi) then
         require false : "Not enough injective embeddings known to intersect.";
      end if;
   end for;
   return #(G1 meet G2) eq #G2;
end intrinsic;

intrinsic 'subset'(G1::ModAbVarSubGrp, G2::ModAbVarSubGrp) -> BoolElt
{True if G1 is a subset of G2.}
   if IsFinite(G1) and #G1 eq 1 then
      return true;
   end if;
   if AmbientVariety(G1) eq AmbientVariety(G2) then
      return Lattice(G1) subset Lattice(G2);
   end if;

   // Check if we can use "meet" to decide equality.
   t, E := FindCommonEmbeddings([AmbientVariety(G1), AmbientVariety(G2)]);
   require t : "Not enough embeddings known to decide inclusion.";
   for phi in E do 
      if not IsInjective(phi) then
         require false : "Not enough injective embeddings known to intersect.";
      end if;
   end for;
   n := #(G1 meet G2);
   m := #G1;
   if IsEven(m) or IsEven(#G2) or Sign(AmbientVariety(G1)) eq 0 then
      return n eq m;
   end if;
   return OddPart(n) eq OddPart(m);
end intrinsic;

intrinsic 'subset'(G::ModAbVarSubGrp, A::ModAbVar) -> BoolElt
{True if G is a subset of the abelian variety A.}
   if AmbientVariety(G) eq A then 
      return true;
   end if;
   if not IsFinite(G) then
      return false;
   end if;

   // Now try to use embeddings:
   t, E := FindCommonEmbeddings([A, AmbientVariety(G)]);
   if not t then
      return false;
   end if;
   if not IsInjective(E[1]) and IsInjective(E[2]) then
      return "No way to compare A and G.";
   end if;
   n := #(E[1](A) meet E[2](G)) ;
   m := #E[2](G);
   if IsEven(m) or Sign(A) eq 0 then
      return n eq m;
   end if;
   return OddPart(n) eq OddPart(m);
end intrinsic;

intrinsic 'subset'(A::ModAbVar, G::ModAbVarSubGrp) -> BoolElt
{True if the abelian variety A is a subset of the finitely generated
group G.  }
   return Dimension(A) eq 0;
end intrinsic;

intrinsic IsFinite(G::ModAbVarSubGrp) -> RngIntElt
{True if G is known to be finite, e.g., generated by 
torsion elements.  }
   return G`over_Q;
end intrinsic;




function Create_ModAbVarSubGrp(gens)
   assert Type(gens) eq SeqEnum;
   if #gens eq 0 or Dimension(Parent(gens[1])) eq 0 then
      return ZeroSubgroup(ZeroModularAbelianVariety());
   end if;
   assert Type(gens[1]) eq ModAbVarElt;
   G := New(ModAbVarSubGrp);
   G`field_of_definition := CommonFieldOfDefinition(gens);
   G`ambient_variety := Parent(gens[1]);
   G`generators := gens;
   G`over_Q := &and[IsOverQ(x) : x in gens];
   G`name := "";
   if G`over_Q then
      ComputeGroupStructure(G);
   end if;
   return G;  
end function;

procedure ComputeGroupStructure(G)
   Verbose("ComputeGroupStructure", Sprintf("Computing group structure of G=%o.",G), "");
   assert Type(G) eq ModAbVarSubGrp;
   assert G`over_Q;
   if assigned G`abgroup then
      return;
   end if;
   // find explicit subgroup of ambient_variety generators by generators.
   /* Algorithm: 
       (1) Construct lattice L generated by all integral homology I and the 
           rational homology classes that represent each generator. 
       (2) Using MAGMA quo to compute explicitly L/I and a map L --> L/I 
       (3) Map comes with lifting function, and this is what we need. */

   I := IntegralHomology(G`ambient_variety);
   B := Basis(I) cat [g`element : g in G`generators];
   L := MakeLattice(B);
   if Dimension(L) eq 0 then
      // zero-dimensional lattices aren't allowed in MAGMA, so I have
      // to fake some stuff. 
      G`abgroup := AbelianGroup([]);
      G`from_abgroup := hom<G`abgroup -> G`ambient_variety | x :-> G`ambient_variety!0>;
      G`to_abgroup := hom<G`ambient_variety -> G`abgroup | x :-> G`abgroup!0>;
      G`generators := [G`ambient_variety|];
      return;
   end if;   
   G`abgroup, phi := L/I;
   V := RationalHomology(G`ambient_variety);
   G`from_abgroup := hom<G`abgroup -> G`ambient_variety | x :-> G`ambient_variety!(V!(x@@phi))>;
   G`to_abgroup := hom<G`ambient_variety -> G`abgroup | x :-> phi(x`element)>;
   G`generators := [G`ambient_variety|G`from_abgroup(x) : x in Generators(G`abgroup)];
   
end procedure;

intrinsic Print(G::ModAbVarSubGrp, level::MonStgElt)
{}
   printf "%oinitely generated subgroup of abelian variety%o", 
          Name(G) ne "" select Sprintf("%o: f",Name(G)) else "F",
         (assigned G`abgroup select Sprintf(" with invariants %o",Invariants(G)) else "");
end intrinsic;

intrinsic 'in'(x::ModAbVarElt, G::ModAbVarSubGrp) -> BoolElt
{True if x is an element of G.  If the ambient variety of x is
different than the ambient variety of G, then use Embeddings to
attempt to find a common abelian variety that contains (up to isogeny)
both and check inclusion of images.}
   require G`over_Q : "Argument 2 must be generated by elements of rational homology.";
   A := AmbientVariety(G);
   if Parent(x) ne A then
      // Try to find common embedding:
      B := Parent(x);
      X := [A,B];
      t, E := FindCommonEmbeddings(X);
      if not t then 
         return false;
      end if;
      return E[2](x) in E[1](G);
   end if;
   // Make lattice generated by integral homology of A and generator of G.
   // Ask if x is in this lattice.
   L := Lattice(G);
   if IsOverQ(x) then 
      return Element(x) in L;
   end if;
   _, d := ClosestVectors(L, Element(x));
   return Abs(d) lt 10^(-Parent(x)`point_precision);
end intrinsic;

