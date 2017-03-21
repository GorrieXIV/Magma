freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: decomp.m
   DESC: Decomposition of modular abelian varieties as products, up to isogeny.

 ***************************************************************************/

/*
HANDBOOK_TITLE: Decomposing and Factoring Abelian Varieties


*/

import "complements.m":
   CanUseIntersectionPairing,
   ComplementsAreGuaranteedOrthogonal,
   FindHomologyDecompositionOfSubspaceUsingDecomposition;

import "homology.m":
   AllModularSymbolsSpacesAreFull,
   Create_ModAbVarHomol,
   DimensionQ,
   HeckeTraces,
   HomologyLevel,
   ModSymMap_to_HomologyMatrix,
   ModSymMatrix_to_HomologyMatrix;

import "linalg.m":
   RestrictionOfScalars,
   VerticallyStackMatrices;

import "misc.m":
   NoSpaces,
   IsSquareFree;

import "modabvar.m":
   AllCharactersTrivial,
   Create_ModAbVar,
   Create_ModAbVar_ModSym,
   Name, 
   SetName,
   Verbose;

import "morphisms.m":
   Create_MapModAbVar,
   Create_MapModAbVar_Name,
   Create_MapModAbVar_MultiplyToMorphism;

import "rings.m":
   QQ, ZZ,
   IsNumberField,
   OverField;

forward
   Create_Af_and_Homs,
   DegeneracyMatrixQ_From_ModSym,
   DegeneracyMatrixQ_ModSym,
   DegeneracyMatrixQ_To_ModSym,
   Homology_NewformDecomposition,
   LabelNewformSpace,
   Newform_ModularAbelianVariety_Decomposition_of_ModSym_AbVar,
   SeenThisAfBefore,
   ToIsogenyCode,
   noexport_Decomposition_from_Af;


NOT_YET_PROGRAMMED_MESG := "Decomposition for this modular abelian variety is not yet programmed.  " * 
       "If this error occurs with a big traceback, it is not a bug.  The problem is that " *
       "good algorithms for decomposing abelian varieties over fields other than Q either " * 
       "don't exist or haven't been implemented yet.   Also many computations use, at some point, " * 
       "a simple decomposition, and this might explain surprising arrival at this error message.";

/* Extend this in a future version. */
function IsAllowedField(A)
   K := BaseRing(A);
   if Characteristic(K) ne 0 then
      return false;
   end if;
   if Type(K) eq FldRat then
      return true;
   end if;
   for eps in DirichletCharacters(A) do 
      if not IsTrivial(eps) then
         return false;
      end if;
   end for;
   N := Level(A);
   return N eq SquarefreeFactorization(N);
end function;

/***************************************************************************

  << Decomposition >>


 ***************************************************************************/

intrinsic Decomposition(A::ModAbVar) -> SeqEnum
{A sequence of isogeny simple
abelian subvarieties of A whose product is isogenous to A.  Each is
equipped with an embedding into A.}
   require IsAllowedField(A) : 
        NOT_YET_PROGRAMMED_MESG;
   if not assigned A`decomposition then
      Verbose("Decomposition", Sprintf("Decomposing A=%o as product of simples.", A),"");
      if Dimension(A) eq 0 then
         A`decomposition := [A];
         return A`decomposition;
      end if;
      DA := Factorization(A);
      X := [];
      for D in DA do
         for phi in D[2] do
            B := phi(D[1]);
            if Name(D[1]) ne "" then
               if #D[2] gt 1 and Name(phi) ne "" then
                  name := Sprintf("%o(%o)",Name(phi),Name(D[1]));
               else
                  name := Name(D[1]);
               end if;
               if not IsAttachedToModularSymbols(A) then
                  name := Sprintf("image(%o)",name);
               end if;
               SetName(B,name);
            end if;
            B`is_Af := <D[1],SurjectivePart(phi)>;
            Append(~X,B);
         end for;
      end for;
      A`decomposition := X;
   end if;
   return A`decomposition;
end intrinsic;

intrinsic '@'(n::RngIntElt, A::ModAbVar) -> ModAbVar
{The nth factor in Decomposition(A), denoted A(n).}
   require IsAllowedField(A) : 
      NOT_YET_PROGRAMMED_MESG;
   D := Decomposition(A);
   require n ge 1 and n le #D : "Argument 1 must be positive and at most", #D;
   return D[n];
end intrinsic;


/***************************************************************************

  << Factorization >>


 ***************************************************************************/

intrinsic Factorization(A::ModAbVar) -> List
{Factorization of A as a product with multiplicities
of abelian varieties B=A_f attached to newforms.  }
   require IsAllowedField(A) : 
     NOT_YET_PROGRAMMED_MESG;

   if not assigned A`isogeny_decomp then
      Verbose("Factorization", 
       Sprintf("Computing factorization of A as a product of simples, where A=%o.",A),"");
      if IsAttachedToModularSymbols(A) then
         A`isogeny_decomp := 
            Newform_ModularAbelianVariety_Decomposition_of_ModSym_AbVar(A);
      else
         i := ModularEmbedding(A);
         J := Codomain(i);
         V := Image(Matrix(i));
         D, _, A`only_maximal_newform_blocks :=  
               FindHomologyDecompositionOfSubspaceUsingDecomposition(J, V);
         K := OverField([* BaseRing(A) *]);
         // Now everything is done, except we need to turn the maps 
         // in D into homomorphisms of abelian varieties. 
         E := [* *];
         for j in [1..#D] do 
            C, PHI := Explode(D[j]);
            PHI2 := [];
            for phi in PHI do
               // Use phi to construct a matrix that defines a linear
               // map H_1(C,Q) --> H_1(A,Q) that sends H_1(C,Z) into H_1(A,Z).
               // We want unique X such that X*[i] = [phi]. 
               C_to_A := Solution(Matrix(i),phi);
               Append(~PHI2,Create_MapModAbVar_MultiplyToMorphism(C,A, C_to_A, K));
            end for;
            Append(~E,<C,PHI2>);
         end for;
         A`isogeny_decomp := E;
      end if;
   end if;
   return A`isogeny_decomp;
end intrinsic;


function ToIsogenyCode(n)
   // Returns the n-th isogeny coding.  The coding goes A,B,C,...,Z,AA,BB,...
   if n eq 0 then return "?"; end if;
   return &cat[CodeToString(65+((n-1)mod 26)): i in [0..((n-1) div 26)]];
end function;


function DegeneracyMatrixQ_ModSym(modsym,i,MN,d,from)
   assert Type(modsym) eq SeqEnum;
   assert Type(i) eq RngIntElt;
   assert i le #modsym;
   assert #modsym eq 0 or i ge 1;
   assert Type(d) eq RngIntElt;

   MN := AmbientSpace(MN);
   M := modsym[i];
   n := &+[ZZ|DimensionQ(AmbientSpace(M)) : M in modsym];
   assert (Level(MN) mod Level(M) eq 0) or (Level(M) mod Level(MN) eq 0);
   
   if from then  // add zero rows
      degen := RestrictionOfScalars(DegeneracyMatrix(AmbientSpace(M),MN,d));
      psi := RMatrixSpace(QQ,n,Ncols(degen))!0;
      start := &+[ZZ|DimensionQ(AmbientSpace(modsym[j])) : j in [1..i-1]] + 1;
      stop  := start+DimensionQ(AmbientSpace(modsym[i]))-1;
      for r in [start..stop] do
         psi[r] := degen[r-start+1];
      end for;
   else          // add zero columns
      degen := Transpose(RestrictionOfScalars(DegeneracyMatrix(MN,AmbientSpace(M),d)));
      psi := RMatrixSpace(QQ,n,Ncols(degen))!0;      
      start := &+[ZZ|DimensionQ(AmbientSpace(modsym[j])) : j in [1..i-1]] + 1;
      stop  := start+DimensionQ(AmbientSpace(modsym[i])) - 1;
      for r in [start..stop] do
         psi[r] := degen[r-start+1];
      end for;
      psi := Transpose(psi);   // transposes because only know how to set rows in MAGMA.
   end if;
   return psi;
end function;

function DegeneracyMatrixQ_To_ModSym(modsym,i,MN,d)
   return DegeneracyMatrixQ_ModSym(modsym,i,MN,d, false);
end function;

function DegeneracyMatrixQ_From_ModSym(modsym,i,MN,d)
   return DegeneracyMatrixQ_ModSym(modsym,i,MN,d, true);
end function;

function SeenThisAfBefore(D, name)
   for j in [1..#D] do 
      if D[j][3] eq name then
         return j;
      end if;
   end for;
   return 0;
end function;

function LabelNewformSpace(M, n)
   eps := DirichletCharacter(M);
   eps_label := IsTrivial(eps) select "" else NoSpaces(Sprintf("%o",Eltseq(eps)));
   return Sprintf("%o%o%o%o",Level(M),
         (Weight(M) eq 2 select "" else Sprintf("k%o",Weight(M))),
         ToIsogenyCode(n),eps_label);
end function;

function Homology_NewformDecomposition(H)
   assert Type(H) eq ModAbVarHomol;
   assert assigned H`modsym;

   Verbose("Homology_NewformDecomposition", Sprintf("HOMOLOGY: Decomposition of %o", H), "");

   modsym := H`modsym;
   D := [* *];
   zero := [* *];
   for M in modsym do
      Append(~zero, M!0);
   end for;
   con := 0;
   for i in [1..#modsym] do
      M := modsym[i];
      Verbose("Homology_NewformDecomposition", 
             Sprintf("Decomposing space %o (of %o): %o\n", i, #modsym, M), "");
      // For each divisor of the level of M, compute the new subspace of corresponding
      // modular symbols space, find its subspaces corresponding to newforms, and
      // append corresponding modular abelian variety to D with appropriate multiplicity.
      for N in Reverse(Divisors(Level(M))) do 
         Verbose("Homology_NewformDecomposition", "", 
                         Sprintf("Considering level %o\n", N));
         t := Cputime();
         MN := ModularSymbols(AmbientSpace(M),N);
         ND := SortDecomposition(NewformDecomposition(NewSubspace(CuspidalSubspace(MN))));
         for number in [1..#ND] do
            MB := ND[number];
            t := Cputime();
            Verbose("Homology_NewformDecomposition", 
               Sprintf("Constructing abelian varieties from %o\n", MB), "");
            // For each d | Level(M)/N, there is an inclusion map from 
            // B into the space of level N.  There is one abelian 
            // variety A_f for each of these images.
            up_1 := DegeneracyMap(MN,AmbientSpace(M),1);
            if not up_1(MB.1) in M then
               continue;   // Don't include because no image of B can be in M.
                           // Note also that modular symbols spaces are, by definition,
                           // never smaller than what can be cut out using
                           // anemic Hecke algebra.
            end if; 
            name := LabelNewformSpace(MB, number);
            j := SeenThisAfBefore(D, name);
            if j eq 0 then
               H_Af := Create_ModAbVarHomol(MB);
               Append(~D,[* H_Af, [], name, number *]);
               j := #D;
            else
               H_Af := D[j][1];
            end if;
            PHI := D[j][2];
            // Append matrix to PHI for each degeneracy map.
            for d in Divisors(Level(M) div N) do
               phi := DegeneracyMatrixQ_To_ModSym(modsym,i,MN,d);
               embed := ModSymMatrix_to_HomologyMatrix(H_Af, H, phi);
               name := Level(MN) eq HomologyLevel(H) select "" 
                           else Sprintf("N(%o,%o,%o)",Level(MN),HomologyLevel(H),d);
               Append(~PHI, <embed, name>);
            end for;
            D[j][2] := PHI;
            con +:= Cputime(t);
         end for;
      end for;
   end for;
   return D;
end function;



function Create_Af_and_Homs(A, modsym, PHI, name, number) 
   assert Type(A) eq ModAbVar;
   assert Type(modsym) eq ModSym;   // new modsym space over Q(eps) attached to newform
   assert Type(PHI) eq SeqEnum;
   assert Type(name) eq MonStgElt;

   /* A newform abelian variety B = A_f/Q associated to a newform f
      breaks up over an extension K as a power of an abelian variety 
      which we call A_f=A_f/K since its THE (up to isogeny) simple  
      abelian variety over K associated to f.  These things have the
      the attribute is_Af set to true in MAGMA.
   */

   K := BaseRing(A);
   B := Create_ModAbVar_ModSym(name, modsym);
   B`newform_number := number;
   B`base_ring := K;
   if K cmpeq QQ then
      B`conductor := Level(B)^Dimension(B);
   end if;
   phi_hom := [Hom(B,A)| Create_MapModAbVar_MultiplyToMorphism(B, A, phi[1], QQ) : phi in PHI];
   for i in [1..#phi_hom] do 
      SetName(phi_hom[i], PHI[i][2]);
   end for;

   B`is_Af := true;
   inner_twists := InnerTwists(B);
   cm_twists := CMTwists(B);
   if #inner_twists le 1 or Dimension(B) eq 1 then
      A := B;
      A`is_Af := true;
      A`is_quaternionic := false;
      return A, phi_hom;
   end if;

   // In the presence of inner twists!  HERE'S WHAT TO DO.
   /* We now:
         (1) Compute *a* decomposition of homology of B into 
             subspaces corresponding to copies of A_f
         (2) Create homomorphism maps giving these embeddings
         (3) Determine if A has quaternionic multiplication or not (and set A`is_quaternionic!)
    */

   print "WARNING: Nontrivial inner twists ignored in decomposition algorithm!";
   A := B;
   A`is_Af := true;
   A`is_quaternionic := false;
   return A, phi_hom;
    
   

end function;

function Newform_ModularAbelianVariety_Decomposition_of_ModSym_AbVar(A)
   assert Type(A) eq ModAbVar;
   assert IsAttachedToModularSymbols(A);
   // A list of pairs <Af,[phi]> where Af is an abelian variety
   // attached to a newform and the phi are maps from Af into A, 
   // such that the product of all images of all Af is isogenous to A.

   D := [* *];
   PHI := [];
   i := 1;
   for X in Homology_NewformDecomposition(Homology(A)) do 
      H_Af, PHI, name, number := Explode(X);
      A_f, phis := Create_Af_and_Homs(A, ModularSymbols(H_Af)[1], PHI, name, number);
      Append(~D, <A_f, phis>);
   end for;

   return D;
end function;

function noexport_Decomposition_from_Af(newform_block)
// The input is a sequence of pairs <Af, phi> where phi is
// an embedding of Af into an ambient modular abelian variety
// attached to a sequence of spaces of newforms and Af is
// a single abelian variety over Q attached to a newform.
   X := [x[1] : x in newform_block];

   PHI := [x[2] : x in newform_block];
   if Type(BaseRing(X[1])) eq FldRat then   
             // theorem of Ribet -- no extra endomorphisms over Q.
      return X, PHI;
   end if;
   // Over bigger fields have to worry about inner twists, etc..
   // We decompose a single A_f as a power of a B using these 
   // inner twists, then use this single B to decompose all the
   // other images of A_f (somehow).

   // This is quite nontrivial, and I haven't implemented it yet.
   print "SimpleDecomposition -- not implemented over fields over than Q.  Not decomposing further.";
end function;


/***************************************************************************

  << Decomposition with respect to an Endomorphism or a Commutative Ring >>

 ***************************************************************************/


function Do_Decomposition_By_Operators(A, X) 
   Verbose("Do_Decomposition_By_Operators", 
         Sprintf("Decomposing A by operators in X, where A=%o and X=%o.",A,X),"");
   if #X eq 0 or Dimension(A) eq 1 then
      return [A];
   end if;
   phi := X[1];
   Remove(~X,1);
   D := [];
   FAC := FactoredCharacteristicPolynomial(phi);
   if #FAC eq 1 then
      return [A];
   end if;
   for F in FAC do
      psi := Evaluate(F[1],phi)^(F[2] div (Sign(A) eq 0 select 2 else 1));
      B,i := ConnectedKernel(psi);
      if Dimension(B) eq Degree(F[1]) then
         // Since psi acts irreducibly on D, no further decomposition is necessary.
         Append(~D, B); 
      else
         E := End(B);
         for C in Do_Decomposition_By_Operators(B, 
                [E | RestrictEndomorphism(f,i) : f in X]) do
            Append(~D, C);
         end for; 
      end if;
   end for;
   return D;
end function;

intrinsic DecomposeUsing(phi::MapModAbVar) -> SeqEnum
{Decompose A  using the endomorphism phi.}
   require IsEndomorphism(phi) : "Argument 1 must be an endomorphism.";
   require IsAllowedField(Domain(phi)) : 
       NOT_YET_PROGRAMMED_MESG;
   if not IsMorphism(phi)  then
      phi := Denominator(phi)*phi;
   end if;
   return Do_Decomposition_By_Operators(Domain(phi),[phi]);
end intrinsic;

intrinsic DecomposeUsing(R::HomModAbVar) -> SeqEnum
{Decompose A using the commutative ring of  endomorphisms generated by A.}
   require IsAllowedField(Domain(R)) : 
        NOT_YET_PROGRAMMED_MESG;
   A := Domain(R);
   require Codomain(R) cmpeq A : "Argument 1 must be a space of endomorphisms.";
   require IsRing(R) : "Argument 1 must be a ring.";
   require IsCommutative(R) : "Argument 1 must be commutative.";
   X := Generators(R);
   return Do_Decomposition_By_Operators(A, X);
end intrinsic;
