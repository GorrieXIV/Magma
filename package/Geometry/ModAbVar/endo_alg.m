freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: endo_alg.m
   DESC: computation of endomorphism ring using shimura/ribet inner twists theory

   Creation: 06/16/03 -- initial creation
      
 ***************************************************************************/

/*
HANDBOOK_TITLE: Endomorphism Algebras
*/


import "linalg.m":
   MatrixLatticeBasis,
   Pivots,
   RestrictionOfScalars,
   ZeroMatrix;

import "misc.m":
   idxG0,
   IsSquareFree;

import "modabvar.m":
   Verbose;

import "morphisms.m":
   Create_MapModAbVar;

import "rings.m":
   QQ,ZZ;

forward
   Basis_For_Hecke_Algebra_Over_Q,
   Basis_For_Hecke_Algebra_Over_Z,
   Basis_for_EndomorphismMatrixAlgebra_of_Af,
   Basis_for_EndomorphismMatrixAlgebra_of_SimpleAbVar,
   Basis_for_HeckeMatrixAlgebra_of_Af,
   Compute_InnerTwist_Endomorphisms,
   Decide_If_Quaternionic,
   Generalized_Hecke_Bound,
   Is_Full_EndAf_Commutative,
   MatrixAlgebraBasis,
   OperatorOnSum;


function Basis_for_HeckeMatrixAlgebra_of_Af(A)
   assert Type(A) eq ModAbVar;
   assert IsAttachedToNewform(A);
   M := ModularSymbols(Homology(A))[1];
   N := Level(M);
   n := Dimension(M) div (Sign(M) eq 0 select 2 else 1);
   G := [HeckeOperator(M,i) : i in [1..Floor(n*3/2)]];
   b := 3;
   B := MatrixAlgebraBasis(G, n, b);
   while #B eq 0 do
      G := G cat [HeckeOperator(M,i) : i in [#G+1..#G+10+Floor(n/2)]];
      b := b+2;
      B := MatrixAlgebraBasis(G, n, b); 
   end while;

   // Now multiply by all scalars and restrict down to Q, then pull back to H_1(A,Q).
   K := BaseField(M);
   B := [alpha*Tn : Tn in B, alpha in Basis(K)];   // a Q-basis for T tensor K.
   BQ := [RestrictionOfScalars(x) : x in B];
   return BQ;

end function;

function Basis_For_Hecke_Algebra_Over_Q(A)
   if IsAttachedToNewform(A) then
      B := Basis_for_HeckeMatrixAlgebra_of_Af(A);
      return [Hom(A,A,true) | Create_MapModAbVar(A,A,g,QQ) : g in B];
   end if;

   N := Level(A);
   n := Dimension(A);

   G := [Matrix(HeckeOperator(A,i)) : i in [1..Floor(n*3/2)]];
   b := 5;
   B := MatrixAlgebraBasis(G, n, b);

   while #B eq 0 do
      G := G cat [Matrix(HeckeOperator(A,i)) : i in [#G+1..#G+10+Floor(n/2)]];
      b := b+2;
      B := MatrixAlgebraBasis(G, n, b); 
   end while;

   return [Create_MapModAbVar(A,A,g,QQ) : g in B];
end function;

function Generalized_Hecke_Bound(modsym_list)
   assert Type(modsym_list) eq SeqEnum;
   assert Type(modsym_list[1]) eq ModSym;
   N := LCM([Level(M) : M in modsym_list]);
   k := Max([Weight(M) : M in modsym_list]);
   d := Max([Degree(BaseField(M)) : M in modsym_list]);
   b := d*Ceiling(k*idxG0(N)/12);
   if #d gt 1 or #modsym_list gt 1 then
     printf "Using a conjectural bound of %o on the number "*
            "of Hecke operators needed to generate Hecke algebra.", b;    
   end if;
end function;

function OperatorOnSum(modsyms,i,T)
   assert Type(modsyms) eq SeqEnum;
   assert Type(i) eq RngIntElt;
   assert Type(T) eq AlgMatElt;
   n := &+[ZZ|Degree(BaseField(M))*Dimension(M) : M in modsyms];
   j := &+[ZZ|Dimension(modsyms[k]) : k in [1..i-1]];
   A := ZeroMatrix(QQ,n);
   for r in [1..Nrows(T)] do
      for c in [1..Ncols(T)] do
         A[r+j,c+j] := T[r,c];
      end for;
   end for;
   return A;
end function;

function Basis_For_Hecke_Algebra_Over_Z(A)
   assert IsAttachedToModularSymbols(A);
   if IsAttachedToNewform(A) then
      B := Basis_for_HeckeMatrixAlgebra_of_Af(A);
      return [Hom(A,A) | Create_MapModAbVar(A,A,g,QQ) : g in B];
   end if;
   if Dimension(A) eq 0 then
      return [];
   end if;

   N := Level(A);
   /* If A is attached to modular symbols, it is a product of spaces 
      for which it is reasonably clear how to compute a Z-basis for Hecke. 
      To compute Hecke algebra associated to a single space of modular symbols
      defined over Q(eps), do the following:
           (1) Compute n = k*idxG0(N)/12 = Hecke bound 
           (2) Compute T_1, ..., T_n on modular symbols space over Q(eps).
           (3) Compute basis of B of Z[eps] over Z.
           (4) Take all products alpha*T_i.
           (5) Restrict scalars to Q.
           (6) These are the generators. 
      Since A is a product of such spaces we take the direct sum.
      */
   G := [];

   modsyms := ModularSymbols(A);
   for k in [1..#modsyms] do M := modsyms[k];
      n := Ceiling(Weight(M)*idxG0(Level(M))/12.0);
      assert Type(BaseField(M)) in {FldRat, FldCyc};
      B := Basis(BaseField(M));  
      for i in [1..n] do 
         T := HeckeOperator(M,i);
         for b in B do 
            S := RestrictionOfScalars(b*T);
            Append(~G, OperatorOnSum(modsyms,k,S));
         end for;
      end for;
   end for;
   G := MatrixLatticeBasis(G);
   return [Hom(A,A) | Create_MapModAbVar(A,A,g,QQ) : g in G];
end function;

function Compute_InnerTwist_Endomorphisms(M, inner_twists)
   assert Type(M) eq ModSym;
   assert Type(inner_twists) eq SeqEnum;
   if #inner_twists eq 0 then
      return [];
   end if;
   assert Type(inner_twists[1]) eq GrpDrchElt;
   endos := [];
   for chi in inner_twists do
      A := InnerTwistOperator(M, AssociatedPrimitiveCharacter(chi));
      Append(~endos, A);
   end for;
   return endos;
end function;


function Basis_for_EndomorphismMatrixAlgebra_of_Af(A)
/* Compute Q-basis of matrices for the endomorphism algebra 
   of A_f over BaseRing(A).   When the base ring is Q or 
   f is a newform on Gamma_0(N) with N square free, then 
   this ring is generated by Hecke operators.  Otherwise,
   one might need to include inner twists. */
   assert Type(A) eq ModAbVar;
   assert IsAttachedToNewform(A);

   T := Basis_for_HeckeMatrixAlgebra_of_Af(A);
   M := ModularSymbols(Homology(A))[1];
   if #InnerTwists(A) eq 0 then
      return T;
   end if;

   /* Compute extra inner twist endomorphisms. */
   inner_twists := InnerTwists(A);
   N := Level(M);
   eps := DirichletCharacter(M);
   Verbose("Basis_for_EndomorphismMatrixAlgebra_of_Af",
           "Computing inner twist endomorphisms.", "");
   Twist_Endomorphisms := Compute_InnerTwist_Endomorphisms(M, inner_twists);
   Verbose("Basis_for_EndomorphismMatrixAlgebra_of_Af",
           Sprintf("It is %o",Twist_Endomorphisms), "");

   // Compute the dimension of the endomorphism algebra using various theorems.
   // By Ribet, page 59, the dimension is the degree of the Fourier field E 
   // times the number of inner twists.

   Verbose("Basis_for_EndomorphismMatrixAlgebra_of_Af",
           "Building endomorphism ring for endomorphisms so far.", "");

   dim := #T * #Twist_Endomorphisms;
   B := [t*w : t in T, w in Twist_Endomorphisms];
   return B;
end function;

function Basis_for_EndomorphismMatrixAlgebra_of_SimpleAbVar(A)
/* Compute Q-basis for the endomorphism algebra of the 
   isogeny simple modular abelian variety A over BaseRing(A). 
   Our hypothesis is that S is simple over BaseRing(A).  This
   means that A is a factor of an A_f.  If the base ring is QQ,
   then A = A_f for a newform f.   If the base ring is bigger,
   things can be more complicated, though in most cases A still
   equals A_f.   I haven't programmed the general case yet, but
   it shouldn't be difficult, since it will just use the A_f case.
*/
   if IsAttachedToNewform(A) then
      return Basis_for_EndomorphismMatrixAlgebra_of_Af(A);
   end if;
   
   error "endo_alg.m:Basis_for_EndomorphismMatrixAlgebra_of_SimpleAbVar -- Not written in necessary generality.";

end function;


// Here G is a sequence of matrices that generate a space of dimension r.
// This function finds a basis for that space.
function MatrixAlgebraBasis(G, dim, stop)
   //    Choose a j such that the map from T that sends a matrix
   //    to the submatrix of first j columns has image of dimension d.
   if stop eq 0 then
      stop := dim;
   end if;
   n   := 0; 
   d := Nrows(G[1]);
   K := BaseRing(Parent(G[1]));
   row := VectorSpace(K,d);
   repeat 
      n   +:= 1;
      if n gt stop or n gt d then
         return [];
      end if;
      V    := VectorSpace(K,d*n);
      gens := [V!&cat[Eltseq(row.j*t) : j in [1..n]] : t in G];
      W    := sub<V|gens>;
      Verbose("MatrixAlgebraBasis", "",
        Sprintf("Dim W = %o, goal = %o.", Dimension(W), dim));
   until Dimension(W) eq dim;

   E, F := EchelonForm(Transpose(RMatrixSpace(K,#gens,d*n)!gens));
   P := Pivots(Basis(RowSpace(E)));
   return [G[i] : i in P];
end function;


function Decide_If_Quaternionic(A)
   if BaseRing(A) cmpeq QQ then
      A`is_quaternionic := false;  // can't have quaqternionic mult over Q.
   end if;
   assert Type(A) eq ModAbVar;
   if IsAttachedToNewform(A) then
      assert assigned A`is_quaternionic;
      return A`is_quaternionic;
   end if;
   for D in Factorization(A) do 
      if Decide_If_Quaternionic(D[1]) then
         return true;
      end if;
   end for;
   return true;
end function;       

function Is_Full_EndAf_Commutative(A)
   assert Type(A) eq ModAbVar;
   assert IsAttachedToNewform(A);

   return not IsQuaternionic(A);
end function;


