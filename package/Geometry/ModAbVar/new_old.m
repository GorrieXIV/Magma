freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: newold.m
   DESC: new and old pieces of ModAbVar's

   Creation: 06/16/03 -- initial creation
      
 ***************************************************************************/

/*
HANDBOOK_TITLE: New and Old Subvarieties and Natural Maps
*/



import "homology.m":
   Create_ModAbVarHomol_Subspace,
   Rational_to_ModSym_Matrix, 
   ModSym_to_Rational_Matrix;

import "linalg.m":
   HorizontallyStackMatrices,
   RestrictionOfScalars,
   VerticallyStackMatrices;

import "modabvar.m":
   Create_ModAbVar,
   Name,
   SetName,
   Verbose;

import "morphisms.m":
   Create_MapModAbVar,
   Create_MapModAbVar_MultiplyToMorphism,
   Create_MapModAbVar_Name;

import "rings.m":
   QQ,
   CommonFieldOfDefinition;

forward 
   DegeneracyMatrixOverQ,
   ModularSymbols_ValidNaturalMap,
   ModularSymbols_NewSubspace,
   ModularSymbolsSequence_NewSubspace,
   ModularSymbols_OldSubspace,
   ModularSymbolsSequence_OldSubspace,
   Pullback_to_RationalHomology,
   ZeroMatrixOverQ;

/* In each algorithm below we first reduce to the modular symbols case. */


/***************************************************************************

  << Natural Maps >>

 ***************************************************************************/

intrinsic NaturalMaps(A::ModAbVar, B::ModAbVar) -> SeqEnum
{Sorted list of maps NaturalMap(A,B,d), where d runs through all divisors
of the level of A over the level B, or the level of B over
the level A.}
   Verbose("NaturalMaps", Sprintf("Computing natural maps from A to B, where A=%o, B=%o.",
        A, B), "");
   NA := Level(A);
   NB := Level(B);
   if NA mod NB eq 0 then
      return [Hom(A,B) | NaturalMap(A, B, d) : d in Divisors(NA div NB)];
   elif NB mod NA eq 0 then
      return [Hom(A,B) | NaturalMap(A, B, d) : d in Divisors(NB div NA)];
   end if;
   return [];
end intrinsic;

intrinsic NaturalMap(A::ModAbVar, B::ModAbVar) -> MapModAbVar
{The natural map induced by the identity on modular forms, or 0
if there is none.}
   return NaturalMap(A, B, 1);
end intrinsic;

intrinsic NaturalMap(A::ModAbVar, B::ModAbVar, d::RngIntElt) -> MapModAbVar
{The natural map from A to B induced, in a potentially complicated way,
from the map f(q)\mapsto f(q^d) on modular forms.  }
   Verbose("NaturalMaps", Sprintf("Computing natural maps for d=%o from A to B, where A=%o, B=%o.",
        d, A, B), "");
   name := Sprintf("N(%o)",d);
   // First reduce to the case the A and B are modular symbols abelian varieties.
   if not (IsAttachedToModularSymbols(A) and IsAttachedToModularSymbols(B)) then
      eA := ModularEmbedding(A);
     piB := ModularParameterization(B);    
       d := eA*NaturalMap(Codomain(eA),Domain(piB),d)*piB;
       SetName(d,name);
       return d;
   end if;
   // Now both A and B are attached to modular symbols. 
   MSA := [AmbientSpace(X) : X in ModularSymbols(A)];
   MSB := [AmbientSpace(X) : X in ModularSymbols(B)];
   D := [* *];
   for i in [1..#MSA] do 
      Append(~D,DegeneracyMatrixOverQ(MSA[i],MSB, d));
   end for;
   T := VerticallyStackMatrices(D);
   // Now T defines the map we want on restrictions of scalars of ambient
   // spaces of modular symbols.  
   matrix := Rational_to_ModSym_Matrix(Homology(A)) * T * 
               ModSym_to_Rational_Matrix(Homology(B));
   K := CommonFieldOfDefinition([* A, B *]);
   phi :=  Create_MapModAbVar_MultiplyToMorphism(A,B,matrix,K);
   phi`name := name;
   return phi;   
end intrinsic;


/***************************************************************************

  << New Subvarieties and Quotients>>

 ***************************************************************************/


intrinsic NewSubvariety(A::ModAbVar, r::RngIntElt) -> ModAbVar, MapModAbVar
{The r-new subvariety of A.}
   Verbose("NewSubvariety", Sprintf("Computing %o-new subvariety of A=%o.\n",r,A),"");
   if Name(A) ne "" then
      name := Sprintf("%o_%onew",Name(A),r eq 0 select "" else Sprintf("%o-,",r));
   else
      name := "";
   end if;
   if not IsAttachedToModularSymbols(A) then  
      e := ModularEmbedding(A);
      Jold, pi := OldQuotient(Codomain(e),r);
      Anew, i := ConnectedKernel(e*pi);
      Name(Anew,name);
      return Anew, i;
   end if;
   NS_modsym := ModularSymbolsSequence_NewSubspace(ModularSymbols(A), r);
   NS_homol := Pullback_to_RationalHomology(Homology(A), NS_modsym);
   H,embed := Create_ModAbVarHomol_Subspace(Homology(A), NS_homol);
   K := FieldOfDefinition(A); R := BaseRing(A);
   J := <A, embed, false>;
   Anew := Create_ModAbVar(name, H, K, R, J);
   i := Create_MapModAbVar(Anew, A, embed, K);
   return Anew, i;
end intrinsic;

intrinsic NewQuotient(A::ModAbVar, r::RngIntElt) -> ModAbVar, MapModAbVar
{The r-new quotient of A.}
   Verbose("NewQuotient", Sprintf("Computing %o-new quotient variety of %o.\n",r,A),"");
   if Name(A) ne "" then
      name := Sprintf("%o^%onew",Name(A),r eq 0 select "" else Sprintf("%o-,",r));
   else
      name := "";
   end if;
   pi := ModularParameterization(A);
   Jold, i := OldSubvariety(Domain(pi),r);
   Anew, f := Cokernel(i*pi);
   SetName(Anew,name);
   return Anew, f;
end intrinsic;

intrinsic NewSubvariety(A::ModAbVar) -> ModAbVar, MapModAbVar
{The new subvariety of A.}
   return NewSubvariety(A,0);
end intrinsic;
intrinsic NewQuotient(A::ModAbVar) -> ModAbVar, MapModAbVar
{The new quotient of A.}
   return NewQuotient(A,0);
end intrinsic;

/***************************************************************************

  << Old Subvarieties and Quotients>>

 ***************************************************************************/

intrinsic OldSubvariety(A::ModAbVar, r::RngIntElt) -> ModAbVar, MapModAbVar
{The r-old subvariety of A.}
   Verbose("OldSubvariety", Sprintf("Computing %o-old subvariety of %o.\n",r,A),"");
   if Name(A) ne "" then
      name := Sprintf("%o_%oold",Name(A),r eq 0 select "" else Sprintf("%o-",r));
   else
      name := "";
   end if;
   if not IsAttachedToModularSymbols(A) then  
      e := ModularEmbedding(A);
      Jnew, pi := NewQuotient(Codomain(e),r);
      Aold, i := ConnectedKernel(e*pi);
      SetName(Aold,name);
      return Aold, i;
   end if;
   OS_modsym:= ModularSymbolsSequence_OldSubspace(ModularSymbols(A), r);
   OS_homol := Pullback_to_RationalHomology(Homology(A), OS_modsym);
   H, embed := Create_ModAbVarHomol_Subspace(Homology(A), OS_homol);
   K := FieldOfDefinition(A); R := BaseRing(A);
   J := <A, embed, false>;
   Aold := Create_ModAbVar(name, H, K, R, J);
   i := Create_MapModAbVar(Aold, A, embed, K);
   return Aold, i;

end intrinsic;

intrinsic OldQuotient(A::ModAbVar, r::RngIntElt) -> ModAbVar, MapModAbVar
{The r-old quotient of A.}
   Verbose("OldQuotient", Sprintf("Computing %o-new quotient variety of %o.\n",r,A),"");
   if Name(A) ne "" then
      name := Sprintf("%o^%oold",Name(A),r eq 0 select "" else Sprintf("%o-,",r));
   else
      name := "";
   end if;
   pi := ModularParameterization(A);
   Jnew, i := NewSubvariety(Domain(pi),r);
   Aold, f := Cokernel(i*pi);
   SetName(Aold,name);
   return Aold, f;
end intrinsic;

intrinsic OldSubvariety(A::ModAbVar) -> ModAbVar, MapModAbVar
{The old subvariety of A.}
   return OldSubvariety(A,0);
end intrinsic;
intrinsic OldQuotient(A::ModAbVar) -> ModAbVar, MapModAbVar
{The old quotient of A.}
   return OldQuotient(A,0);
end intrinsic;

function ModularSymbols_NewSubspace(M, r)
   Verbose("ModularSymbols_NewSubspace", "",
        Sprintf("Finding modular symbols of %o-new subspace of %o.", r, M));
   assert Type(M) eq ModSym;
   assert Type(r) eq RngIntElt;
   if r eq 0 then
      return VectorSpace(NewSubspace(M));
   end if;
   if r eq 1 then
      return VectorSpace(ZeroSubspace(M));
   end if;
   // the r-new subspace of the modular symbols space M.
   N := Level(M);
   f := Conductor(DirichletCharacter(M));
   if not (r mod f eq 0 and N mod r eq 0) then
      return VectorSpace(M);
   end if;

   // Make the space M2 of level N/r and compatible character. 
   N2 := N div r;
   M2 := ModularSymbols(AmbientSpace(M),N2);
   if Dimension(CuspidalSubspace(M2)) eq 0 then
      return VectorSpace(M);
   end if;

   /* Now intersect, for each divisor t of d, the kernels
      of the t-degeneracy map from M to M2. */
   V := VectorSpace(M);
   for t in Divisors(r) do 
      delta := DegeneracyMatrix(AmbientSpace(M),M2,t);
      V := V meet Kernel(delta);
   end for;
   return V;
end function;

function ModularSymbolsSequence_NewSubspace(modsym, r)
   return DirectSum([
          RestrictionOfScalars(ModularSymbols_NewSubspace(M,r)) 
                    : M in modsym]);
end function;

function ModularSymbols_OldSubspace(M, r)
   Verbose("ModularSymbols_OldSubspace", "",
        Sprintf("Finding modular symbols of %o-old subspace of %o.", r, M));
   assert Type(M) eq ModSym;
   assert Type(r) eq RngIntElt;
   if r eq 0 then
      return VectorSpace(OldSubspace(M));
   end if;
   if r eq 1 then
      return VectorSpace(M);
   end if;
   // the r-old subspace of the modular symbols space M.
   N := Level(M);
   f := Conductor(DirichletCharacter(M));
   if not (r mod f eq 0 and N mod r eq 0) then
      return VectorSpace(ZeroSubspace(M));
   end if;
   // Make the space M2 of level N/r and compatible character. 
   N2 := N div r;
   M2 := ModularSymbols(AmbientSpace(M),N2);
   if Dimension(CuspidalSubspace(M2)) eq 0 then
      return VectorSpace(ZeroSubspace(M));
   end if;
   /* Now add, for each divisor t of d, the images
      of the t-degeneracy maps from M2 to M. */
   V := VectorSpace(ZeroSubspace(M));
   for t in Divisors(r) do 
      delta := DegeneracyMatrix(M2,AmbientSpace(M),t);
      V := V + Image(delta);
   end for;
   return V meet VectorSpace(M);
end function;

function ModularSymbolsSequence_OldSubspace(modsym, r)
   return DirectSum([
          RestrictionOfScalars(ModularSymbols_OldSubspace(M,r)) 
                    : M in modsym]);
end function;

function ZeroMatrixOverQ(M1, M2)
   assert Type(M1) eq ModSym;
   assert Type(M2) eq ModSym;
   nrows := Degree(BaseField(M1))*Dimension(M1);
   ncols := Degree(BaseField(M2))*Dimension(M2);
   return RMatrixSpace(QQ,nrows,ncols)!0;
end function;

function DegeneracyMatrixOverQ(M, D, d)
   assert Type(M) eq ModSym;
   assert Type(D) eq SeqEnum;
   // For each modular symbols space D[i], compute the 
   // restriction of scalars to Q of the d-th degeneracy matrix
   // from M to D[i].  If this wouldn't be defined on modular
   // symbols, compute the zero map.  Put these matrices all
   // together by concatenating them horizontally.
   X := [* *];
   for i in [1..#D] do
      M2 := D[i];
      if ModularSymbols_ValidNaturalMap(M, M2, d) then
         Append(~X,RestrictionOfScalars(DegeneracyMatrix(M,M2,d)));
      else
         Append(~X,ZeroMatrixOverQ(M,M2));
      end if;
   end for;
   return HorizontallyStackMatrices(X);
end function;

function ModularSymbols_ValidNaturalMap(M1, M2, d)
   // Decide whether there is a valid degeneracy map.
   assert Type(M1) eq ModSym;
   assert Type(M2) eq ModSym;
   assert Type(d) eq RngIntElt;

   if BaseField(M1) cmpne BaseField(M2) then
      return false;
   end if;
   if Weight(M1) ne Weight(M2) then
      return false;
   end if;
   N1 := Level(M1);
   N2 := Level(M2);

   if N1 mod N2 eq 0 then  // N2 divides N1 -- lower
      if not ((N1 div N2) mod d eq 0) then
         return false;
      end if;
      if not (Parent(DirichletCharacter(M1))!DirichletCharacter(M2) 
                      eq DirichletCharacter(M1)) then
         return false;
      end if;
   elif N2 mod N1 eq 0 then // N1 divides N2 -- raise level
      if not ((N2 div N1) mod d eq 0) then
         return false;
      end if;
      if not (Parent(DirichletCharacter(M2))!DirichletCharacter(M1) 
                      eq DirichletCharacter(M2)) then
         return false;
      end if;
   else
      return false;
   end if;
   return true;
end function;

function Pullback_to_RationalHomology(H, V)
   assert Type(H) eq ModAbVarHomol;
   assert Type(V) eq ModTupFld;
   // V is a subspace of the restriction of scalars of the 
   // modular symbols spaces attached to H.  This function
   // computes a subspace of the rational homology of H 
   // that maps to (the projection onto the cuspidal 
   // subspace of) V.
   phi := ModSym_to_Rational_Matrix(H);
   B := [VectorSpace(H) | b*phi : b in Basis(V)];
   return VectorSpaceWithBasis(B);
end function;
