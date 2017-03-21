freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: operators.m
   DESC: computation of Hecke, Atkin-Lehner, etc. operators

   Creation: 06/16/03 -- initial creation
      
 ***************************************************************************/

/* 
  HANDBOOK_TITLE: Hecke and Atkin-Lehner Operators
*/

import "homology.m":
   Create_ModAbVarHomol_Subspace;

import "linalg.m":
   RestrictionOfScalars;

import "misc.m":
   GatherFactorExponents;

import "modabvar.m":
   Create_ModAbVar,
   Verbose;

import "morphisms.m":
   Create_MapModAbVar,
   Create_MapModAbVar_Name,
   Create_MapModAbVar_PossiblyUpToIsogeny;

import "rings.m":
   QQ, ZZ;   

forward
   ComputeOperator,
   OP,
   OP_mav,
   OP_ms;


function ComputeOperator(A, OP_ms, OP_mav, name)
   Verbose("ComputeOperator", Sprintf("Computing %o on %o", name, A),"");
   if IsAttachedToModularSymbols(A) then
      modsym := ModularSymbols(A);
      matrix := RestrictionOfScalars(OP_ms(modsym[1]));      
      for i in [2..#modsym] do 
         matrix := DirectSum(matrix,RestrictionOfScalars(OP_ms(modsym[i])));
      end for;
      return Create_MapModAbVar_Name(A, A, matrix, QQ, name);
   end if;
   t, A_f, phi := IsAttachedToNewform(A);
   if t then
      op :=  ComputeOperator(A_f, OP_ms, OP_mav, name);            
      ans := Inverse(phi)*op*phi;
      return ans;
   end if;

   // Harder case.
   e := ModularEmbedding(A);
   J := Codomain(e);
   TnJ := Matrix(OP_mav(J));
   E := Matrix(e);
   B := E*TnJ;
   if RowSpace(B) subset RowSpace(E) then // Hecke operator is an endomorphism up to isogeny
      matrix := Solution(E, B);   
      Tn,d := Create_MapModAbVar_PossiblyUpToIsogeny(A, A, matrix, FieldOfDefinition(A));
      return Tn;
   end if;
   // Hecke operator is *not* even an endomorphism, so we create image B of 
   // Hecke operator as an abelian variety, etc.
   H, embed_matrix := Create_ModAbVarHomol_Subspace(Homology(J), RowSpace(B));
   modular_data := <J, embed_matrix, false>;
   TnA := Create_ModAbVar("", H, FieldOfDefinition(A), FieldOfDefinition(A), modular_data);
   matrix := IdentityMatrix(QQ, Dimension(Homology(A)));
   return Create_MapModAbVar(A, TnA, matrix,FieldOfDefinition(A));
end function;

/***************************************************************************

  << Creation >>

 ***************************************************************************/


intrinsic HeckeOperator(A::ModAbVar, n::RngIntElt) -> MapModAbVar
{The Hecke operator T_n of index n induced on A by virtue of its morphism
to a modular symbols abelian variety.}
   Verbose("HeckeOperator", Sprintf("T_%o on %o", n, A),"");
   require Characteristic(BaseRing(A)) eq 0 : 
      "Argument 1 must be over a ring of characteristic 0.";
   name := Sprintf("T%o",n);
   function OP(X) 
      return HeckeOperator(X,n);
   end function;
   t := ComputeOperator(A, OP, OP, name);
   t`hecke_operator := n;
   t`parent := HeckeAlgebra(A);
   Verbose("HeckeOperator = ", "", Matrix(t));
   return t;
end intrinsic;

function ContainsZetaN(R, N)
   S := PolynomialRing(R);
   f := S!CyclotomicPolynomial(N);
   return HasRoot(f) eq true;
end function;

function SufficientBaseField(A);
   for eps in DirichletCharacters(A) do 
      if not IsTrivial(eps) then
         R := BaseRing(A);
         c := Modulus(eps);
         if not ContainsZetaN(R,c) then
            return false, 
        Sprintf("The base ring of argument 1 must contain a %oth root of unity.", c);
         end if;
      end if;
   end for;
   return true, _;
end function;

intrinsic AtkinLehnerOperator(A::ModAbVar, q::RngIntElt) -> MapModAbVar, RngIntElt
{The Atkin-Lehner operator W_q of index n induced on A by virtue of A being modular.}
   require Characteristic(BaseRing(A)) eq 0 : 
     "Argument 1 must be over a ring of characteristic 0.";
   N := Level(Codomain(ModularEmbedding(A)));
   require N mod q eq 0 and GCD(N div q, q) eq 1 : 
      "Argument 2 must exactly divide the level of the modular symbols abelian " *
      "variety that contains A.";
   t, msg := SufficientBaseField(A);
   require t : msg;
   name := Sprintf("W%o",q);
   function OP_ms(X) 
      return AtkinLehnerOperatorOverQ(X,q);
   end function;
   function OP_mav(X) 
      return AtkinLehnerOperator(X,q);
   end function;
   W := ComputeOperator(A, OP_ms, OP_mav, name);
   return W;
end intrinsic;

intrinsic AtkinLehnerOperator(A::ModAbVar) -> MapModAbVar
{The morphism (or morphism tensor Q) on (or from) A induced by the Atkin-Lehner
operator.}
   require Characteristic(BaseRing(A)) eq 0 : "Argument 1 must be over a ring of characteristic 0.";
   t, msg := SufficientBaseField(A);
   require t : msg;
   e := ModularEmbedding(A);
   return AtkinLehnerOperator(A,Level(Codomain(e)));
end intrinsic;


/***************************************************************************

  << Invariants >>

 ***************************************************************************/

intrinsic MinimalHeckePolynomial(A::ModAbVar, n::RngIntElt) -> RngUPolElt
{The minimal polynomial of the Hecke operator T_n acting on A.}
   Verbose("MinimalHeckePolynomial", 
    Sprintf("Computing minimal polynomial of Hecke operator T_%o on A=%o.",n,A),"");
   if Characteristic(BaseRing(A)) ne 0 then
      return MinimalHeckePolynomial(ChangeRing(A,RationalField()),n);
   end if;
   if IsAttachedToModularSymbols(A) then
      modsym := ModularSymbols(A);
     // would norm of charpoly over cyclo field be better?
      return &*[MinimalPolynomial(
             RestrictionOfScalars(HeckeOperator(M,n))) : M in modsym];
   end if;
   T := HeckeOperator(A,n);
   require IsEndomorphism(T) : "The Hecke operator must be an endomorphism.";
   return MinimalPolynomial(T);
end intrinsic;

intrinsic HeckePolynomial(A::ModAbVar, n::RngIntElt) -> RngUPolElt
{The characteristic polynomial of the Hecke operator T_n acting on A.}
   Verbose("HeckePolynomial", 
    Sprintf("Computing characteristic polynomial of Hecke operator T_%o on A=%o.",n,A),"");
   if Characteristic(BaseRing(A)) ne 0 then
      return HeckePolynomial(ChangeRing(A,RationalField()),n);
   end if;
   if IsAttachedToModularSymbols(A) then
      modsym := ModularSymbols(A);
     // would norm of charpoly over cyclo field be better?
      return &*[CharacteristicPolynomial(
             RestrictionOfScalars(HeckeOperator(M,n))) : M in modsym];
   end if;
   T := HeckeOperator(A,n);
   require IsEndomorphism(T) : "The Hecke operator must be an endomorphism.";
   return CharacteristicPolynomial(T);
end intrinsic;

intrinsic FactoredHeckePolynomial(A::ModAbVar, n::RngIntElt) -> RngUPolElt
{The factored characteristic polynomial of the Hecke operator T_n acting on A.}
   Verbose("FactoredHeckePolynomial", 
    Sprintf("Computing factored characteristic polynomial of Hecke operator T_%o on A=%o.",n,A),"");
   if Characteristic(BaseRing(A)) ne 0 then
      return FactoredHeckePolynomial(ChangeRing(A,RationalField()),n);
   end if;
   if IsAttachedToModularSymbols(A) then
      modsym := ModularSymbols(A);
      X := &cat[Factorization(CharacteristicPolynomial(
                    RestrictionOfScalars(HeckeOperator(M,n)))) : M in modsym];
      return GatherFactorExponents(X);
   end if;
   T := HeckeOperator(A,n);
   require IsEndomorphism(T) : "The Hecke operator must be an endomorphism.";
   return Factorization(CharacteristicPolynomial(T));
end intrinsic;
