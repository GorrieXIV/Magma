freeze;
 
import "core.m":
   ConvFromModularSymbol,
   LiftToCosetRep,
   ModularSymbolsBasis;

import "linalg.m":
   Restrict,
   RestrictionOfScalars,
   UnRestrictionOfScalars;

import "operators.m":
   ActionOnModularSymbolsBasis,
   Heilbronn,
   TnSparse;


import "maps.m": 
   DegeneracyCosetReps;

function ConjugateMatrix(A)
    return Parent(A)![ComplexConjugate(x) : x in Eltseq(A)];
end function;

function MC_ActionOnModularSymbolsBasis(g, M)
   // 1. Compute basis of modular symbols for M.
   B  := ModularSymbolsBasis(M);
   // 2. Apply g to each basis element. 
   gB := [ModularSymbolApply(M, g,B[i]) : i in [1..#B]];
   // 3. Map the result back to M.
   gM := [Representation(ConvFromModularSymbol(M,gB[i])) : i in [1..#gB]];
   return MatrixAlgebra(BaseField(M),Dimension(M))!gM;
end function;

function ComplexConjugationMatrix(K, n)
   // matrix of complex conjugation on basis of field K.
   if n gt 1 then
      return DirectSum(ComplexConjugationMatrix(K,n-1),ComplexConjugationMatrix(K,1));
   end if;
   V, K_to_V := VectorSpace(K, Rationals());   
   return MatrixAlgebra(RationalField(),Degree(K))!(&cat[Eltseq(ComplexConjugate(b) @@ K_to_V) : b in Basis(K)]);
end function;


function MatrixOnModSymBases(M1, M2, g)
   return MatrixAlgebra(BaseField(M1),Dimension(M1))!
       &cat[Eltseq(M2!ModularSymbolApply(M1,g,b)) : b in ModularSymbolsBasis(M1)];
end function;

function ConjugateModSym(x)
   return [<ComplexConjugate(Coefficients(a[1])[1]),a[2]> : a in x];
end function;

function MatrixOnModSymBasesConj(M, g)
   return RMatrixSpace(BaseField(M),Dimension(M),Dimension(M))!
       &cat[Eltseq(M!ConjugateModSym(ModularSymbolApply(M,g,b))) : b in ModularSymbolsBasis(M)];
end function;

function FieldAutomorphismMatrix(M, phi)
   assert Type(M) eq ModSym;

// Matrix of base field automorphism phi with respect to same basis that restriction
// of scalars are computed with respect to.
   K := BaseField(M);
   BK := Basis(K);
   BM := Basis(M);
   /* basis is bk1*bm1, bk1*bm2, ..., bk1*bmr, bk2*bm1, ... */

   I := MatrixAlgebra(RationalField(),Dimension(M))!1;

   // C is the matrix of phi on BK;
   V, K_to_V := VectorSpace(K, Rationals());   
   C := MatrixAlgebra(RationalField(),Degree(K))!
                 (&cat[Eltseq(phi(b) @ K_to_V) : b in Basis(K)]);

   return TensorProduct(C,I);
end function;

/*function Cached_ActionOnModularSymbolsBasis(g,M)
   assert Type(M) eq ModSym;
   assert Type(g) eq SeqEnum;
   assert IsAmbientSpace(M);
   if not assigned M`action_on_modsyms then
      M`action_on_modsyms := [* *];
   end if;
   if exists(i) {i  : i in [1..#M`action_on_modsyms]
                             | M`action_on_modsyms[i][1] eq g } then
      "found g = ", g," in cache.";
      return M`action_on_modsyms[i][2];
   end if;
   "computing action of g=", g;
   A := ActionOnModularSymbolsBasis(g,M);
   Append(~M`action_on_modsyms, <g,A>);
   return A;
end function;
*/

/*
intrinsic GOOD_InnerTwistOperator(M::ModSym, chi::GrpDrchElt) -> AlgMatElt
{}
   return InnerTwistOperator(M, chi);
end intrinsic;
*/


intrinsic InnerTwistOperator(M::ModSym, chi::GrpDrchElt) -> AlgMatElt
{Inner twist on restriction of scalars of M to Q.}
   if not assigned M`inner_twists then
      M`inner_twists := [* *];
   end if;
   if exists(i) {i  : i in [1..#M`inner_twists]
                             | M`inner_twists[i][1] eq chi } then
      return M`inner_twists[i][2];
   end if;

   vprint ModularSymbols : "Computing inner twist on M = ", M, 
          "\n of character ", chi, " of order ", Order(chi);

   eps := DirichletCharacter(M);
   K := BaseField(M);
   Amb := AmbientSpace(M);

   r := Conductor(chi);
   N := Level(M);
   s := Conductor(eps);
   NN := LCM([N,r^2,r*s]);
   vprint ModularSymbols : "NN = ", NN;

   C := DegeneracyCosetReps(N,NN,1);
   Z := MatrixAlgebra(Integers(),2); 
   C_matrix := [Z!g : g in C];
   

   epsinv := eps^(-1);

   matalg := MatrixAlgebra(BaseField(Amb),Dimension(Amb));
   A := matalg!0;
   eps_gamma := chi^2*eps;
   eps_gamma_val := [Evaluate(eps_gamma,g[1]) : g in C];
  
   for u in [u : u in [1..r] | GCD(u,r) eq 1] do 
      if r gt 3 then
         printf "Computing an inner twist endomorphism... %o percent done.\n",Round(100*u/r*1.0);
      end if;
      alpha := Z![r,u,0,r];
      A +:= Evaluate(chi, u)^(-1) * (&+[matalg|
                 eps_gamma_val[i]*
                 ActionOnModularSymbolsBasis(Eltseq(alpha*C_matrix[i]),Amb) : 
                    i in [1..#C_matrix]]);
   end for;
   if Type(K) eq FldRat then
      w := Restrict(A,VectorSpace(M));
      Append(~M`inner_twists,<chi, w>);
      return w;
   end if;

   aut := 0;
   for j in [1..Degree(K)] do 
      function f(x) return Conjugate(x,j); end function; 
      eps_of_f := ApplyAutomorphism(eps,f);
      if eps_of_f eq eps_gamma then
         aut := j;
         break;
      end if;
   end for;
   assert aut ne 0;
   phi := function(x) return Conjugate(x,aut); end function;  
   phi_Q := FieldAutomorphismMatrix(Amb, phi);  

   vprint ModularSymbols : "Automorphism is ", aut, " which has order ", Order(phi_Q), " and charpoly ", 
               Factorization(CharacteristicPolynomial(phi_Q));

   A_Q := RestrictionOfScalars(A);
   T := phi_Q*A_Q;
   if Dimension(M) eq Dimension(Amb) then
      TonM := T;
   else  // Now we restrict T to the restriction of scalars of M.
      V := VectorSpace(Amb);
      B := Basis(M);
      B_Q := [RestrictionOfScalars(V!Eltseq(z*b)) : b in B, z in Basis(K)];
      W := VectorSpaceWithBasis(B_Q);
      TonM := Restrict(T,W);
   end if;

   Append(~M`inner_twists,<chi, TonM>);
 
   return TonM, phi_Q, A_Q;
end intrinsic;

function Compute_Image_Under_Eta_Using_Symbols(chi, R, x)
   assert Type(x) eq ModSymElt;
   assert Type(R) eq SeqEnum;
   assert Type(chi) eq GrpDrchElt;
   M := AmbientSpace(Parent(x));
   eps := DirichletCharacter(M);

   A := InnerTwistOperator(M, chi);
   v := RestrictionOfScalars(Representation(x));
   w := UnRestrictionOfScalars(v*A,BaseField(M));
   return M!w;
end function;

function Compute_Image_Under_Eta_Of_Manin_Symbol(M, chi, psi, R, P, cd)
end function;

function Compute_Image_Under_Eta(chi, R, x)
   assert Type(x) eq ModSymElt;
   assert Type(R) eq SeqEnum;
   assert Type(chi) eq GrpDrchElt;

   M := Parent(x);
   assert IsAmbientSpace(M);
   eps := DirichletCharacter(M);

/*
   correct_answer_using_modsym := Compute_Image_Under_Eta_Using_Symbols(chi, R, x);
*/

/* 
   Given Manin symbol repn. x = [P,cd], compute 
      sum_{u=1}^r chi^(-1)(u) sum_{\gamma in R} psi(gamma) [P, \alpha_u \gamma abcd]
*/
   function pi(g) 
      return [Integers(Level(M))|g[2,1],g[2,2]];
   end function;

   matN := MatrixAlgebra(Integers(Level(M)),2);
   mat0 := MatrixAlgebra(Integers(),2);
//   psi := chi^2*eps;
//   psi := eps^(-1);
   psi := eps;
   manin := ManinSymbol(x);
   assert #manin eq 1;
   P, cd := Explode(manin[1]);
   abcd := mat0!LiftToCosetRep(cd,Level(M));
   z := M!0;
   r := Conductor(chi);
   for u in [1..r] do 
      w := M!0;
      alpha_u := Parent(R[1])![r,u,0,r];
      for gamma in R do 
         y := <P, pi(gamma*abcd)>;         
         w := w+Evaluate(psi,gamma[1,1])*ConvertFromManinSymbol(M, y);
      end for;
//      z := z + Evaluate(chi^(-1),u)*w;
      z := z + w;
   end for;
   print "manin symbols answer = ", z;
//   print "correct = ", correct_answer_using_modsym;
   return z;
   
end function;

function RestrictToQ_and_Change_By_Automorphism(M, chi, A)
   Type(M) eq ModSym;
   Type(A) eq AlgMatElt;
   Type(chi) eq GrpDrchElt;

   K := BaseField(M);
   eps := DirichletCharacter(M);
   eps_gamma := chi^2*eps;
   aut := 0;
   for j in [1..Degree(K)] do 
      function f(x) return Conjugate(x,j); end function; 
      if ApplyAutomorphism(eps,f) eq eps_gamma then
         aut := j;
         break;
      end if;
   end for;
   assert aut ne 0;
   phi := function(x) return Conjugate(x,aut); end function;  
   phi_Q := FieldAutomorphismMatrix(M, phi);  

   vprint ModularSymbols : "Automorphism is ", aut, " which has order ", Order(phi_Q), " and charpoly ", 
               Factorization(CharacteristicPolynomial(phi_Q));

   A_Q := RestrictionOfScalars(A);
   return phi_Q*A_Q;
end function;

function Compute_Coset_Reps(M, chi)
   Type(M) eq ModSym;
   Type(chi) eq GrpDrchElt;

   N := Level(M);
   r := Conductor(chi);
   s := Conductor(DirichletCharacter(M));
   NN := LCM([N,r^2,r*s]);

   R := [MatrixAlgebra(Integers(),2)!g : 
                  g in DegeneracyCosetReps(N,NN,1)];

   return R;
end function;

intrinsic Experimental_InnerTwistOperator(M::ModSym, chi::GrpDrchElt) -> AlgMatElt
{Inner twist on restriction of scalars of M to Q.  Use Manin symbols for speed.}
// assert IsAmbientSpace(M);
   if not assigned M`inner_twists then
      M`inner_twists := [* *];
   end if; 
   J := AmbientSpace(M);
   if exists(i) {i  : i in [1..#J`inner_twists]
                             | J`inner_twists[i][1] eq chi } then
      A := J`inner_twists[i][2];
      if IsAmbientSpace(M) then 
         return A;
      end if;
      return Restrict(A, RestrictionOfScalars(VectorSpace(M)));
   end if;

   vprint ModularSymbols : "Computing inner twist on M = ", M, 
              "\n of character ", chi, " of order ", Order(chi);

   R      := Compute_Coset_Reps(M, chi);
   images := [Compute_Image_Under_Eta(chi, R, x) : x in Basis(M)];
   images := [Coordinates(VectorSpace(M),Representation(x)) : x in images];
   A      := MatrixAlgebra(BaseField(M),Dimension(M))!(&cat[Eltseq(x) : x in images]);
   A      := RestrictToQ_and_Change_By_Automorphism(M, chi, A);
   Append(~M`inner_twists,<chi, A>);
   return A;
end intrinsic;

