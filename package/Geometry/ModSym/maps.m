freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: maps.m (Maps between spaces of modular symbols)
                                                                            
   $Header: /home/was/magma/packages/ModSym/code/RCS/maps.m,v 1.8 2002/10/01 06:03:10 was Exp was $

   $Log: maps.m,v $
   Revision 1.8  2002/10/01 06:03:10  was
   *** empty log message ***

   Revision 1.7  2001/07/13 02:55:01  was
   Added extra cashing in both directions for degeneracy maps, instead of
   just the outgoing direction.

   Revision 1.6  2001/07/03 19:48:01  was
   nothing.

   Revision 1.5  2001/06/07 01:42:04  was
   Allan put DegeneracyCosetReps in C.

   Revision 1.4  2001/06/01 23:09:11  was
   nothing.

   Revision 1.3  2001/05/14 02:42:59  was
   Updated comments and changed the asserts in DegeneracyMatrix
   to requires.

   Revision 1.2  2001/05/13 03:50:27  was
   Changed ModularForms flag to ModularSymbols.

   Revision 1.1  2001/04/20 04:46:59  was
   Initial revision

   Revision 1.4  2000/06/03 04:52:51  was
   verbose: ModularForm --> ModularForms

   Revision 1.3  2000/06/03 03:50:16  was
   Round

   Revision 1.2  2000/05/14 23:32:16  was
   changed DegeneracyMatrix into an intrinsic.

   Revision 1.1  2000/05/02 08:02:30  was
   Initial revision


 ***************************************************************************/

import "arith.m"  : idxG0;

import "core.m"   : ConvFromModularSymbol, 
                    ModularSymbolsBasis;

import "modsym.m" : CreateTrivialSpace;

import "operators.m" : GeneralizedHeilbronnOperator,
                       Heilbronn;

import "multichar.m" : MC_DegeneracyMatrix,
                       MC_ModularSymbols_of_LevelN;


/*******************************************************************
  DEGENERACY COSET REPRESENTATIVES:
    Let N be a positive integer and M a multiple of N.
    Let t be a divisor of N/M, and let T be the 2x2 matrix T=[0,0,  0,t].
    Find coset reps for Gamma_0(N) \ T Gamma_0(M).

  FACTS: T^(-1)*(a,b,c,d)*T = (a,bt,c/t,d)
         T^(-1)*Gamma_0(N)*T is contained in Gamma_0(M)
         Gamma_0(N)*T is contained in T*Gamma_0(M)
         

  SOLUTION:  
    (1) Computes representatives for Gamma_0(N/t,t) inside 
        of Gamma_0(M):
        COSET EQUIVALENCE: 
           Two right cosets represented by (a,b;c,d) & 
           (a',b';c',d') of Gamma_0(N/t,t) in SL_2(Z) are equivalent iff
           (a,b)=(a',b') as points of P^1(t), i.e., ab'=ba'(mod t),
           and (c,d)=(c',d') as points of P^1(N/t).  
        ALGORITHM:
           (A) Compute the number of cosets.
           (B) Compute a random element x of Gamma_0(M). 
           (C) Check if x is equivalent to anything generated so
               far; if not, add x to the list. 
           (D) Continue until the list is as long as the bound
               computed in A.  

    (2) There is a natural bijection 
         Gamma_0(N)\T*Gamma_0(M) <---> Gamma_0(N/t,t)\Gamma_0(M) 
        given by
            Tr  <---------> r
        Consequently we obtain coset representatives for
        Gamma_0(N)\T*Gamma_0(M) by left multiplying by T each 
        coset representative of Gamma_0(N/t,t)\Gamma_0(M) found 
        in step 1.
 ********************************************************************/

function XXXDegeneracyCosetReps(M, N, d) 
   n       := idxG0(N)/idxG0(M);      // number of coset representatives.
   Ndivd   := N div d;
   R       := [];                     // coset reps found so far. 
//   max     := 4*(n+10);
   max := 4*(n+10);
   halfmax := Ceiling(max/2);
   while #R lt n do
      // try to find another coset representative. 
      cc := M*Random(-halfmax, halfmax);
      dd :=   Random(-halfmax, halfmax);
      g, bb, aa := XGCD(-cc,dd);
      if g eq 0 then continue; end if;
      cc div:= g;
      dd div:= g;
      if cc mod M ne 0 then continue; end if;
      // Test if we've found a new coset representative.
      is_new:=true;
      for r in R do
           if ((r[2]*aa - r[1]*bb) mod d eq 0) and
               ((r[4]*cc - r[3]*dd) mod Ndivd eq 0) then 
            is_new := false;
            break ;
         end if;
      end for;
      // If it is new add it to the list.
      if is_new then
         Append(~R,[aa,bb,cc,dd]);
      end if;
   end while;     
   // Return the list left multiplied by T. 
   return [[r[1],r[2],r[3]*d,r[4]*d] : r in R];
end function;


/*
    Allan moved this into the C (06/06/01):

    "The first 4 lines are the same as the original, except for the original
    initialization assignment to R which is unnecessary now of course.
    I wrote a C function for the inner loop as this was very expensive --
    it does an O(n^2) loop.  It's HEAPS faster now in the C!" -- Allan
*/

function DegeneracyCosetReps(M, N, d) 
   n       := idxG0(N)/idxG0(M);     // number of coset representatives.
   Ndivd   := N div d;
   max     := 4*(n+10);
   halfmax := Ceiling(max/2);
   
   return DegeneracyCosetRepsInner(M, N, 
                         d, Integers()!n, halfmax);
end function;



/**********************************************************
  DEGENERACY AND INCLUSION MAPS -- newforms.
  If possible compute the map M1 --> M2 corresponding
  to the integer d. 

  WARNING: There might be a problem here when
  the characteristic of the base field divides d,
  because d occurs in the denominators of the
  DegeneracyReps.

 d:=1;c:=3;M:=11;N:=M*d*c; 
 A:=Mk(M,2); B:=Mk(N,2); 
 bet:=dm(A,B,d); alp:=dm(B,A,d); 
 bet*alp;      // must be a scalar.

 **********************************************************/
function EvaluateOnMatrix(eps, gamma) 
   // Evaluate the character eps on the matrix gamma=[a,b, c,d] in Gamma_0(N).
   // The result is eps(a).
   return Evaluate(eps, gamma[1]);
end function;


intrinsic DegeneracyMap(M1::ModSym, M2::ModSym, d::RngIntElt) -> Map
{The degneracy map M_1 ---> M_2 associated to d. 
Let N_i be the level of M_i for i=1,2. Suppose that d 
is a divisor of either the numerator or denominator of 
the rational number N_1/N_2, written in reduced form. 
If N_1 divides N_2, then this intrinsic returns 
alpha_d : M_1 ---> M_2, or if N_2 divides N_1, then this
intrinsic returns beta_d : M_1 ---> M_2.  It is an error if
neither divisibility holds.  There is also a condition about
Dirichlet characters.
}

   require Weight(M1) eq Weight(M2) : "The weight of argument 1 must equal weight of argument 2.";

   require Sign(M1) eq Sign(M2) : "The sign of argument 1 must equal sign of argument 2.";
   // (the code works regardless, but the caching doesn't look at the sign)

   M1 := AmbientSpace(M1);
   M2 := AmbientSpace(M2);

/*   Currently I get incomprehensible errors like the following.
This is avoided if we set M1 and M2 equal to their ambient spaces.
The functionality is essential what the user wants, but some error
checking and Domain/Range are gone.
> d(x);

<Source not available>
Runtime error in 'eq': Element is not in the domain of the map
*/

   N1 := Level(M1);
   N2 := Level(M2);
   multi := IsMultiChar(M1) or IsMultiChar(M2);

   if N1 mod N2 eq 0 then  // N2 divides N1 -- lower
      require (N1 div N2) mod d eq 0:
           "Third argument must divide the quotient of the first two arguments.";
      if not multi then
         eps1 := DirichletCharacter(M1);
         eps2 := DirichletCharacter(M2);
         bool, eps21 := IsCoercible(Parent(eps1), eps2);
         require bool and eps21 eq eps1 :
            "Arguments 1 and 2 must have compatible dirichlet characters.";
      end if;

   elif N2 mod N1 eq 0 then// N1 divides N2 -- raise level
      require (N2 div N1) mod d eq 0 :
           "Third argument must divide the quotient of the first two arguments.";
      if not multi then
         eps1 := DirichletCharacter(M1);
         eps2 := DirichletCharacter(M2);
         bool, eps12 := IsCoercible(Parent(eps2), eps1);
         require bool and eps12 eq eps2 :
            "Arguments 1 and 2 must have compatible dirichlet characters.";
      end if;
   else
      require false: "The level of argument 1 must divide the level of argument 2, or conversely.";
   end if;
  
   DegenMat := DegeneracyMatrix(M1,M2,d);
   return hom <M1->M2 | x:->M2!((x`element)*DegenMat)>;
end intrinsic;


intrinsic DegeneracyMatrix(M1::ModSym, M2::ModSym, d::RngIntElt) -> AlgMatElt
{The matrix of DegeneracyMap(M1,M2,d) with respect to Basis(M1) and
Basis(M2).  Both IsAmbientSpace(M1) and IsAmbientSpace(M2) must be true.}


   require IsAmbientSpace(M1) : 
          "Argument 1 must satisfy IsAmbientSpace(M1) eq true."; 
   require IsAmbientSpace(M2) : 
          "Argument 2 must satisfy IsAmbientSpace(M2) eq true."; 
   require Weight(M1) eq Weight(M2) : 
          "Arguments 1 and 2 must have the same weight.";
   require Sign(M1) eq Sign(M2) : 
          "Arguments 1 and 2 must have the same sign.";
          // (the code works regardless, but the caching doesn't look at the sign)

   if IsMultiChar(M1) then
      require IsMultiChar(M2) : "Arguments 1 and 2 must both be multicharacter spaces.";
         // TO DO: evidently this was not implemented correctly
         require false : "DegeneracyMatrix is not implemented for multi-character spaces";
         print "BOGUS MC degen matrix";
         return RMatrixSpace(BaseField(M1),Dimension(M1),Dimension(M2))!0;
         return MC_DegeneracyMatrix(M1, M2, d);
   end if;
 
   N1 := Level(M1);
   N2 := Level(M2);

   if not assigned M1`degeneracy_matrices_out then
      M1`degeneracy_matrices_out := [* *];
   end if;

   if not assigned M2`degeneracy_matrices_in then
      M2`degeneracy_matrices_in := [* *];
   end if;

   if exists(ii_out) { ii_out : ii_out in [1..#M1`degeneracy_matrices_out] | 
                  N2 eq M1`degeneracy_matrices_out[ii_out][1] } then
      if exists(jj) { jj : jj in [1..#M1`degeneracy_matrices_out[ii_out][2]] | 
                       d eq M1`degeneracy_matrices_out[ii_out][2][jj][1] } then
         already_known := M1`degeneracy_matrices_out[ii_out][2][jj][2];
      end if;
   end if;

   if exists(ii_in) { ii_in : ii_in in [1..#M2`degeneracy_matrices_in] | 
                  N1 eq M2`degeneracy_matrices_in[ii_in][1] } then
      if exists(jj) { jj : jj in [1..#M2`degeneracy_matrices_in[ii_in][2]] | 
                       d eq M2`degeneracy_matrices_in[ii_in][2][jj][1] } then
         already_known := M2`degeneracy_matrices_in[ii_in][2][jj][2];
      end if;
   end if;

   if not assigned already_known then
      if IsVerbose("ModularSymbols") then
         t := Cputime();
         printf "Computing index-%o degeneracy map from level %o to %o.\n",
                d, N1, N2;
      end if;
   end if;

  if N1 eq N2 then
      require d eq 1 : "Argument 3 must equal 1.";
      require M1 eq M2: "Arguments 1 and 2 must be equal.";
                       // we easily *could* write down the map between
                       // different presentations of M_k(N), but
                       // we won't for now, since there should
                       // never be a need.   NOTE that at present there
                       // *is* only one presentation for any given space,
                       // since it's a reduced row echelon form of a matrix.
      F := BaseField(M1);
      return Hom(Representation(M1), 
               Representation(M2))!MatrixAlgebra(F,Degree(M1))!1;

   elif N1 mod N2 eq 0 then  // N2 divides N1 -- lower
      require (N1 div N2) mod d eq 0 :
              "Argument 3 must divide Level(M1) div Level(M2).";
      eps1 := DirichletCharacter(M1);
      eps2 := DirichletCharacter(M2);
      bool, eps21 := IsCoercible(Parent(eps1), eps2);
      require bool and eps21 eq eps1 :
         "Arguments 1 and 2 must have compatible dirichlet characters.";

      if assigned already_known then
         return already_known;
      end if;


      /* Proposition 2.6.15 of Merel's paper. */
      Heil := Heilbronn(M1, d, true);           
      A := GeneralizedHeilbronnOperator(M1, M2, Heil : t:=d);

// Previous version -- VASTLY SLOWER, but well tested and good
// for testing the above fast version.

/*    B  := ModularSymbolsBasis(M1);
      D  := [d,0,0,1];
      DB := [ModularSymbolApply(M1,D, B[i])  : i in [1..#B] ];
      otherA  := [Representation(ConvFromModularSymbol(M2,DB[i])) : i in [1..#DB]]; 
      assert A eq Hom(Representation(M1), Representation(M2)) ! otherA; 
*/


   elif N2 mod N1 eq 0 then// N1 divides N2 -- raise level
      require (N2 div N1) mod d eq 0 : 
          "Argument 3 must divide Level(M2) div Level(M1).";
      eps1 := DirichletCharacter(M1);
      eps2 := DirichletCharacter(M2);
      bool, eps12 := IsCoercible(Parent(eps2), eps1);
      require bool and eps12 eq eps2 :
         "Arguments 1 and 2 must have compatible dirichlet characters.";

      if assigned already_known then
         return already_known;
      end if;

      B   := ModularSymbolsBasis(M1); 
      R   := DegeneracyCosetReps(N1, N2, d);
      eps := DirichletCharacter(M1);
      if IsTrivial(eps) then
         RB := [ &cat[ModularSymbolApply(M1, r, B[i]) : r in R] 
                                                  : i in [1..#B]];
         // This step takes a lot of time.
         A := [Representation(ConvFromModularSymbol(M2,RB[i])) 
                                                  : i in [1..#RB]];
      else
         A   := [ &+[EvaluateOnMatrix(eps,r)*
                      Representation(ConvFromModularSymbol(M2,
                              ModularSymbolApply(M1, r, B[i]))) : r in R] 
               : i in [1..#B]];
      end if;
   else
      assert false;
   end if;

   vprintf ModularSymbols, 2: "\t\t(%o s)\n",Cputime(t);

   h := Hom(Representation(M1), Representation(M2)) ! A; 
   if not assigned ii_out then
      Append(~M1`degeneracy_matrices_out, <N2, [* <d,h> *]>);
   else
      Append(~M1`degeneracy_matrices_out[ii_out][2], <d,h>);
   end if;
   if not assigned ii_in then
      Append(~M2`degeneracy_matrices_in, <N1, [* <d,h> *]>);
   else
      Append(~M2`degeneracy_matrices_in[ii_in][2], <d,h>);
   end if;
   return h;

end intrinsic;


intrinsic ModularSymbols(M::ModSym, N::RngIntElt) -> ModSym
{The modular symbols space of level N associated to M.
Let NN be the level of M.
If NN divides N, then
this intrinsic returns the modular symbols space
 Sum_(d|N/NN)alpha_d(M)
If N divides NN, then
this intrinsic returns the modular symbols space
 Sum_(d|NN/N)beta_d(M).
In this latter case, if 
Conductor(DirichletCharacter(M)) does not divide N,
then the 0 space is returned.
}

   requirege N,1;
   require Level(M) mod N eq 0 or N mod Level(M) eq 0 :
       "Argument 2 must divide or be divisible by the level of argument 1.";

   if N eq Level(M) then return M; end if;

   if IsMultiChar(M) then
      return MC_ModularSymbols_of_LevelN(M,N);
   end if;

   if not assigned M`other_levels then
      M`other_levels := [* *];
   end if;
   if not exists(pos) { pos : pos in [1..#M`other_levels] 
                            | M`other_levels[pos][1] eq N} then
      /****************************************************************
         M does not know the old modular symbols at level NN.  Here's what 
         we do:
            (1) If this object has a creator, ask it for
                the modular symbols at level NN. If so, done;
                otherwise continue with the next step.
            (2) If not, construct the space of symbols at level NN.
       ****************************************************************/

      // Step 1.
      if assigned M`creator then
         Append(~M`other_levels, <N,ModularSymbols(M`creator,N)>);
      else
         // Step 2: We are the creator.  
         eps   := DirichletCharacter(M);
         F     := BaseField(M);   
         if N mod Conductor(eps) ne 0 then
            epsN := Restrict(Parent(eps)!1,1);
            Append(~M`other_levels, <N,CreateTrivialSpace(Weight(M),epsN,Sign(M))>);
         else
            if Level(M) mod N eq 0 then
               epsN := Restrict(eps,N);
            else
               epsN := Extend(eps,N);
            end if;
            if IsAmbientSpace(M) then
               MS  := ModularSymbols(epsN,Weight(M),Sign(M));
               if Level(M) mod N eq 0 then
                  Append(~M`other_levels, <N,MS>);
               else
                  Append(~M`other_levels, <N,MS!!M>);
               end if;
            else
               Append(~M`other_levels, <N,ModularSymbols(AmbientSpace(M),N)!!M>);
            end if;
         end if;
         (M`other_levels[#M`other_levels][2])`creator := M;  
      end if;
      pos := #M`other_levels;
   end if;
   return M`other_levels[pos][2];
end intrinsic;





