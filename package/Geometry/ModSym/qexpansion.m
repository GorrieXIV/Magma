freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: qexpansion.m (Computing q-expansions)

   2007-06   (Steve) Changed the behaviour of qIntegralBasis in the multi-character case,
             so that it includes all the images of oldforms under the various maps.
             This seems the most logical behaviour, otherwise the dimensions don't match.
             Note that qExpansionBasis behaves differently again (so can't be used as a guide) 
              -- it limits itself to the AssociatedNewSpace in the multi-character case.
             It's hard to tell exactly what was intended, based on the documentation.

   2007      (Steve) Lots of minor changes recently, especially in linear algebra stuff.

   2004-10-24: (was) commented out some exported intrinsics that begin xxx_

   11/18/02: (was) Added CompactSystemOfEigenvaluesOverQ, which
             is needed for the modular forms database.

   11/17/02: (was)  In the call to NewformDecomposition below, which is 
             used in one of the algorithms for computing a basis of  
             newforms, the default was to order the factors.  This
             is wasteful, so we set it to false.

   $Header: /home/was/magma/packages/ModSym/code/RCS/qexpansion.m,v 1.15 2002/08/26 03:54:38 was Exp was $

   $Log: qexpansion.m,v $
   Revision 1.15  2002/08/26 03:54:38  was
   Added some code for multicharacter spaces.

   Revision 1.14  2002/05/04 17:00:15  was
   Added more ways to call qEigenform.

   Revision 1.13  2002/02/19 02:25:08  was
   forced "universal" algorithm for atkin-lehner subspaces.

   Revision 1.12  2001/11/22 17:56:07  was
   nothing.

   Revision 1.11  2001/07/27 20:26:23  was
   BaseExtend |--> ChangeRing for elliptic curves.

   Revision 1.10  2001/07/20 21:00:33  was
   Fixed a little bug in CompactSystemOfEigenvaluesVector.

   Revision 1.9  2001/07/20 09:10:17  was
   nothing.

   Revision 1.8  2001/07/17 07:50:30  was
   Added CompactSystemOfEigenvalues.

   Revision 1.7  2001/07/13 23:58:35  was
   ?

   Revision 1.6  2001/07/13 19:58:58  was
   Fixed a bug in SystemOfEigenvalues.

   Revision 1.5  2001/05/16 21:14:13  was
   Fixed bug in Compute_qExpansion.

   Revision 1.4  2001/05/13 03:51:27  was
   Changed ModularForms flag to ModularSymbols.

   Revision 1.3  2001/05/13 03:51:25  was
   *** empty log message ***

   Revision 1.2  2001/04/24 06:52:31  was
   Added a NewformDecomposition check to qEigenform.

   Revision 1.1  2001/04/20 04:47:01  was
   Initial revision

   Revision 1.11  2001/02/04 23:23:23  was
   *** empty log message ***

   Revision 1.10  2001/02/04 18:10:56  was
   Added some commented-out code to function EigenvectorModSym(A)
   that might be useful later when computing eigenvectors over finite fields.

   Revision 1.9  2001/02/04 15:57:45  was
   Nothing!

   Revision 1.8  2001/02/03 19:08:44  was
   Removed the
       Dimension(W) ne goal
   assertion from

      function qExpansionBasisUniversal(M, prec, do_saturate)

   because there are situation where it should not be satisfied, i.e.,
   when prec is too small.  It is still there as a WARNING.

   Revision 1.7  2001/01/16 03:30:06  was
   Fixed a bug in function EigenvectorModSym(A):
   Before if it couldn't find an irreducible eigenvector after trying
   10 times it gave up.  Now it will try forever.    Enrique gave me
   an example of level 408 that killed the old version!

   Revision 1.6  2000/07/27 07:40:17  was
   Fixed a bad bug, that manifest when the command time LSeries(MS("1k24A"),1,97);
   is executed. The problem is with the function EigenformInTermsOfIntegralBasis,
   in which a "Degree" must be changed to an "AbsolutePrecision".

   Revision 1.5  2000/06/14 18:58:06  was
   nothing

   Revision 1.4  2000/06/05 00:44:54  was
   added IsCuspidal test

   Revision 1.3  2000/06/03 04:53:13  was
   verbose: ModularForm --> ModularForms

   Revision 1.2  2000/05/15 01:02:06  was
   quick fix of bad comparison.

   Revision 1.1  2000/05/02 08:09:13  was
   Initial revision
  
                                                                            
 ***************************************************************************/


import "arith.m"  :   DotProd, 
                      PrimePos,
                      SmallestPrimeNondivisor,
                      ToLowerCaseLetter;

import "linalg.m" :   EchelonPolySeq,
                      MyCharpoly,
                      Pivots,
                      SaturatePolySeq,
                      Saturate;

import "multichar.m": 
   AssociatedNewformSpace, 
   HasAssociatedNewformSpace;

import "subspace.m":  MinusSubspaceDual,
                      PlusSubspaceDual;


forward Compute_qExpansion,
        DenominatorOf,
        EigenvectorOfMatrixWithCharpoly,
        EigenvectorModSym,
        EigenvectorModSymSign,
        EisensteinConstantCoefficient,
        SpaceGeneratedByImages;

intrinsic PowerSeries(M::ModSym, prec::RngIntElt) -> RngSerPowElt
{The q-expansion of one of the Galois-conjugate newforms
associated to M, computed to absolute precision prec.  The
coefficients of the q-expansion lie in a quotient of a polynomial
extension of the base field of M.}
   return qEigenform(M,prec);
end intrinsic;

intrinsic PowerSeries(M::ModSym) -> RngSerPowElt
{"} // "
   return qEigenform(M);
end intrinsic;

intrinsic Eigenform(M::ModSym) -> RngSerPowElt
{Same as qEigenform}
   prec := assigned M`qeigenform select M`qeigenform[1] else 8;
   return qEigenform(M,prec);
end intrinsic;

intrinsic Eigenform(M::ModSym, prec::RngIntElt) -> RngSerPowElt
{"} // "
   return qEigenform(M,prec);
end intrinsic;

intrinsic qEigenform(M::ModSym) -> RngSerPowElt
{The q-expansion of one of the Galois-conjugate newforms
associated to M, computed to absolute precision prec.  The
coefficients of the q-expansion lie in a quotient of a polynomial
extension of the base field of M.}

   prec := assigned M`qeigenform select M`qeigenform[1] else 8;
   return qEigenform(M,prec);
end intrinsic;

intrinsic qEigenform(M::ModSym, prec::RngIntElt : debug:=false) -> RngSerPowElt
{"} // "
   if IsMultiChar(M) then
      return qEigenform(AssociatedNewformSpace(M), prec);
   end if;

   prec := Max(2,prec);
   if not assigned M`qeigenform or M`qeigenform[1] lt prec then

//      require IsCuspidal(M) : "Argument 1 must be cuspidal.";

      if IsMultiChar(AmbientSpace(M)) then
         return qEigenform(AssociatedNewformSpace(M),prec);
      end if;

      if assigned M`associated_new_space then
         if Level(AssociatedNewSpace(M)) lt Level(M) then
            return qEigenform(AssociatedNewSpace(M),prec);   
         end if;
      end if;

      if Characteristic(BaseField(M)) eq 0 then
         D := NewformDecomposition(M);
         require #D eq 1 : "Argument 1 must correspond to a single Galois-conjugacy class of newforms.";
         M := D[1]; 
         if assigned M`qeigenform and M`qeigenform[1] ge prec then
            return M`qeigenform[2] + O((Parent(M`qeigenform[2]).1)^prec);
         end if;
      end if;
     
      vprintf ModularSymbols,1: 
         "Finding eigenvector for newform modular symbols space of dimension %o ... \n", Dimension(M);
      time0 := Cputime();
      if Sign(M) ne 0 or Dimension(M) eq 1 then
         eig := EigenvectorModSym(M);    
      else
         eig := EigenvectorModSymSign(M,IsMinusQuotient(M) 
                                           select -1 else +1);
      end if;

      if IsVerbose("ModularSymbols") then
         printf " ... finding eigenvector took %o sec\n", Cputime(time0);
         printf "Computing q-expansion of eigenform ... \n";
         IndentPush();
         tm := Cputime();
      end if;
     
      require not (eig cmpeq false): "Argument 1 must correspond to a newform.";

      if assigned M`one_over_ei then
         i, ei, one_over_ei := Explode(M`one_over_ei);
         if eig[i] cmpne ei then  // it came out of some other eig (now unknown)
            one_over_ei := false; 
         end if;
      else 
         one_over_ei := false;
      end if;
         
      if one_over_ei cmpeq false then 
         dummy := exists(i) { i : i in [1..Degree(eig)] | eig[i] ne 0 };
      end if;

      if not assigned M`qeigenform then  
         M`qeigenform := <1, PowerSeriesRing(Parent(eig[1]))!0>;
      end if;
      
      if prec gt 10 then 
         vprintf ModularSymbols,2: "Setting up the Tpei (for p less than %o) ... ", prec;
      end if;
      time0 := Cputime();
      Tpei := HeckeImages(AmbientSpace(M),i, prec);                         // "time critical"
      vprintf ModularSymbols,2: "%os\n", Cputime(time0);
      
      M`qeigenform[2], new_one_over_ei := Compute_qExpansion(M`qeigenform[1], M`qeigenform[2],
                                       prec, Tpei,
                                       DirichletCharacter(M), Weight(M),
                                       i, eig, false : one_over_ei:=one_over_ei);

      M`qeigenform[1] := prec;
      if one_over_ei cmpeq false then 
         M`one_over_ei := <i, eig[i], new_one_over_ei>;
      end if;
      if IsVerbose("ModularSymbols") then
         IndentPop();
         printf " ... %os for computing q-expansion of eigenform\n", Cputime(tm);
      end if;
   end if;
   return M`qeigenform[2] + O((Parent(M`qeigenform[2]).1)^prec);
end intrinsic;
 

function EisensteinConstantCoefficient(M)
   if GetVerbose("ModularSymbols") ge 2 then
      print "WARNING: constant coefficient of Eisenstein series *might* be incorrect.";
   end if;
   eps := DirichletCharacter(M);
   f   := Conductor(eps);
   if f ne Modulus(eps) then
      eps := Restrict(eps,f);
   end if;
   return Coefficient(PrimitiveEisensteinSeries(Weight(M),eps,1),0);
end function;


function Compute_qExpansion(num_known, f, prec, Tpei, eps, 
                            k, i, eig, prime_only : one_over_ei:=false)

debug := false;
if debug then SetVerbose("ModularSymbols",2); end if;
   
   degr := Degree(Parent(eig[i]));
   if one_over_ei cmpeq false then 
      if IsVerbose("ModularSymbols") and degr ge 30 then
         printf "Computing inverse of (nasty) element in a field of degree %o\n", degr;
      end if;
      time0 := Cputime();
      one_over_ei := 1/eig[i];
      if IsVerbose("ModularSymbols") and degr ge 30 then
         printf " ... phew! Got the inverse in %os\n", Cputime(time0);
      end if;
   elif debug then  
      assert one_over_ei * eig[i] eq 1;  // the calling function should ensure this
   end if;

   R<q> := Parent(f);

if debug then SetVerbose("ModularSymbols",3); end if;
   vprintf ModularSymbols,2: "Computing coefficients of eigenform:\n";

   for n in [num_known..prec-1] do
      if degr ge 100 then vprintf ModularSymbols,3: "coeff%o...", n; end if;
      n_time0 := Cputime();
     
     if n eq 1 then
         an := 1;
      elif IsPrime(n) then

         an := DotProd(Tpei[PrimePos(n)],eig) * one_over_ei;

      elif not prime_only then
         fac := Factorization(n); 
         if #fac eq 1 then
            // a_{p^r} := a_p * a_{p^{r-1}} - eps(p)p^{k-1} a_{p^{r-2}}.
            p  := fac[1][1];
            r  := fac[1][2];
            an := Coefficient(f,p) * Coefficient(f,p^(r-1))
                     - Evaluate(eps,p)*p^(k-1)*Coefficient(f,p^(r-2));
         else  // a_m*a_r := a_{mr} and we know all a_i for i<n.
            m  := fac[1][1]^fac[1][2];
            an := Coefficient(f,m)*Coefficient(f,n div m);
         end if;            
      else
         an := Parent(f)! 0;
      end if;
      f +:= an * q^n;
      if degr ge 100 then vprintf ModularSymbols,3: "%os, ", Cputime(n_time0); end if;
   end for;

   if degr ge 100 then vprintf ModularSymbols,3: "\n"; end if;
if debug then SetVerbose("ModularSymbols",2); end if;

   return f, one_over_ei;
end function;


intrinsic qIntegralBasis(D::SeqEnum,
                         prec::RngIntElt :
                         Al := "Newform") -> SeqEnum
{The integral basis of q-expansions for the
sum of the spaces of modular forms associated to the modular symbols
spaces in D, computed to absolute precision prec.  
The base field must be either the rationals or a cyclotomic field.}
   prec := Max(2,prec);
   if #D eq 0 then
      return [];
   end if;
/*   require BaseField(D[1]) cmpeq RationalField():
          "The base field of argument 1 must be the rationals.";
*/
   S := SaturatePolySeq(&cat[qIntegralBasis(B,prec : Al := Al) : B in D ],prec);
   R:=Parent(S[1]);
   q:=R.1;
   return [ f+O(q^prec) : f in S | not IsWeaklyZero(f+O(q^prec)) ];
end intrinsic;


forward qExpansionBasisNewform,
        qExpansionBasisUniversal;


intrinsic qExpansionBasis(D::[ModSym],
                          prec::RngIntElt :
                          Al := "Newform") -> SeqEnum
{The K-vector space basis of q-expansions in reduced row echelon
form for the sum of the spaces of modular forms associated to the
modular symbols spaces in D, where K is their common base field.
The absolute precision of the q-expansions is prec.}
   prec := Max(2,prec);
   S  := EchelonPolySeq(&cat[qExpansionBasis(B,prec : Al := Al) : B in D],prec);
   R:=Universe(S);
   q:=R.1;
 //return [ f+O(q^prec) : f in S | not IsWeaklyZero(f+O(q^prec)) ];
   // save memory
   for i := #S to 1 by -1 do 
      if Valuation(S[i]) lt prec then 
        S[i] +:= O(q^prec); 
      else 
        Remove(~S,i); 
      end if;
   end for;
   return S;
end intrinsic;

intrinsic qExpansionBasis(M::ModSym:
                          Al := "Newform") -> SeqEnum
{The K-vector space basis of q-expansions in reduced row echelon
form for the space of modular forms associated to M, where K is
the base field of M.  The absolute precision of the q-expansions
is prec.

The optional parameter Al can take the values "Newform"
and "Universal".  The default is "Newform", which computes
a basis of q-expansions by finding a decomposition of M into subspace 
corresponding to newforms, computing their q-expansions, and then
taking all of their images under the degeneracy maps.  If 
Al is set equal to "Universal" then the algorithm described
in Merel's paper "Universal Fourier expansions of modular forms"
is used instead.  This latter algorithm does not require computing
a newform decomposition of M, but requires computing the action
of more Hecke operators.}
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   require Al eq "Universal" or Al eq "Newform" :
       "Al paramater must equal either \"Universal\" or \"Newform\".";

   prec := assigned M`qexpbasis select M`qexpbasis[1] else 8;
   return qExpansionBasis(M, prec : Al := Al);
end intrinsic;

intrinsic qExpansionBasis(M::ModSym, prec::RngIntElt :
                          Al := "Newform") -> SeqEnum
{"} // "
   prec := Max(2,prec);

   require IsCuspidal(M) : "Argument 1 must be cuspidal.";

   require Al eq "Universal" or Al eq "Newform" :
       "Al paramater must equal either \"Universal\" or \"Newform\".";

   if assigned M`al_decomp then
      Al := "Universal";
      vprint ModularSymbols, 1: "Since M is got by an Atkin-Lehner decomposition, switching ";
      vprint ModularSymbols, 1: "to Merel's algorithm.  I'm *not* convinced that Merel's algorithm works";
      vprint ModularSymbols, 1: "on Atkin-Lehner spaces.  Note that the lemma on page 112 of SLNM 1585 ";
      vprint ModularSymbols, 1: "claims it should, but I don't believe that proof.";
   end if;

   require Characteristic(BaseField(M)) eq 0 or
           Al eq "Universal":
       "The characteristic of the base field must equal 0.  Try qEigenform on an irreducible space instead.";

   if IsMultiChar(M) then
      return qExpansionBasis(AssociatedNewformSpace(M), prec: Al := Al);
   end if;

   if Dimension(M) eq 0 then
      return [];
   end if;

   if not assigned M`qexpbasis then
      M`qexpbasis := [* 0,[PowerSeriesRing(BaseField(M))!0] *];
   end if;
   if M`qexpbasis[1] lt prec then
      if IsVerbose("ModularSymbols") then
         printf "Computing q-expansion basis at level %o.\n", Level(M);
      end if;
      M`qexpbasis[1] := prec;
      M`qexpbasis[2] := Al eq "Universal" select
                        qExpansionBasisUniversal(M,prec, false) else
                        qExpansionBasisNewform(M,prec, false);
   end if;
   _<q> := Universe(M`qexpbasis[2]);
   return [f + O(q^prec) : f in M`qexpbasis[2] | not IsWeaklyZero(f+O(q^prec)) ];
end intrinsic;


intrinsic qIntegralBasis(A::ModSym:
                         Al := "Newform") -> SeqEnum
{The integral basis of q-expansions in reduced form for the
space of modular forms associated to M, computed to absolute precision prec.  
The base field must be either the rationals or a cyclotomic field.}
   require Type(BaseField(A)) in {FldRat, FldCyc} : 
                 "The base field must be either the rationals or a cyclotomic field.";
   require IsCuspidal(A) : "Argument 1 must be cuspidal.";
   require Al eq "Universal" or Al eq "Newform" :
         "Al paramater must equal either \"Universal\" or \"Newform\".";

   prec := assigned A`qintbasis select A`qintbasis[1] else 8;
   return qIntegralBasis(A, prec : Al := Al);
end intrinsic;

intrinsic qIntegralBasis(A::ModSym, prec::RngIntElt :
                         Al := "Newform") -> SeqEnum
{"} // "
   prec := Max(2,prec);

   if assigned A`al_decomp then
      Al := "Universal";
      vprint ModularSymbols, 1: "Since M is got by an Atkin-Lehner decomposition, switching ";
      vprint ModularSymbols, 1: "to Merel's algorithm.  I'm *not* convinced that Merel's algorithm works";
      vprint ModularSymbols, 1: "on Atkin-Lehner spaces.  Note that the lemma on page 112 of SLNM 1585 ";
      vprint ModularSymbols, 1: "claims it should, but I don't believe that proof.";
   end if;

   require Type(BaseField(A)) in {FldRat, FldCyc} : 
                 "The base field must be either the rationals or a cyclotomic field.";
   require IsCuspidal(A) : "Argument 1 must be cuspidal.";
   require Al eq "Universal" or Al eq "Newform" :
         "Al paramater must equal either \"Universal\" or \"Newform\".";

   if Dimension(A) eq 0 then
      return [];
   end if;

   if IsMultiChar(A) then
      if HasAssociatedNewformSpace(A) then
         B := AssociatedNewformSpace(A);
         Q := qIntegralBasis(B, prec: Al := Al);
         // Include to level the level of A.
         // R := SpaceGeneratedByImages(Q, Level(A) div Level(B), IntegerRing(), true, prec);
         // Steve's comment: I'm not sure why this call to 'SpaceGeneratedByImages' 
         // was commented out ... is it redundant, or just in the wrong place?  
         return Q;
      else
         // I think this was wrong -- we should include the 'SpaceGeneratedByImages'
         // of pieces of the NewformDecomposition that have lower level than A.
         //    -- Steve
         /*
         D := NewformDecomposition(A);
         return qIntegralBasis(D,prec : Al := Al);
         */
         R := PowerSeriesRing(BaseRing(A));  
         unsaturated := [R| ];
         for NF in NewformDecomposition(A) do 
            qexps_NF := qIntegralBasis(NF, prec : Al:=Al);
            if Level(NF) ne Level(A) then
               assert Level(A) mod Level(NF) eq 0;
               // no point in saturating until the final step, I guess
               qexps_NF := SpaceGeneratedByImages(qexps_NF, 
                                 Level(A) div Level(NF), BaseRing(A), false, prec);
            end if;
            unsaturated cat:= qexps_NF;
         end for;
         S := SaturatePolySeq(unsaturated, prec);
         delete unsaturated;
         _<q> := Universe(S);
         for i := #S to 1 by -1 do 
            if Valuation(S[i]) lt prec then 
              S[i] +:= O(q^prec); 
            else 
              Remove(~S,i); 
            end if;
         end for;
         return S;
      end if;
   end if;

   if not assigned A`qintbasis then
      A`qintbasis := [* 0,[PowerSeriesRing(Integers())!0] *];
   end if;
   if A`qintbasis[1] lt prec then
      if IsVerbose("ModularSymbols") then
         printf "Computing q-integral basis at level %o.\n", Level(A);
         if Al eq "Univeral" then
            printf "Using Universal Fourier expansion algorithm.\n";
         end if;
      end if;
      if Al eq "Universal" then 
         prec := Max(prec, HeckeBound(A));
         ans := qExpansionBasisUniversal(A, prec, true);
      else
         ans := qExpansionBasisNewform(A, prec, true);
      end if;
      A`qintbasis[2] := ans;
      A`qintbasis[1] := prec;
   end if;
   if BaseRing(Universe(A`qintbasis[2])) eq Rationals() then 
      ChangeUniverse( ~A`qintbasis[2], PowerSeriesRing(Integers()) );
   end if;
   _<q> := Universe(A`qintbasis[2]);
   return [f + O(q^prec) : f in A`qintbasis[2] | not IsWeaklyZero(f+O(q^prec)) ];
end intrinsic;

function SpaceGeneratedByImages(C, N, F, do_saturate, prec : debug:=false)
// Compute the images of the q-expansion f given by the vectors in the 
// sequence C under the maps f(q) |---> f(q^d) for each divisor d of N.    
// The q-expansions are coerced into F[[q]], and if
//   do_saturate = true:  compute Hermite normal form for restriction
//                        of scalars to F[[q]] (here F=integers)
//   do_saturate = false: compute echelon form over the field F.

// C may contain either power series or vectors.
// When power series, they are expected to have Valuation at least 1.
// Vectors v are taken to represent the series v[1]*q + ... + v[n]*q^n.

   R := PowerSeriesRing(F);
   q := R.1;
   if #C eq 0 then
      return [R|];
   end if;

   if not do_saturate and ISA( Type(C[1]), ModTupRngElt) then
     // feed a sequence of vectors to EchelonPolySeq 
     // TO DO: change SaturatePolySeq so it will accept vectors too
     V0 := Universe(C);
     V := VectorSpace(BaseRing(V0), prec);
     // WARNING: V0 could have dimension *less* than prec-1
     ans := [V| ];
//"Messing around with vectors"; time 
     for b in C do 
        for d in Divisors(N) do 
           v := [BaseRing(V)| 0 : i in [0..Dimension(V)-1]];  // the 0'th entry will stay 0
           for i := 1 to prec do 
              if i*d ge prec then break; end if;
              k := i*d+1;
              v[k] := (i le Ncols(b)) select b[i] else 0;
           end for;
           Append(~ans, V!v);
        end for;
     end for;
   else
     if ISA( Type(C[1]), ModTupRngElt) then
        C := [q*R!Eltseq(b) : b in C];
     else 
        assert ISA( Type(Universe(C)), RngSer);
        if BaseRing(Universe(C)) ne BaseRing(R) then ChangeUniverse(~C, R); end if;
     end if;
     ans := [];
     for f in C do
        Append(~ans, f);
        for d in Divisors(N) do
          if d ne 1 then
              ff := Evaluate(f, q^d);
              Append(~ans, ff);
          end if;
        end for;
     end for;
   end if;

   if do_saturate then
      if Type(BaseRing(Parent(C[1]))) eq FldCyc then
         // project ans onto rational field, using restriction of scalars:
         Q<q> := PowerSeriesRing(Integers());
         ans2 := [];
         for f in ans do
            d := LCM([Denominator(Coefficient(f,n)) : n in [0..Degree(f)]]);
            g := d*f;
            for i in [1..Degree(BaseRing(Parent(C[1])))] do
               Append(~ans2, &+[Integers()!(Eltseq(Coefficient(g,n))[i])*q^n : n in [0..Degree(g)]]);
            end for;
         end for;
         ans := ans2;
      end if;
      return SaturatePolySeq(ans,prec);
   end if;  
   ans := EchelonPolySeq(ans,prec);
   return ans;
end function;

function qExpansionBasisNewform(A, prec, do_saturate)
   assert IsCuspidal(A);
   assert prec ge 1;

   debug:=false;
   if debug then SetVerbose("ModularSymbols",2); end if;                          

   if debug then
   print "**** Called qExpansionBasisNewform with prec", prec, "and do_saturate", do_saturate;
   end if;

   if do_saturate then
      assert Type(BaseField(A)) in {FldRat, FldCyc};
   end if;

   if debug and not assigned A`newform_decomposition and not HasAssociatedNewSpace(A) 
            and not assigned CuspidalSubspace(AmbientSpace(A))`newform_decomposition then
     printf "**** Computing NewformDecomposition of %o ...\n", A;
     time   D := NewformDecomposition(A : Sort := false);
     print "  ... for NewformDecomposition ****";
     print "  NewformDecomposition is:\n", D;
   end if;
 
   D := NewformDecomposition(A : Sort := false);

   if #D gt 1 then
      if do_saturate then
         return qIntegralBasis(D,prec : Al:="Newform");
      else
         return qExpansionBasis(D,prec : Al:="Newform"); 
      end if;
   else
      A`associated_new_space := D[1]`associated_new_space;
      if debug then 
         print "Calling qEigenform ...";
         IndentPush(); time0 := Cputime();
      end if;
      f := qEigenform(A,prec : debug:=debug);
      if debug then 
         IndentPop();
         printf " ... qEigenform took %os\n", Cputime(time0);
      end if;
      Q := BaseRing(Parent(f));
      V := VectorSpace(BaseField(A),#Eltseq(f));
      if Q cmpeq BaseField(A) then
         seq := Eltseq(f);
         B := [V!seq];
         F := (do_saturate and Type(BaseField(A)) eq FldRat) 
                             select Integers() else BaseField(A);
      else
         if ISA( Type(Q), FldNum) then
            V := VectorSpace(BaseField(A), prec-1); // note that the dimension may be different
                                                    // because Eltseq(f) omits trailing zeros
            // TO DO: make the next line optimal
            // time 
            coeffs := [ Eltseq(Coefficient(f,i)) : i in [1..prec-1] ];
            B := [V! [coeffs[i][j] : i in [1..#coeffs]] : j in [1..Degree(Q)]];
            delete coeffs;
         else
            assert Type(Q) eq RngUPolRes;
            // this is what was here previously:
            g := Modulus(Q);
            n := Degree(g);
            R := PreimageRing(Q);
            B := [V![Coefficient(R!a,j) : a in Eltseq(f)] : j in [0..n-1]];
         end if;
         if do_saturate 
            and Type(BaseField(A)) eq FldRat then
               // Steve changed this
               // C := Basis(Saturate(B));
               B := Saturation(Matrix(B));
               r := Nrows(B);
               B := [ B[i] : i in [1..r] ];
               F := Integers();
         else
            F := BaseField(A);
         end if;
      end if;
      assert #B gt 0;
      // B may contain either vectors or power series (see SpaceGeneratedByImages)
      return SpaceGeneratedByImages(B, Level(A) div Level(AssociatedNewSpace(A)), 
                                    F, do_saturate, prec : debug:=debug);
   end if;
end function;


/* Surprisingly, this algorithm turns out to be very slow, because 
   the list of Heilbronn matrices for T_n, with n composite, is 
   too large.

   However, it works for modular symbols in characteristic p, whereas
   the other algorithm seems to not. */
function qExpansionBasisUniversal(M, prec, do_saturate)
// Computes a basis of q-expansions for M to precision at least prec.
// If prec is too small, not enough vectors will be computed.
// If do_saturate is true, then the basis is saturated in Z[[q]].
//   assert IsCuspidal(M);
   if prec lt 2 then 
      prec := 2;
   end if;
   if do_saturate then
      if Type(BaseField(M)) ne FldRat then
         error "qIntegralBasis using the Universal algorithm is not programmed.";
      end if;
   end if;

   V := VectorSpace(BaseField(M),prec-1);
   W := sub<V|0>;
   goal := Dimension(M);
   e := [i : i in [1..Degree(M)] | 
        exists(b) { b : b in Basis(DualRepresentation(M)) | Eltseq(b)[i] ne 0}];
   i := 1;
   if Sign(M) eq 0 then
      goal := goal div 2;
      S := PlusSubspaceDual(CuspidalSubspace(M));
   else
      S := CuspidalSubspace(M);
   end if;
   pi := Transpose(RMatrixSpace(BaseField(M),
                   Dimension(S),Degree(S))!Basis(DualRepresentation(S)));
   while Dimension(W) lt goal and i le #e do
      // Hit basis vector i by T_1, ..., T_prec.  (this is fast)
      ims := HeckeImagesAll(M,e[i], prec-1);
      // Now project each image onto the cuspidal subspace
      pi_ims := [Representation(ims[l])*pi : l in [1..prec-1]];            
      // make a subspace from the transposes...
      W +:= sub<V|[[pi_ims[j][k] : j in [1..#pi_ims]]:
                                  k in [1..Degree(pi_ims[1])]] >;
      i +:= 1;
   end while; 
   if Dimension(W) ne goal then
      vprint ModularSymbols : "WARNING: qExpansion basis has too small of dimension.";
   end if;
   R<q>:=PowerSeriesRing(BaseField(M));
   if do_saturate then
      d := LCM([Integers()|Denominator(b[n]) : n in [1..prec-1], b in Basis(W)]);
      C := [&+[d*b[n]*q^n : n in [1..prec-1]] : b in Basis(W)];
      return SaturatePolySeq(C,prec);
   else
      return EchelonPolySeq([&+[b[n]*q^n : n in [1..prec-1]] : b in Basis(W)],prec);
   end if;
end function;



/*************************************************************
 *                                                           *
 *  EIGENVALUES: COMPUTATION OF HECKE EIGENVALUES            *
 *                                                           *
 *************************************************************/

function EigenvectorOfMatrixWithCharpoly(T, f)
/* Let T be an nxn matrix over K with irreducible characteristic
 polynomial f.  This function returns an eigenvector for T
 over the extension field K[x]/(f(x)). */

   // This is implemented using a quotient of a polynomial ring
   // because this works generically for any field.
   n  := Degree(f);
   K  := Parent(T[1,1]);
   if n eq 1 then
      return VectorSpace(K,n)![1];
   end if;
   
   vprintf ModularSymbols,1: "Calling EigenvectorOfMatrixWithCharpoly ... ";
   time0_eig := Cputime();

   if Type(K) eq FldRat or ISA(Type(K),FldAlg) then
      L<a> := ext< K | f : DoLinearExtension, Check:=false>;
   else
      // still occurs in the finite characteristic case
      R := PolynomialRing(K);
      L<a> := quo<R | f>;
   end if;
   b    := 1/a;
   c    := [-b*Coefficient(f,0)];
   for i in [1..Degree(f)-1] do
      Append(~c, (c[i] - Coefficient(f,i))*b);
   end for;

   Ln := RSpace(L,n);     // magma is weird in that it can take *way* too long to do this!
                          // (possible thing to optimize)  see remarks in same function 
                          // level1.m in ModFrm package
                          //
                          // This will have changed because we're using number fields now,
                          // not quo's. I think this problem has been fixed for quo's, anyway.  
                          //   --- Steve
   time0 := Cputime();
   
   if Type(K) eq FldRat then
      S := IntegerRing();
      denom := LCM([Denominator(x): x in Eltseq(T)]);
      // "denom:", denom;
      denom_scale := 1/denom;
      T := Matrix(S, denom*T);
   else
      S := L;
      T  := RMatrixSpace(L,n,n)!T;
      denom := 1;
      denom_scale := 1;
   end if;
 if Cputime(time0) gt 1 then "RMatrixSpace coercion", Cputime(time0); end if;

   Ln := RSpace(L, n);
   Sn := RSpace(S, n);
   v  := Sn!0;

   repeat
      v[Random(1,n)] +:= 1;
      w  := c[1]*Ln!v;
      vv := v;
      scale := denom_scale;
// "eigen loop", #c; time
      for i in [2..#c] do 
 time0 := Cputime();
         vv := vv*T;
 time1 := Cputime(time0);
         //w +:= c[i]*vv;
         u := Ln!vv;
 time2 := Cputime(time1);
	 if denom_scale ne 1 then
	    e := Eltseq(vv);
	    g := GCD(e);
	    if g ne 1 then
		// printf " {GCD %o}", g;
		vv := Parent(vv)![x div g: x in e];
		scale *:= g;
	    end if;
	    u := Ln!vv;
	    u := scale*u;
	    scale *:= denom_scale;
	 else
	    u := Ln!vv;
	 end if;
         w +:= c[i]*u;
 time3 := Cputime(time0);
 //printf "  %o", [time1, time3-time1];
      end for;
   until w ne Parent(w)! 0;
   
   vprintf ModularSymbols,1: "%os\n", Cputime(time0_eig);

   return w;   
end function;


function deg_set(L)
    if #L eq 0 then
	return { 0 };
    end if;

    t := L[#L];
    Prune(~L);
    DD := deg_set(L);
    d := Degree(t[1]);
    m := t[2];
    D := DD;
    for i := 1 to m do
	D join:= { x + d: x in D };
    end for;

    return D;
end function;


// For a matrix X over F, test whether the min poly of the reduction of X 
// has full degree (reduction in a random residue field GFp of F).
// 
// This is called for X belonging to an irreducible Hecke algebra,
// ie a matrix algebra over F isomorphic to a field extension of F.
// In this situation, X either generates the extension, or else 
//   char_poly(X) = min_poly(X)^e with e > 1
// which then also holds over GFp.
//
// SRD, November 2010

function QuickIrredTest(X)

    F := BaseRing(Parent(X));
    n := Ncols(X);

    B := 11863283;
    p := Random(Round(2/3 * B), B);

    if Type(F) in {RngInt, FldRat} then 
        repeat
            p := NextPrime(p);
            A := MatrixAlgebra(GF(p), n);
            l, Y := IsCoercible(A, X);
        until l;
    else
        assert IsAbsoluteField(F);
        flag := false;
        repeat
            p := NextPrime(p);
            if not exists(P){tup[1] : tup in Factorization(p*Integers(F)) | Degree(tup[1]) eq 1} then
                continue; 
            end if;
            GFp, res_map := ResidueClassField(P);
            res_map := hom< F -> GFp | F.1 @ res_map >;
            _, res_map := ChangeRing(Parent(X), GFp, res_map);
            try 
                Y := X @ res_map;
                flag := true;
            catch ERR
                flag := false;
            end try;
        until flag;
    end if;

    f := MinimalPolynomial(Y);
    return Degree(f) eq n;

end function;

function FindIrreducibleHeckeOperator(A)
    // Find a linear combination of Hecke operators whose
    // charpoly on A is irreducible. 

    vprintf ModularSymbols, 1: 
        "Looking for an irreducible element in the Hecke algebra of %o\n", A;
    IndentPush();

    use_quick := t in {RngInt, FldRat} or ISA(t, FldAlg) where t is Type(BaseRing(A));

    p := SmallestPrimeNondivisor(Level(A), 2);
    T := DualHeckeOperator(A, p);

    i := 1;
    str := "T_" * IntegerToString(p);
    while true do
	vprintf ModularSymbols, 2:
	    "FindIrreducibleHeckeOperator, try #%o, %o\n", i, str;
        if use_quick then
            if QuickIrredTest(T) then
                 vprintf ModularSymbols, 2: "CharacteristicPolynomial: "; 
                 vtime ModularSymbols, 2:
                 f := CharacteristicPolynomial(T);
                 // assert IsIrreducible(f);
                 break;
            end if;
        else
            f := CharacteristicPolynomial(T);
            if IsIrreducible(f) then
                break;
            end if;
        end if; 

	if i eq 15 then
            "WARNING: it seems hard to find an irreducible element in the Hecke algebra.";
	    if Characteristic(BaseRing(A)) gt 0 then
                "In characteristic p, the algorithm is not guaranteed to terminate.";
	    end if;
	end if;

	p := SmallestPrimeNondivisor(Level(A), NextPrime(p));
        rand := Random([-1,1]);
        T +:= rand*DualHeckeOperator(A,p);
        str *:= " + " * IntegerToString(rand) * "*T_" * IntegerToString(p);
	i +:= 1;
    end while;
   
    IndentPop();
    vprintf ModularSymbols,1: 
        "Irreducible element of Hecke algebra (of dimension %o) is %o\n", Dimension(A),str;
    return T, f;

end function;


function EigenvectorBeforeLift(A)
   T, f := FindIrreducibleHeckeOperator(A);
   return EigenvectorOfMatrixWithCharpoly(T,f);
end function;

function EigenvectorModSym(A)
   // Returns an eigenvector of the Hecke algebra on A over
   // a polynomial extension of the ground field.
   // The eigenvector lies in DualSpace(A) tensor Qbar.
   if not assigned A`eigen then
      e := EigenvectorBeforeLift(A);
      F := Parent(e[1]);
      V := RSpace(F,Degree(A));
      // B := [V!b : b in Basis(DualRepresentation(A))];
      // A`eigen := &+[e[i]*B[i] : i in [1..#B]];
      B := Basis(DualRepresentation(A));
      sum := V!0;
      for i := 1 to #B do
	sum +:= e[i]*V!B[i];
      end for;
      A`eigen := sum;
   end if;
   return A`eigen;
end function;


function EigenvectorModSymSign(A, sign)
// Compute eigenvector for sign subspace of A.
   assert sign eq -1 or sign eq 1 ;
   if IsPlusQuotient(A) then
      assert sign ne -1;
      return EigenvectorModSym(A);
   end if ;
   if IsMinusQuotient(A) then
      assert sign ne +1 ;
      return EigenvectorModSym(A);
   end if ;
   if sign eq +1 then
      if not assigned A`eigenplus then
         A`eigenplus := EigenvectorModSym(PlusSubspaceDual(A));   
      end if;
      return A`eigenplus;
   end if;
   if sign eq -1 then
      if not assigned A`eigenminus then
         A`eigenminus := EigenvectorModSym(MinusSubspaceDual(A));   
      end if;
      return A`eigenminus;
   end if;
end function;


function EigenformInTermsOfIntegralBasis(A) 
/*
  Returns the linear combination of qIntegralBasis(A,n)
  which gives qEigenform(A,n), where n is HeckeBound(A).

    *  1) Find pivot columns for the integral basis     *
    *  2) Invert                                        *
    *  3) Obtain eigenform in terms of integral basis   *

*/

   if not assigned A`eigenint then

      vprint ModularSymbols : "Writing eigenform in terms of integral basis...";
      B := qIntegralBasis(A,HeckeBound(A)+1);
      f := qEigenform(A,HeckeBound(A)+1);      
      F := BaseRing(Parent(f));
      d := AbsolutePrecision(f)-1;
      V := VectorSpace(F,d);
      fvec := V![Coefficient(f,n) : n in [1..d]];
      Bvec := [V![Coefficient(g,n) : n in [1..d]] : g in B];
      W := VectorSpaceWithBasis(Bvec);
      A`eigenint := Eltseq(Coordinates(W,fvec));

   end if;
   return A`eigenint;

end function;


intrinsic Eigenform(E::CrvEll, prec::RngIntElt) -> RngSerPowElt
{The q-expansion of the newform attached to the elliptic curve E.}
   return qEigenform(E, prec);
end intrinsic;


intrinsic qEigenform(E::CrvEll, prec::RngIntElt) -> RngSerPowElt
{"} // "

   require BaseRing(E) cmpeq RationalField() : "The base ring of argument 1 must be the rational field.";
   
   E := MinimalModel(E);
   R<q>:=PowerSeriesRing(Integers());
   f := R!0;
   D := Integers()!Discriminant(E);

   for n in [1..prec-1] do
      if n eq 1 then
         an := 1;
      elif IsPrime(n) then
         if D mod n eq 0 then
            case ReductionType(E,n):
               when "Additive": an := 0;
               when "Split multiplicative": an := 1;
               when "Nonsplit multiplicative": an := -1; 
               when "Good" : error "Bug in qExpansion.";
            end case;
         else
            an := FrobeniusTraceDirect(E,n);
         end if;
      else
         fac := Factorization(n); 
         if #fac eq 1 then
            p  := fac[1][1];
            r  := fac[1][2];
            an := Coefficient(f,p) * Coefficient(f,p^(r-1))
                     - (D mod p eq 0 select 0 else p*Coefficient(f,p^(r-2)));
         else  // a_m*a_r := a_{mr} and we know all a_i for i<n.
            m  := fac[1][1]^fac[1][2];
            an := Coefficient(f,m)*Coefficient(f,n div m);
         end if;            
      end if;
      f +:= an * q^n;
   end for;
   return f+O(q^prec);
end intrinsic;


intrinsic CompactSystemOfEigenvaluesVector(M::ModSym, prec::RngIntElt) 
                                                    -> SeqEnum
{Exactly the same as CompactSystemOfEigenvalues, but returns
only the vector and not the map.}

   require Sign(M) ne 0 : "Argument 1 must have nonzero sign.";
   if IsMultiChar(M) then
      return CompactSystemOfEigenvaluesVector(AssociatedNewformSpace(M), prec);
   end if;

   phi := RationalMapping(M);

   // It is important that the i chosen here be the first so that
   // phi(M.i) ne 0, because this is assumed when computing psi below.
   i := 1;
   while IsZero(phi(AmbientSpace(M).i)) do
      i := i+1;
   end while;

   // Compute the vector [...v_i...]   
   // This can be optimized more! 
   Tpe := HeckeImages(AmbientSpace(M),i, prec);
   vec := [phi(Tpe[n]) : n in [1..#[p : p in [2..prec] | IsPrime(p)]]];

   return vec;
end intrinsic;

// suggested by John Cremona.
intrinsic CompactSystemOfEigenvalues(M::ModSym, prec::RngIntElt) 
                                                    -> SeqEnum, Map
{Elements [v_2, v_3, v_5, v_7, ...,v_p] of a vector space and a
map psi such that psi(v_i) = a_i, where a_i is the ith Fourier
coefficient of one of the newforms corresponding to M.
The prime p is the largest prime <= prec.   This 
intrinsic takes far less memory and the output is MUCH more 
compact than SystemOfEigenvalues.  To get everything over Q when M
is defined over a cyclotomic extension, use CompactSystemOfEigenvaluesOverQ.} 

   require Sign(M) ne 0 : "Argument 1 must have nonzero sign.";

   require HasAssociatedNewSpace(M) : 
          "Argument 1 must have been constructed using NewformDecomposition.";
 
   if IsMultiChar(M) then
      return CompactSystemOfEigenvalues(AssociatedNewformSpace(M), prec);
   end if;

   vec := CompactSystemOfEigenvaluesVector(M, prec);

   // compute the map psi.
   if not assigned M`field_embedding then
      s := Cputime();
      eig := EigenvectorBeforeLift(M);
      eig := eig / eig[1];
   
      // The map PSI is just the dot product with eig.
      K := Parent(eig[1]);
      phi := RationalMapping(M);
      M`field_embedding := hom<Codomain(phi) -> K | v :-> DotProd(v, eig)>;
      vprint ModularSymbols : "computing psi took ", Cputime(s);
   end if;
   return vec, M`field_embedding;   
end intrinsic;

// needed for the modular forms database
intrinsic CompactSystemOfEigenvaluesOverQ(M::ModSym, prec::RngIntElt) -> SeqEnum, Map
{Exactly the same as CompactSystemOfEigenvalues, but coefficients of the answer are in
Q instead of a cyclotomic extension of Q.}
   require Sign(M) ne 0 : "Argument 1 must have nonzero sign.";

   require HasAssociatedNewSpace(M) : 
          "Argument 1 must have been constructed using NewformDecomposition.";
 
   if Type(BaseField(M)) eq FldRat then
      V, psi := CompactSystemOfEigenvalues(M, prec);      
      return V, psi, hom<RationalField() -> RationalField() | >;
   end if;

   require not IsMultiChar(M) : "Argument 1 must not be a multicharacter space.";

   C := BaseField(M);  // a cyclotomic field.
   require Type(C) eq FldCyc : "The base field of argument one must be rational or cyclotomic.";
   z := C.1;    // primitive n-th root of unity
   n := CyclotomicOrder(C);   // n = order of z.
   phin := EulerPhi(n);
   V, phi := CompactSystemOfEigenvalues(M, prec);

   E := Domain(phi);  // a vector space over C.
   if Type(Codomain(phi)) eq RngUPolRes then
      f := Modulus(Codomain(phi));
      K := ext<C|f : Check:=false>; // field extension of C that contains the eigenvalues a_p.
      L<a> := AbsoluteField(K);  // comes equipped with coercion.
      inc := hom<Codomain(phi) -> L | L.1>;
   else
      L<a> := NumberField(DefiningPolynomial(C) : Check:=false);
      inc := hom<C -> L | L.1>;
   end if;

   //f2 := CharacteristicPolynomial(L.1);   
   W := VectorSpace(RationalField(), Degree(C)*Dimension(M));
   V2 := [W|&cat[Eltseq(e) : e in Eltseq(v)] : v in V];
   R := Domain(phi);
   function G(v)
      return [[v[phin*i+j] : j in [1..phin]] : i in [0..Dimension(M)-1]];
   end function;

   psi := hom<W -> L | v :-> inc(phi(R![C!x : x in G(v)]))>;

   return V2, psi, inc;
end intrinsic;



intrinsic SystemOfEigenvalues(M::ModSym, prec::RngIntElt) -> SeqEnum
{The system of Hecke eigenvalues [a2, a3, a5, a7, ..., a_p] attached to M, where
 p is the largest prime less or equal to prec.  The a_i lie in a quotient of 
 a polynomial extension of the base field of M.  It is assumed that M corresponds
 to a single Galois-conjugacy class of newforms.}

   require IsCuspidal(M) : "Argument 1 must be cuspidal.";

   if IsMultiChar(M) then
      return SystemOfEigenvalues(AssociatedNewformSpace(M), prec);
   end if;

   if assigned M`associated_new_space and not IsNew(M) then
        return SystemOfEigenvalues(AssociatedNewSpace(M),prec);   
   end if;

   if Characteristic(BaseField(M)) eq 0 then
      D := NewformDecomposition(M);
      require #D eq 1 : "Argument 1 must correspond to a single Galois-conjugacy class of newforms.";
      M := D[1];
   end if;

   if IsMultiChar(M) then
      return SystemOfEigenvalues(AssociatedNewformSpace(M), prec);
   end if;

   if Sign(M) ne 0 or Dimension(M) eq 1 then
      eig := EigenvectorModSym(M);    
   else
      eig := EigenvectorModSymSign(M,IsMinusQuotient(M) 
                                        select -1 else +1);
   end if;

   require not (eig cmpeq false): "Argument 1 must correspond to a newform.";

   dummy := exists(i) { i : i in [1..Degree(eig)] | eig[i] ne 0 };  // nonzero entry
   Tpei := HeckeImages(AmbientSpace(M),i, prec+1);                         // "time critical"
   f := Compute_qExpansion(0, PowerSeriesRing(Parent(eig[1]))!0, prec+1, Tpei,
                              DirichletCharacter(M), Weight(M), 
                              i, eig, true);   // true, so we only get the a_n with n prime.
   return [Coefficient(f,p) : p in [2..prec] |IsPrime(p)];

end intrinsic;


intrinsic qExpansion(M::ModSym, f::RngSerPowElt, prec::RngIntElt) -> RngSerPowElt
{Let f be an element of qExpansionBasis(M,AbsolutePrecision(f)).  This
intrinsic computes and returns the q-expansion of the modular form
associated to f, to precision prec.}

   f_prec := AbsolutePrecision(f);
   K := BaseRing(Parent(f));
   q := Parent(f).1;
   if prec le f_prec then  // trivial case
      return f + O(q^prec);
   end if;

   /* Recompute qExpansionBasis for M to precision prec, then
      write f as a linear combination of the basis. */
   B := qExpansionBasis(M,prec);
   V := VectorSpace(K,f_prec);
   vecs := [V![Coefficient(g,n) : n in [0..f_prec-1]] : g in B];
   W := VectorSpaceWithBasis([w : w in vecs | w ne 0]);
   v := V![Coefficient(f,n) : n in [0..f_prec-1]];
   require v in W : "Argument 2 must be the q-expansion of a modular form corresponding to an element of argument 1.";

   coords := Coordinates(W, v);
 
 //return &+[coords[i]*B[i] : i in [1..#coords]];

   // avoid creating (possibly bulky) sequence 
   ans := Parent(q)! 0;  
   for i := 1 to #coords do 
      ans +:= coords[i]*B[i];
   end for;
   return ans;
   
end intrinsic;

/*
intrinsic XXXEigenvectorInTermsOfIntegralBasis(M::ModSym) -> SeqEnum, RngIntElt
{A sequence v of elements of the field generated by the eigenvalues of a newform 
associated to M and an integer d such that the linear combination of qIntegralBasis(M,prec) 
defined by v is a d*(a newform).  M must have nonzero sign and have been constructed 
using NewformDecomposition. If thie}
   require Sign(M) ne 0 : "Argument 1 must have nonzero sign.";
   require HasAssociatedNewSpace(M) : 
          "Argument 1 must have been constructed using NewformDecomposition.";

   if not assigned M`eigenvector_in_terms_of_integral_basis then
      d := Dimension(M)*Degree(BaseField(M));
      prec := 1;
      for n in [1..2*d] do
         prec := NextPrime(prec);
      end for;
      tries := 1;
      while true do
         B := qIntegralBasis(M, prec+1);
         V, psi := CompactSystemOfEigenvaluesOverQ(M,prec);
         // Let H be the matrix whose columns are the 
         // prime-indexed columns of the matrix of coefficients of B.
         H := RMatrixSpace(RationalField(),d,#V)!(
                               &cat[[Coefficient(f,p) : p in [q : q in [2,prec]|IsPrime(q)]] : f in B]);

error "Need to add rank stuff like for rational version of this function.";
         
         // Let G be the matrix whose columns are the element of V.
         G := Transpose(RMatrixSpace(RationalField(),#V,d)!V);

         // Find a matrix A such that A*H=G.  Then the vector we want
         // is v*A, where v = [psi(W.i) : i in [1..Dimension(W)], 
         // where W = Domain(psi).   If we can't find such a matrix A,
         // increase the precision and try again.  If we fail 10 times,
         // abort. 
         t, A := IsConsistent(H,G);
         if not t then
            print "EigenvectorInTermsOfIntegralBasis: Forced to increase precision. Tries =", tries;
            tries := tries + 1;
            for i in [1..10] do 
               prec := NextPrime(prec);
            end for;
         else
            K := Codomain(psi);
            W := Domain(psi);
            v := VectorSpace(K,d)![psi(W.i) : i in [1..d]];
            A := MatrixAlgebra(Codomain(psi),d)!A;
            v := v*A;
            denom := DenominatorOf(v);
            M`eigenvector_in_terms_of_integral_basis := <denom*v, denom>;
            break;
         end if;
      end while;
   end if;
   return Explode(M`eigenvector_in_terms_of_integral_basis);
end intrinsic;
*/


intrinsic EigenvectorInTermsOfExpansionBasis(M::ModSym) -> SeqEnum, RngIntElt, RngIntElt
{A sequence v of elements of the field generated by the eigenvalues of a newform 
associated to M and an integer d such that the linear combination of qIntegralBasis(M,prec) 
defined by v is a d*(a newform).  Also, the lcm of the denominators of the numbers appearing
in the qExpansionBasis of M.   M must have nonzero sign and have been constructed 
using NewformDecomposition.}
   require Sign(M) ne 0 : "Argument 1 must have nonzero sign.";
   require HasAssociatedNewSpace(M) : 
          "Argument 1 must have been constructed using NewformDecomposition.";

   if not assigned M`eigenvector_in_terms_of_expansion_basis then
      d := Dimension(M);
      K := BaseField(M);
      prec := 1;
      for n in [1..2*d] do
         prec := NextPrime(prec);
      end for;
      
      tries := 1;
      while true do
         B := qExpansionBasis(M, prec+1);
         V, psi := CompactSystemOfEigenvalues(M,prec);
         // Let H be the matrix whose columns are the 
         // prime-indexed columns of the matrix of coefficients of B.
         assert #V eq #[q : q in [2..prec] | IsPrime(q)];
         H := RMatrixSpace(K,#B,#V)!(
                               &cat[[Coefficient(f,p) : p in [q : q in [2..prec] |IsPrime(q)]] : f in B]);
	 if Rank(H) lt d then
            print "EigenvectorInTermsOfExpansionBasis: Forced to increase precision. Tries =", tries;
            tries := tries + 1;
            if tries gt 20 then
               error "EigenvectorInTermsOfExpansionBasis: Could not find enough independent rows", tries;
            end if;
            for i in [1..10] do 
               prec := NextPrime(prec);
            end for;
            continue;
         end if;
         
         // Let G be the matrix whose columns are the element of V.
         G := Transpose(RMatrixSpace(K,#V,d)!V);

         // Find a matrix A such that A*H=G.  Then the vector we want
         // is v*A, where v = [psi(W.i) : i in [1..Dimension(W)], 
         // where W = Domain(psi).   If we can't find such a matrix A,
         // increase the precision and try again.  If we fail 10 times,
         // abort. 
         t, A := IsConsistent(H,G);
         if not t then
            error "EigenvectorInTermsOfExpansionBasis: BUG!! Inconsistent!!";
         else
            K := Codomain(psi);
            W := Domain(psi);
            v := VectorSpace(K,d)![psi(W.i) : i in [1..d]];
            A := MatrixAlgebra(Codomain(psi),d)!A;
            v := v*A;
            denom := DenominatorOf(v);
	    denom_qexp := DenominatorOf(B);
            M`eigenvector_in_terms_of_expansion_basis := <Eltseq(denom*v), denom, denom_qexp>;
            break;
         end if;
      end while;
   end if;
   return Explode(M`eigenvector_in_terms_of_expansion_basis);
end intrinsic;

intrinsic qEigenformReductions(M::ModSym, p::RngIntElt, prec::RngIntElt) -> List
{List of all reductions to characteristic p of a normalized eigenform corresponding 
to M.  The list of reductions is divided up into sequences corresponding to each
prime over p.}
   f := qEigenform(M,prec);
   return Reductions(f, p);
end intrinsic;

function DenominatorOf(v)
   case Type(v):
      when FldRatElt:
         return Denominator(v);
      when RngIntElt:
         return v;
      when SeqEnum:
         return LCM([Integers()|DenominatorOf(x) : x in v]);
      when FldNumElt, FldCycElt:
         return DenominatorOf(Eltseq(v));
      when RngUPolResElt, ModTupFldElt, RngUPolElt, RngSerPowElt:
         return DenominatorOf(Eltseq(v));
   end case;
   error Sprintf("Denominator Of -- Type = %o not yet handled.", Type(v));
end function;


function AbsoluteRep(K)
   f := Modulus(K);
   R := Parent(f);
   Rel := NumberField(f : Check:=false);
   L := AbsoluteField(Rel);
   psi := hom<R -> L | L!Rel.1>;
   return L, map<K -> L | x :-> psi(R!x)>;
end function;


intrinsic Reductions(f::RngSerPowElt, p::RngIntElt) -> List
{For internal use}			     
   prec := AbsolutePrecision(f);
   /* Assume f is defined over Q, a cyclotomic field, or a rink K[a]/h where K = Q or a cyclotomic field. */
   K := BaseRing(Parent(f));
   if Type(K) eq FldRat then
      R<q> := PowerSeriesRing(GF(p));
      return &+[Coefficient(f,n)*q^n : n in [0..prec-1]] + O(q^(prec));
   end if;

   denom := DenominatorOf(f);
   if Type(K) eq RngUPolRes then
      denom := LCM(denom, DenominatorOf(Modulus(K)));
   end if;
   if denom mod p ne 0 then
      return Reductions_Factor(f, p);
   end if;

   if Type(K) eq RngUPolRes then
      L, psi := AbsoluteRep(K);
   elif Type(K) in {FldCyc, FldNum} then
      L, psi := AbsoluteField(K);
   else
      require false: "Unsupported field.";
   end if;
   R<q> := PowerSeriesRing(L);
   f := &+[psi(Coefficient(f,n))*q^n : n in [0..prec-1]] + O(q^(prec));

   denom := LCM(DenominatorOf(f), DenominatorOf(DefiningPolynomial(L)));
   X := [* *];
   denom2 := denom/p^Valuation(denom,p);
   for phi in AllReductionMaps(L, p, denom) do 
      k := Codomain(phi);
      S<q> := PowerSeriesRing(k);
      Append(~X, &+[(phi(denom2*Coefficient(f,n))/denom2)*q^n : n in [0..prec-1]] +  O(q^prec));
      AssignNames(~k,["a"]);
   end for;
   return X;
end intrinsic;

intrinsic AllReductionMaps(K::FldNum, p::RngIntElt, d::RngIntElt : check_optimal := true) -> List
{All reduction maps from O_K to F_p, where the maps are only required
to be evaluateable on elements of K whose denominators are only divisible
by primes that divide d.  Here denominator is a notion that depends on
how K is presented.}
   require IsPrime(p) : "Argument 2 must be prime.";


   O := EquationOrder(K);
   Op := pMaximalOrder(O,p);
   ans := [* *];
   for P in Decomposition(Op,p) do
      F, pi := ResidueClassField(P[1]);
      r := map<K -> F | x :-> pi(Op!x)>;
      Append(~ans,r);
   end for;
   return ans;

end intrinsic;




///////////////////////////////////////////////////
// Easy (but long) factorization reduction code //
intrinsic Reductions_Factor(f::RngSerPowElt, p::RngIntElt) -> List
{For internal use}			     
   prec := AbsolutePrecision(f);
   // Assume f is defined over Q, a cyclotomic field, or a rink K[a]/h where K = Q or a cyclotomic field. 
   L := BaseRing(Parent(f));
   if Type(L) eq FldRat then
      R<q> := PowerSeriesRing(GF(p));
      return &+[Coefficient(f,n)*q^n : n in [0..prec-1]] + O(q^(prec));
   end if;
   X := [* *];
   for phi in AllReductionMaps_Factor(BaseRing(Parent(f)), p) do 
         k := Codomain(phi);
         S<q> := PowerSeriesRing(k);
         Append(~X, &+[phi(Coefficient(f,n))*q^n : n in [0..prec-1]] +  O(q^prec));
         AssignNames(~k,["a"]);
   end for;
   return X;
end intrinsic;

function NumberFieldToPolyQuo_Factor(K)
   f := DefiningPolynomial(K);
   assert Type(BaseRing(f)) eq FldRat;   // otherwise bad things!
   R := Parent(f);
   Q := quo<R|f>;
   return Q, hom<K -> Q | Q.1>;
end function;

intrinsic AllReductionMaps_Factor(K::FldRat, p::RngIntElt) -> List
{All reduction maps from O_K to F_p, where the maps are only required
to be evaluate-able on elements of K whose denominators are only divisible
by primes that divide d.  Here denominator is a notion that depends on
how K is presented.}
   require IsPrime(p) : "Argument 2 must be prime.";
   k := GF(p);
   return [* map<RationalField() -> k | x :-> k!x > *];
end intrinsic;


intrinsic AllReductionMaps_Factor(K::FldCyc, p::RngIntElt) -> List
{"} // "
   // d is irrelevant...
   f := DefiningPolynomial(K);
   R := PolynomialRing(GF(p));
   ans := [* *];
   for F in Factorization(R!f) do
      g := F[1];
      k := GF(p^Degree(g));
      for r in Roots(PolynomialRing(k)!g) do
         Append(~ans, hom<K -> k | r[1]>);
      end for;
   end for;
   return ans;
end intrinsic;

intrinsic AllReductionMaps_Factor(K::FldNum, p::RngIntElt) -> List
{"} // "
   R := PolynomialRing(RationalField());
   f := DefiningPolynomial(K);
   S := quo<R|f>;
   S, phi := NumberFieldToPolyQuo_Factor(K);
   ans := [* *];
   for R in AllReductionMaps_Factor(S, p) do 
      for r in R do
         Append(~ans, map<K -> Codomain(r) | x :-> r(phi(x))>);
      end for; 
   end for;
   return ans;
end intrinsic;


intrinsic AllReductionMaps_Factor(K::RngUPolRes, p::RngIntElt) -> List
{"} // "
   require IsPrime(p) : "Argument 2 must be prime.";
   h := Modulus(K);
   assert Coefficient(h,Degree(h)) eq 1;  // but we should be able to deal with that case...
   C := BaseRing(K);      
   require Type(C) in {FldRat, FldCyc} : "Argument 1 must be over the rationals or a cyclotomic field.";

   ans := [* *];
   S<x> := Parent(h);
   for pi in AllReductionMaps_Factor(C, p) do
         function poly_pi(g)
            x := PolynomialRing(Codomain(pi)).1;
            return &+[Parent(x)|pi(Coefficient(g,n))*x^n : n in [0..Degree(g)]];
         end function;
         pi_of_f := poly_pi(h);
         k := Parent(Coefficient(pi_of_f,0));
         for F in Factorization(pi_of_f) do 
            m := GF(p^(Degree(k)*Degree(F[1])));
            for r in Roots(PolynomialRing(m)!F[1]) do 
               psi := hom<PolynomialRing(k) -> m | r[1]>;
               Append(~ans, map<K -> m | z :-> psi(poly_pi(S!z))>);
            end for;
         end for;
      end for;
   return ans;

end intrinsic;
