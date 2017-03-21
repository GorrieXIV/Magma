freeze;
 
/****-*-magma-*-************************************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: q-expansions.m

   05/2007:  (Steve) Slightly adjusted syntax in ExactPrecisionBound so it will work
             correctly over inexact base rings.

   04/2007:  (Steve) Added new rigmarole for constructing spaces from auxiliary spaces.
   
   03/2007:  (Steve) Bug fix in qExpansion_EisensteinSeries, replacing a psi by psibar.
             See the comment there, and the change log in eisenstein.m for the whole story.

   08/15/03: (WAS) Added intrinsic CyclotomicEmbedding as requested by Kevin Buzzard.
   
   08/15/03: (WAS) Fixed significant bug found by Kevin Buzzard in 
             MoveIntoPowerSeriesRingOverANumberField
             that would have caused incorrect q-expansions
             for modular forms in some cases.
 
   04/05/03: (WAS) fixed bug in qExpansionOfModularFormsBasis:
             When level 1 one and base ring wasn't Z it would
             not coerce the basis correctly.

   ------------- old RCS comments ------------

   Revision 1.13  2002/09/11 17:36:40  was
   Nothing.

   Revision 1.12  2002/05/30 09:42:09  was
   Made default for PrecisionBound Exact := false, since this speeds up lots of other code.

   Revision 1.11  2002/05/22 21:34:56  was
   Added Bound parameter to CoefficientRing.

   Revision 1.10  2001/12/07 01:12:47  was
   fixed little bug in Coefficient.

   Revision 1.9  2001/12/05 22:11:51  was
   Added CoefficientRing and CoefficientField.

   Revision 1.8  2001/11/22 17:54:18  was
   Added a Coefficient intrinsic.

   Revision 1.7  2001/11/10 18:48:19  was
   Changed from SeqEnum to List in an assertion to ApplyMapsTo_qExpansion.

   Revision 1.6  2001/11/10 18:34:11  was
   Fixed serious bug in Reductions.

   Revision 1.5  2001/10/25 02:53:17  was
   ??

   Revision 1.4  2001/07/26 19:23:10  was
   Added some more verbosity.

   Revision 1.3  2001/05/30 18:56:42  was
   Created.

   Revision 1.2  2001/05/16 04:11:23  was
   *** empty log message ***

   Revision 1.1  2001/05/16 03:52:09  was
   Initial revision

      
 ***************************************************************************/

import "level1.m":      Level1Basis;

import "half-integral.m": q_expansion_basis_weight_half,
                          q_expansion_basis_half_integral,
                          q_expansion_basis_via_space_div_elt; // should really be moved in here

import "weight1.m":     compute_weight1_cusp_space,
                        qExpansion_wt1_dihedral_form;

import "misc.m" :       EchelonPowerSeriesSequence;
import "misc.m" :       SaturatePowerSeriesSequence;
import "misc.m" :       CoercePowerSeries;
import "misc.m" :       ToLowerCaseLetter;

import "modular_symbols.m" : MF_ModularSymbols;

import "newforms.m"   : ComputeEisensteinNewforms;

import "predicates.m":  CoercionMap;
import "predicates.m":  AssociatedSpaceOverZ;
import "predicates.m":  SpaceType;

import "qexp_mappings.m" : ModpReductionMaps;
import "qexp_mappings.m" : pAdicEmbeddingMaps;
import "qexp_mappings.m" : ComplexEmbeddingMaps;

forward BasisOfHalfIntegralWeightForms,
        ClearDenominators,
        ClearDenominatorsAndSaturate,
        CoercePowerSeriesElement,
        Compute_ith_Conjugate,
        Compute_qExpansionsOfForm,
        PowerSeriesInternal,
        qExpansionOfModularFormsBasis,
        RestrictionOfScalarsToQ; 


// helper for ApproximatePrecisionBound -- assumes M is cuspidal,
// and idx is the index of the group fixing M inside PSL2(Z).
function cusp_term(M, idx)  // ModFrm, RngIntElt -> FldRatElt
   N := Level(M); 
   if N eq 1 then 
      cuspterm := 0;
   elif IsGamma0(M) then
      cuspterm := &+[ EulerPhi(GCD(d, N div d)) : d in Divisors(N) ] - 1;
   elif IsGamma1(M) then
      assert idx gt 1 and N ne 2; // since that falls in the previous case
      cuspterm := &+[ EulerPhi(d) * EulerPhi(N div d) : d in Divisors(N) ]/2 - 1;
   else
      chars := [chi : chi in DirichletCharacters(M) | not IsTrivial(chi)];
      if #chars gt 1 then
         // just use group generators
         A, fromA := AbelianGroup(Universe(chars));
         G := sub< A | [chi @@ fromA : chi in chars] >;
         chars := [g @ fromA : g in Generators(G)];
      end if;
      char_orders := [Order(chi) : chi in chars];
      orders_of_char_vals := [];  // store orders of the value list for each char
      for chi in chars do
         m := Order(chi);
         vals := ValueList(chi);  // from 1 to Modulus(chi)
         Append( ~orders_of_char_vals, [OrderOfRootOfUnity(v,m) : v in vals]);
      end for;
      scalars := {};
      for s := 1 to N-1 do 
         if GCD(s,N) eq 1 and 
            (#chars eq 0 or &and[ords[s] eq 1 : ords in orders_of_char_vals]) then 
            scalars join:= {s, (-s) mod N}; end if; 
      end for;
      // Not very efficient -- iterate over all coset reps of Gamma1(N) in PSL2(Z).
      // These are given by all possible bottom rows (c,d), modulo sign.
      cuspterm := 0;
      checked_cds := [[] : c in [0 .. N div 2]];
      for c := 0 to N div 2 do 
         d_max := (N gt 2 and c in {0,N/2}) select Floor(N/2) else  N-1;
         for d := 0 to d_max do
           if d in checked_cds[c+1] then continue; end if;
           for s in scalars do 
              sc := (s*c) mod N;
              if 2*sc le N then 
                 Append( ~checked_cds[sc+1], (s*d) mod N ); 
              end if;
           end for;
           if GCD([N,c,d]) ne 1 then continue; end if;
           w1 := N div GCD(c^2,N);  
           if #chars eq 0 then 
             xx := 1;
           elif #chars eq 1 then 
             xx := ords[1 + (c*d*w1) mod #ords] where ords := orders_of_char_vals[1];
           else
             xx := LCM([ ords[1 + (c*d*w1) mod #ords] : ords in orders_of_char_vals ]);
           end if;
           width := w1*xx;
           cuspterm +:= 1/width;
         end for;
      end for;
      cuspterm -:= 1;  // remove trivial term
      assert cuspterm gt (idx-1)/N or IsPrime(N); // sanity check -- should be stronger than the old bound
 //else   -- old version, valid in all cases (takes width = N for all cusps)
 //   cuspterm := (idx-1)/N;  
   end if;
   return cuspterm;
end function;

function ApproximatePrecisionBound(M)
   /* 
   IMPORTANT NOTE ( --Steve):
   The ApproximatePrecisionBound should also satisfy the following property:
   if f in M is such that the coefficients in the q-expansion of f up to 
   ApproximatePrecisionBound(M) are integers, then all the coefficients are integers.
   (If this property fails, then Basis(M) is no longer uniquely fixed, 
   and could change when M`default_precision is changed.
   See also the comment where ApproximatePrecisionBound is called in 
   qExpansionOfModularFormsBasis.)
   */
   if assigned M`approx_precision_bound then 
      return M`approx_precision_bound; 
   elif assigned M`associated_space_over_z then
      return ApproximatePrecisionBound(M`associated_space_over_z);
   elif assigned M`ambient_space then
 assert not IsIdentical(M, M`ambient_space);
      if IsCuspidal(M) then
         if not IsIdentical(M, CuspidalSubspace(M`ambient_space)) then 
            return ApproximatePrecisionBound(CuspidalSubspace(M`ambient_space));
         end if;
      else
         return ApproximatePrecisionBound(M`ambient_space);
      end if;
   end if;

   k := Weight(M);
   N := Level(M);

   if (k ne 1 or assigned M`dimension) and Dimension(M) eq 0 then 
      return 0; end if;

   ans := -1;  // means it's not computed yet
 
   if k eq 1/2 or k eq 1 then
      // use precision bound of the relevant weight 2 space
      if IsGamma0(M) or #DirichletCharacters(M) eq 1 and Order(DirichletCharacters(M)[1]) le 2 then
         // powers of forms are in Gamma0(N) space
         MM := ModularForms(N);
      elif IsGamma1(M) or k eq 1/2 then  // precision comes cheap for weight 1/2
         MM := ModularForms(Gamma1(N));
      elif k eq 1 then
         // find Galois reps for all products of characters for M
         // TO DO: faster? (takes non-negligible time)
         chars := &cat[ [chi^i : i in [1..m] | GCD(i,m) eq 1] where m is Order(chi) 
                       : chi in DirichletCharacters(M)];
         chars2 := [chi*chi1 : chi in chars, chi1 in DirichletCharacters(M)];
         MM := ModularForms(chars2);
      end if;
      if IsCuspidal(M) then MM := CuspidalSubspace(MM); end if;
      ans := Ceiling(k/2 * ApproximatePrecisionBound(MM));
   elif not IsIntegral(k) then
      // Multiplying by theta = Sum( q^{n^2} ) maps the space injectively into a
      // space of weight k + 1/2, so we can use the precision bound for that space.
      // Note: maybe we should check whether M has auxiliary spaces of this kind, 
      // for which precision bounds are already known ... however, in that case,
      // a q-expansion basis for M is presumably also known, making the check redundant.
      kk := Integers()! (k+1/2);
      if IsGamma1(M) then 
         MM := ModularForms(Gamma1(N), kk);
      elif IsEven(kk) then 
         MM := ModularForms(DirichletCharacters(M), kk);
      else
         chi4 := KroneckerCharacter(-1);
         chis := [ chi4 * chi : chi in DirichletCharacters(M) ];
         MM := ModularForms(chis, kk);
      end if;
      if IsCuspidal(M) then MM := CuspidalSubspace(MM); end if;
      ans := ApproximatePrecisionBound(MM);
   else
     // NEW VERSION (by Steve)
     // Using sharper bounds based on results from William's book.
     // Also, using Buzzard's observation (when there is only one character).
     // Note that his observation applies also to Sturm's mod m result.
     idxGamma0N := &*[Integers()| t[1]^t[2] + t[1]^(t[2]-1) : t in Factorization(N)];
     chars := DirichletCharacters(M);
     if IsGamma0(M) then
        idx := idxGamma0N;
     elif #chars eq 1 and Order(chars[1]) in {2,1} then
        // the same bound holds for quadratic characters as for Gamma0
        // (multiply and divide by 2 here to take care of odd k)
        ans2 := IsCuspidal(M) select PrecisionBound(CuspForms(N,2*k))
                               else  PrecisionBound(ModularForms(N,2*k));
        ans := Ceiling(ans2/2);
     elif IsGamma1(M) then 
        assert N gt 2; // since that falls in the previous case
        idx := idxGamma0N * EulerPhi(N) div 2;  // index in PSL2(Z)
     else
        A, AtoChi := AbelianGroup(Universe(chars));
        chars_gp := sub< A | [chi @@ AtoChi : chi in chars] >;
        // get the subgroup of chi for which chi(-1)=1
        C2 := AbelianGroup([2]);
        h := hom< chars_gp -> C2 | [ (Evaluate( chi@AtoChi, -1) eq 1) select C2!0 else C2.1 
                                    : chi in Generators(chars_gp)] >;
        idx := idxGamma0N * #Kernel(h); 
     end if;
     if ans eq -1 then
        ans := IsCuspidal(M) select Floor( idx*k/12 - cusp_term(M,idx) ) + 1
                              else  Floor(idx*k/12) + 1;
     end if;
   end if;
   vprintf ModularForms: "Obtained precision bound %o for %o\n", ans, M;
   if k ne 1 then 
     error if ans lt Dimension(M), "Precision bound obtained is too good to be true";
   end if;
   M`approx_precision_bound := ans;
   return ans;
   /* ORIGINAL VERSION (by WAS)
   es := Dimension(EisensteinSubspace(M));
   if IsGamma0(M) or then
      return Ceiling(idxGamma0N*(k/12))+1 + es;
   else
      return Ceiling(idxGamma0N*EulerPhi(N)*(k/12))+1 + es;
   end if;
   */
end function;

function ExactPrecisionBound(M)
   assert Type(M) eq ModFrm;
   b := Dimension(M);
   if b eq 0 then return 1; end if;
   q := PowerSeriesRing(BaseRing(M)).1;
   f := M.Dimension(M);
 //while PowerSeries(f,b) eq O(q^b) do // (WAS)
 //while Valuation(PowerSeries(f,b)) ge b do // Steve's preferred version, but currently not working over p-adics
   while forall{cc: cc in Coefficients(PowerSeriesInternal(f,b)) | IsWeaklyZero(cc)} do 
      b +:= 1;
   end while;
   assert b ge Dimension(M);
   // check the ApproximatePrecisionBound, which should have been calculated already.
   if assigned M`approx_precision_bound then assert b le ApproximatePrecisionBound(M); end if;
   return b;
end function;

intrinsic PrecisionBound(M::ModFrm : Exact := false) -> RngIntElt
{Some integer b such that f + O(q^b) determines
 any modular form f in M.  If the optional paramater Exact 
 is set to true then the smallest such integer is returned.}
   if IsRingOfAllModularForms(M) then
      return Infinity();
   end if;
   if not assigned M`precision_bound then
      if Exact then
         M`precision_bound := ExactPrecisionBound(M);
      elif assigned M`associated_space_over_z then
         return PrecisionBound(M`associated_space_over_z);
      elif assigned M`q_expansion_basis and BaseRing(M) cmpeq Integers() then
         qexps := M`q_expansion_basis[2];
         require #qexps eq Dimension(M) and not IsWeaklyZero(qexps[#qexps]) : 
            "Precision was too small in q-expansion basis computation";
         M`precision_bound := Valuation(qexps[#qexps]) + 1;
      else
         return ApproximatePrecisionBound(M);        
      end if;
   end if;
   return M`precision_bound;
end intrinsic;

/*
function ExactNewformPrecisionBound(M)
   error "Not written";
end function;

function ApproximateNewformPrecisionBound(M)
   return PrecisionBound(M : Exact := false);  // very bad!!
end function;

intrinsic NewformPrecisionBound(M::ModFrm : Exact := true) -> RngIntElt
{The smallest integer b such that f + O(q^b) determines
 any newform f in M.  If the optional paramater Exact 
is set to false than some integer b such that f+O(q^b) determines
any modular form f in M is returned, but b need not be minimal.}
   if IsRingOfAllModularForms(M) then
      return Infinity();
   end if;
   if not assigned M`newform_precision_bound then
      if Exact then
         M`newform_precision_bound := ExactNewformPrecisionBound(M);
      else
         return ApproximateNewformPrecisionBound(M);
      end if;
   end if;
   return M`newform_precision_bound;
end intrinsic;
*/

function idxG0(n)
   return 
      &*[Integers()| t[1]^t[2] + t[1]^(t[2]-1) : t in Factorization(n)];
end function;

function idxG1(n)
   return EulerPhi(n)*idxG0(n);
end function;

intrinsic CoefficientRing(f::ModFrmElt : Bound := -1) -> Rng
{A ring that contains the coefficients of f.  If IsNewform(f) is true, then
this is the ring generated by the Fourier coefficients.  The optional
paramater Bound can be used to obtain the ring generated by the coefficients
a_n with n <= Bound.}
   if IsNewform(f) then
      if Degree(f) eq 1 then
	 return IntegerRing();
      end if;
      if Bound eq -1 then      
         if IsGamma0(Parent(f)) then
            bnd := Ceiling(Weight(f) * idxG0(Level(f)) / 12);
         else
            bnd := Ceiling(Weight(f) * idxG1(Level(f)) / 12);
         end if;
      else 
         bnd := Max(Bound,1);
      end if;
      qexp := PowerSeriesInternal(f,bnd+1);
      return Order([Coefficient(qexp,n) : n in [2..bnd]]);
   else
      return Parent(Coefficient(f,1));
   end if;   
end intrinsic;

intrinsic CoefficientField(f::ModFrmElt) -> Fld
{The field in the which the Fourier coefficients lie.}
   return FieldOfFractions(Parent(Coefficient(f,1)));
end intrinsic;

intrinsic Coefficient(f::ModFrmElt, n::RngIntElt) -> RngElt
{The nth Fourier coefficient of f.}
   requirege n, 0;
   return Coefficient(PowerSeriesInternal(f,n+1),n);
end intrinsic;

intrinsic '!'(R::RngSer, f::ModFrmElt) -> RngSerElt
{The q-expansion of the modular form f, as a power series in the given ring R.}
   return R! PowerSeriesInternal(f, Precision(Parent(f)));
end intrinsic;

intrinsic Basis(M::ModFrm, prec::RngIntElt) -> SeqEnum[RngSerPowElt]
{Same as qExpansionBasis}
   return qExpansionBasis(M, prec);
end intrinsic;

intrinsic qExpansionBasis(M::ModFrm, prec::RngIntElt) -> SeqEnum[RngSerPowElt]
{A sequence of power series containing q-expansions of the standard basis of M, to absolute precision 'prec'.}
   bas := [PowerSeriesInternal(f,prec) : f in Basis(M)];
   if #bas gt 0 then 
      if assigned M`q_name then
         name := M`q_name;
      else
         name := "q";
      end if;
      R := Universe(bas);
      AssignNames(~R, [name]);
   end if;
   return bas;
end intrinsic;

intrinsic qExpansion(f::ModFrmElt, prec::RngIntElt) -> RngSerPowElt
{The q-expansion of the modular form f to absolute precision prec.}
   return PowerSeries(f,prec);
end intrinsic;

intrinsic qExpansion(f::ModFrmElt) -> RngSerPowElt
{"} // "
   return PowerSeries(f);
end intrinsic;

intrinsic PowerSeries(f::ModFrmElt) -> RngSerPowElt
{"} // "
   return PowerSeries(f,Precision(Parent(f)));
end intrinsic;

intrinsic PowerSeries(f::ModFrmElt, prec::RngIntElt) -> RngSerPowElt
{"} // "
   fq := PowerSeriesInternal(f, prec);
   R := Parent(fq);
   M := Parent(f);
   if assigned M`q_name then
      name := M`q_name;
   else
      name := "q";
   end if;
   AssignNames(~R,[name]);
   return fq;
end intrinsic;

function PowerSeriesInternal(f, prec)
   if not assigned f`q_expansion or 
                AbsolutePrecision(f`q_expansion) lt prec then
      f`q_expansion := Compute_qExpansionsOfForm(f,"normal", 0, prec)[1][1];
   end if;
   fq := f`q_expansion;
   return fq + O(Parent(fq).1^prec);
end function;

function Turn_qExpansionsIntoModularForms(f, expansions)
   ans := [* *];
   for orb in expansions do
      mf_orb := [* *];
      for g in orb do
         M := BaseExtend(Parent(f),BaseRing(Parent(g)));
         h := M!g;
         if assigned f`nebentype then
             h`nebentype := f`nebentype;
         end if;
         Append(~mf_orb, h);
         mf_orb[#mf_orb]`degree := #orb;
      end for;
      Append(~ans, mf_orb);
   end for;
   return ans;
end function;

intrinsic Reductions(f::ModFrmElt, p::RngIntElt) -> List
{The mod p reductions of the modular form f.  Because of denominators,
the list of reductions can be empty.} 
   require IsPrime(p) and p gt 0 : "Argument 2 must be prime.";
   require Type(BaseRing(Parent(f))) in 
     {FldRat, RngInt, FldCyc, FldNum} : 
    "The base ring of the parent of argument 1 must be a number field or Z.";

   if not assigned f`modp_reductions then
      f`modp_reductions := [];   // sequence of pairs <p,fbar>
   end if;
   if exists(i) { i : i in [1..#f`modp_reductions]
                             | f`modp_reductions[i][1] eq p } then
      return f`modp_reductions[i][2];
   end if;
   prec := PrecisionBound(AmbientSpace(Parent(f)));
   if IsEisensteinSeries(f) then
      c0 := Coefficient(PowerSeriesInternal(f,1),0);
      if Type(Parent(c0)) eq FldRat then
         denom := Denominator(c0);
      else
         denom := LCM([Denominator(b) : b in Eltseq(c0)]);
      end if;
      if denom mod p eq 0 then
         return [* *];
      end if;
   end if;
   expansions := Compute_qExpansionsOfForm(f,"modp", p, prec);
   modp_forms := Turn_qExpansionsIntoModularForms(f, expansions);
   Append(~f`modp_reductions, <p, modp_forms>);

   return (f`modp_reductions[#f`modp_reductions])[2];   
end intrinsic;

intrinsic pAdicEmbeddings(f::ModFrmElt, p::RngIntElt) -> List
{The p-adic embeddings of f.}
   require IsPrime(p) and p gt 0 : "Argument 2 must be prime.";
   require Type(BaseRing(Parent(f))) in 
     {FldRat, RngInt, FldCyc, FldNum} : 
    "The base ring of the parent of argument 1 must be a number field or Z.";
/*
   if not assigned f`padic_embeddings then
      f`padic_embeddings := [];   // sequence of pairs <p,fbar>
   end if;
   if exists(i) { i : i in [1..#f`padic_embeddings]
                             | f`padic_embeddings[i][1] eq p } then
      return f`padic_embeddings[i][2];
   end if;
*/

   prec := PrecisionBound(Parent(f));
   expansions := Compute_qExpansionsOfForm(f,"padic", p, prec);
   padic_forms := Turn_qExpansionsIntoModularForms(f, expansions);
   return padic_forms;

/*
   Append(~f`padic_embeddings, <p, padic_forms>);

   return (f`padic_embeddings[#f`padic_embeddings])[2];   
*/
end intrinsic;

intrinsic ComplexEmbeddings(f::ModFrmElt) -> List
{The complex embeddings of f.}
   prec := PrecisionBound(Parent(f));
   expansions := Compute_qExpansionsOfForm(f,"complex", 0, prec);
   complex_forms := Turn_qExpansionsIntoModularForms(f, expansions);
   return complex_forms;
end intrinsic;

/*
   GeneralizedBernoulli: 
   k   : RngIntElt,   nonnegative integer weight
   eps : GrpDrchElt,  a Dirichlet character (not necessarily primitive) 

   Compute the generalized Bernoulli numbers B_{k,eps}, as defined 
   on page 44 of Diamond-Im: 

        sum_{a=1}^{N} eps(a) t*e^(at)/(e^(N*t)-1) 

                 = sum_{k=0}^{\infty} B_{k,eps}/{k!}*t^k. 

   where N is the modulus of eps. 
*/

// Note: BernoulliNumber is automatically identical to Bernoulli (see bind/b.b)

intrinsic Bernoulli(k::RngIntElt, eps::GrpDrchElt) -> RngElt
{The kth generalized Bernoulli number B_[k,eps] associated to the Dirichlet character eps.
By definition, B_[k,eps]/k! equals the coefficient of t\^k in the sum over 1<=a<=N of 
eps(a)*t*e^(at)/(e^(N*t)-1), where N is Modulus(eps)} 
   assert Type(k) eq RngIntElt and k ge 0;
   assert Type(eps) eq GrpDrchElt;
   assert Evaluate(eps,-1) eq (-1)^k;
  
   N    := Modulus(eps);
   K    := BaseRing(eps);
   R<t> := PowerSeriesRing(K);
   prec := ( char eq 0 or GCD(N,char) eq 1 where char is Characteristic(K) )
            select k+2 else k+5; 
   repeat 
     denom := Exp(N*t+O(t^prec)) - 1;
     num := &+[ Evaluate(eps,a)*t*Exp(a*t+O(t^prec)) : a in [1..N] ];
     F := num div denom;  
     prec +:= 5;
   until AbsolutePrecision(F) ge k; // might not be, in unlucky cases in finite characteristic
     
   Bk   := Coefficient(F,k)*Factorial(k);
   return Bk;
end intrinsic;


function qExpansion_EisensteinSeries(f,prec)
   assert Type(f) eq ModFrmElt;
   assert Type(prec) eq RngIntElt;
   assert assigned f`eisenstein;

   /* 
   chi is a primitive character of conductor L
   psi is a primitive character of conductor M
   MLt divides N

   E_k(chi,psi,t) is 
        c_0 + sum_{m \geq 1}[sum_{n|m}psibar(n)n^{k-1}chi(m/n)] q^{mt}
   c_0 = 0 if L>1 
    and 
   c_0 = L(1-k,psibar)/2 if L=1 (where L(1-k,psibar) denotes the L-function value)
   
   Steve changed psi to psibar in both occurrences in this formula 
   (copying from Miyake, and verifying c_0 via an extra calculation)

   Special case in weight 2: 
   E_2(1,1,t) is E_2(z) - t*E_2(t*z) where E_2 denotes the usual non-convergent sum
   */
 
   chi, psi, t := Explode(EisensteinData(f));
   psibar := psi^-1;
   L := Conductor(chi);
   M := Conductor(psi);
   mstop := (prec div t) + 1;
   // Store values of the characters (shouldn't take long...)
   if Modulus(chi) lt mstop and not assigned chi`ValueList then 
      _ := ValueList(chi); end if;
   if Modulus(psi) lt mstop and not assigned psi`ValueList then 
      _ := ValueList(psi); end if;

   m := LCM(CyclotomicOrder(BaseRing(chi)), CyclotomicOrder(BaseRing(psi)));
   R := PowerSeriesRing(m le 2 select RationalField() else CyclotomicField(m));
   q := R.1;
   k := Weight(f);

   if k eq 2 and IsTrivial(chi) and IsTrivial(psi) then
      assert t gt 1;
      E2 := PrimitiveEisensteinSeries(2,prec);
      q := Parent(E2).1;
      qexp := E2 - t*Evaluate(E2,q^t); 
   else
       // Changed psi to psibar here   --Steve
       if L eq 1 then
          c_0 := -Bernoulli(k,psibar)/(2*k);
       else
          c_0 := 0;   
       end if;
       qexp := c_0;
       for m := 1 to mstop do 
          c_m := &+[ Evaluate(psibar,n) * n^(k-1) * Evaluate(chi,m div n) 
                                                         : n in Divisors(m)];
          qexp +:= c_m * q^(m*t);
       end for;
   end if;

   return qexp + O(q^prec);
end function;

function qExpansion_CreatedFrom(f,prec)
   assert Type(f) eq ModFrmElt;
   assert Type(prec) eq RngIntElt;
   assert assigned f`created_from;

   op, g, h := Explode(f`created_from);
   case op:
      when "*":
         return PowerSeriesInternal(g,prec)*PowerSeriesInternal(h,prec);
      when "+":
         return PowerSeriesInternal(g,prec)+PowerSeriesInternal(h,prec);
      when "-":
         return PowerSeriesInternal(g,prec)-PowerSeriesInternal(h,prec);
      when "scalar":
         return g*PowerSeriesInternal(h,prec);
      else:
         error "Invalid created_from attribute.";
   end case;
end function;

function qExpansion_Theta(f,prec)
   assert Type(f) eq ModFrmElt;
   assert Type(prec) eq RngIntElt;
   assert assigned f`theta_data;

   Lats := [tup[1] : tup in f`theta_data];
   coeffs := [tup[2] : tup in f`theta_data];
   return &+[ PowerSeriesRing(BaseRing(Parent(f))) | 
               coeffs[i] * ThetaSeries(Lats[i], prec) : i in [1..#Lats]];
end function;

function qExpansion_Gadget(f,prec)
   assert Type(f) eq ModFrmElt;
   assert Type(prec) eq RngIntElt;
   assert assigned f`gadget;

   return f`gadget(prec);
end function;

function qExpansion_EllipticCurve(f,prec)
   assert Type(f) eq ModFrmElt;
   assert Type(prec) eq RngIntElt;
   assert assigned f`elliptic_curve;

   return qEigenform(f`elliptic_curve, prec);
end function;


function Compute_ith_Conjugate(F, g, i)
   assert Type(F) in {FldPad, FldRat, FldFin};
   assert Type(g) eq RngSerPowElt;
   assert Type(i) in RngIntElt;
   assert i ge 1;

   error "Compute_ith_Conjugate -- not yet written.";
end function;

function CreateNumberFieldFromCyclotomicField(K)
   assert Type(K) eq FldCyc;
   f := DefiningPolynomial(K);
   F := NumberField(f);
   phi := hom<K -> F | F.1>;
   return F, phi;
end function;

function MoveIntoPowerSeriesRingOverANumberField(f, qexp)
   assert Type(f) eq ModFrmElt;
   assert Type(qexp) eq RngSerPowElt;
   R := BaseRing(Parent(qexp));
   if Type(R) eq FldRat or 
      Type(R) eq FldNum and IsAbsoluteField(R) then  // it already is where we want it
      if not assigned f`number_field_coercion_map then
         f`number_field_coercion_map := hom<R -> R | x :-> x>;
         f`cyclotomic_embedding_map := f`number_field_coercion_map;
      end if;        
      return qexp;
   end if;

   if not assigned f`number_field_coercion_map then  
      if Type(R) eq RngUPolRes then
         h := Modulus(R);
         K := NumberField(h : Check:=false);
         L := AbsoluteField(K);   
         poly_ring := Parent(h);
         f`number_field_coercion_map := hom<poly_ring -> L | L!K.1>;
         f`cyclotomic_embedding_map := hom<BaseRing(h) -> L | x :-> L!(K!x)>;
      elif Type(R) eq FldCyc then
         _,f`number_field_coercion_map := CreateNumberFieldFromCyclotomicField(R);
         f`cyclotomic_embedding_map := f`number_field_coercion_map;
      elif Type(R) eq FldNum then
         L := AbsoluteField(R);
         f`number_field_coercion_map := hom< R -> L | x :-> L!x >; 
         f`cyclotomic_embedding_map := f`number_field_coercion_map;
      else
         error "Bug in q-expansions.m";
      end if;
   end if;
   prec := AbsolutePrecision(qexp);
   S    := PowerSeriesRing(Codomain(f`number_field_coercion_map));
   phi  := f`number_field_coercion_map;
   return &+[phi(Coefficient(qexp,n))*S.1^n : n in [0..prec-1]] + O(S.1^prec);
end function;

intrinsic CyclotomicEmbedding(f::ModFrmElt) -> Map
{The canonical map from the field Q(eps) generated by the
values of eps into the field K_f generated by the Fourier
coefficients of f.  We assume that f is a newform 
with Dirichlet character eps.}
   if not assigned f`cyclotomic_embedding_map then
      dummy := PowerSeries(f,2);
   end if;
   return f`cyclotomic_embedding_map;
end intrinsic;

function qExpansion_ModularSymbols(f,prec)
   assert Type(f) eq ModFrmElt;
   assert Type(prec) eq RngIntElt;
   assert assigned f`mf_modular_symbols;

   vprintf ModularForms, 2: 
     "Computing q-expansion using %o\n", f`mf_modular_symbols;
   eig := qEigenform(f`mf_modular_symbols,prec); 
   g := MoveIntoPowerSeriesRingOverANumberField(f, eig);

/*
   F := BaseRing(Parent(g));
   if ISA(Type(F), FldAlg) and assigned f`which_conjugate then
     A := Automorphisms(F);  // F is galois
     a := A[f`which_conjugate];
     g := Parent(g) ! [F| Coefficient(g,n) @ a : n in [0..prec-1]];
   end if;
*/

R := BaseRing(Parent(g));
if assigned f`which_conjugate and Type(R) ne FldRat then
AssignNames(~R,[ToLowerCaseLetter(f`which_conjugate)]);
end if;

// MW revert
  
   return g + O(Parent(g).1^prec);
end function;


function qExpansion_Element(f, prec)
   assert Type(f) eq ModFrmElt;
   assert assigned f`element;
   assert Type(prec) eq RngIntElt;
   assert assigned f`element;

   e := Eltseq(f`element);
   M := Parent(f);
   
   B := qExpansionOfModularFormsBasis(M,prec); 
   v := PowerSeriesRing(BaseRing(M))!0;
   for i in [j : j in [1..#e] | e[j] ne 0] do
      v +:= e[i]*B[i];
   end for;
   return v + O(Parent(v).1^prec);
end function;


function ApplyMapTo_qExpansion(f, psi)
   assert Type(f) eq RngSerPowElt;
   assert Type(psi) eq Map;
   R := Parent(f);
   S<q> := PowerSeriesRing(Codomain(psi));
   prec := AbsolutePrecision(f);
   K := Parent(Coefficient(f,0));
   R := Domain(psi);
   assert R eq K;
   return &+[psi(Coefficient(f,n))*S.1^n : n in [0..prec-1]] + O(S.1^prec);
end function;

function ApplyMapsTo_qExpansion(f, phi)
   assert Type(f) eq RngSerPowElt;
   assert Type(phi) eq List;
   assert #phi gt 0;
   ans := [* *];
   for i in [1..#phi] do 
      orbit_of_maps := phi[i];
      orbit := [* *];  
      for psi in orbit_of_maps do
         Append(~orbit, ApplyMapTo_qExpansion(f,psi));
      end for;
      Append(~ans, orbit);
   end for;
   return ans;
end function;


// The q-expansion of the modular form f to absolute precision prec. 
function Compute_qExpansionsOfForm(f, type, data, prec) 
   assert Type(f) eq ModFrmElt;
   assert Type(prec) eq RngIntElt;
   assert Type(data) eq Map or Type(data) eq RngIntElt;
   vprintf ModularForms, 3 : "Computing q-expansion to precision %o for element of type ", prec;

   case type:
      when "normal":
         if assigned f`created_from then
            vprint ModularForms, 3: "created from";
            g := qExpansion_CreatedFrom(f,prec);
         elif assigned f`eisenstein then
            vprint ModularForms, 3: "eisenstein";
            g := qExpansion_EisensteinSeries(f,prec);
         elif assigned f`wt1_dihedral_data then
            vprint ModularForms, 3: "dihedral";
            g := qExpansion_wt1_dihedral_form(f,prec);
         elif assigned f`theta_data then
            vprint ModularForms, 3: "theta";
            g := qExpansion_Theta(f,prec);
         elif assigned f`q_expansion_gadget then
            vprint ModularForms, 3: "gadget";
            g := qExpansion_Gadget(f,prec);
         elif assigned f`elliptic_curve then
            vprint ModularForms, 3: "elliptic curve";
            g := qExpansion_EllipticCurve(f,prec);
         elif assigned f`mf_modular_symbols then
            vprint ModularForms, 3: "modular symbols";
            g := qExpansion_ModularSymbols(f,prec);
         elif assigned f`element then 
            vprint ModularForms, 3: "modular element";
            g := qExpansion_Element(f, prec);
         else
            error "Could not figure out how to compute q-expansion of ", f;    
         end if;
         assert AbsolutePrecision(g) ge prec;
         return [* [g] *];
      when "modp":
         phi := ModpReductionMaps(f, data);
      when "padic":
         phi := pAdicEmbeddingMaps(f, data);
      when "complex":
         phi := ComplexEmbeddingMaps(f);
      when "map":
         phi := data;
      else      
         assert false;
   end case;
   return ApplyMapsTo_qExpansion(PowerSeriesInternal(f,prec), phi);
end function;


function BasisOfWeightOneCuspForms(M,prec)
   assert Type(M) eq ModFrm;
   assert Weight(M) eq 1;
   assert Type(prec) eq RngIntElt and prec ge 0;
   assert IsCuspidal(M);
   assert IsIdentical(M, CuspidalSubspace(AmbientSpace(M)) );

   if not assigned M`is_wt1_dihedral then compute_weight1_cusp_space(~M); end if;
   assert assigned M`is_wt1_dihedral and assigned M`wt1_auxil_modsyms and 
          assigned M`ambient_space`wt1_dihedral_forms;
   dihedforms := M`ambient_space`wt1_dihedral_forms;

   // Get qexps for each chi either from dihedral_forms or from auxil_modsyms
   qexps := [];
   for i := 1 to #M`is_wt1_dihedral do 
      chi := M`is_wt1_dihedral[i][1];
      if M`is_wt1_dihedral[i][2] then 
        // the 'chi'-component is spanned by the dihedral_forms
        assert IsIdentical(chi, dihedforms[i][1]);          // if not, the order got screwed up
        qexps_chi := [PowerSeriesInternal(f,prec) : f in dihedforms[i][2]];
      else
        assert IsIdentical(chi, M`wt1_auxil_modsyms[i][1]); // if not, the order got screwed up
        _, F, vecs, MS := Explode(M`wt1_auxil_modsyms[i]);  
        // F is a ModFrmElt, vecs are vectors specifying combinations of the qExpansionBasis of MS
        // (this is stable assuming it was done up to the Sturm bound)
        assert not IsEmpty(vecs);
        assert Degree(Universe(vecs)) eq Dimension(MS);

        // val := valuation of F
        val := 0; while Coefficient(PowerSeriesInternal(F,val+1),val) eq 0 do val +:= 1; end while;

        // Compute q-exps of MS to required precision and identify the Gs in there
        prec1 := prec + val;
        repeat prec1 +:= 1; 
           qexpsMS := qExpansionBasis(MS, prec1);
        until #qexpsMS eq Dimension(MS);
        SR := ChangeRing(Universe(qexpsMS), BaseRing(Universe(vecs)));
        Gs := [&+[ v[i] * SR! qexpsMS[i] : i in [1..Ncols(v)]] : v in vecs];

        // Divide the Gs by F
        F := qExpansion(F, prec1); 
        one_over_F := 1/F;
        qexps_chi := [G*one_over_F : G in Gs];
      end if;
      // qexps_chi may be over an extension field, so get qexps over Q by pulling off coefficients
      qexps cat:= &cat[ RestrictionOfScalarsToQ(f) : f in qexps_chi];
   end for;

   return EchelonPowerSeriesSequence(qexps);
end function;


function BasisOfWeightOneForms(M,prec)
   assert Type(M) eq ModFrm;
   assert Weight(M) eq 1;
   assert Type(prec) eq RngIntElt and prec ge 0;

   C := CuspidalSubspace(M);
   C_basis := BasisOfWeightOneCuspForms(C,prec);

   E := EisensteinSubspace(M);
   E_basis := qExpansionOfModularFormsBasis(E,prec);

   return  EchelonPowerSeriesSequence(C_basis cat E_basis);
end function;


function CuspformBasisUsingModularSymbols(M,prec)
   assert Type(M) eq ModFrm;
   assert Weight(M) ge 2;
   assert Type(prec) eq RngIntElt and prec ge 0;
   assert IsCuspidal(M);
   assert Type(BaseRing(M)) in {FldRat, RngInt};

   modsym := MF_ModularSymbols(M,+1);

   if Type(modsym) eq SeqEnum then
      Q := &cat [qExpansionBasis(m,prec) : m in modsym];
   else
      Q := qExpansionBasis(modsym,prec);
   end if;
   if #Q eq 0 then
      return Q;
   end if;
   F := BaseRing(Parent(Q[1]));
   if Type(F) eq FldCyc then
      Q := EchelonPowerSeriesSequence(&cat[
                   RestrictionOfScalarsToQ(f) : f in Q]);   
   end if;
   return Q;
end function;


function BasisUsingBrandtModule(M,prec)
   assert Type(M) eq ModFrm;
   assert Weight(M) ge 2;
   assert Type(prec) eq RngIntElt and prec ge 0;

   error "BasisUsingBrandtModule -- Not programmed.";
end function;


// William envisaged a function called BasisGotByMultiplyingLowerWeight.
// Below is Steve's version of that.

// helper
// list all representations of k as a sum of the integers in ks, 
// where 'ks' is a sequence in increasing order
// TO DO: the general case apparently gets really inefficient before too long
function knapsack(k, ks : sorted:=false)

   if not sorted then assert ks eq Sort(ks); end if; // must be sorted

   // easy cases
   if k eq 0 then 
      return {[0 : kk in ks]}; 
   elif #ks eq 1 then 
      return (k mod ks[1] eq 0) select {[k div ks[1]]} else {};
   elif ks eq [2,4] then 
      if IsOdd(k) then return {}; end if;
      return {[(k-4*b) div 2, b] : b in [0 .. k div 4]};
   end if;
   
   n := #ks;
   assert k gt 0;
   // sols using ks[n]
   if k lt ks[n] then 
      ans1 := {};
   else
      ans1 := knapsack(k-ks[n], ks : sorted);
      ans1 := {a[1..n-1] cat [a[n]+1] : a in ans1};
   end if;
   // sols not using ks[n]
   if n eq 1 then 
      ans2 := {};
   else
      ans2 := knapsack(k, ks[1..n-1] : sorted);
      ans2 := {a cat [0] : a in ans2};
   end if;
   return ans1 join ans2;
end function;

function RankLowerBound(X)
    if Type(BaseRing(X)) in {RngInt, FldRat} then
	B := 23.5;
	repeat
	    p := PreviousPrime(Random(Round(2^(B - 1)), Round(2^B)));
	    K := GF(p);
	    l, Y := IsCoercible(ChangeRing(Parent(X), K), X);
	until l;
	return Rank(Y);
    end if;
    return Rank(X);
end function;

function multiply_bases(bas0, bas1 : dim:="?", same:=false)

   R := Universe(bas0);
   prec := AbsolutePrecision(bas0[1]);
   V := RSpace(Integers(), prec);
   prods := []; 

   for i in [1,#bas0] cat [2 .. #bas0-1] do 
// if dim cmpne "?" then "i =", i; end if;
      chop := prec - Valuation(bas0[i]);
      for j := (same select i else 1) to #bas1 do 
        f := bas0[i] * (bas1[j] + O(R.1^chop)); // chop precision to prevent product working too hard
        assert AbsolutePrecision(f) eq prec;
        fcoeffs, lowest := Coefficients(f+O(R.1^prec));
        if lowest gt 0 then fcoeffs := [0 : i in [0..lowest-1]] cat fcoeffs; end if;
        if #fcoeffs lt Dimension(V) then fcoeffs cat:= [0 : i in [#fcoeffs+1..Dimension(V)]]; end if;
        v := V!fcoeffs;
        Append(~prods, v);
      end for; 

      if dim cmpne "?" then 
	r := RankLowerBound(Matrix(prods));
	// "Now rank", r;
	if r eq dim then break; end if;
        error if r gt dim,
	     "Multiplying bases of power series -- space obtained is too large";
      end if;
   end for;

//"Echelon"; time
   // The next line was carefully crafted by Allan -- Saturation does echelon over Q
   M := EchelonForm(Saturation(Matrix(RationalField(), Matrix(prods))));
   r := Rank(M);
   error if dim cmpne "?" and r lt dim,
        "Multiplying bases of power series -- space obtained is too small";
   return [R! Eltseq(M[i]) + O(R.1^prec) : i in [1..r]];
end function;

// helper
// the answer gets assigned to 'bas', and the 'known' arguments get updated if desired
// (Maybe this 'known' paraphenalia shouldn't be here at all)
procedure get_basis_for_comb_by_repeated_squaring
              ( orig_bases, ~known_combs, ~known_bases, comb, ~bas : dims:=[], store:=true)
   assert #orig_bases eq 1;
   m := comb[1];
   // dims should list the dimensions of (orig_bases[1])^i for 1 <= i <= m
   assert #dims eq m;  
   // write m in binary, so m = Sum_i  m_bin[i] * 2^(i-1)
   m_bin := [];  mm := m;
   while mm gt 0 do 
      Append( ~m_bin, mm mod 2);
      mm div:= 2;
   end while;
 assert m eq &+[ m_bin[i] * 2^(i-1) : i in [1..#m_bin]] and m_bin[#m_bin] eq 1;
   bas_powers := [ orig_bases[1] ];
   for i := 1 to #m_bin - 1 do 
      Append( ~bas_powers, multiply_bases(bas_powers[i], bas_powers[i] : dim:=dims[2^i], same:=true) );
   end for;
   if store then
      known_combs cat:= [2^(i-1) : i in [2..#m_bin]];
      known_bases cat:= [bas_powers[i] : i in [2..#m_bin]];
   end if;
   i1 := Index(m_bin,1);  // should find the first occurence
 assert i1 gt 0 and m_bin[i1] eq 1 and &and[m_bin[j] eq 0 : j in [1..i1-1]];
   mm := 2^(i1-1);
   bas := bas_powers[i1];
   for i := i1+1 to #m_bin do 
      if m_bin[i] eq 1 then 
         mm +:= 2^(i-1);
         bas := multiply_bases(bas, bas_powers[i] : dim:=dims[mm] );
         if store then
            Append( ~known_combs, mm);
            Append( ~known_bases, bas);
         end if;
      end if;
   end for;
   assert mm eq m;
end procedure;

// helper
// the answer gets assigned to 'bas', and the 'known' arguments get updated
procedure get_basis_for_comb( orig_bases, ~known_combs, ~known_bases, comb, ~bas : dims:=[])
   idx := Index( known_combs, comb);
   if idx ne 0 then bas := known_bases[idx]; return; end if;
   use_dims := #orig_bases eq 1 and #dims ge comb[1]; 
            // if true, assume dims = [Dimension(orig_bases[1]^i) : 1 <= i <= comb[1]]
   // recurse
   // TO DO: be smarter
   assert Max(comb) gt 0;  // if not, recursion has run amok ...
   _,i := Max(comb); comb1 := comb; comb1[i] -:=1;
   bas0 := orig_bases[i];
   get_basis_for_comb( orig_bases, ~known_combs, ~known_bases, comb1, ~bas1 : dims:=dims);
   dim := use_dims select dims[comb[1]] else "?";
   bas := multiply_bases(bas0, bas1 : dim:=dim, same:=(bas0 eq bas1) );
   Append( ~known_combs, comb);
   Append( ~known_bases, bas);
end procedure;

// A q-expansion basis of the space of forms of weight k spanned by 
// arbitrary power-products of forms from the spaces in the given sequence.
// 'dim_bound' is an upper bound on the dimension of the space generated.
// 'dims' are exact dimensions of the intermediate product spaces.
function q_expansion_basis_using_lower_weight(k, prec, spaces : dims:=[], dim_bound:=Infinity(),
                                                                dim_bound_is_exact:=false) 
   assert &and &cat[ [Type(f) eq ModFrmElt : f in M] : M in spaces];
   ks := [Weight(M[1]) : M in spaces];
   orig_bases := [ [qExpansion(f,prec) : f in M] : M in spaces];

   use_dims := #spaces eq 1 and not IsEmpty(dims);

   if use_dims and 1 eq 1 then // switch on the 'repeated squaring' method 
      // dims[i] should be the dimension of (spaces[1])^i 
      m := k div ks[1];
      assert dims[1] eq #spaces[1] and #dims eq m and dims[m] le dim_bound;
      s1 := []; s2 := [];  // dummy variables (this is silly)
      get_basis_for_comb_by_repeated_squaring( orig_bases, ~s1, ~s2, [m], ~ans : dims:=dims, store:=false);
      error if #ans gt dim_bound, 
              "Using lower weight: the space generated is too large";
      error if dim_bound_is_exact and #ans lt dim_bound,
              "Using lower weight: the space generated is too small";
      return ans; 
   end if;
      
   Sort(~ks, ~perm);
   spaces := [* spaces[i] : i in Eltseq(perm) *];  // order the spaces by weight
   combs := knapsack(k, ks);  // all combinations of weights that add up to k
   vprintf ModularForms,1:
          "Products of lower weight spaces ... there are %o possible combinations\n", #combs;

   // Store bases of intermediate products that have been worked out 
   // (initially just the spaces themselves)
   known_combs := [ [j eq i select 1 else 0 : j in [1..#ks]]  :  i in [1..#ks] ];
   known_bases := orig_bases;

   ans := [];
   num_combs_used := 0;
   for comb in combs do 
      num_combs_used +:= 1;
      vprintf ModularForms,3: "Trying combination %o\n", comb;
      get_basis_for_comb( orig_bases, ~known_combs, ~known_bases, comb, ~bas 
                        : dims:=(use_dims select dims else "?") ); 
      ans := EchelonPowerSeriesSequence(ans cat bas);
      // The 'ans' MUST be echelonized at this point
      error if #ans gt dim_bound, "Using lower weight: the space generated is too large";
      if #ans eq dim_bound then  // early exit
         vprintf ModularForms,1: "Needed to use %o combinations\n", num_combs_used;
         return ans; end if;  
   end for;
   vprint ModularForms,1: "Needed to use all combinations";   
   error if dim_bound_is_exact and #ans lt dim_bound, 
        "Using lower weight: the space generated is too small";
   return ans;
end function;


function q_expansion_basis_using_auxiliary(M, prec)
/*
 The attribute M`generated_by_auxiliary is a list of tuples.
 Each tuple gives a recipe for a subspace of M, and these subspaces
 together generate M. The tuples have the form <type, data> where
 'type' is a string, and 'data' depends on the type. The options are:
    type = "eisenstein", no data :
           the eisenstein subspace
    type = "elts_mult_elts", data = [*seq1,seq2*] :
           the space generated by the q-expansions f1*f2, 
           for all f1 in seq1 and f2 in seq2, 
           where seq1 and seq2 are sequences of ModFrmElt's
    type = "space_div_elt", data = <M1, M2, f1, f2> :  
           the space of q-expansion { m/f1 : m in M1, f2*m lies in f1*M2 }
           (for more details see q_expansion_basis_via_space_div_elt)
    type = "low_weight_spaces", data = [M1,M2,...,Mn] :  
           the space generated by all products f = f1^k1*...*fn^kn  (for fi in Mi)
           for which Weight(f) = Weight(M),
           where each Mi is a list of ModFrmElt's generating a subspace 
           of some ModFrm space with the same level as M (but lower weight).
           Optionally the tuple can have a third item <dim_bound,dim_bound_is_exact> = <Integer,BoolElt>,
           and even a fourth item giving dimensions of all the intermediate product spaces
*/
   assert Type(M) eq ModFrm;
   assert IsIntegral(Weight(M)) select prec ge PrecisionBound(M) 
                                 else  prec gt 0;
   assert BaseRing(M) cmpeq Integers(); // otherwise should have gone via associated_space_over_Z
   assert assigned M`generated_by_auxiliary; // function is only called if this has been assigned
   
   if GetVerbose("ModularForms") ge 2 then
      printf "Getting q-expansions using auxiliary spaces of the following kinds:";
      for tup in M`generated_by_auxiliary do printf " %o,", tup[1]; end for; 
      printf "\n"; end if;
 
   span := [];
   for tup in M`generated_by_auxiliary do
      // work out the space of q-expansions indicated by tup, to precision prec
      if tup[1] eq "eisenstein" then 
         E := EisensteinSubspace(M);
         new_stuff := qExpansionOfModularFormsBasis(E,prec);
      elif tup[1] eq "elts_mult_elts" then 
         seq1, seq2 := Explode(tup[2]);
         new_stuff := [ qExpansion(f1,prec) * qExpansion(f2,prec) : f1 in seq1, f2 in seq2];
      elif tup[1] eq "space_div_elt" then
         new_stuff := q_expansion_basis_via_space_div_elt(M, prec, tup[2]);
      elif tup[1] eq "low_weight_spaces" then 
         if #tup ge 3 then 
            dim_bound, exact := Explode(tup[3]);
         elif #M`generated_by_auxiliary eq 1 then
            dim_bound:=DimensionByFormula(M); exact:=true;
         else
            // nothing
            dim_bound:=Infinity(); exact:=false;
         end if;
         dims := (#tup ge 4) select tup[4] else [];
/* printf "New method -- using lower weight spaces (weights %o) to get the q-expansion basis for\n", 
                                                   [Weight(Universe(fseq)) : fseq in tup[2]];  
   if dim_bound lt DimensionByFormula(M) then printf IntegerToString(dim_bound)*"-dimensional subspace of "; end if;
   print M; */
         new_stuff := q_expansion_basis_using_lower_weight(Weight(M), prec, tup[2] : dims:=dims,
                                                           dim_bound:=dim_bound, dim_bound_is_exact:=exact);
      end if;
      span := EchelonPowerSeriesSequence(span cat new_stuff);
   end for;
   if #span lt Dimension(M) then 
      // TO DO: this can currently occur with half-integral multi-char spaces
      printf "The precision used ( = %o) seems to be too low", prec; 
      printf " -- try running qExpansionBasis with higher precision";  
      error "";
   end if;
   return span;
end function;


function can_get_basis_from_lower_weight(M)
// true iff we know how to generate the basis of M by multiplying forms from other spaces
// If true then store these other bases in M`generated_by_auxiliary

   // This check is a bit silly ...  in any case the calling function 
   // should first check whether there's already a known way to compute the space
   if assigned M`generated_by_auxiliary then 
      aux := M`generated_by_auxiliary;
      if #aux eq 1 and aux[1][1] eq "low_weight_spaces" then
         return true;
      else   
         // Could just return true anyway, but during development I want to know if this happens.
         error "Already know how to generate M using auxiliary data (not only using low weight)";
      end if;
   end if;
   
   if SpaceType(M) cmpne "full" then return false; end if;
   
   // TO DO: handle the cuspidal subspaces too

   /*
   Proofs of the facts used below are given in notes available from Steve.
   In the case of Gamma0(4), another argument is given in Koblitz exercise 17(f), page 146 
   */

   k := Weight(M); N := Level(M);
   ans := 0;
   if k eq 2 or IsOdd(k) or (not IsGamma0(M) and not IsGamma1(M)) then 
      return false; 
   elif IsGamma0(M) and N eq 2 and IsEven(k) and k ge 6 then
      ans := [*<"low_weight_spaces", [*[ModularForms(2,2).1], [ModularForms(2,4).2]*] >*];
   elif IsGamma0(M) and N eq 3 and k ge 6 then 
      /*
      case k mod 6 :
        when 0: spaces := [*Basis(ModularForms(KroneckerCharacter(-3),3))*];
        when 2: spaces := [*Basis(ModularForms(KroneckerCharacter(-3),3)), Basis(ModularForms(3,2))*];
        when 4: spaces := [*Basis(ModularForms(KroneckerCharacter(-3),3)), Basis(ModularForms(3,4))*];
      end case;
      ans := [*<"low_weight_spaces", spaces>*];
      */
      if k mod 6 eq 0 then 
         ans := [*<"low_weight_spaces", [*Basis(ModularForms(KroneckerCharacter(-3),3))*]>*];
      elif k mod 6 eq 2 then
         ans := [*<"elts_mult_elts", [*Basis(ModularForms(3,k-2)),[ModularForms(3,2).1]*]>*];
      elif k mod 6 eq 4 then
         ans := [*<"elts_mult_elts", [*Basis(ModularForms(3,k-4)),[ModularForms(3,4).2]*]>,
                  <"low_weight_spaces", [*[ModularForms(3,2).1]*], <1,true>> *];
      end if;
   elif IsGamma0(M) and N in {4,6,8,9,12} and IsEven(k) and k ge 4 then
      ans := [*<"low_weight_spaces", [*Basis(ModularForms(N))*] >*];
   elif IsGamma0(M) and N eq 5 and IsEven(k) and k ge 6 then 
      spaces := [*Basis(ModularForms(5)), [M4.2,M4.3] where M4 is ModularForms(5,4)*];
      ans := [*<"low_weight_spaces", spaces>*];
   elif IsGamma0(M) and N eq 7 and IsEven(k) and k ge 6 then
      if k mod 6 eq 0 then
         ans := [*<"low_weight_spaces", [*Basis(ModularForms(KroneckerCharacter(-7),3))*]>*];
      elif k mod 6 eq 2 then
         ans := [*<"elts_mult_elts", [*Basis(ModularForms(7,k-2)),[ModularForms(7,2).1]*]>*];
      elif k mod 6 eq 4 then
         // TO DO: more efficient would be to do weight k-1 (obtained from weight 3) times the weight 1 form
         // obtained by taking the square root of the weight 2 form
         ans := [*<"elts_mult_elts",[* Basis(ModularForms(7,k-4)), [M4.1,M4.3] where M4 := ModularForms(7,4) *]>*];
      end if;
   elif IsGamma0(M) and N eq 11 and IsEven(k) and k ge 6 then 
      spaces := (k mod 4 eq 0) select [*Basis(CuspForms(11)), [M4.1,M4.2,M4.4] where M4 is ModularForms(11,4)*]
                                else  [*Basis(ModularForms(11)), [ModularForms(11,4).4]*];
                            // the first is supposedly more efficient, while the second is valid for all k
      ans := [*<"low_weight_spaces", spaces>*];
   elif IsGamma1(M) and N ge 4 and IsEven(k) and k ge 4 and ( IsPrime(N) or N in {4,6,8,9,10,12} ) then 
      // TO DO : Put a limit on which cases to use this method (or else make the multiplication stuff efficient)
      // The prime case is from a result in Borisov-Gunnells, proving that everything comes from weight 1 
      // (which implies that everything in even weight comes from weight 2)
      ans := [*<"low_weight_spaces", [*Basis(ModularForms(Gamma1(N)))*], 
                                     <DimensionByFormula(ModularForms(Gamma1(N),k)),true>,
                                     [DimensionByFormula(ModularForms(Gamma1(N),kk)) : kk in [2 .. k by 2]] >*];
   end if;
   
   if ans cmpeq 0 then 
      return false;
   else
      M`generated_by_auxiliary := ans;
      return true;
   end if;
end function;


function BasisOfIntegralWeightAtLeast2Forms(M, prec)
   assert Type(M) eq ModFrm;
   assert Weight(M) ge 2;
   assert Type(prec) eq RngIntElt and prec ge 0;
   assert not IsEisenstein(M);  // or there might be an infinite recursion.

   C := CuspidalSubspace(M);
   C_basis := CuspformBasisUsingModularSymbols(C,prec);
   E := EisensteinSubspace(M);
   E_basis := qExpansionOfModularFormsBasis(E,prec);
   return  EchelonPowerSeriesSequence(C_basis cat E_basis);
end function;


function MakeRestrictionOfScalars(E)
   assert Type(E) eq SeqEnum;
   assert #E ne 0;
   prec := #E;
   q := PowerSeriesRing(Parent(E[1][1])).1;
   return [&+[E[n+1][i]*q^n : n in [0..prec-1]] + O(q^prec) : i in [1..#E[1]]];
end function;


function RestrictionOfScalarsFromCycloToQ(f)
   assert Type(f) eq RngSerPowElt;

   R := BaseRing(Parent(f));  
   assert Type(R) in {FldCyc, FldRat, RngInt};
   if Type(R) in {FldRat, RngInt} then
      return [f];
   end if;

   /* f is a q-expansion over a cyclotomic field.
      Compute the sequence of restrictions to Q. */
   prec := AbsolutePrecision(f);
   R    := PowerSeriesRing(Rationals());
   q    := R.1;
   if prec eq 0 then
      return [O(q)];
   end if;
   E := [Eltseq(Coefficient(f,n)) : n in [0..prec-1]];
   return MakeRestrictionOfScalars(E);
end function;

function FldEltseq(a, d)
   e := Eltseq(a);
   return e cat [0 : i in [#e+1..d]];
end function;

function RestrictionOfScalarsFromPolResToBase(f)
   assert Type(f) eq RngSerPowElt;
   d := Degree(Modulus(BaseRing(Parent(f))));
   prec := AbsolutePrecision(f);
   E := [FldEltseq(Coefficient(f,n),d) : n in [0..prec-1]];
   return MakeRestrictionOfScalars(E);
/*   q := PowerSeriesRing(BaseRing(BaseRing(Parent(f)))).1;
   return [&+[E[n+1][i]*q^n : n in [0..prec-1]] + O(q^prec) : i in [1..#E[1]]];
*/
end function;

function RestrictionOfScalarsFromFldNumToBase(f)
   assert Type(f) eq RngSerPowElt;
   prec := AbsolutePrecision(f);
   E := [Eltseq(Coefficient(f,n)) : n in [0..prec-1]];
   return MakeRestrictionOfScalars(E);
end function;

function RestrictionOfScalarsToQ(f)
   assert Type(f) eq RngSerPowElt;

   if Type(BaseRing(Parent(f))) eq RngUPolRes then
      F := RestrictionOfScalarsFromPolResToBase(f);
   elif Type(BaseRing(Parent(f))) eq FldNum then
      F := RestrictionOfScalarsFromFldNumToBase(f);
   else
      F := [f];
   end if;

   return &cat[RestrictionOfScalarsFromCycloToQ(g) : g in F];

end function;


function BasisOfEisensteinSpace(M, prec)
   assert Type(M) eq ModFrm;
   assert Type(prec) eq RngIntElt;
   assert SpaceType(M) in { "eis", "eis_new" };
   if SpaceType(M) eq "eis_new" then
      E := [* *];
      for f in ComputeEisensteinNewforms(M) do
         for g in f do
            Append(~E, g);
         end for;
      end for;
   else
      E := EisensteinSeries(M);  
   end if;
   basis := &cat [RestrictionOfScalarsToQ(PowerSeriesInternal(f,prec)) : f in E];
   basis := EchelonPowerSeriesSequence(basis);
   return basis;
end function;


function CoercePowerSeriesElement(R, f)
   assert Type(R) eq RngSerPow;
   assert Type(f) eq RngSerPowElt;
   prec := AbsolutePrecision(f);
   return &+[(BaseRing(R)!Coefficient(f,n))*R.1^n : n in [0..prec-1]] + O(R.1^prec);
end function;


function CoerceAndEchelonBasis(basis, F)
   assert Type(basis) eq SeqEnum;
   R := PowerSeriesRing(F);
   B := [R|CoercePowerSeriesElement(R,f) : f in basis];
   return EchelonPowerSeriesSequence(B);
end function;


function qExpansionOfModularFormsBasis(M, prec) 
   assert Type(M) eq ModFrm;
   assert Type(prec) eq RngIntElt;
   prec := Max(prec, PrecisionBound(M)); 
   // changed ApproximatePrecisionBound to PrecisionBound here  -- Steve
      /* Comment from Steve:
      The reasons why its necessary to go up to the PrecisionBound are:
      1) The results do not determine which q-expansions have integral coefficients.
         (On the other hand, if f has integral coefficients up to ApproximatePrecisionBound(M)
          then all its coefficients are integral. This follows from Sturm's mod m result, as
          stated in William's book, together with Buzzard's observation about taking powers.)
      2) As a consequence of 1), the Basis(M) will not be uniquely determined
         (regardless of the ground field, since Basis(M) is obtained from the 
          basis of the associated space over Z).
      */
      
   R := PowerSeriesRing(BaseRing(M));
   q := R.1;
   if Dimension(M) eq 0 then
      return [R|];
   end if;

   if not assigned M`q_expansion_basis or M`q_expansion_basis[1] lt prec then
      if assigned M`made_from_newform then
         f := PowerSeriesInternal(M`made_from_newform,prec);
         basis_Z := ClearDenominatorsAndSaturate(
                       EchelonPowerSeriesSequence(
                       RestrictionOfScalarsToQ(f)));
         basis := [R!f : f in basis_Z];
      elif Level(M) eq 1 and not IsEisenstein(M) then
         basis := Level1Basis(Weight(M), prec);
         if IsCuspidal(M) then
            Remove(~basis,1);
         end if;
         basis := [R!f : f in basis];
      elif Type(BaseRing(M)) ne RngInt then
         assert Dimension(M) eq Dimension(AssociatedSpaceOverZ(M));
         basis_Z := qExpansionOfModularFormsBasis(AssociatedSpaceOverZ(M),prec);  
         basis := [R!f : f in basis_Z];
      else  // over Z
         basis := [R|];
         if Weight(M) le 0 then
            // nothing
         elif IsEisenstein(M) then
            basis := BasisOfEisensteinSpace(M,prec);
         elif Weight(M) eq 1 then
            basis := BasisOfWeightOneForms(M,prec);
         elif Weight(M) eq 1/2 then
            basis := q_expansion_basis_weight_half(M,prec);
         elif not (Weight(M) in Integers()) and (2*Weight(M) in Integers()) then
            basis := q_expansion_basis_half_integral(M,prec);
         elif assigned M`generated_by_auxiliary 
              or can_get_basis_from_lower_weight(M) then 
            basis := q_expansion_basis_using_auxiliary(M,prec);
         else
            basis := BasisOfIntegralWeightAtLeast2Forms(M,prec);
         end if;
         basis := ClearDenominatorsAndSaturate(basis);
      end if;
      M`q_expansion_basis := <prec, basis>;
      // check that we computed the right dimension
      if BaseRing(M) cmpeq Integers() then 
         assert #basis eq Dimension(M); end if;
      if AbsolutePrecision(basis[#basis]) ge ApproximatePrecisionBound(M) then 
         assert not IsWeaklyZero(basis[#basis]); end if;
   end if;
   basis := [R|f + O(q^prec) : f in M`q_expansion_basis[2]];
   if #basis lt Dimension(M) then
      basis cat:= [O(q^prec) : i in [#basis+1..Dimension(M)]];
   end if;
   return basis;
end function;

function ClearDenominators(f)
   assert Type(f) eq RngSerPowElt;
   if Type(BaseRing(Parent(f))) eq RngInt then
      return f;
   end if;
   assert Type(BaseRing(Parent(f))) eq FldRat;
   denom := LCM([Denominator(Coefficient(f,n)) : n in [0..AbsolutePrecision(f)-1]]);
   return denom*f;
end function;

function ClearDenominatorsAndSaturate(rational_basis)
   assert Type(rational_basis) eq SeqEnum;
   if #rational_basis eq 0 then
      return rational_basis;
   end if;
   assert Type(BaseRing(Parent(rational_basis[1]))) in {RngInt, FldRat};
   no_denominators := [ClearDenominators(f) : f in rational_basis];
   basis           := SaturatePowerSeriesSequence(no_denominators);
   return basis;
end function;
