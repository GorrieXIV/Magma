freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: eisenstein.m  (Eisenstein series)

   05/02/03: Massively optimized PrimitiveEisensteinSeries for level 1. -- WAS
                                                                            
   $Header: /home/was/magma/packages/ModSym/code/RCS/eisenstein.m,v 1.3 2002/09/25 19:01:43 was Exp was $

   $Log: eisenstein.m,v $
   Revision 1.3  2002/09/25 19:01:43  was
   Fixed very serious bug in Do_PrimitiveEisensteinSeries (I had a stupid optimization).

   Revision 1.2  2001/05/27 11:04:56  was
   Got rid of import ValueList, because it is not an intrinsic.

   Revision 1.1  2001/05/27 11:04:30  was
   Initial revision

   Revision 1.1  2000/05/02 08:01:00  was
   Initial revision


 ***************************************************************************/

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

function GeneralizedBernoulli(k, eps)
   assert Type(k) eq RngIntElt and k ge 0;
   assert Type(eps) eq GrpDrchElt;
   assert Evaluate(eps,-1) eq (-1)^k;
  
   N    := Modulus(eps);
   K    := BaseRing(eps);
   R<t> := LaurentSeriesRing(K);
   prec := k+5;
   F    := &+[Evaluate(eps,a)*t*Exp(a*t+O(t^prec))/(Exp(N*t+O(t^prec)) -1) 
                     : a in [1..N]];
   Bk   := Coefficient(F,k)*Factorial(k);
   return Bk;
end function;


/* PrimitiveEisensteinSeries:
   k   : RngIntElt,   nonnegative integer weight
   eps : GrpDrchElt,  a Dirichlet character modulo N that is 
                      of conductor N (i.e., is primitive)
   prec : RngIntElt,  the absolute precision of the resulting series

   This function returns the normalized Eisenstein series of weight k  
   associated to the primitive Dirichlet character eps.  The series
   is normalized so that the constant coefficient is 1.  The formula,
   which is incorrectly stated in Diamond-Im, page 45, is:

          1/A + sum_{n=1}^{\infty} (sum_{d|n} eps(d)*d^{k-1})q^n,

   where
    
            A = -2k/B_{k,eps}. 
    
*/

function Do_PrimitiveEisensteinSeries(k, eps, prec)
   assert Type(k) eq RngIntElt and k ge 0;
   assert Type(eps) eq GrpDrchElt;
   assert Type(prec) eq RngIntElt and prec ge 1; 

   K    := BaseRing(Parent(eps));
   if IsTrivial(eps) then
      R<q> := PowerSeriesRing(K);
      return R!PrimitiveEisensteinSeries(k, prec);
   end if;
   
   R<q> := PowerSeriesRing(K);
   A    := -2*k/GeneralizedBernoulli(k,eps);
   N    := Modulus(eps);
   f := R!([K|1/A] cat [K|&+[Evaluate(eps,d)*d^(k-1) : d in Divisors(n)] 
                      : n in [1..prec-1]]) + O(q^prec);
   return f;

end function;


intrinsic PrimitiveEisensteinSeries(k::RngIntElt, 
                                 prec::RngIntElt) -> RngSerPowElt

{Compute the q-expansion of the weight-k Eisenstein series 
 of level 1, normalized so that the coefficient of q is 1.}
   requirege k,0;
   requirege prec,1;
   R<q> := PowerSeriesRing(RationalField());
   A    := -2*k/BernoulliNumber(k);

   // v[n] is n-th coefficient of eisenstein series.
   v := [0 : i in [1..prec-1]];  
   v[1] := 1;
   for n in [2..prec-1] do
      if IsPrime(n) then
         v[n] := n^(k-1) + 1;
      else
         F := Factorization(n);
         if #F gt 1 then
            m := F[1][1]^F[1][2];
            v[n] := v[m]*v[n div m];
         else  // prime power
            p := F[1][1];
            v[n] := v[n div p]*v[p] - p^(k-1)*v[n div (p^2)];
         end if;
      end if;
   end for;
   f := 1/A + R!([0] cat v) + O(q^prec);
   return f;
end intrinsic;

intrinsic PrimitiveEisensteinSeries(k::RngIntElt, 
                                  eps::GrpDrchElt, 
                                 prec::RngIntElt) -> RngSerPowElt
 
 {Compute the q-expansion of the Eisenstein series associated 
to the primitive character epsilon, normalized so that
the coefficient of q is 1.}

   requirege k,0;
   requirege prec,1;
   require Evaluate(eps,-1) eq (-1)^k : 
      "The sign of argument 2 must equal the parity of argument 1.";
   require Conductor(eps) eq Modulus(eps) :
      "Argument 2 must be primitive.";

   return Do_PrimitiveEisensteinSeries(k,eps,prec);

end intrinsic;

