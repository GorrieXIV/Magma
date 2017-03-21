freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: dims.m (Dimension formulas)                                        
                                                                            
   $Header: /home/was/magma/packages/ModSym/code/RCS/dims.m,v 1.11 2002/05/21 18:36:30 was Exp $
 
   $Log: dims.m,v $
   Revision 1.11  2002/05/21 18:36:30  was
   fixed a bug!
    I just found a potentially-very-annoying bug in dims.m, which
   resulting from some slopiness.  Line 542 of ModSym/dims.m should be
              DimensionNewCuspForms(eps,k);
   instead of
              DimensionNewCuspFormsGamma1(eps,k);

   Revision 1.10  2002/04/13 05:57:29  was
   Added dimensions for p-new subspaces.

   Revision 1.9  2001/12/05 22:16:14  was
   nothing.

   Revision 1.8  2001/11/26 06:17:06  was
   Added DimensionNewCuspForms for nontrivial character.

   Revision 1.7  2001/09/03 23:17:24  was
   fixed bug.

   Revision 1.6  2001/08/09 21:35:11  was
   Integrated  Kevin Buzzard's optimization to the dimension formulas when the
   character is nontrivial.

   Revision 1.5  2001/08/08 20:32:43  was
   Better handling for weight 0 special case.

   Revision 1.4  2001/08/07 03:25:27  was
   Changed DimensionCuspForms slightly to take into account the possibility of
   characters over ComplexField.

   Revision 1.3  2001/05/19 00:49:58  was
   removed DimEisenstein...

   Revision 1.2  2001/05/16 04:49:57  was
   Added dummy EisensteinSeries dimension functions.

   Revision 1.1  2001/04/20 04:46:19  was
   Initial revision

   Revision 1.2  2001/01/16 11:01:30  was
   nothing.

   Revision 1.1  2000/05/02 08:00:10  was
   Initial revision

  
 ***************************************************************************/


/*
  EXPORTS:
    DimensionCuspForms
    DimensionCuspFormsGamma0
    DimensionCuspFormsGamma1
    DimensionNewCuspFormsGamma0
    DimensionNewCuspFormsGamma1

  USES:
    Nothing else from the modular symbols package
*/


/*****************************************************************
  STANDARD MODULAR FORMS DIMENSION FORMULAS

  The first part of this file contains standard functions for
  computing dimensions of spaces of modular forms. It is based 
  on a PARI script, which was written by Bruce Caskel and 
  extended by Kevin Buzzard.
 *****************************************************************/


function mu0(n)
   return &*([n] cat [1+1/t[1]:  t in Factorization(n)]);
end function;


function mu20(n)
   if n mod 4 eq 0 then
      return 0;
   end if;
   return &*[Integers()| 1+KroneckerSymbol(-4,t[1]): t in Factorization(n)];
end function;


function mu30(n)
   if (n mod 2 eq 0) or (n mod 9 eq 0) then
      return 0 ;
   end if;
   return &*[Integers()| 1+KroneckerSymbol(-3,t[1]): t in Factorization(n)];
end function;


function c0(n) 
   return &+[EulerPhi(Gcd(d, Integers()!(n/d))) : d in Divisors(n)];
end function;


function g0(n)
   return Integers()!(1 + mu0(n)/12 - mu20(n)/4 - mu30(n)/3 - c0(n)/2);
end function;


function mu1(n)
   if n le 2 then
      return mu0(n);
   else
      return Integers()!(EulerPhi(n)*mu0(n)/2);
   end if;
end function;


function mu21(n)
   if n lt 4 then return mu20(n); else return 0; end if;
end function;


function mu31(n)
   if n lt 4 then return mu30(n); else return 0; end if;
end function;


function c1(n)
   if n le 3 then return c0(n); end if;
   if n eq 4 then return 3; end if;
   return Integers()!
     (&+[EulerPhi(d)*EulerPhi(Integers()!(n/d))/2 : d in Divisors(n)]);
end function;


function g1(n)
   return Integers()!(1+mu1(n)/12-mu21(n)/4-mu31(n)/3-c1(n)/2);
end function;


function ss0(n,p) 
   assert IsPrime(p) and (n mod p ne 0);
   return g0(n*p) - 2*g0(n) + 1;
end function;

      
function muXNp(n,p) 
   return mu1(n)*mu0(p);
end function;


function mu2XNp(n,p)
   return 0;
end function;


function mu3XNp(n,p)
   return 0;
end function;


function cXNp(n,p) 
   return 2*c1(n);
end function;


function gXNp(n,p)
   if n lt 4 then 
      return g0(n*p);
   end if;
   return 1 + muXNp(n,p)/12 - mu2XNp(n,p)/4 
              - mu3XNp(n,p)/3 - cXNp(n,p)/2 ;
end function;


function ss1(n,p)
   assert IsPrime(p) and (n mod p ne 0);
   return gXNp(n,p) - 2*g1(n) + 1;
end function;


function eisen(p)
   assert IsPrime(p);
   return Numerator((p-1)/12);
end function;


function S0(n,k)
   assert n gt 0;
   if (k le 0) or (k mod 2 ne 0) then 
      return 0;
   end if;
   if k eq 2 then
      return g0(n);
   end if;
   return Integers()!((k-1)*(g0(n)-1) + 
       (k/2-1)*c0(n)+mu20(n)*Floor(k/4)+mu30(n)*Floor(k/3));
end function;


function S1(n,k)
   assert n gt 0;
   if (k le 0) or ((n lt 3) and (k mod 2 ne 0)) then 
      return 0;
   end if;
   if k eq 1 then 
      error "S1, k = 1 not programmed.";
   end if;
   if k eq 2 then
      return g1(n);
   end if;
   if n lt 3 then
      return S0(n,k);
   end if;
   a := (k-1)*(g1(n)-1)+(k/2-1)*c1(n);
   if n eq 4 and k mod 2 ne 0 then
      a +:= 1/2;
   elif n eq 3 then
      a +:= Floor(k/3);
   end if;
   return Integers()!a;
end function;


function idxG0(n)
   return 
      &*[Integers()| t[1]^t[2] + t[1]^(t[2]-1) : t in Factorization(n)];
end function;
   

function idxG1(n)
   return EulerPhi(n)*idxG0(n);
end function;



/*****************************************************************

   Formula of Cohen-Oesterle for dim S_k(Gamma_1(N),eps).
   REF: Springer Lecture notes in math, volume 627, pages 69--78.
   The functions CO_delta and CO_nu, which were first written by Kevin Buzzard,
   are used only by the function CohenOesterle. 

 *****************************************************************/

function CO_delta(r, p, N, eps)
   assert Type(r) eq RngIntElt and r gt 0;
   assert Type(p) eq RngIntElt;
   assert Type(N) eq RngIntElt;
   assert Type(eps) eq GrpDrchElt;

   K := BaseRing(eps);

   if p mod 4 eq 3 then 
      return 0; 
   end if;
   if p eq 2 then 
      return r eq 1 select 1 else 0; 
   end if;

   // interesting case, p=1 mod 4.
   R := PolynomialRing(GF(p));
   x := R.1;
   omega := Integers()!(Roots(x^2+1)[1][1]);
   // omega is a 4th root of 1 mod p

   n := Integers(N)!CRT([omega,1],[p,N div p^r]); // this is within a
                                                  // p-power root of a "local"
                                                  // 4th root of 1 mod p.
   n := n^(p^(r-1)); // this is dead-right now.
   assert (Integers(N)!n)^4 eq 1;

   t := K!Evaluate(eps,n);
   if t eq K!1 then 
      return K!2;
   elif t eq K!-1 then 
      return K!-2;
   else
      return K!0;
   end if;

//   return K!Evaluate(eps,n) + K!Evaluate(eps,-n);
end function;

function CO_nu(r, p, N, eps)
   assert Type(r) eq RngIntElt and r gt 0;
   assert Type(p) eq RngIntElt;
   assert Type(N) eq RngIntElt;
   assert Type(eps) eq GrpDrchElt;

   K := BaseRing(eps);

   if p mod 3 eq 2 then 
      return K!0;
   end if;
     
   if p eq 3 then
      return r eq 1 select 1 else 0; 
   end if;

   // interesting case, p=1 mod 3.
   R := PolynomialRing(GF(p));
   x := R.1;
   omega := Integers()!(Roots(x^2+x+1)[1][1]);
                                  // cube root of 1 mod p
   n := Integers(N)!CRT([omega,1],[p,N div p^r]); // this is within a
                                                  // p-power root of a "local"
                                                  // cube root of 1 mod p.
   n := n^(p^(r-1)); // this is dead-right now.

   t := K!Evaluate(eps,n);
   if t eq K!1 then 
      return K!2;
   else 
      return K!-1;
   end if;
end function;


/* Kevin's clever function has a bug, so I'm not using it now:
 K := CyclotomicField(3);   
 eps := DirichletGroup(7*43,K).1^2;
 CuspidalSubspace(ModularForms([eps],2));
 boom!
*/

function CohenOesterle(eps, k)
   N    := Modulus(eps);   
   facN := Factorization(N); 
   f    := Conductor(eps); 
   facf := [<p,Valuation(f,p)> : p in [q[1] : q in facN]];
   
   gamma_k := 0;
   if k mod 4 eq 2 then
      gamma_k := -1/4;
   elif k mod 4 eq 0 then
      gamma_k := 1/4;
   end if;
   mu_k := 0;
   if k mod 3 eq 2 then
      mu_k := -1/3;
   elif k mod 3 eq 0 then
      mu_k := 1/3;
   end if;

   function lambda(r,s,p)
     if 2*s le r then
         if IsEven(r) then
            return p^(r div 2) + p^((r div 2)-1);
         else
            return 2*p^((r-1) div 2);
         end if;
      else
         return 2*p^(r-s);
      end if;
   end function;

   K := BaseRing(eps);

   return
     -(1/2)  *  &*[lambda(facN[i][2],facf[i][2],facN[i][1]) 
                  : i in [1..#facN]]
     +gamma_k * &*[K | CO_delta(facN[i][2],facN[i][1],N,eps) : i in [1..#facN]]
     +mu_k    * &*[K | CO_nu(   facN[i][2],facN[i][1],N,eps) : i in [1..#facN]];

end function;


function XXXCohenOesterle(eps, k)
   N    := Modulus(eps);   
   facN := Factorization(N); 
   f    := Conductor(eps); 
   facf := [<p,Valuation(f,p)> : p in [q[1] : q in facN]];
   
   gamma_k := 0;
   if k mod 4 eq 2 then
      gamma_k := -1/4;
   elif k mod 4 eq 0 then
      gamma_k := 1/4;
   end if;
   mu_k := 0;
   if k mod 3 eq 2 then
      mu_k := -1/3;
   elif k mod 3 eq 0 then
      mu_k := 1/3;
   end if;

   function lambda(r,s,p)
     if 2*s le r then
         if IsEven(r) then
            return p^(r div 2) + p^((r div 2)-1);
         else
            return 2*p^((r-1) div 2);
         end if;
      else
         return 2*p^(r-s);
      end if;
   end function;

   K := BaseRing(eps);

   return
     -(1/2)  *  &*[lambda(facN[i][2],facf[i][2],facN[i][1]) 
                  : i in [1..#facN]]
     +gamma_k * &+[K|Evaluate(eps,x) : x in Integers(N) | x^2+1 eq 0]
     +mu_k    * &+[K|Evaluate(eps,x) : x in Integers(N) | x^2+x+1 eq 0];

end function;




intrinsic DimensionCuspForms(eps::GrpDrchElt, k::RngIntElt) -> RngElt
{Compute the dimension of the space of cusp forms of weight k and
character eps.}
   require Characteristic(BaseRing(eps)) eq 0 :
      "The base ring of argument 1 must be of characteristic 0.";
   requirege k,2;
   N := Modulus(eps);
   if IsTrivial(eps) then
      return S0(N,k);
   end if;
   if (IsOdd(eps) and IsEven(k)) or (IsEven(eps) and IsOdd(k)) then
      return 0;
   end if;
   ans := idxG0(N) * (k-1)/12 + CohenOesterle(eps,k);
   if Type(ans) in {FldRatElt, FldCycElt} then
      return Integers()!ans;
   end if;
   return ans;
end intrinsic;


intrinsic DimensionCuspFormsGamma0(N::RngIntElt, k::RngIntElt) -> RngIntElt
{The dimension of S_k(Gamma_0(N)).}
   if k eq 0 then 
      return 0;
   end if;
   requirege k,2;
   return DimensionCuspForms(DirichletGroup(N)!1, k);
end intrinsic;


intrinsic DimensionCuspFormsGamma1(N::RngIntElt, k::RngIntElt) -> RngIntElt
{The dimension of S_k(Gamma_1(N)).}
   if k eq 0 then 
      return 0;
   end if;
   requirege k,2;
   return S1(N,k);
end intrinsic;


function mumu(N)
   if Type(N) ne RngIntElt or N lt 1 then
      error "mumu(N): N must be a positive integer.";
   end if;
   p := 1;
   m := Factorization(N);
   for m in Factorization(N) do
      if m[2] gt 2 then 
         p := 0 ;
      elif m[2] eq 1 then
         p := -2*p;
      end if;
   end for;
   return p;
end function;


intrinsic DimensionNewCuspFormsGamma0(N::RngIntElt, k::RngIntElt) -> RngIntElt
{The dimension of the new subspace of S_k(Gamma_0(N)).}
   if k eq 0 then 
      return 0;
   end if;
   requirege k,2;
   return &+[DimensionCuspFormsGamma0(M,k)*mumu(N div M) : M in Divisors(N)];
end intrinsic;


intrinsic DimensionNewCuspFormsGamma0(N::RngIntElt, k::RngIntElt, p::RngIntElt) -> RngIntElt
{The dimension of the p-new subspace of S_k(Gamma_0(N)).}
   if k eq 0 then 
      return 0;
   end if;
   requirege k,2;
   require p eq 0 or IsPrime(p) : "Argument 3 must be prime or 0.";
   if p eq 0 then return 
      DimensionNewCuspFormsGamma0(N,k);
   end if;
   if N mod p ne 0 then
      return DimensionCuspFormsGamma0(N,k);
   end if;
   return DimensionCuspFormsGamma0(N,k) - 2*DimensionCuspFormsGamma0(N div p, k);
end intrinsic;


intrinsic DimensionNewCuspFormsGamma1(N::RngIntElt, k::RngIntElt) -> RngIntElt
{Compute the dimension of the new subspace of S_k(Gamma_0(N)).}
   if k eq 0 then 
      return 0;
   end if;
   requirege k,2;
   return &+[DimensionCuspFormsGamma1(M,k)*mumu(N div M) : M in Divisors(N)];
end intrinsic;


intrinsic DimensionNewCuspFormsGamma1(N::RngIntElt, k::RngIntElt, p::RngIntElt) -> RngIntElt
{The dimension of the p-new subspace of S_k(Gamma_1(N)).}
   if k eq 0 then 
      return 0;
   end if;
   requirege k,2;
   require p eq 0 or IsPrime(p) : "Argument 3 must be prime or 0.";
   if p eq 0 then return 
      DimensionNewCuspFormsGamma1(N,k);
   end if;
   if N mod p ne 0 then
      return DimensionCuspFormsGamma1(N,k);
   end if;
   return DimensionCuspFormsGamma1(N,k) - 2*DimensionCuspFormsGamma1(N div p, k);
end intrinsic;

intrinsic DimensionNewCuspForms(eps::GrpDrchElt, k::RngIntElt) -> RngElt
{Compute the dimension of the new subspace of cusp forms of weight k and
 character eps.}
   require Characteristic(BaseRing(eps)) eq 0 :
      "The base ring of argument 1 must be of characteristic 0.";
   requirege k,2;
   N := Modulus(eps);
   D := [Conductor(eps)*d : d in Divisors(N div Conductor(eps))];
   return &+[DimensionCuspForms(Restrict(eps,M), k)
                *mumu(N div M) : M in D];
end intrinsic;

intrinsic DimensionNewCuspForms(eps::GrpDrchElt, k::RngIntElt, p::RngIntElt) -> RngElt
{Compute the dimension of the p-new subspace of cusp forms of weight k and
 character eps.}
   require Characteristic(BaseRing(eps)) eq 0 :
      "The base ring of argument 1 must be of characteristic 0.";
   requirege k,2;
   require p eq 0 or IsPrime(p) : "Argument 3 must be prime or 0.";
   if p eq 0 then return 
      DimensionNewCuspForms(eps,k);
   end if;
   all := DimensionCuspForms(eps,k);
   if Modulus(eps) mod p ne 0 then  // no p-old forms.
      return all;
   end if;
   if Valuation(Conductor(eps),p) eq Valuation(Modulus(eps),p) then
      return all;                  // also no p-old forms
   end if;
   eps_p := Restrict(eps,Modulus(eps) div p);
   old := DimensionCuspForms(eps_p,k);
   return all - 2*old;
end intrinsic;

////////////////////// END dims.m ////////////////////////////
