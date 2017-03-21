freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                          
                  HECKE:  Modular Symbols in Magma                        
                           William A. Stein                               
                                                                         
  FILE: derivative.m (derivatives of L-series)                             

  $Header: /home/was/magma/modsym/RCS/derivative.m,v 1.4 2001/05/25 04:23:49 was Exp $

  $Log: derivative.m,v $
  Revision 1.4  2001/05/25 04:23:49  was
  fixed typo in comment.

  Revision 1.3  2001/05/13 03:48:05  was
  Changed verbose flag ModularForms to ModularSymbols.

  Revision 1.2  2001/04/24 06:06:26  was
  Fixed comment.

  Revision 1.1  2001/04/20 04:46:19  was
  Initial revision

  Revision 1.2  2000/06/03 04:50:15  was
  Changed verbose ModularForm flag to ModularForms

  Revision 1.1  2000/05/02 07:59:48  was
  Initial revision


                                                                          
 ***************************************************************************/


import "analytic.m"  : DefaultPrec,
                       EULER, 
                       PI;

import "operators.m" : AtkinLehnerSign;
import "arith.m" : GetModulus;


// This code for DerivGr is ported directly from Cremona's C++ package.

function is_approx_zero(x) 
   return Abs(x) lt 10^(-10);
end function;


function DerivG1(x)
//Compute the G_1 function defined in section 2.13 of Cremona's
// Algorithms book.}
   if x gt 708 then   // it's what John does...
      return 0;
   end if;
   if x lt 2 then
      ans := -Log(x) - EULER;
      p   := -1;
      if GetVerbose("ModularSymbols") ge 2 then
         printf "Computing DerivG1 for x = %o using series\n",x;
      end if;
      ok  := 0;
      // The following does not work for large x!  (The terms get too big 
      // before they get small, and overflow destroys the result.)
      for n in [1..5000] do 
         p   /:=  n ; 
         p   *:= -x ;
         term := p/n;
         ans +:= term;
         if is_approx_zero(term/ans) then
            break;
         end if;
      end for;
      return ans;
   else
      //  else  x>2, use continued fraction form from B-G-Z p.478,
      //  or section 2.13 of Cremona.
      if GetVerbose("ModularSymbols") ge 2 then
         printf "Computing DeriveG1 for x = %o using continued fraction\n",x;
      end if;
      a0 := 0.0;
      b0 := 1.0; 
      b1 := x;
      ans:= 0.0;
      a1 := Exp(-x);
      for k in [2..20000] do
         if IsOdd(k) then 
            ca := Floor((k-1)/2);
            a2 := x*a1+ca*a0; 
            a0 := a1; 
            a1 := a2;
            b2 := x*b1+ca*b0; 
            b0 := b1; 
            b1 := b2;
         else 
            ca := Floor(k/2);
            a2 := a1+ca*a0; 
            a0 := a1; 
            a1 := a2;
            b2 := b1+ca*b0; 
            b0 := b1; 
            b1 := b2;
         end if;
         newans := a2/b2;
         if is_approx_zero(ans-newans) then
             return newans;
         end if;
         ans:=newans;
      end for;
   end if;
   "In function g1, continued fraction method, reached end of loop!";
   return 0;
end function;


function DerivG2(x) 
//{Compute the G_2 function defined in section 2.13 of Cremona's
// Algorithms book.}
   if (x gt 20) then
      return 0;
   end if;
   ans := -Log(x) - EULER;
   vprintf ModularSymbols, 2: "Computing myg2 for x = ",x;
   ans := ans*ans/2 + Pi(RealField())*Pi(RealField())/12;
   p   := 1;
   for n in [1..500] do
      p   /:=  n ;  
      p   *:= -x ;
      term := (p/n)/n;
      ans +:= term;
      if is_approx_zero(term/ans) then
         return ans;
      end if;
   end for;
   "In function g2, reached end of loop!";
   return ans;
end function;


function DerivG3(x)
//{Compute the G_3 function defined in section 2.13 of Cremona's
// Algorithms book.}
   if (x gt 20) then
      return 0;
   end if;
   ans := -Log(x) - EULER;
   if GetVerbose("ModularSymbols") ge 2 then
      "Computing myg3 for x = ",x;
   end if;
   ans := (Pi(RealField())^2 + 2*ans^2) * ans/12 - 1.20205690315959428540/3;
   p   := -1;
   for n in [1..500] do
      p   *:= -x/n;
      term := p/(n^3);
      ans +:= term;
      if is_approx_zero(term/ans) then
         return ans;
      end if;
   end for;
   "In function g3, reached end of loop!";
   return ans;
end function;


function DerivWt2(f, N, r) 
//{Compute (d!)*Prod L^(dr)(fi,1) over the d Galois conjugates of f.
//TODO: When both r > 1 and d>1 the normalization is wrong!
//   It's trivial combinatoric to work out but I have not done it.}
   assert r ge 0;
   assert N ge 1;
   // Essentially, we use the formula in Proposition 2.13.1 of [Cr].
   case r:
      when 1: Gr := DerivG1;
      when 2: Gr := DerivG2;
      when 3: Gr := DerivG3;
      else: 
        error "DerivWt2: r must be 1,2, or 3.";
   end case;
   rootN := Sqrt(N);

   G := [Gr(2*PI*n/rootN) : n in [1..Degree(f)]];
   Q      := BaseRing(Parent(f));
   if Type(Q) ne FldRat then
      PC := PolynomialRing(ComplexField()); a := PC.1;
      g      := GetModulus(Q);
      d      := Degree(g);
      if r gt 1 and d gt 1 then
         "DerivWt2 -- WARNING: the normalization is wrong.";
      end if;
      roots  := Roots(PC!g);         // find all conjugates of eigen...
      assert #roots eq Degree(g);   // g must be square free!
      ans := &*[ 
        &+[Evaluate(PC!Eltseq(Coefficient(f,n))/n,roots[j][1]) * G[n] 
             : n in [1..Degree(f)]]
             : j in [1..#roots]];
      ans *:= Factorial(d)*2^d*Factorial(r)^d;
   else 
      ans := 2*Factorial(r)*
          &+[Coefficient(f,n)/n * G[n] : n in [1..Degree(f)]];
   end if;
   return ans;
end function;



function ComputeSpecialValueAndRankWt2(A,n)
   f := qEigenform(A,n);
   N := Level(A);
   e := AtkinLehnerSign(A);
   if e eq -1 and LRatio(A,1) ne 0 then
      return LSeries(A,1,n), 0;
   end if;
   if e eq 1 then
      a := DerivWt2(f,N,1);
      if Abs(a) gt 10^(-3) then
         return a, 1;
      end if;
      if IsVerbose("ModularSymbols") then
         "L'(A,1) ~ ", a, " hence computing second derivative.";
      end if;
   end if;
   if e eq -1 then
      a := DerivWt2(f,N,2);
      if Abs(a) gt 10^(-3) then
         return a, 2;
      end if;
      if IsVerbose("ModularSymbols") then
         "L''(A,1) ~ ", a, " hence computing second derivative.";
      end if;
   end if;
   if e eq 1 then
      a := DerivWt2(f,N,3);
      if Abs(a) gt 10^(-3) then
         return a, 3;
      end if;
      if IsVerbose("ModularSymbols") then
        "WARNING: L'''(A,1) ~ ", a, " even looks zero!  Giving up.";
      end if;
   end if;
   error "ERROR: not able to determine rank.";
   return a, -1;
end function;


/*intrinsic LSeriesLeadingCoefficient(A::ModSym) -> FldComElt
{}
   return LSeriesLeadingCoefficient(A,1,DefaultPrec(A));
end intrinsic;


intrinsic LSeriesLeadingCoefficient(A::ModSym, n::RngIntElt) -> FldComElt
{}
   return LSeriesLeadingCoefficient(A,1,n);
end intrinsic;
*/


intrinsic LSeriesLeadingCoefficient(M::ModSym, j::RngIntElt, 
                                    prec::RngIntElt) -> FldComElt, RngIntElt
{The leading coefficient of Taylor expansion about the critical
 point j and the order of vanishing of L(M,s) at s=j.}
   require IsTrivial(DirichletCharacter(M)) : 
          "At present, the character of argument 1 must be trivial.";
   require Weight(M) eq 2 :
          "At present, the weight of argument 1 must be 2.";
   require 1 le j and j le Weight(M)-1 :
          "Argument 2 must lie between 1 and the weight of argument 1 minus one.";

   if IsTrivial(DirichletCharacter(M)) and Weight(M) eq 2 then
      Lval, r := ComputeSpecialValueAndRankWt2(M,prec);
      return Lval/Factorial(r*DimensionComplexTorus(M)), r;
   end if;
end intrinsic;


