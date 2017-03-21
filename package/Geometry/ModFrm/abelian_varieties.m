freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: abelian_varieties.m 

   $Header: /home/was/magma/packages/ModFrm/code/RCS/abelian_varieties.m,v 1.3 2002/08/26 20:11:25 was Exp was $

   $Log: abelian_varieties.m,v $
   Revision 1.3  2002/08/26 20:11:25  was
   Use MF_NewformModularSymbols.

   Revision 1.2  2002/01/18 06:56:13  was
   Added a function!

   Revision 1.1  2001/05/16 03:50:33  was
   Initial revision

      
 ***************************************************************************/

import "modular_symbols.m" : MF_NewformModularSymbols;

intrinsic TorsionBound(f::ModFrmElt, n::RngIntElt) -> RngIntElt
{A bound on the size of the rational torsion subgroup of the
associated abelian variety A_f obtained by looking at the first n good odd primes.} 

   require IsNewform(f) : "Argument 1 must be a newform.";
   require assigned f`mf_modular_symbols : "Associated space of modular symbols not known.";
   A := MF_NewformModularSymbols(f);
   eps := DirichletCharacter(f);
   orders := [Integers()!Norm(Evaluate(
             CharacteristicPolynomial(DualHeckeOperator(A,p)), 
                             1 + Evaluate(eps,p)*p)) : p in [3..n] |
                             IsPrime(p) and Level(f) mod p ne 0];
   return GCD(orders);
end intrinsic;

/* Example:
function J1tor(p, n) 
   S := CuspidalSubspace(ModularForms(Gamma1(p)));
   ans := 1;
   for i in [1..NumberOfNewformClasses(S)] do
      f := Newform(S,i);
      ans := ans*TorsionBound(f,n);
   end for;
   return ans;
end function;
   
 for p in P do j:=J1tor(p,17); p, j, factor(j); end for;
13 19                     [ <19, 1> ]
17 584                    [ <2, 3>, <73, 1> ]
19 4383                   [ <3, 2>, <487, 1> ]
23 9406793                [ <11, 1>, <23, 1>, <37181, 1> ]
29 65973497856            [ <2, 12>, <3, 1>, <7, 1>, <43, 1>, <17837, 1> ]
31 549578344700           [ <2, 2>, <5, 2>, <7, 1>, <11, 1>, <31, 1>, <2302381, 1> ]
37 160516686697605        [ <3, 2>, <5, 1>, <7, 1>, <19, 1>, <37, 1>, <73, 1>, <577, 1>, <17209, 1> ]
41 107768799408099440     [ <2, 4>, <5, 1>, <13, 1>, <31, 2>, <431, 1>, <250183721,1> ]
43 3127105065969759812    [ <2, 2>, <7, 1>, <19, 1>, <29, 1>, <463, 1>, <1051, 1>, <416532733, 1> ]
47 3279937688802933030787 [ <23, 1>, <139, 1>, <82397087, 1>, <12451196833, 1> ]

(These are orders of congruences between cuspidal and eisenstein subspaces.)
*/
