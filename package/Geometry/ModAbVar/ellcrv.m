freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: ellcrv.m
   DESC: Functors with category of elliptic curves
      
 ***************************************************************************/

/*
HANDBOOK_TITLE: Elliptic curves 

*/

import "homology.m":
   Create_ModAbVarHomol_Subspace;

import "modabvar.m":
   Create_ModAbVar,
   Create_ModAbVar_AssociatedToModularSymbolsSubspace,
   Verbose;

import "rings.m":
   QQ;

forward
   GetModularSymbols;

/***************************************************************************

  << Creation >>


 ***************************************************************************/

intrinsic EllipticCurve(A::ModAbVar) -> CrvEll
{An elliptic curve isogenous to the modular abelian variety
A over the rational field, if there is an elliptic curve associated to A.}
   require Dimension(A) eq 1 : "Argument 1 must have dimension 1.";
   require Weights(A) eq {2} : "Argument 1 must have weight 2.";
   require BaseRing(A) cmpeq QQ : "Argument 1 must be defined over the rational field.";
   M := GetModularSymbols(A);
   return EllipticCurve(M);
end intrinsic;

intrinsic ModularAbelianVariety(E::CrvEll : Sign := 0) -> ModAbVar
{A modular abelian variety isogenous to E.  }
   Verbose("ModularAbelianVariety", 
    Sprintf("Computing modular abelian variety attached to E=%o.",E),
    Sprintf("Sign = %o", Sign));
   require BaseRing(E) cmpeq QQ : "Argument 1 must be defined over Q.";
   require Sign in {0, -1, +1 } : "Sign must be 0, 1, or -1.";

   label := CremonaReference(E);
   if label cmpeq false then
      name := "";
   else
      j := #label;
      while j gt 0 and StringToCode(label[j]) ge 48 and StringToCode(label[j]) le 57 do
         j -:= 1;
      end while;
      label := &*[label[i] : i in [1..j]];
      name := Sprintf("'Cremona %o'",label);
   end if;
   M := ModularSymbols(E,Sign);
   return Create_ModAbVar_AssociatedToModularSymbolsSubspace(name, M);

end intrinsic;

/***************************************************************************

  << Invariants >> 

 ***************************************************************************/


function GetModularSymbols(A)
   assert Type(A) eq ModAbVar;
   D := Factorization(A);
   Af := D[1][1];
   return ModularSymbols(Af)[1];
end function;


intrinsic EllipticInvariants(A::ModAbVar, n::RngIntElt) -> 
   FldReElt, FldReElt, FldReElt, CrvEll
{Invariants c_4, c_6, j, and an elliptic curve, isogenous
to the one dimensional modular abelian variety A, computed 
using n terms of q-expansion.}
   Verbose("EllipticInvariants", 
      Sprintf("Computing elliptic invariants of A using %o terms, where A=%o.", n,A),"");
   M := GetModularSymbols(A);
   return EllipticInvariants(M, n);
end intrinsic;

intrinsic EllipticPeriods(A::ModAbVar, n::RngIntElt) -> FldReElt, FldReElt
{Elliptic periods w_1 and w_2 of the J_0(N)-optimal
elliptic curve associated to A, computed using n terms 
of the q-expansion.}
   Verbose("EllipticPeriods", 
      Sprintf("Computing elliptic periods of A using %o terms, where A=%o.", n,A),"");
   require Dimension(A) eq 1 : "Argument 1 must have dimension 1.";
   return EllipticPeriods(GetModularSymbols(A),n);
end intrinsic;

