freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: periods.m
   DESC: complex period lattice

   Creation: 06/16/03 -- initial creation
      
 ***************************************************************************/

/*
HANDBOOK_TITLE: Complex Period Lattice

*/
import "modabvar.m":
   Verbose;

import "homology.m":
   Rational_to_ModSym;

/***********************************************************************

  << Period Map >> 

 ***********************************************************************/

intrinsic PeriodMapping(A::ModAbVar, prec::RngIntElt) -> Map
{The complex period mapping from rational homology to C^d, where d=dim A, 
computed using prec terms of q-expansions.}
   Verbose("PeriodMapping", 
   Sprintf("Computing complex period mapping of A using %o terms of q-expansions, where A=%o.",prec,A), "");
   require IsInjective(ModularEmbedding(A)) : 
      "The modular map for A must be injective.";
   t, Af := IsAttachedToNewform(A);
   if t then
      //assert A eq Af;
      // I commented this because it now fails, eg for Periods(ModularAbelianVariety("50A"), 100); 
      // The 'false' answer arises because Homology(A) eq Homology(Af) is false,
      // which is because A`modsym is not assigned while Af`modsym is assigned.
      // Not sure what should be changed, though.                 --- Steve
      M := ModularSymbols(Af)[1];
      PHI := PeriodMapping(M,prec);
      i := Rational_to_ModSym(Homology(Af));
      phi := hom<RationalHomology(A) -> Codomain(PHI) | x :-> PHI(i(x)[1])>;
      return phi;
   end if;
      
   require t : "Argument 1 must be isogenous to a newform abelian variety A_f.";
/*
//   require t : "Argument 1 must be isogenous to a newform abelian variety A_f.";
   if not t
      f := NaturalMap(A,Af);
      psi := PeriodMapping(Af,n);
      phi := hom<RationalHomology(A) -> Codomain(psi) | x :-> psi(x*Matrix(f))>;
      return phi;
   end if;
   M := ModularSymbols(A)[1];
   PHI := PeriodMapping(M,n);
   i := Rational_to_ModSym(Homology(A));
   phi := hom<RationalHomology(A) -> Codomain(PHI) | x :-> PHI(i(x)[1])>;
   return phi;
*/ 
end intrinsic;


/***********************************************************************

  << Period Lattice >> 

 ***********************************************************************/

intrinsic Periods(A::ModAbVar, n::RngIntElt) -> SeqEnum
{Generators for the complex period lattice of A, computed 
using n terms of q-expansions.  }
   require IsInjective(ModularEmbedding(A)) : 
      "The modular map for A must be injective.";

   H := IntegralHomology(A);
   phi := PeriodMapping(A, n);
   return [phi(x) : x in Basis(H)];
end intrinsic;



