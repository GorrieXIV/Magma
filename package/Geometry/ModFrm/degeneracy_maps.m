freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: degeneracy_maps.m

   $Header: /home/was/magma/packages/modform/code/RCS/degeneracy_maps.m,v 1.3 2001/05/30 18:54:29 was Exp $

   $Log: degeneracy_maps.m,v $
   Revision 1.3  2001/05/30 18:54:29  was
   Created.

   Revision 1.2  2001/05/16 04:11:55  was
   *** empty log message ***

   Revision 1.1  2001/05/16 03:51:46  was
   Initial revision

      
 ***************************************************************************/

/*
intrinsic DegeneracyMap(M1::ModFrm, M2::ModFrm, 
                         d::RngIntElt) -> Map
{The degneracy map M_1 ---> M_2 associated to d. 
Let N_i be the level of M_i for i=1,2. Suppose that d 
is a divisor of either the numerator or denominator of 
the rational number N_1/N_2, written in reduced form. 
If N_1 divides N_2, then this intrinsic returns 
alpha_d : M_1 ---> M_2, or if N_2 divides N_1, then this
intrinsic returns beta_d : M_1 ---> M_2.  It is an error if
neither divisibility holds.
}

   require Weight(M1) eq Weight(M2) : 
         "The weight of argument 1 must equal weight of argument 2.";
   assert false;
   error "DegeneracyMap -- Not programmed.";
end intrinsic;


intrinsic DegeneracyMatrix(M1::ModFrm, M2::ModFrm, 
                            d::RngIntElt) -> AlgMatElt
{The matrix of DegeneracyMap(M1,M2,d) with respect to Basis(M1) and
 Basis(M2).  Both IsAmbient(M1) and IsAmbient(M2) must be true.}
   assert false;
   error "DegeneracyMatrix -- Not programmed.";
end intrinsic;
*/

