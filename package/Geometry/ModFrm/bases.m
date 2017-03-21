freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: bases.m

   $Header: /home/was/magma/packages/modform/code/RCS/bases.m,v 1.2 2001/05/30 18:53:43 was Exp $

   $Log: bases.m,v $
   Revision 1.2  2001/05/30 18:53:43  was
   Done.

   Revision 1.1  2001/05/16 03:50:44  was
   Initial revision

      
 ***************************************************************************/

intrinsic Basis(M::ModFrm) -> SeqEnum
{The canonical basis of M.}

/*
 if GetPrecision(M) lt Dimension(M)+5 then 
 print "Mark decided to increase the precision for \n", M, "to ", Dimension(M)+5;
 SetPrecision(M, Dimension(M)+5); // MW 1 Feb 2007
 end if;
*/

   if not assigned M`basis then
      V := RSpace(BaseRing(M),Dimension(M));
      M`basis := [M!V.i : i in [1..Dimension(M)]];
   end if;
 
   if assigned M`basis then
      return M`basis;
   end if;
end intrinsic;


intrinsic '.'(M::ModFrm, i::RngIntElt) -> ModFrmElt
{The i-th basis vector of M.}
   requirege i,1;
   require i le Dimension(M) : 
           "Argument 2 can be at most the dimension of argument 1.";
   return Basis(M)[i];
end intrinsic;

