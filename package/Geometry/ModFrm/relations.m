freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: relations.m

   $Header: /home/was/magma/packages/modform/code/RCS/relations.m,v 1.2 2002/04/13 07:26:56 was Exp $

   $Log: relations.m,v $
   Revision 1.2  2002/04/13 07:26:56  was
   *** empty log message ***

   Revision 1.1  2001/05/30 18:57:16  was
   Initial revision

      
 ***************************************************************************/


import "misc.m" : ToLowerCaseLetter;

forward RSpaceElement,
        qRelationsOfDegree;


intrinsic Relations(M::ModFrm, d::RngIntElt, prec::RngIntElt) -> SeqEnum, SeqEnum
{All relations of degree d satisfied by the q-expansions of Basis(M), 
computed to precision prec.}
   require d ge 1 : "Argument 2 must be at least 1.";
   require prec ge 1 : "Argument 3 must be at least 1."; 
   if Dimension(M) eq 0 then
      return [];
   end if;
   return qRelationsOfDegree([PowerSeries(f,prec) : f in Basis(M)],d, prec);
end intrinsic;


function qRelationsOfDegree(B, d, prec) 
// The algebraic relations of degree d satisfied by 
// the sequence X of independent q-expansions

   assert Type(B) eq SeqEnum;
   assert Type(prec) eq RngIntElt;
   assert Type(d) eq RngIntElt;
   assert d ge 1;
   assert prec ge 1;

   S := Parent(B[1]);
   K := BaseRing(S);
   R := PolynomialRing(K,#B);
   AssignNames(~R,[ToLowerCaseLetter(n) : n in [1..#B]]);
   monoms := MonomialsOfDegree(R,d);
   forms  := [&*[B[i]^exp[i] : i in [1..#B]] where exp := Exponents(m) : m in monoms];
   V    := RSpace(K,prec);
   vecs := [RSpaceElement(V,f) : f in forms];
   A := RMatrixSpace(K,#forms,prec)!vecs;
   relvecs := Basis(Kernel(A));
   rels := [&+[v[i]*monoms[i] : i in [1..#monoms]] : v in relvecs];

   return rels, relvecs;
end function;


function RSpaceElement(V, f)
   R<q>:=Parent(f);
   S := [0 : i in [1..Valuation(f)]] cat Eltseq(f+O(q^Degree(V)));
   S := S cat [0 : i in [1..Degree(V)-#S]];
   return V!S;
end function;
