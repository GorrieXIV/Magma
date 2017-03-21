freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: p-adic.m 

   $Header: /home/was/magma/packages/modform/code/RCS/p-adic.m,v 1.2 2001/05/30 18:56:25 was Exp $

   $Log: p-adic.m,v $
   Revision 1.2  2001/05/30 18:56:25  was
   Created.

   Revision 1.1  2001/05/30 04:10:36  was
   Initial revision


      
 ***************************************************************************/



intrinsic Slopes(M::ModFrm : Proof := true) -> SeqEnum
{The slopes of the Newton polygon of the characteristic polynomial f of
the Hecke operator T_p acting on M, where M is defined over pAdicField(p).  
This is a list of the valuations of the p-adic roots of f.}
   require Type(BaseRing(M)) eq FldPad : 
     "The base ring of argument 1 must be a p-adic field.";
   p := Prime(BaseRing(M));
   return ValuationsOfRoots(HeckePolynomial(M,p : Proof := Proof),p);
end intrinsic;


///////////////////////////////////////////////////////////////////
// Newton Polygons                                               //
// Ported from PARI by William Stein  Feb 12, 2000               //
///////////////////////////////////////////////////////////////////
intrinsic NP(f::RngUPolElt, p::RngIntElt) -> List
{The slopes of the Newton polygon of f with at the prime p.  
The slopes are the valuations of the p-adic roots of f.}
   n := Degree(f);
   if n le 0 then
      return [];
   end if;

   y := [* *];
   vval := [* *];
   for i in [0..n] do 
      Append(~vval,Type(Parent(Coefficient(f,0))) in [RngInt,FldRat] select
                       Valuation(Coefficient(f,i),p)
                   else
   		       Valuation(Coefficient(f,i)));
      Append(~y,0);
   end for;

   a := 1; ind := 2; 
   while a le n do
      if vval[a] ne Infinity() then
         break;
      end if;
      y[ind] := Infinity();   
      ind +:= 1;
      a +:= 1;
   end while;

   b := a+1;
   while b le n+1 do
      while vval[b] eq Infinity() do
         b +:= 1;
      end while;
      u1 := vval[a] - vval[b];
      u2 := b - a;
      c := b+1;
      while c le n+1 do
         if vval[c] eq Infinity() then
            c +:= 1;
            continue;
         end if;
         r1 := vval[a] - vval[c];
         r2 := c - a;
         if u1*r2 le u2*r1 then
            u1 := r1;
            u2 := r2;
             b := c;
         end if;
         c +:= 1;
      end while;

      while ind le b do 
         if u1 eq 0 then
            y[ind] := 0;
         else
            y[ind] := u1 / u2; 
         end if;
         ind +:= 1;
      end while;
      a := b;
      b := a+1;
   end while;
   Remove(~y,1);
   z := [* *];
   for i in [1..#y] do
      Append(~z,y[#y-i+1]);
   end for;
   return z;
end intrinsic;
