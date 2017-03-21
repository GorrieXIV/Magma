freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: qexp_mappings.m

   $Header: /home/was/magma/packages/modform/code/RCS/qexp_mappings.m,v 1.2 2001/11/10 18:49:06 was Exp $

   $Log: qexp_mappings.m,v $
   Revision 1.2  2001/11/10 18:49:06  was
   Changed from SeqEnum to List in orbits of maps, because Magma V2.8-3 now
   pronounces my use of SeqEnum in this case an error (it didn't used to).   -- WAS

   Revision 1.1  2001/05/30 18:56:50  was
   Initial revision


      
 ***************************************************************************/


import "misc.m" : ToLowerCaseLetter;


function MapFromNumberField(K, root)
   R := PolynomialRing(Rationals());
   L := Parent(root);
   phi := hom< K -> R | x :-> R!Eltseq(x) >;
   psi := hom< R -> L | root>;
   return hom< K -> L | x :-> psi(phi(x))>;
end function;


function ComputeComplexMaps(f)
   R := BaseRing(Parent(PowerSeries(f,2)));
   L := ComplexField();

   if Type(R) in {FldRat, RngInt} then
      return [* [hom<R -> L | x :-> L!x>] *];
   end if;

   assert Type(R) in {FldNum, FldCyc};

   h := PolynomialRing(L)!DefiningPolynomial(R);

   orb := [];
   for root in Roots(h) do
//      for i in [1..root[2]] do
         Append(~orb, MapFromNumberField(R, root[1]));   
//      end for;
   end for;
   return [* orb *];  

end function;

function ComputepAdicMaps(f, p)
   assert Type(f) eq ModFrmElt;
   R := BaseRing(Parent(PowerSeries(f,2)));
   L := pAdicField(p);

   if Type(R) in {FldRat, RngInt} then
      return [* [hom<R -> L | x :-> L!x>] *];
   end if;

   assert Type(R) in {FldNum, FldCyc}; 

   h := PolynomialRing(L)!DefiningPolynomial(R);

   // Now we distribute the corresponding maps to the conjugates in the orb.
   ans := [* *];
   j := 1;
   for F in Factorization(h) do
      orb := [* *];
//      for n in [1..F[2]] do
         if Degree(F[1]) eq 1 then
            Append(~orb, MapFromNumberField(R, -Evaluate(F[1],0)));
         else
            S := PolynomialRing(L);
            for i in [1..Degree(F[1])] do 
               T := quo<S|F[1]>; 
               AssignNames(~T,[ToLowerCaseLetter(j)]);
               j +:= 1;
               phi := MapFromNumberField(R, T.1);      
               Append(~orb, phi);
            end for; 
         end if;
//      end for;
      Append(~ans,orb);
   end for;
   return ans;
end function;

function ComputeModpMapsUsingMaximalOrder(f, p)
   assert Type(p) eq RngIntElt;
   assert IsPrime(p) and p gt 0;
   assert Type(f) eq ModFrmElt;

   R := BaseRing(Parent(PowerSeries(f)));
   assert Type(R) in {FldNum, FldCyc};
   L := GF(p) ;

   vprint ModularForms : 
           "Ramification in a degree "*IntegerToString(Degree(R))*
            " extension, so we use slower method to compute mod-"*IntegerToString(p)*" reductions.";

   O := MaximalOrder(R);      
   I := ideal<O|p>;
   ans := [* *];
   which := 1;
   for F in Factorization(I) do
      orb := [ ];
      k, phi := ResidueClassField(O, F[1]);  
      ord_embed := hom<R -> Domain(phi) | x :-> Domain(phi)!x>;
      kk := GF(#k);
      if not IsCoercible(kk,k.1) then   // first time to choose an embedding.
         Embed(k,kk);
      end if;
      embed := hom<k->kk | x :-> kk!x>;
      for i in [0..Degree(k)-1] do
            frob_i := hom<kk -> kk | x :-> x^(p^i)>;
            comp := ord_embed*phi*embed*frob_i;
            Append(~orb, comp);
      end for;   
      Append(~ans,orb);
   end for;
   return ans;
end function;


function ComputeModpMaps(f, p)
   R := BaseRing(Parent(PowerSeries(f,2)));
   L := GF(p);

   if Type(R) in {FldRat, RngInt} then
      return [* [hom<R -> L | x :-> L!x>] *];
   end if;

   assert Type(R) in {FldNum, FldCyc};

   h := DefiningPolynomial(R);
   if not IsEisensteinSeries(f) then    // use maximal order if Z[x]/(h) is not p-maximal in O_R.
      disc_h := Discriminant(h);
      if (Integers()!disc_h) mod p eq 0 and
           (Integers()!(disc_h/Discriminant(MaximalOrder(R))) mod p eq 0) then
         return ComputeModpMapsUsingMaximalOrder(f, p);
      end if;
   end if;

   ans := [* *];
   for F in Factorization(PolynomialRing(L)!h) do
      orb := [];
      k := GF(p^Degree(F[1]));
      for linear in Factorization(PolynomialRing(k)!F[1]) do
//         for i in [1..F[2]] do   // count with multiplicities.
            assert Degree(linear[1]) eq 1;
            root := -Evaluate(linear[1],0);
            Append(~orb, MapFromNumberField(R, root));
//         end for;
      end for;
      Append(~ans, orb);
   end for;
   return ans;
end function;

function ModpReductionMaps(f, p) 
   assert Type(f) eq ModFrmElt;
   assert Type(p) eq RngIntElt;
   assert p gt 0 and IsPrime(p);
   return ComputeModpMaps(f,p);
end function;


function pAdicEmbeddingMaps(f, p)
   assert Type(f) eq ModFrmElt;
   assert Type(p) eq RngIntElt;
   assert p gt 0 and IsPrime(p);
   return ComputepAdicMaps(f,p);
end function;

function ComplexEmbeddingMaps(f)
   assert Type(f) eq ModFrmElt;
   return ComputeComplexMaps(f);
end function;
