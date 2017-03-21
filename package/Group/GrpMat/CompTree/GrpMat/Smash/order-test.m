freeze;

import "numbers.m": PrimePowers;
import "numbers.m": LcmSeq;
import "functions.m": BlockNumbers;
import "functions.m": SetBlockNumbers;

/* compute exponent of GL (d, q)  */

ExponentGL := function (d, q) 

   n := PrimePowers (q - 1);
   for i in [2..d] do
      n := LcmSeq (n, PrimePowers (q^i - 1));
   end for;

   p := PrimePowers (q)[1];
   t := 1;
   pow := p;

   while (pow lt d) do
      pow *:= p;
      t +:= 1;
   end while;
   
   ExpSeq := [p, t] cat n;

   return ExpSeq;

end function;

/* is ElementOrder a valid order for an element in Symmetric (r)? 
   an element of order p1^n1 * p2^n2 * ... * pk^nk needs at least 
   p1^n1 + p2^n2 + ... + pk^nk points */

IsValidSymOrder := function (ElementOrder, r) 
   
   S := Factorisation (ElementOrder);
   T := [S[i][1]^S[i][2] : i in [1..#S]];
   total := (#T gt 0) select &+T else 0;

   return total le r;

end function;

/* compute the gcd of the order of the element 
   and the exponent of GL(d, q) */

GcdOrderGL := function (d, q, ElementOrder)
   
   Factors := PrimeBasis (ElementOrder);

   Char := Factorisation (q)[1][1];

   Result := 1;
   for p in Factors do 
      if p ne Char then 
         i := 1;
         while (Order (q, p^i) le d) and (ElementOrder mod p^i eq 0) do
            i +:= 1;
         end while; 
         Result := Result * p^(i - 1);
      else
         power := 1;
         while (power lt p * d) and (ElementOrder mod power eq 0) do
            power *:= p;
         end while;
         Result *:= (power div p);
      end if;
   end for;
   
   return Result;

end function;

/* given element in GL(d, q) of order ElementOrder; 
   if ElementOrder divides exponent of GL(s,q) wr Sym(r), 
   return true, else false */

IsOrderValid := function (d, q, r, ElementOrder)

   /* compute the gcd of the order of the element and the 
      exponent of GL (d/r, q) */
   matord := GcdOrderGL (d div r, q, ElementOrder);
   //vprint Smash: "value of matorder is ", matord;

   permord := ElementOrder div matord;
   // vprint Smash: "value of permorder is ", permord;

   return IsValidSymOrder (permord, r);

end function;

/* does an element of this Order eliminate any of the 
   possible block sizes? */

procedure OrderOfElement (M, ElementOrder)
 
   if ElementOrder eq 1 then return; end if;

   d, F := BasicParameters (M);
   q := #F;

   NmrOfBlocks := BlockNumbers (M);

   for r in NmrOfBlocks do
      vprint Smash: "r is ", r;
      if IsOrderValid (d, q, r, ElementOrder) eq false then 
         Exclude (~NmrOfBlocks, r);
      end if;
   end for; 

   SetBlockNumbers (M, NmrOfBlocks); 

end procedure;
