freeze;

//$Id:: order.m 1112 2008-10-14 02:53:47Z jbaa004                            $:

/* multiplicative upper bound for order of x */

MultiplicativeUpperbound := function (x)
   F := BaseRing (Parent (x));
   p := Characteristic (F);
   q := #F;
   m := MinimalPolynomial (x);
   facs := Factorisation (m);
   degs := [Degree (facs[i][1]): i in [1..#facs]];
   alpha := Maximum ([facs[i][2]: i in [1..#facs]]);
   beta := Ceiling (Log (p, alpha));
   bound := LCM ([q^i - 1: i in degs]) * p^beta;
   return bound;
end function;

/* obtain an upper bound for the order of x as 2^k * odd,
   where the power k of 2 in the factorisation is correct; 
   c^(o * bound) is the identity, o = 2^k and y = c^bound 
   bound is odd */ 

EstimateOrder := function (x)
   bound := MultiplicativeUpperbound (x);
   /* largest odd divisor of upper bound */
   k := 0; while bound mod 2 eq 0 do k +:= 1; bound div:= 2; end while;
   /* obtain element of even order by powering up odd part */
   if k gt 0 then y := x^bound; else y := x^0; end if;
   o := Order (y);
   return bound * o, y, o, bound;
end function;

/* can we obtain an involution which is a power of x? 
   if degree and field is large, then powering up odd 
   part of x and computing order of resulting 2-power element 
   is faster than computing the order of x */

InvolutionIsPower := function (x: w := [])
   // "method 1";

   bound := MultiplicativeUpperbound (x);
   /* largest odd divisor of upper bound */
   while bound mod 2 eq 0 do bound div:= 2; end while;

   /* obtain element of even order by powering up odd part */
   y := x^bound;
   o := Order (y);
   if IsEven (o) then
      y := y^(o div 2);
      if not (w cmpeq []) then 
         w := w^bound; w := w^(o div 2); return true, y, w;
      end if;
      return true, y, _;
   else
      return false, _, _;
   end if;
end function;

OrderToInvolution := function (y: w := [])
    // "method 2";
   o := Order (y: Proof := false);
   if IsEven (o) then
      o := o div 2;
      y := y^(o);
      if not (w cmpeq []) then 
         w := w^(o); return true, y, w;
      end if;
      return true, y, _;
   else
      return false, _, _;
   end if;
end function;

GenerateInvolution := function (G: Words := true)
   
   if Words cmpeq true then 
      x, w := RandomWord (G);
   else 
      x := Random (G);
      w := [];
   end if;

   F := BaseRing (G);
   p := Characteristic (F);
   e := Degree (F);
   d := Degree (G);

   if   d ge 20 and p ge  5 and e ge 1 then return InvolutionIsPower (x: w := w);
   elif d ge 13 and p ge 11 and e ge 2 then return InvolutionIsPower (x: w := w);
   elif d ge  9 and p ge 11 and e ge 4 then return InvolutionIsPower (x: w := w);
   elif d ge  5 and p ge 11 and e ge 4 then return InvolutionIsPower (x: w := w);
   elif d eq  4 and p ge 11 and e ge 7 then return InvolutionIsPower (x: w := w);
   elif d eq  3 and p ge 11 and e ge 9 then return InvolutionIsPower (x: w := w);
   elif d ge  4 and p eq  7 and e ge 8 then return InvolutionIsPower (x: w := w);
   elif d ge  4 and p eq  5 and e ge 8 then return InvolutionIsPower (x: w := w);
   elif d ge  4 and p eq  3 and e ge 10 then return InvolutionIsPower (x: w := w);
   else return OrderToInvolution (x : w := w); end if;
end function;


/* 
Nmr := 100;
p := 7;
repeat 
for i in [10..12 by 1] do
   for d in [2 .. 20 by 1] do 
      F := GF (p^i);
      G := SL (d, F);
//      "d = ", d, "p = ", p, "i = ", i; 
//      "==============================";
      result := 0;
      for k in [1..Nmr] do 
      x := Random (G);
      y := x;
      t := Cputime ();
      a := IsPowerInvolution (x);
      t1 := Cputime (t);
      delete x;
      t := Cputime ();
      b := Test2 (y);
      t2 := Cputime (t);
      result +:= t1 - t2;
      end for;
      // "Smaller? ", t1, t2, t1 le t2, t2 - t1; 
    if result gt 0 then 
      "d = ", d, "p = ", p, "i = ", i; "result ", result;
      "==============================";
       end if;
   end for;
end for;
p := NextPrime (p);
until p gt 7;
*/
