freeze;
 
import "misc.m": EvaluateImage;
import "numbers.m": PrimePowers;
import "functions.m": SetBlockSizes;
import "functions.m": BlockSizes;
import "is-primitive.m": SettleComputation;
import "stabiliser-test.m": BlockStabiliserTest;

/* if p ne char of F find largest power of x^(p^n) - a in f 
   else find Rank ((x - a)^(p^n - 1)) evaluated for TestElement */

FindLargestPower := function (TestElement, p, n, a, ff, F)

   /* the following is a more compact method of storing a polynomial
      than the alternative PA<x> := Parent (f); this is relevant 
      if p^n is large */

   PA<x> := PolynomialAlgebra (BaseRing (Parent (ff))); 
   f := PA!Coefficients (ff);

   ZeroPol := PA![];

   if p ne Characteristic (F) then

     factor := x^(p^n) - a;

      /* find the largest power, t, of x^(p^n) - a which divides f */
      t := -1;
      repeat 
         quotient, remainder := Quotrem (f, factor);
         if remainder eq ZeroPol then 
            f := quotient;
         end if;
         t +:= 1;
      until remainder ne ZeroPol;

      return <t, f>;

   else
      f := (x - a)^(p^n - 1); 

      /* find d - dimension of NS (f(TestElement)) eq rank of f(TestElement) */
      t := Rank (EvaluateImage (f, TestElement));

      return [t];
      
   end if;
      
end function;

/* find largest t such that V contains a free F[C_p] module of rank t */

FreeRank := function (TestElement, p, ff, F)

   PA<x> := PolynomialAlgebra (BaseRing (Parent (ff))); 
   f := PA!Coefficients (ff);

   one := One (F);

   if p ne Characteristic (F) then

      /* find the largest power of x^p - 1 which divides f 
         where f eq (x^p - 1)^t * Residue */

      Result := FindLargestPower (TestElement, p, 1, 1, f, F);
      t := Result[1];
      Residue := Result[2];
      /* vprint Smash: "Residue = ", Residue; */

      /* now check whether Residue is simply (x - 1)^Degree (Residue) */
      factor := (x - one)^Degree (Residue);
      Excess := (factor ne Residue);
      
      return <t, Excess>;

   else

      factor := x - one;

      Result := FindLargestPower (TestElement, p, 1, 1, f, F);
      t := Result[1];

      /* now find height, h, of residue; do this by finding smallest h 
         such that Rank ((x - 1)^h) = t * (p - h) */

      f := factor;
      h := 0;
      repeat 
         rank := Rank (EvaluateImage (f, TestElement));
         f *:= factor;
         h +:= 1;
      until rank eq t * (p - h);

      return <t, h>;
      
   end if;
      
end function;

/* test characteristic polynomial structure of elements of prime order */

procedure CharPolPrimeOrder (M, TestElement, p, ~Queue)
  
   F := BaseRing (M);
   Char := Characteristic (F);

   f := CharacteristicPolynomial (TestElement);

   SizesOfBlocks := BlockSizes (M);

   Result := FreeRank (TestElement, p, f, F);

   t := Result[1];

   if p ne Char then

      Excess := Result[2];
      q := #F;

      /* smallest integer m such that q^m - 1 is divisible by p */
      OrdMod := Order (q, p);
      //vprint Smash: "In CharPolPrimeOrder, p = ", p, " Excess? ", Excess, 
      //           " OrdMod = ", OrdMod, " t = ", t;

      h := 0;
   else 
      h := Result[2];
      Excess := false;
      OrdMod := 0;
      // vprint Smash: "In CharPolPrimeOrder, p = ", p, " t = ", t, " h = ", h;
   end if;

   /* run over and seek to eliminate block sizes; 
      store eliminated block sizes in Remove */

   first := true; Remove := {};

   for s in SizesOfBlocks do 
      if (p ne Char and s lt OrdMod and Excess) or (p eq Char and s lt h) then 
         //vprint Smash: "in first clause for s = ", s;
         Include (~Remove, s);

      elif p eq Char and s lt p and t mod s ne 0 then  	 
         //vprint Smash: "in second clause for s = ", s;
         Include (~Remove, s);

      elif s gt t and first then 
         //vprint Smash: "in third clause for s = ", s;
         Append (~Queue, <TestElement, t>); 
         first := false;
      end if;
   end for;      

   SetBlockSizes (M, SizesOfBlocks diff Remove); 

end procedure;

/* order of TestElement is p^n; 
   test characteristic polynomial structure of elements of prime power order;
   compute projective order, p^m, of TestElement;
   TestElement^(p^m) is scalar in a, say;
   now find largest power, t, of x^(p^m) - a which occurs in char 
   poly of TestElement */

procedure CharPolPrimePowerOrder (M, TestElement, p, n, ~Queue)
  
   F := BaseRing (M);
   SizesOfBlocks := BlockSizes (M);

   f := CharacteristicPolynomial (TestElement);

   /* note both projective order of TestElement and the scalar a */
   order, a := ProjectiveOrder (TestElement);
   o := PrimePowers (order);
   m := o[2];
  
   Result := FindLargestPower (TestElement, p, m, a, f, F);

   t := Result[1];

   //vprint Smash: "In CharPolPrimePowerOrder, p^n = ", p^n, " proj order = ", p^m, 
   //           " scalar = ", a, " t = ", t;

   /* can we eliminate block sizes? */

   if #SizesOfBlocks gt 0 and t lt Maximum (SizesOfBlocks) then 
     /* keep track of element of prime order for possible later processing */
     Append (~Queue, <TestElement^(p^(m - 1)), t>); 
     vprint Smash: "Candidate for Smash";
   end if;
      
end procedure;

/* examine characteristic polynomial of elements of prime-power order which 
   can be obtained as powers of g, an element of order ElementOrder */

procedure CharPolStructure (M, g, ElementOrder, ~Queue)
   
   /* consider elements of prime order */

   factors := PrimeBasis (ElementOrder);

   for p in factors do

      vprint Smash: "Call CharPolPrimeOrder with element of order ", p;

      TestElement := g^(ElementOrder div p);

      if IsScalar (TestElement) eq false then 

         SizesOfBlocks := BlockSizes (M);
         //vprint Smash: "Before call, Blocksizes are ", SizesOfBlocks;

         CharPolPrimeOrder (M, TestElement, p, ~Queue);

         SizesOfBlocks := BlockSizes (M);
         // vprint Smash: "Blocksizes after CharPolPrimeOrder: ", SizesOfBlocks;
         if SettleComputation (M, Queue) then return; end if; 
      else 
         vprint Smash: "Element of order ", p, " is scalar";
      end if;

   end for; 

   /* now consider elements of prime-power order, p^n, where n > 1 */

   powers := PrimePowers (ElementOrder);
   last := #powers div 2;
   for i in [1..last] do 
      
      p := powers[2 * i - 1];
      n := powers[2 * i];

      if n gt 1 then 

         vprint Smash: "Call CharPolPrimePowerOrder with element of order ", p^n;

         TestElement := g^(ElementOrder div p^n);

         if IsScalar (TestElement) eq false then 
            CharPolPrimePowerOrder (M, TestElement, p, n, ~Queue);
            if SettleComputation (M, Queue) then return; end if; 
         else 
            vprint Smash: "Element of order ", p^n, " is scalar";
         end if;

      end if;

   end for; 

end procedure;
