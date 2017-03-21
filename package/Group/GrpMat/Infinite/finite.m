freeze;

import "attributes.m": RF;
import "virtual.m": IsUnipotentClosure;
import "algebra.m": FunctionFieldAlgebraAlgorithm;
import "general.m": HasKnownIsomorphicCopy;
import "congruence.m": PAFFC, PFFC, IsValidInput, MyCongruenceImage;
import "present.m": ConstructPresentation;
import "random.m": NormalClosureRandom;

declare verbose Infinite, 2;

/* evaluate extension degree for G */

ExtensionDegree := function (G)
   K := BaseRing (G);
   n := Degree (G);

   if Characteristic (K) gt 0 then
      if ISA (Type(K), FldFun) then 
         e := Degree (K); 
      elif ISA (Type(K), FldFunRat) then 
         e := 1; 
      else 
         error "ExtensionDegree: Type of K"; 
      end if;
      return n * e;
   end if;

   if ISA (Type(K), FldRat) or ISA (Type (K), RngInt) then 
      return n;
   end if;

   if ISA (Type(K), FldNum) then return n * Degree (K); end if;

   if ISA (Type(K), FldFunRat) then 
      F := BaseRing (K);
      return n * Degree (F);
   end if;

   if ISA (Type(K), FldFun) then 
      L := BaseRing (K);
      F := BaseRing (L);
      return n * Degree (K) * Degree (F);
   end if;
   
   error "Input type incorrect";
end function;

/* p is characteristic of defining field of g, matrix of degree n;
   d = order of congruence image of g;
   if g element of function field, then 
   use algebra algorithm to decide if <g> is finite;
   Power = true: in positive characteristic evaluate g^(d * p^Ceiling (p, n)), 
   otherwise test if g^d is unipotent;

   Limit: if positive and power > Limit, then abort order computation;
   used by IsFinite; 
*/

MyHasFiniteOrder := function (g, d, b, n0, p: Power := false, Limit := 0)
   if d gt b then return false; end if;

   /* always compute g^d if d < SmallPower */
   SmallPower := 100; 

   G := Parent (g);
   K := BaseRing (G);

   if p eq 0 then 
      primes := PrimeBasis (d);
      if exists{r: r in primes | r gt n0 + 1} then return false; end if;
      if ISA (Type(K), FldFunRat) and d gt SmallPower then 
         "Test order of element using Nilpotent code";
         flag := FunctionFieldAlgebraAlgorithm (sub<Generic (G) | g >: 
                                                     Nilpotent := true);
         return flag;
      else 
         if Limit ne 0 and d gt Limit then 
            vprint Infinite: "Power too large -- ignore"; return "unknown"; 
         end if;
         vprint Infinite: "Char 0: Compute power", d;
         return IsIdentity (g^d); 
      end if;
   else 
      if ISA (Type(K), FldFunRat) and d gt SmallPower then 
         vprint Infinite: "Test order using Nilpotent code";
         flag := FunctionFieldAlgebraAlgorithm (sub<Generic (G) | g >: 
                                                     Nilpotent := true);
      elif Power then 
         power := d * p^Ceiling (Log (p, Degree (G)));
         if Limit ne 0 and power gt Limit then 
            vprint Infinite: "Power too large -- ignore"; return "unknown"; 
         end if;
         vprint Infinite: "Compute power", power;
         flag := IsIdentity (g^power);
      else 
         vprint Infinite: "Unipotent test of matrix -- first compute matrix power ", d;
         if Limit ne 0 and d gt Limit then 
            vprint Infinite: "Power too large -- ignore"; return "unknown"; 
         end if;
         flag := IsUnipotent (g^d); 
      end if;
      return flag;
   end if;
end function;

/* order bound of element of G <= GL(m, K) where n = ExtensionDegree (G) */

ElementOrderBound := function (n, K)
   
   p := Characteristic (K);
   if p eq 0 then return 3^(n div 2) * 2^(Ilog (2, n) + 1); end if;

   if ISA (Type(K), FldFun) then 
      L := BaseRing (K);
      F := BaseRing (L);
   elif ISA (Type(K), FldFunRat) then 
      F := BaseRing (K);
   else
      error "ElementOrderBound: Problem with type of field K"; 
   end if;
   q := #F;
   return q^n - 1;
end function;

/* are the last NmrTries entries in L identical? */

IsSettled := function (L, NmrTries)

   len := #L;
   if L[len] eq 1 then return true; end if;

   if len ge NmrTries then
      S := {L[len - i + 1] : i in [1..NmrTries]};
      return #S eq 1;
   end if;

   return false;
end function;

/* does matrix g have finite order? if so, return true and, 
   if known, a multiplicative upper bound for order of g, else return false;
   if Power is true, then use powering to check if related 
   matrix is the identity, else test if matrix is unipotent;
   PowerLimit > 0: abort computation if required power is > PowerLimit
   Magma: if group defined over integers or rationals, then
          use default magma algorithm to decide; */

MatrixHasFiniteOrder := function (g: Magma := true, Power := false, 
   PowerLimit := 0)

   if IsIdentity (g) then return true, 1; end if;

   G := Parent (g);

   // do we know isomorphic copy of G? if so, compute order of image of g 
   if HasKnownIsomorphicCopy (G) then 
      tau := G`Congruence`Map;
      return true, Order (tau (g));
   end if;

   K := BaseRing (G);
   p := Characteristic (K);

   /* use Magma default algorithm? */
   if Magma and (ISA (Type (K), FldRat) or ISA (Type (K), RngInt) 
      or ISA (Type (K), FldNum)) then 
      return InternalHasFiniteOrder (g), _;
   end if;

   n0 := ExtensionDegree (G);
   b := ElementOrderBound (n0, K);

   O := [];
   if p eq 0 then
      /* check if NmrTrials distinct congruence images of this element have 
         precisely the same order -- otherwise element has infinite order */
      r := 2; nmr := 1; NmrTrials := 2; 
      repeat
         vprint Infinite: "Repeat: compute congruence image for prime r >= ",  NextPrime (r);
         H, tau, images := CongruenceImage (sub<Generic (G) | g>: 
                           Prime := NextPrime (r));
         d, verified := Order (images[1]: Proof := false);
         if verified then 
            Append (~O, d); 
            vprint Infinite: "Congruence image orders: ", O;
            if #Set (O) ne 1 then 
               vprint Infinite: "Char 0: Order of images not constant"; return false, Infty; 
            end if;
         end if;
         r := Characteristic (BaseRing (H));
         nmr +:= 1;
      until nmr gt NmrTrials;
   else
      /* construct NmrTrials distinct congruence images;
         take LCM of orders of images in hope it will exceed 
         bound b on finite order of element */
      NmrTrials := 3; 
      F := Type (K) eq FldFun select BaseRing (BaseRing (K)) else BaseRing (K);
      f := Degree (F);
      CongruenceFunction := Type (K) eq FldFun select PAFFC else PFFC;
      soln := -1;
      /* construct no more than NmrTrials distinct congruence images */
      nmr := 1; 
      repeat
         vprint Infinite: "Construct congruence image";
         H, tau, images, soln := CongruenceFunction (sub<Generic (G) | g>: start := soln);
         d, verified := Order (images[1]: Proof := false);
         if verified then 
            Append (~O, d); 
            vprint Infinite: "Congruence image orders: ", O;
            if LCM (O) gt b then 
               vprint Infinite: "Char > 0: LCM of image orders too large"; 
               return false, Infty; 
            end if;
         end if;
         nmr +:= 1;
      until IsSettled (O, NmrTrials) or nmr gt 2 * NmrTrials;
   end if;
   
   /* take d to be minimum of the image orders computed */
   d := Minimum (O);

   flag := MyHasFiniteOrder (g, d, b, n0, p: Power := Power, Limit := PowerLimit);
   if flag cmpeq true then
      bound := p eq 0 select d else d * p^Ceiling (Log (p, Degree (G))); 
      return flag, bound;
   elif flag cmpeq false then 
      return flag, Infty;
   else 
      return flag, 0;
   end if;
end function;

/* does an element of order o imply G is infinite? */

IsValidOrder := function (G, o)
   n0 := ExtensionDegree (G);

   if n0 le 10 then 
      v1 := [2, 12, 48, 1152, 3840, 103680, 2903040, 696729600, 
             1393459200, 8360755200];
      valid := o le v1[n0]; 
   else 
      valid := o le 2^(n0) * Factorial (n0);
   end if;
   if not valid then return false; end if;

   basis := PrimeBasis (o);
   return forall{p : p in basis | p le n0 + 1}; 
end function;

/* construct composition tree for H */

ConstructCT := function (H: PresentationKernel := true)
   vprint Infinite: "Now construct composition tree for congruence image";
   T := CompositionTree (H: PresentationKernel := PresentationKernel);
   vprint Infinite: "Number of nodes in tree is ", #T;
   o := CompositionTreeOrder (H);
   vprint Infinite: "Order of congruence image is ", o;
   H`Order := o;
   return o;
end function;

procedure SetFiniteFlag (G, value) 
   if not assigned G`Congruence then G`Congruence := rec<RF | >; end if;
   G`Congruence`Finite := value;
end procedure;

/* NumberRandom: number of random elements to test order; 
   Kernel: construct kernel to congruence image;
   Algebra: use algebra algorithm to decide finiteness for function field;
   Presentation: one of "CT", "FP", "PC"
   Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
   Short: defining length for short presentation; 
   Nilpotent: G is nilpotent;
   Magma: if group defined over integers or rationals or over number field, 
          then use default magma algorithm to decide;
*/

IsFiniteMatrixGroup := function (G: Kernel := false, OrderTest := true,
   Prime := 3, Presentation := "CT", Magma := true, Algebra := true, 
   Nilpotent := false, OrderLimit := 10^15, Small := 10^6, Short := 30, NumberRandom := 10) 

   if not IsValidInput (G) then error
      "IsFiniteMatrixGroup: incorrect input";
   end if;

   if assigned G`Congruence and assigned G`Congruence`Finite then 
      return G`Congruence`Finite;  
   end if;

   /* do we want kernel? if so, we must evaluate relations */
   DetTest := not Kernel;
   if Kernel then OrderTest := false; end if;
   if Kernel or Ngens (G) eq 1 then NumberRandom := 0; end if;

   K := BaseRing (G);
   m := Ngens (G);

   vprint Infinite: "IsFiniteMatrixGroup: Input field type is ", Type (K);

   /* use Magma default? */
   if (not Kernel) and Magma and 
      (ISA (Type (K), FldRat) or ISA (Type (K), RngInt) or 
       ISA (Type (K), FldNum)) then 
      vprint Infinite: "Use Magma to decide finiteness ...";
      flag := InternalIsFinite (G);
      SetFiniteFlag (G, flag);
      return flag, _, _, _;
   end if;

   if DetTest then 
      /* do generators of G have constant determinant? */
      if (ISA (Type(K), FldFunRat) or ISA (Type(K), FldFun)) and 
         exists{i : i in [1..m] | not IsConstant (Determinant (G.i))} then
            vprint Infinite: "Generator has non-constant determinant";
         SetFiniteFlag (G, false);
         return false, _, _, _, _; 
      end if;
   end if;

   /* Algebra relevant only for function fields */
   Algebra := Algebra and (not Kernel) and ISA (Type(K), FldFunRat); 

   vprint Infinite: "IsFiniteMatrixGroup: Construct congruence image";
   H, tau, images := MyCongruenceImage (G: Prime := Prime, 
                             Selberg := true, Algebra := Algebra);
   assert #images eq m;

   p := Characteristic (K);
   
   /* char 0: identity or repetition among generator images implies infinite */
   if Kernel eq false and p eq 0 and 
      (Identity (H) in images or #Set (images) ne m) then 
      vprint Infinite: "Deduced congruence subgroup is non-trivial";
      SetFiniteFlag (G, false);
      return false, H, tau, _, _; 
   end if;

   // compute power of matrix only if power < PowerLimit 
   PowerLimit := 10^6;

   RandomElementsHaveFiniteOrder := function (G, K, NumberRandom, PowerLimit)
      P := RandomProcess (G: Scramble := 10);
      for i in [1..NumberRandom] do 
         vprint Infinite: "Test determinant / order of random element i = ", i;
         // g := MyRandomElement (G);
         g := Random (P);
         if ((ISA (Type(K), FldFunRat) or ISA (Type(K), FldFun)) and 
            not IsConstant (Determinant (g))) or 
            MatrixHasFiniteOrder (g: PowerLimit := PowerLimit) cmpeq false then 
            SetFiniteFlag (G, false);
            // return false, H, tau, _, _; 
            return false;
         end if;
      end for;
      return true;
   end function;

   flag := RandomElementsHaveFiniteOrder (G, K, 0, PowerLimit);
   if not flag then return flag, H, tau, _, _; end if;

   if OrderTest then 
      vprint Infinite: "Test whether generators have finite order";
      /* do generators of G have finite order? */
      n0 := ExtensionDegree (G);
      b := ElementOrderBound (n0, K);
      if exists(j){i: i in [1..Ngens (G)] | 
         MyHasFiniteOrder (G.i, Order (images[i]), b, n0, p:
              Power := false, Limit := PowerLimit) cmpeq false} then 
         vprint Infinite: "Generator ", j, " has infinite order";
         SetFiniteFlag (G, false);
         return false, H, tau, _, _; 
      end if;
      /* all generators have finite order */
      if Ngens (G) eq 1 then 
         SetFiniteFlag (G, true);
         return true, H, tau, _, _; 
      end if;
   end if;

   flag := RandomElementsHaveFiniteOrder (G, K, NumberRandom, PowerLimit);
   if not flag then return flag, H, tau, _, _; end if;

   /* use Magma default? */
   if (not Kernel) and Magma and 
      (ISA (Type (K), FldRat) or ISA (Type (K), RngInt)) then 
      vprint Infinite: "Use Magma to decide finiteness ...";
      flag := InternalIsFinite (G);
      SetFiniteFlag (G, flag);
      return flag, H, tau, _;
   end if;

   /* use algebra algorithm for function field? */
   if Algebra then 
      vprint Infinite: "Use Algebra Algorithm to decide";
     flag, H, tau := FunctionFieldAlgebraAlgorithm (G: 
             Magma := Magma, Nilpotent := Nilpotent or Ngens (G) eq 1);
     if flag then
	return flag, H, tau, _;
     else
	return false, _, _, _;
     end if;
    
   end if;

   vprint Infinite: "Congruence image is defined over ", BaseRing (H);
   /* construct composition tree for H */
   o := ConstructCT (H);

   if Kernel eq false and p eq 0 and not IsValidOrder (G, o) then 
      vprint Infinite: "Order of congruence image is not valid";
      SetFiniteFlag (G, false);
      return false, H, tau, _, _; 
   end if;

   /* construct presentation for H; 
      gens are preimages in G of generators of H */

   gens, Rels := ConstructPresentation (G, H, images: Small := Small, 
      Presentation := Presentation, OrderLimit := OrderLimit, Short := Short);

   Monte := false;
   if p eq 0 and not Kernel then 
      /* compute congruence image over another finite field */
      // G1 := sub<Generic (G) | G>;
      // H1, tau1, gens1 := CongruenceImage (G1: 
      //    Prime := NextPrime (Characteristic (BaseRing (H))));

      for i in [1..#Rels] do
         /* 
         vprint Infinite: "Evaluate relator ...", i;
         vprint Infinite: "... over second congruence image ...";
         g := Evaluate (Rels[i], gens1);
         if not IsIdentity (g) then 
            vprint Infinite: "Deduced from test over second congruence image";
            SetFiniteFlag (G, false);
            return false, H, tau, _, _; 
         end if;
         */
         vprint Infinite: "Evaluate relator ", i, "over input field ...";
         g := Evaluate (Rels[i], gens);
         if not IsIdentity (g) then 
            vprint Infinite: "Deduced from test over input field";
            SetFiniteFlag (G, false);
            return false, H, tau, _, _; 
         end if;
      end for;
      G`Order := H`Order;
      SetFiniteFlag (G, true);
      G`Congruence`Relations:= Rels;
      G`Congruence`Isomorphism := true;
      return true, H, tau, Rels, sub<G|>;
   else
      vprint Infinite: "Evaluate all relators ...";
      N := sub<Generic (G) | Evaluate (Rels, gens)>;

      if IsTrivial (N) then 
         G`Congruence`Isomorphism := true;
         G`Order := H`Order; 
         finite := true;
      else 
         if p gt 0 then
           vprint Infinite: "Test unipotence of kernel";
           finite := IsUnipotentClosure (G, N);
           vprint Infinite: "Kernel unipotent? ", finite;
         else 
            vprint Infinite: "Construct normal closure";
            fct := Monte select NormalClosureMonteCarlo else NormalClosureRandom; 
            N := fct (G, N); 
            finite := false;
         end if;
      end if;
      SetFiniteFlag (G, finite);
      G`Congruence`Relations:= Rels;
      return finite, H, tau, Rels, N;
   end if;
end function;

intrinsic IsFinite (G :: GrpMat[FldFunRat]: DetermineOrder := false, 
                  Prime := 3, Algebra := true, Presentation := "CT",
                  OrderLimit := 10^15, Small := 10^6, Short := 30, 
                  Nilpotent := false, NumberRandom := 10)
-> BoolElt, RngIntElt 

{  Determine if G is finite; if so, return true and order, else false;
   NumberRandom: number of random elements to test order;
   DetermineOrder: if G is finite, then compute and return its order;
   Algebra: use algebra algorithm to decide finiteness for function field;
   Prime: applies to input defined over char 0 only;
          if positive, then lower bound for characteristic of image or
          if 0 then construct char 0 congruence image;
   Nilpotent: G is nilpotent;  
   Presentation: one of "CT", "PC", "FP";
   Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
   Short: defining length for short presentation
}
   if IsTrivial (G) then return true, 1; end if;
   f := IsFiniteMatrixGroup (G: Algebra := Algebra, 
                                Nilpotent := Nilpotent, Prime := Prime, 
                                OrderLimit := OrderLimit,
                                Short := Short, Small := Small, 
                                Presentation := Presentation,
                                NumberRandom := NumberRandom);

   if f and (DetermineOrder or assigned G`Order) then 
      return f, Order (G); 
   else 
      return f, _; 
   end if;
end intrinsic;

intrinsic IsFinite (G :: GrpMat[FldFun]: DetermineOrder := false, 
                  Prime := 3, Presentation := "CT",
                  OrderLimit := 10^15, Small := 10^6, Short := 30, 
                  Nilpotent := false, NumberRandom := 10)
-> BoolElt, RngIntElt 

{  Determine if G is finite; if so, return true and order, else false;
   NumberRandom: number of random elements to test order;
   DetermineOrder: if G is finite, then compute and return its order;
   Prime: applies to input defined over char 0 only;
          if positive, then lower bound for characteristic of image or
          if 0 then construct char 0 congruence image;
   Nilpotent: G is nilpotent;  
   Presentation: one of "CT", "PC", "FP";
   Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
   Short: defining length for short presentation
}
   if IsTrivial (G) then return true, 1; end if;
   f := IsFiniteMatrixGroup (G: Nilpotent := Nilpotent, Prime := Prime, 
                                OrderLimit := OrderLimit,
                                Short := Short, Small := Small, 
                                Presentation := Presentation,
                                NumberRandom := NumberRandom);

   if f and (DetermineOrder or assigned G`Order) then 
      return f, Order (G); 
   else 
      return f, _; 
   end if;
end intrinsic;

intrinsic IsFinite (G :: GrpMat[FldNum]: DetermineOrder := false, 
                  Prime := 3, Presentation := "CT", UseCongruence := false, 
                  OrderLimit := 10^15, Small := 10^6, Short := 30, 
                  Nilpotent := false, NumberRandom := 10)
-> BoolElt, RngIntElt 

{  Determine if G is finite; if so, return true and order, else false;
   NumberRandom: number of random elements to test order;
   DetermineOrder: if G is finite, then compute and return its order;
   Prime: applies to input defined over char 0 only;
          if positive, then lower bound for characteristic of image or
          if 0 then construct char 0 congruence image;
   Nilpotent: G is nilpotent;  
   UseCongruence: use congruence homomorphism to decide;
   Presentation: one of "CT", "PC", "FP";
   Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
   Short: defining length for short presentation
}
   if IsTrivial (G) then return true, 1; end if;
   f := IsFiniteMatrixGroup (G: Nilpotent := Nilpotent, Prime := Prime, 
                                OrderLimit := OrderLimit,
                                Magma := UseCongruence eq false,
                                Short := Short, Small := Small, 
                                Presentation := Presentation,
                                NumberRandom := NumberRandom);

   if f and (DetermineOrder or assigned G`Order) then 
      return f, Order (G); 
   else 
      return f, _; 
   end if;
end intrinsic;
 
intrinsic IsFinite (G :: GrpMat[FldRat]: DetermineOrder := false, 
                  Prime := 3, Presentation := "CT", UseCongruence := false, 
                  OrderLimit := 10^15, Small := 10^6, Short := 30, 
                  Nilpotent := false, NumberRandom := 10)
-> BoolElt, RngIntElt 

{  Determine if G is finite; if so, return true and order, else false;
   NumberRandom: number of random elements to test order;
   DetermineOrder: if G is finite, then compute and return its order;
   Prime: applies to input defined over char 0 only;
          if positive, then lower bound for characteristic of image or
          if 0 then construct char 0 congruence image;
   Nilpotent: G is nilpotent;  
   UseCongruence: use congruence homomorphism to decide;
   Presentation: one of "CT", "PC", "FP";
   Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
   Short: defining length for short presentation
}
   if IsTrivial (G) then return true, 1; end if;
   f := IsFiniteMatrixGroup (G: Nilpotent := Nilpotent, Prime := Prime, 
                                OrderLimit := OrderLimit,
                                Magma := UseCongruence eq false,
                                Short := Short, Small := Small, 
                                Presentation := Presentation,
                                NumberRandom := NumberRandom);

   if f and (DetermineOrder or assigned G`Order) then 
      return f, Order (G); 
   else 
      return f, _; 
   end if;
end intrinsic;

intrinsic IsFinite (G :: GrpMat[RngInt]: DetermineOrder := false, 
                  Prime := 3, Presentation := "CT", UseCongruence := false, 
                  OrderLimit := 10^15, Small := 10^6, Short := 30, 
                  Nilpotent := false, NumberRandom := 10)
-> BoolElt, RngIntElt 

{  Determine if G is finite; if so, return true and order, else false;
   NumberRandom: number of random elements to test order;
   DetermineOrder: if G is finite, then compute and return its order;
   Prime: applies to input defined over char 0 only;
          if positive, then lower bound for characteristic of image or
          if 0 then construct char 0 congruence image;
   UseCongruence: use congruence homomorphism to decide;
   Nilpotent: G is nilpotent;  
   Presentation: one of "CT", "PC", "FP";
   Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
   Short: defining length for short presentation
}
   if IsTrivial (G) then return true, 1; end if;
   f := IsFiniteMatrixGroup (G: Nilpotent := Nilpotent, Prime := Prime, 
                                OrderLimit := OrderLimit,
                                Magma := UseCongruence eq false,
                                Short := Short, Small := Small, 
                                Presentation := Presentation,
                                NumberRandom := NumberRandom);

   if f and (DetermineOrder or assigned G`Order) then 
      return f, Order (G); 
   else 
      return f, _; 
   end if;
end intrinsic;
