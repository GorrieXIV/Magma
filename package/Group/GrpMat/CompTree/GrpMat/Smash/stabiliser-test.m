freeze;

import "order-test.m": ExponentGL;
import "numbers.m": FactorsToInteger;
import "random.m": ChooseRandomElements;
import "functions.m": SetBlockSystem;
import "numbers.m": Collected;
import "numbers.m": PrimePowers;
import "numbers.m": RestrictedPartitions;
import "misc.m": BubbleSort;
import "minblocks.m": MinBlocks, NumberBlocks, IsBlockSystem;
import "minsub.m": MinimalSubmodule;
import "random.m": RandomElement;
import "misc.m": FormCommutators;
import "is-primitive.m": SmashElement;
import "is-primitive.m": ExamineSmashResult;

/* S is a submodule of module; rewrite its basis vectors in the 
   full vector space V -- we need these for input to MinBlocks */
 
EchelonisedBasis := function (V, module, S)

   B := Basis (S);
   B := [module!v : v in B];
   B := Basis (sub < V | [Eltseq (B[j]) : j in [1..#B]]>);
   return [V!v : v in B ];

end function;

/* check which element of prime order can be obtained from powers of the 
   supplied elements; return element of largest prime order found */

ExtractLargestPrimeOrderElement := function (Elts, Orders)

   vprint Smash: "Order sequence is ", Orders;

   /* store maximum prime which occurs in factorisation of this order */
   prime := [Maximum (PrimeBasis (Orders[i])): i in [1..#Elts]];

   vprint Smash: "Prime sequence is ", prime;

   /* maximum prime encountered */
   p, pos := Maximum (prime);
    
   z := Elts[pos]^(Orders[pos] div p);
   return <z, p>;

end function;

/* given z an element of order p and w;
   set up w[index] * z^k * w[j]^-1 for j = 1 .. index - 1 and k = 1..p;
   and add them to y */
  
procedure SetupElements (~y, z, w, index, p)

   if index lt 2 then return; end if; 

   /* set up powers of z  */
   power := [z^k : k in [1..p]];

   for j in [1..index - 1] do
      inv := w[j]^-1;
      y cat:= [w[index] * power[k] * inv : k in [1..p]];
   end for;

end procedure;

/* can we deduce that z of order p acts fixed-point freely on r blocks?
   we can if p divides r, p does not divide exp GL ( d / r, q)
   and char pol of z is (x^p - 1)^(d / p) */

FixedPointFreeElement := function (M, z, p, r)

   if r mod p ne 0 then return false; end if;

   d, F := BasicParameters (M);
   q := #F;

   /* find exponent of GL (d div r, q) */
   exp := FactorsToInteger (ExponentGL (d div r, q));
   if exp mod p eq 0 then return false; end if;

   f := CharacteristicPolynomial (z);

   /* has element z a characteristic polynomial equal to (x^p - 1)^(d / p)? */
   PA<x> := Parent (f);
   pol := (x^p - 1)^(d div p);

   return (f eq pol);

end function; 

/* take the supplied elements and check which element of prime power
   order can be obtained from powers of each; among these, find and return 
   the element of largest prime-power order co-prime to r -- if you do 
   not want to impose this restriction, supply 1 as the value of r */

ExtractLargestPrimePowerOrderElement := function (Elts, Orders, r)

   prime := [];

   for i in [1..#Elts] do 
      powers := Factorisation (Orders[i]);
      if #powers ne 0 then 
         prime[i] := Maximum ([powers[j][1]^powers[j][2] : j in [1..#powers]]);
      end if;
   end for;

   /* non-trivial prime powers encountered which are coprime to r */
   new := [prime[i] : i in [1..#prime] | 
              prime[i] ne 1 and Gcd (prime[i], r) eq 1];

   vprint Smash: "Order sequence is ", Orders; 
   vprint Smash: "Prime power sequence is ", prime;
   vprint Smash: "Filtered prime power sequence is ", new;

   if #new eq 0 then return false; end if;

   /* largest non-trivial prime power encountered which is coprime to r */
   p := Maximum (new);

   /* find its position in original list */
   pos := Position (prime, p);
   z := Elts[pos]^(Orders[pos] div prime[pos]);

   return <z, p, pos>;

end function; 

/* sort composition factors of each dimension by decreasing multiplicity */

SortCFs := function (CF) 

   d := SetToSequence ({Dimension (CF[i][1]) : i in [1..#CF]});
   Sort (~d);

   Result := [];
   for x in d do
      facs := [CF[j]: j in [1..#CF] | Dimension (CF[j][1]) eq x]; 
      m := [CF[j][2]: j in [1..#CF] | Dimension (CF[j][1]) eq x]; 
      BubbleSort (~m, ~facs);
      Reverse (~facs);
      Result cat:= facs;
   end for;

   return Result;

end function;

/* find all linear combinations of the integer s in  terms of the  d[i],  
   where each coefficient of the d[i] is bounded above by m[i] */

FindExpressions := function (s, d, m)

   R := RestrictedPartitions (s, d);

   /* check whether the number of occurrences of each entry in a
      partition is at most the corresponding entry in the sequence m */

   solutions := []; 

   for i in [1..#R] do
      C := Collected (R[i]);
      if (#[j: j in [1..#C] | C[j][2] gt m[Position (d, C[j][1])]]) eq 0 then 
         Append (~solutions, C);
      end if;
   end for;

   // vprint Smash: "Good partitions: ", solutions;
   return solutions;

end function; 

/* CF is the list of composition factors;
   set up the list of invariants; concurrently, set up sequences d and m, 
   which store the distinct dimensions of factors, and the number of 
   factors of each *distinct* dimension, respectively; 

   now use FindExpressions to find all solutions a[i] to the equation
  
         sum of a[i] * d[i] = s
   
   where a[i] <= m[i]; return set of solutions, invariants, d, m */

FindSolutions := function (CF, s)

   /* set up d, m, invariants */

   d := []; m := []; invariants := [];
   for i in [1..#CF] do
      dim := Dimension (CF[i][1]);
      mult := CF[i][2];
      invariants[i] := [dim, mult];
      index := Position (d, dim);
      if index eq 0 then 
         Append (~d, dim);
         m[#d] := mult;
      else
         m[index] +:= mult;
      end if;
   end for;

   vprintf Smash: "Invariants for submodule are %o\n", invariants;
   // vprint Smash: "Distinct dimensions of factors = ", d, "Multiplicities = ", m;

   R := FindExpressions (s, d, m);

   vprintf Smash: "The number of possible solutions is %o\n", #R;
   // vprint Smash: "Solutions are ", R;

   return R, invariants, d, m;

end function;

/* run two tests on each component of the solution; if no component of 
   the solution passes either test, then we must retain the submodule
  
   if any component of the solution passes either test, we note relevant
   composition factors and later obtain a minimal submodule containing
   this composition factor to hand to MinBlocks; since the only
   requirement for MinBlocks is that we have a space contained in 
   the block, it is sufficient to find any space contained in it;
   we do not need to find all */
   
procedure TestSolution (invariants, solution, d, m, combined, ~check, ~retain)

   /* for each solution, take each component 
   
       [D, C] 
  
      and see if it satisfies either of the following:

       (i) are there C factors of dimension D?
      (ii) do all factors of dimensions D occur with multiplicity 1?
   
     if the component of the solution satisfies either of these tests, 
     then note relevant composition factors
   
     if no component of the solution satisfies either of these
     tests, we cannot settle definitely whether the associated 
     minimal submodule may be contained in a block so we must 
     save this submodule for later processing  */
   
   len := #invariants;

   retain := true;
   NmrComponents := #solution; 

   vprintf Smash: "\nConsider possible solution %o\n", solution;
   j := 0;
   while j lt NmrComponents and retain do 

      j +:= 1;

      /* consider component [D, C];  first check if the coefficent 
         C equals the sum of the multiplicities for all factors of 
         this dimension D */

      D := solution[j][1];
      C := solution[j][2];

      if solution[j] in combined then  

         retain := false; 

         vprintf Smash: "Component [%o, %o] passed Test 1\n", D, C;

         /* note index of any one of the composition factors of dimension D */
         if exists (k) {k : k in [1..len] | invariants[k][1] eq D} then 
            Include (~check, k);
         end if;
          
      else 
        
         /* check if the multiplicity of each factor of dimension D is 1 */
         case2 := true;
         k := 1;
         repeat
            dim := invariants[k][1];
            if dim eq D then 
               case2 := (invariants[k][2] eq 1);
            end if;
            k +:= 1;
         until case2 eq false or dim gt D or k gt len;

         /* if so, we need to take at most 
          
            (number of factors of dimension D) - C + 1 
          
            CFs before finding some minimal submodule containing this block */

         if case2 eq true then 
            vprintf Smash: "Component [%o, %o] passed Test 2\n", D, C;
            retain := false;
            index := Position (d, D);
            reqnmr := m[index] - C + 1; 
            k := 1; nmr := 0;
            repeat 
               if invariants[k][1] eq D then 
                  Include (~check, k);
                  nmr +:= 1;
               end if;
               k +:= 1;
            until nmr eq reqnmr;
         end if; 

      end if; 

      if retain then 
         vprintf Smash: "Component [%o, %o] fails both tests\n", D, C;
      end if;

   end while; /* while j */

end procedure; 

/* processing at most MaxNmr minimal submodules of module isomorphic 
   to a particular composition factor and hand each to MinBlocks */

ProcessLattice := function (M, module, Submods)

   d, F := BasicParameters (M);
   V := VectorSpace (F, d);

   /* test each minimal submodule in MinBlocks */

   NmrSubmods := #Submods;

   vprintf Smash: "Number of minimal submodules is %o\n", NmrSubmods;
   for i in [1..NmrSubmods] do
      B := EchelonisedBasis (V, module, Submods[i]);
      BT := MinBlocks (M, B);
      if NumberBlocks (BT) gt 1 then
         return BT;
      end if;
   end for;

   return true;

end function; 

/* M is irreducible module for matrix group 
   module is the reducible module for subgroup
   CF is result of Meataxe for the reducible module
   s is the block size 
   
   if non-trivial block system found, it is returned,
   else the procedure returns value of RetainSubgroup */
   
FindMinimalSubmods := function (M, module, CF, s, iteration)

    RetainSubgroup := false; /* do not keep this subgroup */

    solutions, invariants, d, m := FindSolutions (CF, s);

    if #solutions eq 0 then return RetainSubgroup; end if;

    /* note d and m record *distinct* dimensions and multiplicities 
       for that dimension -- not for each factor */

    combined := [[d[i], m[i]] : i in [1..#d]]; 

    /* when all solutions are processed, take the set of invariants noted,
       and for each such invariant, find a minimal submodule of module 
       containing this composition factor and hand it to MinBlocks */

    check := []; /* indices for invariants to consider */
    Resolved := {}; /* record resolved solutions */

    V := VectorSpace (BaseRing (M), Dimension (M)); 

    for i in [1..#solutions] do 

       TestSolution (invariants, solutions[i], d, m, combined, ~check, ~retain);

       /* does any component in the solution fail both test 1 and test 2?
          if so, we try to apply test 3 to complete solution */

       if retain eq true then 

          /* if block size s equals (d_1, 1) then apply test 3 -- 
             compute a basis for the homomorphisms from each composition
             factor of dimension s to the module;
             if the length of the basis is at most one for each such 
             composition factor, we may apply MinBlocks to each basis;
             if no block system found, we rule out solution */ 
           
          if (s eq solutions[i][1][1]) then
             HM := [];
             AllAtMostOne := true;

             for j in [1..#CF] do
                if (invariants[j][1]) eq s then 
                   HomBasis := Basis (GHom (CF[j][1], module));
                   BasisLength := #HomBasis;

                   /* store the length of the basis as part of the 
                      invariant sequence for this submodule */
                   invariants[j][3] := BasisLength;

                   // vprint Smash: "Length of GHom basis for CF[", j, "] is ", BasisLength;
                   if BasisLength gt 1 then AllAtMostOne := false; end if;

                   /* store one element from basis */
                   if BasisLength eq 1 then 
                      Append (~HM, V!Eltseq (HomBasis[1][1]));
                   end if;

                end if;
             end for;

             /* if all bases for the homomorphisms from each CF[i] 
                to module have dimension at most one, we can run 
                MinBlocks on one vector from each basis */

             if AllAtMostOne then 
                vprintf Smash: "Dimension of GHom basis is at most 1 \
for all relevant composition factors\n";
                vprint Smash: "Hence run MinBlocks on element of each HomBasis";
                
                Include (~Resolved, i); 

                /* apply MinBlocks to each vector stored in HM */
                for j in [1..#HM] do
                   BT := MinBlocks (M, [HM[j]]);
                   NmrBlocks := NumberBlocks (BT);
                   if NmrBlocks gt 1 then 
                      return BT;
                   end if; 
                end for; 
             end if;
          else 
             vprintf Smash: "No solution component passed test 1 or 2 \
and solution did not pass test 3\n";
          end if; /* test 3 */
       else 
          Include (~Resolved, i); 
       end if; /* if retain */

    end for; /* for i */

    // vprint Smash: "After 3 basic tests on solutions, Resolved is ", Resolved;

    /* run through all composition factors whose indices occur in check;
       compute a minimal submodule of module containing this composition
       factor and hand this submodule to MinBlocks */

    for i in [1..#check] do
       index := check[i];
       vprintf Smash: "Now computing minimal submodule for CF[%o]\n", index;
       S := MinimalSubmodule (module, CF[index][1]);
       B := EchelonisedBasis (V, module, S);
       BT := MinBlocks (M, B);
       NmrBlocks := NumberBlocks (BT);
       if NmrBlocks gt 1 then 
          return BT;
       end if; 
    end for; 

    /* now, if necessary, apply following strategy:
       for each composition factor whose dimension occurs in a solution, 
       we compute some minimal submodules of module which are isomorphic 
       to this factor; if for each factor we compute all such minimal 
       submodules and hand each to MinBlocks without finding a block 
       system we do not need to retain this module */

    Remain := {1..#solutions} diff Resolved;

    if #Remain ne 0 then 

       /* what dimensions occur in solutions? */
       SolnSizes := {solutions[i][j][1] : j in [1..#solutions[i]], 
                                           i in Remain};
       vprintf Smash: "Remaining possible solutions are %o\n", Remain;
       vprintf Smash: "Dimensions in remaining solutions are %o\n", SolnSizes;

       /* set the maximum number of minimal submodules to compute for 
          each factor to be the larger of q + 1 or a multiple of 50 */

       q := #BaseRing (M);
       MaxNmr := 1000 * iteration;
       MaxNmr := Maximum (q + 2, MaxNmr + 1);

       /* process all composition factors of dimension an element of SolnSizes; 
          abort the process if for any composition factor we have failed to 
          compute all the minimal submodules isomorphic to this factor */

       t := Cputime ();
       L := [];
       for j in [1..#CF] do 
          if (Dimension (CF[j][1]) in SolnSizes) then 
             Submods, AllFound := MinimalSubmodules (module, CF[j][1]: 
                                                     Limit := MaxNmr);
             /* did we find all minimal submodules isomorphic to CF? */
             if not AllFound then 
                 vprint Smash: "We did not find all minimal submodules"; 
                 return invariants;
             end if;
             Append (~L, Submods);
          end if;
       end for;

       for j in [1..#L] do 
          R := ProcessLattice (M, module, L[j]);
          if IsBlockSystem (R) then return R; end if;
       end for;

       vprint Smash: "Time taken by minimal submodule approach is ", Cputime () - t;
      
    end if; /* if Remain <> 0 */

    return false;
             
end function;

/* chop submodule H; if reducible, then find appropriate minimal submodules;  
   the function returns a block system, or a list of invariants if we 
   must keep submodule, or false if no solution nor block system found */

ProcessSubmodule := function (M, H, s, iteration) 

   /* chop the module H */
   CF := ConstituentsWithMultiplicities (H);

   /* if the module is reducible, can we find block system? */
   if #CF gt 1 or CF[1][2] gt 1 then 
      //vprint Smash: "Submodule is reducible";
      CF := SortCFs (CF);
      R := FindMinimalSubmods (M, H, CF, s, iteration);
   else 
      R := false;
   end if; 

   return R;

end function; 

/* apply MeatAxe to various modules to get their composition factors
   M irreducible module
   S collection of submodules 
   z element of order p a prime 
   s block size 
   
   if block system found return block system else return false; 

   T is list of subgroups not eliminated, Invariants is list of invariants */

procedure ExamineCompositionFactors (M, S, SInvariants, 
            ConjugatesRequired, z, p, s, iteration, ~T, ~TInvariants, ~Result) 

   NmrTries := ((Dimension (M) div s) div p) + 1;
   vprintf Smash: "We must select %o elements w[n]\n", NmrTries;

   T := [];
   TInvariants := [];

   w := [];

   /* if we decide that a particular element w[n] is not suitable, then 
      ReplaceElement is set true and we choose new w[n] */

   ReplaceElement := false;

   Large := GL (Dimension (M), BaseRing (M));

   n := 0; N := 10; trial := 1;
   while n lt NmrTries and trial lt N do
 
      n +:= 1; trial +:= 1;
      vprintf Smash: "\nNow working with element w[%o] ...\n", n;

      x := RandomElement (M);
      w[n] := x;
      ReplaceElement := false;

      y := ConjugatesRequired select [w[n] * z * w[n]^-1] else [];

      SetupElements (~y, z, w, #w, p);
      vprintf Smash: "Computed %o elements y[j]\n", #y;

      /* modules and their invariants retained for current w[n] */
      RetainModules := [];
      RetainInvariants := [];

      i := 0;
      while i lt #S and ReplaceElement eq false do 

         i +:= 1;
         //vprint Smash: "Invariants of S[", i, "] is ", SInvariants[i];

         /* initialise Current to contain invariants of S[i] and add 
            to it the list of invariants retained for <S[i], y[j]>;
            if two submodules containing S[i] have the same set of 
            invariants, we choose a new w[n] */

         Current := [SInvariants[i]]; 

         /* set up generators of S[i] as sequence gens */
         gens := GroupGenerators (Group (S[i]));

         j := 0;
         while j lt #y and ReplaceElement eq false do 
            j +:= 1;

            /* set up H as the module generated by S[i] and y[j] */
            H := sub <Large | y[j], gens>;
            H := GModule (H); 

            vprintf Smash: "Processing submodule %o %o %o\n", n, i, j;

            R := ProcessSubmodule (M, H, s, iteration);

            /* did we find block system? if so, return */
            if IsBlockSystem (R) then 
               Result := R;
               return; 
            end if;

            /* do we retain the subgroup? */
            if Type (R) eq SeqEnum then 
               Sort (~R);
               ReplaceElement := (R in Current);
               if ReplaceElement eq false then 
                  // vprint Smash: "Invariants of this submodule differ from others";
                  vprint Smash: "We add the subgroup to list T";
                  Append (~RetainModules, H);
                  Append (~RetainInvariants, R); 
               else 
                  vprintf Smash: "Invariants of this submodule are already known \
-- so we choose new element\n";
                  n -:= 1;
                  RetainModules := [];
                  RetainInvariants := [];
               end if;
            end if;

         end while; /* while j */
      end while; /* while i */

      /* update contents of T by adding to it modules retained */
      T cat:= RetainModules;
      TInvariants cat:= RetainInvariants;

   end while; /* while n */

   if trial eq N then Result := "unknown"; else Result := false; end if;
   
end procedure; 

/* select m random elements from the range [a..b] */

SampleOfElements := function (a, b, m)

    Sample := {};
    if m eq 0 then return Sample; end if;

    repeat 
       Include (~Sample, Random ([a..b]));
    until #Sample eq m;
    
    return SetToSequence (Sample);

end function;

/* calculate commutators of a random sample of m elements from Elts */

SampleOfCommutators := function (Elts, m)

   Sample := SampleOfElements (1, #Elts, m);
   Sample := [Elts[x] : x in [1..#Elts] | x in Sample];

   return SetToSequence (FormCommutators (Sample));

end function;

/* w is an element of order o = p^n, a prime-power, and w^o = z; if the 
   characteristic polynomial of w is not a power of (x^o - z), then at 
   least one orbits of w does not have length o and so w^(p^(n - 1)) 
   will fix a block */

SomePowerFixesBlock := function (M, w, o, z)

   if IsPrimePower (o) eq false then return false; end if;

   f := CharacteristicPolynomial (w);
   PA<x> := Parent (f);
   factor := x^o - z;

   d := Dimension (M);
   return (f ne factor^(d div o));
  
end function;

/* find an element which fixes at least one of the r blocks 
   
   in EliminateBlockNumber we build up the stabiliser of the block
   and want to find a generating set for this stabiliser as quickly
   as possible; hence, we also want an element which lies in as few 
   proper subgroups of the block stabiliser as we can find; we try 
   to find an element of large prime-power order which fixes a block
   
   a non-trivial element with this property is very useful to
   EliminateBlockNumber strategy -- thus we work hard to try to find one 
   
   if we can find an element *whose order is prime-power* and *coprime to r*
   it will fix at least one block;
  
   we first try to find such an element among powers of our currently 
   selected random elements; 
  
   if we don't find one, we first select new random elements; 
   if we still don't find one, we compute commutators of some 
   existing elements and examine these; 
   if we don't find one using any of these strategies, we then examine
   elements of prime-power order obtained as powers of the random
   elements to see whether we can deduce from characteristic polynomial 
   structure that a power of this element of prime-power order 
   fixes a block
  
   we iterate these searches for a preset number of times determined by the
   value of NmrIterations 
  
   if after all this, we cannot find one, we return the identity */

procedure ChooseFirstElement (M, ~Elts, ~Orders, r, ~w, ~o, ~pos)

   /* can we find one among powers of our existing random elements? */

   R := ExtractLargestPrimePowerOrderElement (Elts, Orders, r);
   if Type (R) ne BoolElt then 
      w := R[1]; o := R[2]; pos := R[3]; 
      return; 
   end if;

   vprintf Smash: "No suitable w among supplied collection of elements\n";

   /* these parameters determine length of search for element */
   MaxSampleSize := 10;
   NmrIterations := 3;

   NmrSearches := 0;

   repeat 
      NmrSearches +:= 1;

      /* current number of random elements */
      NmrElements := #Elts;

      /* extend the collection of random elements */
      SampleSize := Minimum (#Elts, MaxSampleSize);
      NewElts := ChooseRandomElements (M, SampleSize: NonScalar := true);
      NewOrders := [ProjectiveOrder (NewElts[i]): i in [1..#NewElts]];
      Elts := Elts cat NewElts;
      Orders := Orders cat NewOrders;

      R := ExtractLargestPrimePowerOrderElement (NewElts, NewOrders, r);
      if Type (R) ne BoolElt then 
         w := R[1]; o := R[2]; pos := R[3] + NmrElements; 
         return; 
      end if;

      vprint Smash: "After selecting new random elements, no suitable w found";

      NmrElements := #Elts; 

      /* if we have not found suitable first element, add in 
         commutators of some existing random elements and try again */

      SampleSize := Minimum (NmrElements, 
                             Floor (Sqrt (2 * MaxSampleSize) + 1));
      EltComms := SampleOfCommutators (Elts, SampleSize);

      CommOrders := [];
      CommOrders := [Order (EltComms[i]): i in [1..#EltComms]];
      Elts := Elts cat EltComms;
      Orders := Orders cat CommOrders;

      R := ExtractLargestPrimePowerOrderElement (EltComms, CommOrders, r);
      if Type (R) ne BoolElt then 
         w := R[1]; o := R[2]; pos := R[3] + NmrElements; 
         return; 
      end if;

      vprint Smash: "After adding commutators, no suitable w found";

      /* if we have still not found one, look at characteristic 
      polynomial structure of elements of prime-power order 
      and try to deduce that power of one does act with some fixed point

      if first iteration, look at current collection of random elements 
      else look at the new elements selected  */

      if NmrSearches eq 1 then
         offset := 0;
         SampleList := Elts;
         SampleOrders := Orders;
      else 
         NewElts := NewElts cat EltComms;
         NewOrders := NewOrders cat CommOrders;
         offset := #Elts - #NewElts;
         SampleList := NewElts;
         SampleOrders := NewOrders;
      end if;
         
      NmrElements := #SampleList;

      SampleSize := Minimum (NmrElements, MaxSampleSize);
      Sample := SampleOfElements (1, NmrElements, SampleSize);
 
      /* initialise o */
      o := 1;

      for i in [1..SampleSize] do

         vprintf Smash: "Examining powers of element %o\n", i;
         g := SampleList[Sample[i]];
         order := SampleOrders[Sample[i]];

         /* look at prime-powers  */
         powers := PrimePowers (order);
         last := #powers div 2;
         for j in [1..last] do
            p := powers[2 * j - 1];
            if p gt o then 
               n := powers[2 * j];
               pow := p^n;
               vprintf Smash: "Examine char polynomial of element of order %o\n", pow;
               x := g^(order div pow);
               z := x^pow; 
               if SomePowerFixesBlock (M, x, pow, z[1][1]) eq true then 
                  w := x^(p^(n - 1));
                  o := p;
                  pos := Sample[i];
               end if;
            end if;
         end for;

      end for; 
         
      if o ne 1 then 
         pos +:= offset;
         return; 
      end if;

      vprint Smash: "Char polynomials of prime power order elements give no suitable w";

   until NmrSearches eq NmrIterations;

   /* if all else fails, return the identity element */
   vprintf Smash: 
      "Failed to find non-trivial element which fixes at least one of %o \
blocks\n", r;

   w := Elts[1]^0; o := 1; pos := 0;

end procedure;

/* seek to eliminate block number r 
   return true if successful; otherwise return false
   if block system found, it is stored as component of M  */

procedure BlockStabiliserTest (M, ~Elts, ~Orders, r, ~Result)

   Result := false;

   /* find element w which fixes at least one block  */
   ChooseFirstElement (M, ~Elts, ~Orders, r, ~w, ~o, ~pos);
   vprintf Smash: "\nFirst element w has order %o\n", o;

   /* replace the element used to provide w by a random conjugate to try 
      to ensure that the next element z selected is different from w */
   if pos ne 0 then 
      n := 0;
      repeat 
         n +:= 1;
         x := RandomElement (M);
         new := Elts[pos]^x;
      until new ne Elts[pos] or n gt 10;
      Elts[pos] := new;
   end if;

   /* search for elements of prime order and return the largest, z */
   R := ExtractLargestPrimeOrderElement (Elts, Orders);
   
   /* element z of order p */
   z := R[1];
   p := R[2];

   vprintf Smash: "The element z chosen has order %o\n", p;

   /* is it possible that w = z? */
   if w eq z then 
      vprintf Smash: "w = z in EliminateBlockNumber, replace z by a conjugate\n";
      x := RandomElement (M);
      z := z^x;
   end if;

   /* can we deduce that z acts fixed-point freely on the r blocks? */
   fpf := FixedPointFreeElement (M, z, p, r);

   /* if not, does it fix every block? */
   if fpf eq false then 

      // vprint Smash: "Calling SmashModule with element z ...";

      _ := SmashElement (M, z, false);
      Result := ExamineSmashResult (M, true);
      if Result cmpeq true then Result := false; return; end if;
      
      // we previously terminated if we discovered semilinearity 
      // if not (Result cmpeq false) then return; end if;

      if Result cmpeq "unknown" then
         fpf := false; 
      else 
         /* not all of the r blocks are fixed; 
            thus, if p = r, z is fpf */
         fpf := (p eq r);
      end if;

   end if;

   /* note the block size */
   s := Dimension (M) div r;

   /* set up invariants of first entry in T */
   T := [GModule ([w])];
   CF := ConstituentsWithMultiplicities (T[1]);
   Invariants := [];
   Invariants[1] := [[Dimension (CF[i][1]), CF[i][2]] : i in [1..#CF]];
   Sort (~Invariants[1]);

   //vprint Smash: "Invariants of start submodule is ", Invariants[1];

   /* in ExamineCompositionFactors, find collection of elements y[i], 
      at least one of which fixes the same block as does w; we must add 
      to y conjugates of z by the random elements selected if we 
      have not deduced that z acts fixed-point freely on the blocks */

   // vprint Smash: "Conjugates required? ", not fpf;

   /* now apply meataxe to various modules, iterating this until
      the set T is empty or until we find a block system */

   iteration := 0;
   repeat 
      iteration +:= 1;
      vprintf Smash: "\nCalling main procedure with list T of length %o\n", #T;
      ExamineCompositionFactors (M, T, Invariants, not fpf, 
                                 z, p, s, iteration, ~T, ~Invariants, ~Result);
  
      /* did we find block system? */
      if IsBlockSystem (Result) then 
         SetBlockSystem (M, Result); 
         Result := false;
         return;
      end if;
      if Result cmpeq "unknown" then return; end if;

      /* otherwise T is the list of outstanding subgroups and Invariants
         is collection of invariants of these subgroups */
      // vprint Smash: "Length of list T is ", #T;

   until #T eq 0;

   Result := true;

end procedure; 
