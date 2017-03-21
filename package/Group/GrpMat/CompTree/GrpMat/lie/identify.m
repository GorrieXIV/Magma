freeze;

/***************************************************************/
/*   Identify the non-abelian simple composition factor        */
/*   of a nearly simple matrix group.                          */
/*                                                             */
/*   Step 1: Determine possible underlying characteristic      */
/*                                                             */
/*   Step 2: Identify Lie type groups using LieType ()         */
/*                                                             */
/*   Step 3: Determine degree (if alternating)                 */
/*                                                             */
/*   Step 4: Determine sporadic candidates                     */
/*                                                             */
/*    Gunter Malle & E.A. O'Brien                   March 2001 */
/*    latest version May 2007                                  */
/***************************************************************/

// SetVerbose ("STCS", 1);
// SetVerbose ("RandomSchreier", 1);

declare verbose Identify, 1;

import "lietype.m": LieTypeOfCharpGroup, ClassicalTypeToLieType; 
import "char.m": MyDerivedSubgroup;
import "../../GrpMat/util/order.m": MyCentralOrder;

/* eliminate known isomorphisms from list of candidates */

procedure RemoveCoincidences (~types, ns)

   /* PSL (2, 9) and A6 */
   if <"A", 1, 9> in types and ns eq 6 then 
      Exclude (~types, <"A", 1, 9>);
   end if;

   /* PSL(4, 2) and A8 */
   if <"A", 3, 2> in types and ns eq 8 then 
      Exclude (~types, <"A", 3, 2>);
   end if;

   /* PSL (2, 7) and PSL(3, 2) */
   if <"A", 1, 7> in types and <"A", 2, 2> in types then 
      Exclude (~types, <"A", 1, 7>);
   end if;

   /* PSL (2, 5) and PSL (2, 4) and A5 */
   if <"A", 1, 5> in types and <"A", 1, 4> in types then 
      Exclude (~types, <"A", 1, 5>);
   end if;
   if <"A", 1, 5> in types and ns eq 5 then 
      Exclude (~types, <"A", 1, 5>);
   end if;
   if <"A", 1, 4> in types and ns eq 5 then 
      Exclude (~types, <"A", 1, 4>);
   end if;

   /* PSU(4, 2) and PSp (4, 3) */
   if <"2A", 3, 2> in types and <"C", 2, 3> in types then
      Exclude (~types, <"C", 2, 3>);
   end if;

end procedure;

RemoveSome := function (types, ns, orders)
   if ns eq 7 and not 6 in orders then
      ns := 0;
   end if;
   if ns eq 9 then
      if 15 in orders then
         // Exclude (~types, "U_4 ( 3 )");
         if #types ne 0 then Exclude (~types, "<2A, 3, 3>"); end if;
      else ns := 0;
      end if;
   end if;
   if ns ge 19 then
      if not orders subset {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 
         13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 28, 30, 33, 35} then
         // Exclude (~types, "2E_6 ( 2 )");
         if #types ne 0 then Exclude (~types, <"2E", 6, 2^2>); end if;
      end if;
   end if;
   return types, ns;
end function; // RemoveSome

DegreeAlternating := function (orders)
   degrees := {}; primes := {};
   for m in orders do 
      if m gt 1 then
         f := Factorization (m);
         n := &+[i[1]^i[2]: i in f];
         if f[1][1] eq 2 then n +:= 2; end if;
         Include (~degrees, n);
         primes join:= {i[1] : i in f};
      end if; 
   end for;
   return degrees, primes;
end function; // DegreeAlternating

RecognizeAlternating := function (orders)

   degrees, primes := DegreeAlternating (orders);
   if #degrees eq 0 then return "unknown"; end if;

   mindeg := Maximum (degrees); // minimal possible degree
   
   p1 := PreviousPrime (mindeg + 1);
   p2 := PreviousPrime (p1);
   if not p1 in primes or not p2 in primes then
      return 0;
   end if;
   if mindeg mod 2 eq 1 then
      if not {mindeg, mindeg - 2} subset orders then return 0; end if;
   else
      if not mindeg - 1 in orders then return 0; end if;
   end if;
   
   for i in [3..Minimum (mindeg div 2 - 1, 6)] do
      if IsPrime (i) and IsPrime (mindeg - i) then
         if not i * (mindeg - i) in orders then
	   return 0;
	end if;
      elif IsPrime (i) and IsPrime (mindeg - i -1) then
         if not i * (mindeg - i - 1) in orders then
	   return 0;
         end if;
      end if;
   end for;

   return mindeg;

end function; // RecognizeAlternating

RecogniseAlternating := RecognizeAlternating;

/* given a list of projective orders in a sporadic group, identify it */

RecognizeSporadic := function (orders)
   maxords := {i : i in orders |
               #{j: j in orders | j mod i eq 0} eq 1};
   spors := [* *];
   if maxords eq {5, 6, 8, 11} then
      Append (~spors, <18, 1, "M11">);
   end if;
   if maxords eq {6, 8, 10, 11} then
      Append (~spors, <18, 2, "M12">);
   end if;
   if maxords eq {5, 6, 7, 8, 11} then
      Append (~spors, <18, 3, "M22">);
   end if;
   if maxords subset {6, 8, 11, 14, 15, 23} 
      and {11,14,15,23} subset maxords then
      Append (~spors, <18, 4, "M23">);
   end if;
   if maxords subset {8, 10, 11, 12, 14, 15, 21, 23} 
      and {11,21,23} subset maxords then
      Append (~spors, <18, 5, "M24">);
   end if;
   if maxords subset {6, 7, 10, 11, 15, 19} 
      and {11,15,19} subset maxords then
      Append (~spors, <18, 6, "J1">);
   end if;
   if maxords subset {7, 8, 10, 12, 15} 
      and {7,12,15} subset maxords then
      Append (~spors, <18, 8, "J2">);
   end if;
   if maxords subset {8, 9, 10, 12, 15, 17, 19} 
      and {15,17,19} subset maxords then
      Append (~spors, <18, 11, "J3">);
   end if;
   if maxords subset {7, 8, 10, 11, 12, 15, 20} 
      and {11,20} subset maxords then
      Append (~spors, <18, 7, "HS">);
   end if;
   if maxords subset {8, 9, 11, 12, 14, 30} 
      and {11,14,30} subset maxords then
      Append (~spors, <18, 9, "McL">);
   end if;
   if maxords subset {11, 13, 14, 15, 18, 20, 21, 24} 
      and {11,13} subset maxords then
      Append (~spors, <18, 10, "Suz">);
   end if;
   if maxords subset {14, 15, 16, 20, 24, 26, 29} 
      and {26,29} subset maxords then
      Append (~spors, <18, 20, "Ru">);
   end if;
   if maxords subset {14, 18, 20, 21, 22, 23, 24, 30} 
      and {22,23,24,30} subset maxords then
      Append (~spors, <18, 14, "Co3">);
   end if;
   if maxords subset {11, 16, 18, 20, 23, 24, 28, 30} 
      and {16,23,28,30} subset maxords then
      Append (~spors, <18, 13, "Co2">);
   end if;
   if maxords subset {16, 22, 23, 24, 26, 28, 33, 35, 36, 39, 40, 42, 60} 
      and {33,42} subset maxords then
      Append (~spors, <18, 12, "Co1">);
   end if;
   if maxords subset {11, 12, 15, 16, 19, 20, 28, 31 }
      and {19,28,31} subset maxords then
      Append (~spors, <18, 21, "ON">);
   end if;
   if maxords subset {13, 14, 16, 18, 20, 21, 22, 24, 30} 
      and {13,24,30} subset maxords then
      Append (~spors, <18, 16, "Fi22">);
   end if;
   if maxords subset {8, 10, 12, 15, 17, 21, 28 } 
      and {17,28} subset maxords then
      Append (~spors, <18, 15, "He">);
   end if;
   if maxords subset {18, 22, 24, 25, 28, 30, 31, 33, 37, 40, 42, 67 } 
      and {31,67} subset maxords then
      Append (~spors, <18, 19, "Ly">);
   end if;
   if maxords subset {16, 23, 24, 28, 29, 30, 31, 33, 35, 37, 40, 42, 43, 44, 66 } 
      and {37,43} subset maxords then
      Append (~spors, <18, 26, "J4">);
   end if;
   /* new cases added */
   if maxords subset {9, 12, 14, 19, 21, 22, 25, 30, 35, 40}
      and ({19} subset maxords or {22} subset maxords) then
      Append (~spors, <18, 23, "HN">);
   end if;
   if maxords subset {13, 14, 16, 17, 22, 23, 24, 26, 27, 28, 35, 36, 39, 42, 60 }    
      and {17,23} subset maxords then
      Append (~spors, <18, 17, "Fi23">);
   end if;
   if maxords subset {16, 17, 22, 23, 24, 26, 27, 28, 29, 33, 35, 36, 39, 42, 45, 60} 
      and {17,29} subset maxords then
      Append (~spors, <18, 18, "Fi24">);
   end if;
   if maxords subset {19, 20, 21, 24, 27, 28, 30, 31, 36, 39} and 
      {19,31,39} subset maxords then
      Append (~spors, <18, 22, "Th">);
   end if;
   return spors;  
end function; // RecognizeSporadic

RecogniseSporadic := RecognizeSporadic; 

IsGoodInput := function (G)

   /* replace G by successive terms of its derived series  
      until we obtain a perfect group; if there are more
      than 3 iterations, then we can conclude that
      G/Z (F^*(G)) is probably not almost simple */

   if IsProbablyPerfect (G) then return true, G; end if;

   limit := 0;
   repeat 
      limit +:= 1;
      vprint Identify: "Replace by derived group - iteration", limit;
//      G := DerivedGroupMonteCarlo (G);
G := MyDerivedSubgroup (G);
      if IsTrivial (G) then 
	  vprint Identify : "Group is not nearly simple"; 
          return false, _; 
      end if;
      good := IsProbablyPerfect (G);
   until good or limit eq 3; 

   if good then 
      return true, G; 
   else 
      vprint Identify: "G is probably not nearly simple";
      return false, _; 
   end if;
end function;

MySimpleGroupName := function (K: NumberRandom := NumberRandom, OmegaFactor := 20,
Perfect := false) 

   if IsTrivial (K) then return false, _; end if;

   // pick up easy case 
   // use this only for degree at least 9 -- avoid coincidence of names
   if Type (K) eq GrpMat and Degree (K) gt 8 and IsIrreducible (K) 
      and RecogniseClassical (K) cmpeq true then
      return true, [* ClassicalTypeToLieType (K) *];
   end if;

   if not Perfect then 
      flag, G0 := IsGoodInput (K);
      if flag eq false then return false, _; end if;
      if IsTrivial (G0) then return false, _; end if;
   else
      G0 := K;
   end if;

   P := RandomProcess (G0);

   d := Degree (G0);
   orders := {MyCentralOrder (G0, Random (P)) : i in [1..NumberRandom]};

   if Type (K) eq GrpMat then max := 2 * d; else max := 100; end if;
   types := {};
   p := LieCharacteristic (G0: Verify := false);
   if Type (p) eq RngIntElt then 
      vprint Identify: "Possible defining characteristic: ", p;
      flag, result := LieTypeOfCharpGroup (G0, p, orders: 
                      OmegaFactor := OmegaFactor, 
                      NumberRandom := Maximum (NumberRandom, max));
      if flag cmpeq true then 
         types := {result};
         vprint Identify: "Possible classical types are ", types;
      end if;
   end if;

   ns := RecognizeAlternating (orders);
   vprint Identify: "Possible alternating degrees are ", ns;

   if not (ns cmpeq "unknown") then 
      RemoveCoincidences (~types, ns);
   end if;
   types := SequenceToList (SetToSequence (types));

   if not (ns cmpeq "unknown") then 
      types, ns := RemoveSome (types, ns, orders);
      if ns ne 0 then Append (~types, <17, ns, 0>); end if;
   end if;

   spors := RecognizeSporadic (orders);
   vprint Identify: "Possible sporadic groups are ", spors;
   types cat:= spors;

   /* EOB: revision to LieCharacteristic to avoid RandomSchreier allows 
      certain chars to survive; Sp(4, 13) and Alt(7) sometimes arise */
   t := [* <"C", 2, 13>, <17, 7, 0> *];
   if #[* x: x in t | Position (types, x) gt 0 *] eq 2 then
      if Maximum (orders) le 7 then 
         types:= [* x : x in types | not (x cmpeq <"C", 2, 13>) *];  
      else 
         types:= [* x : x in types | not (x cmpeq <17, 7, 0>) *];  
      end if;
   end if;

   if #types ge 1 then return true, types; end if;

   return false, _;
end function;

intrinsic SimpleGroupName (K:: GrpMat: Perfect := false, NumberRandom := 250, OmegaFactor := 20) -> BoolElt, List
{ If the input group is nearly simple, 
  return true and list of possible names for its non-abelian 
  composition factor, otherwise return false.
  If Perfect is true, then the algorithm assumes that G is perfect}
   flag, names := MySimpleGroupName (K: NumberRandom := NumberRandom, OmegaFactor := OmegaFactor, Perfect := Perfect);
   if flag then return flag, names; else return flag, _; end if;
end intrinsic;

intrinsic SimpleGroupName (K:: GrpPerm: Perfect := false, NumberRandom := 250) -> BoolElt, List
{ If the input group is nearly simple, 
  return true and list of possible names for its non-abelian 
  composition factor, otherwise return false.
  If Perfect is true, then the algorithm assumes that G is perfect}
   flag, names := MySimpleGroupName (K: NumberRandom := NumberRandom, Perfect := Perfect);
   if flag then return flag, names; else return flag, _; end if;
end intrinsic;
