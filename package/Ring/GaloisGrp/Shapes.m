freeze;

/* Shapes.m --- Auxiliary functions to deal with shapes.

   Functions in the file:

   IsSnAn(Patterns)                        -- Assuming the group to be transitive. 
                                              Returns  0 : nothing proven
                                                       1 : group contains A_n
                                                       2 : group contains S_n


   PowerPattern(pat,ex)                    -- Shape of ex-power of permutation with shape pat

   PossibleBlockSizes(Patterns)            -- Assuming the group to be transitive!
                                              Possible sizes of blocks in an blocksystem of a 
                                              permutation group with shapes in Patterns

   PossibleProperSubfieldDegrees(Patterns) -- Assuming the Patterns belong to a field
                                              i.e. assuming group is transitive!
                                              Possible numbers of blocks in a blocksystems in 
                                              case we have shapes as in Patterns

   DivisorOfGroupOrder(Patterns)           -- Assuming the group to be transitive!
                                              Factor of the group order proven by the given shapes.

   IsProbablyNormal(Patterns)              -- Assuming the Patterns belong to a field
                                              i.e. assuming group is transitive!
                                              true  : Field is probably normal 
                                                      i.e. group is probably given by regular representation
                                              false : Field proven not to be normal
                                                      i.e. group not given by regular representation

   ScCostEst(Pattern)                     --  A coarse estimate for the costs of the short cosets we have to
                                              deal with when starting from S_n with this pattern as known subgroup.

                                              1st return value: Estimated number of short cosets
                                              2nd return value: Degree of local splitting field
                                             
                                              A good choice is to minimize the product of the two numbers 
                                              times the degree of the prime you started with.   

   IsDoubleTransitive(Patterns)           --  Assuming the group to be transitive!
                                              returns true if group is proven to be 2-transitive.
                                              2nd returned value: Possible orbit-lengths of the 1-point 
                                                                  stabilizer on the n-1 remaining points.
 
   PossibleOrbitSizesOnTwoSets(Patterns)  --  Assuming the group to be transitive!
                                              returns a set of possible orbit-sizes of the action on 2-sets.
                                                                                                            
   IsEasySnAn(f)                          --  Quick test for A_n, S_n based on cycle types  

   */

intrinsic IsEasySnAn(f :: RngUPolElt: Trials := 50, AssumeIrreducibility := false) -> RngIntElt
{Test the Galois of f to be S_n or A_n. Returnvalue 1 : S_n proven, 2 : A_n proven, 0 : nothing proven.} 

 r := FieldOfFractions(BaseRing(Parent(f)));
 require r cmpeq Rationals() : "Rational polynomial expected.";

 if (not AssumeIrreducibility) and (not IsIrreducible(f)) then
  return 0;
 end if;

 if Degree(f) lt 3 then
  return 1;
 end if;
 if Degree(f) eq 3 then
  if IsSquare(Discriminant(f)) then return 2; else return 1; end if;
 end if;

 p := NextPrime(Degree(f));
 i := 0;
 HasOdd := false;
 HasLongPrimeCycle := false;
 HasExtra := (Degree(f) ne 6); // Degree 6 polynomial needs or testing 
 repeat
  suc, fp := IsCoercible(PolynomialRing(GF(p)),f);
  if Degree(fp) eq Degree(f) then
   fac := Factorization(fp);
   if {1} eq {a[2] : a in fac} then
    dl := [Degree(a[1]) : a in fac];
    HasOdd := HasOdd or (#[a : a in dl | a mod 2 eq 0] mod 2 eq 1);
    mm := Max(dl);
    HasExtra := HasExtra or (dl in [[1,2,3],[1,1,1,3], [2,4]]);
    if IsPrime(mm) then
     if Degree(f) in [4,5,6,7] and 2*mm gt Degree(f) and (mm lt Degree(f)) then HasLongPrimeCycle := true; end if;
     if Degree(f) eq 8 and mm eq 5 then HasLongPrimeCycle := true; end if;
     if Degree(f) gt 8 and (2*mm gt Degree(f)) and (mm lt Degree(f) - 2) then HasLongPrimeCycle := true; end if;
    end if;
   end if;
  end if;
  if  HasOdd and HasLongPrimeCycle and HasExtra then
   return 1;
  end if;
  p := NextPrime(p);
  i := i + 1;
 until (i gt Trials);

 if HasLongPrimeCycle and HasExtra then
  if IsSquare(Discriminant(f)) then return 2; else return 1; end if;
 end if;

 return 0; 
end intrinsic;

function ScCostEst(Pattern)
 a := Set(Pattern);
 return &*[Factorial(#[k : k in Pattern | k eq j])  : j in a] * &*Pattern div LCM(Pattern), LCM(Pattern);
end function;


// Given the cycle-pattern of a permutation, compute the pattern of its ex power.
function PowerPattern(pat,ex)
 
 gcd_l := [Gcd(a,ex) : a in pat];
 return Sort(&cat [[pat[i] div gcd_l[i] : j in [1..gcd_l[i]]  ] : i in [1..#pat]]);
end function;

/* Primitive double transitive groups, that are not detected as double transitive:
  9P3, 21P4, 25P12, 25P17, 25P20, 28P3, 28P4, 28P6, 49P22, 49P23, 49P29           */
function IsDoubleTransitive(Patterns)
 if #Patterns eq 0 then return false; end if;
 m := {&+a : a in Patterns};
 assert #m eq 1;
 n := Representative(m);
 if n le 2 then return true, {n-1}; end if;

// Generate shapes of the 1-point stabilizer:
 PatternsFP := { PowerPattern(p,ex) : ex in Set(p), p in Patterns | not 1 in p}
                 join {p : p in Patterns | 1 in p}; // use pattens with fixed points first.
 Patterns_PS := [ Exclude(p,1) : p in PatternsFP];

 o_kand := {1..n-1}; //possible sizes of orbits
 for a in Patterns_PS do
  sum_set := {0};
  for m in a do sum_set := sum_set join {m + a : a in sum_set}; end for;
  o_kand := o_kand meet sum_set;
  if o_kand eq {n-1} then return true,o_kand; end if;
 end for;
 
 return false, o_kand;
end function;

/* Groups, transitive in 2-sets we can not detect:
   9P3, 21P4,  25P12, 25P17, 25P20, 28P3, 28P4, 28P6, 49P22, 49P23, 49P29  */
function PossibleOrbitSizesOnTwoSets(Patterns)
 assert #Patterns gt 0;
 m := {&+a : a in Patterns};
 assert #m eq 1;
 n := Representative(m);
 if n eq 2 then return [1]; end if; 
 if n le 3 then return [3]; end if;

 dt, o_stab := IsDoubleTransitive(Patterns);
 if dt then
  return {n * (n-1) div 2};
 end if;

/* Orbit-lengths in 2-tuples are n*a where a is orbit-length of the 1-point stabilizer
   Projecting from 2-tupes to 2-sets may change by a factor of 2.                         */
 o_cand := { n*a : a in o_stab | 2*a le n-1} join {n*a div 2 : a in o_stab | n*a mod 2 eq 0};
 
/* Now we check up to what extend this is compatible with the shapes we see on 2-sets.
   I.E. we map the shapes to 2-sets.                                                      */  
 pat2 := {};
 for act in Patterns do
  act2 := [];
  for i := 1 to #act do
   if act[i] gt 1 then // Add all 2-set with 2 points in the cycle act[i]
    if act[i] mod 2 eq 1 then
     act2 := act2 cat [act[i] : j in [1..(act[i]-1) div 2]];
    else
//     act2 := act2 cat [act[i] : j in [1..(act[i] * (act[i]-1) - act[i] div 2) div (2*act)]];  
     act2 := act2 cat [act[i] : j in [1..(act[i]-2) div 2]];  
     Append(~act2,act[i] div 2); 
    end if;
   end if;
  end for; 
// 2-sets with one point in the orbit act[i] and one point in act[j]:
  for i := 1 to #act-1 do
   for j := i+1 to #act do
    ggt := Gcd(act[i],act[j]);
    lcm := act[i] * act[j] div ggt;
    act2 := act2 cat [lcm : j in [1..ggt]];
   end for;
  end for; 
  Include(~pat2,act2);
 end for;
 assert {&+a : a in pat2} eq {n*(n-1) div 2};
// pat2;
 
// o_cand_old := o_cand;
 for a in pat2 do
  s_set := {0};
  for b in a do s_set := s_set join {s+b : s in s_set}; end for; 
  o_cand := o_cand meet s_set;
 end for; 

/* if #o_cand_old ne #o_cand then
  "Improvement possilbe", o_cand, o_cand_old;
 end if; */
 
 return o_cand;
end function;

/* Pretest based on factorization patterns.
   Can we exclude some degrees for subfieds.

   Idea of the approach:
   - Subfields are related to block-systems
   - Fixed points lead to fixed blocks
   - Try to derive a contradiction to assumed block-sizes.
   (Similar to the first step of Juergens algorithm) */
// Given a set of factorization patterns of an irreducible polynomial f modulo various primes
// This function computes a list of possible sizes of block-systems of the Galois group
function PossibleBlockSizes(Patterns)
 ls := {&+a : a in Patterns};
 assert #ls eq 1; 
 n := Representative(ls);
 if IsPrime(n) then // No subfields possible
  return [], n;
 end if;

 Patterns := {a : a in Patterns | #Set(a) gt 1}; // need different cycles in a pattern to derive something
 di := Divisors(n);
 di := {a : a in di | not a in {1,n}};
 if #Patterns eq 0 then
  return Sort(SetToSequence(di)), n;
 end if;

// All patterns that are generated from the above
 PatternsFP := { PowerPattern(p,ex) : ex in Set(p), p in Patterns | not 1 in p}
                 join {p : p in Patterns | 1 in p}; // use pattens with fixed points first.
 

// 1st stage: A fixed point leads to a fixed block:
 for act in PatternsFP do
  e1 := Index(act,1);
  if e1 gt 0 then  // if we have a fixed point
   b := Remove(act,e1);
   s_sum := {1};
   for tmp in b do
    s_sum := s_sum join {tmp + c : c in s_sum};
   end for; 
// s_sum sizes of fixed sets that contain a fixed point
   di := di meet s_sum; // Only these can be block-sizes
   if #di eq 0 then return [],n; end if;
  end if;
 end for;

// 2nd stage: In case we have blocks consisting only of fixed points
 for act in PatternsFP do
  if Set(act) ne {1} then  
   m := Min({a : a in act | a gt 1});
   fc := #[a : a in act | a eq 1];
   di := {a : a in di | (a ge m) or (fc mod a eq 0)}; 
   if #di eq 0 then return [],n; end if;
  end if;
 end for;

/* 3rd stage: A prime number can only divide the group order in case 
              it is less or equal the block-size or the number of blocks. */
 grp_ord_fac := LCM([LCM(a) : a in Patterns]);
 pd := PrimeDivisors(grp_ord_fac) cat [1];
 p_max := Max(pd); 
 di := {a : a in di | (a ge p_max) or  (n div a ge p_max)};
 if #di eq 0 then return [],n; end if;


/* 4th stage: In case a prime divisor p of the group order is bigger than the block-size
              we have an orbit of blocks of length divisible by p. 
              I.e. total number of points on orbits of length multiple of p is divisible by the block-size.  */
 for p in pd do
  p_sums := {&+([b : b in a | b mod p eq 0] cat [0]) : a in Patterns};
  di := {a : a in di | (p le a) or (&and [s mod a eq 0 : s in p_sums])}; 
 end for; 
 if #di eq 0 then return [],n; end if;

/* 5th stage: If a cycle of prime length is longer than the number of blocks it must stabilize a block.
              Thus, it must be possilbe to complete the block by adding further orbits.   */
 
 for p in pd do
  if p gt (n div Max(di)) then
   for act in Patterns do
    if p in act then
     i0 := Index(act,p);
     sumset := {p};
     for j := 1 to #act do if j ne i0 then  sumset := sumset join {a + act[j] : a in sumset}; end if; end for;
     di := { a : a in di | ((n div a) ge p) or  (a in sumset)};
     if #di eq 0 then return [],n; end if;
    end if;
   end for;
  end if;
 end for;

/* 6th stage: The set of all pairs (i,j) with i,j in the same block is G-invariant.
              Thus, n * (Blocksize-1)/2 is an orbit-size of the corresponding wreath-product acting on s-sets 
 
 two_sets_olc := PossibleOrbitSizesOnPairs(Patterns); 
 di := {a : a in di | n*(a-1) div 2 in two_sets_olc}; 

 Does not help much!
*/

 return Sort(SetToSequence(di)),n;
end function;

// List of possible degrees of subfields is case we have the pattern-list Patterns modulo various primes
function PossibleProperSubfieldDegrees(Patterns)

 assert #Patterns gt 0;
 e1,e2 := PossibleBlockSizes(Patterns); 
 return Sort([e2 div a : a in e1]);
end function;

function IsSnAn(Patterns)  
 if #Patterns eq 0 then return 0; end if;
 m := {&+a : a in Patterns};
 assert #m eq 1;
 n := Representative(m);
 if n le 2 then return 2; end if;

 HasOdd := 1 in {#[j : j in a | j mod 2 eq 0] mod 2 : a in Patterns}; //Test for existence of an odd permutation

 if n eq 3 then
  if HasOdd then return 2; else return 1; end if;
 end if;

/* We test for
     n = 4: 3-cycle
     n = 5: 3-cycle
     n = 6: 5-cycle and [1,1,1,3] or [1,2,3] pattern
     n = 7: 5-cycle
     n > 7: p-cycle with n/2 < p < n - 2 e.g. n = 8/9: 5-cycle, n = 10..13 : 7-cycle */
 lim_up := (n ge 8) select (n - 3) else n-1;
 HasBigPrime :=  {0} ne { #[i : i in a | i gt (n div 2) and (i le lim_up) and  IsPrime(i)] : a in Patterns}; 
 if not HasBigPrime then return 0; end if;

 if n ne 6 then
  if HasOdd then return 2; else return 1; end if;
 end if;  

// case n = 6 remains
 p3 := {a : a in Patterns | 3 in a};
 if not (p3 subset {[3,3]}) then
  if HasOdd then return 2; else return 1; end if;
 end if;
 return 0;
end function;

intrinsic InternalDivisorOfGroupOrder(Patterns : Set) -> RngIntElt
{Divisor of order of Galois group of an irreducible polynomial with cycle types as in Patterns}
 if #Patterns eq 0 then return 1; end if;
 m := {&+a : a in Patterns};
 assert #m eq 1;
 n := Representative(m);
 p_seq := SetToSequence(Patterns);
 LCM_seq := [LCM(a) : a in p_seq];
 t3 := 1;
 for p := 1 to n do 
  if IsPrime(p) then
   if #{&+([b : b in p_seq[i] | b mod p eq 0] cat [0]) 
         : i in [1..#p_seq] | LCM_seq[i] mod p eq 0} gt 1 then
// More than a cyclic Sylow subgroup of order p!
    t3 := t3 * p^2;
   end if;
  end if;
 end for;
 t1 := LCM(LCM_seq);
 t2 := LCM([LCM(a) : a in Patterns | 1 in a] cat 
           [LCM(PowerPattern(a,ex)) : ex in SequenceToSet(a), a in Patterns | not 1 in a]);  
 return LCM([t1,n * t2,t3]); 
/* t1 factor of group order. 
   t2 factor of order of 1-point-stabilizer. (My interpretation of Juergens suggestion) */
end intrinsic;


function IsProbablyNormal(Patterns)  
 if #Patterns eq 0 then return true; end if;
 m := {&+a : a in Patterns};
 assert #m eq 1;

 return &and [ 1 eq #Set(a) : a in Patterns];
end function;

