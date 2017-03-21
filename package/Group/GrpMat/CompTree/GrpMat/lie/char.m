freeze;

/* implementation of algorithm of Liebeck and O'Brien to 
   determine characteristic of quasisimple group of Lie type;

   this version Oct 2011 */

declare verbose Characteristic, 1;

import "../../GrpMat/util/order.m": EstimateOrder;

forward MyNormalClosure;

/* given a direct product of a number of copies 
   of a simple group, construct one factor */

KillFactors := function (G : NumberTrials := 100)
  
   P := RandomProcess (G);

   trial := 0; 
   repeat 
      trial +:= 1;
      g := Random (P);
      n := Order (g);
      B := PrimeBasis (n);
      Exclude (~B, 2);
      if #B ne 0 then 
         p := Minimum (B);
         h := g^(n div p);
      end if;
   until (#B gt 0 and IsCentral (G, h) eq false) or (trial gt NumberTrials);

   if (trial gt NumberTrials) then error "Problem in KillFactors"; end if;

   trial := 0; 
   repeat 
      trial +:= 1;
      k := Random (P);
      m := (h, k);
   until (IsCentral (G, m) eq false) or (trial gt NumberTrials);

   if (trial gt NumberTrials) then error "Problem in KillFactors"; end if;

   return MyNormalClosure (G, m);
end function;

/* G is central product of at most 4 semisimple groups, 
   construct one factor */

OneFactor := function (G : Limit := 5)
   N := G;
   nmr := 1;
   repeat 
      N := KillFactors (N);
      nmr +:= 1;
   until nmr ge Limit; 
   return N;
end function;

/* two largest orders of elements of G */

TwoLargestOrders := function (G: NmrTries := 100)
   d := Degree (G);
   max := Type (G) eq GrpPerm select NmrTries else Maximum (d, NmrTries);
   P := RandomProcess (G);
   O := {CentralOrder (Random (P)): i in [1..max]};
   if #Set (O) le 1 then  
      // error "Problem in TwoLargestOrders"; 
      return false, [];
   end if;
   m := Maximum (O);
   Exclude (~O, m);
   s := Maximum (O);
   return true, [m, s];
end function; // TwoLargestOrders

/* is n a proper prime-power? */

MyIsPrimePower := function (n)
   flag, p, k := IsPrimePower (n);
   if flag and k gt 1 then return true, p, k; else return false, _, _; end if;
end function;

/* construct normal closure gens^G */

MyNormalClosure := function (G, gens: NumberOfElements := 10)
   L := Generic (G);
   N := sub <L | gens>;
   E := [NormalSubgroupRandomElement (G, N): i in [1..2 * NumberOfElements]];
   N := sub <L | gens, E>;
   P := RandomProcess (N);
   gens := [Random (P): i in [1..NumberOfElements]];
   return sub <L | gens>, P;
end function;

MyDerivedSubgroup := function (G: NumberOfElements := 10)
   gens := [G.i : i in [1..Ngens (G)]];
   gens := {(g, h): g in gens, h in gens};
   N, P := MyNormalClosure (G, gens: NumberOfElements:= NumberOfElements);
   return N, P;
end function;

/* perfect subgroup of G */

PerfectSubgroup := function (G : NumberRandom := 100)
   Number := 5;
   for i in [1..Number] do 
      G, P := MyDerivedSubgroup (G: NumberOfElements:= 10);
      if IsTrivial (G) then return G, P; end if;
   end for;
//   flag := IsProbablyPerfect (G: NumberRandom := 100 * Degree (G)); 
//   if not flag then return $$ (G); end if;
   return G, P;
end function;

/* construct non-central involution t in G */
NonCentralInvolution := function (G: NmrTries := 100)
   P := RandomProcess (G); 
  
   found := false;
   nmr := 0;
   repeat 
      f, h := RandomElementOfOrder (G, 2);
      if f eq true then 
         order := Order (h);
         t := h^(order div 2);
         found := not IsCentral (G, t); 
         nmr +:= 1;
      end if;
   until nmr eq NmrTries or found;

   // if nmr eq NmrTries then 
   if not found then 
      vprint Characteristic: "Failed to find non-central involution"; 
      return false, _; 
   end if;

   return true, t;

end function;

/* t is involution in G; construct K = C_G(t)^infty;
   construct normal closure of non-central element k 
   in K and decide if it is a 2-group */

EstimateO2 := function (G, t: NmrTries := 50)

   /* centraliser of t */
   C := CentraliserOfInvolution (G, t);
   vprint Characteristic: "Number of generators for centraliser is ", Ngens (C);

   K, P := PerfectSubgroup (C);

   /* if K = C^infty is trivial, then G is one of a small list
     of groups or is (P)SL(2, q), q odd */
   if IsTrivial (K) then 
      vprint Characteristic: "C^infty = 1, so G is on a list"; 
      return 1, _;
   end if;

   /* K = C^infty is non-trivial; construct normal closure
      of non-central involution k and decide if it 2-group */
   for i in [1..NmrTries] do 
      flag, k := NonCentralInvolution (K);
      if not flag then return 3, K; end if;
 
      N, P := MyNormalClosure (K, k);
 
      /* is N a 2-group? */
      nmr := 0;
      twogp := true; 
      repeat 
         x := Random (P);
         o := Order (x);
         if not IsPowerOf (o, 2) then 
            twogp := false;
         end if;
         nmr +:= 1;
      until nmr gt NmrTries or twogp eq false;

      if twogp then 
         vprint Characteristic: "O_2 is non-trivial, I = ", i; 
         return 2, K; 
      end if;
   end for;

   vprint Characteristic: "Failed to find non-trivial O_2";
   return 3, K;
end function;

intrinsic SL2Characteristic (H :: Grp: NumberRandom := 100, 
                              Verify := true) -> RngIntElt, RngIntElt 
{Monte Carlo algorithm to determine characteristic and field size of 
 quasisimple group having central quotient PSL(2, q); 
 if Verify then prove that H is perfect}

   if Verify then 
      require IsProbablyPerfect (H): "Input group must be perfect";
   end if;

   NumberTrials := 5; NmrElements := 100; 

   for i in [1..NumberTrials] do 

      flag, LargeOrders := TwoLargestOrders (H: NmrTries := i * NmrElements);
      L := {}; Q := {};
      if not flag then continue; end if;

      /* n is the largest order of element of (P)SL(2, q) */
      n := LargeOrders[1];

      /* m is the second largest order of element of (P)SL(2, q) */
      m := LargeOrders[2];

      /* n = q + 1? */
      if m + 2 eq n then 
         flag, p := MyIsPrimePower (n - 1);
         if flag then Include (~L, p); Include (~Q, n - 1); end if;
      end if;

      /* n = (q + 1) div 2? */
      if m + 1 eq n then 
         flag, p := IsPrimePower (2 * n - 1);
         if flag then Include (~L, p); Include (~Q, 2 * n - 1); end if;
      end if;

      /* p = q and n = p + 1 and m = p */
      if IsPrime (m) and n eq m + 1 then 
         Include (~L, m); Include (~Q, m);
      end if; 

      /* p = q and n = 2q */
      k := n div 2;
      if IsEven (n) and IsPrime (k) and 2 * (m - 1) eq n then 
         Include (~L, k); Include (~Q, k); 
      end if; 

      /* p = q and n = p + 1 and m = p - 1 */
      if IsPrime (m + 1) and n eq m + 2 then 
         Include (~L, n - 1); Include (~Q, n - 1);
      end if; 

      /* p = q and n = p */
      if IsPrime (n) and (2 * m - 1) eq n then 
         Include (~L, n);
         Include (~Q, n);
      end if; 

      /* PSL(2, 2) vs PSL (2, 3) vs SL(2, 3) */
      if LargeOrders eq [3, 2] then 
         if #H eq 6 then return 2, 2; else return 3, 3; end if;
      end if;
   
      /* SL(2, 4) = PSL(2, 4) = PSL(2, 5) */
/* 
      if LargeOrders eq [5, 3] then 
         if Type (H) eq GrpMat then
            F := BaseRing (H);
            flag, p := IsPrimePower (#F);
            if p eq 2 then 
               Exclude (~L, 5); Exclude (~Q, 5);
            else
               Exclude (~L, 2); Exclude (~Q, 4);
            end if;
         else 
            Exclude (~L, 2); Exclude (~Q, 4);
         end if;
*/
      if LargeOrders eq [5, 3] then 
         Exclude (~L, 2); Exclude (~Q, 4);
      end if;

      if #L eq 1 and #Q eq 1 then return Rep (L), Rep (Q); end if;
   end for;

   /* process the coincidences among number of form 
      (q - 1)/ 2 and primes which can occur for PSL;
      given relative proportions of elements in PSL, we 
      assume that (q - 1)/2 determines field size */

   if #L eq 2 then 
      X := SetToSequence (L);
      x := X[1]; y := X[2];  
      q := 2 * y + 1;
      flag, p, m := IsPrimePower (q);
      if flag and p eq x then return p, q; end if;
      x := X[2]; y := X[1];  
      q := 2 * y + 1;
      flag, p, m := IsPrimePower (q);
      if flag and p eq x then return p, q; end if;
   end if;
      
   return 0, 0;
   // if #L eq 0 then return 0, 0; else return L, Q; end if;
end intrinsic;

/* H has involution with soluble centraliser */

OldProcessList := function (H: LargeOrders := [])

   if #LargeOrders eq 0 then 
      flag, LargeOrders := TwoLargestOrders (H);
   end if;

   if flag eq false then return 0, _; end if;

   /* n is the largest order of element of (P)SL(2, q) */
   n := LargeOrders[1];

   /* list of maximal orders of elements for each simple group
      having soluble centraliser */

   if n in [

      /* for q = 2^i, i = 1..4 */
      /* L_2(q) */ 5, 9, 17,              /* q > 2 */
      /* L_3(q) */ 7, 73, 91,
      /* U_3(q) */ 4, 15, 21, 255,  
      /* Sp(4, q) */ 17, 65, 257,         /* q > 2 */
      /* 2B2(q) */ 13,                    /* q = 2^3 only */

      /* L(d, 2)  d = 4, 5, 6  */ 15, 31, 63,
      /* U(d, 2)  d = 4, 5, 6  */ 12, 18, 33,
      /* U(d, 2), d = 7, 8, 9  */ 66, 132, 132,
      /* Sp(d, 2) d = 6, 8, 10 */ 15, 30, 60,
      /* OmegaPlus (d, 2), d = 6, 8, 10 */ 15, 15, 60, 
      /* OmegaMinus (d, 2), d = 6, 8, 10 */ 12, 30, 35,
      /* 3D_4(2)  */ 28, 
      /* 2F_4(2)' */ 16, 
      /* F_4(2)   */ 30, 
      /* 2E_6(2)  */ 60, 
      /* char 3   */ 12, 13, 20] then 

      /*  the list of maximal orders includes
          some coincidences with (P)SL_2(q) --
          SL_2 for  q = 2^8, 2^6, 2^5, 2^4, 2^3; 
          SL_2 for  q = 3^3; 
          PSL_2 for q = 257, 5^3, 73, 31, 25, 17, 13, 7, 5 */

      HH := sub<Generic (H) | [H.i: i in [1..Ngens (H)]]>;
      if Type (HH) eq GrpMat then
         succeed := RandomSchreierBounded (HH, 10^7);
         if not succeed then 
            vprint Characteristic: "Failed in characteristic computation"; 
            return 0, []; 
         end if;
      else
         RandomSchreier (HH);
      end if;
     
      // Verify (HH);
      C := CompositionFactors (HH);

      vprint Characteristic: "Explicit computation completed";
      // if C[1] gt 2 then error "Input group is not quasisimple"; end if;

      if exists(c){c : c in C | c[1] in [1..16]} then 
         q := c[3];
         flag, p, e := IsPrimePower (q);
         return p;
      /* PSL(2, 4) = SL(2, 5) = Alt (5) */
      elif <17, 5, 0> in C then 
         return 5; 
      /* OmegaMinus (4, 3) = PSL(2, 9) = Alt (6) */
      elif <17, 6, 0> in C then 
         return 3; 
      /* OmegaPlus (6, 2) = SL(4, 2) = Alt (8) */
      elif <17, 8, 0> in C then 
         return 2; 
      else
         vprint Characteristic: "Composition factors are ", C;
         return 0, C;
         // error "Error in ProcessList"; 
      end if;
   else
      return SL2Characteristic (H: Verify := false);
   end if;
end function;

/* Version 1 from Bill: H has involution with soluble centraliser */

BillV1ProcessList := function (H: LargeOrders := [])

   if #LargeOrders eq 0 then
      flag, LargeOrders := TwoLargestOrders (H);
   end if;

   if flag eq false then return 0, _; end if;

    /* Unambiguous characteristic 2 */
   if LargeOrders in
    {
      [ 7, 5 ],		/* L(3,4) */
      [ 9, 7 ], 	/* L(2,8) */
      [ 15, 7 ],	/* L(2,8), L(4,2) */
      [ 15, 12 ],	/* S(6,2), O(8,2) */
      [ 15, 13 ],	/* U(3,4) */
      [ 16, 13 ],	/* 2F(4,2)' */
      [ 17, 15 ],	/* S(4,4) */
      [ 18, 15 ],	/* U(5,2), U(6,2) */
      [ 21, 19 ],	/* U(3,8) */
      [ 28, 21 ],	/* 3D(4,2) */
      [ 30, 21 ],	/* O(8,2) */
      [ 30, 24 ],	/* S(8,2) */
      [ 30, 28 ],	/* F(4,2) */
      [ 31, 21 ],	/* L(5,2) */
      [ 35, 33 ],	/* 2E(6,2) */
      [ 60, 51 ],	/* O(10,2) */
      [ 63, 31 ],	/* L(6,2) */
      [ 65, 63 ],	/* S(4,8) */
      [ 66, 63 ],	/* U(7,2) */
      [ 73, 63 ],	/* L(3,8) */
      [ 91, 85 ],	/* L(3,16) */
      [ 132, 129 ],	/* U(8,2), U(9,2) */
      [ 255, 241 ],	/* U(3,16) */
      [ 257, 255 ]	/* S(4,16) */
    } then return 2;
   end if;

    /* Unambiguous characteristic 3 */
   if LargeOrders in
    {
      [ 12, 8 ],	/* U(3,3) */
      [ 13, 8 ],	/* L(3,3) */
      [ 20, 13 ],	/* L(4,3) */
      [ 20, 18 ]	/* O(7,3), O+(8,3) */
    } then return 3;
   end if;

    /* cases with one group, but ambiguous characteristic, change at will */

    if LargeOrders eq [5,3] then return 5; end if; /* L(2,4) = L(2,5) */
    if LargeOrders eq [7,4] then return 7; end if; /* L(2,7) = L(3,2) */

    /* Two groups, one char 3, the other 2 and 3 */
    if LargeOrders eq [12, 9] then /* U(4,3) or U(4,2)=S(4,3) */
     /* Declare U(4,2)=S(4,3) to have char 3. This could be changed
      * with some extra work, as below ...*/
     return 3;
    end if;

   if LargeOrders eq [13, 7] then /* PSz(8) or PSL(2,13) */
    /* Two possible groups: use element orders to decide */
    P := RandomProcess(H);
    repeat
	ord := CentralOrder(Random(P) : Proof := true);
	if ord mod 3 eq 0 then return 13; end if;
	if ord in {4,5} then return 2; end if;
    until false;
   end if;

   if LargeOrders eq [13, 12] then /* PSL(2,25) or G(2,3) */
    /* Two possible groups: use element orders to decide */
    P := RandomProcess(H);
    repeat
	ord := CentralOrder(Random(P) : Proof := true);
	if ord eq 5 then return 5; end if;
	if ord in {7,8,9} then return 3; end if;
    until false;
   end if;

   return SL2Characteristic (H: Verify := false);

end function;

/* Version 2 from Bill: H has involution with soluble centraliser */

ProcessList := function (H: LargeOrders := [])

   if #LargeOrders eq 0 then
      flag, LargeOrders := TwoLargestOrders (H);
   end if;

   if flag eq false then return 0, _; end if;

    /* Unambiguous characteristic 2 */
   if LargeOrders in
    {
      [ 7, 5 ],         /* L(3,4) */
      [ 9, 7 ],         /* L(2,8) */
      [ 15, 7 ],        /* L(4,2) */
      [ 15, 12 ],       /* S(6,2), O+(8,2) */
      [ 15, 13 ],       /* U(3,4) */
      [ 16, 13 ],       /* 2F(4,2)' */
      [ 17, 15 ],       /* S(4,4), L(2,16) */
      [ 18, 15 ],       /* U(5,2), U(6,2) */
      [ 21, 19 ],       /* U(3,8) */
      [ 28, 21 ],       /* 3D(4,2) */
      [ 30, 21 ],       /* O-(8,2) */
      [ 30, 24 ],       /* S(8,2) */
      [ 30, 28 ],       /* F(4,2) */
      [ 31, 21 ],       /* L(5,2) */
      [ 35, 33 ],       /* 2E(6,2), O-(10,2) */
      [ 60, 51 ],       /* S(10,2), O+(10,2) */
      [ 63, 31 ],       /* L(6,2) */
      [ 65, 63 ],       /* S(4,8) */
      [ 66, 63 ],       /* U(7,2) */
      [ 73, 63 ],       /* L(3,8) */
      [ 91, 85 ],       /* L(3,16) */
      [ 132, 129 ],     /* U(8,2), U(9,2) */
      [ 255, 241 ],     /* U(3,16) */
      [ 257, 255 ]      /* S(4,16) */
    } then return 2;
   end if;

    /* Unambiguous characteristic 3 */
   if LargeOrders in
    {
      [ 12, 8 ],        /* U(3,3) */
      [ 13, 8 ],        /* L(3,3) */
      [ 20, 13 ],       /* L(4,3) */
      [ 20, 18 ]        /* O(7,3), O+(8,3) */
    } then return 3;
   end if;

    /* cases with one group, but ambiguous characteristic, change at will */

    if LargeOrders eq [5,3] then return 5; end if; /* L(2,4) = L(2,5) */
    if LargeOrders eq [7,4] then return 7; end if; /* L(2,7) = L(3,2) */

    /* Two groups, one char 3, the other 2 and 3 */
    if LargeOrders eq [12, 9] then /* U(4,3) or U(4,2)=S(4,3) */
     /* Declare U(4,2)=S(4,3) to have char 3. This could be changed
      * with some extra work, as below ...*/
     return 3;
    end if;

   if LargeOrders eq [13, 7] then /* PSz(8) or PSL(2,13) */
    /* Two possible groups: use element orders to decide */
    P := RandomProcess(H);
    repeat
        ord := CentralOrder(Random(P) : Proof := true);
        if ord mod 3 eq 0 then return 13; end if;
        if ord in {4,5} then return 2; end if;
    until false;
   end if;

   if LargeOrders eq [13, 12] then /* PSL(2,25) or G(2,3) */
    /* Two possible groups: use element orders to decide */
    P := RandomProcess(H);
    repeat
        ord := CentralOrder(Random(P) : Proof := true);
        if ord eq 5 then return 5; end if;
        if ord in {7,8,9} then return 3; end if;
    until false;
   end if;

   /* Tricky case where we need to fail */
   if LargeOrders eq [7,6] /* Alt(7) */ then
    return 0;
   end if;

   return SL2Characteristic (H: Verify := false);

end function;

/* C is C_G(t)^infty and is non-abelian */

OddChar := function (C: Centralize := true)
   repeat 
     C := OneFactor (C);
     M := C;
     flag, u := NonCentralInvolution (C);
     if not flag then 
         vprint Characteristic: "Believe C is SL(2, q) for q odd"; 
         return SL2Characteristic (C: Verify := false);
      else 
         /* centraliser of u */
         vprint Characteristic: "Iterating construction";
         C := CentraliserOfInvolution (C, u);
         C := PerfectSubgroup (C);
      end if;
   until IsTrivial (C);

   return ProcessList (M);
end function;

/* determine characteristic of quasisimple group of Lie type */

intrinsic LieCharacteristic (G :: Grp : NumberRandom := 100,
                                        Verify := true) -> RngIntElt
{Monte Carlo algorithm to determine characteristic of quasisimple 
 group of Lie type; if Verify then prove that G is perfect}


   require Type (G) eq GrpMat or Type (G) eq GrpPerm: 
      "Input must be matrix or permutation group";

   if Type (G) eq GrpMat then
	require Type(BaseRing(G)) eq FldFin:
	 "Input matrix group must be over a finite field";
   end if;

   if IsTrivial (G) then return false; end if;

   if Type (G) eq GrpMat and RecogniseClassical (G) cmpeq true then 
      return Characteristic (BaseRing (G));
   end if;

   if Verify then 
      require IsProbablyPerfect (G): "Input group must be perfect";
   end if;

   d := Degree (G);

   P := RandomProcess (G);
   max := Type (G) eq GrpPerm select NumberRandom else 
                                     Maximum (d, NumberRandom);

   S := [Random (P): i in [1..max]];

   Large := Type (G) eq GrpMat and (#BaseRing (G) gt 10^3) and (d gt 10);

   E := []; O := [];
   for i in [1..#S] do
      g := S[i];
      if Large then
         _, g, o := EstimateOrder (S[i]);
         // vprint Characteristic: "Estimate this case", o;
      else
         o := Order (S[i]);
      end if;
      if IsEven (o) then
         Append (~E, g);
         Append (~O, o);
      end if;
   end for;

   vprint Characteristic: "Number of even order elements found is ", #E;

   Factor := 10;
   if #E lt #S div Factor then 
      vprint Characteristic: "Conclude characteristic is 2"; return 2; 
   end if;

   Cinfty := sub<G|>;
   processed := {@ @};
   OnList := false;

   for i in [1..#E] do
      t := E[i]^(O[i] div 2);

      if IsCentral (G, t) or (t in processed) then continue; end if;

      if exists {x : x in processed | AreInvolutionsConjugate (G, t, x)} then 
         // "involution known already"; 
         continue; 
      end if;

      value, K := EstimateO2 (G, t);

      /* if 1 then G is on list or is PSL(2, q) for q odd */
      if value eq 1 then OnList := true; end if;

      // EOB change in strategy 8/2/2011: 
      // process other involutions before we process list 
/* 
      if value eq 1 then
         L := ProcessList (G);
         if L cmpeq 0 then 
            vprint Characteristic: "This group is probably not quasisimple"; 
            return false;
         end if;
         return L;
      end if;
*/
   
      /* if value is 2 then ncl<K | k> is 2-group for some non-central k in K */
      if value eq 2 then 
         vprint Characteristic: "Conclude characteristic is 2";
         return 2;
      end if;

      /* if value is 3 then ncl<K | k> is not 2-group 
         for some non-central k in K */

      Include (~processed, t);
      if #processed ge 5 then break; end if;
   end for;

   vprint Characteristic: "Number of involutions considered ", #processed;

   /* if no non-central involutions, then G is SL(2, q) for q odd */
   if #processed eq 0 then 
      vprint Characteristic: "Believe G is SL(2, q) for q odd"; 
      L := SL2Characteristic (G: Verify := false);
   elif OnList then
         L := ProcessList (G);
         if L cmpeq 0 then 
            vprint Characteristic: "This group is probably not quasisimple"; 
            return false;
         end if;
         return L;
   else 
      vprint Characteristic: "Believe characteristic is odd"; 
      L := OddChar (K); 
   end if;
   
   if L cmpeq 0 then 
      vprint Characteristic: "This group is probably not quasisimple"; 
      return false; 
   end if;

   return L; 
end intrinsic;
