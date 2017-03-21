freeze;
//

declare verbose GaloisInvarEnv, 2;
 
char_p_invars := true;
char_2_SD_invars := true;

import "Galois.m" : color_array, cheat, max_cost, MaxInnerInvar,
                    UseCache, CacheHasInvar, CachePutInvar, Classical,
                    get_tschirni_R, invar_coeff_ring;

import "Inv2.m" : IntransitiveSubgroupInv, FactorDeltaInv, FactorDeltaInvL, IntransitiveInvariant, 
                  CheapInvariantOnPairs, BlockTransferInv, BlockSimplifyInv, HardBlockSimplifyInv,
                  InvByCode, InvByF3Code, KernBlockInv5, Part4ToPart2Inv, PWPInv, SnMapedInv;


//color_array := [red, green, RED, blue, purple, BLUE, grey, normal];
red := color_array[1];
green := color_array[2];
RED := color_array[3];
blue := color_array[4];
purple := color_array[5];
BLUE := color_array[6];
grey := color_array[7];
normal := color_array[8];

// This is to make an integer slpoly into a non-integer slpoly
// Other uses of Evaluate attempt to reverse this
function SLPRGg(R, g)
    return Evaluate(g, [S.i : i in [1 .. Rank(Parent(g))]]) where S := SLPolynomialRing(R, Rank(Parent(g)) : Global);
    return SLPolynomialRing(R, Rank(Parent(g)) : Global)!g;
end function;

MaxWorklevel := 7;

function check(x, f, s:Sign)
//  "In check";
  // Cheat on the cheat for now, get around the char p coercion probs
  // Need to install homs for slpoly rings - another day
  if cheat then
    if Characteristic(Parent(f)) eq 0 then
	F := GF(NextPrime(2^30));
    else
	F := CoefficientRing(CoefficientRing(Parent(f)));
//	F := ext< F | Ceiling(Log(Characteristic(F), 2^30))>;
	F := quo<PolynomialRing(F) | RandomIrreduciblePolynomial(F, Ceiling(Log(Characteristic(F), 2^30)))>;
    end if;
    m := Coercion(CoefficientRing(Parent(f)), F);
//    "InCheck:", F;
    r := [Random(F) : i in [1..Degree(Parent(x))]];
    SLP := SLPolynomialRing(F, Rank(Parent(f)) : Global);
    if Sign then
      fl := Evaluate(f, r, m) eq -Evaluate(f, PermuteSequence(r, x), m);
    else
      fl := Evaluate(f, r, m) eq Evaluate(f, PermuteSequence(r, x), m);
    end if;
  else
    g := MultivariatePolynomial(f);
    if Sign then
      fl := -g eq g^x;
    else
      fl := g eq g^x;
    end if;
  end if;
 // "Checking ", s, ": ", fl;
  return fl;
end function;

procedure clear_attributes(G)
  return;
  for i in GetAttributes(Type(G)) do
    if assigned G``i then
      try
        delete G``i;
      catch e;
      end try;
    end if;
  end for;
end procedure;
 

intrinsic InternalTestBlockQuotients(G::GrpPerm,H::GrpPerm, B::GSet : InvarRing := Integers(), BQ_Worklevel := -1) ->BoolElt, HomGrp
{Tests, if there is a suitable quotient for which we can try to compute invariants}

  BB:=Representative(B);
  vprint Invariant, 3: "BlockQuotients of", BB, "in ", B;
  if #BB gt Maximum(10, Degree(G) div 2) then
    vprint Invariant, 3: "degree too large";
    return false, _;
  end if;
//  f, Im, ker:= BlocksAction(G, B);
  St:=Stabilizer(G,BB);
  f, g:=OrbitAction(St,BB);

//  G1:=Stabilizer(G,Random(BB));
//  [ <i@f, i> : i in BB];
//  [<i@@f, i> : i in [1..Degree(g)]];

// Trivial pre-test:
  if IsRegular(g) then // All BlockQuotients are E-cases.
     vprint Invariant, 3:"Block system skiped. Action restricted to one block is regular.";
     return false, _;
  end if;

  K2 := g;
  if BQ_Worklevel eq 1 then
   if IsOdd(Index(G,H)) then
    return false, _;
   end if;
   KK1 := Subgroups(K2:IndexEqual := 2, IsTransitive := true); 
   /* 1st try: Index-2-subgroups, that do not correspond to E-Invariants (an intransitive one, will have blocks as orbits) */
  else

   fac_ord := FactoredOrder(g);
   if #fac_ord gt 1 then
    KK1 := Subgroups(K2:IndexLimit := #BB-1);
   else
// Make more effort in the p-group case...

    if (BQ_Worklevel eq 2) and (Degree(g) le 4) then // No groups for BQ_Worklevel 2
     return false, _; 
    end if; 

    p := fac_ord[1][1];
    fac_deg := Factorization(Degree(g));
    sylow_ord :=  p^((p^(fac_deg[1][2] - 1)-1) div (p-1)); // Order of the p-Sylow subgroup in the largest S_n we want to map to.

    if Order(K2) le sylow_ord then // Faithful BlockQuotients of the action (restricted to a block) are possible.  
     start := sub<K2 | >;
    else
// Quotient of the action  (restricted to a block) has to have a kernel. 
// Idea: Find the largest normal subgroup that has to be in the kernel. 
//       Use the fact that a p-group with cyclic centre has a unique minimal normal subgroup.
// In case this kernel proves the impossiblity of a BlockQuotient invariant, we skip the block system.
// In case we find a non-trivial normal subgroup we speed the subgroup search by using the normal subgroup.
     pc,pi := PCGroup(K2);
     ucs := UpperCentralSeries(pc);
     ucs := [u : u in ucs | Order(u) * sylow_ord le Order(K2)];

     if #ucs gt 1 then 
// go upward in the lattice of normal subgroups as long as this is unique
      non_cyc := false;
      u_ns_l := [ucs[1]];
      k := 0;
      repeat
       k := k+1;
       if Index(ucs[k+1],ucs[k]) gt p then
        qq := quo<ucs[k+1] | ucs[k]>;
        non_cyc :=  not IsCyclic(qq);
       end if;
      until non_cyc or (k+2 gt #ucs);
      if non_cyc then
       start := ucs[k] @@ pi;
      else
       start := ucs[#ucs] @@ pi;
      end if;
     else
      start := sub<K2 | >;
     end if;    
    end if;

// All the permutation representations of K2 we want to inspect have start in the kernel. 
// Thus, we can make an early abort if this is to much.
    if Order(start) gt 1 then
     if #G eq #sub<G | H, Core(G,start @@ f)> then
// No block quotient map will show a difference of G and H
      vprint Invariant, 3:"Block system skiped by upper central series test.";
      return false,_;
     end if; 
// Compute only those subgroups that contain start.
     KK1 := Subgroups(K2,start:IndexLimit := #BB-1);
     KK1 := [a : a in KK1 | Order(a`subgroup) * #BB gt Order(K2)];
    else
     KK1 := Subgroups(K2:IndexLimit := #BB-1);
    end if;
   end if;
  

   if BQ_Worklevel eq 2 then
    KK1 := [u : u in KK1 | u`order * 2 lt Order(K2)]; /* 2nd try: Subgroups of Index > 2 */
   end if;
  end if;
 
  KK1 := [u`subgroup : u in KK1]; 

// Filter groups by comparing with cheap normal subgroups of K2
  if #KK1 gt 10 then
   der := DerivedSubgroup(K2);
   if #G eq #sub<G | H, Core(G,der @@ f)> then
     KK1 := [u : u in KK1 | not der subset u];
   end if; 
  end if;
 
  if #KK1 eq 0 then
    vprint Invariant, 3: "no subgroups";
    return false, _;
  end if;

  index_l := [ Index(K2,u) : u in KK1];
  ParallelSort(~index_l, ~KK1);
 
  for sK1 in KK1 do
    K1 := sK1;
    assert K1 subset K2;
    if K1 eq K2 then
      vprint Invariant, 3: "eq, bad choice";
      continue sK1;
    end if;

    UU:=K1 @@ f;

    c_hom := CosetAction(G,UU);
    if #c_hom(G) eq #c_hom(H) then 
      vprint Invariant, 3: "same coset image size, bad choice";
      continue sK1;
    end if;
 
    vprint Invariant, 2: "Doing block quotient. Block size",#BB,"new degree",Index(G,UU);
    vprint Invariant, 2: "Group orders",Order(G),Order(Image(c_hom));

    IndentPush();
    if IsMaximal(K2, K1) then
//      c, I_K2_K1 := GaloisGroupInvariant(InvarRing, K2, K1:DoCost, NoGeneric := Degree(K2) gt 8);
      c, I_K2_K1 := GaloisGroupInvariant(InvarRing, K2, K1:DoCost);
      if c cmpeq false then
        vprint Invariant, 2: "No invariant found - and degree too large for generic";
        IndentPop();
        clear_attributes(K2);
        clear_attributes(K1);
        continue;
      end if;
    else
      I_K2_K1 := RelativeInvariant(InvarRing, K2, K1:IsMaximal := false);
      c := NumberOfOperations(I_K2_K1, "*");
      I_K2_K1 := func<|I_K2_K1>;
    end if;
    IndentPop();

//    if c gt 10000 then
//      vprint Invariant, 3: "too expensive: cost=", c;
//      continue;
//    end if;
    I_K2_K1 := I_K2_K1();
    if Characteristic(Parent(I_K2_K1)) eq 0 then
	F := GF(NextPrime(2^22));
    else
	F := CoefficientRing(Parent(I_K2_K1));
	F := quo<F | RandomIrreduciblePolynomial(CoefficientRing(F), Ceiling(Log(Characteristic(F), 2^30)))>;
    end if;

    GG := c_hom(G);
    HH := c_hom(H);
    tr := [i @@ c_hom : i in Labelling(GG)]; 

//    if (not IsExport()) and (not IsTransitive(HH)) then     printf"Block-quotint with HH non-transitive\n";     end if;

    vprint Invariant, 3: "eq";
    if GG eq HH then
if not IsExport() then "How did we get here?"; end if;
      vprint Invariant, 3: "eq, pair is useless";
      continue;
    end if;
//    assert MyIsMaximal(GG, HH); Why? Recursive constructions might lead to non-maximal subgroups.
    vprint Invariant, 3: "get costs for F";
    IndentPush();
    C, F := GaloisGroupInvariant(InvarRing, GG, HH:DoCost);
    IndentPop();
    clear_attributes(GG);
    clear_attributes(HH);
    if C cmpeq false or C gt MaxInnerInvar then
      vprint Invariant, 3: "inner invar too expensive, ", 
                        C, ">", MaxInnerInvar;
      continue;
    end if;
    vprint Invariant, 3: "get F";
    IndentPush();
    F := F();
    IndentPop();

    R := SLPolynomialRing(BaseRing(Parent(I_K2_K1)), Degree(G) : Global);
    I_K2_K1 := Evaluate(I_K2_K1,[R.(i@@f) : i in Labelling(K1)]);
    
    vprint Invariant, 3: "start test";
 
    Zx := PolynomialRing(Integers());
    gen_G := [a : a in GeneratorsSequence(G) | not a in H];

// Try to use a BlockMarker instead of a general transformation first.
    BlockMarker := &+[R.(i@@f) : i in Orbits(K1)[1]];
    for tran := 1 to (IsTransitive(K1) select 2 else 3) do
     I_akt := I_K2_K1;
     case tran:
      when 2: I_akt := I_akt + BlockMarker;
      when 3: I_akt := I_akt * (1 + BlockMarker) + BlockMarker;
     end case;     
      I_K2_K1_orb := [Evaluate(I_akt,PermuteSequence([R.i : i in [1..Degree(G)]],s)) : s in tr]; 
      res := Evaluate(F,I_K2_K1_orb);
      if not &and [IsInvariant(SLPRGg(InvarRing, res), s) : s in gen_G] then
        assert forall(x){x : x in Generators(H) | IsInvariant(SLPRGg(InvarRing, res), x)};
        vprint Invariant, 3: "BQ: using BB:", BB, "of", B;    
        res`GalInvType := "BlockQuotient";
//        if (tran gt 1) and not IsExport() then       printf"Case %o of marking\n",tran;        end if;
        return true, res;
      end if;
    end for;
  
//    if not IsExport() then  printf"Using general tschirni\n"; end if;
    I_K2_K1_orb := [Evaluate(I_K2_K1,PermuteSequence([R.i : i in [1..Degree(G)]],s)) : s in tr]; 

    Zx := PolynomialRing(Integers());
    tschirni := Zx.1^2 + Zx.1 + 1;
    all_tschirni := {Zx.1 + 1, Zx.1, tschirni};
    repeat
      i := {@ Evaluate(tschirni, y) : y in I_K2_K1_orb @}; 
      if #i lt #tr then 
        g := SLPolynomialRing(Integers(), Degree(G) : Global)!0;
      else 
        assert #i eq #I_K2_K1_orb;
        g := Evaluate(F, Setseq(i));
      end if;
      g`GalInvType := "BlockQuotient";
      BlockQuotientInvar := g;
      assert assigned BlockQuotientInvar`GalInvType;
      if not &and [IsInvariant(SLPRGg(InvarRing, BlockQuotientInvar), s) : s in gen_G] then
        assert forall(x){x : x in Generators(H) | IsInvariant(SLPRGg(InvarRing, g), x)};
        vprint Invariant, 3: "BQ: using BB:", BB, "of", B;    
        return true, BlockQuotientInvar;
      else
        repeat
          tschirni := Polynomial([Random(5) : x in [1..Random(1+Max([Degree(f) : f in all_tschirni]))]] cat [1]);
        until (tschirni notin all_tschirni) and (Degree(tschirni) gt 0);
        Include(~all_tschirni, tschirni);
	if not IsExport() then
	    if #all_tschirni gt 50 then
	      error "too many tschirni's in invariant";
	    end if;
	end if;
      end if;
    until false;  
  end for;
  return false, _;
end intrinsic;

function GetInvar_8(G, H:DoCost:= false)
//intrinsic GetInvar_8(G::Grp, H::Grp:DoCost:= false) -> ., SeqEnum
//  {Compute a G-relative H-invariant polynomial (or s.th. similar?) and a Bound}
  // Step 8 (Algo 6.4?) of KG, p144  
//  "Compute invariants ", G, " in ", H;
//if H is maximal in G it is sufficient to check the condition
//for one g in G\H.

  R:=InvariantRing(H,Integers());

  S:={x: x in Generators(G) | not x in H};
  S:={Random(S)};// H maximal subgroup


//Compute minimal degree of the wanted invariant  (gal_inv_degree)
  n := Degree(G);
  max := n*(n-1) div 2;
  n := 0;
  repeat
    n +:= 10;             
    d:=Valuation(MolienSeriesApproximation(G, n) -
                 MolienSeriesApproximation(H, n));
  until d lt n;

  vprint Invariant, 1: "Degree(G)=",Degree(G), "Degree invariant=", d;

  if DoCost then
//JK: costs (d-1) * length of Orbit(O), where O is not known
//    and #O bounded by Minimum(H,Binomial(Degree(G)+d-1, Degree(G)-1))
    return Binomial(Degree(G)+d-1, Degree(G)-1);
  end if;

  if Binomial(Degree(G)+d-1, Degree(G)-1) gt max_cost then
     printf "Degree (Deg(G):%o, deg:%o) too big for generic invariant: Binom:%o\n", 
       Degree(G), d, Binomial(Degree(G)+d-1, d-1);
     error "stop here";
  end if;

  //If degree is too big do something special...

  vprint Invariant, 2: "Time for invariant...";
  vtime Invariant, 2: inv:=InvariantsOfDegree(R,d);
  for g in S do //for later purpose in loop...
    goodinvs:=[x: x in inv |x^g ne x];
  end for;
  min,pos:=Minimum([#Monomials(f): f in goodinvs]);//choose the smallest one...
  inv:=goodinvs[pos];

  return inv,[d,min];
end function;

// invariants:
// invariants are functions taking 1 argument. The argument can be
//  - a sequence of RngElt, in which case they are simply evaluated and
//    the result is returned
//  - an integer, in which case it is  interpreted as an upper
//    bounds for complex numbers that might be used in case 1.
//    A bound for the result is returned.
//  - a permutation. In which case a boolean is retunred indicating
//    wether the invariant is stable under p or not. Is Sign is true
//    we test if the permutation induces a sign change.
//  - the string "poly" in which case the polynomial is computed.  
//  - the string "cost" in which case the (approximate) number of
//    multiplications neccessary per evaluation is returned
//  - the string "print" in which case a "human readable form" is
//    returned as a string.
//  - the string "type" in which case the type of the invar is returned
//    (S1, S2, Sm, D, Generic, ...)
// 
// We have:
// - GenericInv
//   Created using GenericInvCreate(RngMPolElt)
// - SqrtDiscInv
// - Case3.1Inv
// - Case 3.2 Inv: D, S1, Sm, S2, DSm

function IntransitiveInvCreate(H : O := false)
  if O cmpeq false then
    O:=Orbit(H,1);
  end if;
  /* sum of variables indexed by i in O */
  S := SLPolynomialRing(Integers(), Degree(H) : Global);
  g := Zero(S);
  g := &+ [S.i : i in O];
  g`GalInvType := "Intransitive";
//"Creating Intransitive polynomial";
  return g;
end function;

function S1InnerProd(S, B, k, j)
    g := One(S);
    for b in B do 
	for r in b do
	    for s in b do
		if r lt s and (r ne k or s ne j) then
		    tmp := (S.r + S.s);
//"S1Inner", r, s, tmp;
		    g *:= tmp;
		end if;
	    end for;
	end for;
    end for;
    return g;
end function;

function SqrtDiscChar2Prod(S, i, j)
    g := One(S);
    n := Rank(S);
    for k in [1 .. n] do
	for l in [k + 1 .. n] do
	    if k ne i or l ne j then
		g *:= (S.k + S.l);
	    end if;
	end for;
    end for;
    return g;
end function;

function SqrtDiscInvChar2Old(n)
    S := SLPolynomialRing(Integers(), n : Global);
    g := Zero(S);
    for i in [1 .. n] do
	for j in [i + 1 .. n] do
	    g +:= S.i*SqrtDiscChar2Prod(S, i, j);
	end for;
    end for;
//"Constructed char 2 sqrt disc invar";
    return g;
end function;

function SqrtDiscInvCreate(n : Char2 := false)
//  "\n\nSqrtDiscInvCreate\n\n";
  S := SLPolynomialRing(Integers(), n : Global);
  if Char2 then
    part := [1,0];
    for i := 1 to n-1 do
	for j := i+1 to n do
	    part := [part[1] * S.i + part[2] * S.j, part[1] * S.j + part[2] * S.i];
	end for;
    end for;
    g := part[1];
      g`GalInvType := "SqrtDiscChar2";
  else
      g := SqrtDiscriminantPolynomial(S);
      g`GalInvType := "SqrtDisc";
  end if;
  return g;
end function;

function GenericInvCreate(S, G,H:DoCost := false)
//  "\n\nGenericInvCreate\n\n";
  
  if DoCost then
    return GetInvar_8(G, H:DoCost), func<|GenericInvCreate(S, G, H)>;
  end if;  
  if GetInvar_8(G, H:DoCost) gt max_cost then
  //if true or GetInvar_8(G, H:DoCost) gt max_cost then
    i := MyRelativeInvariant(S, G, H:IsMaximal);
    return InternalGalInvBuild(H, i);
  end if;  
  f, s := GetInvar_8(G,H:DoCost := DoCost);
  g := Evaluate(f, [S.i : i in [1 .. n]]) 
    where S is SLPolynomialRing(Integers(), n : Global) where n is Rank(Parent(f));
  if not assigned g`GalInvType then  
    g`GalInvType := "Generic-KG";
  end if;  
  return g;
end function;

function ProdSumInvCreate(p:Char2 := false)
//  "\n\nProdSumInv\n\n";
  S := SLPolynomialRing(Integers(), #p*#Representative(p) : Global);
  g := Zero(S);
  for s in p do
    gg := Zero(S);
    for y in s do
	gg +:= S.y;
    end for;
    if Char2 then
      g +:= gg^3; 
    else
      g +:= gg^2; 
    end if;
  end for;
  g`GalInvType := "ProdSum";
  return g;
end function;
   

function DInvCreate(B : Char2 := false)
if Char2 then
//"Constructed char 2 DInv";
end if;
  m := #B;
  l := #Representative(B);
  d := SqrtDiscInvCreate(m : Char2 := Char2);
  //"d:", d;
  n := l*m;
  // If d was an SLPoly (hopefully in the future) then Evaluate(d, G) should
  // give the poly for this function (in the universe of G for evaluating
  // at x)
  G := [ &+ [S.y : y in b] : b in B] where S is SLPolynomialRing(Integers(), n : Global);
//"Creating D polynomial";
  d := Evaluate(d, G);
  d`GalInvType := "DInv";
  return d;
end function;

function IsS1Invariant(G, B)
//B is a block system of G
  
//  f, Im, ker:=BlocksAction(G, B);
  BB:=Representative(B);
  S:=Stabilizer(G,BB); 
  SS:=OrbitImage(S,BB);

  return IsEven(SS);
end function;

function S1InvCreate(B : Char2 := false)
//  "\n\nS1Inv\n\n";
  m := #B;
  l := #Representative(B);
  n := l*m;
  if Char2 then
"Constructing S1Inv\n\n";
      S := SLPolynomialRing(Integers(), n : Global);
      g := Zero(S);
      for b in B do
	for k in b do
	    for j in b do
	      if j lt k then
		  tmp := S1InnerProd(S, B, k, j);
//j, k, tmp;
		  tmp *:= S.k;
//tmp;
		  g +:= tmp;
	      end if;
	    end for;
	  end for;
      end for;
g;
  else
      d := SqrtDiscInvCreate(l : Char2 := Char2);
      S := SLPolynomialRing(Integers(), m : Global);
      // Is there some evaluation of polys we can do here to get just one poly for
      // the function?
      g := S1(S);
    //"Creating S1 polynomial";
      g := Evaluate(g, [Evaluate(d, [S.y : y in b]) : b in B]) where S is SLPolynomialRing(Integers(), n : Global);
  end if;
  g`GalInvType := "S1Inv";
  return g;
end function;

function SmInvCreate(B : Char2 := false)
//  "\n\nSmInv\n\n";
if not false and Char2 then
  error "CAN'T USE THIS INVAR IN CHAR 2 : IT IS NOT POLYNOMIAL";
  return S1InvCreate(B : Char2);
end if;
if not IsExport() and Char2 then
"Sm Char 2 inv constructed";
end if;
  m := #B;
  l := #Representative(B);
  d := SqrtDiscInvCreate(l : Char2 := Char2);
  n := l*m;
  // As above, is there one polynomial?
  g := Sn(S) where S is SLPolynomialRing(Integers(), m : Global);
  g := Evaluate(g, [Evaluate(d, [S.y : y in b]) : b in B]) where S is SLPolynomialRing(Integers(), n : Global);
  g`GalInvType := "SmInv";
  return g;
end function;

function S2InvCreate(B,tau : Char2 := false)
//  "\n\nS2Inv\n\n";
  m := #B;
  mm2 := m*(m-1) div 2;
  l := #Representative(B);
  d := SqrtDiscInvCreate(l : Char2 := Char2);
  n := l*m;
  // As above, is there one polynomial?
  s2 := S2(S) where S is SLPolynomialRing(Integers(), m : Global);
//"Creating S2 polynomial";
  tt:=tau^-1;
  s2 := Evaluate(s2, [Evaluate(d, [S.(y^tt) : y in b]) : b in B]) where S is SLPolynomialRing(Integers(), n : Global);
  s2`GalInvType := "S2Inv";
  return s2;
end function;

function IsDInvariant(G, B)
//B is a block system of G
  
  _, Im, _:=BlocksAction(G, B);

  return IsEven(Im);
end function;

function IsOddPerm(B, gen)
//B is a block system of sorted blocks
  elt:=1;
  for BB in B do
    C:=BB^gen;
//    C,g:=Sort(C,func<a,b|a-b>);
    Sort(~C,~g);
    if IsOdd(g) then elt*:=-1;end if;
  end for;
  if elt eq 1 then return false;end if;

  return true;
end function;

function IsOddEvenPerm(B, gen)
//B is a block system of sorted blocks
//Checks if the induced action is even or odd for all blocks
  elt:=0;num:=0;
  for BB in B do
    C:=BB^gen;
//    C,g:=Sort(C,func<a,b|a-b>);
    Sort(~C,~g);
    if IsOdd(g) then elt+:=-1;else elt+:=1;end if;
    num+:=1;
    if num ne Abs(elt) then return false;end if;
  end for;

  return true;
end function;

/* under development
function IsSmInvariantGeneral(G, B, BB, GB, N)
//B is a block system of G
//BB is a block
//GB is the action of G on Stab_G(BB)|BB
//N is a normal subgroup of index 2
  
  R:=RightTransversal(G, Stabilizer(G, BB));
  B:=[Sort(SetToSequence(x)):x in B];
  for gen in Generators(G) do
    if IsOddPerm(B, gen) then return false; end if;
  end for;
  return true; 

end function;
*/
function IsSmInvariant(G, block)
//B is a block system of G
  
  B:=[Sort(SetToSequence(x)):x in block];
  for gen in Generators(G) do
    if IsOddPerm(B, gen) then return false; end if;
  end for;
  return true; 

end function;

function IsS2Invariant(G, block)
//B is a block system of G
  
  B:=[Sort(SetToSequence(x)):x in block];
  for gen in Generators(G) do
    if not IsOddEvenPerm(B, gen) then return false; end if;
  end for;
  return true; 

end function;

/*
function IsS2Invariant(G, B)
//B is a block system of G
  
//  f, Im, ker:=BlocksAction(G, B);
  BB:=Representative(B);
  S:=Stabilizer(G,BB);
  gen:=Generators(S); 
  SS:=[OrbitAction(S,BB) : BB in B];
  for g in gen do
    gg:={IsEven(f(g)): f in SS};
    if #gg gt 1 then 
       return false;
    end if;   
  end for;
  return true;
end function;
*/

function IsDSmInvariant(G, B)
//B is a block system of G

  Bs:=[Sort(SetToSequence(x)):x in B];
  f, Im, ker:=BlocksAction(G, B);

  gen:=Generators(G);
  for g in gen do
    H:=sub<G|g>;
    if IsEven(f(H)) xor (not IsOddPerm(Bs,g)) then
       return false;
    end if;
  end for;
  return true;
end function;

function DSmInvCreate(B : Char2 := false)
// SLPolys tested (4, 1) (6, 8) (8, 1)
//  "\n\nDSmInv\n\n";

  D := DInvCreate(B : Char2 := Char2);
  assert not Char2;
    Sm := SmInvCreate(B : Char2 := Char2);
  //"DSmInv", Sm,"D:", D;
  n := #B*#Representative(B);
  // If D and Sm are both polys then assign one polynomial as their product
//"Creating D*Sm polynomial";

  Sm := Parent(D)!Sm;
  D := D*Sm;
  D`GalInvType := "DSmInv";
  return D;
end function;

function EInvCreate(B, e)
//  "\n\nEInv\n\n";

  n := #B*#Representative(B);
  // What is e? function? polynomial? Invariant? 
  // Looking at print I think it is an invariant, in which case Evaluate(e, G)
  // would be the polynomial for this function when it becomes a poly.
//"Creating E polynomial";
  G := [ &+ [S.y : y in b] : b in B] where S is SLPolynomialRing(Integers(), n : Global);

  e := Evaluate(e, G);
  e`GalInvType := "EInv";
  return e;
end function;

function FInvCreate(C, f, S)
//  "\n\nFInv\n\n";

  // f looks like an invariant
  // C is a sequence of permutations
  // S is a sequence of indices?
  
  //Apply y to f?
  n := Degree(Universe(C));
  g := S1(SLPolynomialRing(Integers(), #C : Global));
  gg := Evaluate(g, [Evaluate(f, [y[i] : i in [1 .. n] | i in S] 
    where y := PermuteSequence(s, c)) : c in C]) 
      where s is [SL.i : i in [1 .. n]] 
        where SL := SLPolynomialRing(Integers(), n : Global);
  gg`GalInvType := "FInv";

//"Creating F polynomial";
  return gg;
end function;

function F1F2InvCreate(S, G, H1, H2:DoCost := false)
//  "\n\nF1F2Inv\n\n";


  if Characteristic(S`Base) eq 2 then
    error "bad!";
  end if;
  c1, i1 := GaloisGroupInvariant(invar_coeff_ring(S), G, H1:DoCost);
  s1 := RightTransversal(G, H1);
  s1 := [ x : x in s1 | x notin H1][1];
  i1 := i1();
  if check(s1, i1, "H1-test":Sign) then
    f1 := false;
  else 
    f1 := true;
  end if;
  c2, i2 := GaloisGroupInvariant(invar_coeff_ring(S), G, H2:DoCost);
  s2 := RightTransversal(G, H2);
  s2 := [ x : x in s2 | x notin H2][1];
  i2 := i2();
  if check(s2, i2, "H2-test":Sign) then
    f2 := false;
  else
    f2 := true;
  end if;
  vprint Invariant, 2: RED, "step 5.2 can be applied", normal;

  // i1 and i2 are invariants?

//"Creating F1F2 polynomial", f1, f2;
  if f1 and f2 then
    i1:= (i1 - Apply(s1, i1))* Parent(i1)!(i2 - Apply(s2, i2));
  elif f1 and not f2 then
    i1:= Parent(i2)!(i1 - Apply(s1, i1))* i2;
  elif not f1 and f2 then
    i1:= i1* Parent(i1)!(i2 - Apply(s2, i2));
  else 
    i1:= i1*Parent(i1)!i2;
  end if;
  i1`GalInvType := "F1F2Inv";
  if DoCost then
    return c1*(f1 select 2 else 1)+c2*(f2 select 2 else 1), func<|i1>;
  else
    return i1;
  end if;  
end function;

forward TestIndex2Subgroup;
function TestIndex2InternalSubgroupSum(G,H)
//intrinsic TestIndex2InternalSubgroupSum(G::GrpPerm,H::GrpPerm) -> BoolElt, GrpPerm,GrpPerm
//{Tests if H is the sum of two good subgroups}

   if #G ne #H *2 then
//     "not an index 2 subgroup AT ALL";
     return false, _, _;
   end if;
   if TestIndex2Subgroup(G,H) then 
//      "already realizable with special invariant";
      return false, _, _;
   end if;
   if assigned G`Sub2 then
      ss:=G`Sub2;
   else
      s:=MaximalSubgroups(G:IndexLimit:=2);
      s:=[x`subgroup:x in s|x`subgroup ne G];
      ss:=[x:x in s|TestIndex2Subgroup(G,x)];
      G`Sub2:=ss;
   end if;
   if #ss lt 2 then
     return false, _, _;
   end if;


   for HH in ss do
     H3:=InternalSubgroupSum(G,H,HH);
     if H3 in ss then
//     if TestIndex2Subgroup(G,H3) then
//        "H = H1 + H2 ";
        return true, HH, H3;
     end if;
   end for;
   return false, _, _;       
end function;

function TestIndex2Subgroup(G,H)
//intrinsic TestIndex2Subgroup(G::GrpPerm,H::GrpPerm) -> BoolElt
//{Tests, if a special invariant is applicable}
     if assigned G`Blocks then
        B_G:=G`Blocks;
     else
        B_G := {MinimalPartition(G: Block := x) : x in AllPartitions(G)};
        G`Blocks:=B_G;
     end if;
     ev:=IsEven(G);
     if not IsTransitive(H) then
        vprint Invariant, 3: "intransitive";
        return true;
     end if;
     if not ev and IsEven(H) then
        vprint Invariant, 3: "even";
        return true;
     end if;
     if #AllPartitions(H) gt #B_G then
        vprint Invariant, 3: "more blocks";
        return true;
     end if;

     for B in B_G do
       f, Im, ker:= BlocksAction(G, B);
       subG:=Im;
       subH:=f(H);
       if #subH ne #subG then
          vprint Invariant, 3: "subH differs";
          return true;
       end if;
       BB:=Representative(B);
       stab:=Stabilizer(G,BB);
       g:=OrbitAction(stab,BB);
       relG:=Image(g);
       stabH:=IntersectionWithNormalSubgroup(stab,H);
       relH:=g(stabH);
       if #relH ne #relG then
          vprint Invariant, 3: "relH differs";
          return true;
       end if;

// Test for D makes no sense since in this case
// subH <A_m, subG not => subH ne subG already tested...
/*    
       W:=InternalWreathProductD(B);
       if not G subset W and H subset W then
          vprint Invariant, 3: "D for ", Representative(B);
          return true;
       end if;
*/
/*
       W:=InternalWreathProductSm(B);
       if not G subset W and H subset W then
          vprint Invariant, 3: "Sm for ", Representative(B);
          return true;
       end if;
*/
       if not IsSmInvariant(G,B) and IsSmInvariant(H,B) then
          vprint Invariant, 3: "Sm for ", Representative(B);
          return true;
       end if;

//       W:=InternalWreathProductDSm(B);
//       if not G subset W and H subset W then
       if not IsDSmInvariant(G,B) and IsDSmInvariant(H,B) then
          vprint Invariant, 3: "DSm for ", Representative(B);
          return true;
       end if;
     end for;

   return false;
end function;


function OldIntransitiveInvariant(IR, G, H,DoCost, Worklevel, NoGeneric)
    o := Orbits(G);
    oH := Orbits(H);
    R := SLPolynomialRing(Integers(), Degree(G) : Global);

    best_I := false;
    for O in o do
      mg, g := OrbitAction(G, O);
      mh, h := OrbitAction(H, O);
      if h ne g then
        IndentPush();
        I := GaloisGroupInvariant(IR, g, h);
        IndentPop();
        I := Evaluate(I, [R.(i @@ mg) : i in [1..#O]]);
        if best_I cmpeq false then
          best_I := I;
        elif TotalDegreeAbstract(I) lt TotalDegreeAbstract(best_I) then
          best_I := I;
        end if;
      end if;
    end for;
    if best_I cmpne false then
      best_I`GalInvType := "IntransitiveOrbit";
      vprint Invariant, 1: RED, "Both intransitive, but orbit action different", normal;
      if DoCost then
        return NumberOfOperations(best_I, "*"), func<|best_I>;
      end if;
      return best_I;
    end if;

    vprint Invariant, 1: RED, "Both intransitive, translating to transitive", normal;
    np := Set(CartesianProduct(o));
    gs:= GSet(G, np, map<car<np, G> -> np| x:-><x[1][i]^x[2] : i in [1..#x[1]]>>);
    gs := Orbit(G, gs[1]);
    G_new := Action(G, gs);

    nG := Image(G_new);
    assert #nG eq #G;
    _, mnG := StandardGroup(nG);
    nG := mnG(nG);
    nH := mnG(G_new(H));
    assert IsMaximal(nG, nH);
    assert IsTransitive(nG);
    I  := GaloisGroupInvariant(IR, nG, nH: Worklevel := Worklevel);
    if I cmpeq false then
      return I, false;
    end if;
    cur_t := Polynomial([0,1]);
    all_t := {cur_t};
    tschirni_bound := IsExport() select 100 else 5;
    repeat
      nI := Evaluate(I, [Evaluate(cur_t, &+ [R.(x[i]) : i in [1..#o]]) : x in gs]);
      repeat 
        cur_t := get_tschirni_R(Integers(), Minimum(#all_t, 10), Random(#all_t) div 2 +2, all_t, I`GalInvType);
      until Degree(cur_t) ge 1 and not cur_t in all_t;
      Include(~all_t, cur_t);
      assert forall{x : x in Generators(H)| IsInvariant(SLPRGg(IR, nI), x)};
    until #all_t gt tschirni_bound or exists{x : x in Generators(G) | not IsInvariant(SLPRGg(IR, nI), x)};

    // Try some integer tschirnis first to keep invars over Z which map easier

    ChangeUniverse(~all_t, PolynomialRing(IR));
    RR := SLPolynomialRing(IR, Rank(R) : Global);
    while not exists{x : x in Generators(G) | not IsInvariant(SLPRGg(IR, nI), x)} do
      if #all_t gt 5000 then
	error "Too many transformations";
      end if;
      cur_t := get_tschirni_R(IR, Minimum(#all_t, 10), Random(#all_t) div 2 +1, all_t, I`GalInvType);
      Include(~all_t, cur_t);
if not IsExport() and IR cmpne Integers() then
"\n\n\n\n";
"non-export printing";
"DO WE GET HERE?";
Parent(cur_t);
R;
Parent(I);
"end ne";
"\n\n\n\n";
end if;
      nI := Evaluate(I, [Evaluate(cur_t, &+ [RR.(x[i]) : i in [1..#o]]) : x in gs]);
      nI := Evaluate(I, [Evaluate(cur_t, &+ [R.(x[i]) : i in [1..#o]]) : x in gs]);
      assert forall{x : x in Generators(H)| IsInvariant(SLPRGg(IR, nI), x)};
    end while;
      nIc := Evaluate(nI, [R.i : i in [1 .. Rank(R)]]);
      ic := Parent(nIc) cmpeq R;
    //ic, nIc := IsCoercible(R, nI);
    if ic then 
	nI := nIc;
    end if;
//    if not I`GalInvType in ["Intransitive", "ProdSum"] then
//     "Hard sub-direct product case";
//     TotalDegreeAbstract(nI), NumberOfOperations(nI,"*"), Rank(Parent(I)), I`GalInvType;
//    end if;
    nI`GalInvType := "IntransitiveMapped";
    if DoCost then
      return NumberOfOperations(nI, "*"), func<|nI>;
    else
      return nI;
    end if;
    if (Worklevel in {-1, 7}) and (not NoGeneric) then
      return GenericInvCreate(IR, G, H: DoCost := DoCost);
    else
      return false, false;
    end if;
end function;


// Needs changing to allow more fun:
// we need to have an invar environment (possibly S?)
// the GetInvar nedds to get a "Worklevel" indicating how much effort
// it should put into finding invariants
// The idea is to use this as follows:
// - for all subgroups U in L that needs processing try to find easy subgroups
//   (and their invariants) first
// - (do this with increasing WorkLevelLimit)
// - among those where invariants are known, start using them
// - WorkLevelLimit 1 should be only obvious invariants (mind, some are
// expensive to use and should therefore be deferred!)
// - WorkLevelLimit ? should then also try to combine already known invariants
// to get invariants for new subgroups (generailzes the Index2Sum)
// We'll see...
//

// The cost of an invariant is difficult to assess. We distinguish two
// different factors:
// - cost of finding an invariant (Workload in GaloisGroupInvariant)
// - cost of applying an invariant which will be computed by
//   - cost of the invar (number of multiplications)
//   - the bound neccessary
//   The cost should be I("cost")*x*(Ilog2(x)+1) where x := Ilog2(B)+1;
//   of course, time #CosetsReps....
//   B is the Bound for a complex root evaluation, and the +1 is to avoid
//   having zeroes anywhere.
// Thus the cost of an invariant can increase if Tschirnhaus transformations
// are neccessary.
// The idea is to create an InvarEnv - which will be empty initially.
// Then one calls EnvNext to return the "cheapest" invariant for a missing
// group, if neccessary, calling GaloisGroupInvariant to compute an invariant.
// If Tschirnhaus transformations are neccessary, then the invariant can be
// returned to the environment, using the ChangeInvar call.
// The EnvNext should also see if invariants that are already known can
// produce new invariants.
AddAttribute(MakeType("GaloisData"), "InvEnv");  
InvEnv_fmt := recformat<L, Level : RngIntElt, 
                        MaxLevel,
                        I, T, M, U, C, G:GrpPerm, A, V,
                        P, G_nor:GrpPerm, AbQ, AbH, AbI, UseShort>;
// L: Eseq of groups
// I: the invariants for the groups
// T: the Tschirnhausesn trafo for the invar - if neccessary
// M: <c, b> number of multiplications, bound (-1 if not known)
// U: BoolElt to indicate if the invariant is already been used or not
// C: CosetReps for this descent
// P: List of pairs that have been checked for combination invariants
// V: BoolElt to indicate if this group has to be considered or not
// AbQ: Abelian quotient of G
// AbH: Projection to abelian quotient
// AbI: List of images of subgroups in the abelian quotient
// All list must have the same ordering!!!
// Level: the Worklevel used
// 
// G_nor: The Normalizer of G in S_n
// 
intrinsic InternalGaloisInvarEnvInit(S::GaloisData, G::GrpPerm, L::[GrpPerm]:MaxLevel := Infinity())
  {}

  if Characteristic(S`Base) eq 0 then
      Zx := PolynomialRing(Integers());  
      c := Integers;
  else
    if Type(S`Prime) eq RngUPolElt then
	Zx := PolynomialRing(Parent(S`Prime));
    else
	Zx := PolynomialRing(Parent(Minimum(S`Prime)));
    end if;
    c := Rationals;
  end if;
  assert assigned S`Type;
  assert assigned S`max_comp;

  S`InvEnv := rec<InvEnv_fmt | L := L, Level := 0, 
                               MaxLevel := MaxLevel,
                               I := [*false : i in L*],
                               T := [Zx|],
                               M := [car<Integers(), c()>|],
                               U := [ Booleans()| ],
                               C := [Parent([G.0])|],  
                               A := [Parent({Zx.1})|],  
                               P := [],  
                               V := [true : x in L],  
                               G := G,
                               UseShort := [true : x in L]  >;

  IR := invar_coeff_ring(S);
  if Characteristic(S`Base) eq 0 then
   il2 := Ilog2;
  else
   il2 := map<Rationals() -> Rationals() | x :-> x>;
  end if;

/* We use the abelian quotient to simplify the check for conjugacy in normalizer */
  S`InvEnv`AbQ, S`InvEnv`AbH := AbelianQuotient(G);
  S`InvEnv`AbI := [S`InvEnv`AbH(H) : H in L ];

  S`InvEnv`I := FactorDeltaInvL(G,L: Char2 := Characteristic(IR) eq 2); 


  for k := 1 to #L do
   if S`InvEnv`I[k] cmpne false then 
    b := InternalBound(S, Universe(S`InvEnv`T).1, S`InvEnv`I[k], 1);

    S`InvEnv`M[k] := <NumberOfOperations(S`InvEnv`I[k], "*"), il2(b + 1) + 1>;
    S`InvEnv`T[k] := Universe(S`InvEnv`T).1;
    S`InvEnv`U[k] := false;
    S`InvEnv`C[k] := [G|];
    S`InvEnv`A[k] := {};
   end if;
  end for; 

/* Combineing invariants has cubic time and quadratic memory complexity in the number of groups.
   We don't try it with to many groups.                           */
  if #L le 500 then 
// Combining two FactorDelta invariants is useless. FactorDeltaInvL did this alreaddy.
   S`InvEnv`P := [{i,j} : i,j in [1..#L] | (i lt j) and (S`InvEnv`I[i] cmpne false) and  (S`InvEnv`I[j] cmpne false)];
  else 
   vprint GaloisInvarEnv,2: "Number of subgroups is large. Switch CombineInvariants off."; 
   S`InvEnv`P := false;
  end if;

// Upper bound for the number of invariants that could be generated by using the normalizer.
  ord_rep := #[a : a in S`InvEnv`I | a cmpeq false] 
             - #{Order(L[i]) : i in [1..#L] | S`InvEnv`I[i] cmpeq false };   

  if (Degree(G) le 100) and (ord_rep ge 5) then 
// The normalizer might be helpfull, but only when it is not to costly and groups of equal order remain.
   vprint Invariant,2: "Computing Normalizer";
   S`InvEnv`G_nor := Normalizer(Sym(Degree(G)), G);
  else
   S`InvEnv`G_nor := G;
  end if;

end intrinsic;

intrinsic InternalGaloisInvarEnvClear(S::GaloisData)
  {Clear the environment - helps the memory management.}
  for i in S`InvEnv`L do
    clear_attributes(i);
  end for;
  clear_attributes(S`InvEnv`G);
  delete S`InvEnv;
end intrinsic;

intrinsic InternalGaloisInvarEnvGetRest(S::GaloisData) -> []
  {Returns the list of subgroups we haven't dealt with (yet)}
  I := S`InvEnv;  
  return [I`L[i] : i in [1..#I`L] | I`I[i] cmpeq false  or not I`U[i]];
end intrinsic;


intrinsic InternalGaloisInvarEnvSieve(S::GaloisData, F::UserProgram) 
  {}
  for i in [1..#S`InvEnv`L] do
    if S`InvEnv`V[i] then
      S`InvEnv`V[i] := F(S`InvEnv`L[i]);
    end if;
  end for;
end intrinsic;

intrinsic InternalGaloisInvarEnvNumber(S) -> RngIntElt 
  {}
  return #[x :x in S`InvEnv`V|x];
end intrinsic;

// It might happen, that several subgroups of G are conjugate in the normalizer of G but not in G
// In this case we can carry over the invariant easily.
// 
// We take all the data of the invariant enviornment and focus on the i-th subgroup
// We write all results in the environment.
// we return the number subgroups covered by the construction

// I_0 can be mapped to group j via tr
function AddConjugateInvariant(IR,S,j,I_0,tr, il2)
 I := Evaluate(I_0, [Parent(I_0).(k^tr) : k in [1..Rank(Parent(I_0))]]); 
 I`GalInvType := I_0`GalInvType;
 assert &and [IsInvariant(SLPRGg(IR,I),a) : a in GeneratorsSequence(S`InvEnv`L[j])];
 assert not &and [IsInvariant(SLPRGg(IR,I),a) : a in GeneratorsSequence(S`InvEnv`G)];
 S`InvEnv`I[j] := I;
 b := InternalBound(S, Universe(S`InvEnv`T).1, S`InvEnv`I[j], 1);
 S`InvEnv`M[j] := <NumberOfOperations(S`InvEnv`I[j], "*"), il2(b + 1) + 1>;
 S`InvEnv`T[j] := Universe(S`InvEnv`T).1;
 S`InvEnv`U[j] := false;
 S`InvEnv`C[j] := [S`InvEnv`G|];
 S`InvEnv`A[j] := {};
 return true;
end function;

function InvarCheckNormalizerOrbit(S,i)
 InvEnv := S`InvEnv;  
 G := InvEnv`G;
 H := InvEnv`L[i];
 assert InvEnv`I[i] cmpne false;
 I_0 := InvEnv`I[i];

 AbHom := InvEnv`AbH;

 G_nor := InvEnv`G_nor;

 cnt := 0;
 if (G_nor eq G) or IsNormal(G_nor, H) then // Normalizer will not join conjugacy class of H with other subgroupclasses in G.
  return cnt;
 end if;

 H_nor := Normalizer(G_nor, H);

 cl_G_H_size := IsNormal(G,H) select 1 else Index(G,H);

 if Index(G_nor,H_nor) le cl_G_H_size then return cnt; end if; 

 IR := invar_coeff_ring(S);
 if Characteristic(S`Base) eq 0 then
  il2 := Ilog2;
 else
  il2 := map<Rationals() -> Rationals() | x :-> x>;
 end if;

 if Kernel(AbHom) subset H then 
//  "Using Abelian Quotient";
  tr_nor := Transversal(G_nor,H_nor);
  orb_H := [AbHom(H^s) : s in tr_nor];
  orb_H_s := Set(orb_H);
  for j := 1 to #InvEnv`L do
   if (InvEnv`I[j] cmpeq false) and (Order(InvEnv`L[j]) eq Order(H)) then
    if InvEnv`AbI[j] in orb_H_s then
     _ := AddConjugateInvariant(IR, S,j,I_0, tr_nor[Index(orb_H, InvEnv`AbI[j])] , il2);
     cnt := cnt + 1;     
    end if;
   end if;
  end for;    
 else
  if cl_G_H_size lt 100 then // Enumerate the conjugacy class in the normalizer
   tr_nor := Transversal(G_nor,H_nor);
   orb_H := [H^s : s in tr_nor];
   orb_H_s := Set(orb_H);
//   "Using Transversal",#orb_H,cl_G_H_size;
   for j := 1 to #InvEnv`L do
    if (InvEnv`I[j] cmpeq false) and (Order(InvEnv`L[j]) eq Order(H)) then
     if InvEnv`L[j] in orb_H_s then
      _ := AddConjugateInvariant(IR, S,j,I_0, tr_nor[Index(orb_H, InvEnv`L[j])] , il2);
      cnt := cnt + 1;     
     end if;
    end if;
   end for;  
  else // Use IsConjugate
//   "Using IsConjugate";
   for j := 1 to #InvEnv`L do
    if (InvEnv`I[j] cmpeq false) and (Order(InvEnv`L[j]) eq Order(H)) then
     suc, tr := IsConjugate(G_nor, H, InvEnv`L[j]);
     if suc then
      _ := AddConjugateInvariant(IR, S,j,I_0,tr, il2);
      cnt := cnt + 1;
     end if;
    end if;
   end for;
  end if; 
 end if;

 if (GetVerbose("GaloisInvarEnv") ge 2) or (cnt gt 0 and GetVerbose("GaloisInvarEnv") ge 1) then 
  "Degree(G) =",Degree(G)," Order(G) =",Order(G)," #L =",#InvEnv`L,
  cnt,"new invariants by use of normalizer,",
  #[a : a in S`InvEnv`I | a cmpeq false],"missing invariants"; 
 end if;
 return cnt;
end function;


function AddInvariantsByCombine(S,IR,il2)

 G := S`InvEnv`G;
 L := S`InvEnv`L;
 M := S`InvEnv`M;
 V := S`InvEnv`V;


 c := [ <i, L[i]> : i in [1..#L] | IsDefined(M, i) and 
               NumberOfOperations(S`InvEnv`I[i], "*") lt 2000 and
               (IsNormal(G, L[i]) and Index(G, L[i]) lt 10 
                 or Index(G, L[i]) lt 5)];                        // Groups that have invariants that should be combined
 s := { {i[1],j[1]} : i, j in c | i ne j}; 
 R :=    SLPolynomialRing(Integers(), Degree(G) : Global);
 cnt := 0;
 cnt_new_inv := 0;
 pos_0 := [i : i in [1..#L] | not IsDefined(M, i) ];
 for p in s do
  if cnt ge #pos_0 div 2 then
   cnt_new_inv := cnt_new_inv + cnt;
   cnt := 0;
   pos_0 := [i : i in [1..#L] | not IsDefined(M, i) ];
   if #pos_0 eq 0 then break p; end if; // Nothing to do. All groups have invariants.
  end if;
  if not p in S`InvEnv`P then
//          "checking for combination", p;
   Append(~S`InvEnv`P, p);
   U := Core(G, L[x[1]] meet L[x[2]]) where x := [t : t in p];
   pos := [ i : i in pos_0 | U subset L[i] and IsNormal(G, L[i])];
   if #pos ne 0 then
//            "possibilities", pos;
    I := S`InvEnv`I;
    T := S`InvEnv`T;
    for k in pos do
     if S`InvEnv`I[k] cmpeq false then
      inv := CombineInvariants(IR, G, <L[i], I[i], T[i]>, <L[j], I[j], T[j]>, 
                                        L[k]) where i, j := Explode(SetToSequence(p));
      vprint Invariant, 2: "success", inv`GalInvType; 
      invc := Evaluate(inv, [R.i : i in [1 .. Rank(R)]]);
      ic := CoefficientRing(Parent(invc)) cmpeq Integers();
        //ic, invc  := IsCoercible(R, inv);
      if not ic then
       if not char_p_invars then  continue;       end if;
      else
       invc`GalInvType := inv`GalInvType;
       inv := invc;
      end if;
      S`InvEnv`I[k] := inv;
      assert assigned S`InvEnv`I[k]`GalInvType;
      b := InternalBound(S, Universe(S`InvEnv`T).1, inv, 1);
      S`InvEnv`M[k] := <NumberOfOperations(inv, "*"), il2(b + 1) + 1>;
      S`InvEnv`T[k] := Universe(S`InvEnv`T).1;
      S`InvEnv`U[k] := false;
      S`InvEnv`C[k] := [G|];
      S`InvEnv`A[k] := {};
/*
 // Compare Costs of combined invariant with direct computed one:
vgl := GaloisGroupInvariant(G,L[k]);
TotalDegreeAbstract(vgl), NumberOfOperations(vgl,"*");
TotalDegreeAbstract(invc), NumberOfOperations(invc,"*"); 
*/
      cnt := cnt + 1 + InvarCheckNormalizerOrbit(S,k);
     end if;
    end for;
   end if;
  else
//          "Pair", p, "already investigated";
  end if;
 end for;
/* 
if cnt + cnt_new_inv gt 0 then
 cnt + cnt_new_inv,"Invariants added by combine";
end if;
*/
 return cnt + cnt_new_inv;
end function;

function AddInvariantsByGalInv(S,IR,il2, _MaxWorklevel)
 L := S`InvEnv`L;
 V := S`InvEnv`V;
 G := S`InvEnv`G;
 cnt_new_inv := 0;

 for i in [1..#L] do
  if not IsDefined(S`InvEnv`M, i) and (V[i] or S`InvEnv`Level le 4) and (S`InvEnv`Level le _MaxWorklevel) then
   vprint GaloisInvarEnv, 2: 
           "computing invar for group", i, "at level", S`InvEnv`Level;

// FactorDelta code was already called in the initialization step of the environment       
   inv := GaloisGroupInvariant(IR, G, L[i] : Worklevel := S`InvEnv`Level, TryFactorDelta := false);
   if inv cmpne false then
    cnt_new_inv := cnt_new_inv + 1;
    assert assigned inv`GalInvType;
    vprint GaloisInvarEnv, 1: "success", inv`GalInvType;
    S`InvEnv`I[i] := inv;
    assert assigned S`InvEnv`I[i]`GalInvType;
    b := InternalBound(S, Universe(S`InvEnv`T).1, inv, 1);
    S`InvEnv`M[i] := <NumberOfOperations(inv, "*"), il2(b + 1) + 1>;
    S`InvEnv`T[i] := Universe(S`InvEnv`T).1;
    S`InvEnv`U[i] := false;
    S`InvEnv`C[i] := [G|];
    S`InvEnv`A[i] := {};

    cnt_new_inv := cnt_new_inv + InvarCheckNormalizerOrbit(S,i);
          
    if V[i] and (Classical or S`InvEnv`M[i][2] le 
                 S`InvEnv`Level^2*(il2(S`max_comp)+1)*Degree(S`InvEnv`G)+100) then
// "DECREMENT LEVEL", S`InvEnv`Level, S`InvEnv`M[i][2];
     S`InvEnv`Level -:= 1;    
     break; 
    end if;
   else
    vprint GaloisInvarEnv, 1: "nothing found";
   end if;
  else
   vprint GaloisInvarEnv, 2: "Invar for ", i, "of", #L, "already known";
  end if;
 end for;
 return cnt_new_inv;
end function;

intrinsic InternalHasGaloisInvarEnvNext(S::GaloisData) -> BoolElt, GrpPerm, RngSLPolElt, Tup
  {}
  InvEnv := S`InvEnv;  
  _MaxWorklevel := Minimum(MaxWorklevel, InvEnv`MaxLevel);
  G := InvEnv`G;
  L := InvEnv`L;
  V := InvEnv`V;
  IR := invar_coeff_ring(S);
    if Characteristic(S`Base) eq 0 then
	il2 := Ilog2;
    else
	il2 := map<Rationals() -> Rationals() | x :-> x>;
    end if;
  repeat
//"In loop with";
//#S`InvEnv`I;
//if #S`InvEnv`I ge 15 then
//TES(S`InvEnv`I[4]);
//end if;
    M := S`InvEnv`M;
    U := S`InvEnv`U;
    C := S`InvEnv`C;
//if #S`InvEnv`I eq 18 then
//TES(S`InvEnv`I[4]);
//end if;
    c := [<i, (#C[i] eq 0 select Index(G, L[i]) else  #C[i]) 
                 * M[i][1]*x*(il2(x)+1) where x := M[i][2],
                 M[i][1], M[i][2], S`InvEnv`I[i]`GalInvType> 
              : i in [1..#L] | IsDefined(M, i) and not U[i] and V[i]];
    if Classical and #c ne 0 then
      m := c[1][1];
      S`InvEnv`U[m] := true;
      vprint GaloisInvarEnv, 1: purple, "Working on group", m, "now", normal;
      return true, L[m], S`InvEnv`I[m], <S`InvEnv`T[m], C[m], S`InvEnv`A[m]>;
    elif #c ne 0 then
      Sort(~c, func<a,b|a[2]-b[2]>);
      if GetVerbose("GaloisInvarEnv") ge 1 then
        print "Invars and their costs:";
        print "\t", "<n, t, c, b, type>";
        for i := 1 to #c do
            print "\t", c[i];
        end for;
        print "n: number of subgroup";
        print "t: total cost for this invariant";
        print "c: number of mult. (without Tschirnhaus) for a single eval";
        print "b: bound on the complex size for a single eval without Tschirnhaus";
      end if;

      if c[1][2] gt S`InvEnv`Level^2*(il2(S`max_comp)+1)*Degree(S`InvEnv`G)+100 
         and
         S`InvEnv`Level lt _MaxWorklevel then
 if not IsExport() then
// "EXPENSIVE INVAR, level", S`InvEnv`Level, c[1][2];
 end if;
        vprint GaloisInvarEnv, 2: "Invars are all expensive, try next level";
      else
        m := c[1][1];
        S`InvEnv`U[m] := true;
        vprint GaloisInvarEnv, 1: purple, "Working on group", m, "now", normal;
        return true, L[m], S`InvEnv`I[m], <S`InvEnv`T[m], C[m], S`InvEnv`A[m]>;
      end if;
    end if;
    
    // depending on the level, we need to combine known invars here
    // TODO!
    S`InvEnv`Level +:= 1;
    if (S`InvEnv`Level gt 4) and (S`InvEnv`P cmpne false) then
     _ := AddInvariantsByCombine(S,IR,il2);
    end if;
    _ := AddInvariantsByGalInv(S,IR,il2, _MaxWorklevel);
  until S`InvEnv`Level gt _MaxWorklevel;
  return false, _, _, _;
end intrinsic;

intrinsic InternalGaloisInvarSetUseShort(S::GaloisData, I :: RngSLPolElt, use_short :: BoolElt)
{}
  for i in [1..#S`InvEnv`L] do
    if S`InvEnv`I[i] cmpne false and S`InvEnv`I[i] cmpeq I then
       S`InvEnv`UseShort[i] := use_short;
       return;
    end if;
  end for;
  error "Error: Unknown invariant passed in...";
end intrinsic;

intrinsic InternalGaloisInvarGetUseShort(S::GaloisData, I :: RngSLPolElt) -> BoolElt
{}
  for i in [1..#S`InvEnv`L] do
    if S`InvEnv`I[i] cmpne false and S`InvEnv`I[i] cmpeq I then
       return S`InvEnv`UseShort[i];
    end if;
  end for;
  error "Error: Unknown invariant passed in...";
end intrinsic;


intrinsic InternalGaloisInvarEnvChangeInvar(S::GaloisData, I::RngSLPolElt, T::RngUPolElt, C::[GrpPermElt], A::{RngUPolElt})
  {}
  for i in [1..#S`InvEnv`L] do
    if S`InvEnv`I[i] cmpne false and S`InvEnv`I[i] cmpeq I then
      S`InvEnv`T[i] := T;
      S`InvEnv`U[i] := false;
      S`InvEnv`C[i] := C;
      b := InternalBound(S, T, I, 1);
      if Characteristic(S`Base) eq 0 then
	  S`InvEnv`M[i] := <NumberOfOperations(I, "*"), Ilog2(b + 1) + 1>;
      else
	  S`InvEnv`M[i] := <NumberOfOperations(I, "*"), (b + 1) + 1>;
      end if;
      S`InvEnv`A[i] := A;
      return;
    end if;
  end for;
  error "Error: Unknown invariant passed in...";
end intrinsic;

intrinsic GaloisGroupInvariant(G::GrpPerm, H::GrpPerm:DoCost :=false, GalRel := false, Worklevel := -1, NoGeneric := false, TryFactorDelta := true) -> UserProgram
  {For a maximal subgroup H of the transitive group G, compute a G-relative H-invariant}
  return GaloisGroupInvariant(Integers(), G, H : DoCost := DoCost, GalRel := GalRel, Worklevel := Worklevel, NoGeneric := NoGeneric, TryFactorDelta := TryFactorDelta);
end intrinsic;

intrinsic GaloisGroupInvariant(IR::Rng, G::GrpPerm, H::GrpPerm:DoCost :=false, GalRel := false, Worklevel := -1, NoGeneric := false, TryFactorDelta := true) -> UserProgram
  {For a maximal subgroup H of the transitive group G, compute a G-relative H-invariant over the ring IR}
  //{Algo 6.24, p 143}
      //return GenericInvCreate(S, G, H);

    require IR cmpeq Integers() or (Type(IR) eq RngUPol and Type(CoefficientRing(IR)) eq FldFin) : "Argument 1 must be the integers or a polynomial ring over a finite field";

  Char2 := Characteristic(IR) eq 2;
  if GalRel then
    BB := Integers()`GalBlock;
    relG:=OrbitImage(Stabilizer(G,BB),BB);
    relH:=OrbitImage(Stabilizer(H,BB),BB);
    vprint Invariant, 1: BLUE, "GalRel:", 
                           RED, " step 4.1.4 can be applied", normal;
    if DoCost then
      IndentPush();
      c, f := GaloisGroupInvariant(IR, relG, relH:DoCost);
      IndentPop();
      // TODO: better cost function!
      f := func<|FInvCreate(RightTransversal(H, Stabilizer(H, BB)), f(), BB)>; 
      assert assigned f()`GalInvType;
      clear_attributes(relG);
      clear_attributes(relH);
      return 1+c, f;
    else
      IndentPush();
      I := GaloisGroupInvariant(IR, relG, relH);
      clear_attributes(relG);
      clear_attributes(relH);
      IndentPop();
      C := RightTransversal(H, Stabilizer(H,BB));
      F := FInvCreate(C, I, BB);
      if UseCache() then
        CachePutInvar(G, H, F);
      end if;
      assert assigned F()`GalInvType;
      return F;
    end if;
  end if;
  if not IsTransitive(G) then
    //Try to map to the transitive case...
    o := Orbits(G);
    oH := Orbits(H);
    R := SLPolynomialRing(Integers(), Degree(G) : Global);
    if exists(O){x : x in oH | not x in o} then
      vprint Invariant, 1: RED, "Both intransitive, but different orbits", normal;
      I := IntransitiveInvCreate(H : O := O);
      if DoCost then
        return NumberOfOperations(I, "*"), func<|I>;
      else
        return I;
      end if;
    end if;

    if TryFactorDelta then 
     inv := FactorDeltaInv(G,H:Char2 := Characteristic(IR) eq 2);
     if inv cmpne false then 
      vprint Invariant, 1: RED, "FactorDeltaInv", normal;
       if DoCost then
         return NumberOfOperations(inv, "*"), func<|inv>;
       end if;
      return inv; 
     end if; 
    end if; 

    inv, typ := IntransitiveInvariant(IR, G, H: TryFactorDelta := false);
    
    if inv cmpne false then
//     if not assigned inv`GalInvType then inv`GalInvType := "Other"; end if;
    
     vprint Invariant, 1: RED, "Intransitive invariant of type ", inv`GalInvType, normal;
     if DoCost then
        return NumberOfOperations(inv, "*"), func<|inv>;
     end if;
     return inv;
    end if;
    
    if not IsExport() then
     "Fail in IntransitiveInvariant, using old code";
    end if;
    return OldIntransitiveInvariant(IR, G, H,DoCost, Worklevel, NoGeneric);
  end if;
  assert H subset G;
  if UseCache() then
    f, i := CacheHasInvar(G, H);
    if f then
      if DoCost then
        return NumberOfOperations(i, "*"), func<|i>;
      else
	assert assigned i`GalInvType;
        return i;
      end if;
    end if;
  end if;

  // OK for char 2? : Yes
  if Worklevel in {-1, 1} and not IsTransitive(H) then
    vprint Invariant, 1: RED, "Intransitive", normal;
    if DoCost then
       return 0, func<|IntransitiveInvCreate(H)>;
    else
      return IntransitiveInvCreate(H);
    end if;
  end if;

//"Checking FactorDelta";
  if TryFactorDelta and Worklevel in {-1, 4} and IsEven(Index(G,H)) then
   inv := FactorDeltaInv(G,H:Char2 := Characteristic(IR) eq 2);
   if inv cmpne false then
    vprint Invariant, 1:RED, "FactorDelta used", normal;
    if UseCache() then
     CachePutInvar(G, H, inv);
    end if;
    if DoCost then
     return NumberOfOperations(inv,"*"),func<|inv>;
    else
     return inv;
    end if; 
   end if;
  end if;

  n := Degree(G);
  // Ok not for char 2
  if TryFactorDelta and Worklevel in {-1, 1} and IsEven(H) and not IsEven(G) and (char_2_SD_invars or not Char2) then 
    vprint Invariant, 1: RED, "SqrtDiscInvCreate", normal;
     if DoCost then
       // THIS COST WILL BE MORE IN CHAR 2?
       // SQUARE IT? SINCE EACH PRODUCT IS ONE LESS THAN
       // THE NON CHAR 2 CASE THEN MULTIPLY IN A VARIABKE
       // BUT THERE ARE THAT MANY TERMS IN EACH SUM
       return n*(n-1) div 2, func<|SqrtDiscInvCreate(Degree(G) : Char2 := Char2)>;
     else
       return SqrtDiscInvCreate(Degree(G) : Char2 := Char2); // and char ne 2
     end if;
  end if; 

  // Ok for char 2
  if Worklevel in {-1,5} and IsPrimitive(G) and IsPrimitive(H) then
    inv := IntransitiveSubgroupInv(IR, G, H);
    if inv cmpeq false then inv := CheapInvariantOnPairs(IR,G,H); end if;
    if not inv cmpeq false then
     if UseCache() then
        CachePutInvar(G, H, inv);
        assert assigned inv`GalInvType;
     end if;

     vprint Invariant, 1: RED, inv`GalInvType, normal;

     if DoCost then
        return NumberOfOperations(inv, "*"), func<|inv>;       
     end if;
     return inv;
    end if;
  end if;

  if Worklevel in {-1,6} and IsPrimitive(G) and IsPrimitive(H) then
    inv := PWPInv(IR, G, H);
    if inv cmpne false then vprint Invariant, 1: RED, "PWPInv", normal; end if;
    if inv cmpeq false then 
     inv := SnMapedInv(IR,G,H); 
     if inv cmpne false then vprint Invariant, 1: RED, "SnMapedInv", normal; end if;
    end if;
    if not inv cmpeq false then
     if UseCache() then
        CachePutInvar(G, H, inv);
        assert assigned inv`GalInvType;
     end if;
     if DoCost then
        return NumberOfOperations(inv, "*"), func<|inv>;       
     end if;
     return inv;
    end if;
  end if;


  if (Worklevel in {-1, 7}) and IsPrimitive(G) and IsPrimitive(H) and (not NoGeneric) then
    vprint Invariant, 1: RED, "GenericInv", normal;
    if UseCache() and not DoCost then
      g := GenericInvCreate(IR, G, H);
      CachePutInvar(G, H, g);
      assert assigned g`GalInvType;
      return g;
    end if;
    return GenericInvCreate(IR, G, H:DoCost := DoCost);
  end if;

//  vprint Invariant, 2: "Trying partitions";

  if (Worklevel in {-1, 1, 2, 3, 5}) and IsTransitive(H) then
    if assigned G`Blocks then
       B_G:=G`Blocks;
    else
      B_G := {MinimalPartition(G: Block := x) : x in AllPartitions(G)};
      G`Blocks:=B_G;
    end if;
    if assigned H`Blocks then
      B_H := H`Blocks;
    else
      B_H := {MinimalPartition(H: Block := x) : x in AllPartitions(H)};
      H`Blocks := B_H;
    end if;
  end if;

  // permutation thing!!!
  function check_invar(i)
    //"check_invar";
    if not forall(x){x : x in Generators(H) | IsInvariant(SLPRGg(IR, i), x)} then
      return false;
    end if;
    if not  exists(x){x : x in Generators(G) | not IsInvariant(SLPRGg(IR, i), x)} then
      return false;
    end if;
    assert H subset G;
    assert IsTransitive(H);
    assert IsTransitive(G);
    return true;
  end function;

  // char ne 2 assumed here.
  // char 2??? What's the problem - it is not Sqrt or Disc or minus!
  if Worklevel in {-1, 1} and IsTransitive(H) and exists(x) { x : x in B_H | x notin B_G} then
    vprint Invariant, 1: RED, "ProdSum", normal;
    if DoCost then
      return #x, func<|ProdSumInvCreate(x:Char2 := Char2)>;
    else
      g := ProdSumInvCreate(x:Char2 := Char2);
      assert assigned g`GalInvType;
      assert check_invar(g);
      if UseCache() then
        CachePutInvar(G, H, g);
      end if;
      return g;
    end if;
  end if;
  ind:=Index(G,H);


  if Worklevel in {-1, 2, 3} and IsTransitive(H) then
    for B in B_G do
      if #B eq 1 or #B eq Degree(G) then
        error "Error: should never happen";
        continue;
      end if; 
      m := #B;
      l := #Representative(B);

      // char 2 : these invariants need to be changed to use in char 2
      if Worklevel in {-1, 2, 3} and ind eq 2 and (char_2_SD_invars or not Char2) then
/*        W:=InternalWreathProductD(B);
        if not G subset W and H subset W then
*/
        if TryFactorDelta and not IsDInvariant(G, B) and IsDInvariant(H, B) then
          vprint Invariant, 1: RED, "Take special invariant D", normal;
          if DoCost then
            return #B*(#B-1) div 2, func<|DInvCreate(B : Char2 := Char2)>;
          else
            D := DInvCreate(B : Char2 := Char2);
            assert assigned D`GalInvType;
            if UseCache() then
              CachePutInvar(G, H, D);
            end if;
            return D;
          end if;
        end if; 

	//Turn off char 2 for now
        if TryFactorDelta and Worklevel in {-1, 3} and not IsSmInvariant(G, B) and IsSmInvariant(H, B) and (not true or not Char2) then
          vprint Invariant, 1: RED, "Take special invariant Sm", normal;
          if DoCost then
            assert check_invar(SmInvCreate(B : Char2 := Char2));
            return (#B-1)*l*(l-1) div 2, func<|SmInvCreate(B : Char2 := Char2)>;
          else
            Sm := SmInvCreate(B : Char2 := Char2);
            assert assigned Sm`GalInvType;
            if UseCache() then
              CachePutInvar(G, H, Sm);
            end if;
            return Sm;
          end if;
        end if; 

        if TryFactorDelta and Worklevel in {-1, 3} and not Char2 then
//          W:=InternalWreathProductDSm(B);
//          if not G subset W and H subset W then
//In Char 2 we might be DSmInvariant but we can let CombineInvariants handle
//this as we should have the 2 other invariants for the 2 other index
//subgroups
          if not IsDSmInvariant(G, B) and IsDSmInvariant(H, B) and not Char2 then
            vprint Invariant, 1: RED, "Take special invariant DSm", normal;
            if DoCost then
              assert check_invar(DSmInvCreate(B : Char2 := Char2));
              return 1+(#B*(#B-1) div 2)+(#B-1)*l*(l-1), func<|DSmInvCreate(B : Char2 := Char2)>;
            else
              DSm := DSmInvCreate(B : Char2 := Char2);
              assert assigned DSm`GalInvType;
              if UseCache() then
                CachePutInvar(G, H, DSm);
              end if;
              return DSm;
            end if;
          end if;
        end if;
      end if;//index 2 tests 

      if false and Worklevel in {-1, 3} and ind le 2^(#B) and (char_2_SD_invars or not Char2) then
//This test is equivalent to 4.1.4 + SqrtInvCreate
        if not IsS1Invariant(G, B) and IsS1Invariant(H, B) then
          W:=InternalWreathProductS1(B);
          U:=G meet W;        
          if U eq H then
             vprint Invariant, 1: RED, "Take special invariant S1", normal;
          elif IsConjugate(G,H,U) then
             Generators(G);Generators(H);B;
             error "Conjugated S1";
          else
             Generators(G);Generators(H);B;
             error "other S1 problem";
          end if;
          if DoCost then
            return l*(l-1) div 2,func<|S1InvCreate(B : Char2 := Char2)>;
          else
            S1 := S1InvCreate(B : Char2 := Char2);
            if UseCache() then
              CachePutInvar(G, H, S1);
            end if;
            return S1;
          end if;
        end if;
      end if;

// The direct S2Inv construction is not efficient. We let block-quotient do the job.
      if false and Worklevel in {-1, 3} and ind le 2^(#B-1) and (false and char_2_SD_invars or not Char2) then
  //The corresponding subgroup is not normal. Therefore we need to check if it
  //corresponds to a conjugate of the wanted subgroup
        if not IsS2Invariant(G, B) and IsS2Invariant(H, B) then
          W:=InternalWreathProductS2(B);
          U := G meet W;
          b,g:=IsConjugate(G,H,U);
          if b then
            vprint Invariant, 1: RED, "Take special invariant S2", normal;
            if DoCost then
              return #B*l*(l-1) div 2, func<|S2InvCreate(B,g : Char2 := Char2)>;
            else
              S2 := S2InvCreate(B,g : Char2 := Char2);
              assert assigned S2`GalInvType;
              if UseCache() then
                CachePutInvar(G, H, S2);
              end if;
              return S2;
            end if;
//          else
//            Generators(G);Generators(H);B;
//            print RED,  "Warning, Wrong S2 test!", normal;
          end if;
        end if;
      end if;   

    end for;
  end if; //Worklevel in {-1, 2, 3}


  //Start Step 4 of algorithm
  if Worklevel in {-1, 3} and IsTransitive(H) then
    for _B in B_G do
      m := #_B;
      l := #Representative(_B);
      B := [ x : x in _B]; 
      f, Im, ker:= BlocksAction(G, B);
      BB:=Representative(B);
      subG:=Im;
      subH:=f(H);
      
      if subH ne subG then //step 4.1.2
        //Compute subH-invariant subG relative polynomial E
        //return E(y_1,...,y_m)
        vprint Invariant, 1: RED, "step 4.1.2 can be applied", normal;
        if DoCost then
          IndentPush();
          c, f := GaloisGroupInvariant(IR, subG, subH:DoCost, TryFactorDelta := TryFactorDelta);
          IndentPop();
          f := func<|EInvCreate(B, f())>; // TODO: better cost function!
          assert check_invar(f());
          clear_attributes(subG);
          clear_attributes(subH);
          return 1+c, f;
        else
          IndentPush();
          I := GaloisGroupInvariant(IR, subG, subH: TryFactorDelta := TryFactorDelta );
          IndentPop();
          clear_attributes(subG);
          clear_attributes(subH);
          e := EInvCreate(B, I);
          assert assigned e`GalInvType;
          if UseCache() then
            CachePutInvar(G, H, e);
          end if;
          return e;
        end if;
      end if;

      relG:=OrbitImage(Stabilizer(G,BB),BB);
      relH:=OrbitImage(Stabilizer(H,BB),BB);
      
      if relH ne relG and IsMaximal(relG, relH) then 
        //Compute relH-invariant relG -relative polynomial F
        //compute sum sigma(F)...
        vprint Invariant, 1: RED, "step 4.1.4 can be applied", normal;
        if DoCost then
          IndentPush();
          c, f := GaloisGroupInvariant(IR, relG, relH:DoCost);
          clear_attributes(relG);
          clear_attributes(relH);
          IndentPop();
          f := func<|FInvCreate(RightTransversal(H, Stabilizer(H, BB)),
                              f(), BB)>; // TODO: better cost function!
          assert check_invar(f());                   
          return 1+c, f;
        else
          IndentPush();
          I := GaloisGroupInvariant(IR, relG, relH);
          IndentPop();
          clear_attributes(relG);
          clear_attributes(relH);
          C := RightTransversal(H, Stabilizer(H,BB));
          F := FInvCreate(C, I, BB);
          assert assigned F`GalInvType;
          if UseCache() then
            CachePutInvar(G, H, F);
          end if;
          return F;
        end if;
      end if;
    end for;
  end if; // Worklevel

  //Start Step 4.5 of algorithm
  if Worklevel in {-1, 3} and ind eq 2 and not Char2 then
    //currently(?) NOT implemented...
  end if;
  //Step 5...
  //char 2 : can this be adapted to work? Don't bother - fix Combine intrinsic

/*  Syntax of F1F2InvCreate has changed. This code does no longer work.

    if Worklevel in {-1, 4} and Classical and not Char2 then // possibly superflous.... (with new combination code)
    f, H1, H2 := TestIndex2InternalSubgroupSum(G, H);
    if f then
      "Worklevel 4 can make F1F2-invariant";
      vprint Invariant, 1: RED, "step 5.2 can be applied", normal;
      if DoCost then
        c, f := F1F2InvCreate(IR, G, H1, H2:DoCost := DoCost);
        assert check_invar(f());
        return c, f;
      else
        F :=  F1F2InvCreate(IR, G, H1, H2:DoCost := DoCost);
        if UseCache() then
          CachePutInvar(G, H, e);
        end if;
	assert assigned F`GalInvType;
        return F;
      end if;
    end if;
  end if; */

  if Worklevel in {-1, 5} and IsTransitive(H) and (#B_G gt 0) then
// Try Transfer
   i := false;
   for akt in B_G do
    i := BlockTransferInv(G,H, IR, akt, B_G);
    if i cmpne false then break akt; end if;
   end for;
   if i cmpne false then
    vprint Invariant, 1:RED, "Transfer used", normal;
    if UseCache() then
       CachePutInvar(G, H, i);
    end if;
    if DoCost then
       return NumberOfOperations(i, "*"), func<|i>;
    else
       assert assigned i`GalInvType;
       return i;
    end if;
   end if; 

// Try BlockQuotient
   f := false;
   for BQ_Level := 1 to 2 do
    for B in Sort([x : x in B_G | #Representative(x) gt 2], func<a,b|#b-#a>) do // Blocks of size 2 do not help
      f, i := InternalTestBlockQuotients(G, H, B : InvarRing := IR, BQ_Worklevel := BQ_Level); //TODO: use more
      if f then break; end if;            // sophisticated method here
    end for;
    if f then
      vprint Invariant, 1:RED, "BlockQuotients used", normal;
      if UseCache() then
        CachePutInvar(G, H, i);
      end if;
      if DoCost then
        return NumberOfOperations(i, "*"), func<|i>;
      else
        assert assigned i`GalInvType;
        return i;
      end if;
    end if;
   end for; 
  end if;

  if Worklevel in {-1, 6} and IsTransitive(H) then
   inv := CheapInvariantOnPairs(IR,G,H);
   if inv cmpeq false then inv := BlockSimplifyInv(IR,G,H);         end if;   
   if inv cmpeq false then inv := InvByCode(IR,G,H);                end if;
   if inv cmpeq false then inv := InvByF3Code(IR,G,H);              end if;
   if inv cmpeq false then inv := Part4ToPart2Inv(IR,G,H);          end if;
   if inv cmpeq false then inv := KernBlockInv5(IR,G,H);            end if;
   if inv cmpeq false then inv := HardBlockSimplifyInv(IR,G,H);     end if;
   if inv cmpne false then
//    if not assigned inv`GalInvType then inv`GalInvType := "Other"; end if;
    if DoCost then
      return NumberOfOperations(inv, "*"), func<|inv>; // BAD XXX
    else
      if UseCache() then
        CachePutInvar(G, H, inv);
      end if;
      return inv;
    end if;
   end if;
  end if;


  if Worklevel in {-1, 7} and not NoGeneric then
    vprint Invariant, 1: RED, "Generic Inv", normal;
    g := GenericInvCreate(IR, G, H);
    assert assigned g`GalInvType;
    if DoCost then
      return NumberOfOperations(g, "*"), func<|g>; // BAD XXX
    else
      if UseCache() then
        CachePutInvar(G, H, g);
      end if;
      return g;
    end if;
  end if;
  return false, false;
end intrinsic;

intrinsic IsInvariant(g::RngSLPolElt, perm::GrpPermElt : Sign := false) -> BoolElt
{Determine whether g is probably invariant under perm};

    if not assigned g`GalInvType then
      return check(perm, g, "" : Sign := Sign);
    end if;
    case g`GalInvType:
        when "SqrtDisc":
            if Sign then
                return IsOdd(perm);
            else
                return IsEven(perm);
            end if;
    end case;

    return check(perm, g, "" : Sign := Sign);

end intrinsic;

