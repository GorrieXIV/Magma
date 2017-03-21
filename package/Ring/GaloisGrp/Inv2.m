freeze;

/* Inv2.m 

   More special invariants - more fun with Galois groups.


Function to be called from this file:
=====================================

  FactorDeltaInv(G,H: Char2 := false)     
  FactorDeltaInvL(G,HL: Char2 := false)   -- Factor Delta invariant for a group and a list of subgroups.
                                             Does initialization only once.

  IntransitiveInvariant(IR,G,H:TryFactorDelta := true) -- General purpose code for intransitive groups. 


Functions for imprimitive groups (in case that ProdSum/E/F/block-quotient fails): (Try in the order as listed)
==============================================================================================================

  CheapInvariantOnPairs(IR,G,U)           -- Searches for new orbits an block-systems of the action on pairs.
                                             If exist: construct an invariant.

  BlockTransferInv(G,U, IR, akt_part, all_part)  -- simple invariant based on transfer to the block-stabilizer
                                                    In case action on one block is not cyclic we try 
                                                    an induction from subgroup level.
                                                    akt_part the block to which stabilizer we try to transfer to
                                                    all_part all partitions used for a final combine step

  BlockSimplifyInv(IR,g,h)     -- Try to find a subgroup with smaller group acting in one block. 
                                  Simplification of group is done by inspecting the derived subgroup.
                                  Lift invariant from subgroup level. 


  InvByCode(IR,g,h)            -- Similar to KernBlockInv5 but uses magmas coding theory (code over F_2)
                                  algorithms instead of a subgroup search.   
                                  ONLY for the case of a minimal partition with block size 2.

  InvByF3Code(IR,g,h)          -- Similar to InvByCode and KernBlockInv5 but uses codes over F_3 to find a starting point 
                                  for the transfer construction. 
                                  ONLY for the case of a block-system of block-size 3.

  Part4ToPart2Inv(IR,G,H)      -- Give a group with smallest block-size 4 searches for an odd index subgroup with block-size 2.
                                  Tries to lift invariant from subgroup-level.

  HardBlockSimplifyInv(IR,g,h) -- Similar to BlockSimplifyInv but uses LowIndexSubgroups. 
                                  Tested for the very few remaining cases up to degree 46. 
                           
  KernBlockInv5(IR,G,H)    -- Take a minimal partition and computes the action on it.
                              Searches for intransitive subgroups on the partitions.
                              Try to build an invariant by combining blocks-action and 
                              transfer to block-stabilizer.


For primitive groups:
=====================

  IntransitiveSubgroupInv(IR, G, H)      -- Searches for an intransitive subgroup U of H of low index. 
                                            In case that one orbit of U has an longer orbit under G than under H
                                            we get an invariant.

  PWPInv(IR, G, H)         -- Assuming that G is a primitive wreath product or something similar. 
                              Trys to map G to an imprimitive representation of smaller degree.
                              Constructs invariant for the image and maps it back. 
 
  SnMapedInv(IR, G, H)     -- Let G be the symmetric group acting on k-sets and H be the alternating group.
                              Constructs an invariant for this case.

You can also try: (see: Old_inv.m)
=================

  SmallerWreathProductInductionInv(IR, G, H, B_G) -- Trys to remove some extension of G and embed everything into a 
                                                     smaller wreath-product. B_G is a list of all block systems.


  TwoMinPartInv(IR, G,H)   -- Invariant in the case that G has 2 minimal partitions
                              The direct product of the block-actions defines an intransitive embeding of G.
                              This function applies IntransitiveInvariant to the image and then maps back.

  KernBlockInv4(IR,G,H)    -- Same as KernBlockInv5, but only the case of a minimal partition of 2 elements.
                              (Fast solution for most frequent special case. Now replaced by InvByCode)

  RemExtInv(IR,G,H)        -- Trys to remove some extensions from the groups G and H. Trys to find an invariant by 
                              hoping for a simpler setting on subgroup level.
 
   							 								*/


// import "GalInvar.m" : SLPRGg;
function SLPRGg(R, g)
    return Evaluate(g, [S.i : i in [1 .. Rank(Parent(g))]]) where S := SLPolynomialRing(R, Rank(Parent(g)) : Global);
end function;


// Kernel of the Transfer from g to u/ker. 
// assuming: u/ker cyclic
//           u subset g 
TransferKernel := function(g,u,ker)
 tran := SetToSequence(Transversal(g,u));
 tran_inv := [a^(-1) : a in tran];
 kg0 := [];

 verl_ziel, ver_pi := quo<u | ker>;

 k0 := sub<g | kg0>;
 bild_order := 1;
 repeat
  r := Random(g);  /* Compute the transfer image of r  */
  if not r in k0 then
   im_r := Identity(verl_ziel); /* Compute image successively in im_r */
   for i := 1 to #tran do
    j := 1; 
    rm1 := tran[i]*r;
    repeat
     rm2 := rm1 * tran_inv[j];
     j := j + 1;   
    until rm2 in u;
    im_r := im_r * ver_pi(rm2);
   end for; 
   if im_r eq Identity(verl_ziel) then
    Append(~kg0,r);
    k0 := sub<g | kg0>;
   end if;
   bild_order := LCM(Order(im_r), bild_order);  
  end if;
 until Order(k0) * bild_order eq Order(g);
 
 return k0;
end function;


function SnMapedInv(IR, g, h)
 if not IsTransitive(h) then return false; end if;
 if not IsPrimitive(h) then return false; end if;
 assert h subset g;
 if not Index(g,h) eq 2 then return false; end if;

 vprint Invariant,2: "Trying SnMapedInv";
 
 s1 := Stabilizer(g,1);
 orb := Orbits(s1);
 pl := [];
 for a in orb do
  phi := Action(s1,a);
  part := AllPartitions(Image(phi));
  for p in part do
   if #p eq (#a div 2) then 
    ker := TransferKernel(g,s1,Stabilizer(s1,p));  
    if ker eq h then
     pc := [i : i in a | not i in p];
     tr := Transversal(g,s1);
     rr := SLPolynomialRing(Integers(),Degree(g) : Global);
     if Characteristic(IR) ne 2 then
      inv := &*[&+[rr.(j^s) : j in p] - &+[rr.(j^s) : j in pc] : s in tr];
     else
      inv := [1, 0];
      for s in tr do
       fac := [&+[rr.(j^s) : j in p], &+[rr.(j^s) : j in pc]];
       inv := [inv[1] * fac[1] + inv[2] * fac[2], inv[1] * fac[2] + inv[2] * fac[1]];
      end for;
      inv := inv[1];
     end if;
     inv`GalInvType := "Other";
     assert &and [IsInvariant(inv,a) : a in GeneratorsSequence(h)];
     assert not &and [IsInvariant(inv,a) : a in GeneratorsSequence(g)];
     vprint Invariant,1:"Success in SnMapedInv";
     return inv;
    end if;
   end if;
  end for; 
 end for;
   
 vprint Invariant,2:"SnMapedInv failed!";
 return false;
end function;

/* Assuming g to be a primtive. (e.g., a primtive wreath product).
   Try to find a representation of smaller degree by use of the coset action on an intransitive subgroup. 
   Construct an invariant for the image and map it back.  */
PWPInv := function(IR,g,u)
 assert u subset g;
 if not IsTransitive(u) then return false; end if;
 if not IsPrimitive(u) then return false; end if;

 vprint Invariant,2 : "Trying PWPInv in degree",Degree(g);

 ugv := LowIndexSubgroups(g,Round(Sqrt(Degree(g))));
 ugv := [u : u in ugv | IsTransitive(u)];
 ugv := [u : u in ugv | not IsPrimitive(u)];
 if #ugv eq 0 then  vprint Invariant,2 : "failed!"; return false; end if;
 part_l := SetToSequence(&join [AllPartitions(u) : u in ugv]);
 orb_l := [Orbit(g,a) : a in part_l];
 orb_l := [a : a in orb_l | #a lt Degree(g)];
 if #orb_l eq 0 then vprint Invariant,2 : "failed!"; return false; end if;
 Sort(~orb_l,func<a,b| #a - #b>);

 for akt in orb_l do
  phi := Action(g,akt);
  if phi(g) ne phi(u) then
   std,pi := StandardGroup(phi(g));
   IndentPush();
   inv0 := GaloisGroupInvariant(IR,pi(phi(g)),pi(phi(u)));
   IndentPop();
   r0 := SLPolynomialRing(BaseRing(Parent(inv0)),Degree(g):Global);
   ex := 1;
   repeat 
    res := Evaluate(inv0,[&+[r0.j : j in a]^ex : a in Labelling(Image(phi))]); 
    assert &and [IsInvariant(SLPRGg(IR, res),a) : a in GeneratorsSequence(u)];     
    if not &and [IsInvariant(SLPRGg(IR,res),a) : a in GeneratorsSequence(g)] then 
     vprint Invariant,1 : "Success in PWPInv";
     res`GalInvType := "PrimitiveMapped";
     return res; 
    end if;
    ex := ex+1;
   until ex gt 5; 
   if not IsExport() then "Tschirni problem in PWPInv"; end if;
  end if;
 end for;
 vprint Invariant,2 : "failed!";
 return false;
end function;


/* Check for an intransitive subgroup of small index. One of its orbits might help. */
function IntransitiveSubgroupInv(IR, G, H)
 vprint Invariant,2 : "Trying IntransitiveSubgroupInv in degree",Degree(G);
 ugv := MaximalSubgroups(H: IsTransitive := false, IndexLimit := 2*Degree(G)^2);
 ugv := [u`subgroup : u in ugv];
 Sort(~ugv,func<a,b | Order(b) - Order(a)>);
 for i := 1 to #ugv do
  orbs := Orbits(ugv[i]);
  for akt in orbs do
   orb := Orbit(H, Set(akt));
   suc,orb2 := OrbitBounded(G, akt, #orb+2);
   if not suc or (#orb lt #orb2) then 
    R := SLPolynomialRing(Integers(),Degree(G):Global);
    ex := 1;
    repeat
     ex := ex + 1;
     inv := &+[ &+[R.j : j in mm]^ex : mm in orb ];
     if (not &and [IsInvariant(SLPRGg(IR, inv),a) : a in GeneratorsSequence(G)]) then
      assert  &and [IsInvariant(SLPRGg(IR, inv),a) : a in GeneratorsSequence(H)];
      inv`GalInvType := "SetOrbit";
      vprint Invariant,1 : "Success in IntransitiveSubgroupInv";
      return inv;
     end if;
     if ex ge #akt then
      inv := &+[ &*[R.j : j in mm] : mm in orb ];
      assert  &and [IsInvariant(SLPRGg(IR, inv),a) : a in GeneratorsSequence(H)];
      assert not &and [IsInvariant(SLPRGg(IR, inv),a) : a in GeneratorsSequence(G)];
      vprint Invariant,1 : "Success in IntransitiveSubgroupInv";
      inv`GalInvType := "SetOrbit";
      return inv; 
     end if;
    until false;
   end if;
  end for; 
 end for;
 vprint Invariant,2 : "failed!";
 return false;
end function;


/* Functions for FactorDeltaInv: */

/* Transfer to all conjugacy classes of 2-set stabilizers */
function RepL(G)
 if IsOdd(Order(G)) then return []; end if;

 if Transitivity(G) ge 2 then
  if IsEven(G) then
   return [];
  end if;
  ll := Labelling(G);
  return [<[[ ll[i], ll[j]] : i,j in [1..Degree(G)] | i lt j], G meet Alt(Degree(G)) >];
 end if;
 
 mp := MinimalPartitions(G);
 if #mp gt 1 then // More than one minimal partition: All the information is cheaper in the action on the blocks!
  return [];
 end if;
 if #mp eq 1 then
  pp := Representative(mp[1]);
  s2 := Subsets(pp,2); 
  orb2 := [];
  while #s2 gt 0 do
   a := Representative(s2);
   orb := Orbit(G,a);
   Append(~orb2,orb);
   s2 := {a : a in s2 | not a in orb};
  end while;
 else
  orb2 := Orbits(G,GSet(G,Subsets(Support(G),2)));
 end if;
 
 res := [];
 for a in orb2 do
  ind_l := [[Min(c),Max(c)] : c in a];
  chi := [ #[1 : a in ind_l | a[1]^G.jj gt a[2]^G.jj] mod 2 : jj in [1..Ngens(G)]]; 
  if Set(chi) ne {0} then
   Append(~res,<ind_l, Kernel(hom<G -> Sym(2) | [a eq 0 select Sym(2)![1,2] else Sym(2)![2,1] : a in chi]>)>);
  end if;
 end for;
 return res;
end function;

/* G transitive, collect representations constructable via action on block-systems */
function AllRepOrbit(G)

 part := SetToSequence(AllPartitions(G)) cat [{Representative(Labelling(G))}];
 
 res := [];
 for i := 1 to #part do
  orb := Orbit(G,part[i]);
  phi := Action(G,orb); 
  sg2,pi2 := StandardGroup(Image(phi));
  ll := Labelling(Image(phi));
  tmp := RepL(sg2); 
  for a in tmp do
   Append(~res,<[  [ ll[pp[1]] , ll[pp[2]] ]  : pp in a[1]] ,(phi^-1)((pi2^-1)(a[2]))>);
  end for;  
 end for;
 
 return res;
end function;

/* Collect all representations constructable via the action on orbits */
function AllRep(G)
 orb := Orbits(G);
 res := [];
 for a in orb do
  phi := Action(G,a);
  res := res cat [<b[1], (phi^-1)(b[2])> : b in AllRepOrbit(Image(phi))];
 end for;
 return res;
end function;

function FactorDeltaInv(G,H: Char2 := false)
 if Index(G,H) mod 2 ne 0 then /* Will only work for subgroups of even index. */
  return false;
 end if;
 vprint Invariant,2 : "Trying FactorDeltaInv in degree",Degree(G);

 n := Degree(G);
 R := SLPolynomialRing(Integers(),n:Global);

// short cut for the 2-transitive case
 if IsTransitive(G,2) then
  if IsEven(H) and IsOdd(G) then
   vprint Invariant,1: "Success! SqrtDisc found in FactorDeltaInv";
   if Char2 eq false then
    inv := &*[R.i - R.j : i,j in [1..n] | i lt j];
   else
    inv := [1,0];
    for i := 1 to n-1 do
     for j := i+1 to n do
      inv := [inv[1] * R.i + inv[2] * R.j, inv[1] * R.j + inv[2] * R.i];
     end for;
    end for;
    inv := inv[1];
   end if;
   inv`GalInvType := "FactorDelta";
   return inv;
  end if;
  vprint Invariant,2:"Fail in FactorDeltaInv";
  return false;
 end if;

 rl := AllRep(G);
// rl;
 if #rl eq 0 then vprint Invariant,2 : "failed!"; return false; end if;
 
// if &meet [a[2] : a in rl] subset H then
  mat_H := Matrix(GF(2),[[s in a[2] select 0 else 1 : s in GeneratorsSequence(H)] : a in rl]);
  mat_G := Matrix(GF(2),[[s in a[2] select 0 else 1 : s in GeneratorsSequence(G)] : a in rl]);

  k_H := Kernel(mat_H);
  k_G := Kernel(mat_G);
//  k_G; k_H;
  bm := BasisMatrix(k_H);
  lat := Lattice(Matrix(RowSequence(2*IdentityMatrix(Integers(),#rl)) cat [[Integers()!a : a in b] : b in  RowSequence(bm)]),
                 DiagonalMatrix([#a[1] : a in rl])  );
  bm_lat := BasisMatrix(LLL(lat));
  for i := 1 to NumberOfRows(bm_lat) do
   if not k_H!bm_lat[i] in k_G then
    vprint Invariant,3 : "FactorDelta";
    if not Char2 then 
     inv := &*[ &*[&+[R.k : k in ind_lst[1]] - &+[R.k : k in ind_lst[2]] :  ind_lst in rl[j][1] ]  
                 : j in [1..#rl] | IsOdd(bm_lat[i,j]) ];
     if not assigned inv`GalInvType then inv`GalInvType := "FactorDelta"; end if;
     vprint Invariant,1 : "Success in FactorDeltaInv";
     return inv; 
    else
     inv := [1, 0];
     for j := 1 to #rl do
      if IsOdd(bm_lat[i,j]) then
       for ind_lst in rl[j][1] do
        s1 := &+[R.k : k in ind_lst[1]]; s2 := &+[R.k : k in ind_lst[2]];
        inv := [inv[1] * s1 + inv[2] * s2, inv[1]*s2 + inv[2] * s1];    
       end for;
      end if;
     end for;
     res := inv[1];
     if not assigned res`GalInvType then res`GalInvType := "FactorDelta"; end if;
     vprint Invariant,1 : "Success in FactorDeltaInv";
     return res, inv;
    end if;
   end if;
  end for;
// end if;
 vprint Invariant,2 : "failed!";
 return false; 
end function; 

/* Invariants for a list of subgroups */
function FactorDeltaInvL(G,HL: Char2 := false)
 vprint Invariant,2:"FactorDeltaInvL searching for invariants for index 2 groups";
 if &and [ IsOdd(Index(G,H)) : H in HL] then /* Will only work for index 2 subgroups */
  return [* false : i in [1..#HL] *];
 end if;

 rl := AllRep(G);
 if #rl eq 0 then return [* false : i in [1..#HL] *]; end if;

 mat_G := Matrix(GF(2),[[s in a[2] select 0 else 1 : s in GeneratorsSequence(G)] : a in rl]);
 k_G := Kernel(mat_G);
 R := SLPolynomialRing(Integers(),Degree(G):Global);
// rl_core := &meet [a[2] : a in rl];

// precomputing a representation as an SL-poly for each entry in rl:
 rl_factors := [];
 for j := 1 to #rl do
  if not Char2 then
   Append(~rl_factors,&*[&+[R.k : k in ind_lst[1]] - &+[R.k : k in ind_lst[2]] :  ind_lst in rl[j][1] ]);
  else
   inv := [1, 0];
   for ind_lst in rl[j][1] do
    s1 := &+[R.k : k in ind_lst[1]]; s2 := &+[R.k : k in ind_lst[2]];
    inv := [inv[1] * s1 + inv[2] * s2, inv[1]*s2 + inv[2] * s1];    
   end for;
   Append(~rl_factors,inv);   
  end if;
 end for;

// combine rl_factors to invariants: 
 res := [* *];
 cnt := 0;
 for H in HL do
  if (cnt mod 100 eq 0) and (cnt ne 0) then
   vprintf Invariant,2:"%o groups treated up to now by FactorDeltaInvL. %o Invariants found.\n",
           cnt, cnt - #[a : a in res | a cmpeq false];
  end if;
  cnt := cnt + 1;
  suc := false;
  mat_H := Matrix(GF(2),[[s in a[2] select 0 else 1 : s in GeneratorsSequence(H)] : a in rl]);
  k_H := Kernel(mat_H);
  bm := BasisMatrix(k_H);
  lat := Lattice(Matrix(RowSequence(2*IdentityMatrix(Integers(),#rl)) cat [[Integers()!a : a in b] : b in  RowSequence(bm)]),
                 DiagonalMatrix([#a[1] : a in rl])  );
  bm_lat := BasisMatrix(LLL(lat));
  for i := 1 to NumberOfRows(bm_lat) do
   if not k_H!bm_lat[i] in k_G then
    if not Char2 then 
     inv := &*[ rl_factors[j] : j in [1..#rl] | IsOdd(bm_lat[i,j]) ];
    else
     inv := [1, 0];
     for j := 1 to #rl do
      if IsOdd(bm_lat[i,j]) then
       inv := [inv[1] * rl_factors[j][1] + inv[2] * rl_factors[j][2], inv[1] * rl_factors[j][2] + inv[2] * rl_factors[j][1]];
      end if;
     end for;
     inv := inv[1];
    end if;
    suc := true;
    inv`GalInvType := "FactorDelta";
    Append(~res,inv);
    break i;
   end if;
  end for;
  if not suc then Append(~res, false); end if;
 end for;
 return res; 
end function; 

// Induce Invariant from subgroup-level.
// inv0 is g1/h1 relative invariant. marker is a H / h1 relative invariant.
// We produce a G/H relative invariant by applying the Reynolds operator.
function InduceInvariant(IR, G,H,g1,h1, inv0, marker)
 vprint Invariant,2 : "Trying to induce invariant. Index",Index(H,h1);
 R := Parent(inv0);
 tr := Transversal(H,h1);
 inv := &+[Evaluate(inv0,PermuteSequence([R.i : i in [1..Degree(G)]],s)) : s in tr];
 if not &and [IsInvariant(SLPRGg(IR,inv),a) : a in GeneratorsSequence(G)] then
  assert &and [IsInvariant(SLPRGg(IR,inv),a) : a in GeneratorsSequence(H)];
  inv`GalInvType := "Induced";
  return inv;
 end if;
 if marker cmpeq false then vprint Invariant,2 : "failed! Need a marker."; return false; end if;
 Zx := PolynomialRing(Integers());
 for tran in [Zx.1, 1 + Zx.1, 1 + Zx.1 + Zx.1^2, 1 + Zx.1+Zx.1^2 + Zx.1^3, 1 + Zx.1 + Zx.1^4, 1 + Zx.1 + Zx.1^5] do
  inv1 := inv0 * Evaluate(tran,marker);      
  inv := &+[Evaluate(inv1,PermuteSequence([R.i : i in [1..Degree(G)]],s)) : s in tr];
  if not &and [IsInvariant(SLPRGg(IR,inv),a) : a in GeneratorsSequence(G)] then
   assert &and [IsInvariant(SLPRGg(IR,inv),a) : a in GeneratorsSequence(H)];
   inv`GalInvType := "Induced";
   return inv;
  end if;
 end for;

// The induction fails. Let's doublecheck the input.
 assert not &and [IsInvariant(SLPRGg(IR, inv0),a) : a in GeneratorsSequence(g1)]; 
 assert &and [IsInvariant(SLPRGg(IR, inv0),a) : a in GeneratorsSequence(h1)]; 

// if not IsExport() then printf"Problem in induction step\n"; end if;
 vprint Invariant,2 : "failed! Bad marker.";
 return false;
end function;


// Code for the intransitive case:

function show_min_non_ab(G,H) // Select orbits, that show the difference of G and H. Try to stay in the abelian world.

 assert G ne H;
 orb := Orbits(G);
 Sort(~orb, func<a,b | #a - #b>); 
 hom_orb := [Action(G,a) : a in orb];
 hom_ab := [];
 hom_l := [];
 for f in hom_orb do
  std,pi := StandardGroup(Image(f));
  Append(~hom_l,hom<G -> std | [ pi(f(a)) : a in GeneratorsSequence(G)] >);
  q_ab, pi := AbelianQuotient(Image(f));
  pg, iso := PermutationGroup(q_ab);
  compos := hom<G -> pg | [ (pi(f(a)))@@iso : a in GeneratorsSequence(G)] >;
  Append(~hom_ab, compos);
 end for;  

 hl := hom_ab cat hom_l;
 
 orb_prod, embedd, project := DirectProduct([Image(f) : f in hl]);

 ind := {1..2*#orb}; 
 for j := 2*#orb to 1 by -1 do
  if #ind gt 1 then
   im_g := sub<orb_prod | [ &*[embedd[k](hl[k](a)) : k in ind | k ne j] 
                            : a in GeneratorsSequence(G)]>;
   im_h := sub<orb_prod | [ &*[embedd[k](hl[k](a)) : k in ind | k ne j] 
                            : a in GeneratorsSequence(H)]>;
   if Index(im_g,im_h) gt 1 then /* Difference of groups is visible without this homomorphism. */
    Exclude(~ind, j);
   end if;
  end if;
 end for;

 ind_ab := [i : i in [1..#orb] | i in ind];
 ind_n := [i : i in [1..#orb] | i + #orb in ind];
 
 return [orb[i] : i in ind_ab], [orb[i] : i in ind_n];
end function;

/* Minimal list of orbits that shows a difference of G and H */
function min_show_diff(G,H:risky := false)
 
 assert G ne H;  
 orb := Orbits(G);
 hom_l := [Action(G,a) : a in orb];
 orb_fac := [Image(f) : f in hom_l];
 
 orb_prod, embedd, project := DirectProduct(orb_fac);

 ind := [1..#orb];
 for j := #orb to 1 by -1 do
  if #ind gt 1 then 
   im_g := sub<orb_prod | [ &*[embedd[k](hom_l[k](a)) : k in ind | k ne j] : a in GeneratorsSequence(G)]>;
   im_h := sub<orb_prod | [ &*[embedd[k](hom_l[k](a)) : k in ind | k ne j] : a in GeneratorsSequence(H)]>; 
   if risky then
    if im_g ne im_h then
     ind := [k : k in ind | k ne j];
    end if;
   else
    if Index(im_g,im_h) eq Index(G,H) then /* Difference of groups is visible without this orbit. */
     ind := [k : k in ind | k ne j];
    end if;
   end if;
  end if;
 end for; 

 return [orb[i] : i in ind]; 
end function;

function SmallQuotientStabCompleteSearch(im1, imK1, imK1H, index_limit)

// Small index, compute all intermediate groups
 if Index(im1, imK1H) lt 100 then
  phi := CosetAction(im1, imK1H);
  bg := Image(phi); 
  part := AllPartitions(bg) join {{1}};
  ugv := [(phi^-1)(Stabilizer(bg,a)) : a in part];
  ugv := [u : u in ugv | Core(im1,u) meet imK1 eq imK1H];

  e1,e2 := Max([Order(u) : u in ugv]);
  return ugv[e2]; 
 end if;

//check subgroups of small index
 lim := 2;
 repeat
  ugv := SubgroupClasses(im1:IndexLimit := lim);
  ugv := [u`subgroup : u in ugv];
  ugv := [u : u in ugv | (imK1H subset u) and (not imK1 subset u)];
  crl := [Core(im1,u) : u in ugv];
  ind := [i : i in [1..#ugv] | crl[i] meet imK1 eq imK1H];
  if (lim ge index_limit) and (#ind eq 0) then 
   return false;
  end if;
  lim := Min(lim * 2, index_limit);
 until #ind gt 0; 
 pos := Max(ind); 
 return ugv[pos];
end function;

// tries to find a super-group of start that solves the problem
function post_reduce(im1, imK1,imK1H, start)
 res0 := start; 
 repeat
  phi := CosetAction(im1,res0); 
  bg := Image(phi);
  mp := MinimalPartitions(bg);
  ntl_1 := [(phi^-1)(Stabilizer(bg, Representative(a))) : a in mp];
  ntl_1 := [a : a in ntl_1 | (Core(im1,a) meet imK1) eq imK1H]; 
  if #ntl_1 gt 0 then
   e1,e2 := Max([Order(Core(im1,a)) : a in ntl_1]);
   res0 := ntl_1[e2];
  end if;
 until #ntl_1 eq 0;
 return res0;
end function; 

// Random search for a subgroup of im1 such that intersection of its core with imK1 results in imK1H. 
// Limit search to groups of index index_lim. Treat max_par random pathes in the subgroup lattice in parallel.
function SmallQuotientStabRandom(im1, imK1, imK1H,index_lim, max_par)
 g0 := im1;
// descend as long as there is only one possible subgroup
 repeat
  if Core(im1,g0) meet imK1 eq imK1H then
   return g0;
  end if;
  ugv := MaximalSubgroups(g0);
  ugv := [u`subgroup : u in ugv | imK1H subset u`subgroup];  
  g0 := ugv[1];
 until #ugv gt 1;

// #ugv,"Subgroups possible to start with";

// Check for success
 crl := [Core(im1,u) : u in ugv];
 ind_suc := [i : i in [1..#crl] | crl[i] meet imK1 eq imK1H];
 if (#ind_suc gt 0) and (Index(im1, ugv[ind_suc[1]]) lt 100*index_lim) then
  tmp := post_reduce(im1,imK1,imK1H, ugv[ind_suc[1]]);
  if Index(im1,tmp) le index_lim then return tmp; end if;
 end if;

// "Continue by random";
// Descend on random pathes
 sol_l := [];
 for i := 1 to max_par do
  ugv1 := [Random(ugv)];
  suc := false;
  repeat
   g0 := Random(ugv1);
   ugv1 := MaximalSubgroups(g0:IndexLimit := index_lim div Index(im1,g0));
   ugv1 := [u`subgroup : u in ugv1];
   ugv1 := [u : u in ugv1 | imK1H subset u];
   crl := [Core(im1,u) : u in ugv1];
   ind_suc := [i : i in [1..#crl] | crl[i] meet imK1 eq imK1H];
   if #ind_suc gt 0 then
    e1,e2 := Max([Order(ugv1[i]) : i in ind_suc]);
    if Index(im1, ugv1[ind_suc[e2]]) le 100 * index_lim then
     Append(~sol_l, post_reduce(im1,imK1,imK1H, ugv1[ind_suc[e2]]));
    end if;
    e1,e2 := Max([Order(u) : u in sol_l]);
    if Index(im1,sol_l[e2]) lt #sol_l then
     return sol_l[e2];
    end if;
    suc := true;
   end if;
  until #ugv1 eq 0 or suc;
 end for;
 if #sol_l eq 0 then 
  //"fail"; 
  return false; 
 end if;

 e1,e2 := Max([Order(sol_l[i]) : i in [1..#sol_l]]);
 return sol_l[e2];
end function;

/* find a subgroup U of im1 of small index such that the kernel of the 
   corresponding permutation representation intersected with imK1 will result in imK1H.
   We assume there is no normal subgroup between imK1 and imK1H. */
function SmallQuotientStab(im1, imK1, imK1H)

// GetSeed(); Generators(im1); Generators(imK1); Generators(imK1H);

 gsd1,gsd2 := GetSeed(); // Store the seed, need it for debugging.

 assert imK1 ne imK1H;
 assert imK1H subset imK1; 

// Check the action of on a block-system it might suffice:
 if IsTransitive(im1) then 
  part := SetToSequence(AllPartitions(im1));
  Sort(~part, func<a,b | #b - #a>);
  for akt in part do
   phi := Action(im1,Orbit(im1,akt));
   if Kernel(phi) meet imK1 subset imK1H then
    std,pi := StandardGroup(Image(phi));
//    "Recursion in block system";
    return (phi^-1)((pi^-1)(SmallQuotientStab(pi(phi(im1)), pi(phi(imK1)), pi(phi(imK1H)))));   
   end if;
  end for;

// Try point stabilizer
  s1 := Stabilizer(im1,Labelling(im1)[1]);
  if Core(im1,s1) eq imK1H then
//   "Point stabilizer";
   return s1;
  end if;
 end if;
 
 if imK1 meet DerivedSubgroup(im1) subset imK1H then //Suffices to inspect the abelian quotient 
  abq0,pi0 := AbelianQuotient(im1);
  ab_imK1 := pi0(imK1); ab_imK1H := pi0(imK1H);
  res1 :=  ab_imK1H;
  repeat
   res0 := res1;
   abq,pi := quo<abq0 | res1>;
   res := sub<abq | Zero(abq) >; 
   for test in Generators(abq) do
    ord := Order(test); 
    fac := PrimeDivisors(ord);
    for a in fac do
      res2 := sub<abq | res, (ord div a)*test>;
      if res2 meet pi(ab_imK1) subset pi(ab_imK1H) then
       res := res2;
      end if;
    end for;
   end for;
   res1 := (pi^-1)(res);
  until res1 eq res0; 
  assert IsCyclic(quo<abq0 | res1>); // Smaller normal subgroup is not maximal inside the bigger one.
//  "General abelian";
  return (pi0^-1)(res1);
 end if;

 sol_l := [];
 u := SmallQuotientStabRandom(im1, imK1, imK1H, Degree(im1)^3, Degree(im1));
 if u cmpne false then
// "Random search";
  return u;
 end if; 
 
/* The random search is more general than this.

if Index(im1, imK1H) le Degree(im1)^3 then // construct the quotient by quo -- uses at least Index(im1,imK1H) memory
  sol_0 := imK1H;
  repeat
   bg,pi := quo<im1 | sol_0>;
   ntl := MinimalNormalSubgroups(bg);
   ntl := [(pi^-1)(a) : a in ntl];
   ntl := [ a : a in ntl | a meet imK1 subset imK1H];
   if #ntl gt 0 then
    sol_0 := ntl[1];
   end if;
  until #ntl eq 0;

  qu,pi := quo<im1 | sol_0>;
  assert IsTransitive(qu);
//  "using quo";
  return (pi^-1)(Stabilizer(qu, Labelling(qu)[1]));
 end if; */

// Special case: The center of a wreath product. Start with the stabilizer of the union of two blocks
 if IsTransitive(im1) and not IsPrimitive(im1) then
  mp := MinimalPartitions(im1);
  for a in mp do
   phi_a := Action(im1,a);
   std,pi := StandardGroup(Image(phi_a));
   orb := Orbits(std, GSet(std, Subsets(Support(std),2)));
   for dbl_block in orb do 
    s1 := (phi_a^-1)((pi^-1)(Stabilizer(std, Representative(dbl_block))));
    if imK1H subset Core(im1,s1) then // A subgroup of s1 might do it.
     cl := Subgroups(s1:IndexLimit := #Representative(a));
     cl := [u`subgroup : u in cl];
     Sort(~cl,func<a,b | #b - #a>);
     for akt in cl do
      if Core(im1,akt) meet imK1 eq imK1H then
       phi := CosetAction(im1,akt);
       bg := Image(phi); part := SetToSequence(AllPartitions(bg)) cat [{1}];
       Sort(~part,func<a,b | #b - #a>);
       for p0 in part do
        u := (phi^-1)(Stabilizer(bg, p0));
        if u meet imK1 eq imK1H then "Center of wreath product case"; return u; end if;
       end for;
      end if;
     end for;
    end if;
   end for;
  end for;
 end if;

// next try: Low index subgroups and all intermediate groups if index is small.
// In Degree 12 we will frequently need index 16.  
 "Doing complete search for subgroup";
 u := SmallQuotientStabCompleteSearch(im1, imK1, imK1H, (Degree(im1) eq 12) select 16 else Degree(im1));

 if u cmpne false then 
//  "naive direct search"; 
  return u; 
 end if;

 "Using greedy strategy:";
// Greedy search for a subgroup. To not care to much about the degree
 s0 := im1;
 if IsTransitive(im1) then
  mp := SetToSequence(AllPartitions(im1));
  s0 := im1;
  for j := 1 to #mp do // First approximation by stabilizer of a block.
   s1 := Stabilizer(s0,mp[j]);
   if imK1H subset s1 then s0 := s1; end if;
   if Core(im1,s0) meet imK1 eq imK1H then 
//    "Block stabilizer"; 
    return s0; 
   end if;
  end for; 
 end if;

 repeat
  ugv := MaximalSubgroups(s0);
  ugv := [u`subgroup : u in ugv];
  ugv := [u : u in ugv | imK1H subset u];
  crl := [Core(im1,u) : u in ugv];
  e1,e2 := Max([Order(ugv[i])^2 / Order(crl[i]) : i in [1..#crl]]); // Heuristic for group big, core small
  s0 := ugv[e2];
 until Core(im1,s0) meet imK1 eq imK1H;
 phi := CosetAction(im1,s0);
 e1,e2 := DegreeReduction(Image(phi));
 u := (phi^-1)((e2^-1)((Stabilizer(e1,1))));
 
 assert Core(im1,u) meet imK1 eq imK1H;

// "Iteration of maximal subgroup";
 return u;
end function;

/* Assuming the difference of G and H is visible in the abelian quotient of the direct product... */
function AbelianInvariant(IR,G,H,orb)
 
 p := Index(G,H);
 assert IsPrime(p);

 ab_q_l := [];
 pi_l := [];
 orb_h_l := [Action(G, GSet(G,akt)) : akt in orb];

 for phi in orb_h_l do
  aq,pi := AbelianQuotient(Image(phi));
  Append(~ab_q_l,aq);
  Append(~pi_l, hom<G -> aq | [pi(phi(a)) : a in GeneratorsSequence(G)]>);
 end for;

 g_ab, inc, proj := DirectProduct(ab_q_l);

 im_g := sub<g_ab | [&+[inc[i](pi_l[i](a)) : i in [1..#orb]] : a in GeneratorsSequence(G)]>;
 im_h := sub<g_ab | [&+[inc[i](pi_l[i](a)) : i in [1..#orb]] : a in GeneratorsSequence(H)]>;

// Order(g_ab), Order(im_g), Order(im_h); 
 
 assert Order(im_g) gt Order(im_h);

/* Find an element in the dual group of g_ab, that is trivial on im_h but not on im_g */
 prod_dual, scp := Dual(g_ab); 
 gen_d := [a : a in Generators(prod_dual)];
 mat_g := [[scp(a,b) : b in Generators(im_g)] : a in gen_d];  
 mat_h := [[scp(a,b) : b in Generators(im_h)] : a in gen_d];  

 ker_g := Kernel(Matrix(mat_g));
 ker_h := Kernel(Matrix(mat_h));
// ker_g; ker_h;
 bm := BasisMatrix(ker_h);
 i := 1; 
 while ker_h!bm[i] in ker_g do i := i + 1; end while; 
 
 lf := &+[Integers()!bm[i][j] * gen_d[j] : j in [1..#gen_d]];
 lf := lf * (Order(g_ab) div p^Valuation(Order(g_ab),p));
  
/* We want to construct the representation of g, which is given by x -> scp(lf, &+[inc[i](x) : i in [1..#orb]])
   Problem: Not clear in which group the summands are. */
 ch := Characteristic(BaseRing(ker_g));
 mult := GCD([Integers()!scp(lf,inc[i](pi_l[i](x))) : i in [1..#orb], x in GeneratorsSequence(G)] cat  [ch]); 
 order := Characteristic(BaseRing(ker_g)) div mult;
/* Sum will be in ZZ / order ZZ */ 
 reps := []; ZZ_ch := AbelianGroup([ch]);
 R := SLPolynomialRing(Integers(),Degree(G):Global);
 for i := 1 to #orb do
  akt := hom<G -> ZZ_ch | [ZZ_ch!(Integers()!scp(lf,inc[i](pi_l[i](x)))) : x in GeneratorsSequence(G)  ] >;
  k0 := Kernel(akt);
  if Order(G) ne Order(k0) then
   orb_im := Image(orb_h_l[i]);
   bg,pi := StandardGroup(orb_im);
   u := pi(orb_h_l[i](k0));
//   Order(bg), Order(u);
   inv0 := RelativeInvariant(IR, bg,u);
   
   inv := Evaluate(inv0,[R.j : j in Labelling(orb_im)]);
   rep := [Parent(inv)!0 : j in [1..order]];
   tr := Transversal(G, k0);
   for s in tr do rep[1+(Integers()!scp(lf, inc[i](pi_l[i](s))) div mult)] := Evaluate(inv^s,[R.i : i in [1..Rank(R)]]); end for;
   Append(~reps, rep);
  else
   if not IsExport() then printf"Orbit %o not used\n",orb[i]; end if;
  end if;
 end for;

// "Tensor-Step";
/* Tensor-Product of the cyclic representations in reps */ 
 tschirn := Polynomial([0,1]);
 iter := 1;
 repeat
  iter := iter + 1;
  tp := [Evaluate(tschirn,a) : a in reps[1]];
  for i := 2 to #reps do
   tp := [&+[tp[j+1]*Evaluate(tschirn,reps[i][k+1]) : j,k in [0..order-1] | (j + k) mod order eq m] : m in [0..order-1]]; 
  end for;
// "Final Check";
  assert  &and [IsInvariant(SLPRGg(IR,tp[1]),a) : a in GeneratorsSequence(H)];
  tschirn := Polynomial([Random([1..iter]) : j in [1..iter]] cat [1]);
  assert iter lt 3+Degree(G);
 until not &and [IsInvariant(SLPRGg(IR,tp[1]),a) : a in GeneratorsSequence(G)];

 if iter gt 2 then
  if not IsExport() then printf"Tschirni used in abelian tensor product"; end if;
 end if; 

 return tp[1], tp;
end function;

/* Assume H maximal in G. We are interested in the subdirect product case. */
function IntransitiveInvariant(IR, G,H:TryFactorDelta := true)
 if TryFactorDelta then
  inv := FactorDeltaInv(G,H: Char2 := Characteristic(IR) eq 2);
  if not inv cmpeq false then
   return inv,"FactorDelta";
  end if; 
 end if;

 vprint Invariant,2 : "Trying IntransitiveInvariant in degree",Degree(G);

 orb_ab, orb_na := show_min_non_ab(G,H);

 assert #(Set(orb_ab) meet Set(orb_na)) eq 0;

 if #orb_ab + #orb_na eq 1 then  // One orbit suffices -> go to transitive case
  vprint Invariant,2 : "Reduction to one orbit in IntransitiveInvariant";
  inv_sup := (orb_ab cat orb_na)[1];
  phi := Action(G,GSet(G,inv_sup));
  bg,pi := StandardGroup(Image(phi));
  IndentPush(); 
  inv0 := GaloisGroupInvariant(IR, bg,pi(phi(H)));
  IndentPop();
  R := SLPolynomialRing(Integers(),Degree(G):Global);
  inv := Evaluate(inv0,[R.i : i in Labelling(Image(phi))]);
  inv`GalInvType := "IntransitiveOrbit";
  assert &and [IsInvariant(SLPRGg(IR,inv),a) : a in GeneratorsSequence(H)];
  assert not &and [IsInvariant(SLPRGg(IR,inv),a) : a in GeneratorsSequence(G)];

  vprint Invariant,1 : "Success in IntransitiveInvariant (projection to orbit)";
  return inv, inv0`GalInvType;
 end if;

 if #orb_na eq 0 then // The abelian quotient of the orbit-groups suffices
  vprint Invariant,2 : "Reduction to abelian quotient of the action on ",orb_ab;
  phi := Action(G, GSet(G,&join orb_ab));
  std,pi := StandardGroup(Image(phi)); 
  inv := AbelianInvariant(IR, std,pi(phi(H)), Orbits(std));
  R := SLPolynomialRing(Integers(),Degree(G):Global);
  inv :=  Evaluate(inv,[R.i : i in Labelling(Image(phi))]);
  inv`GalInvType := "IntransitiveAbelian";
  assert &and [IsInvariant(SLPRGg(IR,inv),a) : a in GeneratorsSequence(H)];
  assert not &and [IsInvariant(SLPRGg(IR,inv),a) : a in GeneratorsSequence(G)];
  vprint Invariant,1 : "Success in IntransitiveInvariant (abelian case)";
  return inv, "Abelian";
 end if; 

 if #orb_ab gt 0 then
  vprint Invariant,2 : "Reduction to abelian quotient on ",orb_ab,"and general case on",orb_na;
/* Compute relevant abelian quotient of not abelian visible part and then glue with AbelianInvariant */
  phi_ab := Action(G,GSet(G,&join orb_ab));
  phi_na := Action(G,GSet(G,&join orb_na));
  k_ab := Kernel(phi_ab);
  k_na := Kernel(phi_na);

  hl := [Action(G,a) : a in orb_ab];
  prod, inc,proj := DirectProduct([Image(f) : f in hl]);
  inc_prod := hom<G -> prod | [&*[inc[i](hl[i](a)) : i in [1..#hl]] 
                         : a in GeneratorsSequence(G)]>;
  der0 := (inc_prod^-1)(DerivedSubgroup(prod) meet Image(inc_prod));
  bg := Image(phi_ab);
  der := phi_ab(der0);  // Kernel of the "abelian quotient of orbits"-map on orb_ab
  n_g_ab := sub<bg | der, phi_ab(k_na)>;
  n_h_ab := sub<bg | der, phi_ab(k_na meet H)>;
  
  u00 := SmallQuotientStab(Image(phi_ab), n_g_ab, n_h_ab); // Use linear algebra to find u00 faster!
  u_na := phi_na((phi_ab^-1)(u00) meet H);
 
  std, pi := StandardGroup(Image(phi_na));
  inv_na := RelativeInvariant(IR, std,pi(u_na));
  phi := CosetAction(std, pi(u_na));
  tr := [ i @@ phi : i in Labelling(Image(phi))]; 
//  Transversal doesn't give us the transversal used by CosetAction:
//  tr0 := Transversal(std,pi(u_na));
//  tr eq SetToSequence(tr0);
  R := Parent(inv_na);
  rep := [Evaluate(inv_na,PermuteSequence([R.i : i in [1..Rank(R)]],s)) : s in tr];

  R_fin := SLPolynomialRing(Integers(),Degree(G):Global);
  rep_na := [Evaluate(a,[R_fin.i : i in Labelling(Image(phi_na))]) : a in rep];
  
  ab_pr, inc, pr := DirectProduct([Image(phi_ab)] cat [phi(std)]);
  im_g := sub<ab_pr | [inc[1](phi_ab(a)) * inc[2](phi(pi(phi_na(a)))) : a in GeneratorsSequence(G)]>;  
  im_h := sub<ab_pr | [inc[1](phi_ab(a)) * inc[2](phi(pi(phi_na(a)))) : a in GeneratorsSequence(H)]>;  
  
  inv0 := AbelianInvariant(IR, im_g,im_h, Orbits(im_g));
  
  R_fin := SLPolynomialRing(Integers(),Degree(G):Global);
  inv := Evaluate(inv0,[R_fin.i : i in Labelling(Image(phi_ab))] cat rep_na);
  inv`GalInvType := "MixedIntransitive";  

  assert &and [IsInvariant(SLPRGg(IR, inv),a) : a in GeneratorsSequence(H)];
  assert not &and [IsInvariant(SLPRGg(IR, inv),a) : a in GeneratorsSequence(G)];

  vprint Invariant,1 : "Success in IntransitiveInvariant (relative abelian case)";
  return inv,"Partial Abelian";
 end if;
 
/* Check for induction of abelian case with small index. */
 for i := 1 to #orb_na do
  akt := orb_na[i];
  phi_akt := Action(G,akt); 
  phi_remaining := Action(G,GSet(G, &join ([orb_na[j]  : j in [1..#orb_na] | j ne i])));
  bg := Image(phi_akt);
  ker_G := phi_akt(Kernel(phi_remaining)); 
  ker_H := phi_akt(Kernel(phi_remaining) meet H); 
  
  der := DerivedSubgroup(bg);  
  assert ker_G subset sub<bg | der, ker_H>;

  if not ker_G subset sub<bg | ker_H, DerivedSubgroup(der)> then // we have a chance for an easy induction... 
   u00 := SmallQuotientStab( bg, ker_G, ker_H);
   phi := CosetAction(bg,u00);
   u0 := (phi^-1)(DerivedSubgroup(Image(phi))); // u0 subset bg (group acting on orb_na[i])
   u := (phi_akt^-1)(u0);
   if Index(G,u) le Degree(bg) then
    h1 := u meet H;
    csa := CosetAction(u,h1);
    M := MinimalPartitions(Image(csa));
    if #M gt 0 then 
     part:=Flat([[x:x in y |1 in x] : y in M]);
     u := Stabilizer(Image(csa), Representative(part)) @@csa;
    end if;  

    orb_ab_sub, orb_na_sub := show_min_non_ab(u, h1);
    if (#orb_ab_sub gt 2) or (#orb_na_sub eq 0) then //only in case of significant simplification on subgroup level
     i0 := IntransitiveInvariant(IR, u, h1);
     inv :=  InduceInvariant(IR, G,H, u,h1, i0, false);
     if inv cmpne false then
      vprint Invariant,1 : "Success in IntransitiveInvariant (simple induction)";
      return inv,"Induced";
     else
//     "Problem in induction step";
      std,pi := StandardGroup(bg);
      marker := RelativeInvariant(IR, pi(phi_akt(H)), pi(phi_akt(h1)));
      marker := Evaluate(marker,[Parent(i0).i : i in Labelling(bg)]);
      inv := InduceInvariant(IR, G,H, u,h1, i0, marker );
      if inv cmpne false then 
      vprint Invariant,1 : "Success in IntransitiveInvariant (induction with marker)";
       return inv,"Induced with marker";
      end if;
      if not IsExport() then "Problem in induction step (2)"; end if;
     end if;
    end if;
   end if; 
  end if;
 end for;

// No orbit is of abelian quotient type.  
 inv_sup := orb_na;

// printf"n(%o)",#inv_sup; 

 if #inv_sup eq 1 then /* Further test for degenerated cases */
  phi := Action(G,inv_sup[1]);
  ll := Labelling(Image(phi));
  bg,pi := StandardGroup(Image(phi));
  IndentPush();
  inv0 := GaloisGroupInvariant(IR, pi(phi(G)), pi(phi(H)));
  IndentPop();
  R := SLPolynomialRing(Integers(),Degree(G): Global);
  inv :=  Evaluate(inv0,[R.i : i in ll]);
  inv`GalInvType := "IntranstiveOrbit";
  assert &and [IsInvariant(SLPRGg(IR, inv),a) : a in GeneratorsSequence(H)];
  assert not &and [IsInvariant(SLPRGg(IR, inv),a) : a in GeneratorsSequence(G)];
  vprint Invariant,1 : "Success in IntransitiveInvariant (projection to orbit)";
  return inv, inv0`GalInvType;
 end if;


/* sub-direct product case: */
 phi1 := Action(G,inv_sup[1]); 
 phi2 := Action(G,GSet(G,&join [inv_sup[j] : j in [2..#inv_sup]]));

 im1 := Image(phi1);
 K1 := Kernel(phi2);
 imK1 := phi1(K1);
 K1H := K1 meet H;
 imK1H :=  phi1(K1H);

/* Now H can be described as the subgroup of G (= {(g_1,g_2) | ...}  subset phi1(G) x phi2(G)) with 
    g_1 (modulo K1H) = g_2 (modulo ...)   */
/* need a subgroup of im1 of minimal index such that it's core intersected with imK1 results in imK1H.
   For example  would do this, but we search for one of smaller index. */  
 u1 := SmallQuotientStab(im1, imK1, imK1H);

 pre_u1_H := (phi1^-1)(u1) meet H;
 u2 := phi2(pre_u1_H);

 bg1,pi1 := StandardGroup(im1);
 im2 := Image(phi2);
 bg2,pi2 := StandardGroup(im2);

 index1 := Index(im1,u1);
 index2 := Index(im2,u2);
 assert index1 eq index2;
 if index1 gt Degree(im1) and (not IsExport()) then printf"Using subgroup of index %o\n", Index(im2, u2); end if;
 inv1 := RelativeInvariant(IR, pi1(im1), pi1(u1));
 inv2 := RelativeInvariant(IR, pi2(im2), pi2(u2));

 /* H is the preimage of the diagonal of the permutation prepresentation of G given by the orbit of inv1 and the orbit of inv2.
    Note that the image of the representations lead to the same subgroups in S_n. */ 

 R := SLPolynomialRing(Integers(), Degree(G):Global);

 inv1 := Evaluate(inv1,[R.i : i in Labelling(im1)]);
 inv2 := Evaluate(inv2,[R.i : i in Labelling(im2)]);

 trans := Transversal(H, pre_u1_H);
 
 tschirn := Polynomial([0,1]);
 iter := 2;
 var_l := [R.i : i in [1..Rank(R)]];
 repeat
  inv := &+[ Evaluate(Evaluate(tschirn,inv1) * inv2, PermuteSequence(var_l,s)) : s in trans];
  iter := iter + 1;
  tschirn := Polynomial([Random([1..iter]) : j in [1..iter]] cat [1]);
  assert iter lt 3 + Degree(G); 
 until not &and [IsInvariant(SLPRGg(IR, inv),a) : a in GeneratorsSequence(G)];  
 if (iter gt 3) and (not IsExport()) then
  "Using Tschirni in last step";
 end if;
 inv := Evaluate(inv,[R.i : i in [1..Degree(G)]]);
 inv`GalInvType := "Intransitive(na)";

 assert &and [IsInvariant(SLPRGg(IR,inv),a) : a in GeneratorsSequence(H)];
 assert not &and [IsInvariant(SLPRGg(IR,inv),a) : a in GeneratorsSequence(G)];

 vprint Invariant,1 : "Success in IntransitiveInvariant (general case)";
 return inv, Sprintf("non-abelian(%o)",#inv_sup);
end function;


// Simple check what action on pairs gives us:
function CheapInvariantOnPairs(IR,G,U)
 vprint Invariant,2 : "Trying CheapInvariantOnPairs in degree",Degree(G);

 s2 := Subsets(Support(G),2); 
 orb := Orbits(G,GSet(G,s2));
 orb_u := Orbits(U,GSet(U,s2));
 R := SLPolynomialRing(Integers(),Degree(G):Global); 

 if #orb_u ne #orb then
  inv := 0;
  di := [a : a in orb_u | not a in orb][1];
  for i := 1 to Degree(G) do
   m2 := [j : j in [1..Degree(G)] | {i,j} in di];
   if #m2 gt 0 then 
    inv := inv + R.i * &+[R.j : j in m2]; 
    di := {a : a in di | not i in a}; 
   end if;
  end for;
  assert &and [IsInvariant(SLPRGg(IR, inv),a) : a in GeneratorsSequence(U)];
  assert not &and [IsInvariant(SLPRGg(IR, inv),a) : a in GeneratorsSequence(G)];
  inv`GalInvType := "PairOrbit";
  vprint Invariant,1 : "Success in CheapInvariantOnPairs (new orbit)";
  return inv;
 end if;

 vprint Invariant,2 : "Checking for block systems on pairs. Have ",#orb,"orbits to inspect."; 
 for i := 1 to #orb do
  phi := Action(U,GSet(U,orb[i]));
  bg := Image(phi);
  rr := Representative(Labelling(bg));
  s1 := Stabilizer(bg,rr);
  tr := Transversal(bg,s1);
  cand_gen_part := {Orbit(sub<bg | s1,a>, rr) : a in tr};
  cand_gen_part := [a : a in cand_gen_part | (not #a in [1,Degree(bg)]) and (Degree(bg) mod #a eq 0)]; 

  new_part := [];
  for akt in cand_gen_part do
   len := Degree(bg) div #akt;
   suc2, o2 := OrbitBounded(G, akt, len + 2);
   if (not suc2) or (len ne #o2) then
    suc1, o1 := OrbitBounded(bg, akt, len + 2);
    if suc1  and (#o1 eq len) then
     Append(~new_part,Set(akt));
     if #new_part eq 10 then
      vprint Invariant,2: "10 new partitions found. Stopping further search.";
      break akt;
     end if;   
    end if;
   end if;
  end for;

// We have generating new partitions in new_part
// Have to find the biggest new partition
  if #new_part gt 0 then
   vprint Invariant,2: "Orbit of length",Degree(bg);
   vprint Invariant,2: "Starting with",#new_part,"initial new block systems. Computing all above them.";
   vprint Invariant,2: "Block sizes",Sort([#a : a in new_part]);   
   bl2 := &join [ {&join b : b in AllPartitions(Image(Action(bg,Orbit(bg,a))))} : a in new_part];
   for akt in bl2 do
    suc3,o3 := OrbitBounded(G,akt, Degree(bg) div #akt + 2);  
    if (not suc3) or (#o3 gt Degree(bg) div #akt) then
     Append(~new_part,akt);
    end if;
   end for;
   vprint Invariant,2: "Number of new block systems found",#new_part;
   vprint Invariant,3: "With block size",Sort([#a : a in new_part]);
  
   e1,e2 := Max([#a : a in new_part]);
   o1 := Orbit(bg,new_part[e2]);
// o1 is a system of blocks of u but not for g 
   inv := 0;
   if Characteristic(IR) eq 2 then ex := 3; else ex := 2; end if;
   repeat
    for a in o1 do
     sum := 0;
     aa := a;
     for j := 1 to Degree(G) do
      m2 := [k : k in [1..Degree(G)] | {j,k} in aa];
      if #m2 gt 0 then 
       sum := sum + R.j * &+[R.k : k in m2]; 
       aa := { b : b in aa | not j in b};
      end if;
     end for;
     inv := inv + sum^ex;
    end for;
    if ex gt 20 then
     if not IsExport() then
      printf"CheapInvariantOnPairs: No exponent found\n";
     end if;
     vprint Invariant,2 : "failed! No exponent found.";
     return false;
    end if;
    ex := ex + 1;
   until not &and [IsInvariant(SLPRGg(IR, inv),a) : a in GeneratorsSequence(G)];
   assert &and [IsInvariant(SLPRGg(IR, inv),a) : a in GeneratorsSequence(U)];
   inv`GalInvType := "PairBlock";
   vprint Invariant,1 : "Success in CheapInvariantOnPairs (new block)";
   return inv;
  end if;
 end for;
 vprint Invariant,2 : "failed! No new orbit or block system for action on pairs.";
 return false;
end function;


/* Try to find subgroups of G with nice action on one block B.
   In case there are no good subgroups we return G */
function ShrinkWreathProduct(G,B)
 s1 := Stabilizer(G,B);
 phi := Action(s1,GSet(s1,B));
 if IsRegular(Image(phi)) then // nothing to do!
  return [G];
 end if;
 g_bl := Image(phi);
 
 g1 := sub<G | DerivedSubgroup(G), DerivedSubgroup(Image(phi)) @@ phi>; 
 if (phi(s1 meet g1) eq Image(phi)) then // No starting point
   return [G]; 
 end if;
 
// g1 is a proper subgroup of G.
// We check all the intermediate groups:
 psi := CosetAction(G,g1);
 bg := Image(psi);
 part := AllPartitions(bg);
 sl := [g1] cat [ Stabilizer(bg,a) @@ psi : a in part];
 sl := [a : a in sl | IsTransitive(a)]; 
 sl := [a : a in sl | Index(G,a) eq Index(g_bl,phi(s1 meet a))];
 return sl;
end function;


// Basic routines for invariants with cyclotomic coefficients:
// Mul and Mod polynom:
function RedSeq(s, red)
 res := [ &+[red[j][i] * s[j] : j in [1..#s]] : i in [1..#red[1]]];
 return res;
end function;


function MulSeq(s1, s2, red)
 res := [&+[s1[j1] * s2[j2] : j1 in [1..#s1], j2 in [1..#s2] | j1 + j2 eq i] : i in [2..#s1 + #s2]];
 res := [ &+[red[j][i] * res[j] : j in [1..#res]] : i in [1..#red[1]]];
 return res;
end function;

function MulSeqSeq(s, red)
 res := s[1];
 for j := 2 to #s do
  res := MulSeq(res, s[j], red);
 end for;
 return res;
end function;

function RedMat(n: Char2 := false)
  
 phi := CyclotomicPolynomial(n);
 t := Parent(phi).1;
 if Char2 and (n mod 2 eq 0) then phi := t^n-1; end if;

 res := [];
 for i := 0 to 2 * Degree(phi) do
  tr := t^i mod phi;
  co := Coefficients(tr);
  co := co cat [0 : j in [#co..Degree(phi)-1]];
  Append(~res,co); 
 end for;
 
 return res;
end function;

function TransferRep(start, s1, phi, part, IR)
 repeat
  r0 := Random(s1);
 until Order(phi(r0)) eq #part;
//    phi(r0);
 i0 := Representative(part);
 ind1 := [i0^(r0^s) : s in [0..#part-1]];
 tr_pr := Transversal(start, s1);
 R := SLPolynomialRing(Integers(),Degree(start):Global);
 mat := RedMat(#part:Char2 := Characteristic(IR) eq 2);
 fac := [RedSeq([R.(a^s) : a in ind1],mat) : s in tr_pr];
 l := MulSeqSeq(fac, mat);
 return l, r0;
end function;

/* Try transfer via blocksystem akt_part */
function BlockTransferInv(G,U, IR, akt_part, all_part) 
 part := Representative(akt_part);
 if (not IsPrimePower(#part)) or ((#part mod Index(G,U)) ne 0) or 
    (not IsPrime(Index(G,U))) then return false; end if;

 vprint Invariant,2 : "Trying BlockTransferInv in degree",Degree(G);

 s1 := Stabilizer(G, part);
 phi := Action(s1,GSet(s1,part));
 bg := Image(phi);
 if (#part * EulerPhi(#part)) mod Order(bg) ne 0 then
  vprint Invariant,2: "Failed! Block action to far from cyclic.";
  return false;
 end if;

 cand := ShrinkWreathProduct(G,part);
 cand := [a : a in cand | IsCyclic(phi(s1 meet a))];
 if #cand gt 0 then
  start := cand[1];
  u_start := U meet start;
 else
  vprint Invariant,2:"Failed! No transitive subgroup with cyclic action on block found.";
  return false;
 end if;
 
/* if not IsNormal(G,U) then
  nt := Core(G,U);
  if Index(U,nt) gt 100 then vprint Invariant,2 : "failed!"; return false; end if;
  qu, pi := quo<G | nt>;
  im_U := pi(U); 
  cl := SubgroupClasses(qu:IsCyclic := true, OrderEqual := Index(G,U));
  cl := [u`subgroup : u in cl];
  cl := [u : u in cl | Order(u meet im_U) eq 1];
  if #cl eq 0 then vprint Invariant,2 : "failed!"; return false; end if;
 // cl;
  start := (pi^-1)(cl[1]);
  if not IsTransitive(start) then vprint Invariant,2 : "failed!"; return false; end if;
  u_start := nt;
 // Order(G), Order(U), Order(nt), Order(start);
 else
  start := G;
  u_start := U;
 end if; */

 vprintf Invariant, 3: "Trying transfer to block %o group order %o degree %o\n",part,#G, Degree(G);
 s1 := Stabilizer(start,part);
 phi_s1 := Action(s1,GSet(s1,part));
 if IsCyclic(Image(phi_s1)) then
  ker_tr := TransferKernel(start,s1,Kernel(phi_s1));
  if Index(start,ker_tr) ne Index(start, u_start) then vprint Invariant,2 : "failed!"; return false; end if; // transfer not helpfull
  if ker_tr eq u_start then                   // transfer shows difference of groups 
   l, gen := TransferRep(start, s1, phi_s1, part, IR);
   if G eq start then
    inv := l[1]; 
    inv`GalInvType := "BlockTransfer";
    assert      &and [IsInvariant(SLPRGg(IR, inv),a) : a in GeneratorsSequence(u_start)];
    assert (not &and [IsInvariant(SLPRGg(IR, inv),a) : a in GeneratorsSequence(  start)]);
    vprint Invariant,1 : "Success in  BlockTransferInv";
    return inv;
   else
    for l_akt in l do 
     res := InduceInvariant(IR, G,U, start, u_start, l_akt, false);
     if res cmpne false then break l_akt; end if;
    end for;
    if res cmpne false then
     res`GalInvType := "InducedTransfer"; 
     vprint Invariant,1 : "Success in  BlockTransferInv (with induction)";
     return res; 
    end if;
   end if;
   vprint Invariant,2 : "failed!";
   return false;
  end if;
   
  for combine_block in all_part do
   phi_bl := Action(start, combine_block);
   k_phi_bl := Kernel(phi_bl);
   if  (not k_phi_bl subset u_start) and
       (k_phi_bl meet ker_tr) subset u_start then // Transfer and action on blocksystem can be combined to an invariant
    vprintf Invariant,3: "Combine of transfer and action on blocksystem %o is possible\n", part;
    GG, pi := StandardGroup(Image(phi_bl));
    HH := pi(phi_bl(u_start meet ker_tr));
    if #part mod Index(GG,HH) ne 0 then vprint Invariant,2 : "failed!"; return false; end if;

    IndentPush();
    inv_bl := RelativeInvariant(IR,GG,HH);
    IndentPop();

    R_fin := SLPolynomialRing(BaseRing(Parent(inv_bl)), Degree(G) : Global);
    inv_bl := Evaluate(inv_bl,[&+[R_fin.j : j in a] : a in Labelling(Image(phi_bl))]);
    l,gen := TransferRep(start, s1, phi_s1, part, IR);
    l := [Evaluate(f,[R_fin.i : i in [1..Degree(G)]]) : f in l];
     
    if Characteristic(Parent(inv_bl)) eq 0 then
	F := GF(NextPrime(2^22));
    else
 	F := CoefficientRing(Parent(inv_bl));
	F := quo<F | RandomIrreduciblePolynomial(CoefficientRing(F), Ceiling(Log(Characteristic(F), 2^30)))>;
    end if;
    SetEvaluationComparison(Parent(inv_bl), F, 4);        

    mat := RedMat(#part:Char2 := Characteristic(IR) eq 2);
  
    tr := Transversal(u_start, u_start meet ker_tr);
    tr := [a : a in tr | GG eq sub<GG | pi(phi_bl(a)), HH>];
    assert #tr gt 0;
    h0 := tr[1];
    mul := [1];
    ex := 0;
    l_h0 := [ Evaluate(a,PermuteSequence([R_fin.i : i in [1..Rank(R_fin)]],h0)) : a in l];
    repeat
     ex := ex + 1;
     mul := [0] cat mul;
     assert ex le #part;
    until MulSeqSeq([l, mul], mat) eq l_h0;  
/* h0 acts on l via multiplication with mul */

    l2 := [Evaluate(inv_bl,PermuteSequence([R_fin.j : j in [1..Rank(R_fin)]], h0^e)) : e in [0..Index(GG,HH)-1]];
    zc := #part div  Index(GG,HH) - 1;
    if zc gt 0 then 
     zc := #part div  Index(GG,HH) - 1;
     l2 := &cat [ [a] cat [0 : j in [1..zc]] : a in l2];  
    end if;

/* Reorder l2 s.t. h0 acts on l2 as on l */
    ex := Modinv(ex div (zc + 1),#part);
    l2 := [l2[1 + (ex * j - 1) mod #part] : j in [1..#l2]];
    l3 := MulSeqSeq([l, RedSeq(l2,mat)], mat);
    if G eq start then
     res := l3[1]; 
     res`GalInvType := "CombinedTransfer";
     assert &and [IsInvariant(SLPRGg(IR, res),a) : a in GeneratorsSequence(U)]; 
     assert not &and [IsInvariant(SLPRGg(IR, res),a) : a in GeneratorsSequence(G)]; 
     vprint Invariant,1 : "Success in BlockTransferInv (with combine step)";
     return res;
    else
     for l_akt in l3 do
      res := InduceInvariant(IR, G,U,start, u_start, l_akt, false);
      if res cmpne false then break l_akt; end if;
     end for;
     if not res cmpeq false then
      vprint Invariant,1 : "Success in BlockTransferInv (with combine step and induction)";
      res`GalInvType := "InducedCombinedTransfer";
      return res; end if;
    end if;
   end if; 
  end for;
 end if;   
// "Transfer failed", Order(G), Order(U);
 vprint Invariant,2 : "failed!";
 return false;
end function;


// Compute #part-1 transfer representations from G to the stabilizer of part
// One for each choice of a root of unity.
function OrbitBlockTransfer(R,G,orb,part, mat)

 s1 := Stabilizer(G,part);
 phi := Action(s1,GSet(s1,part));
 bg := Image(phi);
 assert #bg eq #part;
 gen := [a : a in bg | Order(a) eq #part][1];
 gen := (phi^-1)(gen);  // A generator for the cyclic group that acts on part
 i0 := Representative(part);
 s_i0 := Stabilizer(s1,i0);
 lfl := [];
 for ex := 1 to #part -1 do 
  lf_akt := [R!0 : i in [1..#part]];
  for j := 0 to #part - 1 do
   lf_akt[1+(ex*j mod #part)] := lf_akt[1+(ex*j mod #part)] + R.(i0^(gen^j));
  end for;
  Append(~lfl,RedSeq(lf_akt,mat));
 end for;

 tr := Transversal(G, s1);

 return [ MulSeqSeq([[Evaluate(a,[R.(j^s) : j in [1..Degree(G)]]) : a in l] : s in tr], mat) : l in lfl];
end function; 


// Given an intransitive group g and a subgroup h. Acting on the partition mp (from an transitive over group)
// with kernel ker_g and ker_h. Try to construct (proof inexistence)
// of an invariant consisting of block transfer and blocks-action
function InternalTransferBlockTest(IR, g, h, ker_g, ker_h, mp)

 orb := Orbits(g); // Orbits are unions of blocks from the block-system akt
 part_orb := [ {t : t in mp | t subset ao} : ao in orb];
 part_rep := [ Representative(a) : a in part_orb];
 s1l := [Stabilizer(g,a) : a in part_rep];
 s1hl := [Action(s1l[i], GSet(s1l[i],part_rep[i])) : i in [1..#part_orb]];
 index_l := [i : i in [1..#s1hl] | IsCyclic(Image(s1hl[i])) and IsTransitive(Image(s1hl[i]))];
 if #index_l gt 0 then
  ker_l := [TransferKernel(g,s1l[i],Stabilizer(s1l[i],Representative(part_rep[i]))) : i in index_l];
  k_tot := &meet ker_l meet ker_g;
  if Order(sub<ker_g | k_tot, ker_h>) lt Order(ker_g) then
   ind := []; ker_l2 := [];
   for i in [1..#ker_l] do
    if (ker_l[i] ne g) and (not ker_l[i] in ker_l2) then
     Append(~ker_l2, ker_l[i]);
     Append(~ind,index_l[i]);
    end if;
   end for; // ker_l2: List of non-trivial transfer kernels
            // ind:    List of corresponding numbers of orbits.
   aql0 := [* *];
   for i := 1 to #ker_l2 do
    csl := CosetAction(g, ker_l2[i]);
    aq, pi := AbelianQuotient(Image(csl));
    Append(~aql0, <aq, pi, csl>);
   end for;
   prod, inc := DirectProduct([a[1] : a in aql0]);
   aql := [* < inc[i],aql0[i][2],aql0[i][3]>  : i in [1..#aql0] *];
   dual,scp := Dual(prod);
   gen_dual := [dual.i  : i in [1..#aql0]];   
   mat_g := [[ scp(a,&+[m[1](m[2](m[3](x))) : m in aql]) : x in GeneratorsSequence(ker_g)] : a in gen_dual];   
   mat_h := [[ scp(a,&+[m[1](m[2](m[3](x))) : m in aql]) : x in GeneratorsSequence(ker_h) cat [ker_h.0]] : a in gen_dual];   
   m_ker_g := Kernel(Matrix(mat_g));
   m_ker_h := Kernel(Matrix(mat_h));
   bm := BasisMatrix(m_ker_h);
   deg := #Representative(mp);
   e,p := IsPrimePower(deg);
   assert e;

   mat := RedMat(deg: Char2 := Characteristic(IR) eq 2);
   R := SLPolynomialRing(Integers(),Degree(g): Global);
   SetEvaluationComparison(R,GF(NextPrime(2^22)), 4); 
   for j := 1 to NumberOfRows(bm) do
    transfer_fac := [];
    if not bm[j] in m_ker_g then 
     for k := 1 to #ind do
      if bm[j,k] ne 0 then
       fac := OrbitBlockTransfer(R,g,orb[ind[k]],part_rep[ind[k]], mat);
//       fac;inv_l := [* *];
       g_test := Representative([b : b in GeneratorsSequence(g) | sub<g | b,ker_l2[k]> eq g]);
       m := aql[k];
       t_val := Integers()!scp(gen_dual[k],m[1](m[2](m[3](g_test)))) * (deg div Exponent(dual));  
       t_val := t_val * (Integers()!bm[j,k]) mod deg;
       assert t_val ne 0;     
//       t_val := InverseMod(t_val div p^Valuation(t_val,p),deg);
//       t_val := (-t_val) mod deg;
       mul := RedSeq([0 : i in [1..t_val]] cat [1], mat);
       sol := [a : a in fac | MulSeq(a, mul, mat) eq [b^g_test : b in a]];
       assert #sol eq (deg div Exponent(dual));
       Append(~transfer_fac, sol[1]);
      end if;
     end for;

     transfer_prod := MulSeqSeq(transfer_fac,mat);

     assert &and [IsInvariant(SLPRGg(IR, transfer_prod[1]),a) : a in GeneratorsSequence(ker_h)];
     assert not &and [IsInvariant(SLPRGg(IR, transfer_prod[1]),a) : a in GeneratorsSequence(ker_g)];


     tg := AbelianGroup([#Representative(mp)]);    
     tv := [];
     for a in  GeneratorsSequence(g) do 
      Append(~tv, [ j : j in [1..deg] | MulSeq(transfer_prod, RedSeq([0 : bb in [1..j]] cat [1],mat), mat) eq transfer_prod^a]);
     end for;
     assert &and [#a eq 1 : a in tv];
     t_rep := hom<g -> tg | [a[1] : a in tv]>;
     k_t_rep := Kernel(t_rep);
     if h subset k_t_rep then
      return true, transfer_prod[1],transfer_prod;
     end if;
// Need the action on the block-system to combine an invariant.  
     phi := Action(g, mp);
     
     bg,pi := StandardGroup(Image(phi));
     inv_bl := RelativeInvariant(IR,bg,pi(phi(h meet k_t_rep)));
     inv_bl := Evaluate(inv_bl,[&+[R.i : i in a] : a in Labelling(Image(phi))]);     

     e1,e2 := Max([Order(t_rep(a)) : a in GeneratorsSequence(h)]);
     gen_h := GeneratorsSequence(h)[e2];

     t_im := [i : i in  [1..deg] | MulSeq(transfer_prod, RedSeq([0 : aa in [1..i]] cat [1],mat), mat) 
                                eq [a^gen_h : a in transfer_prod]];
     assert #t_im eq 1;
     t_im := t_im[1];
// The action of t_im on tranfer_prod is given by t_im steps of rotation
     mul := InverseMod(t_im div p^Valuation(t_im,p), deg);
     comp_rep := [inv_bl^(gen_h^(mul * i)) : i in [0..Index(h,h meet k_t_rep)-1]];
     if Index(h,h meet k_t_rep) lt deg then
      comp_rep := &cat [[comp_rep[i]] cat [0 : j in [2..deg div Index(h,h meet k_t_rep)]] : i in [1..#comp_rep]];
     end if;
 
     ex := 1;
     repeat
      tensor := MulSeq(transfer_prod, RedSeq([a^ex : a in comp_rep],mat),mat);
      assert &and [IsInvariant(SLPRGg(IR, tensor[1]),a) : a in GeneratorsSequence(h)]; 
      ex := ex + 1;
      assert ex lt 20;
     until not &and [IsInvariant(SLPRGg(IR, tensor[1]),a) : a in GeneratorsSequence(g)];

     return true, tensor[1], tensor;
    end if;
   end for;
  end if;
 end if; 
 ind := [i : i in [1..#s1hl] |   not IsCyclic(Image(s1hl[i])) and
                                 Exponent(Image(s1hl[i])) mod #part_rep[1] eq 0];
 return false, [part_rep[i] : i in ind], [s1hl[i] : i in ind]; 
end function;

/* Case prime-power index. Prime is size of minimal block system. */
function KernBlockInv5(IR,G,H)

 vprint Invariant,2 : "Trying KernelBlockInv5 in degree",Degree(G);

 ind := Index(G,H);
 mp := MinimalPartitions(G);
// mp := [a : a in mp | (Gcd(ind,#Representative(a)) gt 1) and IsPrimePower(#Representative(a))];
 if #mp ne 1 then vprint Invariant,2 : "failed!"; return false; end if; // No unique minimal Partition to start with
 mp := Representative(mp);
 akt := Representative(mp);
 if Gcd(#akt, Index(G,H)) eq 1 then vprint Invariant,2 : "failed!"; return false; end if; // Call block-quotient or remove extension!

// Check that the stabilizer of the block has a cyclic subgroup that we can use for transfer. 
 e1,p := IsPrimePower(#akt);
 if not e1 then vprint Invariant,2 : "failed!"; return false; end if;

 s1 := Stabilizer(G,akt);
 phi_s1 := Action(s1,GSet(s1,akt));
 bg_s1 := Image(phi_s1);
 if Order(bg_s1) div #akt gt Degree(G) then vprint Invariant,2 : "failed!"; return false; end if; // Index to big for induction of invariants
 im_syl := SylowSubgroup(bg_s1,p);
 if Exponent(im_syl) ne #akt then vprint Invariant,2 : "failed!";return false; end if; // No cyclic subgroup for transfer!


// Search for intransitive low-index subgroups to reduce to:
 phi := Action(G,mp);
 if phi(G) ne phi(H) then vprint Invariant,2 : "failed!";return false; end if; // error: we have an e-invariant.
 bg,pi := StandardGroup(Image(phi));
 ugv0 := SubgroupClasses(bg:IndexLimit := 2*Degree(G));   
 ugv0 := [u`subgroup : u in ugv0 | not IsTransitive(u`subgroup) ]; // and not 1 in [#a : a in  Orbits(u)]];
 if #ugv0 eq 0 then vprint Invariant,2 : "failed!"; return false; end if;
 ord_l := [-Order(a) : a in ugv0];
 ParallelSort(~ord_l,~ugv0);

 R := SLPolynomialRing(Integers(),Degree(G):Global);

 k_G := Kernel(phi);
 k_H := k_G meet H;
// printf"%o ",#ugv0;
 for u0 in ugv0 do
  orb0 := Orbits(u0);
  if #Orbit(bg,orb0) ne Index(bg,u0) then continue u0; end if; // Nor the biggest subgroup with these orbits!
  aux := (phi^-1)((pi^-1)(u0)); 
  orb := Orbits(aux); 

  suc,p_re, h_re :=  InternalTransferBlockTest(IR, aux,aux meet H,k_G, k_H, mp);
  if suc then 
   inv0 := p_re;
   assert &and [IsInvariant(SLPRGg(IR, inv0),a) : a in GeneratorsSequence(aux meet H)];  
   assert not &and [IsInvariant(SLPRGg(IR, inv0),a) : a in GeneratorsSequence(aux)];  

   R := Parent(inv0);
   inv := InduceInvariant(IR, G, H, aux, aux meet H, inv0, &+[(k-1)*(&+[R.i : i in orb[k]]) : k in [1..#orb]]);
//   assert inv cmpne false;
//   printf"%o ",Index(H,H meet aux);
   
   vprint Invariant,1 : "Success in KernBlockInv5";
   return inv;
  end if;

  if #p_re gt 0 then
   cl := SubgroupClasses(aux:IndexLimit := Max([Order(Image(f)) div #akt : f in h_re]));
   cl := [a`subgroup : a in cl | #Orbits(a`subgroup) eq #orb and Order(a`subgroup) lt Order(aux)];
   ord_l2 := [-Order(a) : a in cl];
   ParallelSort(~ord_l2,~cl);
   for aux2 in cl do 
    s1l_a := [Stabilizer(aux2,a) : a in p_re];
    m_ind := [i : i in [1..#s1l_a] | IsCyclic(h_re[i](s1l_a[i])) and IsTransitive(h_re[i](s1l_a[i]))];
    if #m_ind gt 0 then
     if k_G meet aux2 ne k_H meet aux2 then
      suc, inv0 :=  InternalTransferBlockTest(IR, aux2, aux2 meet H,k_G meet aux2, k_H meet aux2, mp);
      if suc then 
       assert &and [IsInvariant(SLPRGg(IR, inv0),a) : a in GeneratorsSequence(aux2 meet H)];  
       assert not &and [IsInvariant(SLPRGg(IR, inv0),a) : a in GeneratorsSequence(aux2)];  
       R := Parent(inv0);
       inv1 := InduceInvariant(IR, aux, aux meet H, aux2, aux2 meet H, inv0, false);
       if inv1 cmpeq false then
        part_marker := p_re[Representative(m_ind)]; 
        s1_m := Stabilizer(aux,part_marker);
        phi_m := Action(s1_m,GSet(s1_m,part_marker));
        std_m,pi_m := StandardGroup(Image(phi_m));
        IndentPush();
        marker := RelativeInvariant(IR, std_m,pi_m(phi_m(aux2 meet s1_m)));
        IndentPop();
        marker := Evaluate(marker,[R.i : i in Labelling(Image(phi_m))]);
        marker := &+[marker^s : s in Transversal(aux2,aux2 meet s1_m)];
        inv1 := InduceInvariant(IR, aux, aux meet H, aux2, aux2 meet H, inv0, marker);
        if (inv1 cmpeq false) then
         vprint Invariant,2: "No good marker found.";           
        end if;
       end if;
       if inv1 cmpne false then
        inv := InduceInvariant(IR, G, H, aux, aux meet H, inv1, &+[(k-1)*(&+[R.i : i in orb[k]]) : k in [1..#orb]]);
        assert inv cmpne false;
        vprint Invariant,1 : "Success in  SmallerWreathProductInductionInv (with marker)";
        return inv;
       end if;
      end if;
     end if;
    end if;
   end for; 
  end if;
 end for;
 vprint Invariant,2 : "failed!";
 return false;
end function;
 

// Use code over F_3
function InvByF3Code(IR,g,h)
 if not IsTransitive(g) then return false; end if;

 mp := MinimalPartitions(g);
 mp := [a : a in mp | 3 eq #Representative(a)];
 if #mp eq 0 then 
   return false; // No blocksystem -- can not encode the problem in a code!
 end if; 

 if Index(g,h) mod 2 eq 0 then
   return false; // Use BlockQuotient in this case
 end if;

 mp := mp[1];
 phi := Action(g,mp);
 kg := SylowSubgroup(Kernel(phi),3);
 kh := kg meet h; 
 if kg eq kh then 
   return false; // Use E-Invariant in this case   
 end if;  

 vprint Invariant,2 : "Trying InvByF3Code in degree",Degree(g);

 mp_seq := [SetToSequence(a) : a in mp];  
 phi := Action(g,mp);
 bg,pi := StandardGroup(Image(phi));
 
// Represent the the kernel as a F_2 vectorspace.
 mat_g := Matrix(GF(3),[[Index(b,b[1]^a) - 1 : b in mp_seq] : a in GeneratorsSequence(kg)] 
                       cat [[0 : i in [1..#mp_seq]]]);
 mat_h := Matrix(GF(3),[[Index(b,b[1]^a) - 1 : b in mp_seq] : a in GeneratorsSequence(kh)]
                       cat [[0 : i in [1..#mp_seq]]]);

 code_g := LinearCode(mat_g);
 code_h := LinearCode(mat_h);

 dual_g := Dual(code_g);
 dual_h := Dual(code_h);


 if (Dimension(code_g) gt 10 and Dimension(dual_g) gt 10) or
    (Dimension(code_h) gt 10 and Dimension(dual_h) gt 10) then 
// Codes are to big for complete search. This can only happen for polynomials of degree > 64
  vprint Invariant,2:"Code is to big for fast weight enumeration";
  return false;
 end if;
 
 wt_g := WeightEnumerator(dual_g);
 wt_h := WeightEnumerator(dual_h);

 w_diff := wt_h - wt_g; // Weight-Numberator for the linear forms that vanish on k_h but not an k_g

 zz := PolynomialRing(Integers()); x := zz.1;
 w_diff := Evaluate(w_diff,[1,x]);
 
 v := Valuation(PowerSeriesRing(Integers())!w_diff); // Smallest weight of a word in dual_h \setminus dual_g


 if MonomialCoefficient(Evaluate(wt_h,[1,x]),x^v) gt 10^5 then // to many words!
  vprint Invariant,2:"Code is to big for fast word enumeration";
  return false;
 end if;

 words := WordsOfBoundedWeight(dual_h, v, v); 
 words := {a : a in words | not a in dual_g};

// Have to compute the action of g on words and the shortest orbit.
 ii := Order(g);
 mp_seq_0 := [Min(a) : a in mp_seq]; 
 ii := Order(g);
 repeat
  a := Representative(words);
// Compute the largest subgroup of g for which a is a linear representation.
  lfl := [a[i] eq 2 select mp_seq[i][[1,3,2]] else mp_seq[i] : i in [1..#mp_seq] | a[i] ne 0];
  g1 := Stabilizer(g,Set(&cat lfl));
  phi_aux := Action(g1,GSet(g1,{@ k : k in &cat lfl @}));
  bg,pi := StandardGroup(Image(phi_aux));
  g2 := (bg meet WreathProduct(Alt(3),Sym(Degree(bg) div 3))) @@ pi @@ phi_aux;
  if Index(g,g1) le ii then
   ii := Index(g,g1);
   opt_word := a;
   opt_stab := g1;
   opt_rep := g2;
   opt_lfl := lfl;
  end if;
// Exclude the g-orbit of the word a as it would result in the same invariant.
  tr := Transversal(g,g2); 
  for s in tr do
   ww := [];
   for i := 1 to #mp_seq do
    im_c_i := [b^(s^-1) : b in mp_seq[i]];
    j := Index(mp_seq_0,Min(im_c_i));
    if a[j] eq 0 then 
      Append(~ww,0);
    else
      if im_c_i in {PermuteSequence(mp_seq[j],tt) : tt in Alt(3)} then 
        Append(~ww,a[j]);
      else
        Append(~ww,-a[j]);
      end if;
    end if;
   end for;
   assert ww in words;
   Exclude(~words,ww);
//   Exclude(~words,[-a : a in ww]);
  end for; 
 until #words eq 0;

 g0 := opt_rep;
 h0 := g0 meet h;
 assert g0 ne h0;

// We have found the code word opt_word that defindes a C_3 representation of g0.
// However it might be good to define a dihedral representation
  
// Now we need the kernel of the 1-dimensional representation of g0 given by the word opt_word.
// inv0 defines an C_3 representation of g0. But there my be an overgroup (factor 2 bigger), such that we have a 
// dihedral representation
 s2 := SylowSubgroup(h meet Kernel(phi),2);
 phi_s2 := Action(s2, GSet(s2,Set(&cat lfl)));
 std,pi_std := StandardGroup(Image(phi_s2));
 orbs_std := [a : a in Orbits(std) | #a eq 2];
 sup_std := &join orbs_std;
 perm := Sym(Degree(std))![ (not i in sup_std) select i else (&+[a : a in orbs_std | i in a][1] - i) : i in [1..Degree(std)]];
 if (#orbs_std eq #lfl) and (perm in std) then
//"Dihedral representation fould";
  perm := (perm @@ pi_std) @@ phi_s2; // we can construct a dihedral representation of  sub<g | g1 , perm>
  assert not perm in h0;
  orb_s := &join [a : a in Orbits(sub<g | perm>) | #a eq 2]; 
  lfl_2 := [];
  for a in opt_lfl do // rotate a such that a[1] is fixed by perm
   b := a;  
   if b[1] in orb_s then b := b[[2,3,1]]; end if;
   if b[1] in orb_s then b := b[[2,3,1]]; end if;
   assert b[1]^perm eq b[1];
   Append(~lfl_2,b);
  end for;
  opt_lfl := lfl_2;
 else 
  perm := Identity(g);
 end if; 
  

 gen := GeneratorsSequence(g0);
 im_l := []; 

 for a in gen do
  val := 0;
  for akt in opt_lfl do
    b := [i^a : i in akt];
    pp := [b in opt_lfl, b[[2,3,1]] in opt_lfl, b[[3,1,2]] in opt_lfl];
    assert &or pp;
    val := val + Index(pp,true) - 1;
  end for;
  Append(~im_l,(Alt(3)!(1,2,3))^(val mod 3));
 end for;
 
 rep := hom<g0 -> Alt(3) | im_l>;
 ker := Kernel(rep); 

 mat := RedMat(3);

 rr := SLPolynomialRing(Integers(),Degree(g):Global);

 inv0 := MulSeqSeq([[rr.j : j in a] : a in opt_lfl], mat); 

 assert &and [IsInvariant(inv0[1],a) : a in GeneratorsSequence(ker)];
 assert &and [IsInvariant(inv0[2],a) : a in GeneratorsSequence(ker)];
 assert not &and [IsInvariant(inv0[1],a) : a in GeneratorsSequence(g0)];

 orbs := Orbits(g0);
 if h0 subset ker then
  vprint Invariant,2:"Can induce directly. Index",Index(h,h0);
//"Kernel matches!";
// We can lift directly, doing lift to dihedral case first:
  if perm ne Identity(g) then
//"Using dihedral instead of cyclic representation";
   assert #inv0 eq 2;
   inv00 := inv0;
   inv0 := [2*inv0[1] - inv0[2]]; // Trace is conjugation invariant 
   g0 := sub<g | g0, perm>;
   h0 := sub<g | h0, perm>;
   assert &and [IsInvariant(inv0[1],a) : a in GeneratorsSequence(h0)];
   assert not &and [IsInvariant(inv0[1],a) : a in GeneratorsSequence(g0)];
  end if;

  l := 1;
  repeat
   inv := InduceInvariant(IR, g,h, g0,h0, inv0[1], &+[&+[rr.j : j in orbs[e]]^(e) : e in [1..l]]  );
   if (inv cmpeq false) and (#inv0 gt 1) then 
// inv0[1] my be degenerated, try 2nd component
    inv := InduceInvariant(IR, g,h, g0,h0, inv0[2], &+[&+[rr.j : j in orbs[e]]^(e) : e in [1..l]]  );
   end if;
   if inv cmpne false then 
    vprint Invariant,1 : "Success in InvByF3Code";
    return inv; 
   end if;
   l := l + 1;
  until l gt #orbs;
  vprint Invariant,2 : "Failed";
  return false;
 end if;
// "Combined case";
// Use of dihedral group not implemented
 vprint Invariant,2:"Have to combine with the action on the blocks";
 bg,pi := StandardGroup(phi(h0));
 u_aux := pi(phi(ker meet h0));
 assert Index(bg,u_aux) eq 3;
 IndentPush();
 inv_quot := GaloisGroupInvariant(IR,bg,u_aux);
 IndentPop();
 inv_quot_l := Evaluate(inv_quot,[&+[rr.j :  j in bl] : bl in mp_seq] );
 rep_quot := [Evaluate(inv_quot_l,PermuteSequence([rr.j : j in [1..Degree(g)]],sigma)) : sigma in Transversal(h0,h0 meet ker) ];

 prod1 := MulSeqSeq([rep_quot, inv0], mat);
 prod2 := MulSeqSeq([rep_quot[[1,3,2]], inv0], mat);

 suc1 := &and [IsInvariant(prod1[1],a) : a in GeneratorsSequence(h0)];
 suc2 := &and [IsInvariant(prod2[1],a) : a in GeneratorsSequence(h0)];

 assert #{suc1,suc2} eq 2; // exactly one of the two should be right.

 if suc2 then prod1 := prod2; end if;

// Don't know how to do the dihedral approach in this generality. 
// I.e. how do I get the supergroup that has the dihedral representation?
 
 assert not &and [IsInvariant(prod1[1],a) : a in GeneratorsSequence(g0)];
 l := 1;
 repeat
   inv := InduceInvariant(IR, g,h, g0,h0, prod1[1], &+[&+[rr.j : j in orbs[e]]^(e) : e in [1..l]]  );
   if (inv cmpeq false) and (#prod1 gt 1) then 
// prod1[1] my be degenerated, try 2nd component
    inv := InduceInvariant(IR, g,h, g0,h0, prod1[2], &+[&+[rr.j : j in orbs[e]]^(e) : e in [1..l]]  );
   end if;
   if inv cmpne false then 
    vprint Invariant,1 : "Success in InvByCodeF3 (combined case)";
    return inv; 
   end if;
   l := l + 1;
 until l gt #orbs;
 vprint Invariant,2 : "Failed";
 return false;
end function;

// Use codes over F_2
function InvByCode(IR,g,h)
 if not IsTransitive(g) then return false; end if;
 mp := MinimalPartitions(g);
 mp := [a : a in mp | 2 eq #Representative(a)];
 if #mp eq 0 then return false; end if;
 
 mp := mp[1];
 phi := Action(g,mp);
 kg := Kernel(phi);
 kh := kg meet h;

 if kg eq kh then return false; end if; // we do not have an E-invariant for g subset h

 vprint Invariant,2 : "Trying InvByCode in degree",Degree(g);

 rep_l := [Representative(a) : a in mp];  

 phi := Action(g,mp);
 bg,pi := StandardGroup(Image(phi));

// Represent the the kernel as a F_2 vectorspace.
 mat_g := Matrix(GF(2),[[(b eq b^a) select 0 else 1 : b in rep_l] : a in GeneratorsSequence(kg)] 
                       cat [[0 : i in [1..#rep_l]]]);
 mat_h := Matrix(GF(2),[[(b eq b^a) select 0 else 1 : b in rep_l] : a in GeneratorsSequence(kh)]
                       cat [[0 : i in [1..#rep_l]]]);


 code_g := LinearCode(mat_g);
 code_h := LinearCode(mat_h);

 dual_g := Dual(code_g);
 dual_h := Dual(code_h);

// AddAutomorphisms(d); 


 if (Dimension(code_g) gt 16 and Dimension(dual_g) gt 16) or
    (Dimension(code_h) gt 16 and Dimension(dual_h) gt 16) then 
// Codes are to big for complete search. This can only happen for polynomials of degree > 64
  vprint Invariant,2 : "Failed! Code to big.";
  return false;
 end if;
 
 wt_g := WeightEnumerator(dual_g);
 wt_h := WeightEnumerator(dual_h);

 w_diff := wt_h - wt_g; // Weight-Numberator for the linear forms that vanish on k_h but not an k_g

 zz := PolynomialRing(Integers()); x := zz.1;
 w_diff := Evaluate(w_diff,[1,x]);
 
 v := Valuation(PowerSeriesRing(Integers())!w_diff); // Smallest weight of a word in dual_h \setminus dual_g

 if MonomialCoefficient(Evaluate(wt_h,[1,x]),x^v) gt 10^5 then // to many words!
  vprint Invariant,2 : "Failed! Code to big.";
  return false;
 end if;

 words := WordsOfBoundedWeight(dual_h, v, v); 
 
 words := {a : a in words | not a in dual_g};
 w_sup := {Support(a) : a in words};
 
 supp := [];
 while #w_sup gt 0 do
  orb := Orbit(bg,Representative(w_sup));
  Append(~supp, orb);
  w_sup := {a : a in w_sup | not a in orb};
 end while;  
 
 e1,e2 := Min([#a : a in supp]);
 
 start := Representative(supp[e2]); // Code word we want to use for the invariant

 stab := Stabilizer(bg, start);

 g0 := (phi^-1)((pi^(-1))(stab));
 ind := [mp[i] : i in start]; 
 
 R := SLPolynomialRing(Integers(),Degree(g):Global);
 if Characteristic(IR) ne 2 then
  inv0 := &*[R.Min(a) - R.Max(a) : a in ind];
 else
  inv0 := [1,0];
  for a in ind do
   inv0 := [inv0[1] * R.Min(a) - inv0[2] * R.Max(a), inv0[1] * R.Max(a) + inv0[2] * R.Min(a)];
  end for;
 end if;
// inv0 is a relative invariant for ker_h subset ker_g.
// It defines an representation of stab. 
//
// We have to combine it with an invariant for a subgroup of phi(stab)
// to get an invariant for h meet stab subset h.

 h0 := g0 meet h;
 hom_inv0 := hom<g0 -> Sym(2) | [&*[(Min(akt)^a lt Max(akt)^a) select Sym(2)![1,2] else Sym(2)![2,1]  : akt in ind]  
                                    : a in GeneratorsSequence(g0)] >;

 k0 := Kernel(hom_inv0);
 if not h0 subset k0 then // we have to combine with something from the image of phi

// Direct product of hom_inv_0 and bg
  dp,incl,proj := DirectProduct(Sym(2), bg);
 
  im_g0 := sub<dp | [incl[1](hom_inv0(a)) * incl[2](pi(phi(a))) : a in GeneratorsSequence(g0)]>;
  im_h0 := sub<dp | [incl[1](hom_inv0(a)) * incl[2](pi(phi(a))) : a in GeneratorsSequence(h0)]>;
  assert im_h0 subset im_g0;
  assert Order(im_h0) lt Order(im_g0);

  IndentPush();
  inv_aux := GaloisGroupInvariant(IR, im_g0,im_h0); 
  IndentPop();
  if Characteristic(IR) eq 2 then
   inv1 := Evaluate(inv_aux, inv0 cat [&+[R.i : i in a] : a in Labelling(Image(phi))]);
  else
   inv1 := Evaluate(inv_aux, [inv0,-inv0] cat [&+[R.i : i in a] : a in Labelling(Image(phi))]);
  end if;
 else
  if Characteristic(IR) eq 2 then inv1 := inv0[1]; else inv1 := inv0; end if;
 end if;
 
 inv := InduceInvariant(IR, g,h, g0, g0 meet h, inv1, &+[R.i : i in &join ind]); 
 vprint Invariant,1 : "Success in InvByCode";

 return inv;
end function;


function Part4ToPart2Inv(IR,G,H)
 part_G := AllPartitions(G);
 if (2 in [#b : b in part_G]) or (not 4 in [#b : b in part_G]) 
    or IsOdd(Index(G,H)) then return false; end if; // not the case we are looking for

 vprint Invariant,2 : "Trying Part4ToPart2Inv in degree",Degree(G);

// Have to find a subgroup of G that has a blocksystem of blocksize 4
// 1st try: Use the derived subgroup:
 g0 := G;
 suc := false;
 for i := 1 to 2 do 
  g0 := DerivedSubgroup(g0);
  if IsTransitive(g0) and (not suc) then
   p_der := MinimalPartitions(g0);
   p2 := [a : a in p_der | #Representative(a) eq 2];
   if #p2 gt 0 then
    suc := true;
    ind := [Index(H,Stabilizer(H,Representative(a))) : a in p2];
    e1,e2 := Min(ind);
    p2 := p2[e2]; // Keep the subgroup as big as possible -- cheap induction. 
   end if;
  end if;
 end for;

 suc := false;

 if suc then
  g1 := G meet WreathProduct(p2);
  h1 := H meet g1;
  if (h1 ne g1) and (IsTransitive(g1)) then
   IndentPush();
   inv0 := GaloisGroupInvariant(IR,g1,h1);
   IndentPop();
   R := Parent(inv0);
   marker := &+[&*[R.j : j in bl] : bl in p2];
   inv1 := InduceInvariant(IR, G, H, g1, h1, inv0, marker);
   if inv1 cmpne false then
    vprint Invariant,2 :"Sucess in Part4ToPart2Inv (derived subgroup case)",inv0`GalInvType, Index(H,h1);
    return inv1;
   end if;
  end if; 
 end if;

// Approach didn't work. Try to start from 2-Sylow-subgroup:
 s2 := SylowSubgroup(G,2);
 if Index(G,s2) gt 2 * Degree(G)^2 then 
       vprint Invariant,2 : "Failed!"; return false; end if; // Index to big for this approach
  phi := CosetAction(G,s2);
  bg := Image(phi);
  part := AllPartitions(bg);
  part := SetToSequence(part);
  Sort(~part,func<a,b | #b - #a>);
  Append(~part,{1});
  s1l := [(phi^-1)(Stabilizer(bg,a)) : a in part];
  Sort(~s1l, func<a,b | Order(a) ne Order(b) select #b - #a else Min([#c : c in Orbits(a)]) - Min([#c : c in Orbits(b)])  >);
  for g1 in s1l do
   inv0 := false;
   if IsTransitive(g1) then
    part2 := AllPartitions(g1);
    if 2 in [#b : b in part2] then
     for wl in [4,2,3,5] do
      IndentPush();
      inv0 := GaloisGroupInvariant(IR,g1,g1 meet H : Worklevel := wl);
      IndentPop();
      if inv0 cmpne false then 
       break wl; 
      end if;
     end for;
     IndentPush();
     if inv0 cmpeq false then inv0 := InvByCode(IR,g1,g1 meet H); inv0`GalInvType := "Other"; end if;
     IndentPop();
     if inv0 cmpne false then 
      R := Parent(inv0);     
      marker := &+[&+[&+[R.i : i in b]^2 : b in Orbit(g1,a)] : a in part2 | not a in part_G];   
     end if;
    end if;
   else
    IndentPush();
    inv0 := IntransitiveInvariant(IR, g1,g1 meet H);
    IndentPop();
    orb := Orbits(g1 meet H);
    R := Parent(inv0); inv0`GalInvType := "Other";
    marker := &+[j * (&+[ R.i : i in orb[j]]) :  j  in [1..#orb]];
   end if;
   if inv0 cmpne false then
    inv1 := InduceInvariant(IR, G, H, g1, g1 meet H, inv0, marker);
    if inv1 cmpne false then
     vprint Invariant,1 : "Success in Part4ToPart2Inv (2-Sylow-Subgroup case)",inv0`GalInvType, Index(H,g1 meet H);
     return inv1;
   end if;
  else
//   printf"No sub-invariant found\n";
  end if; 
 end for;

 vprint Invariant,2 : "Failed!";
 return false;
end function;


function BlockSimplifyInv(IR,G,H)
 if not IsTransitive(G) then return false; end if;
 if IsPrimitive(G) then return false; end if;

 part := SetToSequence(AllPartitions(G)); 
 if #AbelianInvariants(AbelianQuotient(G)) gt 5 then // Limit the number of groups generated in ShrinkWreathProduct
  part := [a : a in part | #a le 10]; 
 end if; 
 Sort(~part,func<a,b | #a - #b>);

 vprint Invariant,2:"Trying SimplifyBlockInv. Have",#part,"block systems to try.";
 rr := SLPolynomialRing(Integers(),Degree(G):Global);	  

 old_g := {};
 for B in part do
  grl := ShrinkWreathProduct(G,B);
  grl := [ a : a in grl | not a in old_g];
  old_g := old_g join Set(grl);
  grl := [a : a in grl | (a ne G) and (not a subset H)];
  Sort(~grl,func<a,b | Order(b) - Order(a)>);
  if #grl gt 0 then
   vprint Invariant,3:"Trying block",B,"have",#grl,"subgroups available";  
  end if;
  for start in grl do
   p2 := AllPartitions(start);
   np := [a : a in p2 | not a in part];
// Make sure that induction of invariant will work. 
// We will use the new block system for the marker. Thus, start has to be the stabilizer of the partition.
   np := [a : a in np | #Orbit(H,a) eq Degree(H) div #a * Index(H,H meet start)]; 
   if #np gt 0 then
    Sort(~np, func<a,b | #b - #a>);
    h0 := start meet H; 
    for i := 1 to #np do
     phi := Action(start,Orbit(start,np[i]));
     if Order(phi(h0)) lt Order(phi(start)) then
      std,pi := StandardGroup(Image(phi)); 
      IndentPush();
      inv0 := GaloisGroupInvariant(IR, std,pi(phi(h0)));
      IndentPop();
      inv0 := Evaluate(inv0,[&+[rr.j : j in a] : a in Labelling(phi(h0))]);   
      if Characteristic(IR) eq 2 then ex := 3; else ex := 2; end if; 
      marker := &+[&+[rr.j : j in a]^ex : a in Orbit(start,np[i])];
      inv := InduceInvariant(IR, G,H,start,h0,inv0,marker);
      if inv cmpne false then
       vprint Invariant,1:"Success in SimplifyBlockInv. (E-case)";
       return inv;
      end if;	  
     end if;	 
    end for;	
   end if;
  end for;
 end for;
 vprint Invariant,2:"Fail in SimplifyBlockInv.";
 return false;
end function;


function HardBlockSimplifyInv(IR,G,H)
 if not IsTransitive(G) then return false; end if;
 if IsPrimitive(G) then return false; end if;

 part := SetToSequence(AllPartitions(G)); 
 if #part ne 1 then
  return false;
 end if;
 vprint Invariant,2:"Trying HardSimplifyBlockInv.";
 rr := SLPolynomialRing(Integers(),Degree(G):Global);	  
 
 B := Representative(part);
 lo := LowIndexSubgroups(G,7);
 lo := [u : u in lo | IsTransitive(u) and (#AllPartitions(u) gt 1)];
 if #lo eq 0 then
  vprint Invariant,2:"Fail in HardSimplifyBlockInv. No starting group found.";
  return false;
 end if;
 start := lo[1];
 h0 := start meet H;
 if h0 eq start then
  vprint Invariant,2:"Fail in HardSimplifyBlockInv. Starting group skew.";
  return false;
 end if; 

 IndentPush();
 inv0 := GaloisGroupInvariant(IR, start, h0);
 IndentPop();

 np := [a : a in AllPartitions(start) | a ne B];
 if Characteristic(IR) eq 2 then ex := 3; else ex := 2; end if; 
 marker := &+[&+[rr.j : j in a]^ex : a in Orbit(start,np[1])];
 
 inv := InduceInvariant(IR, G,H, start,h0,inv0,marker);
 if inv cmpne false then
  vprint Invariant,1:"Success in SimplifyBlockInv. (E-case)";
  return inv;
 end if;	  
 vprint Invariant,2:"Induction failed in HardSimplifyBlockInv.";
 return false;
end function;


// Prints the SL-Poly akt into a string. 
// Multiply used subexpressions will be presented as T_xxx
// returns the indices of used subexpressions as 2nd result
// Increases the counter of subexpressions 
function print_slpoly_(akt, sub_l, cnt_l, level_1)
 
 op1,op2 := Operands(akt);
 opt := Operator(akt);
 if opt in {"var","const"} then
  return Sprint(akt),[];
 end if;

// Print reference for repreted subexpressions:
 if not level_1 then
  i1 := Index(sub_l, akt);
  if i1 gt 0 then
   if cnt_l[i1] gt 1 then
    return Sprintf("T_%o",i1),[i1]; 
   end if;  
  end if; 
 end if;
 
 s1,u1 := print_slpoly_(op1,sub_l,cnt_l,false);
 if opt eq "^" then
  s2 := Sprint(op2);
  u2 := [];
 else 
  s2,u2 := print_slpoly_(op2,sub_l,cnt_l,false);
 end if;

 if level_1 then
  return s1 cat opt cat s2, u1 cat u2;
 end if;

 return "(" cat s1 cat opt cat s2 cat ")", u1 cat u2;
end function;

intrinsic PrettyPrintInvariant(inv0 :: RngSLPolElt) -> MonStgElt
{Prints an SL Polynomial to string like it is stored internally.}
// Eliminate all permutations in the SL-Poly
 inv := Evaluate(inv0,[Parent(inv0).i : i in [1..Rank(Parent(inv0))]]);

// Build up a list of subexpressions
 cnt_l := [1];
 sub_l := [inv];
 ref_ll := [[]];
 op_l := []; 
 que := [ inv0 ]; 
 while #que gt 0 do
  akt := que[1]; 
  ops1,ops2 := Operands(akt);
  op := Operator(akt);
  if not op in {"const","var"} then
   i1 := Index(sub_l,ops1);
   i2 := Index(sub_l,ops2);
   if i1 eq 0 then 
     Append(~sub_l,ops1); Append(~cnt_l,1); Append(~que,ops1);
	 Append(~ref_ll,[]); 
	 i1 := #sub_l;  
   else
     cnt_l[i1] := cnt_l[i1] + 1; 
   end if;   
   if i2 eq 0 then 
     Append(~sub_l,ops2); Append(~cnt_l,1); Append(~que,ops2);
	 Append(~ref_ll,[]);
	 i2 := #sub_l;  
   else
     cnt_l[i2] := cnt_l[i2] + 1; 
   end if;   
   i0 := Index(sub_l,akt);
   Append(~ref_ll[i1],i0);
   Append(~ref_ll[i2],i0);
  end if;
  Remove(~que,1); 
 end while; 
 
 // Count how often we have already refered to a subexpression
 ucl := [0 : i in [1..#cnt_l]];
 to_print := {}; 
  
 s,to_do := print_slpoly_(sub_l[1], sub_l, cnt_l,true);
 to_print := to_print join Set(to_do);
 for i in to_do do
  ucl[i] := ucl[i] + 1;
 end for;

 
 while #to_print gt 0 do
/*  printf"\n\n";
 s;
 cnt_l;
 ucl; 
 to_print;
 [cnt_l[i] : i in to_print];
 [ucl[i] : i in to_print]; */

  print_now := [a : a in to_print | ucl[a] eq cnt_l[a]]; 
  Sort(~print_now);
  assert #print_now gt 0;
  for akt in print_now do
   s1, to_do := print_slpoly_(sub_l[akt], sub_l, cnt_l,true);
   to_print := to_print join Set(to_do);
   for i in to_do do
    ucl[i] := ucl[i] + 1;
   end for;   
   s := s cat " where T_" cat IntegerToString(akt) cat " := " cat s1;  
  end for; 
  to_print := to_print diff Set(print_now);
 end while;
 
 return s;
end intrinsic;

