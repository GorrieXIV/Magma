freeze;
//

declare verbose ShortCosets, 2;

intrinsic ShortCosets(p::GrpPCElt, H::GrpPC, G::GrpPC:Limit := 10^6) -> []
  {Finds representatives for all right cosets of G modulo H that contain p.}

  assert H subset G;
  vprint ShortCosets, 1: "ShortCosets (PC group): start",Order(p), #H, #G;
  if Index(G, H) le 1000 or (Order(H) gt 2^30 and Index(G,H) lt 10000) then 
// Threshold should dynamically depend on the Size of G and H
    vprint ShortCosets, 1: 
       "Small index case in ShortCosets, using the direct approach";
    c := RightTransversal(G, H);
    R := [ x : x in c | p^x^-1 in H];
    return R;
  else
/*    if #H gt 2^40 or (#AbelianQuotient(H) gt 10000) then */
      vprint ShortCosets, 2: "ShortCosets: computing core";
      vtime ShortCosets, 1: U := Core(G, H);
      if #U gt 1 then
        GG, mGG := quo<G|U>;
        HH := mGG(H);
        p := p@mGG;
      else
        GG := G;
        HH := H;
      end if;
/*    else
      GG := G;
      HH := H;
    end if; */
    if #U gt 1 then 
     vprint ShortCosets,2: "Core size",#U,"reduces to groups of size",Order(p),#HH,#GG;
    else
     vprint ShortCosets,2: "Core is trivial";
    end if; 
    vtime ShortCosets,2: C := ConjugacyClasses(HH);
    R := [];
    vtime ShortCosets,2: CGp := Centralizer(GG, p);
    for c in C do
      vprintf ShortCosets,2: ".";
      f, g := IsConjugate(GG, c[3], p);
      if f then
        vprintf ShortCosets,2: "!"; 
        assert p eq c[3]^g;
        CHg := Centralizer(HH^g, p);
        if Index(CGp, CHg) gt Limit-#R then
          if GetVerbose("GaloisGroup") ge 2 or GetVerbose("ShortCosets") ge 1 then
            "2:ShortCosets: returning false";
          end if;
          return false;
        end if;
        A := RightTransversal(CGp, CHg);
        R cat:= [g*x : x in A];
        if #R gt Limit then
          if GetVerbose("GaloisGroup") ge 2 or GetVerbose("ShortCosets") ge 1 then
            "2:ShortCosets: returning false";
          end if;
          return false;
        end if;
      end if;
    end for;
    vprintf ShortCosets,2: "Loop done.\n";
  end if;
  if GetVerbose("GaloisGroup") ge 3 or GetVerbose("ShortCosets") ge 1 then
    "ShortCosets: returning a coset of size ", #R, " instead of ", #G div #H;
  end if;
 
  if IsIdentical(GG, G) then
    return R;
  else
    return [x@@mGG : x in R];
  end if;
end intrinsic;

/* Computing short cosets by using conjugacy classes */
function ShortCosets_CC(p, H, G, Limit)
// "ShortCosets_CC", Order(G),Order(H);
 c := CycleStructure(p);
 C := ConjugacyClasses(H);
 C := [ x : x in C | CycleStructure(x[3]) eq c];
 vprint ShortCosets, 2: "Removed some (hopefully) remaining: ", #C;
 R := [];
 CGp := Centralizer(G, p);
 for c in C do
   f, g := IsConjugate(G, c[3], p);
   if f then
     assert p eq c[3]^g;
     CHg := Centralizer(H^g, p);
     if Index(CGp, CHg) gt Limit-#R then
       if GetVerbose("GaloisGroup") ge 2 or GetVerbose("ShortCosets") ge 1 then
         "2:ShortCosets: returning false, Index is", Index(CGp, CHg);
       end if;
       return false;
     end if;
     A := RightTransversal(CGp, CHg);
     R cat:= [g*x : x in A];
     if #R gt Limit then
       if GetVerbose("GaloisGroup") ge 2 or GetVerbose("ShortCosets") ge 1 then
         "1:ShortCosets: returning false, too many cosets found", #G;
       end if;
       return false;
     end if;
   end if;
 end for;
 return R;
end function;

/* Compute Short Cosets by using a BlockQuotient in case that this leads to a permutation group of smaller degree */
function ShortCosets_BlockQuotient(p, H, G, Limit)

 vprintf ShortCosets, 2: "Searching for a quotient to construct short cosets. Group of order %o\n",Order(G);
/* Pretest: Don't know wether this is a speed up.
 U := Core(G,H);
 if Order(U) eq 1 then  
  return ShortCosets_CC(p,H,G, Limit);
 end if; */
 part := SetToSequence(AllPartitions(G));
 for a in part do
  s1 := Stabilizer(G,a);
  phi := Action(s1,GSet(s1,a));
  bg := Image(phi);
  ugv := Subgroups(bg:IndexLimit := #a-1); 
  ugv := [u`subgroup : u in ugv];
  Sort(~ugv,func<a,b|#b-#a>);
  ugv := [(phi^(-1))(u) : u in ugv]; /* We want to try the coset-action of g on these groups */
  for j := 1 to #ugv do
   phi := CosetAction(G,ugv[j]);
   im_G := phi(G); im_H := phi(H);
//   #im_G, #im_H;  
// Check that the index of the image is the same as the index of the inital groups.
   if (Order(im_G) lt Order(G)) and (Order(im_G) / Order(im_H) eq Order(G) / Order(H)) then
    vprintf ShortCosets, 2: "Quotient of Order %o found\n",Order(im_G);
    sc := ShortCosets(phi(p), im_H, im_G: Limit := Limit); 
    if sc cmpeq false then return sc; end if;
    return [(phi^(-1))(c) : c in sc];
   end if;
  end for;
 end for;
 vprintf ShortCosets, 2: "No quotient found\n";
 return ShortCosets_CC(p,H,G,Limit);
end function;


/* Generate a list of trivial homomorphism starting at G */
function TrivialHoms(G)
 
 orbs := Orbits(G);
 res := [* *];
 for akt in orbs do
  phi := Action(G,akt);
  _, pi := StandardGroup(Image(phi));
  Append(~res, phi * pi);
  bg := Image(phi);
  part := AllPartitions(bg);
  for p in part do
   phi2 := Action(bg,Orbit(bg,p));
   _, pi := StandardGroup(Image(phi2));
   Append(~res, phi * phi2 * pi);
  end for;
 end for;

 abq,pi := AbelianQuotient(G);
 Append(~res, pi);
 if Order(abq) ne 1 then
  if IsCyclic(Image(pi)) then
   d1 := DerivedSubgroup(G);
   d2 := DerivedSubgroup(d1);
   if d1 ne d2 then
    ind := Index(G,d2);
    if (ind le 10^3) then
     qu2,pi2 := quo<G | d2>;
    else
     sol,pi_sol := SolvableQuotient(G);
     qu2,pi_2 := quo<sol | pi_sol(d2)>;
     pi2 := pi_sol * pi_2;
     assert pi2(Random(G)) in qu2;
    end if;
    Append(~res,pi2);
    for p in PrimeDivisors(Order(Image(pi2))) do
     qu3,pi3 := pQuotient(Image(pi2), p, 2);
     pp := pi2 * pi3;
     assert pp(Random(G)) in qu3;
     Append(~res,pp);
    end for;        
   end if;
  end if;
 end if;
 return res;
end function;


intrinsic ShortCosets(p::GrpPermElt, H::GrpPerm, G::GrpPerm:Limit := 10^6) -> []
 {Finds representatives for all right cosets of G modulo H that contain p.}

 assert H subset G;
 vprintf ShortCosets, 2: "ShortCosets: start group orders %o %o\n",Order(G), Order(H);

// Small index, just do it naively
 if (Index(G, H) le 1000) or (Index(G,H) le 10000 and Order(H) gt 2^30)  then 
 // Threshold should depend on the Size of G and H
  vprintf ShortCosets, 1: "Small index (%o) in ShortCosets, using the direct approach\n",Index(G,H);
  c := RightTransversal(G, H);
  R := [ x : x in c | p^x^-1 in H];
  vprintf ShortCosets, 1: "ShortCosets: returning a coset of size %o instead of %o\n", #R, #G div #H;
  return R;
 end if;
 
 if Order(H) lt 10^6 then // group H is small, no reduction necessary
  R := ShortCosets_CC(p,H,G,Limit);  
  vprintf ShortCosets, 2: "ShortCosets: returning a coset of size %o instead of %o\n", 
                          (R cmpne false) select #R else "FAIL", #G div #H;
  return R;
 end if;
// "Trying subgroup reduction in short cosets";
// Order(G), Order(H);
// Now we try to reduce the problem...
 G1 := G; H1 := H;
 repeat
  G2 := G1; H2 := H1;
  vprintf ShortCosets,2: "ShortCosets: Searching for homomorphisms for subgroup reduction\n";
  hl := TrivialHoms(G1);
  for f in hl do
   if (f(G1) eq f(H1)) and (sub< Image(f) | f(p)> ne Image(f)) then
    f2 := hom< G1 -> Image(f) | [f(a) : a in GeneratorsSequence(G1)]>;
    G1 := sub<G1 | Kernel(f2), p>;
    H1 := G1 meet H1;
   end if;
  end for;
 until G2 eq G1;

 if GetVerbose("ShortCosets") ge 2 then
  printf "ShortCosets: reduced to group orders %o %o by reduction to subgroups\n",Order(G1),Order(H1);
  printf "Core size %o\n", Order(Core(G1, H1));
// If (G ne G1) we have no reason to believe that H1 is maximal in G1
  pc_q, pi_pc := SolvableQuotient(G1);
  printf "Image in solvabe quotient of size %o %o %o\n", Order(pc_q), Order(pi_pc(H1)),Order(pi_pc(p));
 end if;
 
// Try to map to pc case:
 der := G1;
 repeat
  der0 := der;
  der := DerivedSubgroup(der);
  if der subset H1 then  // Take quotient by der in the PC-category
   G_pc, pi := SolvableQuotient(G1);
   G_pc2, pi2 := quo<G_pc | pi(der)>;
   H_p2 := pi2(pi(H1));
   vprintf ShortCosets,2: "ShortCosets: Mapping to PC groups of orders %o %o\n",Order(H_p2), Order(G_pc2);
   vprintf ShortCosets,2: "Remaining core size %o\n", Order(Core(G_pc2, H_p2));
   IndentPush();
   res := ShortCosets(pi2(pi(p)), H_p2, G_pc2);
   IndentPop();
   if res cmpeq false then 
    return false;
   else
    res := [G!((a  @@ pi2) @@ pi) : a in res]; 
    assert forall{x : x in res | p^x^-1 in H};
    return res;
   end if;
  end if;
 until der eq der0;

 if (Order(H1) gt 2^40) and IsTransitive(G1) then
  R := ShortCosets_BlockQuotient(p,H1,G1,Limit);
 else
  R := ShortCosets_CC(p,H1,G1,Limit);     
 end if;
 vprintf ShortCosets, 2: "ShortCosets: returning a coset of size %o instead of %o\n", 
                         (R cmpne false) select #R else "FAIL", #G div #H;

 if R cmpne false then R := [G!a : a in R]; end if;  
 return R;
end intrinsic;

declare attributes GrpPerm : OptimalClass;


/* Given the group H return a Frobenius-Element for short cosets */
function pick_optimal_class(G,H, StartLimit, MaxLimit)

  if #H ne 1 then
    if IsSymmetric(G) then
      if assigned H`OptimalClass then
        p, h := Explode(H`OptimalClass);
        h := H!h;
      else
        c := Classes(H);
        ct := [ CycleStructure(x[3]) : x in c ];
        cs := Set(ct);
        p := Infinity();
        for a in cs do
          l := [c[x] :x in [1..#ct] | ct[x] eq a];
          pp := &+ [#Centralizer(G, x[3])*x[2]/#H : x in l];
          if pp lt p then
            p := pp;
            h := l[1][3];
          end if;
        end for;
        H`OptimalClass := <p, Eltseq(h)>;
      end if;
      StartLimit := Maximum(StartLimit, p);
      if p gt MaxLimit then
        return -1, _;
      end if;
    else
      h := [ Order(H.i) : i in [1..Ngens(H)]];
      _, h := Maximum(h);
      h := H.h;
    end if;
  else
    h := H.0;
  end if;
 return h, StartLimit;
end function;

/* Find a superset of all cosets G/m such that H is in the corresponding conjugate of m */
function candidates_for_conjugation(G,m,H,h, StartLimit, MaxLimit)

 if IsNormal(G, m) then
  vprint Invariant, 2: "IsNormal";
  return [G.1], h;
 end if;

 if Index(G, m) lt 100 then
  vprint Invariant, 2: "Transversal";
  return RightTransversal(G, m), h;
 end if;

 vprint Invariant, 2: "ShortCoset";
 c := ShortCosets(h, m, G:Limit := StartLimit);
 if c cmpeq false or #c gt StartLimit then
  vprint Invariant, 1: "Too many short cosets (", 
                       c cmpeq false select "way to many" else #c, "), trying again";
  hh := Order(h);
  li := StartLimit;
  attempt := 0;
  repeat
   repeat
    x := Random(H);
   until Order(x) ge hh;
   cc := ShortCosets(x, m, G:Limit := li);
   attempt +:= 1;
   if attempt mod 6 eq 0 then
    hh *:= 0.99;
   // printf "li was %o", li;
    if li eq MaxLimit then
     return -1, -1;
    end if;
    li := Round(li*1.4);
    li := Minimum(MaxLimit, li);
   end if;
  until cc cmpne false;
  if c cmpeq false or #cc lt #c then
   c := cc;
   h := x;
  end if;
 end if;
 
 return c,h; 
end function;

/* StartLimit, MaxLimit : control for short cosets and Frobenius-selection
   MaxLen: Maximal Length of descent chain. If chain is longer, we return only the first entries of the chain
   SubGroup: If subgroup is set, we try only to desecent to a conjugate of SubGroup directly.
             In this case the return values are true/false and the conjugating element.                  */
intrinsic InternalGetChain(G::GrpPerm, H::GrpPerm:MaxLen := Infinity(), 
                          SubGroup := false, Small := false, MaxLimit := Infinity(), StartLimit := 100) -> []
  {Computes a chain of maximal subgroups of G down to H}

  require H subset G : "H must be a subgoup of G";

  if SubGroup cmpne false then
   if Order(SubGroup) ne Order(H) then return false,_; end if;
  end if;

  C := [G];
  if (SubGroup cmpeq false) then
   repeat
    l_C := #C;
    hl := TrivialHoms(G);
    for f in hl do
     if Category(Image(f)) cmpeq GrpPerm then // Recursion is only possible in this category
      if (Order(f(G)) lt Order(G)) and (Order(f(H)) lt Order(f(G))) then
       f_res := hom<G -> f(G) | [f(a) : a in GeneratorsSequence(G)]>;
       dc := InternalGetChain(f_res(G), f_res(H): MaxLen := MaxLen - #C + 1, 
                            SubGroup := false, Small := Small, MaxLimit := MaxLimit, StartLimit := StartLimit);
       if dc cmpne -1 then
        for j := 2 to #dc do
         Append(~C,(f_res^(-1))(dc[j]));
        end for;
        G := C[#C];
       end if;
      end if;
     end if;
    end for;
   until #C eq l_C;  
  end if;
  if #C gt 1 then
   vprintf Invariant, 1: "Descent to group of order %o by use of homomorphisms\n",Order(C[#C]);
  end if;

  h,StartLimit := pick_optimal_class(G,H,StartLimit,MaxLimit);
  if h cmpeq -1 then return -1,_; end if;

  while #G gt #H and MaxLen ge #C do
    assert H subset G;
    if SubGroup cmpeq false then
      M := MaximalSubgroups(G:IsTransitive := IsTransitive(H), OrderMultipleOf := Order(H));
      M := [x`subgroup : x in M];
    else
      M := [SubGroup];
    end if;
    S := [];
    for m in M do
//      if #m lt #H then continue; end if; This case is eliminated earlier.
      c,h := candidates_for_conjugation(G,m,H,h,StartLimit, MaxLimit);      
      vprint Invariant, 1: "using ", #c, " cosets";
      for i in c do
        if H subset m^i then
          Append(~S, <i, m>);
        end if;
      end for;
    end for;
// S contains all decent options from G to a supergroup of H
    if #S gt 1 then
      vprint Invariant, 1: 
        "I'm confused - multiple decents possible, choosing the largest";
    end if;
    if #S eq 0 then
      vprint Invariant, 1: "must be done - no decent possible...";
      if SubGroup cmpne false then
        return false, _;
      end if;
      assert C[#C] eq H;
      return C;
    end if;
    if Small then
      _, i := Maximum([Order(x[2]) : x in S]);
    else
      _, i := Minimum([Order(x[2]) : x in S]);
    end if;
    G := S[i][2]^S[i][1];
    if SubGroup cmpne false then
      if G eq H then
        return true, S[1][1];
      else
        return false, _;
      end if;
    end if;
    Append(~C, G);
  end while;
  if SubGroup cmpne false then
    return false, _;
  end if;

  return C;
end intrinsic;
    
intrinsic MyIsMaximal(G::GrpPerm, H::GrpPerm) -> BoolElt
  {}
 
  require H subset G: "H must e a subgroup of G";
  if #H eq #G then return false; end if;
  for i in [1..10] do
    S := sub<G|H, Random(G)>;
    if S ne G and S ne H then
      return false;
    end if;
  end for;
  C := InternalGetChain(G, H:MaxLen := 2);  
  if #C lt 2 or #C[2] ne #H then
    return false;
  else
    return true;
  end if;
end intrinsic;

intrinsic MyIsConjugate(G::GrpPerm, H1::GrpPerm, H2::GrpPerm) -> BoolElt, GrpPermElt
  {}

  function ret_false()
    return false;
  end function;
  function ret_true()
    return true;
  end function;
  
  if #H1 ne #H2 then
    return false, _;
  end if;
  if H1 eq H2 then
    return true, G.0;
  end if;
  if IsAbelian(H1) then
    if not IsAbelian(H2) then 
      return false, _;
    end if;
    if AbelianInvariants(H1) ne AbelianInvariants(H2) then
      return false, _;
    else
      return IsConjugate(G, H1, H2);
    end if;
  end if;
  a,b := InternalGetChain(G, H2:SubGroup := H1, MaxLimit := 10^6);

  if a cmpeq -1 then
    return IsConjugate(G, H1, H2);
  end if;

  if a then
    return ret_true(), b;
  else 
    return ret_false(), _;
  end if;

//  return InternalGetChain(G, H2:SubGroup := H1);  This will never happen.
end intrinsic;


/* What is this function computing? */
intrinsic MyIsConjugateSubgroup(G::GrpPerm, H1::GrpPerm, H2::GrpPerm) -> BoolElt, GrpPermElt
  {}

  if Degree(H1) ne Degree(H2) then
    "Intersting case";
    if Degree(H1) mod Degree(H2) ne 0 then
      return false; // degrees don't match
    end if;
    A := AllPartitions(H1);
    A := [a : a in A | #a eq Degree(H1) div Degree(H2)];
    for a in A do
      O := Orbit(H1, a);
      h1 := StandardGroup(ActionImage(H1, O));
      if MyIsConjugateSubgroup(Generic(h1), h1, H2) then
        return true;
      end if;
    end for;
    return false;
  end if;
  if assigned H2`OptimalClass then
    c := H2!H2`OptimalClass[2];
  else
    c2 := Classes(H2);
    ct := [ CycleStructure(x[3]) : x in c2 ];
     cs := Set(ct);
     p := Infinity();
     for a in cs do
       l := [c2[x] :x in [1..#ct] | ct[x] eq a];
       pp := &+ [#Centralizer(G, x[3])*x[2]/#H2 : x in l];
       if pp lt p then
         p := pp;
         h := l[1][3];
       end if;
     end for;
     H2`OptimalClass := <p, Eltseq(h)>;
     c := h;
  end if;
  c := ShortCosets(c, H1, G);
  if c cmpeq false then
    return IsConjugateSubgroup(G, H1, H2);
  end if;
  for i in c do
    if H2 subset H1^i then
      return true, i;
    end if;
  end for;
  return false, _;
end intrinsic;

intrinsic MyIsConjugateQuotient(G::GrpPerm, H1::GrpPerm, H2::GrpPerm) -> BoolElt, GrpPermElt
  {Essentially cheks if H2 could be the Galois group of a subfield of H1}

    if not IsTransitive(H1) then
      O := Orbits(H1);
      np := Set(CartesianProduct(O));
      gs:= GSet(H1, np, map<car<np, H1> -> np| x:-><x[1][i]^x[2] : i in [1..#x[1]]>>);
      gs := Orbit(H1, gs[1]);
      mp := Action(H1, gs);
      H1 := mp(H1);
      H1 := StandardGroup(H1);
      G := Generic(H1);
    end if;
    if not IsTransitive(H2) then
      O := Orbits(H2);
      np := Set(CartesianProduct(O));
      gs:= GSet(H2, np, map<car<np, H2> -> np| x:-><x[1][i]^x[2] : i in [1..#x[1]]>>);
      gs := [Orbit(H2, x) : x in gs];
      _, p := Minimum([#x :x in gs]);
      gs := gs[p];
      mp := Action(H2, gs);
      H2 := mp(H2);
      H2 := StandardGroup(H2);
    end if;

    if Degree(H1) mod Degree(H2) ne 0 then
      return false; // degrees don't match
    end if;
    
    A := AllPartitions(H1);
    Include(~A, Support(H1));
    Include(~A, {1});
    A := [a : a in A | #a eq Degree(H1) div  Degree(H2)];
    for a in A do
      S := Stabiliser(H1, a);
      N := CosetImage(H1, S);
      assert Degree(N) eq Degree(H2);
      if MyIsConjugateSubgroup(Generic(N), N, H2) then
        return true;
      end if;
    end for;
    return false;
end intrinsic;

