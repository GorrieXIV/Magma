freeze;

declare verbose Invariant, 3;
import "Galois.m" : UseCache,  CacheHasInvar, CachePutInvar, get_tschirni, get_all_tschirni_universe, apply_tschirni, invar_coeff_ring,
                    PrecisionFromBound;

import "GalInvar.m" : SLPRGg;

//Past this degree, we cannot use "generic" intersection methods for
//permutation goups in Magma 2.12. It's not a good criterion as the 
//alternative algorithm is much slower, but....
critical_deg := 40;

//function MyInvars(G, d:LowDim := false, All := true)
intrinsic MyInvars(G::GrpPerm, d::RngIntElt:LowDim := false, All := true) -> .
  {Computes a representation of all invariants of degree d.}

  // My hypothesis is that a G-relative H-invariant of degree d (minimal)
  // as computed by InvariantsOfDegree has to be of the form
  // sum f in Orbit(m) f
  // This is supported by the fact that Gregor Kemper's Algorithm in Magma
  // does just creates objects of this type.
  // Assuming for a moment action of Sn instead of G we can "sort" the 
  // monomial m to arrange that the exponent vector is decreasing.
  // (AllPartitions does essentailly guarantee that)
  //
  // Futhermore, a generating monomial where the exponent set has gaps
  // can be considered to be "generated" by a lower degree invariant.
  // Here, we consider two monomials to be "essentailly" the same iff
  // the exponenent pattern is preserved, that is if
  // [ #[x : x in m | x eq y] : y in [1..d]] 
  // is the same for m and n.
  // This allows for moderately efficient enumeration.
  //
  // If we want all G inavriants of fixed degree we then have to consider
  // the double cosets of of Sn wrt. to G and the stabilizer of m:
  // We want to compute all orbits of (m^p) under G for an arbitrary element 
  // p of Sn (this is to offset the sorting we did in the beginning).
  // Obviously, if we change p by an element in the stabilizer (from the left)
  // we replace m^g by m^(sp) = (m^s)^p = m^p.
  // On the other hand, if we change p from the right by elements in G
  // we at lest land in the same orbit:
  // m^((pg)G) = m^p(gG) = m^pG,
  //
  // If we want to use this to get H-relative invariants only, and in
  // particular, those of minimal degree, we can reduce even further.
  // Since the action of G does not affect the expoenents, we can also assume
  // that the expoenent patterns are (reverse) sorted, for if not, then the
  // same pattern would have occured at a lower degree already.
  //
  

  n := Degree(G);
  R := PolynomialRing(Integers(), n:Global);
  AssignNames(~R, ["R." * IntegerToString(i) : i in [1..n]]);

  function parToM(p)
    return &* [ R.j^r[j] : j in [1..#p]] where r := p;
  end function;

  function getI(D)
    I := [];
    for i in [1..Minimum(D, n)] do
      P := Partitions(D, i);
      for p in P do
        if Maximum(p) le #Set(p) then 
          if not LowDim then
            pp := [ #[x : x in p | x eq y] : y in [1..Maximum(p)]];
            pp := Reverse(Sort(pp));
            if &+ [i*pp[i] : i in [1..#pp]] lt D then
              continue;
            end if;
          end if;
          Append(~I, <parToM(p), p>);
        end if;
      end for;
    end for;
    return I;
  end function;

  I := getI(d);

  // try to find out how many come from a lower dimension:
  function extend(m, d)
    //extends a low-dergee invariant to deg d - if possible.
    p := m[2];
    O := [];
    sum := function(a,b)
      c := a;
      for i in [1..#b] do
        c[i] +:= b[i];
      end for;
      return c;
    end function;
    function refines(a,b)
      i := 1;
      ai := a[1];
      bi := b[1];
      while i le #a do
        while i le #a and a[i] eq ai and b[i] eq bi do
          i +:= 1;
        end while;
        if #a lt i then
          if #b ge i then
            return b[i] ne bi;
          end if;
          return true;
        end if;
        if a[i] ne ai then
          if b[i] eq bi then
            return false;
          else
            ai := a[i];
            bi := b[i];
          end if;
        elif b[i] ne bi then
          bi := b[i];
        end if;
        i +:= 1;
      end while;
      if #b ge i then
        return b[i] ne bi;
      end if;
      return true;
    end function;

    for i in [1..#p] do
      P := Partitions(d-&+p, i);
      for x in P do
        if refines(x, p) then
          Append(~O, sum(p, x));
        end if;
      end for;
    end for;
    return [<parToM(x), x> : x in O];
  end function;
 
  if LowDim then
    low := 0;
    for i in [1..d-1] do
      t := getI(i);
      for m in t do
        e := extend(m, d);
        I cat:= e;
        low +:= #e;
      end for;
    end for;
    vprint Invariant, 2: "From lower dimensions we get ", low, 
                     " here ", #I - low, "total ", #I;
  else
    vprint Invariant, 2: 
           "Total of ", #I, " (primitive) invariants for this degree";
  end if;

  I := [x[1] : x in I];

  if not All then
    return I;
  end if;


  // to get all monomials (that may be useful) we have to
  // apply all permutations from S(n)
  // But as we are interested in the Orbits under H, we can restrict to
  // double cosets wrt to G and the stabilizers in S(n).
  //
  // There is a drawback: in the range I'm interested in,
  // DoubleCosetRepresentatives does not perform too well....

  min := false;
  O := [];
  vprint Invariant, 2: "Double cosets...";
  vtime Invariant, 2: for m in I do
    if true then
      vprint Invariant, 3: "Create Ladder....";
      S := StabilizerLadder(Sym(n), m);
      vprint Invariant, 3: "Process Ladder....";
      r := ProcessLadder(S, Sym(n), G);
      d := r`Di;
      DeleteData(r);
    else
      S := Stabilizer(Sym(n), m);
      vprint Invariant, 3: "Double Cosets....";
      vtime Invariant, 3: d := DoubleCosetRepresentatives(Sym(n), G, S);
    end if;
    for i in d do
      Append(~O, m^i);
    end for;
  end for;

  return O;
end intrinsic;

// Prove that I is not an invariant for one of the groups in listG
Check:=function(I,listG)
  for G in listG do
    if not false in {IsInvariant(I,g):g in GeneratorsSequence(G)} then
       return false;
    end if;
  end for;
  return true;
end function;


intrinsic RelativeInvariant(IR::Rng, G::GrpPerm, H::GrpPerm: IsMaximal := false, Risk := false) -> RngSLPolElt
{For H<G compute a G-relative H-invariant, ie. Stab_G(I) eq H where S contains
information about the polynomial whose Galois group is being computed and the
mapping from it coefficient ring into the completion used for computing roots}
    require H subset G: "2nd group must be a subgroup of the first";
  if IsTransitive(G) and (IsRegular(G) or
     IsMaximal or IsPrime(Index(G, H))) then
    //IsRegular implies H being non-transitive, thus the GaloisGroupInvariant
    //is the the sum over the block 1^H - which, according to Kluener's 
    //thesis will be a correct invariant here...
    i := GaloisGroupInvariant(IR, G, H:Worklevel := -1); //, NoGeneric);
    if i cmpne false then
      return i;
    end if;
  end if;

  f:=CosetAction(G,H);
  U:=Image(f);
  M:=MinimalPartitions(U);
  part:=Flat([[x:x in y |1 in x] : y in M]);
  if #part eq 0 then //IsMaximal!
     return GaloisGroupInvariant(IR,G,H);    
  end if;

  Invs:=[];
  SS:=[Stabilizer(U, x) @@f:x in part];//Minimal overgroups of H 
  for i in [1..#part] do
      I:= GaloisGroupInvariant(IR,SS[i],H);
      if Check(SLPRGg(IR,I), SS) then 
	 vprint Invariant,1: "lucky case";//one of those invariants is G-relative
	 return I;
      end if;
      if (i eq 1) or (BaseRing(Parent(I)) cmpeq BaseRing(Parent(Invs[1]))) then
       Append(~Invs,I);
      else
       if BaseRing(Parent(I)) cmpeq Integers() then 
        Append(~Invs,SLPRGg(IR,I));
       else
        Invs := [SLPRGg(IR,a) : a in Invs] cat [I];
       end if;
      end if;
  end for;

  vprint Invariant,1: "combining invariants for non-maximal subgroup";
  Invs := [SLPRGg(IR,a) : a in Invs];
  I := Parent(Invs[1])!0;
  tr := Transversal(G,H);
  tr := [a : a in tr | not a in H]; // representatives of all non-trivial cosets
  ccc := Characteristic(IR);

  suc := true;
  for i := 1 to #tr do
   if IsInvariant(I,tr[i]) then
   j := 1; 
   while (j le #Invs) and IsInvariant(Invs[j], tr[i]) do j := j + 1; end while;
   if j gt #Invs then suc := false; break i; end if;
    m := 1;
    iter := 1;
    repeat
     I2 := I + Invs[j] * m;
     if ccc eq 0 then m := m + 1; iter := iter + 1; else
      iter := iter + 1;
      m := 0;
      ex := 0;
      repeat
       m := m + IR.1^ex * ((iter div ccc^ex) mod ccc);
       ex := ex + 1;
      until ccc^ex gt iter;
     end if;
    until &and [not IsInvariant(I2,tr[k]) : k in [1..i]];    
    I := I2;
   end if;
  end for;  
//  "End of combine loop";  

  if suc then 
   assert &and [not IsInvariant(I,a) : a in tr];
   return I; 
  end if;
  if not suc then
   vprint Invariant,1: "Can not combine invariants to a relative one. Using generic approach.";
  end if;
 
  I := MyRelativeInvariant(IR, G, H:IsMaximal := IsMaximal, Risk := Risk);
  if Type(I) eq List then
    ii := InternalGalInvBuild(I);
  else
    ii := InternalGalInvBuild(H, I);
  end if;

  return ii;
end intrinsic;

intrinsic RelativeInvariant(G::GrpPerm, H::GrpPerm:
  IsMaximal := false, Risk := false) -> RngSLPolElt
{For H<G compute a G-relative H-invariant, ie. Stab_G(I) eq H.}
    require H subset G: "2nd group must be a subgroup of the first";
    return RelativeInvariant(Integers(), G, H : IsMaximal := IsMaximal, Risk := Risk);
end intrinsic;

  
intrinsic MyRelativeInvariant(IR::Rng, G::GrpPerm, H::GrpPerm:
   Deg := false, LowDim := false, All := false, 
   IsMaximal := false, Risk := false, Raw := true) -> .
  {Computes G-Relative H-Invariant polynomials - or more precisely, a represntatio of them. If Deg is not given, a minimal degree invariant is computed.}

  require G ne H : "The groups need to be different!";
  if UseCache() then
    f, i := CacheHasInvar(G, H);
    if f then
      if Raw then
        return i("data");
      else
        return i;
      end if;
    end if;
  end if;

  if not IsMaximal then
    //require IsTransitive(G) and IsTransitive(H):
    //  "G and H must be transitive";
    vprint Invariant, 1:
       "H is not (known to be) maximal, compute decent chain...";
    C := InternalGetChain(G, H);
    if #C gt 2 then
//      require All cmpeq false :
//        "H is not maximal in G: cannot compute all invariants";
      I := [**];    
      use_risk := false;
      for i in [1..#C-1] do
        //TODO: see if we can us GetInvar from the galois package - it
        //      might be able to use better invariants.
        if Risk and IsTransitive(C[i+1]) then
          d := GaloisGroupInvariant(IR, C[i], C[i+1]);
          use_risk := true;
         else
          d := MyRelativeInvariant(IR, C[i], C[i+1]:
            Deg := Deg, LowDim := LowDim, All := All, IsMaximal);
        end if;
        Append(~I, <d, C[i+1]>);
      end for;
      // now we need to make sure that the invatiants don't interfere with
      // each other. For all we know, the monomials might be identical.
      // There are two possibilities:
      // - if we know that we compute the Orbit sum and not the sum over all
      //   elements in the subgroup (ie. in the resulting polynomial all
      //   coefficients are 1) then we can scale by any factor to seperate
      //   them.
      // - if we cannot assume the latter (which technically currently we
      //   cannot, I think) we have to seperate them by multiplying with some
      //   non-interfering monomial.
      if use_risk then
        return I;
      end if;
      d := { TotalDegree(i[1]) : i in I};

      function return_I(I)
        if UseCache() then
          i := InternalGalInvBuild(I);
          CachePutInvar(G, H, i);
          if Raw then
            return I;
          else
            return i;
          end if;
        end if;
        if Raw then
          return I;
        else
          return InternalGalInvBuild(I);
        end if;
      end function;

      if #d eq #I then
        return return_I(I);
      end if;
      n := Degree(G);
      d := [ {* #{ j : j in [1..n] | Exponents(i[1])[j] eq k} :
                               k in [0..TotalDegree(i[1])]*} : i in I];
      if #Set(d) eq #I then
        return return_I(I);
      end if;
      vprint Invariant, 1: 
           "Changing the invariants to assert disjoint orbits...";
      ds := { TotalDegree(i[1]) : i in I};
      md := SequenceToMultiset(d);
      for i in [1..#I] do
        if Multiplicity(md, d[i]) gt 1 then
          m := Maximum(Exponents(I[i][1]));
          m := &* [ R.j : j in [1..n] | Exponents(I[i][1])[j] eq m] 
                    where R := Parent(I[i][1]);
          repeat
            I[i][1] *:= m;
          until TotalDegree(I[i][1]) notin ds;
          Include(~ds, TotalDegree(I[i][1]));
          Exclude(~md, d[i]);
        end if;
      end for;
      return return_I(I);
    else
      vprint Invariant, 1: "H was maximal after all, continueing";
    end if;
  end if;
      
  Q := Rationals();  

  if Deg cmpeq false then
    n := Degree(G)-10;
    repeat
      n +:= 10;
      hil_G := MolienSeriesApproximation(G, n);
      hil_H := MolienSeriesApproximation(H, n);
    until Valuation(hil_H - hil_G) lt n;
    d := Valuation(hil_H - hil_G);
    found_max := LeadingCoefficient(hil_H - hil_G); // wrong
  else 
    d := Deg;
    found_max := 3;
  end if;

  vprint Invariant, 1: "Invars of degree ", d, "...";
  if All then
    LowDim := true;
  end if;

  R := Sym(Degree(G));
  if All then
    vprint Invariant, 3: "Computing all invariants for H...";
    vtime Invariant, 3: I := MyInvars(H, d:All, LowDim);
    I := [ x : x in I | #G/#Stabilizer(G, x) ne #H/#Stabilizer(H, x)];
    s := [ #Stabilizer(H, x) : x in I];
//    return I, s;
    _, p := Maximum(s);
    return I[p], Stabilizer(H, I[p]);
  else
    vprint Invariant, 3: "Computing generating invariants...";
    vtime Invariant, 3: I := MyInvars(H, d:All := false, LowDim := LowDim);
  end if;
  vprint Invariant, 2: "There are ", #I, " generating invariants of degree", d;

  if Degree(G) lt critical_deg then
    vprint Invariant, 2: "Stabilizers...";
    vtime Invariant, 2: I := [<x, Stabilizer(R, x)> : x in I];
  else
    I := [<x, false> : x in I];
  end if;

  found := [];
  found_first := 0;
  found_last := 0;
  attempt := 0;
  vprint Invariant, 1: "There exists only  ", found_max, " invars";    
  if found_max le 0 then
    return false, _;
  end if;
  found_max := Minimum(found_max, 5);
  vprint Invariant, 1: "Looking for at most ", found_max, " invars";
  vprint Invariant, 1: "Search...";

  //SetSeed(1,10000);

  K := GF(NextPrime(2^30));
  evl := [Random(K) : x in [1..Degree(H)]];
  //a,b := GetSeed();
  function OK(x, r)
    return #DoubleCoset(R, G, r, x[2]) ne #DoubleCoset(R, H, r, x[2]);
  end function;    
  function OK(x, r)
    if Degree(G) lt critical_deg then
      S := G^r^-1 meet x[2];
      SH := S meet H^r^-1;
      /*
      assert Stabilizer(R, x[1]) eq x[2];
      sg := Stabilizer(G, x[1]^r);
      assert sg eq S^r;
      assert (#G div #sg ne #H div #(H meet sg)) eq
             (#G*#SH ne #H*#S);
      */       
     
      return #G*#SH ne #H*#S;
    else
      sg := Stabilizer(G, x[1]^r);
      return #G div #sg ne #H div #(H meet sg);
    end if;
  end function;    
  repeat
    //SetSeed(a,b);
    r := Random(R);
    //a,b := GetSeed();
    if exists(x){x : x in I | OK(x, r)} then
      vprint Invariant, 2: "found", r, x[1], "after ", attempt, "tests";

      if found_first eq 0 then
        found_first := attempt;
      end if;

      if All then
        j := InternalGalInvBuild(x[1]^r, H);
        im := Evaluate(j, evl);
        if Position([y[3] : y in found], im) eq 0 then
          vprint Invariant, 2: "new invar of cost", NumberOfOperations(j, "*"), 
                               " now a total of", #found+1, " invars found";
          Append(~found, <r, x, im, NumberOfOperations(j, "*")>);
        else
          vprint Invariant, 2: "old invar found again";
        end if;
      else
        Append(~found, <r, x, 1, #H div #Stabilizer(H, x[1]^r)>);
      end if;
      found_last := attempt;
    end if;
    attempt +:= 1;
    if attempt mod 100 eq 0 then
      vprint Invariant, 2: "tested ", attempt, " elements";
    end if;
  until #found ge found_max or
       (#found gt 0 and attempt - found_last gt 2* found_first);

  s := [x[4] : x in found];
  _, m := Minimum(s);
  
  i := found[m][2][1]^found[m][1];
  vprint Invariant, 1: "generated by ", i;
  vprint Invariant, 1: "length: ", #H / #Stabilizer(H, i);
  return i, Stabilizer(H,  i);
end intrinsic;

intrinsic HilbertSeriesApproximation(R::RngInvar, d::RngIntElt) -> .
  {The Hilbert series of R as an power series with rel. precision d}

  G := Group(R);
  K := CoefficientRing(R);

  vprint Invariant, 1: 
    "Computing HilbertSeriesApproximation to precision", d, 
    "for group of size", #G, "and degree", Degree(G), "over", K;  

  Kd := PowerSeriesRing(K, d+1);
  vprint Invariant, 2: " Classes...";
  vtime Invariant, 2: cl := Classes(G);
  vprint Invariant, 2: #cl, "classes in total";

  Rd := PolynomialRing(K);
  d := 0;
  nc := 0;
  vprint Invariant, 2: " Getting cycle structures...";
  ind_cl := {@@};
  dat_cl := [];
  for i in cl do
    c := CycleStructure(i[3]);
    if c in ind_cl then
      dat_cl[Position(ind_cl, c)] +:= i[2];
    else
      Include(~ind_cl, c);
      Append(~dat_cl, i[2]);
    end if;
  end for;
  vprint Invariant, 2: " ..done, left with ", #Set(ind_cl);
  vprint Invariant, 2: " Now summing...";
  for i in ind_cl do
    nc +:= 1;
    if nc mod 100 eq 0 then
      vprint Invariant, 2: nc, " classes done";
    end if;
    cd := i;
    d +:= (dat_cl[Position(ind_cl, i)]/Kd!(&* [ (1-Rd.1^c[1])^c[2] : c in cd]));
  end for;

  vprint Invariant, 1: "... done";
  return d / Order(G);
    
end intrinsic;

intrinsic MolienSeriesApproximation(G::GrpPerm, d::RngIntElt) -> .
  {The Molien series of G as a power series with rel. precision d}

  if (IsSymmetric(G) or IsAlternating(G)) and d le Degree(G) then
    Kd := PowerSeriesRing(Integers(), d+1);
    l:=[NumberOfPartitions(i): i in [0..d]];//This is true up to d le Degree(G)
    fff:= Kd ! l;
    ff:=2*(fff/2);//Creates Laurent series ring over rationals...
    return ff;
  else
    return HilbertSeriesApproximation(InvariantRing(G, Integers()), d);
  end if;
end intrinsic;

import "GalInvar.m" : check;

function gen_bi(f,g,s,x:Cost := false)
  if Type(x) eq SeqEnum then
    if Type(g) eq UserProgram then
      return s(f(x), g(x));
    elif Type(g) eq GrpPermElt then
      return f(PermuteSequence(x, g));
    else
      return s(f(x), g);
    end if;
  elif ISA(Type(x), RngElt) then
    b := f(x);
    if Type(g) eq UserProgram then
      return s(b, g(x));
    elif Type(g) eq RngIntElt then
      return s(b, g);
    elif Type(g) eq GrpPermElt then
      return b;
    else
      error "wrong argument type";
    end if;
  elif x cmpeq "cost" then
    b := f(x);
    if Type(g) eq UserProgram then
      if s cmpeq '+' then
        return b+ g(x);
      elif s cmpeq '*' then
        return b+g(x)+1;
      elif Cost cmpne false then
        return b+g(x)+Cost;
      else
        error "don't know how to compute the cost for ", s;
      end if;
    elif Type(g) eq RngIntElt then
      return g*b;
    elif Type(g) eq GrpPermElt then
      return b;
    else
      error "wrong argument type";
    end if;
  elif x cmpeq "print" then
    r := "(" cat f(x) cat ")" cat Sprintf( "%m ", s);
    r cat:= "(" cat g(x) cat ")";
    return r;
  elif Type(x) cmpeq GrpPermElt then
     if Type(g) eq GrpPermElt then
       return check(x, func<t|f(PermuteSequence(t, g))>, "gen_bi":Sign := false);
     else
       return check(x, func<t|s(f(t), g(t))>, "gen_bi"*Sprintf("%m", s):Sign := false);
     end if; 
  elif x cmpeq "type" then
    return "Generic-CF("*Sprintf("%m", s)*")";
  else
    error "wrong argument";
  end if;
end function;

intrinsic InternalInvOp(f::UserProgram, g::GrpPermElt) -> UserProgram
  {}
  return func<x|gen_bi(f, g, '^', x:Cost := 0)>;
end intrinsic;
intrinsic InternalInvOp(f::UserProgram, g::UserProgram, o::Intrinsic:Cost := false) -> UserProgram
  {}
  return func<x|gen_bi(f, g, o, x:Cost := Cost)>;
end intrinsic;
intrinsic InternalInvOp(f::UserProgram, g::UserProgram, o::UserProgram:Cost := false) -> UserProgram
  {}
  return func<x|gen_bi(f, g, o, x:Cost := Cost)>;
end intrinsic;

function _GalInvBuild(L)

  function nest_func(f,G,x)
    if Type(x) eq SeqEnum then
      return f([g[1]([x[i] : i in [1..#x] | i in g[2]]) : g in G]);
    elif ISA(Type(x), RngElt) then
      return f(Maximum([g[1](x) : g in G]));
    elif x cmpeq "cost" then
      return f(x)+&+[g[1](x) : g in G];
    elif x cmpeq "print" then
      r := f(x) cat  "([";
      for g in G do
        r cat:= g[1](x); 
        if not IsIdentical(g, G[#G]) then
          t cat:=  ", ";
        end if;
      end for;
      r cat:= "])";
      return r;
    elif x cmpeq "type" then
      return "Generic-CF(nest)";
    else
      error "wrong argument";
    end if;
  end function;

  function nest(f, g)
    return func<x|nest_func(f, g, x)>;
  end function;

  function add(f,g)
    return func<x|gen_bi(f, g, '+', x)>;
  end function;
  function mult(f,g)
    return func<x|gen_bi(f, g, '*', x)>;
  end function;
  function pow(f,g)
    return func<x|gen_bi(f, g, '^', x)>;
  end function;

  get, set := NewEnv(["pfs_cnt"]);
  set("pfs_cnt", 0);

  function prim_func_small(f, s, perm)
// SLPolys tested (5, 1) (6, 12) (7, 1)
//"prim_func_small";
    T := Terms(f);
    g := &+[ LeadingCoefficient(t)* &*[ S[i]^Exponents(t)[i] : i in [1 .. n]] : t in T ] where S is perm cmpeq false select s else PermuteSequence(s, perm) where n is Rank(Parent(f));

    if not assigned g`GalInvType then
      g`GalInvType := "Generic-CF(small prim)";
    end if;
    return g;

  end function;

/* Compute the orbit sum monomial i and group H */
  function prim(i, H)
//"prim";
    if Type(i) eq RngSLPolElt then
      return i;
    end if;
    S := Stabilizer(H, i);
    vprint Invariant, 2: "prim:", Exponents(i), #H div #S;

    //if #H div #S lt 10 then
    //if #H div #S lt 5 then
    //if #H div #S lt 5000 then
     if #H div #S lt 100000 then 
      if #H lt 10000 then
        f := &+ Orbit(H, i);
      else
        f := &+ [ i^s : s in RightTransversal(H, S)];
      end if;
      return prim_func_small(f, [S.i : i in [1 .. n]], false) where S is SLPolynomialRing(Integers(), n : Global) where n is Rank(Parent(f));
    end if;
    n := Degree(H);
    lp := [];
    lS := [];
    lT := [];
    S := H;
    ii := i;
    R := Parent(i);
//    while #S / #Stabilizer(S, ii) gt 2000 do
    while #S gt 2000 and ii ne 1 do
//        while #S  gt 20 and ii ne 1 do
      ss := [ <#s, x, s> where s := Stabilizer(S, x) : x in [1..n] 
                                                  | Degree(ii, x) ge 1];
      _, p := Maximum([x[1] : x in ss]);

      Append(~lT, RightTransversal(S, ss[p][3]));
      S := ss[p][3];
      Append(~lS, S);
      p := ss[p][2];
      Append(~lp, p);
      ii := Evaluate(ii, [j eq p select 1 else R.j : j in [1..n]]);
    end while;

    vprint Invariant, 1: "using stabilizer chain with sizes", [ #x : x in lS];
    vprint Invariant, 1: "transversals :", [#x : x in lT];
    vprintf Invariant, 2: "and leftover bits %o, %o\n", ii, #S / #Stabilizer(S, ii);

    f_rest := &+ Orbit(S, ii);
    vprint Invariant, 2: "of cost: ", NumberOfOperations(prim_func_small(f_rest, [S.i : i in [ 1.. n]], false), "*") where S is SLPolynomialRing(Integers(), n : Global) where n is Rank(Parent(f_rest));

    e := Exponents(i);
    e := Eltseq(e);

    function prim_func(s, l, perm)
      if l gt #lp then
        r := prim_func_small(f_rest, s, perm);
        return r;
      end if;
      pp := lp[l];
      g := Universe(s)!0;
      for w in lT[l] do
        pt := pp^w;
        pw := pt^perm;
        p := w*perm;
          lo := s[pw];
          s[pw] := 1;
          r := prim_func(s, l+1, p);
          s[pw] := lo;
          g +:= lo^e[pp] * Parent(g)!r;
      end for;

      if not assigned g`GalInvType then
        g`GalInvType := "Generic-CF(prim)";
      end if;
      return g;
    end function;


      s := [S.i : i in [1 .. Rank(S)]] 
          where S is SLPolynomialRing(Integers(), Degree(H) : Global);
    return prim_func(s, 1, H.0);
  end function;

  n := Degree(L[1][2]);

  function wrap(f)
    get, set := NewEnv(["poly"]);
    set("poly", false);
    function wrapped(x)
      if x cmpeq "poly" then
        h := get("poly");
        if h cmpeq false then
          h := f([R.i : i in [1..n]]) where 
                R := PolynomialRing(Integers(), n);
          set("poly", h);      
        end if;
        return h;
      elif x cmpeq "data" then
        return L;
      else
        return f(x);
      end if;
    end function;
    return wrapped;
  end function;


  if #L eq 1 then
    H := L[1][2];
    I := L[1][1];
    if Type(I) eq UserProgram then
//      "Here (1)";
      return I;
    end if;
//    "Here (2)";
    return prim(I, H);
  else
    // This becomes an &+ on i which should hold SLPolys
    i := prim(L[1][1], L[1][2]);
    for j in [2 .. #L] do
	i +:= Parent(i)!prim(L[j][1], L[j][2]);
    end for;
    //i := [Type(x[1]) eq UserProgram select x[1] else prim(x[1], x[2]) : x in L];
//    "Here (3)";
    return i;
  end if;
end function;

intrinsic InternalGalInvBuild(H::GrpPerm, I::RngMPolElt) -> UserProgram
  {Returns a fnction that corresponds to the orbit sum of I under H.}
  
  return _GalInvBuild([<I, H>]);
end intrinsic;

//intrinsic InternalGalInvBuild(I::[<RngMPolElt, GrpPerm>]) -> UserProgram
intrinsic InternalGalInvBuild(I::SeqEnum[Tup]) -> UserProgram
  {}
  return _GalInvBuild(I);
end intrinsic;

intrinsic InternalGalInvBuild(I::List) -> UserProgram
  {Returns a fnction that corresponds to the invar paramterized by I}
  return _GalInvBuild(I);
end intrinsic;
 
intrinsic Stabilizer(G::GrpPerm, d::RngMPolElt) -> GrpPerm
  {Computes the stabilzer of the monomial d}
  require #Terms(d) eq 1:
    "This function only works for monomials";
  e := Exponents(Terms(d)[1]);
  S := G;
  n := Degree(G);
  for i in [1..Maximum(e)] do
    sup := { j : j in [1..n] | e[j] eq i};
    if #sup eq Degree(G) then
      s := G;
    elif #sup eq 0 then
      s := G;
    elif IsSymmetric(G) then
      gens := Generators(DirectProduct(Sym(#sup), Sym(Degree(G)-#sup)));
      gens := [ Eltseq(x) : x in gens];
      Gens := gens;
      order := [ x : x in sup] cat [ x : x in {1..n} diff sup];
      for j in [1..#gens] do
        for k in [1..#gens[j]] do
          Gens[j][k] := order[gens[j][k]];
        end for;
      end for;
      pi := G!order;
      Gens := [ PermuteSequence(x, pi^-1) : x in Gens];
      s := sub<G|Gens>;
      //assert s eq Stabilizer(G, sup);
    else
      s := Stabilizer(G, sup);
    end if;
    S := S meet s;
  end for;
  return S;
end intrinsic;

intrinsic StabilizerLadder(G::GrpPerm, d::RngMPolElt) -> GrpPerm
  {Computes the stabilzer of the monomial d as a ladder}
  require #Terms(d) eq 1:
    "This function only works for monomials";
  e := Exponents(Terms(d)[1]);
  S := G;
  n := Degree(G);
  L := [G];
  E := SequenceToMultiset(e);
  m := Multiplicities(E);
  m := Maximum(m);
  s := Set(e);
  for i in s do
    if Multiplicity(E, i) eq m then
      m +:= 1;
      continue;
    end if;
    ss := {x : x in [1..n] | e[x] eq i};
    j := 1;
    done := {};
    curr := {};
    start := L[#L];
    last := start;
    while #ss gt 0 do
      r := Representative(ss);
      Exclude(~ss, r);
      G := Stabilizer(G, r);
      Include(~curr, r);
      if G ne L[#L] then
        Append(~L, G);
      end if;
      if #curr gt 1 then
        G := Stabilizer(last, curr);
        if G ne L[#L] then
          Append(~L, G);
        end if;
        done join:= curr;
        curr := {};
        G := Stabilizer(start, done);
        if G ne L[#L] then
          Append(~L, G);
        end if;
        last := G;
      end if;
    end while;
    if #curr gt 0 then
      G := Stabilizer(last, curr);
      if G ne L[#L] then
        Append(~L, G);
      end if;
      done join:= curr;
      curr := {};
      G := Stabilizer(start, done);
      if G ne L[#L] then
        Append(~L, G);
      end if;
    end if;
  end for;
  assert Stabilizer(L[1], d) eq L[#L];
  return L;
end intrinsic;

/*
//JK: new function
function FindOvergroup(G,H)
//If H is not maximal in G, this function checks, if there exists a subgroup
//SS of G, such that 
//1) H is maximal subgroup of SS
//2) If H<U<G is any group ne H, then SS \leq U 
//These properties imply, that an H-invariant, SS-relative polynomial is
//automatically G relative
  if IsMaximal(G,H) then return true, G;end if;
  f:=CosetAction(G,H);
  U:=f(G);
  P:=MinimalPartitions(U);
  if #P gt 1 then return false,G;end if;
  m:=#Random(P[1]);
  P:=AllPartitions(U);
  P:=[x:x in P |#x eq m];
  block:=P[1];
  S:=Stabilizer(U, block);
  SS:=S @@ f;
  return true, SS;
end function; */

function _NewGalSubgroup(U, Galois: Invar := false, Risk := false) 

  G, r, S := Explode(Galois);
  if #G eq #U then
    if assigned S`f then
	return Polynomial(CoefficientRing(S`f), [1,1]);
    else
	return Polynomial([1, 1]);
    end if;
  end if;
  Char2 := Characteristic(S`Ring) eq 2;

  if Invar cmpeq false then
   i := RelativeInvariant(invar_coeff_ring(S), G, U);
  else 
   i := Invar;
  end if; 

/* This is now part of RelativeInvariant  
  if IsTransitive(G) then
      better, UU:=FindOvergroup(G,U);//JK
  else 
    better := false;
  end if;

  if Invar cmpeq false then
    if better then
       i:=GaloisGroupInvariant(invar_coeff_ring(S), UU,U);//JK
    else
      i := RelativeInvariant(invar_coeff_ring(S), G, U : IsMaximal := false, Risk := Risk);
    end if;
  else 
    i := Invar;
  end if; */
  if not assigned i`GalInvType then
    i`GalInvType := "Other";
  end if;

  eval_i := Evaluate(i, [SS.j : j in [1 .. Rank(Parent(i))]]) where SS := SLPolynomialRing(Integers(), Rank(Parent(i)) : Global);
  if not assigned eval_i`GalInvType then
    eval_i`GalInvType := "Other";
  end if;


  is_c := CoefficientRing(Parent(eval_i)) cmpeq Integers();

  vprint Invariant, 1: "Using invar of cost ", NumberOfOperations(i, "*");
 
  B := S`max_comp;

  Zx := get_all_tschirni_universe(S);
  all_tschirn := {};
  tschirn := Zx.1;
  T := RightTransversal(G, U);
  c := 2*#T;
  n := Degree(U);
  r := [GaloisRoot(i, S:Bound := c) : i in [1..n]];
  tdeg := n - 1;


//JK: I use 5 chosen tschirnhausen transformation, after that
//I increase the degree depending on the number of attempts
  repeat

    rr := apply_tschirni(S, tschirn, r);
    if not is_c then
       assert assigned S`BaseMap;
if not IsExport() then
"\n\n\nne Evaluating using base map 1";
end if;
        s := {Evaluate(eval_i, PermuteSequence(rr, p), 
                      map<CoefficientRing(Parent(eval_i)) -> Universe(r) | y :-> S`BaseMap(y, PrecisionFromBound(c, S))>) : p in T};
    else
	s := {Evaluate(eval_i, PermuteSequence(rr, p)) : p in T};
    end if;
//    s := {Evaluate(eval_i, PermuteSequence(rr, p)) : p in T};
    s := {ChangePrecision(a,Precision(Representative(r))) : a in s};
    if #s ne #T then
      vprint Invariant, 1: "new tschirni...", #all_tschirn;
      repeat
        if #all_tschirn eq 0 then //JK: Choose nicer tschirnis first
          tschirn:=Zx.1+1;
        elif #all_tschirn eq 1 and Characteristic(Zx) notin {2, 3} then
          tschirn:=Zx.1+3;
        elif #all_tschirn eq 2 and not Char2 then
          tschirn:=Zx.1^2+2;
        elif #all_tschirn eq 3 and not Char2 then
          tschirn:=Zx.1^2+2*Zx.1+2;
        elif #all_tschirn eq 4 and not Char2 then
          tschirn:=Zx.1^4 + 3*Zx.1^2 + 2*Zx.1 + 1;
        else
          if Char2 then 
            tdeg:=Minimum(n-1, #all_tschirn-3) + #all_tschirn div 20;
          else
            tdeg := Minimum(n-1, #all_tschirn);
          end if;
	  if tdeg le 0 then
	    tdeg := n;
	  end if;
	  tschirn := get_tschirni(S, 4, tdeg, all_tschirn, i`GalInvType);
          //tschirn := Polynomial([Random(4) : x in [1..Random(tdeg)]] cat [1]);//JK:Degree increasing
        end if;
      until tschirn notin all_tschirn;
      Include(~all_tschirn, tschirn);
      if not IsExport() then 
	  if #all_tschirn gt 50 then
      #all_tschirn;
	    error "too many transforms";
	  end if;
      end if;
    else
      break;
    end if;
  until false;
  vprint Invariant, 1: "use tschirni ", tschirn;



  Epsilon := false;
  if S`Type in {"F_q(t)", "Q(t)"} then
    i2 := i^#T; i2`GalInvType := "other";
    B := S`Bound(tschirn, i2,1);
//B +:= Degree(tschirn)*S`max_comp*#T*TotalDegreeAbstract(i);
//B;
  else
      B := Evaluate(tschirn, B);
      B := Bound(eval_i, B);
      B := Maximum([Binomial(#T, i)*B^i : i in [0..#T]]);
      if S`Type eq "Complex" then
         Epsilon := 10^-10;
         B := B * 10^25 * (NumberOfOperations(eval_i,"+") + 1);
      end if;
  end if;
  vprint Invariant, 1: "Final lifting started..., bound is of size", 
                                                   Ilog2(B), "bits";
  r := [GaloisRoot(i, S: Bound := B) : i in [1..n]];
  vprint Invariant, 2: "Done. Applying tschirni..";
  r := apply_tschirni(S, tschirn, r);

  if not is_c then
       assert assigned S`BaseMap;
if not IsExport() then
"\n\n\nne Evaluating using base map 1";
end if;
        s := {Evaluate(eval_i, PermuteSequence(r, p), 
                      map<CoefficientRing(Parent(eval_i)) -> Universe(r) | y :-> S`BaseMap(y, PrecisionFromBound(c, S))>) : p in T};
    else
	s := {Evaluate(eval_i, PermuteSequence(r, p)) : p in T};
    end if;
//  s := {Evaluate(eval_i, PermuteSequence(r, p)) : p in T};

  vprint Invariant, 2: "Done. Computing  polynomial.";
  f := &* [ Polynomial([x, 1]) : x in s];
  f := Eltseq(f);
  ff := [];
  for x in f do
    fl, y := IsInt(x, B, S: Epsilon := Epsilon);
/*    if false and not fl then
      r := [GaloisRoot(i, S: Prec := <2*Precision(x)[1], 2*Precision(x)[2]>) : i in [1..n]];
      vprint Invariant, 2: "Done. Applying tschirni..";
      r := [ Evaluate(tschirn, x) : x in r];
      s := {Evaluate(eval_i, PermuteSequence(r, p)) : p in T};
      vprint Invariant, 2: "Done. Computing  polynomial.";
      f := &* [ Polynomial([x, 1]) : x in s];
      fl, y := IsInt(Eltseq(f)[#ff + 1], B, S);
    end if; */
    assert fl;
    Append(~ff, y);
  end for;
  return Polynomial(ff), i;
end function;

intrinsic GaloisSubgroup(K::FldNum, U::GrpPerm: Galois := false, Invar := false, Risk := false) -> FldNum, UserProgram
  {Computes the fixed field under U, the defining polynomial and the invariant are returned}
  if Galois cmpeq false then
    G, r, S := GaloisGroup(K);
    Galois := [*G, r, S*];
  end if;

  return _NewGalSubgroup(U, Galois: Invar := Invar, Risk := Risk);
end intrinsic;

intrinsic GaloisSubgroup(S::GaloisData, U::GrpPerm: Invar := false, Risk := false) -> FldNum, UserProgram
  {Computes the fixed field under U, the defining polynomial and the invariant are returned}

  Galois := [*S`DescentChain[#S`DescentChain][1], 
              S`Roots,
             S*];   

  return _NewGalSubgroup(U, Galois: Invar := Invar, Risk := Risk);
end intrinsic;

intrinsic GaloisSubgroup(f::RngUPolElt, U::GrpPerm: Galois := false, Invar := false, Risk := false) -> FldNum, UserProgram
  {Computes the fixed field under U, the defining polynomial and the invariant are returned}

  if Galois cmpeq false then
    G, r, S := GaloisGroup(f);
    Galois := [*G, r, S*];
  end if;

  return _NewGalSubgroup(U, Galois: Invar := Invar, Risk := Risk);
end intrinsic;


function _NewGalQuot(Q, Galois :Risk := false) 

  G, r, S := Explode(Galois);
  
  s:=Subgroups(G:OrderEqual:=(#G div Degree(Q)));
  s:=[x`subgroup: x in s];
  if Degree(Q) le 31 then //JK: changed 20 to 31
    num:=TransitiveGroupIdentification(Q);
    s:=[x:x in s| TransitiveGroupIdentification(CosetImage(G,x)) eq num];
  else
    s:=[x:x in s| IsIsomorphic(CosetImage(G,x), Q)];
  end if;
  result:=[];
  for H in s do
    Append(~result, _NewGalSubgroup(H, [*G, r, S*]: Risk := Risk));
  end for;
  return result;
end function;

intrinsic GaloisQuotient(K::FldNum, Q::GrpPerm: Galois := false, Risk := false) -> SeqEnum
{Q is a quotient of G=Gal(K). This fnction computes all non isomorphic 
subfields of the splitting field of f such that the Galois groups are
 permutation isomorphic to U.}

  if Galois cmpeq false then
    G, r, S := GaloisGroup(K);
    Galois := [*G, r, S*];
  end if;

  return _NewGalQuot(Q, Galois: Risk := Risk);
end intrinsic;

intrinsic GaloisQuotient(f::RngUPolElt, Q::GrpPerm: Galois := false, Risk := false) -> SeqEnum
{Q is a quotient of G=Gal(f). This fnction computes all non isomorphic 
subfields of the splitting field of f such that the Galois groups are
 permutation isomorphic to U.}

  if Galois cmpeq false then
    G, r, S := GaloisGroup(f);
    Galois := [*G, r, S*];
  end if;
  return _NewGalQuot(Q, Galois:Risk := Risk);
end intrinsic;

intrinsic GaloisQuotient(S::GaloisData, Q::GrpPerm: Risk := false) -> FldNum, UserProgram
{Q is a quotient of G=Gal(f). This fnction computes all non isomorphic 
subfields of the splitting field of f such that the Galois groups are
 permutation isomorphic to U.}

  Galois := [*S`DescentChain[#S`DescentChain][1], 
              S`Roots,
             S*];   

  return _NewGalQuot(Q, Galois: Risk := Risk);
end intrinsic;
