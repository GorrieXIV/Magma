freeze;

Debug := false;

intrinsic InternalInduceMap(K::FldNum, H::UserProgram, p::RngOrdIdl, mA::UserProgram: Sub := false, Level := false) -> Map
  {}

  G, _, mG := AutomorphismGroup(K);
  if Sub cmpne false then
    U := Sub;
    assert U subset G;
  else
    U := G;
  end if;

  if Level cmpeq false then
    try
      x := H(<U.0, U.0>);
      i := 2;
    catch e
      try 
        x := H(<U.0>);
        i := 1;
      catch f
        try
          x := H(<>);
          i := 0;
        catch g
          require false: "2nd argument has to be a cycyle!";
        end try;
      end try;
    end try;
  else
    i := Level;
  end if;

  // everything is absolute here!!!!
  // Kp, mKp := Completion(K, p);
  U := sub<G|[ s : s in U | ideal<Order(p)|(s@mG)(Generators(p))> eq p]>;
  //U should (might) be the correct group here. At least the following should
  //hold:
  //given x in Kp (ie. x+p^n), we can compute a preimage in K, apply an
  //element of U (which will leave p^n invariant) and map back to Kp.

  return func<x|mA(H(x))>;
end intrinsic;

intrinsic CohomologyModule(G::GrpPerm, A::GrpAb, m::.) -> ModCoho
  {For G acting on A through m, create the Cohomology module. m has to be either a map:G->End(A) through which G acts, or a sequence of maps in End(A), one
    for each generator of G}
  // G acts through m on A, somehow.

  i := AbelianInvariants(A);
  if Type(m) eq SeqEnum then
    m := [ Matrix([Eltseq(A.i@j) : i in [1..Ngens(A)]]) : j in m];
  elif Type(m) eq Map  or Type(m) eq UserProgram then
    m := [ Matrix([Eltseq(A.i@m(G.j)) : i in [1..Ngens(A)]]) : j in [1..Ngens(G)]];
  else
    error "argument not supported";
  end if;
  return CohomologyModule(G, i, m);
end intrinsic;

_ClassGroup := ClassGroup;

CreateHom := function(G, GG, mp)
  // h := hom<G -> GG | mp>;  // does not work ...
  // mp is a list of pairs. We want to constuct the map
  // that sends mp[i][1] -> mp[i][2].

  m1 := Matrix(Integers(), [Eltseq(x[1]) : x in mp]);
  m1 := VerticalJoin(m1, DiagonalMatrix([ Order(G.x) : x in [1..Ngens(G)]]));
  _, t := EchelonForm(m1);
  m1 := Matrix(Integers(), [Eltseq(x[2]) : x in mp]);
  t := Matrix(Integers(), [ Eltseq(t[i])[1..#mp] : i in [1..Nrows(t)]]);
  m1 := t*m1;
  mp := [ GG!Eltseq(m1[i]) : i in [1..Ngens(G)]];
  h := hom<G -> GG | mp>;
  return h;
end function;


intrinsic SUnitCohomologyProcess(S::{RngOrdIdl}, U::GrpPerm : ClassGroup := false, Ramification := false) -> SetEnum
  {Creates a cohomology process for the multiplicative group of the number field K. U has to be a subgroup of the automorphism group of K}
   
  M := Ring(Universe(S));
  vprint Cohomology, 1 : "Creating cohomology process for", NumberField(M);  
  vprint Cohomology, 1 : "User supplied", #S, "primes";
  vprint Cohomology, 2 : "Which are", S;

  if Ramification then
    vprint Cohomology, 2: "Adding ramified (finite) primes";
    S join:= Support(Discriminant(M)*M);
  end if;
  if ClassGroup then
    vprint Cohomology, 2: "Adding generators for the class group";
    C, mC := _ClassGroup(M: Proof := "Current");
    if false then // problem: we need the primes magma uses, not
                  // just any nice small ones: the output of 
                  // ClassRepresentative has to be supported at S
      vprint Cohomology, 2: "Choosing small primes to generate the class group";
      p := 1;
      s := sub<C|[x@@ mC : x in S]>;
      while s ne C do
        p := NextPrime(p);
        lp := Decomposition(M, p);
        for i in lp do
          c := i[1] @@ mC;
          if not c in s then
            s := sub<C|s, c>;
            Include(~S, i[1]);
            if s eq C then
              break;
            end if;
          end if;
        end for;
      end while;
    else
      vprint Cohomology, 2: "Decomposing generators of the class group";
      for i in [1..Ngens(C)] do
        S join:= Support(C.i@mC);
      end for;
    end if;
  end if;

  AddAttribute(SetEnum, "S");
  AddAttribute(SetEnum, "Type");
  AddAttribute(SetEnum, "Units");
  AddAttribute(SetEnum, "Coho");
  AddAttribute(SetEnum, "Data");

  C := {1};
  G, _, mG := AutomorphismGroup(NumberField(M));
  vprint Cohomology, 1: "S for Sunit before Galois action of size", #S;
  S := &join { {ideal<Order(x)|(g @ mG)(Generators(x))> : x in S} : g in G};
  vprint Cohomology, 1: "S for Sunit of size", #S;
  S := [PowerIdeal(M)| x : x in S];
  C`S := S;
  SU, mSU, base := SUnitGroup(S:Raw);
  ac := SUnitAction(mSU, [U.i@mG : i in [1..Ngens(U)]], S:Base := base);
  co := CohomologyModule(U, SU, ac);

  C`Type := "S-Unit Cohomology module";
  C`Units := <mSU, base, ac>;
  C`Coho := co;

  return C;
end intrinsic;
  
intrinsic SimpleCohomologyProcess(X::{}, U::GrpPerm : ClassGroup := false, Ramification := false, S := false) -> SetEnum
  {Creates a cohomology process for the multiplicative group of the number field K. U has to be a subgroup of the automorphism group of K}
   
  M := Ring(Universe(S));
  vprint Cohomology, 1 : "Creating simple cohomology process for", NumberField(M);  
  vprint Cohomology, 1 : "User supplied", #X, "elements";
  vprint Cohomology, 2 : "Which are", X;

  AddAttribute(SetEnum, "S");
  AddAttribute(SetEnum, "Type");
  AddAttribute(SetEnum, "Units");
  AddAttribute(SetEnum, "Coho");
  AddAttribute(SetEnum, "Data");

  C := {1};
  G, _, mG := AutomorphismGroup(NumberField(M));
  vprint Cohomology, 1: "size S before Galois action of size", #X;
  X := OrbitClosure(U, func<x|func<y|y@(x@mG)>>, X);
  vprint Cohomology, 1: "after Galois action:", #X;

  SU, mSU := MultiplicativeGroup(SetToSequence(X));
  vprint Cohomology, 1: "mult. group generated here", SU;

  vprint Cohomology, 2: "computing homs...";
  h := [];
  for g in GeneratorsSequence(U) do
    vprint Cohomology, 2: " image for ", g;
    vtime Cohomology, 2: ims := [<x@@mSU, (x@(g@mG))@@mSU> : x in X];
    vtime Cohomology, 2: Append(~h, CreateHom(SU, SU, ims));
  end for;  
  
  co := CohomologyModule(U, SU, h);

  C`Type := "Simple Cohomology module";
  C`Units := <mSU, ClassGroup, Ramification, S>;
  C`Coho := co;

  return C;
end intrinsic;

intrinsic IsCoprime(a::RngIntElt, b::RngIntElt) -> BoolElt
{True iff a and b are corpime}
  return Gcd(a,b) eq 1;
end intrinsic;

/*
intrinsic CyclotomicUnits(K::FldCyc:AllLevels := false, RealUnits := false) -> []
{The cyclotomic units in K}
*/ 
function CyclotomicUnits(K : AllLevels := false, RealUnits := false)
  c := Conductor(K);
  w := RootOfUnity(c, K);
  if RealUnits then
    function unit_at_level(m)
      z := w^(c div m);
      get_expo := function(i)
        if IsOdd(i) then
          return (i-1) div 2;
        else
          assert IsOdd(m);
          return (i+m-1) div 2;
        end if;
      end function;  
      return [z^-get_expo(i)*(z^i-1)/(z-1) : i in [2..m div 2]| IsCoprime(i, m)];
    end function;
  else
    function unit_at_level(m)
      z := w^(c div m);
      return [(z^i-1)/(z-1) : i in [2..m div 2]| IsCoprime(i, m)];
    end function;
  end if;
  if AllLevels then
    return &cat [unit_at_level(d) : d in Divisors(c) | (IsOdd(d) or d mod 4 eq 0) and d ne 1];
  else
    return unit_at_level(c);
  end if;
end function;

function EmbedCyclotomicField(K:DoError, DegreeLimit := 1)
  M := Discriminant(MaximalOrder(K));
  A := MaximalAbelianSubfield(K:Conductor := M);
  if AbsoluteDegree(A) ne Degree(K) then
    if DoError then
      error "Field is not abelian";
    else
      return false, _;
    end if;
  end if;
  if EulerPhi(Minimum(Conductor(A))) gt DegreeLimit * Degree(K) then
    if DoError then
      error "Field is not Cyclotomic";
    else
      return false, _;
    end if;
  end if;
  C := CyclotomicField(Minimum(Conductor(A)));
  G, mG := CyclotomicAutomorphismGroup(C);
  lp := Factorisation(Degree(K));
  b := [];
  c := [];
  for p in lp do
    kp := Subfields(K, p[1]^p[2]);
    assert #kp eq 1;
    cp := Subgroups(G :Quot := AbelianInvariants(AutomorphismGroup(kp[1][1])));
    cp := [FixedField(C, x`subgroup) : x in cp];
    for ccp in cp do
      f, ip := IsIsomorphic(ccp, kp[1][1]);
      if f then
        Append(~b, [K!ip(x) : x in Basis(ccp)]);
        Append(~c, [C!x : x in Basis(ccp)]);
        break;
      end if;
    end for;
    assert f;
  end for;
  b := CartesianProduct(b);
  b := [&* x : x in b];
  m := Matrix([Eltseq(x) : x in b]);
  f, s := IsConsistent(m, Matrix([Eltseq(K.1)]));
  assert f;
  assert Nrows(s) eq 1;
  c := CartesianProduct(c);
  c := [&* x : x in c];
  z := &+ [ s[1][i]*c[i] : i in [1..#b]];
  Embed(K, C, z);
  return C, Coercion(K, C);
end function;


intrinsic IsCyclotomic(K::FldAlg[FldRat]) -> BoolElt, FldCyc, Map
{Tests if K is cyclotomic and if so, return the field}
  C := EmbedCyclotomicField(K:DoError := false, DegreeLimit := 1);
  if C cmpeq false then
    return false, _, _;
  end if;
  Embed(C, K, K!C.1);
  return true, C, Coercion(K, C);
end intrinsic;

intrinsic EmbedIntoMinimalCyclotomicField(K::FldAlg[FldRat]) -> FldCyc, Map
{Returns the smallest cyclotomic field containing K and the embedding map}
  C := EmbedCyclotomicField(K:DegreeLimit := Infinity(), DoError);
  return C, Coercion(K, C);
end intrinsic;


intrinsic SUnitSubGroup(S::[RngOrdIdl]) -> GrpAb, Map
  {}
  M := Order(Rep(S));
  K := NumberField(M);
  require IsNormal(K) : "Field need to be normal";
  f, c := HasComplexConjugate(K);
  require f : "Field needs to be CM";
  A, _, mA := AutomorphismGroup(K);
  g := GeneratorsSequence(K);
  if not exists(c){x : x in A | forall{y : y in g|c(y) eq (x@mA)(y)}} then
    require false: "Field needs to be CM";
  end if;
  require IsNormal(A, sub<A|c>) : "Field needs to be CM";

  "finding real subfield";
  R := FixedField(K, sub<A|c>);
  assert Signature(R) eq Degree(R);

  //Strategy: for each place in S we find the decomposition field and
  //compute the S-Units there. We expect:
  // - the DecompositionFields to be smaller than the original field
  // - the S-Units of those fields to generate a subgroup of finite
  //   index
  // - For the infinite places, the totally real subfield should do  
  // Then we use MultiplicativeGroup to paste the units together...
  // We'll also check if we can re-use fields.

  fields := [*R*];
  grps := [sub<A|c>];
  places := [*[]*];
  for P in S do
    "doing", P;
    D := DecompositionGroup(P);
    "#group", #D;
    if exists(U){U : U in grps | U eq D} then
      "Already know a suitable field!";
      F := fields[Position(grps, U)];
      lp := Decomposition(MaximalOrder(F), Minimum(P));
      if not exists(PP) { PP : PP in lp | M!!PP[1] subset P} then
        error "";
      end if;
      Append(~places[Position(grps, U)], PP[1]);
    else
      "New";
      F := FixedField(K, D);
      Append(~fields, F);
      lp := Decomposition(MaximalOrder(F), Minimum(P));
      if not exists(PP) { PP : PP in lp | M!!PP[1] subset P} then
        error "";
      end if;
      Append(~places, [PP[1]]);
      Append(~grps, D);
    end if;
  end for;

  "OK need some S-Units....", places, fields;

  gens := [];
  for i in [1..#fields] do
    if #places[i] eq 0 then
      if Degree(fields[i]) gt 20 then
        "trying to find cyclotomic field";
        C := EmbedCyclotomicField(fields[i]:DegreeLimit := 5, DoError := false);
        if C cmpeq false then
          "bad luck";
          U, mU := IndependentUnits(MaximalOrder(fields[i]));
          ngens := [U.i @ mU : i in [1..Ngens(U)]];
        else
          "using cyclotomic units in", C;
          ngens := CyclotomicUnits(C:AllLevels);
          n := FixedGroup(C, C!fields[i].1);
          ngens := [&* [(x@mG)(y) : x in n] : y in ngens] where _, _, mG := AutomorphismGroup(C);
        end if;
      else  
        U, mU := IndependentUnits(MaximalOrder(fields[i]));
        ngens := [U.i @ mU : i in [1..Ngens(U)]];
      end if;  
    elif Type(fields[i]) eq FldRat then
      ngens := [Generator(x) : x in places[i]];
    else
      "Sunits", places[i];
      U, mU := SUnitGroup(places[i]);
      ngens := [U.i @ mU : i in [1..Ngens(U)]];
    end if;
    gens cat:= ChangeUniverse(ngens, M);
  end for;

  delete fields;
  delete places;
  delete grps;

  return MultiplicativeGroup(ChangeUniverse(gens, FieldOfFractions(M)));
end intrinsic;

intrinsic SemiSimpleCohomologyProcess(~C::SetEnum)
  {"Refines" the cohomology process to use S-Units from subfields}
  require C`Type eq "Simple Cohomology module":
    "C must be a SimpleCohomologyProcess";

  C`Type := "Semi-Simple Cohomology module";  
end intrinsic;

intrinsic IsGloballySplit(C::SetEnum, H::UserProgram: Sub := false) -> BoolElt, UserProgram 
  {For a 2-cocyle H with values in the number field K (used to create the SUnitCohomologyProcess C), decide if H is globally split, and, if so, return a 1-cochain in the preimage of the boundary operator}

  require assigned C`Type and C`Type in {
    "S-Unit Cohomology module", "Simple Cohomology module",
    "Semi-Simple Cohomology process"}:
    "The 1st argument has to be created using SUnitCohomologyProcess";

  vprint Cohomology, 1: "IsGloballySplit of", H;

  // Let H be a 2-cocycle with values in the number field K.
  // C should be a cohomology process for K...
  // This function essentially reads H as a 2-cocyle with values in some
  // S-unit group for some set S and tries to find a 1-cochain C with values
  // in the same S-unit group that gets mapped to H. 
  // For this to succeed, the set S must be large enough to 
  // - contain the values of H
  // - generate the class group of K
  // Proof:
  // Let h be the derived 2-cocyle with values in ideals of K, ie.
  // h(s,t) := H(s,t)*Z_K
  // then: if H is split (ie. H(s,t) = s HH(t) - HH(s) - HH(st))
  // then h is split as well. Now, cohomology with values in ideals
  // can always be analyzed locally, H^i(G, I_K) = sum H^i(G, (I_K)_p)))
  // where (I_K)_p := <P_1, ..., P_l> with pZ_K = prod P_i^v_i
  // Thus: h(s,t) = d hh where hh is a 1-cochain with values in I_K
  // and, by the above reasoning, hh is supported by the "same" ideals as h.
  // Next, the splitting tilde hh for h that is induced by the splitting for
  // H has to be cohomologue to hh, that is tilde hh and hh differ
  // by the image of a 0-co-chain, (hh  tilde hh^-1)(t) = a^(1-t) for some
  // ideal a. Now, a can be written as alpha b for alpha in K and b a fixed
  // representative for a in the ideal class group of K.
  // HH(s) alpha^1-s should now be a 1-cochain that splits H and is
  // supported where I claim it is:
  // - Splitting: s -> alpha^1-s is a image under d of a 0-cochain, thus 
  //   a 1-coboundary and thus mapped to 1 under the second application 
  //   of d. => d (HH(s) alpha^1-s) = d HH = H
  // - Support: HH(s) alpha^(1-s) -> tilde hh(s) alpha^(1-s)
  //                 = hh(s)
  //   and the support for hh is as claimed.               
  // 
  //
  // Alternatively:
  // Let S be as above (ie. galois closed, all inf. primes, generating the
  // class group). Then we have an exact sequence
  // 1 -> U_S -> K^* -> K^*/U_S -> 1
  // And, K^*/U_S = sum_{p notin S} e_p
  // where e_p has valuation 1 at p, and is supported at S and p ONLY.
  // Since Galois acts transitively on the ideals over a fixed prime,
  // K^*/U_S is an induced module => cohomologycally trivial.
  // (probably only for totally split primes)
  // Wrong:
  // H^2(K^*) is infinite, in fact
  // 0 -> H^2(K) -> sum H^2(K_p) = sum Z/efZ -> Q/Z
  // (the last arrow is summation)
  // The image of H^2(K) in the sum is exactly the kernel, thus it
  // is quite large...
  // At most s.th. along the lines of H^2(U_S) -> sum_{p in S} H^2(K_p)
  // is true...

  G := Group(C`Coho);
  if Sub cmpeq false then
    U := G;
  else
    U := Sub;
    assert U subset G;
  end if;

  d := car<U, U>;
  d := [x : x in d];
  h := [H(x) : x in d];
  if forall{x :x in h | IsOne(x)} then
    vprint Cohomology, 1: "easy: cocycle was identity";
    return true, func<x|h[1]>;
  end if;

  if C`Type eq "Simple Cohomology module" then
    mSU := C`Units[1];
    la := func<x|Eltseq(H(x)@@mSU)>;
    _ := CohomologyGroup(C`Coho, 2);
    c := IdentifyTwoCocycle(C`Coho, la);
    if IsZero(c) then
      vprint Cohomology, 1: "cocycle is trival (no classgroup)";
      vprint Cohomology, 1: "looking for co-boundary now...";
      fl, x := IsTwoCoboundary(C`Coho, la);
      //TODO: find "Nice" pre-image, ie. improve x
      assert fl;
      return true, func<y|mSU(Eltseq(x(y)))>;
    else
      S := C`Units[4];
      vprint Cohomology, 1: "Simple cohomology not conclusive, trying serious ones";
      _ := ClassGroup(Ring(Universe(S)):Bound := 25*Degree(Ring(Universe(S))));
      CC := SUnitCohomologyProcess(S, U:Ramification := C`Units[2],
        ClassGroup := C`Units[3]);
      for i in GetAttributes(Type(C)) do
        if assigned C``i then
          delete C``i;
        end if;
        if assigned CC``i then
          C``i := CC``i;
          delete CC``i;
        end if;
      end for;
      delete CC;
    end if;
  end if;

  //OK: now that we have to work, let's try to reduce the support of the
  //cocycle.
  M := MaximalOrder(CoefficientRing(C`Units[2]));
  _, _, mG := AutomorphismGroup(NumberField(M));
  vprint Cohomology, 1: "computing the support (coprime only) of the cocycle";
  vtime Cohomology, 1: 
              S := Support([x*M : x in h] cat C`S :GaloisStable, CoprimeOnly);
  vprint Cohomology, 1: "C`S of size ", #C`S;
  // TODO: C`S needs to have the support for ClassRep!!!!
  // (it will be self-fixing later on)
 
  fact := func<X|1>;
  Extra := [PowerIdeal(M)|];
  if Debug then
    ss_start := Support([H(x) : x in car<U, U>]) diff Set(C`S);
    "total support at beginning", #ss_start;
  end if;
  while exists(I){I : I in S | not I in C`S} do
    if I eq 1*M then
      Exclude(~S, I);
      continue;
    end if;
    vprint Cohomology, 2: "Trying to reduce the support at", I;
    f, ch, orb := IsSplitAsIdealAt(I, H: Sub := U);
    if not f then 
      // can happen...: implies (I think) that I can split further,
      // Example U:(1,2), I=2*M = P1 * P2
      // H (as ideal) decomposed: 0,0,0,1 (ie. H((1,2),(1,2)) = I)
      // The H^2(U, <I>) = C_2 and H is a generator.
      // However, H^2(U, <P1, P2>) = 0
      for i in orb do
        Append(~Extra, i);
        assert i in S;
        Exclude(~S, i);
      end for;
      vprint Cohomology, 2: "Bad ideal - can't remove it from the support";
      if Debug then
        "Size of S now", #S, #Support(SetToSequence(S)), "o was", #orb;
        ss_start diff:= Support(orb);
      end if;
      continue;
    end if;
    vprint Cohomology, 2: "Ideal can be removed from support";
    vprint Cohomology, 2: "Find the ClassRepresentative for it...";
    vtime Cohomology, 2: a, alpha := ClassRepresentative(I);
    if Debug then
      "a:", { Minimum(x) : x in Support(a)}, 
           &join [ {x[1] : x in Factorisation(Minimum(s))} : s in Support(a)];
      "alpha:", { Minimum(x) : x in Support(alpha*M)}, 
           &join [ {x[1] : x in Factorisation(Minimum(s))} :
                                                       s in Support(alpha*M)];
      "I:", { Minimum(x) : x in Support(I)}, 
           &join [ {x[1] : x in Factorisation(Minimum(s))} : s in Support(I)];

      assert Support([alpha*M]) eq Support(I) join Set(C`S); 
      // C`S generates
      // the class group - but this does NOT mean the Support(a) is in C`S.
      assert a*alpha eq I;
    end if;
    Extra := SetToSequence(Set(Extra) join Support(a) diff Set(C`S));
    S diff:= SequenceToSet(orb);
    if Debug then
      "Size of S now", #S, #Support(SetToSequence(S)), "orb was", #orb;
    end if;
    alpha_orb := [];
    for i in [1..#orb] do
      if exists(u)
           {u : u in U | orb[i] eq ideal<Order(I)|mG(u)(Generators(I))>} then
        Append(~alpha_orb, mG(u)(alpha));
      else
        error "Aut missing";
      end if;
    end for;
    ChangeUniverse(~alpha_orb, FieldOfFractions(Parent(alpha)));
    alpha_arr := [PowerProduct(alpha_orb, Eltseq(ch(<x>))) : x in U];
    alpha := func<x|alpha_arr[Position([u : u in U], x[1])]>;
    // now alpha should be a 1-cochain such that H*delta alpha^-1
    // is supported only at the smaller set...
    d_alpha := func<X|alpha(<X[2]>)*mG(X[2])
                                       (alpha(<X[1]>))/alpha(<X[1]*X[2]>)>;
    fact := func<X|fact(X)*alpha(X)>; //maybe use arrays?
    if Debug then H_old := H; end if;
    H := func<X|H(X)/d_alpha(X)>;
    if Debug then
      ss := Support([H(x) : x in car<U, U>]) 
                       diff (Set(C`S) join Support(Extra));
      "total support now", #ss;
      assert ss_start diff Support(orb) eq ss;
      ss_start := ss;
    end if;
  end while;
  if Debug then
    assert Support([H(x) : x in d]) 
                    subset SequenceToSet(C`S) join Support(Extra);
  end if;
  h := [H(x) : x in d];
  if #Extra ne 0 then
    // need to increase C`S.
    vprint Cohomology, 1: "Need to change the cohomology process, need to add", #Extra, "primes to the support";
    CC := SUnitCohomologyProcess(Set(C`S) join Support(Extra), U);
    for i in GetAttributes(Type(CC)) do
      if assigned C``i then
        delete C``i;
      end if;
      if assigned CC``i then
        C``i := CC``i;
        delete CC``i;
      end if;
    end for;
  end if;

  mSU := C`Units[1];
  SU := Domain(mSU);
  ac := C`Units[3];
  if false and assigned C`Data and C`Data[1] cmpeq H then
    // problem: the group changes as well, we can handle that, but it's 
    // more painful than currently useful.
    hh := C`Data[2];
  else
    hh := SUnitDiscLog(mSU, h, C`S:Base := C`Units[2]);
    C`Data := <H, hh>;
  end if;
  H := func<x|hh[Position(d, x)]>;
  if U eq G then
    cc := C`Coho;
  else
    X := AutomorphismGroup(SU, [SU.i : i in [1..Ngens(SU)]], [[SU.i @ x : i in [1..Ngens(SU)]] : x in ac]);
    mp := hom<G -> X | [X.i : i in [1..Ngens(X)]]>;
    cc := CohomologyModule(U, SU, [mp(U.i) : i in [1..Ngens(U)]]);
  end if;
  _ := CohomologyGroup(cc, 2);
  vprint Cohomology, 1: "The 2nd cohomology group with values in the S-units is of type", Moduli(CohomologyGroup(cc, 2));
  c := IdentifyTwoCocycle(cc, func<x|Eltseq(H(x))>);
  if IsZero(c) then
    vprint Cohomology, 1: "cocycle is trival";
    vprint Cohomology, 1: "looking for co-boundary now...";
    fl, x := IsTwoCoboundary(cc, func<x|Eltseq(H(x))>);
    //TODO: find "Nice" pre-image, ie. improve x
    assert fl;
    return true, func<y|PowerProduct(C`Units[2], mSU(Eltseq(x(y))))*fact(y)>;
  end if;
  vprint Cohomology, 1: "cocycle non zero:", Eltseq(c);
  return false, _;
end intrinsic;

intrinsic PowerProduct(B::[RngOrdFracIdl], E::[RngIntElt]) -> RngOrdFracIdl
  {The power product B^E.}
  //TODO: use a binary algorithm?
  if forall{e : e in E | IsZero(e)} then
    return 1*Order(B[1]);
  end if;
  return &* [B[i]^E[i] : i in [1..#B] | E[i] ne 0];
end intrinsic;


intrinsic IsSplitAsIdealAt(I::RngOrdFracIdl, l::UserProgram: Sub := false) -> .
  {For a 2-cocyle with values in the mult. group of some number field and some prime ideal I, see if the projection of l onto the group generated by I is trivial as a cocycle.}

  vprint Cohomology, 1: "Checking if 2-cocycle understood with values in the ideals is trivial";

  // we assume that
  //  - I behave essentially like a prime 
  //  - I is unramified
  //  - U is a subgroup of the automorphism group
  // we'll see...

  M := Order(I);
  G, _, mG := AutomorphismGroup(NumberField(M));
  if Sub cmpne false then
    U := Sub;
  else
    U := G;
  end if;

  val_at_i := function(x, P)
    if IsPrime(P) then
      return Valuation(x, P);
    end if;
    i := 0;
    PP := P;
    x := FieldOfFractions(M)!x;
    d := Denominator(x);
    if d ne 1 then
      n := x*M meet 1*M;
      d := x^-1*M meet 1*M;
      val_id := function(II)
        ii := 0;
        pp := P;
        while II subset pp do
          ii +:= 1;
          pp *:= P;
        end while;
        return ii;
      end function;
      i := val_id(M!!n) - val_id(M!!d);
      assert ((x*M/P^i meet 1*M) + P) eq 1*M;
      assert ((P^i/(x*M) meet 1*M) + P) eq 1*M;
      return i;
    end if;
    while x in PP do
      PP *:= P;
      i +:= 1;
    end while;
    assert (x*M/P^i + P) eq 1*M;
    return i;
  end function;

  //TODO: orbits can be computed in a more efficient way.
  // - starting with a small set
  // - acting only with the generators of the group
  orb := SetToSequence(Orbit(U, func<u|func<J|ideal<M|(u@mG)(Generators(J))>>>, I));
  vprint Cohomology, 2: "Ideal orbit of size", #orb;

  vprint Cohomology, 2: "Computing action matrices";
  vtime Cohomology, 2: act := [PermutationMatrix(Integers(),
              [Position(orb, ideal<M|(U.i@mG)(Generators(J))>) : J in orb])
         : i in [1..Ngens(U)]];
  C := CohomologyModule(U, [0 : i in orb], act);
  s := CohomologyGroup(C, 2);
  vprint Cohomology, 2: "2nd cohomology is of type", Moduli(s);
  //TODO: compute the "valuations" only once and possibly also check if the
  //factorisation is "complete". eg.
  //Let I = A*alpha with A being supported elsewhere (eg. the class. rep).
  //Then Norm(x*alpha^-v) should be coprime to Minimum(I)
  //If not, then I think we have a factor for I!
  ll := func<x|[val_at_i(l(x), P) : P in orb]>;
  fl, x := IsTwoCoboundary(C, ll);
  if not fl then
    vprint Cohomology, 1: "2-cocyle is non trivial";
    return false, _, orb;
  end if;
  vprint Cohomology, 1: "2-cocyle is trivial!";
  assert forall{x :x in car<U, U> | ll(x) eq Eltseq(lg(x))} where lg := CoboundaryMapImage(C, 1, x);
  return true, x, orb;
end intrinsic;

