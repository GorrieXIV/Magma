freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Fundamental domains for arithmetic Fuchsian groups
// February-May 2006, June 2007, John Voight
// July 2008, December 2008, John Voight
//
//////////////////////////////////////////////////////////////////////////////

declare verbose Shimura, 3;

forward InternalShimuraMingens, InternalShimuraInterreduce, 
        InternalShimuraSequenceDomain, InternalShimuraPruneGens, Vertices;

declare attributes GrpPSL2 : ShimFDArgs, ShimGroupSidepairsIndex, ShimWeight, ShimTotallyPositiveFlag;

declare attributes AlgAssVOrd : TotallyPositiveUnitsReps;
declare attributes AlgQuatOrd : TotallyPositiveUnitsReps;

declare attributes AlgQuat : prec;

import "definvs.m" : TotallyPositiveUnits;
import "../../ModFrmHil/level.m" : FindGammas;

AssignPrecision := procedure(B);
  Z_F := Integers(BaseField(B));
  prec := Log(Discriminant(Z_F)^(3/2)*Norm(Norm(Discriminant(B))));
  prec := Min(200,Max(40,Round(5*prec)));
  B`prec := prec;
end procedure;

InternalShimuraFDH := function(G,H);
  if assigned G`ShimFDDisc then
    return [DiscToPlane(H, x) : x in G`ShimFDDisc];
  else
    O := BaseRing(G);
    B := Algebra(O);
    if not assigned B`prec then AssignPrecision(B); end if;
    D := UnitDisc(: Center := 9/10*UpperHalfPlane().1, Precision := B`prec);
    F := FundamentalDomain(G, D);
    return [DiscToPlane(H, x) : x in F];
  end if;
end function;

//-------------
//
// Recognize norm one (and totally positive) units
//
//-------------

IsNormOneUnit := function(delta : JustTotallyPositive := false);
  Ndelta := Norm(delta);
  O := Parent(delta);
  if Abs(Norm(Ndelta)) eq 1 and not IsScalar(delta) then
    if Norm(Ndelta) lt 0 then
      if not assigned O`ElementOfNormMinusOne then
        O`ElementOfNormMinusOne := delta;
      end if;
      delta := delta*O`ElementOfNormMinusOne;
      Ndelta := Norm(delta);
    end if;
    TPU := NumberField(BaseRing(O))`TotallyPositiveUnits;
    for i := 1 to #TPU do
      bl, u := IsSquare(Ndelta/TPU[i]);
      if bl then
        delta := delta/u;
        if O`TotallyPositiveUnitsReps[i] ne O!1 or TPU[i] eq 1 then
          mu := O`TotallyPositiveUnitsReps[i];
        else
          mu := delta;
          O`TotallyPositiveUnitsReps[i] := mu;
        end if;
        if JustTotallyPositive then
          assert Norm(delta) eq TPU[i];
        else
          delta := delta*mu/TPU[i];
          assert Norm(delta) eq 1;
        end if;
        if not IsScalar(delta) then
          return true, delta;
        end if;
      end if;
    end for;
  end if;
  return false, _;
end function;

function NewGammas(gamma);
  G := Parent(gamma);
  O := BaseRing(G);
  A := Algebra(O);
  newgammas := [];
  gammaseq := Eltseq(A!Quaternion(gamma));
  for signs in [[1,1,-1],[1,-1,-1],[1,-1,1],[-1,1,1],[-1,1,-1],[-1,-1,1],[-1,-1,-1]] do
    newgamma := A!([gammaseq[1]] cat [gammaseq[1+i]*signs[i] : i in [1..3]]);
    if newgamma in O then
      Append(~newgammas,G!newgamma);
    end if;
  end for;
  return newgammas;
end function;

GuessBoundFor := function(G,L,numvecs);
  RR := BaseRing(L);
  bnddet := RR!ArithmeticVolume(G);
  for adjustcost := 1 to 5 do
    enumcost := EnumerationCostArray(L, bnddet)[1];
    enumcosthalf := EnumerationCostArray(L, bnddet/2)[1];
    ratio := enumcost/enumcosthalf;
    alpha := Max(-3, Log(enumcost/numvecs)/Log(ratio));
    bnddet /:= 2^alpha;
    bnddet := RR!bnddet;
  end for;
  enumcost := EnumerationCostArray(L, bnddet)[1];
  return bnddet, enumcost;
end function;

//-------------
//
// Main loop
//
//-------------

intrinsic FundamentalDomain(G::GrpPSL2, D::SpcHyd : StartDomain := [], 
                                 FindEnveloper := true, AssertDomain := false) -> 
                                 SeqEnum[SpcHydElt]
  {Computes a fundamental domain in the unit disc for the action of G.}

  O := BaseRing(G);

  if not assigned G`IsShimuraGroup then
    // Just return domain given by Farey symbols, etc.
    P := FundamentalDomain(G);
    return [PlaneToDisc(D, x) : x in P];
  end if;

  if not IsMaximal(O) and not AssertDomain then
    // Compute using the maximal order.
    vprint Shimura, 2: "Computing the group associated to the maximal order first";
    Omax := MaximalOrder(O);
    Gmax := FuchsianGroup(Omax : TotallyPositive := G`ShimTotallyPositiveFlag);
    _ := FundamentalDomain(Gmax, D);
    _ := Group(Gmax);

    foundgammas := FindGammas(O, Gmax);
    StartDomain cat:= foundgammas;
    vprint Shimura, 2: "Finished with maximal group";
  end if;

  // Find a reduced basis with respect to the absolute reduced norm with respect to p,
  // the center of the unit disc.  Use a weight vector w to adjust the absolute reduced
  // norm to deal with a potentially skew lattice Z_F at the split real place.
  Z_F := BaseRing(O);
  A := Algebra(O);
  F := BaseField(A);
  d := Degree(F);
  if BaseField(A) eq Rationals() then
    B := Basis(O);
  else
    B := ZBasis(O);
  end if;

  RR := RealField(D`prec);

  if not assigned F`TotallyPositiveUnits then
    UF, mUF := UnitGroup(Z_F);
    UFsq, mUFsq := TotallyPositiveUnits(Z_F, UF, mUF);
    F`TotallyPositiveUnits := [1] cat [mUF(UFsq.i@@mUFsq) : i in [1..#Generators(UFsq)]];
  end if;

  if not assigned O`TotallyPositiveUnitsReps then
    O`TotallyPositiveUnitsReps := [O | 1 : i in [1..#F`TotallyPositiveUnits]];
  end if;

  if d eq 1 then
    w := [1];
  else
    w := [RR!1 : v in RealPlaces(F)];
    w[Index(RealPlaces(F), SplitRealPlace(A))] := 
        (4*(RR!Discriminant(Z_F))^(1/d)*ArithmeticVolume(G))^(-1);
  end if;
  G`ShimWeight := w;

  vprint Shimura, 2: "Weight is", w;

  M := DefiniteGramMatrix(B : q := D!0, w := w);
  prec := D`prec;
  while not IsPositiveDefinite(M) do
    prec +:= D`prec;
    RR := RealField(prec);
    D := UnitDisc( : Center := ComplexField(RR)!ComplexValue(D`center));
    w := ChangeUniverse(w, RR);
    M := DefiniteGramMatrix(B : q := D!0, w := w);
  end while;
  L, T := LLL(LatticeWithGram(M));
  RR := BaseRing(L);

  // Initialize domain and flags.
  domain := [];
  bldomain := false;
  domainred := [];
  vol := ArithmeticVolume(G);

  CheckFinished := function(bldomain, domain);
    P, nonP := Vertices(domain, D);
    vprint Shimura, 2: "Vertices are", P, "and impropers occur at", nonP;
    if bldomain then
      volP := ArithmeticVolume(P);
      vprintf Shimura: "Current Volume = %o, which is %o times the fundamental volume\n", 
                                RealField(8)!volP, RealField(4)!(volP/vol);
      vprintf Shimura, 3: "Current domain is %o\n", domain;
      if volP/vol lt 1.5 then
        return true;
      end if;
    end if;
    return false;
  end function;

  // AssertDomain does a quick check, just sequencing the domain.
  if AssertDomain then
    vprint Shimura, 2 : "Domain asserted!";
    domain := ChangeUniverse(StartDomain, G);
    bldomain, _, domainnew := InternalShimuraSequenceDomain(domain, D);
    done := CheckFinished(bldomain, domainnew);
    vprint Shimura, 2 : "Checking finished:", done;

    if done and bldomain and domainnew eq domain then
      G`ShimFDGens := [O!Quaternion(d) : d in domain];
      G`ShimFDDisc := Vertices(domain, D);
      return G`ShimFDDisc;
    else
      print domain;
      print InternalShimuraSequenceDomain(domain,D);
      error "Domain asserted, but not a fundamental domain";
    end if;
  end if;

  // Start out by listing a slew of "small" vectors.
  if StartDomain ne [] then
    vprint Shimura, 2: "StartDomain found", #StartDomain;
    allgammas := ChangeUniverse(StartDomain, O);
  else
    allgammas := [];
  end if;

  // In the easy cases, don't work too hard!  Just list
  // a bunch and check.
  bnddet, enumcost := GuessBoundFor(G,L,400);  
  assert enumcost lt 10^4;
  vprintf Shimura, 2: "First enumeration up to %o (compared to %o), cost %o...\n", 
       RealField(4)!bnddet, (RealField(4)!1)*ArithmeticVolume(G), enumcost;
  vtime Shimura, 2: 
  latgammas := ShortVectors(L, bnddet);
 
  if #latgammas gt 1000*ArithmeticVolume(G) then
    keepar := Round(1000*ArithmeticVolume(G));
    latgammas := latgammas[1..keepar];
    vprintf Shimura, 2: "Keeping only %o latgammas...\n", keepar;
  end if;

  for latgamma in latgammas do
    gamma := &+[Round(latgamma[1][i])*B[i] : i in [1..4*d]];
    bl, delta := IsNormOneUnit(O!gamma : JustTotallyPositive := G`ShimTotallyPositiveFlag);
    if bl then 
      Append(~allgammas, delta);
    end if;
  end for;
  vprintf Shimura, 2: "Of %o vectors, %o were units (including StartDomain)...\n", #latgammas, #allgammas;

  vprintf Shimura, 2: "Trying cheap interreduction first...\n";
  bldomain, domain := InternalShimuraInterreduce(ChangeUniverse(allgammas, G), D : FindEnveloper := false);
  done := CheckFinished(bldomain, domain);
  if done then
    G`ShimFDGens := [O!Quaternion(d) : d in domain];
    G`ShimFDDisc := Vertices(domain, D);
    return G`ShimFDDisc;
  else
    vprintf Shimura, 2: "Trying with 1 enveloper now...\n";
    bldomain, domain := InternalShimuraInterreduce(ChangeUniverse(allgammas, G), D : FindEnveloper := 1);
    done := CheckFinished(bldomain, domain);
    if done then
      G`ShimFDGens := [O!Quaternion(d) : d in domain];
      G`ShimFDDisc := Vertices(domain, D);
      return G`ShimFDDisc;
    end if;
  end if;

  vprint Shimura, 2: "Now it's on!\n";

  // Now it's on.  Grab a bunch of vectors.
  bnddet, enumcost := GuessBoundFor(G,L,10^4);
  assert enumcost lt 10^5;

  vprintf Shimura, 2: "Full enumeration up to %o (compared to %o), cost %o...\n", 
       RealField(4)!bnddet, (RealField(4)!1)*ArithmeticVolume(G), enumcost;
  vtime Shimura, 2: 
  latgammas := ShortVectors(L, bnddet);

  for latgamma in latgammas do
    gamma := &+[Round(latgamma[1][i])*B[i] : i in [1..4*d]];
    bl, delta := IsNormOneUnit(O!gamma : JustTotallyPositive := G`ShimTotallyPositiveFlag);
    if bl then 
      Append(~allgammas, delta);
    end if;
  end for;
  vprintf Shimura, 2: "Of %o vectors, %o were units...\n", #latgammas, #allgammas;

  gammas := allgammas;
  gammas := ChangeUniverse(gammas, G);
  gammas cat:= &cat[NewGammas(gamma) : gamma in gammas];
  gammas := InternalShimuraPruneGens(gammas cat domain);
  vprintf Shimura, 2: "After pruning, starting with %o gammas...\n", #gammas;
  vprint Shimura, 3: gammas;

  for mmm := 0 to #gammas div 200 do
    domain := domain cat gammas[200*mmm+1..Min(200*(mmm+1),#gammas)];
    bldomain, domain := InternalShimuraInterreduce(domain, D : FindEnveloper := false);
    done := CheckFinished(bldomain, domain);
    if done then
      G`ShimFDGens := [O!Quaternion(d) : d in domain];
      G`ShimFDDisc := Vertices(domain, D);
      return G`ShimFDDisc;
    end if;
  end for;
  vprintf Shimura, 3: "Current domain is %o\n", domain;

  bldomain, domain := InternalShimuraInterreduce(domain, D : FindEnveloper := 2);
  done := CheckFinished(bldomain, domain);
  if done then
    G`ShimFDGens := [O!Quaternion(d) : d in domain];
    G`ShimFDDisc := Vertices(domain, D);
    return G`ShimFDDisc;
  end if;

  // Area either infinite or too big.
  done := false;
  m := 0;
  enveloperm := 2;
  bnddet0, enumcost := GuessBoundFor(G,L,10^5);
  while not done do
    m +:= 1;
    bnddetnew := bnddet0*m^(1/2/Degree(F));
    enumcostm := EnumerationCostArray(L, bnddetnew)[1];
    assert enumcostm lt 10^8;
    vprintf Shimura, 2: "==========================================\n";
    vprintf Shimura, 2: "Enumeration %o up to %o > %o, cost %o...\n", 
         m, RealField(4)!bnddetnew, RealField(4)!bnddet, enumcost;
    vtime Shimura, 2: 
    latgammas := ShortVectors(L, bnddet, bnddetnew);
    bnddet := bnddetnew;

    incr := 10000;
    for ell := 0 to (#latgammas div incr) do
      allgamas := [];
      for latgamma in latgammas[ell*incr+1..Min(#latgammas, (ell+1)*incr)] do
        gamma := &+[Round(latgamma[1][i])*B[i] : i in [1..4*d]];
        bl, delta := IsNormOneUnit(O!gamma : JustTotallyPositive := G`ShimTotallyPositiveFlag);
        if bl then 
          Append(~allgammas, delta);
        end if;
      end for;
      vprintf Shimura, 2: "Of %o vectors, %o were units...\n", 
        Min(#latgammas, (ell+1)*incr) - ell*incr, #allgammas;

      allgammasred := [];
      for delta in allgammas do    
        // Reduce delta to see if delta is new
        deltared := ShimuraReduceUnit(G!delta, domain, D);

        // We could skip reduced deltas that we've tried before, but this does not
        // seem to provide much savings in practice.
        if not IsScalar(Quaternion(deltared[1])) then 
          deltared := deltared[1];
          allgammasred cat:= [deltared] cat NewGammas(deltared);
        end if;
      end for;
      vprintf Shimura, 2: "Of %o units, %o were new....\n", #allgammas, #allgammasred;

      if #allgammasred gt 0 or m mod (2*enveloperm) eq 0 then
        domain cat:= allgammasred;
        enveloperm +:= 2;
        // Now interreduce the generators.
        bldomain, domain := InternalShimuraInterreduce(domain, D : 
                                              FindEnveloper := enveloperm, sstart := m);
        done := CheckFinished(bldomain, domain);
        if done then
          break ell;
        end if;
      end if;
    end for;
  end while;

  G`ShimFDGens := [O!Quaternion(d) : d in domain];
  G`ShimFDDisc := Vertices(domain, D);
  return G`ShimFDDisc;
end intrinsic;

//-------------
//
// Reduction algorithm for units.
//
//-------------

intrinsic WordProblem(delta::GrpPSL2Elt) -> SeqEnum
  {Write delta as a word in the generators for its parent Fuchsian group.}

  c := ShimuraReduceUnit(delta);
  assert IsScalar(Quaternion(c[1]));
  return Group(Parent(delta))!c[3];
end intrinsic;

intrinsic ShimuraReduceUnit(delta::GrpPSL2Elt : z0 := 0) -> SeqEnum
  {Optimized reduction algorithm which writes delta as a word in the generators for Gamma by reducing
   on the left.}

  Gamma := Parent(delta);
  D := Parent(Gamma`ShimFDDisc[1]);

  if Quaternion(delta) ne 1 then
    z0 := delta*(D!z0);
  end if;
  lseq := [];

  Uside := Gamma`ShimGroupSidepairs;
  mside := Gamma`ShimGroupSidepairsMap;

  if not assigned Gamma`ShimGroupSidepairsQuats then
    d := #Generators(Uside);
    U,m := Group(Gamma);
    gquats := [m(mside(Uside.i)) : i in [1..d]];
    Gamma`ShimGroupSidepairsQuats := <gquats, [g^(-1) : g in gquats]>;
  end if;
  gammas := Gamma`ShimGroupSidepairsQuats;
  if not assigned Gamma`ShimGroupSidepairsIndex then
    d := #Generators(Uside);
    fIndex := [0 : i in [1..2*d]];
    for j := 1 to #Gamma`ShimFDSidepairs do
      s := Gamma`ShimFDSidepairs[j];
      fIndex[(s[3][1] mod (2*d))+1] := j;
      fIndex[(s[4][1] mod (2*d))+1] := -j;
    end for;
    Gamma`ShimGroupSidepairsIndex := fIndex;
  end if;
  fIndex := Gamma`ShimGroupSidepairsIndex;
  pi := Pi(RealField(Parent(ComplexValue(Gamma`ShimFDDisc[1]))));
  if not assigned Gamma`ShimFDArgs then
    Vs := Vertices(ChangeUniverse(Gamma`ShimFDSidepairsDomain,Gamma), D);
    Gamma`ShimFDArgs := [Argument(z) : z in Vs[2..#Vs]];

    for i := 2 to #Gamma`ShimFDArgs do
      if Gamma`ShimFDArgs[i-1] gt Gamma`ShimFDArgs[i] then
        Gamma`ShimFDArgs[i] +:= 2*pi;
      end if;
    end for;
    assert &and[Gamma`ShimFDArgs[i] lt Gamma`ShimFDArgs[i+1] : i in 
                   [1..#Gamma`ShimFDArgs-1]];
  end if;
  FDArgs := Gamma`ShimFDArgs;

  while not IsScalar(Quaternion(delta)) do
    az0 := Argument(ComplexValue(z0));
    if az0 lt FDArgs[1] then
      az0 +:= 2*pi;
    end if;
    if az0 gt FDArgs[#FDArgs] then
      ji := fIndex[1];
      if ji lt 0 then
        gg := gammas[2][Abs(ji)];
      else
        gg := gammas[1][ji];
      end if;
      if Abs(ComplexValue(gg*z0)) ge Abs(ComplexValue(z0)) then
        ji := fIndex[2];
      end if;
    else
      i := 1;
      while az0 gt FDArgs[i] do
        i +:= 1;
      end while;
      ji := fIndex[i+1];
    end if;
    if ji lt 0 then
      gg := gammas[2][Abs(ji)];
    else
      gg := gammas[1][ji];
    end if;

/*
    assert Abs(ComplexValue(gg*z0)) lt Abs(ComplexValue(z0)) or
          Abs(Abs(ComplexValue(z0)) - 1) lt 100*D`eps;
*/
    z0 := gg*z0;
    delta := gg*delta;
    if #lseq gt 0 and ji + lseq[1] eq 0 then
      // Had a choice, need to pick the other
      ii := -#gammas[1];
      while ii le #gammas[1] do
        if ii + ji ne 0 then
          if (ii lt 0 and Abs(ComplexValue(gammas[2][Abs(ii)]*z0)) lt 
                         Abs(ComplexValue(z0))) or
             (ii gt 0 and Abs(ComplexValue(gammas[1][ii]*z0)) lt 
                         Abs(ComplexValue(z0))) then
            ji := ii;
          else 
            ii +:= 1;
          end if;
        end if;
      end while;
      assert ji + lseq[1] ne 0;
    end if;
    lseq := [ji] cat lseq;
  end while;  

  c := Eltseq(mside(Uside!lseq^(-1)));

  return <delta, lseq, c>;
end intrinsic;

intrinsic ShimuraReduceUnit(delta::GrpPSL2Elt, gammas::SeqEnum[GrpPSL2Elt],
                                               D::SpcHyd : z0 := 0, Inverses := false) -> SeqEnum
  {Optimized reduction algorithm which writes delta as a word in gammas by reducing
   on the left.}

  if #gammas eq 0 then
    return <delta, []>;
  end if;
  if Quaternion(delta) ne 1 then
    z0 := delta*(D!z0);
  end if;
  cz0 := ComplexValue(D!z0);
  lseq := [];

  gammamats := [Matrix(g,D) : g in gammas];
  gammamats := [A/Sqrt(Determinant(A)) : A in gammamats];
  gammamatsinv := [g^(-1) : g in gammamats];

  repeat
    moved := false;
    for i := 1 to #gammas do
      if Abs(gammamats[i][2,1]*cz0+gammamats[i][2,2]) lt 1-D`eps then
        moved := true;
        z0 := gammas[i]*z0;
        cz0 := ComplexValue(z0);
        delta := gammas[i]*delta;
        lseq := [i] cat lseq;
        continue;
      elif Inverses and Abs(gammamatsinv[i][2,1]*cz0+gammamatsinv[i][2,2]) lt 1-D`eps then
        moved := true;
        z0 := gammas[i]^(-1)*z0;
        cz0 := ComplexValue(z0);
        delta := gammas[i]^(-1)*delta;
        lseq := [-i] cat lseq;
        continue;
      end if;
    end for;
  until not moved;

  return <delta, lseq>;
end intrinsic;

//-------------
//
// Algorithm to iteratively building a convex domain.
//
//-------------

// Given a sequence domain of elements, return if the convex polygon
// of isometric circles for domain is compact, and the resulting
// sequence of elements.
InternalShimuraSequenceDomain := function(domain,D);
  if #domain eq 0 then
    return false, [], domain;
  elif #domain eq 1 then
    return false, [1], domain;
  end if;

  domain := InternalShimuraPruneGens(domain);

  vprint Shimura, 2: "Sequencing domain...";

  C := [];
  for i := 1 to #domain do
    c, r := IsometricCircle(domain[i], D);
    C[i] := <c,r>;
  end for;

  B := [BoundaryIntersection(domain[i], D) : i in [1..#C]];
  B := [[Argument(B[i][1]), Argument(B[i][2])] : i in [1..#C]];
  V := [];

  for i := 1 to #domain do
    for j := i+1 to #domain do
      h := InternalIntersection(C[i][1], C[i][2], C[j][1], C[j][2], D);
      if Type(h) eq SpcHydElt then
        Append(~V, <Abs(h), Argument(h), i, j>);
      end if;
    end for;
  end for;

  vprint Shimura, 3: "Intersections computed!";

  // Initialize
  Y := [];
  for i := 1 to #domain do
    M := Matrix(domain[i], D);
    M /:= Sqrt(Determinant(M));
    rts := Roots(Polynomial(
      [ Abs(M[2,2])^2-1, 2*Re(M[2,1]*ComplexConjugate(M[2,2])), Abs(M[2,1])^2]));
    rts := [r[1] : r in rts | r[1] lt 1+D`eps and r[1] gt 0];
    if #rts ge 1 then
      Append(~Y, <rts[1], i>);
    end if;
  end for;
  if #Y eq 0 then
    // Choose the element whose initial infinite vertex comes first.
    isCompact := false;

    Vnext := [B[i][1] : i in [1..#B]];
    thetapos := 0;
    for i in [1..#B] do
      if Vnext[i] lt thetapos then
        Vnext[i] +:= 2*Pi(RealField(D`prec));
      end if;
    end for;
    Vnext := [<Vnext[i]-thetapos,i> : i in [1..#B] | Vnext[i] gt thetapos+2*D`eps];
    ipos := Min(Vnext)[2];
    thetapos := Vnext[ipos][1]+thetapos+D`eps;
    domainnew := [ipos, ipos];
  else
    ymin := Min(Y);
    ymin := ComplexField(Parent(ymin[1]))!ymin[1];
    Y := [y : y in Y | Abs(ymin-y[1]) lt D`eps];
    if #Y gt 1 then
      // If more than one, choose the smallest interior angles
      T := [<InternalTangentAngle(C[y[2]][1], ymin), y[2]> : y in Y];
      Sort(~T);
      t := 1;
      while T[t][1] lt 0 do
        t +:= 1;
      end while;
      domainnew := [T[t][2], T[t][2], T[t-1][2]];
      ipos := domainnew[3];
    elif #Y eq 1 then
      domainnew := [Y[1][2], Y[1][2]];
      ipos := domainnew[2];
    end if;
    thetapos := 0;
    isCompact := true;
  end if;

  repeat
    // Compute the set of geodesics which intersect the current one
    Vnext := [<v[2], v[4]> : v in V | 
                    v[3] eq ipos and v[4] ne domainnew[#domainnew-1] and 
                    v[1] lt 1+D`eps];
    Vnext cat:= [<v[2], v[3]> : v in V | 
                       v[4] eq ipos and v[3] ne domainnew[#domainnew-1] 
                       and v[1] lt 1+D`eps];
    if B[ipos][1] gt B[ipos][2] then
      // Adjust for overlap
      for i := 1 to #Vnext do
        if Vnext[i][1] lt 0 then
          Vnext[i][1] +:= 2*Pi(RealField(D`prec));
        end if;
      end for;
      if thetapos lt 0 then
        thetapos +:= 2*Pi(RealField(D`prec));
      end if;
    end if;
  
    // Include only those that "come next"
    Vnext := [v : v in Vnext | v[1] gt thetapos+D`eps];

    // print domainnew, thetapos, Vnext;
   
    if #Vnext eq 0 then
      // No connecting vertex, so domain is not compact!
      // So return the next improper vertex.
      isCompact := false;

      Vnext := [B[i][1] : i in [1..#B]];
      thetapos := B[domainnew[#domainnew]][2];
      for i in [1..#B] do
        if Vnext[i] lt thetapos then
          Vnext[i] +:= 2*Pi(RealField(D`prec));
        end if;
      end for;
      Vnext := [<Vnext[i]-thetapos,i> : i in [1..#B] | Vnext[i] gt thetapos+2*D`eps];
      if #Vnext eq 0 then
        inext := ipos;
      else
        inext := Min(Vnext)[2];
      end if;
      thetanext := Vnext[inext][1]+thetapos+D`eps;
    else
      // Find the "next" vertex
      Sort(~Vnext);
      thetanext := Vnext[1][1];
      Vnext := [v : v in Vnext | Abs(v[1]-thetanext) lt D`eps];
      // print Vnext;
      if #Vnext gt 1 then
        // If more than one, choose the smallest interior angle
        T := [<InternalAngle(C[Vnext[vi][2]][1], C[Vnext[vi][2]][2], 
                             C[ipos][1], C[ipos][2], D), vi> :
                             vi in [1..#Vnext]];
        // print "T!", T;
        _, t := Min(T);
        inext := Vnext[T[t][2]][2];
      else
        inext := Vnext[1][2];
      end if;
  
      Sort(~Vnext);
      thetanext := Vnext[1][1];
    end if;
  
    // Renormalize the next angle
    if thetanext gt Pi(RealField(D`prec)) then
      thetanext -:= 2*Pi(RealField(D`prec));
    end if;
    Append(~domainnew, inext);
    
    // Repeat
    thetapos := thetanext;
    ipos := inext;
  until domainnew[#domainnew] in domainnew[1..#domainnew-1] or #domainnew gt #domain+2; 
  // i.e., until we intersect the starting geodesic again.

  if #domainnew gt #domain+2 then
    error "Error in FundamentalDomain, #domainnew gt #domain", domainnew;
  end if;

  domainnew := domainnew[2..#domainnew];
  return isCompact, domainnew[Index(domainnew,domainnew[#domainnew])..#domainnew-1], domain;
end function;

//-------------
//
// Algorithms to build a fundamental domain from an order.
//
//-------------

// Returns a multiplicatively minimal subset of generators among the set gammas.
InternalShimuraMingens := function(gammas,G,D);
  if #gammas eq 0 then
    return gammas;
  end if;

  if Type(gammas[1]) eq AlgAssVOrdElt then
    O := Parent(gammas[1]);
    A := Algebra(O);
    gammas := ChangeUniverse(gammas, A);
    returnOFlag := true;
  else
    returnOFlag := false;
  end if;

  gammagens := [];
  for gamma in gammas do
    gammared := ShimuraReduceUnit(gamma, gammagens, G, D)[1][1];
    if not IsScalar(gammared) then
      Append(~gammagens, gammared);
    end if;
  end for;

  if returnOFlag then
    return ChangeUniverse(gammagens, O);
  else
    return gammagens;
  end if;
end function;

// Removes redundant elements of domain.
InternalShimuraPruneGens := function(domain);
  if #domain lt 2 then
    return domain;
  end if;

  domainQuats := [Quaternion(g) : g in domain];
  domainQuats := [g : g in domainQuats | not IsScalar(g)];
  domainTraces := [<Trace(Trace(domainQuats[i])), i> : i in [1..#domainQuats]];
  for i := 1 to #domainTraces do
    if domainTraces[i][1] lt 0 then
      domainQuats[i] *:= -1;
      domainTraces[i][1] *:= -1;
    end if;
  end for;
  Sort(~domainTraces);
  i := 1;
  while i lt #domainTraces do
    j := i+1;
    tracei := domainTraces[i][1];
    gi := domainQuats[domainTraces[i][2]];
    while j le #domainTraces do
      gj := domainQuats[domainTraces[j][2]];
      if IsScalar(gi*gj^(-1)) then
        Remove(~domainTraces, j);
      else
        j +:= 1;
      end if;
    end while;
    i +:= 1;
  end while;
  domainLeft := [g[2] : g in domainTraces];
  Sort(~domainLeft);
  return ChangeUniverse([domainQuats[i] : i in domainLeft], Parent(domain[1]));
end function;

Vertices := function(domain, D);
  if #domain eq 0 then
    return [], [];
  elif #domain eq 1 then
    return [], [1];
  end if;

  C := [];
  for i := 1 to #domain do
    c,r := IsometricCircle(domain[i], D);
    C[i] := <c,r>;
  end for;
  Z := [];
  failedIndices := [];
  for i := 1 to #domain do
    if domain[i] eq domain[i mod #domain+1] then
      z := FixedPoints(domain[i], D)[1];
    else
      z := InternalIntersection(C[i][1], C[i][2], C[i mod #domain+1][1],
                                C[i mod #domain+1][2], D);
    end if;
    if z cmpeq [] then
      Append(~Z, D!0);
      Append(~failedIndices, i);
    else
      Append(~Z, z);
    end if;
  end for;
  return [Z[#Z]] cat Z[1..#Z-1], failedIndices;
end function;

InternalShimuraFindEnveloper := function(G,domain,z : Trials := 3, sstart := 0);
  D := Parent(z);
  q0 := D!0;

  O := BaseRing(G);

  deltared := ShimuraReduceUnit(G!O!1,domain,D : z0 := D!(99/100*z));
  if not IsScalar(Quaternion(deltared[1])) then
    vprint Shimura, 3: "Already external to domain";
    return deltared[1], [];
  end if;

  // Find a reduced basis with respect to the absolute reduced norm with respect to p,
  // the center of the unit disc.
  A := Algebra(O);
  d := Degree(BaseField(A));
  if BaseField(A) eq Rationals() then
    B := Basis(O);
  else
    B := ZBasis(O);
  end if;

  foundelts := [];

  q0 := D!(1/100*z);
  h0 := Distance(q0,D!0) + sstart/2;
  cscale := (Exp(h0)-1)/(Exp(h0)+1);
  q0 := D!(cscale*q0/Abs(q0));

  for cnt := 0 to Trials do  
    h0 := Distance(q0,D!0) + 1/2;
    cscale := (Exp(h0)-1)/(Exp(h0)+1);
    q0 := D!(cscale*q0/Abs(q0));

    M := DefiniteGramMatrix(B : q := q0, w := G`ShimWeight);
    if not IsPositiveDefinite(M) then
      // Means lattice is too small, need to give up.
      return 0, foundelts;
    end if;
    L := LLL(LatticeWithGram(M));

    bnddet, enumcost := GuessBoundFor(G,L,10^4);

    vprintf Shimura, 2: "Enumeration for q = %o up to %o, cost %o...\n",
         RealField(6)!Abs(q0), RealField(4)!bnddet, enumcost;
    vtime Shimura, 2:
    latgammas := ShortVectors(L, bnddet);

    allgammas := [];
    for latgamma in latgammas do
      gamma := &+[Round(latgamma[1][i])*B[i] : i in [1..4*d]];
      bl, delta := IsNormOneUnit(O!gamma : JustTotallyPositive := G`ShimTotallyPositiveFlag);
      if bl then
        Append(~allgammas, delta);
      end if;
    end for;
    vprintf Shimura, 2: "Of %o vectors, %o were units...\n", #latgammas, #allgammas;
    allgammas := ChangeUniverse(allgammas, G);

    allgammasred := [];
    for delta in allgammas do
      deltared := ShimuraReduceUnit(delta, domain, D);
      if not IsScalar(Quaternion(deltared[1])) then
        Append(~allgammasred, deltared[1]);
      end if;
    end for;
    vprintf Shimura, 2: "Of %o units, %o were new...\n", #allgammas, #allgammasred;
    foundelts cat:= allgammasred;

    for delta in allgammasred do
      c, r := IsometricCircle(delta, D);
      if Abs(c-z) lt r-10*D`eps then
        return delta, foundelts;
      end if;
    end for;
  end for;

  return 0, foundelts;
end function;

// Given a set of generators gammas and a set of elements domain,
// attempt to interreduce domain by adding elements to obtain a minimal
// convex domain.
InternalShimuraInterreduce := function(domain,D : FindEnveloper := true, sstart := 0);
  if #domain le 1 then
    return false, [];
  end if;

  G := Parent(domain[1]);

  domain := InternalShimuraPruneGens(domain);
  cntfindenveloper := 0;

  SequenceAndInterreduce := function(domain);
    repeat
      changed := false;
      bl, domainnewseq, domain := InternalShimuraSequenceDomain(domain, D);
      domainnew := [domain[d] : d in domainnewseq];
      for delta in [delta : delta in domain | not &or[ IsScalar(Quaternion(delta*ddgg^(-1))) : ddgg in domainnew]] do
        deltared := ShimuraReduceUnit(delta^(-1), domainnew, D);
        vprint Shimura, 3: deltared;
        if not IsScalar(Quaternion(deltared[1])) and
          not &or[IsScalar(Quaternion(deltared[1]*ddgg^(-1))) : ddgg in domain] then
          vprint Shimura, 2: "Found new via interreduction", deltared[1];
          Append(~domain, deltared[1]);
          domain cat:= NewGammas(deltared[1]);
          changed := true;
        else
          vprint Shimura, 2: "Removed redundant element", delta;
          Remove(~domain, Index(domain, delta));
        end if;
      end for;
    until not changed;

    return bl, domainnew;
  end function;

  bl, domain := SequenceAndInterreduce(domain);
  vprint Shimura, 3 : "domain :=", domain;

  domain := InternalShimuraPruneGens(domain);
  Z, nonV := Vertices(domain, D);

  repeat
    cntfindenveloper +:= 1;
    // Don't waste too much time finding envelopers!
    if not bl and  
      ((Type(FindEnveloper) eq BoolElt and FindEnveloper) or 
       (Type(FindEnveloper) eq RngIntElt and cntfindenveloper le FindEnveloper)) then
      for inoncompact in nonV do
        vprint Shimura,3: "Noncompact, so looking for start at", inoncompact;  

        // Attempt to find a generator which connects
        B := BoundaryIntersection(domain[inoncompact], D);
        zarg := Argument(B[2]);

        z := D!((1-10*D`eps)*B[2]);
        vprintf Shimura, 2: "Finding enveloper for %o\n", Argument(z);
        if Type(FindEnveloper) eq BoolElt then
          deltared, extras := InternalShimuraFindEnveloper(G, domain, z : sstart := sstart);
        else
          deltared, extras := InternalShimuraFindEnveloper(G, domain, z : Trials := FindEnveloper, sstart := sstart);
        end if;
        if deltared cmpeq 0 then
          vprint Shimura, 2: "None found";
          domain cat:= extras;
        else
          vprint Shimura, 2: "Found", deltared;
          domain cat:= [deltared] cat extras;
        end if;
        vprint Shimura, 2: "Taking", #extras, "extras";
        if #extras gt 200 then
          vprint Shimura, 2: "Lotsa extras, so aborting enveloper search";
          break inoncompact;
        end if;
      end for;

      bl, domain := SequenceAndInterreduce(domain);
      vprint Shimura, 3 : "domain :=", domain;
    end if;
 
    repeat
      vprint Shimura, 2 : "REDUCING!";
      domainreduceold := domain;

      domain := InternalShimuraPruneGens(domain);
      Z, nonV := Vertices(domain, D);
      V := [i : i in [1..#domain] | i notin nonV];
      domainwoot := [];
      allpaired := true;

      while #V gt 0 do
        vprint Shimura, 3: V;
        i := V[1];
        j := 1;
        while j le #domain and not IsScalar(Quaternion(domain[i]*domain[j])) do
          j +:= 1;
        end while;
        if j gt #domain then
          j := 0;
        end if;
        if j eq 0 then
          vprint Shimura, 2: i, "has no pair";
          deltared := ShimuraReduceUnit(domain[i], domain, D : z0 := Z[i]);
          vprint Shimura, 3: deltared;
          if not IsScalar(Quaternion(deltared[1])) and deltared[2] ne [] then
            Append(~domainwoot, deltared[1]);
            domainwoot cat:= NewGammas(deltared[1]);
          end if;
          deltared := ShimuraReduceUnit(domain[i], domain, D : z0 := Z[i mod #domain + 1]);
          vprint Shimura,3: deltared;
          if not IsScalar(Quaternion(deltared[1])) and deltared[2] ne [] then
            Append(~domainwoot, deltared[1]);
            domainwoot cat:= NewGammas(deltared[1]);
          end if;
          allpaired := false;
        else
          pairedw1 := Abs(domain[i]*Z[i]-Z[j]) lt D`eps and
                        Abs(domain[i]*Z[i mod #domain + 1]-Z[j mod #domain + 1]) lt D`eps;
          pairedw2 := Abs(domain[i]*Z[i]-Z[j mod #domain + 1]) lt D`eps and
                        Abs(domain[i]*Z[i mod #domain + 1]-Z[j]) lt D`eps;
          if not (pairedw1 or pairedw2) then
            vprint Shimura,3: i, "has vertices not paired";
            deltared := ShimuraReduceUnit(domain[i], domain, D : z0 := Z[i]);
            vprint Shimura,3: deltared;
            if not IsScalar(Quaternion(deltared[1])) and deltared[2] ne [] then
              Append(~domainwoot, deltared[1]);
              domainwoot cat:= NewGammas(deltared[1]);
            end if;
            deltared := ShimuraReduceUnit(domain[i], domain, D : z0 := Z[i mod #domain + 1]);
            vprint Shimura,3: deltared;
            if not IsScalar(Quaternion(deltared[1])) and deltared[2] ne [] then
              Append(~domainwoot, deltared[1]);
              domainwoot cat:= NewGammas(deltared[1]);
            end if;
            deltared := ShimuraReduceUnit(domain[j], domain, D : z0 := Z[j]);
            vprint Shimura,3: deltared;
            if not IsScalar(Quaternion(deltared[1])) and deltared[2] ne [] then
              Append(~domainwoot, deltared[1]);
              domainwoot cat:= NewGammas(deltared[1]);
            end if;
            deltared := ShimuraReduceUnit(domain[j], domain, D : z0 := Z[j mod #domain + 1]);
            vprint Shimura,3: deltared;
            if not IsScalar(Quaternion(deltared[1])) and deltared[2] ne [] then
              Append(~domainwoot, deltared[1]);
              domainwoot cat:= NewGammas(deltared[1]);
            end if;
            allpaired := false;
          else
            vprint Shimura,3: "Side paired with index", j;
          end if;
          ind := Index(V, j);
          if ind ne 0 then
            Remove(~V, ind);
          end if;
        end if;
        if #V gt 0 and V[1] eq i then
          Remove(~V,1);
        end if;
      end while;

      domain := domain cat domainwoot;
      domain := InternalShimuraPruneGens(domain);

      vprint Shimura, 2 : "DONE REDUCING!";
      bl, domain := SequenceAndInterreduce(domain);
      vprint Shimura, 3 : "domain :=", domain;
      done := allpaired or
        (#domain eq #domainreduceold and 
         &and[ IsScalar(Quaternion(domain[i]*domainreduceold[i]^(-1))) : i in [1..#domain]]);
    until done;
    done := bl or cntfindenveloper gt 3;
  until done;

  return bl, domain;
end function;


HistoricShimuraReduceUnit := function(delta, gammagens, G, D : z0 := 0, z1 := 0,
                                      CreateWord := false, NextSmallest := false, 
                                      ReduceOnRight := true);
/*
  {Reduce the unit delta with respect to the generators in gammagens
   by multiplying on the left or right by elements of gammagens to minimize
   the distance from z1 to the image of z0.  Returns a sequence of triples containing
   reduced elements and the sequence on the left and right to obtain them.
   The argument CreateWord reduces delta even if delta is in gammagens,
   disallowing the trivial word.}
*/

  if #gammagens eq 0 then
    return [<delta, [], []>];
  end if;
  z0 := D!z0;
  z1 := D!z1;

  // Initialize generators and distance.
  gammas := [];
  gammasquat := [];
  gs := [];
  for i := 1 to #gammagens do
    gammas cat:= [G!gammagens[i], G!(gammagens[i]^(-1))];
    gammasquat := [gammagens[i], gammagens[i]^(-1)];
    gs cat:= [i, -i];
  end for;
  r := Distance((G!delta)*z0, z1);

  // Take care if delta fixes the origin.
  if r lt D`eps then
    if not CreateWord or Abs(z0-z1) gt D`eps then
      return [<delta, [], []>];
    else
      r := Infty;
    end if;
  end if;

  // Initialize the permitted left and right gammas.  Artificially
  // add them, then take them away at the end.
  if delta in gammasquat and CreateWord then
    added := true;
    nul := [gs[Index(gammasquat, delta)]];
    nur := nul;
  elif -delta in gammasquat and CreateWord then
    added := true;
    nul := [gs[Index(gammasquat, -delta)]];
    nur := nul;
  else
    added := false;
    nul := [];
    nur := [];
  end if;

  while true do
    deltaz0 := (G!delta)*z0;

    // Find the set of permitted left and right gammas.
    if #nul ne 0 then
      tsl := [t : t in [1..#gammas] | not (gs[t] eq -nul[1] or
                                           (Quaternion(gammas[t])^4 eq 1 and gs[t] eq nul[1]))];
      gammasl := [gammas[t] : t in tsl];
      gsl := [gs[t] : t in tsl];
    else
      gammasl := gammas;
      gsl := gs;
    end if;
    if ReduceOnRight then
      if #nur ne 0 then
        tsr := [t : t in [1..#gammas] | not (gs[t] eq -nur[#nur] or
                                             (Quaternion(gammas[t])^4 eq 1 and gs[t] eq nur[#nur]))];
        gammasr := [gammas[t] : t in tsr];
        gsr := [gs[t] : t in tsr];
      else
        gammasr := gammas;
        gsr := gs;
      end if;
    else
      gammasr := [];
    end if;

    // Compute distances
    if not ReduceOnRight then
      rsl := [Distance(gamma*deltaz0,z1) : gamma in gammasl];
      rsr := [];
    else
      rsl := [Distance((gamma*(G!delta))*z0,z1) : gamma in gammasl];
      rsr := [Distance(((G!delta)*gamma)*z0,z1) : gamma in gammasr];
    end if;

    if #rsl gt 0 then
      minl, iil := Min(rsl);
    else
      minl := r+1;
      iil := 0;
    end if;
    if #rsr gt 0 then
      minr, iir := Min(rsr);
    else
      minr := r+1;
      iir := 0;
    end if;
    min := Min(minl, minr);

    // print r, min, rsl, rsr, gsl, gsr;

    if Type(r) eq Cat then
      // r eq Infty, so just take it as the new min
      if minl le minr then
        delta := Quaternion(gammasl[iil])*delta;
        nul := [gsl[iil]] cat nul;
      else
        delta := delta*gammasr[iir];
        nur := nur cat [gsr[iir]];
      end if;
      r := min;
    elif (Abs(min) lt D`eps or Abs(min-r) lt D`eps) or
         (NextSmallest and (min gt r-D`eps or Abs(min) lt D`eps)) then
      // min = 0 implies we have reached the origin and we're done!
      // min = r implies that we have an elliptic point, so we have
      // more than one reduced element, and we're also done!

      if NextSmallest then
        min := r;
      end if;

      // Remove artificially added restricted nus.
      if added then
        nul := nul[1..(#nul-1)];
        nur := nur[2..#nur];
      end if;
      deltaseqs := [];
      deltascheck := [];

      // Cycle through and add all possible reduced elements.
      for t := 1 to #gammasl do
        if Abs(min-rsl[t]) lt D`eps then
          if Quaternion(gammasl[t])*delta notin deltascheck then
            deltaseqs cat:= [<Quaternion(gammasl[t])*delta, [gsl[t]] cat nul, nur>];
            deltascheck cat:= [Quaternion(gammasl[t])*delta, -Quaternion(gammasl[t])*delta];
          end if;
        end if;
      end for;
      for t := 1 to #gammasr do
        if Abs(min-rsr[t]) lt D`eps then
          if delta*Quaternion(gammasr[t]) notin deltascheck then
            deltaseqs cat:= [<delta*Quaternion(gammasr[t]), nul, nur cat [gsr[t]]>];
            deltascheck cat:= [delta*Quaternion(gammasr[t]), -delta*Quaternion(gammasr[t])];
          end if;
        end if;
      end for;
      // If the initial delta is reduced, add it.
      if Abs(min-r) lt D`eps then
        Append(~deltaseqs, <delta, nul, nur>);
      end if;

      // Return the list of reduced elements.
      return deltaseqs;
    elif min gt r-D`eps then
      // None are smaller, so we're done!
      // Remove artificially added restricted nus.
      if added then
        nul := nul[1..(#nul-1)];
        nur := nur[2..#nur];
      end if;

      return [<delta, nul, nur>];
    else
      // We're not done, we have a new min!

      if minl le minr then
        delta := Quaternion(gammasl[iil])*delta;
        nul := [gsl[iil]] cat nul;
      else
        delta := delta*Quaternion(gammasr[iir]);
        nur := nur cat [gsr[iir]];
      end if;

      // Reset r and repeat!
      r := min;
    end if;
  end while;
end function;

//----------------
//
// Supplementary code
//
//----------------

PrintDomain := procedure(deltas, D);
  printf "\\begin{center}\n\\psset{unit=2.5in}\n\\begin{pspicture}(-1,-1)(1,1)\n\\pscircle[fillstyle=solid,fillcolor=lightgray](0,0){1}\n\n";

  for delta in deltas do
    c,r := IsometricCircle(delta,D);
    printf "\\psclip{\\pscircle(0,0){1}} \\pscircle[fillstyle=solid,fillcolor=white](%o,%o){%o} \\endpsclip\n", 
      RealField(6)!Re(c), RealField(6)!Im(c), Max(RealField(6)!r,0.001);
  end for;

  printf "\n";

  for delta in deltas do
    c,r := IsometricCircle(delta,D);
    printf "\\psclip{\\pscircle(0,0){1}} \\pscircle(%o,%o){%o} \\endpsclip\n", 
      RealField(6)!Re(c), RealField(6)!Im(c), Max(RealField(6)!r,0.001);
  end for;

  printf "\\pscircle(0,0){1}\n\\end{pspicture}\n\\end{center}\n\n\\end{document}\n";
end procedure;
