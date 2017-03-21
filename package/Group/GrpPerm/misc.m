freeze;

intrinsic SymmetricCentralizer(x::GrpPermElt) -> GrpPerm
{The centralizer of x in the symmetric group containing x}

    S := Generic(Parent(x));
    to_do := Support(S);
    lengths := {@ @};
    cyc_classes := [];
    while #to_do gt 0 do
	i := Rep(to_do);
	c := Cycle(x, i);
	to_do diff:= IndexedSetToSet(c);
	pos := Index(lengths, #c);
	if pos eq 0 then
	    Include(~lengths, #c);
	    Append(~cyc_classes, [c]);
	else
	    Append(~cyc_classes[pos], c);
	end if;
    end while;
    gens := [];
    ord := 1;
    for cycs in cyc_classes do
	c := cycs[1];
	n := #cycs;
	if #c gt 1 then
	    Append(~gens, S!{c});
	    ord *:= #c^n;
	end if;
	if n eq 1 then continue cycs; end if;
	ord *:= Factorial(n);
	x := S!{ {@ cycs[1,j], cycs[2,j] @}: j in [1..#c] };
	Append(~gens, x);
	if n eq 2 then continue cycs; end if;
	x := S!{ {@ cycs[i,j]:i in [1..n] @}: j in [1..#c] };
	Append(~gens, x);
    end for;
    C := sub<S|gens>;
    AssertAttribute(C, "Order", ord);
    return C;
end intrinsic;

intrinsic CycleIndexPolynomial(G::GrpPerm : Ring := 0) -> RngMPolElt
{The cycle index polynomial of the permutation group G}
    cl := Classes(G);
    cyc_str := [<c[2], CycleStructure(c[3])>: c in cl];
    rank := Max([t[2, 1, 1] : t in cyc_str]);
    if Type(Ring) eq RngMPol and Rank(Ring) ge rank then
        P := Ring;
	require IsInvertible(P!(#G)):"Group order not invertible in given ring";
        x := [P.i: i in [1..rank]];
    elif Type(Ring) eq RngIntElt and Ring ge rank then
	P<[x]> := PolynomialRing(Rationals(), Ring);
    else
        P<[x]> := PolynomialRing(Rationals(), rank);
    end if;
    res := &+[pr[1] * &*[x[t[1]]^t[2]: t in pr[2]] : pr in cyc_str];
    res /:= #G;
    return res;
end intrinsic;

intrinsic OrbitPartitionStabilizer(G::GrpPerm, H::GrpPerm) -> GrpPerm
{The stabilizer  in G of the ordered partition induced by the orbits of H}

    require Generic(G) eq Generic(H): "Permutation groups must be compatible";
    O := Orbits(H);
    OL := { #o : o in O };
    if #OL eq 1 then return G; end if;
    P := [];
    for l in OL do
	Append(~P, &join{ Set(o) : o in O | #o eq l});
    end for;
    S := Stabiliser(G, P : Subgroup := H);
    return S;
end intrinsic;

intrinsic OrbitPartitionIsConjugate(G::GrpPerm, H::GrpPerm, K::GrpPerm) ->
BoolElt, GrpPermElt, GrpPerm, GrpPerm
{Preprocessor for IsConjugate(G,H,K)}
    require Generic(G) eq Generic(H): "Permutation groups must be compatible";
    require Generic(G) eq Generic(K): "Permutation groups must be compatible";
  OH := Orbits(H);
  OK := Orbits(K);
  OL := {* #o : o in OH *};
  if OL ne {* #o : o in OK *} then return false, _,_,_; end if;
  OL := MultisetToSet(OL);
  if #OL eq 1 then
    return true, Id(G), H, G;
  end if;
  PH := [];
  PK := [];
  for l in OL do
    Append(~PH, &join{ Set(o) : o in OH | #o eq l});
    Append(~PK, &join{ Set(o) : o in OK | #o eq l});
  end for;

  if H subset G and K subset G then
      isc, g := IsConjugate(G,PH,PK:LeftSubgroup := H, RightSubgroup := K);
  else
      isc, g := IsConjugate(G,PH,PK);
  end if; 
  if not isc then return false, _, _, _; end if;
  // Stabiliser tests are much quicker than conjugacy tests!
  if K subset G then
      NPK := Stabiliser(G,PK: Subgroup := K);
  else
      NPK := Stabiliser(G,PK);
  end if;
  Hg := H^g;
  return true, g, Hg, NPK;
end intrinsic;

intrinsic SolubleNormalQuotient(G::GrpPerm, R::GrpPerm) -> GrpPerm, Map, GrpPerm
{R is a soluble normal subgroup of G. Compute a quotient G/S, where
S is soluble and contains R}

    require R subset G and IsNormal(G,R):
	"second argument must be normal subgroup of first";
    if IsTrivial(R) then
	return G, hom<G->G|[G.i:i in [1..Ngens(G)]]>, R;
    end if;
    ds := DerivedSeries(R);
    require IsTrivial(ds[#ds]):"second argument must be soluble";
    if G eq R then 
	return H, hom<G->H|[H.0:i in [1..Ngens(G)]]>, G
		where H := sub<G|[G!1:i in [1..Ngens(G)]]>; 
    end if;
    Q, f := AbelianNormalQuotient(G, ds[#ds-1]);
    i := #ds - 2;
    while i gt 0 do
	A := ds[i]@f;
	i -:= 1;
	if IsTrivial(A) then continue; end if;
	Q, f2 := AbelianNormalQuotient(Q, A);
	f := hom<G->Q|[G.i@f@f2: i in [1..Ngens(G)]]>;
    end while;
    return Q, f, Kernel(f);
end intrinsic;

intrinsic FewGenerators(G::GrpPerm:Try := 1) -> []
  {Tries to find a small generating set for G.}
  q := AbelianQuotient(G);
  n := Ngens(q);
  if #G eq 1 then
    return [G.0];
  end if;
  if n+1 ge Ngens(G) then
    return GeneratorsSequence(G);
  end if;
  n_opt := Infinity();
  for j in [1..Try] do
    for i in [1..Degree(G)] do
      s := [Random(G) : x in [1..n+1]];
      s := [x : x in s | x ne G.0];
      if sub<G|s> eq G then
        if #s lt n_opt then
          if #s eq #q then
            return s;
          end if;
          n_opt := #s;
          g_opt := s;
        end if;
      end if;
    end for;
  end for;
  if n_opt lt Ngens(G) then
    return g_opt;
  end if;
  return GeneratorsSequence(G);
end intrinsic;

intrinsic FewGenerators(G::GrpMat:Try := 1) -> []
{"} // "
  return GeneratorsSequence(G);
end intrinsic;

intrinsic YoungSubgroup(P::SeqEnum[RngIntElt]: Full := false) -> GrpPerm
{The direct product of the groups Sym(P_i), where P = [P_1, P_2, ..]}
  if Full cmpeq false then
    return x where x := DirectProduct([Sym(x) : x in P]);
  else
    n := &+ P;
    require Full ge n: "Output degree is too small";
    x := DirectProduct([Sym(x) : x in P]);
    x := Sym(Full)!!x;
    return x;
  end if;
end intrinsic;

intrinsic pCoreQuotient(G::GrpPerm, p::RngIntElt) -> GrpPerm, Map, GrpPerm
{The quotient of G by pCore(G, p), also the quotient map and the p-core}
    require IsPrime(p): "2nd argument must be prime";
    K := pCore(G, p);
    if IsTrivial(K) then
	return G, hom<G->G|[G.i: i in [1..Ngens(G)]]>, K;
    end if;
    Q, f := SolubleNormalQuotient(G, K);
    assert #Q*#K eq #G;
    return Q, f, K;
end intrinsic;

intrinsic CycleSeqToElt(G :: GrpPerm, s :: SeqEnum[SeqEnum[RngIntElt]]) -> GrpPermElt
{Construct the permutation element representated by the given sequence of cycles.}
    n := Degree(G);
    perm := [ i : i in [1..n] ];
    for cycle in s do
        error if Max(cycle) gt n or Min(cycle) le 0, "Cycle elements must be between 1 and", n;
        for ci in [1..#cycle-1] do
            perm[cycle[ci]] := cycle[ci+1];
        end for;
        perm[cycle[#cycle]] := cycle[1];
    end for;
    return G!perm;
end intrinsic;

intrinsic DoubleCosetCanonical(G :: GrpPerm, H :: GrpPerm, g :: GrpPermElt,
K :: GrpPerm : B := 0, M := 0) -> SeqEnum, SeqEnum
{A canonical base image for the double coset HgK in G. The desired base
may be supplied as parameter B, and M may be set as a subgroup of
H meet K^(g^-1). The return values are the canonical base image,
and the base used.}
    if B cmpeq 0 then
	BB := [];
	S := H;
	while #S gt 1 do
	    O := OrbitRepresentatives(S);
	    fl := exists(t){t : t in O | t[1] gt 1};
	    assert fl;
	    Append(~BB, t[2]);
	    S := Stabilizer(S, t[2]);
	end while;
	S := Stabilizer(G, BB);
	while #S gt 1 do
	    O := OrbitRepresentatives(S);
	    fl := exists(t){t : t in O | t[1] gt 1};
	    assert fl;
	    Append(~BB, t[2]);
	    S := Stabilizer(S, t[2]);
	end while;
    else
	BB := B;
    end if;

    if M cmpeq 0 then
	MM := H meet K^(g^-1);
    elif M cmpeq false then
	MM := sub<H|>;
    else
	MM := M;
    end if;
    C := DoubleCosetMinimum(G, H, g, K, BB, MM);
    return C, BB;
end intrinsic;

intrinsic RandomClasses(G::GrpPerm, w::RngIntElt, s::RngIntElt, t::RngIntElt, p::BoolElt, Q::SeqEnum[Tup]) -> BoolElt
{}
    Q1 := [t : t in Q | t[1] eq 1];
    require #Q1 eq 1 and Q1[1,2] eq 1: "Must contain identity class";
    b := Q1[1,3];
    BSGS(G);
    R := Representation(G);
    R := RandomBaseChange(R, b);
    Q1 := [ <t[1], t[2], Permutation(R, t[3])> : t in Q];
    return RandomClassesInternal(G, w, s, t, p, Q1);
end intrinsic;
