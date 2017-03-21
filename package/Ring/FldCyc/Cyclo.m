freeze;
//
/*
 <example>
   G := PCGroup(WreathProduct(DihedralGroup(3), CyclicGroup(5)));
   Reps := AbsolutelyIrreducibleRepresentationsSchur(G, Q);
   R := Reps[54];
   s := TheLot(R);
 </example>
*/

// For compatibility.......//
intrinsic MinimalField(a::FldRatElt) -> Rng
  {Obsolete: use MinimalCyclotomicField instead.}
  return Rationals();
end intrinsic;

intrinsic MinimalField(a::FldCycElt) -> Rng
  {Obsolete: use MinimalCyclotomicField instead.}
  return MinimalCyclotomicField(a);
end intrinsic;

intrinsic MinimalField(a::RngCycElt) -> Rng
  {Obsolete: use MinimalCyclotomicField instead.}
  return MinimalCyclotomicField(a);
end intrinsic;

intrinsic MinimalField(S::[FldRatElt]) -> Rng
  {Obsolete: use MinimalCyclotomicField instead.}
  return MinimalCyclotomicField(S);
end intrinsic;

intrinsic MinimalField(S::[FldCycElt]) -> Rng
  {Obsolete: use MinimalCyclotomicField instead.}
  return MinimalCyclotomicField(S);
end intrinsic;

intrinsic MinimalField(S::[RngCycElt]) -> Rng
  {Obsolete: use MinimalCyclotomicField instead.}
  return MinimalCyclotomicField(S);
end intrinsic;

/////////////////////////////////////////////////////////////

function CycloToGroup(K)
  ZZ := MaximalOrder(Polynomial([-1,1]));
  A, mA := RayClassGroup(Conductor(K)*ZZ, [1]);
  return A, mA;
end function;

intrinsic DirectProduct(Q :: [GrpAb]) -> GrpAb, [], []
  {The direct product of the sequence of groups Q and inclusion/projection maps.}
  QQ := [InvariantRepresentation(x) : x in Q];
  inv := &cat [ AbelianInvariants(i) : i in QQ];
  G := AbelianGroup(inv);
  lI := [];
  lP := [];
  lI := [Coercion(Q[i], QQ[i])*hom<QQ[i] -> G | [ G.(j+l) : l in [1..Ngens(QQ[i])]]> where
    j := &+ [Integers()|Ngens(QQ[l]): l in [1..i-1]] : i in [1..#QQ]];
  lP := [hom<G -> QQ[i] | [QQ[i].0 : l in [1..j]] cat
                         [QQ[i].l : l in [1..Ngens(QQ[i])]] cat
                         [QQ[i].0 : l in [j+Ngens(QQ[i])+1..#inv]]> *
                           Coercion(QQ[i], Q[i])
     where j := &+ [Integers()|Ngens(QQ[l]): l in [1..i-1]] : i in [1..#QQ]];
  
  return G, lI, lP;
end intrinsic;

declare attributes FldCyc : AutGroup;

intrinsic CyclotomicAutomorphismGroup(K::FldCyc) -> GrpAb, Map
  {The automorphism group of the cyclotomic field K as an abelian group.}
  if assigned K`AutGroup then
    A := K`AutGroup;
    return A[1], A[2];
  end if;
  if Conductor(K) eq 1 then
    mG := map<AbelianGroup(G) -> Maps(K,K) | x :-> hom<K ->K | K.1>> where G := AbelianGroup([1]);
    G := Domain(mG);
    K`AutGroup := <G, mG>;
    return G, mG;
  end if;

  A := CycloToGroup(K);
  if IsSimple(K) then
    G, _, mG := InternalAutomorphismGroup(K:Abelian);
    G, mmG := AbelianGroup(G);
    mG := Inverse(mmG)*mG;
//    mmG, G := CosetAction(G, sub<G|>);
//    mG := Inverse(mmG)*mG;
  else
    lG := [];
    lmG := [**];
    lF := Factorization(CyclotomicOrder(K));
    if #lF eq 0 then// we are dealing with Q here
      return G, map<G -> Maps(K,K) | x :-> hom<K ->K | K.1>> where G := AbelianGroup([1]);
    end if;
    // here's the dirty bit:
    //   we rely on the generators K.i to be of exact order lF[i][1]^lF[i]^2
    // could be extended to arbitrary non-simple fields by combining
    // the automorphism groups of the components. But why bother?
    for i in [1..Ngens(K)] do
      m := lF[i][1]^lF[i][2];
      assert K.i^m eq 1;
      G, mG := UnitGroup(Integers(m));
      mG := map<G -> Maps(K, K) |
              g :-> hom<K -> K |
                  [K.j : j in [1..i-1]] cat
                    [K.i^(Integers()!mG(g))] cat
                  [K.j : j in [i+1..Ngens(K)]]>
                       >;
      Append(~lG, G);
      Append(~lmG, mG);
    end for;                   

    G, _, mD := DirectProduct(lG);
    mG := hom<G -> Maps(K, K) |
      g :-> &* [mD[i](g) @ lmG[i] : i in [1..#lG]]>;
  end if;
  K`AutGroup := <G, mG>;
  return G, mG;
end intrinsic;

intrinsic CyclotomicRelativeField(k::FldCyc, K::FldCyc) -> FldNum
  {Realized the larger field as an extension of the smaller.}
  m := Conductor(K);
  n := Conductor(k);
  require m mod n eq 0: "The 1st argument must be a subfield of the 2nd!";
  if n eq m then
    return K;
  end if;

  if IsSimple(k) and IsSimple(K) then 
    return RelativeField(k, K);
  end if;

  if IsSimple(K) then
    f := Factorization(Polynomial(k, DefiningPolynomial(K)));
    Kr := NumberField(f[1][1]);
    Embed(K, Kr, Kr.1);
    Embed(Kr, K, K.1);
    Embed(k, K, [K!k.i : i in [1..Ngens(k)]]);
  end if;

  // the interesting case!
  lf := DefiningPolynomial(K);
  lm := Factorization(m);
  ln := Factorization(n);

  // we MUST have that the ordering of this two lists coincide!!

  lp := [];
  image_K_Kr := [];
  image_Kr_K := [];
  for i in [1..#lm] do
    assert EulerPhi(lm[i][1]^lm[i][2]) eq Degree(lf[i]);
    v := Valuation(n, lm[i][1]);
    if v ne lm[i][2] then
      if v eq 0 then
        Append(~lp, Polynomial(k, CyclotomicPolynomial(lm[i][1]^lm[i][2])));
      else
        j := Position([x[1] : x in ln], lm[i][1]);
        Append(~lp, Polynomial(k, [0,1])^(lm[i][1]^(lm[i][2] - v)) - k.j);
      end if;
    end if;
  end for;
  Kr := NumberField(lp:Abs, Check := false);

  j := 1;
  for i in [1..#lm] do
    assert EulerPhi(lm[i][1]^lm[i][2]) eq Degree(lf[i]);
    v := Valuation(n, lm[i][1]);
    if v ne lm[i][2] then
      Append(~image_Kr_K, K.i);
      Append(~image_K_Kr, Kr.j);
      j +:= 1;
    end if;
  end for;
  
  Embed(K, Kr, image_K_Kr);
  Embed(Kr, K, image_Kr_K);
  if IsSimple(k) then
    Embed(k, K, [K!k.i : i in [1..Ngens(k)]]);
  else
    Embed(k, K, K!k.1);
  end if;


  return Kr;
end intrinsic;

