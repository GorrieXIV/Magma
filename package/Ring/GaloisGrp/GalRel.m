freeze;
//

import "Galois.m" : GenericStauduhar;

declare attributes RngInt: GalBlock;
declare attributes SetEnum: CompData;
CompData_fmt := recformat<M:Map,
                          R:Any,
                          prec : RngIntElt,
                          coeff : SetEnum  
                         >;

intrinsic InternalEasyCompletionsCreate(K::FldAlg, s::SetEnum) -> []
  {}
  
  r := s`CompData;
  M := r`M;
  F := Codomain(M);  
  f := DefiningPolynomial(K);
  if Type(f) cmpeq RngUPolElt then
    R := Roots(Polynomial([M(CoefficientField(K)!x) : x in Eltseq(f)]));
    Sort(~R, func<a,b|Hash(ChangePrecision(a[1], 2))-Hash(ChangePrecision(b[1], 2))>);
//"InternalEasyCompletionsCreate";
//F;
//ResidueClassField(F);
//Roots(Polynomial(ResidueClassField(F), Polynomial([M(x) : x in Eltseq(f)])));
    assert forall(x){x : x in R | x[2] eq 1};
//    assert #R eq Degree(f);
    R := [x[1] : x in R];
//Universe(R);
    M := R;
  else
    R := [ Roots(Polynomial([M(CoefficientField(K)!x) : x in Eltseq(y)])) : y in f];
    //R := [Sort(x, func<a,b|Hash(a)-Hash(b)>): x in R];
    if GetAssertions() ge 1 then
      for r in [1..#f] do
        assert forall(x){x : x in R[r] | x[2] eq 1};
//        assert #R[r] eq Degree(f[r]);
      end for;
    end if;
    R := [ [ x[1] : x in y] : y in R];
    M := [[y : y in x] : x in CartesianProduct(R)];
  end if;
  M := [ rec<CompData_fmt| M := hom<K -> F| r`M, x>, 
                           R := x, prec := F`DefaultPrecision,
           coeff := s> : x in M];
  S := [];
  for i in M do
    s := {1};
    s`CompData := i;
    Append(~S, s);
  end for;
  return S;
end intrinsic;

intrinsic InternalEasyCompletionsCreate(K::FldAlg, F::RngPad: OneOnly := false) -> []
  {}

  if BaseField(K) cmpeq Rationals() then
    r := {1};
    r`CompData := rec<CompData_fmt | M := map<Rationals() -> F | x :-> F!x>>;
    
    return InternalEasyCompletionsCreate(K, r);
  elif OneOnly then
    return InternalEasyCompletionsCreate(K, 
               InternalEasyCompletionsCreate(BaseField(K), F:OneOnly)[1]);
  else
    return &cat [ InternalEasyCompletionsCreate(K, r) : 
       r in InternalEasyCompletionsCreate(BaseField(K), F)];
  end if;
end intrinsic;
  

intrinsic InternalEasyCompletionsUse(x::FldAlgElt, S::SetEnum, P::RngIntElt) -> RngPadElt
  {}

    //problem being that F!(1/p) will give 0
  if Denominator(x) ne 1 then
    d := Denominator(x);
    dF := InternalEasyCompletionsUse(Parent(x)!d, S, P);
    if IsWeaklyZero(dF) then
      return 0;
    end if;
    return InternalEasyCompletionsUse(x*d, S, P)/dF;
  end if;
  if S`CompData`prec ge P then
    y := S`CompData`M(x);
    return ChangePrecision(y, P);
  end if;
  K := Parent(x);
  f := DefiningPolynomial(K);
  F := Codomain(S`CompData`M);
  F`DefaultPrecision := Maximum(P, F`DefaultPrecision);;
  if BaseField(K) cmpeq Rationals() then
    coerce := func<z|F!z>;
  else
    coerce := func<z|F!InternalEasyCompletionsUse(z, S`CompData`coeff, P)>;
  end if;

  if Type(f) cmpeq RngUPolElt then
    S`CompData`R := HenselLift(Polynomial([coerce(BaseField(K)!z) :
                   z in Eltseq(f)]), S`CompData`R, P);
  else
    S`CompData`R := [ 
      HenselLift(Polynomial([coerce(BaseField(K)!z) :
                   z in Eltseq(f[i])]), S`CompData`R[i], P) : i in [1..#f]];
  end if;
  S`CompData`M := hom<K -> F| 
      map<CoefficientRing(K) -> F| x:-> S`CompData`coeff`CompData`M(x)>,
      S`CompData`R>;
  S`CompData`prec := P;
  y := S`CompData`M(x);
  return ChangePrecision(y, P);
end intrinsic;


intrinsic AbsoluteGaloisGroup(A::FldAb:Prime := false, 
          ShortOK := false) 
                       -> GrpPerm, [], GaloisData
  {The Galois group over Q of the abelian extension.}

  K := NumberField(A);
  k := BaseField(K);
  Q := BaseField(k);
  BeClever := true;

  function local_degree(p:CheckSize := false)
    if Discriminant(BaseRing(A)) mod p eq 0 then
      return false;
    end if;
    P := Decomposition(BaseRing(A), p);
    if CheckSize and 
       exists(x){x : x in P | Degree(x[1]) gt Maximum(Degree(k) div 3, 1)} then
      return false;
    end if;
    l := 1;
    for p in P do
      d := DecompositionType(A, p[1]);
      if CheckSize and exists(x){x : x in d | x[2] gt 1} then
        return false;
      end if;
      l := Lcm(l, Degree(p[1])*Lcm([x[1] : x in d]));
    end for;
    return l;
  end function;

  if Prime cmpne false then
    p := Prime;
    l := local_degree(p);
  else
    p := AbsoluteDegree(A);
    lp := [];
    repeat
      vprint GaloisGroup, 2: "Trying prime", p;
      p := NextPrime(p);
      l := local_degree(p:CheckSize);
      if l cmpne false then
        Append(~lp, <p, l>);
      end if;
    until #lp gt 20;
    M, pos := Maximum([x[2] : x in lp]);
    l := 3;
    u := 10;
    if exists(x){x : x in lp | x[2] in [l..u]} then
      p := x[1];
      l := x[2];
    else
      _, pos := Minimum([x[2] : x in lp]);
      p := lp[pos][1];
      l := lp[pos][2];
    end if;
  end if;

  S := InternalGaloisDataCreate(p);
  S`Base := pAdicRing(p);
  S`Type := "p-Adic";

  vprint GaloisGroup, 1:
    "Using prime", p, "to get unram. ext. of degree", l;
  S`Ring := UnramifiedExtension(S`Base, l);


  RootData := InternalEasyCompletionsCreate(k, S`Ring);
  assert #RootData eq AbsoluteDegree(k);

  S`Roots := [ InternalEasyCompletionsUse(k.1, x, 20) : x in RootData];
  Gk, rk, Sk := GaloisGroup(k:Ring := S);

  S`Ring`DefaultPrecision := 20;

  if assigned S`Permutation then
    RootData := PermuteSequence(RootData, S`Permutation);
    delete S`Permutation;
  end if;
  delete S`f;
  delete S`Subfields;
  delete S`DescentChain;
  delete S`KnownSubgroup;


  S`RootData := [ InternalEasyCompletionsCreate(K, x) : x in RootData];
  assert &+ [ #x : x in S`RootData] eq AbsoluteDegree(A);

  pe := 2*&+ [ x : x in Generators(K)];
  pk := 2*k.1;
  while #Set([InternalEasyCompletionsUse(pe+pk, h, 1) 
                            : h in &cat S`RootData]) ne AbsoluteDegree(A) do
    pe := &+ [ Random(4)*x : x in Generators(K)];
    pk := Random(4)*k.1;
  end while;


  a, _, ma := AutomorphismGroup(A);
  //TODO:
  // - compute the AutomorphismGroup(A:Gen) that will only compute 
  //   generators, not everything (thus should be faster)
  // - then build the map ma and such in the p-adic ring to avoid
  //   dealing with large integers (and large degree fields)
  mpa, pa := CosetAction(a, sub<a|>);

  if BeClever then
    W, m1W, m2W, m3W := WreathProduct(pa, Gk);
    assert IsTransitive(W);

    // we assume that m1W[1] acts on [1..Degree(A)],
    //                m1W[2]         [Degree(A)+1 .. 2*Degree(A)] ...
    //It seems to be correct...                

    rd := [];
    S`Roots := [];
    for i in [1..#RootData] do
      rr := [ InternalEasyCompletionsUse(pe+pk, h, 1) : h in S`RootData[i]];

      if GetAssertions() ge 1 then
        rs := [ InternalEasyCompletionsUse((x@@mpa@ma)(pe+pk), 
                       S`RootData[i][1], 1) : x in pa];
        assert Set(rr) eq Set(rs);
      end if;
      assert Degree(A) eq #Set(rr);

      r := [pe+pk];
      offset := (i-1)*Degree(A);
      rp := [1];
      repeat
        s := { x+offset : x in [1..Degree(A)] | IsDefined(r, x)};
        if #s eq Degree(A) then
          break;
        end if;
        g := Random(Generators(Image(m1W[i])));
        if s^g ne s then
          m := s^g diff s;
          for j in m do
            r[j-offset] := (g@@m1W[i]@@mpa@ma)(r[j^g^-1 - offset]);
            rp[j-offset] := Position(rr, 
                 InternalEasyCompletionsUse(r[j-offset], S`RootData[i][1], 1));        
          end for;          
        end if;
      until false;
      Append(~rd, [S`RootData[i][x] : x in rp]);
    end for;
    S`RootData := &cat rd;
  else
    W, m1W, m2W, m3W := WreathProduct(Sym(Degree(pa)), Gk);
    assert IsTransitive(W);
    S`RootData := &cat S`RootData;
  end if;

  S`Roots := [ InternalEasyCompletionsUse(pe+pk, h, 20) : h in S`RootData];

  assert #Set(S`Roots) eq AbsoluteDegree(A);

  procedure GetRoots(SS:Prec := 20)
    if Precision(Representative(SS`Roots)) ge Prec then
      return;
    end if;
    SS`Roots := [ InternalEasyCompletionsUse(pe+pk, h, Prec) :
                                                          h in SS`RootData];
  end procedure;

  S`GetRoots := GetRoots;
  S`DescentChain := [];

  inf := InfinitePlaces(K);
  assert #inf le AbsoluteDegree(K);
  max_comp := Ceiling(Maximum([Abs(Evaluate(pe+pk, x)) : x in inf]));
  S`max_comp := max_comp;

  return GenericStauduhar(W, S, max_comp,
                          func<x|[y`subgroup : 
                                   y in MaximalSubgroups(x:IsTransitive)]>, 
                          func<x|true>:
                          ShortOK := ShortOK, Subfields := false);
end intrinsic;

    





