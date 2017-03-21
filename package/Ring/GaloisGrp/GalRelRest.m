freeze;


import "Galois.m" : GenericStauduhar, GaloisStartingGroup, TestShapes, 
                    color_array, galois_data_copy_for_factor, invar_coeff_ring, intr_subfields;

import "Shapes.m" : IsSnAn;

red := color_array[1];
green := color_array[2];
RED := color_array[3];
blue := color_array[4];
purple := color_array[5];
BLUE := color_array[6];
grey := color_array[7];
normal := color_array[8];

Debug := not true;

declare attributes GaloisData : IsInt, GetPrec, RecoData, BaseMap, CycleTypes;
declare verbose GaloisTower, 3;

function RealBasis(R)
  b := Basis(R, R);
  c := [ Conjugates(x) : x in b];
  r1, r2 := Signature(R);
  m := [];
  for i in [1..#b] do
    n := [];
    for j in [1..r1] do
      Append(~n, Re(c[i][j]));
    end for;
    for j := r1+1 to r1+2*r2 by 2 do
      Append(~n, Re(c[i][j]));
      Append(~n, Im(c[i][j]));
    end for;
    Append(~m, n);
  end for;
  return Matrix(m);
end function;

_np := NextPrime;
/*
 * CF: to aid parting GaloisSubfieldTower and the like to Q(t) case.
 * Not complete and does not work (yet)
 *
intrinsic Norm(x::RngUPolElt, Z::RngUPol) -> RngUPolElt
  {}
  return x;
end intrinsic;
intrinsic Ceiling(r::RngSerPowElt[FldRe]) -> RngSerPowElt
  {}
  R := PowerSeriesRing(Integers(), Parent(r)`DefaultPrecision);
  a,b := Eltseq(r);
  return elt<R|b, [Ceiling(x) : x in a]>;
end intrinsic;

intrinsic Maximum(r::RngSerPowElt[RngInt], s::RngSerPowElt[RngInt]) -> RngSerPowElt
  {}
  R := Parent(r);
  a,b := Eltseq(r);
  x,y := Eltseq(s);
  v := Minimum(b, y);
  u := [];
  for i:= v to Maximum(#a+b-1, #x+y-1) do
    if i-b le 0 or i-b ge #a then
      Append(~u, x[i-y+1]);
    elif i-y le 0 or i-y ge #x then
      Append(~u, a[i-b+1]);
    else
      Append(~u, Maximum(a[i-b+1], x[i-y+1]));
    end if;
  end for;
  return elt<R|v, u>;
end intrinsic;
intrinsic Minimum(r::RngSerPowElt[RngInt], s::RngSerPowElt[RngInt]) -> RngSerPowElt
  {}
  R := Parent(r);
  a,b := Eltseq(r);
  x,y := Eltseq(s);
  v := Minimum(b, y);
  u := [];
  for i:= v to Maximum(#a+b-1, #x+y-1) do
    if i-b le 0 or i-b ge #a then
      Append(~u, x[i-y+1]);
    elif i-y le 0 or i-y ge #x then
      Append(~u, a[i-b+1]);
    else
      Append(~u, Minimum(a[i-b+1], x[i-y+1]));
    end if;
  end for;
  return elt<R|v, u>;
end intrinsic;
intrinsic Minimum(a::RngSerPowElt[RngInt], b::Infty) -> .
  {}
  return a;
end intrinsic;
intrinsic Ilog(a::RngUPolElt, b::RngSerPowElt) -> RngIntElt
  {}
  x,y := Eltseq(b);
  return Ceiling((#x+y)/Degree(a));
end intrinsic;


intrinsic 'gt'(a::RngSerPowElt[RngInt], b::Infty) -> BoolElt
  {}
  return false;
end intrinsic;
*/

/*
intrinsic GaloisGroup(f::RngUPolElt[FldAlg[FldRat]]: Ring := false, 
          Type := "p-Adic", Prime := false, 
          ShortOK := false, Subfields := true)
            -> Grp, [], GaloisData
  {}
  d := Lcm([Denominator(x) : x in Eltseq(f)]);
  return GaloisGroup(NumberField(f*d:DoLinearExtension) :
    Ring := Ring, Prime := Prime,
    ShortOK := ShortOK, Subfields := Subfields,
      NextPrime := _np);
end intrinsic;

intrinsic GaloisGroup(f::RngUPolElt[RngOrd]: Ring := false, 
          Type := "p-Adic", Prime := false, 
          ShortOK := false, Subfields := true)
            -> Grp, [], GaloisData
  {}
  d := Lcm([Denominator(x) : x in Eltseq(f)]);
  return GaloisGroup(NumberField(f*d:DoLinearExtension) :
    Ring := Ring, Prime := Prime,
    ShortOK := ShortOK, Subfields := Subfields,
      NextPrime := _np);
end intrinsic;
*/

// Subfields := true means that we check the subfield discriminants are coprime to p
function GetGaloisData(K : Subfields := false, Prime := false, NextPrime := _np, Ring := false)
  k := BaseField(K);
  Z_k := MaximalOrder(k);
  Q := BaseField(k);

  assert Type(Q) eq FldRat; 

  if (Prime cmpeq false) and Subfields then
   sf := intr_subfields(K);
   sf_polys := [Polynomial(k, DefiningPolynomial(a[1])) : a in sf | Degree(a[1]) lt Degree(K)];
  else
   sf_polys := []; 
  end if;

  lc := Lcm([Denominator(x) : x in Eltseq(f/LeadingCoefficient(f))]) where
        f := Polynomial(k, DefiningPolynomial(K));
  function local_degree(p)
    if Valuation(Discriminant(k), p) ne 0 then
      return false, {};
    end if;
    if lc mod p eq 0 then
      return false, {};
    end if;
    P := Decomposition(Z_k, p);
    if Prime cmpeq false and 
      forall(x){x : x in P | Degree(x[1]) gt Maximum(Degree(k) div 3, 1)} then
      return false, {};
    end if;
    l := [];
    s := {};
    for p in P do
      F, mF := ResidueClassField(p[1]);
      for sfp in sf_polys do
        d := Factorisation(Polynomial([mF(x) :
                            x in Eltseq(sfp)]));
        if exists(x){x : x in d | x[2] gt 1} then
// "Skip Prime ",Norm(p[1])," because of subfield discriminants";
          return false, s;
        end if;
      end for;    
      d := Factorisation(Polynomial([mF(k!x) :
                           x in Eltseq(DefiningPolynomial(K))]));
      if exists(x){x : x in d | x[2] gt 1} then
        return false, s;
      end if;
      Append(~l, <p[1], Lcm([Degree(x[1]) : x in d])>);
      Include(~s, [Degree(x[1]) : x in d]);
    end for;
    return l, s;
  end function;

  if Ring cmpne false then
    S := Ring;
    P := S`Prime;
    p := Minimum(P);
    l := Degree(P);
    sp := {};
  else
    if Prime cmpne false then
      p := Prime;
      l, sp := local_degree(Minimum(p));
      l := l[Position([x[1] : x in l], p)];
      l := l[2];
    else
      p := AbsoluteDegree(K)*1;
      lp := [];
      sp := {};
      repeat
        p := NextPrime(p);
        l, s := local_degree(p);
        if l cmpne false then
          lp cat:= l;
        end if;
        sp join:= s;
      until #lp gt Maximum(2*Degree(K), 20);
      M, pos := Maximum([x[2] : x in lp]);
      l := 3;//CF: TODO not good criteria!!!
      u := 4;// it used to be u := 10 which is also bad.
      if exists(x){x : x in lp | x[2] in [l..u]} then
        p := x[1];
        l := x[2];
      elif exists(x){x : x in lp | x[2] in [2..l]} then
        p := x[1];
        l := x[2];
      else
        _, pos := Minimum([x[2] : x in lp]);
        p := lp[pos][1];
        l := lp[pos][2];
      end if;
    end if;

    l *:= Degree(p);
   
    P := p;
    p := Minimum(p);
  //  "Using prime", P, "of degree", Degree(P);
    S := InternalGaloisDataCreate(P);
    S`Base := UnramifiedExtension(pAdicRing(p), Degree(P)); 
    S`Type := "p-Adic (rel)";
    S`CycleTypes := sp;
    S`Ring := UnramifiedExtension(S`Base, l div Degree(P));

  end if;

  vprint GaloisGroup, 1:
    "Using prime", p, "to get unram. ext. of degree", l;

  vprint GaloisGroup, 2: "computing p-adic embeddings for the base field";
  vtime GaloisGroup, 2: R := InternalEasyCompletionsCreate(k, S`Ring);
  _, pi := TwoElementNormal(P);
  if not exists(x)
     { x : x in R | Valuation(InternalEasyCompletionsUse(k!pi, x, 2)) eq 1} then
    error "Completion not found";
  end if;
  Base := x;
//Base;
//Position(R, Base);
  S`BaseMap := func<x, pr| InternalEasyCompletionsUse(k!x, Base, pr)> ;
//pi;
//S`BaseMap(pi, 20);
//S`BaseMap(k.1, 20);

  S`DescentChain := [];

  vprint GaloisGroup, 2: "computing p-adic embeddings for the extension field";
  vtime GaloisGroup, 2: S`RootData := InternalEasyCompletionsCreate(K, Base);
  assert #S`RootData eq Degree(K);

  if assigned S`Roots then
    r := S`Roots;
    S`Roots := [ InternalEasyCompletionsUse(K.1, h, 20) : h in S`RootData];
    vprint GaloisGroup, 2: "Sorting roots...";
    for i:= 1 to #r do
      j := Position([Valuation(r[i] - x) ge Minimum(Precision(r[i]), 20) : x in S`Roots], true);
      assert j ne 0;
      a := S`Roots[i];
      S`Roots[i] := S`Roots[j];
      S`Roots[j] := a;

      a := S`RootData[i];
      S`RootData[i] := S`RootData[j];
      S`RootData[j] := a;
    end for;
    assert forall{x : x in [1..#r] | 
                           Valuation(r[x]- S`Roots[x]) ge Precision(r[x])};
  else
    S`Roots := [ InternalEasyCompletionsUse(K.1, h, 20) : h in S`RootData];
  end if;
  assert #Set(S`Roots) eq Degree(K);

  l_k := Degree(P);
  S_k := CoefficientRing(S`Ring);

  procedure GetRoots(SS:Prec := 20)
    if Precision(Representative(SS`Roots)) ge Prec then
      return;
    end if;
    r := SS`Roots;
    SS`Roots := [ InternalEasyCompletionsUse(K.1, h, Prec) : h in SS`RootData];
    assert forall{x : x in [1..#r] | Valuation(r[x]- SS`Roots[x]) ge Precision(r[x])-2};
  end procedure;

  Z := Integers();
  function IsInt(x, B, SS:EasyNonInt := false)
//"GalRelRest IsInt";
    assert IsIdentical(SS, S);
    pr := AbsolutePrecision(x);
    if pr eq 0 then
      return true, 0;
    end if;
    f, c := IsCoercible(BaseRing(SS`Ring), x);
    if not f then
      vprint GaloisGroup, 3: "no int - ring error";
      return false, _;
    end if;
    if EasyNonInt then
      return true, 1;
    end if;

    if not assigned SS`RecoData then
      SS`RecoData := [];
    end if;
    if exists(y){x : x in SS`RecoData | x[1] eq pr} then
      vprint GaloisGroup, 3: "reuse reco data for precision", pr;
      R := y[2];
      I := y[3];
    else
      vprint GaloisGroup, 3: "compute reco data for precision", pr;
      R := ReconstructionEnvironment(P, pr);
      M := VerticalJoin(Matrix(Z, [Eltseq(
        BaseRing(SS`Ring)!SS`BaseMap(x, pr))
                 : x in Basis(Z_k, k)]), p^pr*IdentityMatrix(Z, l_k));
      f, I := IsConsistent(M, IdentityMatrix(Z, l_k));
      assert f;
      I := Submatrix(I, 1, 1, l_k, Degree(k));
      Zk := Z_k;
      kk := k;
      assert forall{x : x in [1..l_k] | 
        Valuation(SS`BaseMap(Z_k!Eltseq(I[x]), 10) 
              - BaseRing(SS`Ring)!Eltseq(IdentityMatrix(Z, l_k)[x])) gt 0};
      Append(~SS`RecoData, <pr, R, I>);
    end if;
    Pk := R`pk;
    c := Matrix(Z, [Eltseq(c)]) * I;
    c := Z_k!Eltseq(c);
    //pr := Ceiling(99*pr/100);
    assert IsWeaklyEqual(SS`BaseMap(c, pr), x);
    d := Reconstruct(c, R:UseDenominator := false);
    if Length(d) gt Degree(k)*B^2 then
      vprint GaloisGroup, 3: "no int - size error", 
                          Degree(k)*B^2, "<", Length(d), "= T_2(", d, ")";
//Degree(k)*B^2, "<", Length(d), "= T_2(", d, ")";
      return false, d;                    
    else                      
      vprintf GaloisGroup, 4:  "INT: %o (%o)\n", x, d;
    end if;  
//"return 3";
    return true, d;
  end function;

  RB := Transpose(RealBasis(Z_k));
  a,b := SpectralRadius(RB);
  r1, r2 := Signature(Z_k);
  W := [Sqrt(Norm(RB[i])) : i in [1..r1]] cat
       [(Norm(RB[i]) + Norm(RB[i+1])) : i in [r1+1..r1+2*r2 by 2]];
  n := Degree(Z_k);     
  W := (&*W);
       
  function GetPrec(B, SS) // based on KG, CF and Belabas
    //KG = Diss KG, CF: Fieker & Friedrichs ANTS IV 2000
    //Belbas: A relative van Hoij Algorithm over number fields, 3.10
    C := 1/b*B*Sqrt(n);
    pr := Ceiling(n*Log(C* 2 * 3^(n-1))/Log(Norm(p)));
    return pr;
    return 114*pr;
  end function;

  S`GetRoots := GetRoots;
  S`IsInt := IsInt;
  S`GetPrec := GetPrec;

  vprint GaloisGroup, 3: "Getting complex bounds...";
  vtime GaloisGroup, 3: S`max_comp :=
         Ceiling(Maximum([Abs(Evaluate(K.1, x)) : x in InfinitePlaces(K)]));

  R, mR := ResidueClassField(S`Ring);
  r := [ GaloisRoot(i, S: Prec := 1)@mR : i in [1..Degree(K)]];
  q := #ResidueClassField(CoefficientRing(S`Ring));
  if #Set(r) ne #r then
    pr := 2;
    q := func<x|GaloisImage(x, 1)>;
    repeat
      r := [GaloisRoot(i,S : Prec := pr) : i in [1..Degree(K)]];
      rt := [ q(x) : x in r];
      rt := [ChangePrecision(x, pr) : x in rt];                 
      p := [Position(rt, x) : x in r];
      pr *:= 2;
      if pr gt 100 then
        error "too much(3)";
      end if;
    until #Set(rt) eq #Set(p) and #Set(p) eq Degree(K);
  else
    rt := [ x^q : x in r];
    p := [ Position(rt, x) : x in r];
  end if;
  S`KnownSubgroup := sub<Sym(Degree(K))|p>; // TODO: use automorphisms

  vprint GaloisGroup, 2: "Frobenius permutation: ", S`KnownSubgroup.1;

  return S;
end function;

intrinsic GaloisGroup(K::FldNum[FldNum[FldRat]]: Prime := false, ShortOK, 
     Current := false, Ring := false, Subfields := true, Type,
     NextPrime := _np) -> GrpPerm, [], GaloisData
  {The Galois group of a number field represented as a simple relative extension}

  require IsSimple(K) :
    "The field must be a simple extension";

  S := GetGaloisData(K : Subfields := Subfields, Prime := Prime, NextPrime := NextPrime, Ring := Ring);
  if assigned S`Scale then
if not IsExport() then "Redefining scale!"; end if;
  end if;
  S`Scale := Lcm([Denominator(BaseField(K)!x) : x in Eltseq(f/LeadingCoefficient(f))])
             where f := DefiningPolynomial(K);       
  S`max_comp *:= S`Scale;    

  if Degree(K) eq 1 then
    S`DescentChain := [<Sym(1), true>];
    return Sym(1), S`Roots, S;
  end if;

  if assigned S`CycleTypes then
   tt := IsSnAn(S`CycleTypes);
   if tt gt 0 then
    vprint GaloisGroup, 1:"Shape test detects at least An";
    if tt eq 2 then
     g := Sym(Degree(K));
    else
     di := Discriminant(DefiningPolynomial(K));
     g := IsSquare(di) select Alt(Degree(K)) else Sym(Degree(K)); 
    end if;   
    S`DescentChain := [<g, true>];
    return g, S`Roots, S;
   end if;
  end if; 

  vprint GaloisGroup, 1: "Compute starting group: (relative case)";
  vprint GaloisGroup, 2: "==========================";
  G,reject,aut:=GaloisStartingGroup(K,S: Subfields := Subfields,
                                  Current := Current, ShortOK := ShortOK);
//"StartingGroup", G;
  S`DescentChain := [<G, true>];
  assert IsTransitive(G);
  if GetVerbose("GaloisGroup") ge 2 then 
   printf "Start with group of size %o", FactoredOrder(G);
   printf "%o\n", InternalPrintGroupIdentification(G);
   printf "==========================\n";
  end if;

  if assigned S`CycleTypes then
    sp := S`CycleTypes;
  else
    sp := {};
  end if;

// if Subfields are reliable, then the sieve function can be sharpened 
// as in the absolute case (using Current?)
  return GenericStauduhar(G, S, S`max_comp,
                          func<X|[x`subgroup : x in 
                                      MaximalSubgroups(X:IsTransitive)]>,
                          func<x|TestShapes(x, sp)>:
			  Subfields := Subfields,
                          ShortOK := ShortOK, SubfieldsComplete := false  );
end intrinsic;

intrinsic GaloisData(K::FldNum[FldNum[FldRat]]: Prime := false, 
     NextPrime := _np) -> GaloisData
  {The data structure for the Galois group computation for a number field represented as a simple relative extension}
 require IsSimple(K) :
    "The field must be a simple extension";

    return GetGaloisData(K : Subfields := false, Prime := Prime, NextPrime := NextPrime);
end intrinsic;

intrinsic GaloisGroup(K::FldNum: Prime := false, ShortOK, Type,
     Current := false, Ring := false, NextPrime := _np) -> GrpPerm, [], GaloisData
{The Galois group of a number field represented as a multiple relative extension}

    require IsSimple(K) : "The field must be a simple extension";
    A := AbsoluteField(CoefficientRing(K));
    KK := NumberField(Polynomial(A, DefiningPolynomial(K)));

    G, R, S := GaloisGroup(
    		KK : Prime := Prime, ShortOK := ShortOK, Current := Current, 
		Ring := Ring, NextPrime := NextPrime
	       );

    return G, R, S;
end intrinsic;

intrinsic InternalGaloisDataCreate(p::RngOrdIdl) -> GaloisData
{}
 S := New(MakeType("GaloisData"));
 S`Prime := p;
 return S;
end intrinsic;

intrinsic ConjugatesToPowerSums(c::[]) -> []
  {Given elements in c, compute the power sums, ie. &+ [x^j : x in c]}
  r := [&+c];
  d := c;
  for i := 2 to #c do
    c := [c[j]*d[j] : j in [1..#c]];
    Append(~r, &+c);
  end for;
  return r;
end intrinsic;

intrinsic ElementarySymmetricToPowerSums(c::[]:MaxDeg := 0) -> []
  {Given the elementary symmetric functions, compute the power sums}
  r := [Universe(c)|];
  if MaxDeg cmpeq 0 then MaxDeg := #c; end if;
  for k := 1 to MaxDeg do
    e := 0;
    for j := 1 to k-1 do
      if j le #c then
        e +:= (-1)^j*r[k-j]*c[j];
      end if;
    end for;
    e := (-e)-(-1)^k*k*(k le #c select c[k] else 0);
    Append(~r, e);
  end for;
  return r;
end intrinsic;

intrinsic PolynomialToElementarySymmetric(f::RngUPolElt) -> []
  {Given a polynomial, return the sequence of the elementatry symmetric functions}
  require IsMonic(f) : "The polynomial must be monic";  
  f := Eltseq(f);
  f := Reverse(f);
  f := [IsOdd(i) select f[i] else -f[i] : i in [1..#f]];
  return f[2..#f];
end intrinsic;

intrinsic PolynomialToPowerSums(f::RngUPolElt:MaxDeg := 0) -> []
  {Given a polynomial, return the sequence of power sums of the roots.}
  return ElementarySymmetricToPowerSums(PolynomialToElementarySymmetric(f):MaxDeg := MaxDeg);
end intrinsic;

    
intrinsic PowerSumToCoefficients(c::[]) -> []
  {Given power sums in c, use Newton's relations to obtain the coefficients of the corresponding polynomial.}
  a := [];
  n := #c;
  if n eq 0 then
    a := [Universe(c)|1];
    return a;
  end if;
  a[n+1] := Parent(c[1])!1;
  for i := 1 to n do
    t := 0;
    for j := 0 to i-1 do
      t +:= c[i-j]*a[n-j+1];
    end for;
    a[n-i+1] := -t/i;
  end for;
  return a;
end intrinsic;

intrinsic CoefficientsToElementarySymmetric(c::[RngElt]) -> []
  {Given an array of coefficients of a monic polynomial, transform into the array
    of elementary symmetric polynomials.}

  require c[#c] eq 1 : "Polynomial must be monic";    
  n := #c;    
  return [ IsOdd(i) select -c[n-i] else c[n-i] : i in [1..n-1]];    
end intrinsic;

intrinsic ElementarySymmetricToCoefficients(c::[RngElt]) -> []
  {Given an array containing the elementary symmetric polynomials evaluated at the roots, return the coefficients array}

  n := #c+1;    
  return [ IsEven(i) select -c[n-i] else c[n-i] : i in [1..n-1]] cat [1];    
end intrinsic;


intrinsic PowerSumToElementarySymmetric(c::[RngElt]) -> []
  {Given an array containing power sums, use Newton relations to compute the elementary symmetric polynomials}
  return CoefficientsToElementarySymmetric(PowerSumToCoefficients(c));
end intrinsic;

intrinsic '&*'(t::Tup) -> .
  {}
  g := t[1];
  require ISA(Type(g), GrpElt) or ISA(Type(g), RngElt) or ISA(Type(g), AlgElt) : "Tuple must contain group, ring or algebra elements";
  for i in [2..#t] do
    require ISA(Type(t[i]), GrpElt) or ISA(Type(t[i]), RngElt) or ISA(Type(t[i]), AlgElt) : "Tuple must contain group, ring or algebra elements";
    g := g*t[i];
  end for;
  return g;
end intrinsic;

intrinsic Norm(x::RngIntElt, Z::RngInt) -> RngIntElt
  {For compatibility}
  return x;
end intrinsic;

intrinsic Norm(x::FldRatElt, Z::RngInt) -> RngIntElt
  {"} // "
  return x;
end intrinsic;

intrinsic Conjugates(x::FldAlgElt[FldAlg] : Precision:=0) -> []
  {"} // "
  places := InfinitePlaces(Parent(x));
  if Precision gt 0 then
    return [Evaluate(x, p : Precision:=Precision) : p in places];
  else
    return [Evaluate(x, p) : p in places];
  end if;
end intrinsic;

_Bound := Bound;

intrinsic GaloisSubfieldTower(S::GaloisData, U::[GrpPerm]:
  Risk := false, MinBound := 1, 
  Inv := false, MaxBound := Infinity()) -> FldAlg, [], UserProgram, UserProgram
  {Given a descending chain if subgroups of the Galois group G, return the corresponding tower of fields}

  AlgRoots := false; // a debugging parameter, can be set to an algebraic
                     // representation of the roots in some splitting field.

  vprintf GaloisTower, 1: "GaloisSubfieldTower called with %o groups", #U;
  if Inv cmpne false then
    vprintf GaloisTower, 1: " and user given invariants";
    vprintf GaloisTower, 2: ": %o", Inv;
  end if;
  vprintf GaloisTower, 1: "\n";

  Bound := MinBound;
  
  G := S`DescentChain;
  G := G[#G][1];
  if G ne U[1] then
    U := [G] cat U;
    if Inv cmpne false then
      Inv := [0*Inv[1]] cat Inv;
    end if;
  end if;
  f, x := IsInt(0*S`Roots[1], 10, S);
  assert f;
  Z := Parent(x); // a lie - Z here is either Z or a maximal order...
  D := []; 

  Con := CartesianProduct([PowerSequence(G)|[G.0]]);

  Bas := [*1*];
  bas := [[Parent(GaloisRoot(1, S:Bound := Bound))!1]];
  bas_bound := [1];

  d_bas := bas; // the dual basis

  function Recognize(x: True, Bound := MinBound)
    if True cmpne true then
      f, y := IsInt(x[1], True, S);

// "IsInt 1:", x[1], True, S, f, y;
    else
      f, y := IsInt(x[1], Bound, S);

//"IsInt 2:", x[1], Bound, S, f, y;
    end if;
    if not f then
      if not IsExport() then
        "Fail in Recognize -- not an integer", x, True, Bound;
      end if;
      return false;
    end if;
    return y;
  end function;

  K := FieldOfFractions(Z);
  if Type(Z) in {RngOrd, RngInt, FldOrd, RngQuad} then
    useNumberField := true;
  else
    useNumberField := false;
  end if;

  den := 1;
  Den := [1];
  den_bound := 1;

  AbsDisc := 1;
  AbsDisc_bound := Minimum([Abs(x) : x in Conjugates(AbsDisc)]);

  function GetRoots(b)
    r := [ GaloisRoot(i, S: Bound := b) : i in [1..#S`Roots]];
    //neccesary - the dual basis is not always integral...
    return ChangeUniverse(r, FieldOfFractions(Universe(r)));
  end function;

  function GetConjugates(ii, t, con, Con, bound)
    r := GetRoots(bound);
    r := func<|[Evaluate(t, x) : x in r]>();
    c := func<|[[Evaluate(ii, PermuteSequence(r, x*&*y)) : x in con] : y in Con]>();
    return c;  
  end function;

  function UpdateCon(con, Con)
    return Flat(car<con, Con>);
  end function;
  function UpdateDen(Den, con, Con, c, d)
    ds := [ PowerSumToCoefficients(x) : x in d];
    ds := [ Polynomial(x) : x in ds];
    ds := [ Derivative(x) : x in ds];
    n := #Con div #con;
    dd := [];
    nd := [];
    for j in [0..#con-1] do
      for k in [1..n] do
        nd[j*n+k] := Evaluate(ds[k], c[j*n+k]);
        dd[j*n+k] := Den[k]*nd[j*n+k];
      end for;
    end for;
    return dd, nd;
  end function;
  function UpdateDBas(d_bas, d, cc, con, Con, nd) 
    db := [ [ PowerSumToCoefficients(
               [Universe(d[i])|d[i][j] - x^j : j in [1..#d[i]-1]])
                                    : x in cc[i]] : i in [1..#cc]];
    db := [db[j][i] : j in [1..#db], i in [1..#con]];
    n := #d_bas;
    db := [[Parent(nd[i])| x/nd[i] : x in db[i]] : i in [1..#Con]];
    d_bas := [ &cat [y : x in con] : y in d_bas];
    d_bas_n := [];
    for j in [1..#con] do
      d_bas_n cat:= [ [d_bas[x][l]*db[l][j] : l in [1..#Con]] : x in [1..n]];
    end for;
    return d_bas_n;
  end function;

  function UpdatePrecision(D, bound)
    vprint GaloisTower, 2: "UpdatePrecision to", Ilog(S`Prime, bound);
    Con := CartesianProduct([PowerSequence(G)|[G.0]]);
    d_bas := [[Parent(GaloisRoot(1, S:Bound := bound))!1]];
    Den := [1];
    for j in [1..#D] do
      c := GetConjugates(D[j][1], D[j][2], D[j][3], Con, bound);
      cc := c;
      d := func<|[ ConjugatesToPowerSums(x) : x in c]>();
      c := [c[j][i] : j in [1..#Con], i in [1..#D[j][3]]];
      Con := UpdateCon(D[j][3], Con);
      Den, nd := UpdateDen(Den, D[j][3], Con, c, d);
      assert #Den eq #Con;
      d_bas := UpdateDBas(d_bas, d, cc, D[j][3], Con, nd);
      assert #d_bas eq #Con;
    end for;
    return Den, d_bas;
  end function;

  s := func<x|x>;
  for i in [2..#U] do
    vprint GaloisTower, 2: red, "Level", i, "now", normal;
    if Inv cmpeq false then
      ii := RelativeInvariant(invar_coeff_ring(S), U[i-1], U[i] : IsMaximal := false, Risk := Risk);
    else
      ii := Inv[i];
    end if;
    vprint GaloisTower, 1: "Invariant defines a field of degree ", #Orbit(U[1], MultivariatePolynomial(ii)), " over Q";
    con := RightTransversal(U[i-1], U[i]);
    O := {f^x : x in con} where f := MultivariatePolynomial(ii);
    vprint GaloisTower, 1: "defining polynomial generates deg", #Orbit(U[1], O), "over Q";
    // now find the largest j such that O is  invariant under U[i]:
    // We now that it has to be U[i-1] invariant.
    j := 1;
    while j lt i and #Orbit(U[j], O) gt 1 do
      j +:= 1;
    end while;
    vprint GaloisTower, 1: "Polynomial can be defined at level ", j, "currently we are at ", i;
    // now we need a (relative) primitive element:
    r := GetRoots(2*#con);
    t := Polynomial([0,1]);
    all_t := {t};
    while #{Evaluate(ii, PermuteSequence(r, t)) : t in con} ne #con do
      t := Polynomial([Random(3) : i in all_t] cat [1]);
      Include(~all_t, t);
      if #all_t gt 10 then
        error "too many transformation, cannot find a primitive element";
      end if;
      r := GetRoots(2*#con);
      r := func<|[ Evaluate(t, x) : x in r]>();
    end while;
//    "GaloisSubfieldTower: Setting tschirni to",t;


    vprint GaloisTower, 1: "Rel Degree", #con, "total", &* [Integers()|#x[3] : x in D] * #con, "PE:", ii, "T:", t;
    Append(~D, <ii, t, con>);

    // now that we have the PE, need weed to make sure to have enough
    // precision to recognize the coefficients of the minimal polynomial
    // (more preceisly to recognize the power-sums);
    // So we can evalute ii and t at S`max_comp to get a bound on the
    // complex size of all conjugates of PE, call it M
    // then, n*M^n is a bound for the largest power sum, thus the precision
    // must be sufficient for n*M^n
    n := #Bas;
    // so M is a size bound for the complex size of all complex conjugates of 
    // the primitive element:
    if not assigned ii`GalInvType then
      ii`GalInvType := "Other";
    end if;
    M := _Bound(ii, Evaluate(t, S`max_comp));
    vprint GaloisTower, 2: "Bound", M;
    // Since we "regognize" x*Den, we get 
    //   B := n*M^n*den_bound
    // Now the usual playing with matrices and such gives for the coefficients
    // of x:
    // x_i <= n*(n-1)^((n-1)/2) * &* bas_bound / AbsDisc(K)^(1/2) * B
    // TODO: maybe get bounds for the dual basis and hope it's better
    // than the Hadramat bound.
    // ie. hope that a bound will be better than 
    //   n*(n-1)^((n-1)/2) &* bas_bound / AbsDisc(K)^(1/2)
    // we have to multiply by 2 to account for the sign...
    AbsDisc_bound := Minimum([Abs(x) : x in Conjugates(AbsDisc)]);
    n := #con; // relative degree of the extension
    B := n*M^n*den_bound; 
//   den_bound;
//    AbsDisc_bound, n, B, M;
    n_total := #bas_bound; // total degree of the extension
    bound := 2*n_total*(n_total-1)^((n_total-1)/2) * &* bas_bound / Sqrt(AbsDisc_bound)  * B; 
    assert bound ge 1;
    bound := Ceiling(bound);
    
    assert bound ge 1;
    Bound_old := Bound;
    Bound := Maximum(MinBound, bound);
    if Bound gt MaxBound then
      red, "Cutting precision! Should be ", Ilog(S`Prime, Bound), "limiting to", Ilog(S`Prime, MaxBound), normal;
    end if;
    Bound := Minimum(Bound, MaxBound);
    assert Bound ge 1;
    if Bound gt Bound_old then
      vprint GaloisTower, 1: "need to increase prec to ", Ilog(S`Prime, Bound);
      vtime GaloisTower, 2: Den, d_bas := UpdatePrecision(D[1..#D-1], Bound);
      if i gt 2 then
        bas_i := Transpose(Matrix(d_bas));
        s("Den", Den);
        s("bas_i", bas_i);
      end if;
    end if;


    c := GetConjugates(ii, t, con, Con, Bound);
    cc := c;
    d := func<|[ ConjugatesToPowerSums(x) : x in c]>();
//    d;
    e := [ Recognize([d[x][y] : x in [1..#Con]] : True := Bound) : y in [1..#con]];
//    "Recognize result:", e, [Max([RealField(10)!AbsoluteValue(y) : y in Conjugates(x)]) : x in e], Bound;
//    "AlgRoots",AlgRoots;
    if AlgRoots cmpne false then
      r := [Evaluate(ii, [Evaluate(t, x) : x in PermuteSequence(AlgRoots, c)]) : c in con];
      r := ConjugatesToPowerSums(r);
      er := ChangeUniverse(e, Universe(r));
      assert er eq r;
    end if;
    assert forall{x : x in e | Maximum([Abs(xy) : xy in Conjugates(x)]) lt Bound};
    e := PowerSumToCoefficients(e);
    if useNumberField then
      K := NumberField(Polynomial(e):Check := false, DoLinearExtension);
    else
      K := FunctionField(Polynomial(e):Check := false);
    end if;
    if AlgRoots cmpne false then
      Embed(K, Universe(AlgRoots), Evaluate(ii, [Evaluate(t, x) : x in AlgRoots]));
    end if;
    AbsDisc := AbsDisc^#con * Norm(Discriminant(DefiningPolynomial(K)), Z);    
    // should be equivalent to AbsoluteDiscriminant(K)

    c := [c[j][i] : j in [1..#Con], i in [1..#con]];
    Con := UpdateCon(con, Con);

    if Debug then
      _, tm := RightTransversal(G, U[i]);
      assert #{tm(&*x) : x in Con} eq #Con;
      
      bas := [ &cat [y : x in con] : y in bas];
    end if;

    // now we update
    // - the basis information (algebraic basis, p-adic basis, bounds)
    // - the denominator (algebraic, p-adic, bound)
    // - the dual basis - actually, we don't need the p-adic basis...
    n := #Bas;
//    #Bas, #bas_bound;
//    "Updateing bas_bound",K.1,MinimalPolynomial(K.1,Rationals()), Max([AbsoluteValue(a) : a in Conjugates(K.1)]), M;
    for j in [1..#con-1] do
      Bas cat:= [* Bas[x]*K.1 : x in [#Bas-n+1..#Bas]*];
      if Debug then
        bas cat:= [ [bas[x][l]*c[l] : l in [1..#Con]] : x in [#bas-n+1..#bas]];
      end if;
      bas_bound cat:= [ bas_bound[x]*M : x in [#bas_bound-n+1..#bas_bound]];
    end for;
/* "&*bas_bound^2, AbsDisc";
    &*bas_bound^2*1.0, Conjugates(AbsDisc); */

    if Debug then
      assert #Bas eq #bas and #Bas eq Index(G, U[i]);
      assert forall{x : x in [2..#Bas] | forall{y : y in bas[x] | IsWeaklyZero(Evaluate(MinimalPolynomial(Bas[x], Integers()), y))}};
    end if;

    //den = f'(K.1) = sum_i prod_{i ne j} (x_i - x_j)
    //and thus |den| <= n * (2M)^(n-1)
    den *:= Evaluate(Derivative(DefiningPolynomial(K)), K.1);
    den_bound *:= (2*M)^(#con -1)*#con;
    assert Maximum([Abs(x) : x in Conjugates(den)]) lt den_bound;
/*    "Denominators:";
    den_bound;
    [AbsoluteValue(a[1]) * 1.0 : a in Roots(MinimalPolynomial(den,Rationals()),ComplexField(100))]; */
    Den, nd := UpdateDen(Den, con, Con, c, d);
    assert #Den eq #Con;
    if Debug then
      assert forall{x : x in Den | IsWeaklyZero(Evaluate(AbsoluteMinimalPolynomial(den), x))};
    end if;

    d_bas := UpdateDBas(d_bas, d, cc, con, Con, nd);
    if Debug then
      Transpose(Matrix(d_bas))*Matrix(bas); // should be the identity matrix..
    end if;


    bas_i := Transpose(Matrix(d_bas));
    g,s := NewEnv(["Den", "bas_i"]);
    s("Den", Den);
    s("bas_i", bas_i);

//"Redefining Recognize";
    function Recognize(X : Bound, True)
//      "reco called", X, Bound, True;
      if True cmpne true then
        assert Bound cmpeq true;
        Bound := True;
      else
        n := #bas_bound;
        Bound := 2*n*(n-1)^((n-1)/2) * &* bas_bound / Sqrt(AbsDisc_bound) * Bound;
        Bound := Ceiling(Bound);
        assert Bound ge 1;
      end if;
      vprintf GaloisTower, 3: "1: log_%o(Bound) = %o, prec: %o\n", S`Prime, Ilog(S`Prime, Bound), Precision(X[1]);
if (Bound gt MaxBound) and (not IsExport()) then
  "Reducing Bound";
end if;  
      Bound := Minimum(Bound, MaxBound);
      vprintf GaloisTower, 3: "2: log_%o(Bound) = %o, prec: %o\n", S`Prime, Ilog(S`Prime, Bound), Precision(X[1]);
      Den := g("Den");
      bas_i := g("bas_i");
      if True cmpeq true and Precision(X[1]) gt Ilog(Norm(S`Prime), 2*Bound)+1 then
        x := [ ChangePrecision(t, p) : t in X] 
                      where p := Ilog(Norm(S`Prime), 2*Bound)+1;
      else
        x := X;
      end if;                
      //assert Precision(Den[1]) eq Precision(bas_i[1][1]);
      if True cmpeq true and Precision(x[1]) gt Precision(Den[1]) then
        vprint GaloisTower, 2: "RECO:Increase prec to ", Ceiling(Log(bound)/Log(Norm(S`Prime)));
        Den, d_bas := UpdatePrecision(D, Bound);
        assert Precision(Den[1]) ge Precision(x[1]);
        bas_i := Transpose(Matrix(d_bas));
        s("Den", Den);
        s("bas_i", bas_i);
      end if;
      vprint GaloisTower, 3: "mult: den, then mat", Precision(x[1]), Precision(bas_i[1][1]);
      vtime GaloisTower, 3: x := func<|[x[i]*Den[i] : i in [1..#x]]>();
      vtime GaloisTower, 3: t := Matrix([x])*bas_i; //XXX: this IS expensive. maybe try with reduced precision....
      t := Eltseq(t);
      r := 0;
      for k in [1..#t] do
        f, c := IsInt(t[k], Bound, S);
//        "IsInt 3:",t[k],Bound,f,c;
        if not f then
          return false;
        end if;
        c := FieldOfFractions(Z)!c;
        r +:= Bas[k]*c;
      end for;
      return K!r/den;
    end function;

  end for;
  function GetRootBound(x)
    n := #bas_bound;
    return Ceiling(n*(n-1)^((n-1)/2) * &* bas_bound / Sqrt(AbsDisc_bound) *x);
  end function;
  return K, D, Recognize, GetRootBound;
end intrinsic;

/*
intrinsic CompositionSeries(G::GrpPerm) -> []
  {Starting from the DerivedSeries, refine it until all quotients are simple.}
  C := DerivedSeries(G);
  CC := [C[1]];
  for i in [2..#C] do
    q, mq := quo<C[i-1]| C[i]>;
    if IsSimple(q) then
      Append(~CC, C[i]);
    else
      s := q;
      repeat
        s := MaximalSubgroups(s)[1]`subgroup;
        Append(~CC, sub<C[i-1] | [s.i@@mq : i in [1..Ngens(s)]], C[i]>);
      until #s eq 1;
    end if;
  end for;
  return CC;
end intrinsic;
*/

_Roots := Roots;  
function galois_splitting_field(f, Galois, Roots, Stab, AllAuto, Chain, Name, Inv, MaxBound, MinBound)
  assert Type(CoefficientRing(f)) in {FldRat, RngInt};

  if Galois cmpeq false then
    G, _, S := GaloisGroup(f);
  else
    G, _, S := Explode(Galois);
  end if;

  if #G eq 1 then
    return Rationals(), [r[1] : r in _Roots(f)], G;
  end if;

  n := Degree(f);
  Rx := SLPolynomialRing(Integers(), n : Global);
  if Stab and Chain cmpeq false then
    C := [G];
    d := {1..n};
    e := [];
    Inv := [0*Rx.1];
    while d ne {} do
      s := [<Stabilizer(G, e cat [x]), x> : x in d];
      _, p := Minimum([#x[1] : x in s]);
      e := e cat [s[p][2]];
      Exclude(~d, s[p][2]);
      g := s[p][1];
      if g ne C[#C] then
        Append(~Inv, Rx.s[p][2]);
        Append(~C, g);
      end if;
    end while;
    for i in [1..#Inv] do
      Inv[i]`GalInvType := "Other";
    end for;
    K, D, Reco, GetB := GaloisSubfieldTower(S, C:Inv := Inv, MaxBound := MaxBound, MinBound := MinBound);
  elif Chain cmpne false then
    C := Chain;
    K, D, Reco, GetB := GaloisSubfieldTower(S, C: Inv := Inv, MaxBound := MaxBound, MinBound := MinBound);
  else
    C := InternalGetChain(Stabilizer(G, 1), sub<G|>);
    K, D, Reco, GetB := GaloisSubfieldTower(S, C: MaxBound := MaxBound, MinBound := MinBound);
  end if;
  if not Roots then
    return K, _, _;
  end if;
  if Name cmpne false then
    i := 1;
    k := K;
    repeat
      AssignNames(~k, [Name cat IntegerToString(i)]);
      k := CoefficientField(k);
      kx := PolynomialRing(k);
      AssignNames(~kx, [Name cat IntegerToString(i)]);
      i +:= 1;
    until k cmpeq Rationals();
  end if;

  R := [];
  for i in [1..n] do
    I := Rx.i;
    r := func<|[GaloisRoot(j, S:Bound := GetB(S`max_comp)) : j in [1..n]]>();
    r := func<|[Evaluate(I, PermuteSequence(r, &*p)) :
                  p in CartesianProduct(Reverse([x[3] : x in D]))]>();
    r := Reco(r:Bound := S`max_comp);
    if assigned S`Scale then
      Append(~R, r/S`Scale);
    else
      Append(~R, r);
    end if;
  end for;
  if AllAuto then
    // TODO: if the splitting field can be generated as a direct compositum
    // of smaller extensions, this should be used (the above example allows
    // 9x2 over 4 - which is better than 9 over 2 over 4)
    // TODO: it seems to be much better (in this example) to compute the
    // splitting field using the stabilizer chain. Maybe always do this and
    // then use algebraic transformations to any other tower?
    // XXX: Remark: Mathias Lederer Proves that the SplittingField via 
    // stabilizer chains actually gives a groebner basis for the relations
    // ideal. Use this.
    L := [];
    for d in D do
      I := d[1];
      if not assigned I`GalInvType then
        I`GalInvType := "Other";
      end if;
      T := d[2];
      B := Bound(I, Evaluate(T, S`max_comp));
      rt := [];
      for c in d[3] do
        r := func<|[GaloisRoot(j, S:Bound := GetB(B)) : j in [1..n]]>();
        r := func<|[Evaluate(T, x) : x in r]>();
        r := func<|[Evaluate(I, PermuteSequence(r, c*&*p)) :
                      p in CartesianProduct(Reverse([x[3] : x in D]))]>();
        r := Reco(r:Bound := B);
        Append(~rt, r);
      end for;
      Append(~L, rt);
    end for;
    return K, R, G, L;
  end if;
  return K, R, G, _;
end function;

intrinsic GaloisSplittingField(f::RngUPolElt[FldRat]:Galois := false, Roots := true,
                              Stab := true, AllAuto := false, Chain := false,
                              Name := false, Inv := false, 
                              MaxBound := Infinity(), MinBound := 1)
             -> FldNum, [], GrpPerm
{Computes a splitting field for f (as a tower) and returns the roots in it}
    return galois_splitting_field(f, Galois, Roots, Stab, AllAuto, Chain, Name, Inv, MaxBound, MinBound);
end intrinsic;

intrinsic GaloisSplittingField(f::RngUPolElt[RngInt]:Galois := false, Roots := true,
                              Stab := true, AllAuto := false, Chain := false,
                              Name := false, Inv := false, 
                              MaxBound := Infinity(), MinBound := 1)
             -> FldNum, [], GrpPerm
{Computes a splitting field for f (as a tower) and returns the roots in it}
    return galois_splitting_field(f, Galois, Roots, Stab, AllAuto, Chain, Name, Inv, MaxBound, MinBound);
end intrinsic;

intrinsic CyclicToRadical(K::FldNum, Aut::FldNumElt, Zeta::RngElt) -> FldNum
  {For K being a cyclic extension which automorphism group generated by the map sending K.1 to Aut and Zeta a root of unity of Degree(K), find a Kummer generator for K.}
  //TODO: do s.th. about reducing the content of the genrator,
  //ie. x^2-175/8*(..) can be simplified.
  //
  if Degree(K) eq 2 then
    f := Eltseq(DefiningPolynomial(K));
    k := f[2]/2;
    // try to be clever...
    if IsCoercible(Rationals(), f[1] - k^2) then
      kk := Rationals()!(f[1]-k^2);
      d := Denominator(kk);
      n, q := SquareFreeFactorization(Numerator(kk)*d);
      new_K := ext<CoefficientField(K)|Polynomial([n, 0, 1])>;
      Embed(new_K, K, (K.1+k)*d/q);
      Embed(K, new_K, new_K.1*q/d-k);
    else
      new_K := ext<CoefficientField(K)|Polynomial([f[1]-k^2, 0, 1]): Check := false>;
      Embed(new_K, K, K.1+k);
      Embed(K, new_K, new_K.1-k);
    end if;
    return new_K;
  end if;

  if forall{x : x in [2..Degree(K)]| IsZero(f[x])} where f := Eltseq(DefiningPolynomial(K)) then
    return K;
  end if;
  h := hom<K -> K | Aut>;
  Z := [Zeta];
  for i in [2..Degree(K)] do
    Append(~Z, Zeta*Z[#Z]);
  end for;
  assert Z[#Z] eq 1;
  Z := Reverse(Z);

  a := K.1;
  repeat
    l := [a];
    for i in [2..Degree(K)] do
      Append(~l, h(l[#l]));
    end for;
    b := &+ [l[i]*Z[i] : i in [1..#l]];
    if b eq 0 then
      a := Random(K, 2);
    end if;
  until b ne 0;
  assert b^Degree(K) in CoefficientField(K);
  assert not b in CoefficientField(K);
  new_K := ext<CoefficientField(K)|PolynomialRing(CoefficientField(K)).1^Degree(K)-CoefficientField(K)!(b^Degree(K)):Check := false>;
  Embed(new_K, K, b);
  return new_K;
end intrinsic;

function _SolveByRadicals(f:Prime := false, Name := false, Galois := false, UseZeta_p := false, MaxBound := Infinity())

  // TODO: assign names for the roots of unity

  // TODO: reduce the memory footprint of the SubfieldTower.
  //       11T1 for exmaple needs more than 1GB
  // TODO: change/ fix SubfieldTower to recognize that polynomials can be
  //       defined over smaller fields!

  f := Polynomial(Integers(), Lcm([Denominator(x) : x in Eltseq(f)])*f);
  if Galois cmpeq false then
    pp := &* [ p : p in [1..Maximum(Degree(f), 2)] | IsPrime(p)];
    function np(x)
      // this should only returns primes p>x such that
      // p mod pp eq 1, so that p is totally split in all
      // cyclotomic fields of prime conductor < Degree(f)
      // (which is all primes that might occur in the radical tower
      // ie. in the order of the galois group of f and in the degrees
      // of the neccessary cyclotomic fields)
      // Good example for this is 11T1: the prime chosen for 11T1 will
      // produce a p-adic field of degree 220 after the roots of unity are
      // put in.
      repeat
        x := x+1;
        x := x+(1-x) mod pp;
      until IsPrime(x);
      return x;
    end function;
    G, r, S := GaloisGroup(f:Prime := Prime, NextPrime := np);
  else
    G, r, S := Explode(Galois);
  end if;

  if not IsSolvable(G) then
    error "Galois group is not solvable";
  end if;

  n := [x[1] : x in FactoredOrder(G)];
  n := Set(n);
  if not UseZeta_p then
    m := n;
    repeat
      s := &join [Set([x[1] : x in Factorisation(i-1)]) : i in m];
      m := s diff n;
      n join:= s;
    until m eq {};
  end if;
//  print "Need ", n, "roots of unity";

  n := [i : i in n | i ne 2]; // the 2nd roots are difficult in the
                              // GaloisTower - don't know why.
                              // Bad example: SolveByRadicals(Cyclo(7));
  n := Sort(n);
  ff := [PolynomialRing(Integers())| CyclotomicPolynomial(i) : i in n];
  f := Universe(ff)!f;
  for i in [1..#n] do
    repeat
      g := Gcd(f, ff[i]);
      ff[i] := ff[i] div g;
    until g eq 1;
  end for;
  delete S`Subfields;
  delete S`SubfieldLattice;
  lG := [<G, S>];
  Sall := InternalGaloisGroupProductSetup(S, f*&*ff,  [<x, 1> : x in [f] cat ff]);
  for i in [1..#n] do
    if Degree(ff[i]) eq EulerPhi(n[i]) then
      G, _, S := GaloisGroup(CyclotomicField(n[i]):Prime := S`Prime, Ring := galois_data_copy_for_factor(Sall, ff[i]));
    else
      G, _, S := GaloisGroup(ff[i]:Prime := S`Prime, Ring := galois_data_copy_for_factor(Sall, ff[i]));
    end if;
    delete S`Subfields;
    delete S`SubfieldLattice;
    Append(~lG, <G, S>);
  end for;
  G, r, S := InternalGaloisGroupProduct(Sall, lG, f*&*ff, [<x, 1> : x in [f] cat ff]);
  delete S`Subfields;
  delete S`SubfieldLattice;

  vprint GaloisTower, 1: "aiming for field of degree", #G;
  // now we need to find the roots (the order of the factorisation used by
  // GaloisGroup is independent from our here)
  // Actually, since Factorisation sort the result by degree, it should be
  // mainly obvious.

  ru := [[] : i in ff];
  rf := [];
  for i in [1..#r] do
    if IsWeaklyZero(Evaluate(f, r[i])) then
      Append(~rf, i);
    elif exists(j){j : j in [1..#ff] | IsWeaklyZero(Evaluate(ff[j], r[i]))} then
      Append(~(ru[j]), i);
    else
      error "root not accounted for!";
    end if;
  end for;

  // now we need to build a Chain such that the correspoding tower starts
  // with the roots of units - in ascending order (this way we can represent
  // roots of unity by radicals recursively)
  // Let's find the start, the small fields need to do the cyclotomic first
  C := [];
  for i := 1 to #n by 1 do
    s := &cat [ru[j] : j in [1..i]];
    u := Stabilizer(G, s);
    Append(~C, u);
  end for;
  // now to refine them...
  // The annoying part is to remember WHERE the cyclotomic fields are
  // we need this information later on.
  c := C;
  C := [G];
  cyclo := [];
  for i := 1 to #n by 1 do
    if UseZeta_p or IsPrime(#C[#C] div #c[i]) or #C[#C] eq #c[i] then //the "or" is for z_2
      Append(~C, c[i]);
    else
      q, mq := quo<C[#C]| c[i]>;
      s := q;
      repeat
        s := MaximalSubgroups(s);
        s := s[#s]`subgroup;
        Append(~C, s@@mq);
      until #s eq 1;
    end if;
    cyclo[i] := #C;
  end for;
  assert UseZeta_p or forall{j : j in [2..#C] | #C[j-1] eq #C[j] or IsPrime(#C[j-1] div #C[j])};
//  print "cyclo:", cyclo;

  // next, a refined, derived sg chain for the left-over part.
  lastCyclo := #c;
  C cat:= c[2..#c] where c := CompositionSeries(C[#C]);
  // OK, now some invariants - as we would like to see the roots of unity
  // whereever possible!

  Rx := SLPolynomialRing(Integers(), Degree(G) : Global);
  I := [0*Rx.1];
  for i := 2 to #C do
    if i in cyclo then
      Append(~I, Rx.ru[Position(cyclo, i)][1]);
    else
      ii := RelativeInvariant(invar_coeff_ring(S), C[i-1], C[i] : IsMaximal, Risk);
      Append(~I, ii);
    end if;
  end for;
  
  // then we build the tower with cyclic subfields 

  S`DescentChain := [<G>];
  K, D, Reco, GetB := GaloisSubfieldTower(S, C: Inv := I, MaxBound := MaxBound);

  // now we need to convert the cyclic steps into radical ones
  // If our tower is correct, then at any step we have all the roots we
  // need.
  // For future reference: let's find the roots and the fields:
  K_a := [];
  k := K;
  while k cmpne Rationals() do
    Append(~K_a, k);
    k := CoefficientField(k);
  end while;

  K_a := Reverse(K_a);
  z := [K!K_a[i-1].1 : i in cyclo];
  assert forall{ i : i in [1..#z] | IsOne(z[i]^n[i])};

  // now for all cyclic steps not corresponding to roots of unity
  // we need the automorphisms (ie. all the roots of the polynomial)
  
  L := [];
  vprint GaloisTower, 1: "finding autos...";
  for d in D do
    //TODO: skip the steps where we know the automorphisms (or don't need
    //them), ie.
    // - the steps generated by a root of unity (powering will do)
    // - steps generated by quadratics (transformation to radical is
    //   trivial)
    // - steps alread radical (may happen)
    I := d[1];
    if not assigned I`GalInvType then
      I`GalInvType := "Other";
    end if;
    T := d[2];
    B := Bound(I, Evaluate(T, S`max_comp));
    rt := [];
    // the fields are cyclic of prime degree => we need only one other root.
    if exists(c){c : c in d[3] | not IsIdentity(c)} then
      r := func<|[GaloisRoot(j, S:Bound := Minimum(MaxBound, GetB(B))) : j in [1..Degree(G)]]>();
      r := func<|[Evaluate(T, x) : x in r]>();
      r := func<|[Evaluate(I, PermuteSequence(r, c*&*p)) :
                    p in CartesianProduct(Reverse([x[3] : x in D]))]>();
      r := func<|Reco(r:Bound := B)>();
      vprint GaloisTower, 1: "found 2nd root", r;
      Append(~rt, r);
    else
      error "only identity found";
    end if;
    Append(~L, rt);
  end for;

  // now the transformation to radicals
  // Lagrange resolvent: suppose G=<s> and z is the root
  // of unity. Then for (almost) all a we have that
  // sum z^i s^(n-i)(a)
  // is a Kummer generator
  // Idea: either use a random a or do s.th. systematically:
  // let B be a Z-Basis for the field. The resolvent defines a Q-linear
  // map, so we can represent it by a matrix. Expanding all elements, we can
  // even get it as a matrix over Z. Small elements in the image (LLL) should
  // give "good" generators. I assume that for "small" degrees the latter
  // method is better.
  // XXX: CyclicToRadical implements only the "Random" version.
 
  k := Rationals();
  for i := 1 to #K_a do
    if UseZeta_p and i le lastCyclo then
      K := K_a[i];
    else
      K := ext<k|Polynomial(k, DefiningPolynomial(K_a[i])):Check := false>;
      Embed(K_a[i], K, K.1);
      Embed(K, K_a[i], K_a[i].1);
      vprint GaloisTower, 1: "Cyclic to radical on level ", i;
      K := CyclicToRadical(K, L[i][1], Degree(K) eq 2 select k!-1 else
                                           k!z[Position(n, Degree(K))]);
    end if;
    k := K;                                       
  end for;

  R := [];
  vprint GaloisTower, 1: "Finding roots";
  for i in [1..Degree(f)] do
    vprint GaloisTower, 2: "i:", i;
    I := Rx.i;
    r := func<|[GaloisRoot(j, S:Bound := Minimum(MaxBound, GetB(S`max_comp))) : j in [1..Degree(G)]]>();
    r := func<|[Evaluate(I, PermuteSequence(r, #p eq 0 select G.0 else &*p)) :
                  p in CartesianProduct(Reverse([PowerStructure(SetIndx) | x[3] : x in D]))]>();
    r := func<|Reco(r:True, Bound := S`max_comp)>();
    Append(~R, r/S`Scale);
  end for;

  if Name cmpne false then
    i := 1;
    k := K;
    repeat
      AssignNames(~k, [Name cat IntegerToString(i)]);
      k := CoefficientField(k);
      kx := PolynomialRing(k);
      AssignNames(~kx, [Name cat IntegerToString(i)]);
      i +:= 1;
    until k cmpeq Rationals();
  end if;

  return K, ChangeUniverse(R, K), z;
end function;


intrinsic SolveByRadicals(f::RngUPolElt[RngInt]: Prime := false, Name := false, 
  Galois := false, UseZeta_p := false, MaxBound := Infinity()) -> FldNum, [], []
  {Compute a splitting field as a radical tower and the roots of f as elements in this tower. Return also the non-trivial roots of unity used}

  return _SolveByRadicals(f: Prime := Prime, Name := Name, Galois := Galois, UseZeta_p := UseZeta_p, MaxBound := MaxBound);
end intrinsic;


intrinsic SolveByRadicals(f::RngUPolElt[FldRat]: Prime := false, Name := false, 
  Galois := false, UseZeta_p := false, MaxBound := Infinity()) -> FldNum, [], []
  {"} // "

  return _SolveByRadicals(f: Prime := Prime, Name := Name, Galois := Galois, UseZeta_p := UseZeta_p, MaxBound := MaxBound);
end intrinsic;


/*
 <example BigExample>
   load galpols;
   f := PolynomialWithGaloisGroup(10, 9);
   K := NumberField(f);
   G, _, S := GaloisGroup(K:Subfields := false);
   U := DerivedSeries(G);
   U := InternalGetChain(G, U[2]) cat InternalGetChain(U[2], U[3]);
   Remove(~U, 3);
   q,w,e,r := GaloisSubfieldTower(S, U:Bound := 17^100);
   for c in [1..10] do
     ii := func<x|x[c]>;
     r := [GaloisRoot(i, S:Bound := r(S`max_comp)) : i in [1..10]];
     r := [ii(PermuteSequence(r, &*p)) : 
       p in CartesianProduct(Reverse([x[3]: x in w]))];
     e(r:Bound := S`max_comp);
     Evaluate(DefiningPolynomial(K), $1) eq 0;
   end for;
 </example>
 <example>
   K := NumberField(x^8-2);
   G, _, S := GaloisGroup(K:Subfields := false);
   U := InternalGetChain(G, Stabilizer(G, 1));
   q,w,e := GaloisSubfieldTower(S, U:Bound := 13^40);
   U := InternalGetChain(Stabilizer(G, 1), sub<G|>);
   q,w,e := GaloisSubfieldTower(S, U:Bound := 13^40);
   for c in [1..8] do
     ii := func<x|x[c]>;
     r := [GaloisRoot(i, S:Bound := 13^40) : i in [1..8]];
     r := [ii(PermuteSequence(r, &*p)) : 
       p in CartesianProduct(Reverse([x[3]: x in w]))];
     e(r:Bound := S`max_comp);
   end for;
 </example>
 <example>
   k := CyclotomicField(3);
   K := IterateField((x-2)^3+2, 1, k);
   G, _, S := GaloisGroup(K);
   InternalGetChain(G, sub<G|>);
   U := $1;
   GaloisSubfieldTower(S, U);
   q,w,e,r := $1;
   for c in [1..9] do
     ii := func<x|x[c]>;
     r := [GaloisRoot(i, S:Bound := r(S`max_comp)) : i in [1..9]];
     r := [ii(PermuteSequence(r, &*p)) :
     p in CartesianProduct(Reverse([x[3]: x in w]))];
     e(r:Bound := S`max_comp);
     Evaluate(DefiningPolynomial(K), $1) eq 0;
   end for;
   KK := SimpleExtension(q, k); // non-export, non-existing
   GG, _, SS := GaloisGroup(KK);
 </example>  
 <example>
   k := CyclotomicField(3);
   K := IterateField((x-2)^3+2, 2, k);
   K;
   SetVerbose("GaloisGroup", 2);
   G, _, S := GaloisGroup(K);
 </example>  
   
*/
