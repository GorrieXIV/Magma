freeze;


intrinsic GeneralisedEquationOrder(K::FldAlg) -> RngOrd
{Finds an equation like order for non-integral polynomials}
  h, E := HasAttribute(K, "EquationOrder");
  if h then
    return E;
  end if;
  f := DefiningPolynomial(K);
  function OnePoly(g)
    g := Eltseq(g);
    d := LCM([Denominator(x) : x in g]);
    return [1] cat [d*Polynomial(g[i..#g]) : i in [2..#g-1]];
  end function;
  if Type(f) eq SeqEnum then
    b := [ [ Evaluate(x, K.i) : x in OnePoly(f[i])] : i in [1..#f]];
    b := [ &* x : x in CartesianProduct(b)];
  else
    b := [Evaluate(x, K.1) : x in OnePoly(f)];
  end if;
  return Order(b:Order, Verify := false);
end intrinsic;

_Discriminant := Discriminant;
intrinsic OptimizedRepresentation(K::FldAlg[FldRat]: 
   TrialDivisionLimit := 10^6, 
   PollardRhoLimit := 8191,
   ECMLimit := -1,
   MPQSLimit := -1,
   PartialFactorisation := false,  
   Discriminant:= false, Ramification := false) -> FldAlg, Map
{Tries to find an optimized representation for K}
  if assigned K`MaximalOrder then
    return InternalOptimizedRepresentation(K);
  end if;

  if assigned K`EquationOrder then
    E := K`EquationOrder;
  else
    E := GeneralisedEquationOrder(K);
  end if;


  if Discriminant cmpne false or Ramification cmpne false then
    if Discriminant cmpne false then
      M := MaximalOrder(E:Discriminant := Discriminant);
    else
      M := MaximalOrder(E:Ramification := Ramification);
    end if;
  else
    d := _Discriminant(E);
    assert Type(d) eq RngIntElt;
    if PartialFactorisation then
      MPQSLimit := 0;
      ECMLimit := 10^3;
    end if;
    a,_,c := Factorisation(d:TrialDivisionLimit := TrialDivisionLimit,
                             PollardRhoLimit := PollardRhoLimit,
                             ECMLimit := ECMLimit,
                             Proof := false,  
                             MPQSLimit := MPQSLimit);
    M := false;
    if not assigned c then
      c := [];
    end if;
    for p in a do
      Ep := pMaximalOrder(E, p[1]);
      if M cmpeq false then
        M := Ep;
      else
        M := M+Ep;
      end if;
    end for;
    for p in c do
      Ep := E;
      repeat
        Ip := pRadical(Ep, p);
        Ep_old := Ep;
        Ep := MultiplicatorRing(Ip);
        Ep := Simplify(Ep);
      until Ep eq Ep_old;
      if M cmpeq false then
        M := Ep;
      else
        M := M+Ep;
      end if;
    end for;
  end if;
  f, N, mp := InternalOptimizedRepresentation(M);
  if not f then
    return K, hom<K -> K | K.1>;
  end if;
  return NumberField(N), map<K -> NumberField(N) | x :-> NumberField(N)!x, 
                                                   y :-> K!y>;
end intrinsic;

intrinsic OptimizedRepresentation(O::RngOrd: 
   TrialDivisionLimit := 10^6, 
   PollardRhoLimit := 8191,
   ECMLimit := -1,
   MPQSLimit := -1,
   PartialFactorisation := false,  
   Discriminant:= false, Ramification := false) -> BoolElt, RngOrd, Map
{Tries to find an optimized representation for O}
  require IsAbsoluteOrder(O):
    "Order must be defined over Z";
  K := NumberField(O);
  if assigned K`MaximalOrder then
    a,b,c := InternalOptimizedRepresentation(O);
    if a then
      b := Order(Basis(O, FieldOfFractions(b)):Verify := false, Order := true);
      return a, b, map<O -> b | x :-> b!x, y:-> O!y>;
    end if;
    return false, _, _;
  end if;

  if Discriminant cmpne false or Ramification cmpne false then
    if Discriminant cmpne false then
      M := MaximalOrder(O:Discriminant := Discriminant);
    else
      M := MaximalOrder(O:Ramification := Ramification);
    end if;
  else
    d := _Discriminant(O);
    assert Type(d) eq RngIntElt;
    if PartialFactorisation then
      MPQSLimit := 0;
      ECMLimit := 10^3;
    end if;
    a,_,c := Factorisation(d:TrialDivisionLimit := TrialDivisionLimit,
                             PollardRhoLimit := PollardRhoLimit,
                             ECMLimit := ECMLimit,
                             Proof := false,  
                             MPQSLimit := MPQSLimit);
    if not assigned c then c := []; end if;                         
    M := false;
    for p in a do
      Ep := pMaximalOrder(O, p[1]);
      if M cmpeq false then
        M := Ep;
      else
        M := M+Ep;
      end if;
    end for;
    for p in c do
      Ep := O;
      repeat
        Ip := pRadical(Ep, p);
        Ep_old := Ep;
        Ep := MultiplicatorRing(Ip);
        Ep := Simplify(Ep);
      until Ep eq Ep_old;
      if M cmpeq false then
        M := Ep;
      else
        M := M+Ep;
      end if;
    end for;
  end if;
  a,b,c := InternalOptimizedRepresentation(M);
  if a then
    b := Order(Basis(O, FieldOfFractions(b)):Verify := false, Order := true);
    return a, b, map<O -> b | x :-> b!x, y:-> O!y>;
  end if;
  return false, M, map<M -> M | x :-> x, y:-> y>;;
end intrinsic;

intrinsic MaximalOrder(K::FldAlg:Discriminant := false, Ramification := false) -> RngOrd
{Computes the maximal order of K}

  f, M := HasAttribute(K, "MaximalOrder");
  if f then
    return M;
  end if;

  if Discriminant cmpne false or Ramification cmpne false then
    if assigned K`EquationOrder then
      E := K`EquationOrder;
    else
      E := GeneralisedEquationOrder(K);
    end if;
    if Ramification cmpne false then
      return MaximalOrder(E:Ramification := Ramification);
    else
      return MaximalOrder(E:Discriminant := Discriminant);
    end if;
  end if;
  return InternalMaximalOrder(K);
end intrinsic;

function ApproximateLattice(O: Prec := 40)
  b := AbsoluteBasis(O);
  if ISA(Type(O), RngOrdFracIdl) then
    O := Order(O);
  end if;

  i := InfinitePlaces(O);
 
  function conj(x, s2:Prec := Prec)
    res := [];
    for p in i do
      if IsReal(p) then
        Append(~res, Evaluate(x, p:Precision := Prec));
      else
        c := Evaluate(x,p:Precision := Prec);
        Append(~res, s2*Re(c));
        Append(~res, s2*Im(c));
      end if;
    end for;
    return res;
  end function;
  lambda := 10^Prec;

  R := RealField(2*Prec);
  s2 := Sqrt(R!2);
  M := Matrix([conj(x, s2:Prec := 2*Prec) : x in b]);
  mx := Maximum([Abs(x) : x in Eltseq(M)]);
  // error in Gram computation:
  //  largest error in M (ie. 2^(-prec + Log(2, mx)))
  //  *mx
  //  *n
  // and I'd like this to be < 2^-Prec
  er := Floor(2*Prec - 2*Log(10, mx)- Log(10, #b));
  if er lt Prec then
    R := RealField(Prec + Floor(2*Log(10, mx*#b))+5);
    s2 := Sqrt(R!2);
    M := Matrix([conj(x, s2:Prec := Prec + Floor(2*Log(10, mx*#b))+5) : x in b]);
    lambda := 10^Precision(M[1][1]);
  end if;

  G := M*Transpose(M);
  N := Matrix(Nrows(M), Ncols(M), [Round(x*lambda) : x in Eltseq(G)]);
  N := N+((#b+1) div 2) * IdentityMatrix(Integers(), Nrows(N));

  if not IsPositiveDefinite(N) then
    return ApproximateLattice(O: Prec := Prec*2);
  end if;
  return LatticeWithGram(N), b, lambda;
end function;

intrinsic NewLLLBasis(O::RngOrd: Prec := 40) -> []
  {Computes an approximative LLL basis for O}

  N, b := ApproximateLattice(O:Prec := 40);
  _, T := LLL(N);

  sb := func<|[&+ [T[j][i]*b[i] : i in [1..Ncols(T)]] : j in [1..Nrows(T)]]>();

  return sb;

end intrinsic;

intrinsic InternalAbsoluteOptOrder(O::RngOrd: Prec := 40, SearchMax := 10) -> RngOrd
{Combines AbsoluteField and OptimizedRep}
  
  sb := NewLLLBasis(O:Prec := Prec);
  l := 1;
  n := #sb;
  mind := 0;
  minf := 0;
  max := n div 2 + 1;
  found := 0;
  repeat
    repeat
      x := func<|&+ [Random(sb) : x in [1..l]]>();
      max -:= 1;
      f := AbsoluteMinimalPolynomial(x);
      if Degree(f) eq n then
        d := Abs(Discriminant(f));
        if mind eq 0 or d lt mind then
          mind := Abs(Discriminant(f));
          minf := <x, f>;
          found := 0;
        end if;
        found +:= 1;
      end if;
    until max eq 0 or (mind ne 0 and found gt SearchMax);
    if max eq 0 then
      l +:= 1;
      max := n^l div 2 +1;
    end if;
  until mind ne 0 and found gt 10;  

  K := NumberField(minf[2]);
  Embed(K, FieldOfFractions(O), minf[1]);
  bK := Basis(K, FieldOfFractions(O));
  bK := Matrix([Flat(x) : x in bK]);
//
//  S := O;
//  while S cmpne Integers() do
//    S:Maximal;
//    if IsSimple(S) then
//      s := Solution(bK, Matrix([Flat(FieldOfFractions(O)!NumberField(S).1)]));
//      Embed(NumberField(S), K, K!Eltseq(s[1]));
//    else
//      s := Solution(bK, Matrix([Flat(FieldOfFractions(O)!x) : x in GeneratorsSequence(NumberField(S))]));
//      Embed(NumberField(S), K, [K!Eltseq(s[i]) : i in [1..Nrows(s)]]);
//    end if;
//    S := CoefficientRing(S);
//  end while;
//  return Order([K!NumberField(O)!x : x in sb]);
  s := Solution(bK, Matrix(Rationals(), [Flat(x) : x in sb]));
  O := Order([K!Eltseq(s[i]) : i in [1..n]]:Verify := false, Order);
  return O;
end intrinsic;

intrinsic CanonicalRepresentation(Oin::RngOrd) -> RngOrd
  {Computes a canonical representation over Z}

  fl, l := OptimizedRepresentation(Oin);
  if fl then Oin := l; end if;
  O := Simplify(LLL(Oin));
  O := Simplify(LLL(O));
  // I don't know why, bu experimentally, in interesting examples,
  // the 2nd Simplify(LLL(O)) makes the difference between it working
  // or the enumeration taking forever and lots of memory.
  
  L, b, lambda := ApproximateLattice(O:Prec := 200); 

  // We SHOULD have |Length(L)/lambda - Length(O)|(x) 
  //               <= (3n+1)/2/lambda |x|_2^2
  // so as long as, in the end, BU >= minT + (3n+1)/2/lambda |x|_2^2
  // we are guaranteed to have found the shortest elements.
  LL := LLL(L);
  n := Degree(L);

  minT := 0;
  minf := 0;
  BL := lambda;
  BU := BL*2;
  eps := 10^-10;
  repeat
//    "calling SV woth", BL, BU;
    s := ShortVectors(L, BL, BU);
//    "found", #s, "elements";
    for i in s do
      z := &+ [ i[1][j]*b[j] : j in [1..n]];
      if not IsPrimitive(z) then
        continue;
      end if;
      f := MinimalPolynomial(z);
      pol_cmp := function(x, y)
        x := Eltseq(x);
        x := Reverse(x);
        xa := [Abs(t) : t in x];

        y := Eltseq(y);
        y := Reverse(y);
        ya := [Abs(t) : t in y];
        if xa eq ya then
          return x le y;
        else
          return xa le ya;
        end if;  
      end function;
      if Degree(f) eq n then
        g :=  Evaluate(f, -Parent(f).1);
        s := 1;
        if pol_cmp(g, f) then
          f := g;
          s := -1;
        end if;
        d := Abs(Discriminant(f));
        l := Length(z);
        if minT eq 0 or l lt minT - eps then
          minT := l;
          minf := <z, d, f, s*i[1]>;
//          "best now1", minf, minT, l;
        end if;
        if f eq minf[3] then continue; end if;
        if Abs(l - minT) lt eps then
          if d lt minf[2] then
            minT := l;
            minf := <z, d, f, s*i[1]>;
//            "best now2", minf, minT, l;
          elif d gt minf[2] then
            continue;
          elif pol_cmp(f, minf[3]) then
            minT := l;
            minf := <z, d, f, s*i[1]>;
//            "best now3", minf, minT, l;
          end if;
        end if;
      else
      end if;
    end for;
    BL := BU;
    BU := Ceiling(BU*1.2);
  until minT ne 0 and 
        minT +(3*n+1)/2/lambda*&+[minf[4][j]^2 : j in [1..n]] lt BL;

  return minf[3], minf[1];
end intrinsic;
    
  
