freeze;

declare attributes FldFun : CompData, Components;
declare attributes FldFunRat : CompData;
declare verbose Complete, 2;

intrinsic MyDumbExpand(x::FldFunElt, P :: PlcFunElt, PE :: FldFunElt:RelPrec := 20) -> RngSerLaurElt
  {}
  if false and Degree(P) gt 1 then
    // Cannot be used because Evaluate() amd Completion() do not
    // neccessarily agree, ie. we NEED
    // Evaluate(x, P) eq Eltseq(mC(x))[1]
    // for all x without a pole at P.
    // Unfortunately, this is NOT the case, the residue class field
    // map coming from Completion is a "twist" of the original.
    // TODO: I'm not sure if this is an error or only unfortunate.
    _, mC := Completion(FunctionField(P), P:Precision := RelPrec);
    return mC(x);
  end if;
  if Degree(P) ne 1 then
    q := #ResidueClassField(P);
    ex := q;
    while ex le RelPrec do
      ex *:= q;
    end while;
  else
    ex := 1;
  end if;
  y := [];
  v := Valuation(x, P);
  x := x*PE^-v;
  for i in [1..RelPrec] do
    z := Evaluate(x, P);
    Append(~y, z);
    x := x- Lift(z, P)^ex;
    x := x/PE;
  end for;
  return elt<LaurentSeriesRing(ResidueClassField(P)) | v, y>;
end intrinsic;

intrinsic ConstantCoefficient(f::RngUPolElt) -> RngElt
  {The constant coefficient of the univariate polynomial f}
  return Coefficient(f, 0);
end intrinsic;

intrinsic IsInArtinSchreierRepresentation(g::FldFun) -> BoolElt, FldFunElt
  {}
  f := DefiningPolynomials(g);
  if #f gt 1 then
    return false, _;
  end if;
  f := f[1];
  p := Characteristic(Parent(f));
  if f eq Parent(f).1^p - Parent(f).1 + ConstantCoefficient(f) then
    return true, -ConstantCoefficient(f);
  else
    return false, _;
  end if;
end intrinsic;

intrinsic MyGetLowPrecisionExpandAS(K::FldFun, P::PlcFunElt:RelPrec, PE := false) 
  -> BoolElt
  {}
  
  fl, as := IsInArtinSchreierRepresentation(K);
  require fl: "Field must be Artin-Schreier for this function";
  if Type(as) eq RngUPolElt then
     v := Valuation(as, P);
  else
     v := Valuation(Norm(as, FunctionField(P)), P);
   end if;
  vprint Complete, 1: "Valuation is ", v;
  vv := v;
  RelPrec := Maximum(v+1, RelPrec); // should be high enough to lift further then.
                                    // the critical coefficient is at 0...
//  ll := MyExpand(as, p:PE := PE, Store, RelPrec := RelPrec);
  if IsInArtinSchreierRepresentation(Parent(as)) then
    ll := MyGetLowPrecisionExpand(as, P:PE := PE, RelPrec := RelPrec);
    if ll cmpeq false then
      vprint Complete, 2: "false from MyGetLowPrecisionExpand";
      return false;
    end if;
  else
    ll := MyExpand(as, P:PE := PE, Store, RelPrec := RelPrec);
  end if;
  l := Eltseq(ll);
  L := [ResidueClassField(P)|];
  X := PolynomialRing(ResidueClassField(P)).1;
  x := #ResidueClassField(P) div Characteristic(ResidueClassField(P));
  vprint Complete, 1: "InvFrob is powering by ", x;
  p := Characteristic(ResidueClassField(P));
  if v lt 0 then
    vprint Complete, 2: "false for ramification";
//    return false; // is ramified
    require v mod p eq 0: "Field cannot be ramified!!!";
    vn := v div p;
  else
    vn := v;
  end if;

  for I in [1..#l] do
    i := l[I];
    vprint Complete, 2: "v:", v;
    if v lt 0 then
      if v mod p ne 0 then 
        if i ne 0 then
          vprint Complete, 2: "false(2) for ramification";
          return false;
          error "coefficient should be zero iff K is unramified";
        end if;
        v +:= 1;
        continue;
      end if;
      Append(~L, i^x);
      j := (vv-1+I) div p - vv + 1; 
      if j le #l then
        l[j] +:= i^x;
      end if;
      v +:= 1;
    elif v gt 0 then
      Append(~L, -i);
      j := (vv-1+I) * p - vv + 1; 
      if j le #l then
        l[j] +:= i^p;
      end if;
      v +:= 1;
    else
      r := Roots(X^p -X - i);
      if #r eq 0 or Parent(r[1][1]) ne ResidueClassField(P) then
        vprint Complete, 2: "false for being inert";
        return false; // inert place found
      else
        Append(~L, r[1][1]);
      end if;
      v +:= 1;
    end if;
  end for;
  K`Components := [elt<Parent(ll)|vn, L>];
  return true;
end intrinsic;

intrinsic IsInKummerRepresentation(g::FldFun) -> BoolElt, FldFunElt
  {}
  f := DefiningPolynomial(g);
  p := CoefficientRing(f);
  if (#p-1) mod Degree(f) eq 0 and 
    f eq Parent(f).1^Degree(f) + ConstantCoefficient(f) then
    return true, ConstantCoefficient(f);
  else
    return false, _;
  end if;
end intrinsic;


intrinsic MyGetLowPrecisionExpand(g::FldFunElt, p::PlcFunElt:RelPrec, PE := false) -> RngSerLaurElt
  {}
  /*
   * Here we know that g is NOT stored
   * So we don't need to bother with it.
   * Strategy:
   * Write g in terms of as few field generators as possible.
   * Then compute Expansions for those
   * Then combine them for g
   *
   * As I don't know (in Magma) how to do "as few as possible" I have to
   * compute all.
   */

  // 1st the generators for Parent(g):
  K := Parent(g);
  k := CoefficientField(K);
  R := LaurentSeriesRing(ResidueClassField(p));
  if PE cmpeq false then
    pi := UniformizingElement(p);
  else 
    pi := PE;
  end if;

  if assigned K`Components then
    l := K`Components;
    // l should now contain a sequence containing the expansion of the
    // minimal polynomial of the DefiningPolynomials of K.
    // The expansion of x and the other generators for the coeff field
    // we get elsewhere....
    // (using MyGetLowPrecisionExpand on the CoefficientField ... )
    // The precision in l has to be high enough to allow lifting. 
  elif IsInArtinSchreierRepresentation(K) and FunctionField(p) cmpne K then
    f := MyGetLowPrecisionExpandAS(K, p:RelPrec := RelPrec, PE := PE);
    if not f then
      return false;
    end if;
    l := K`Components;
  else
    l := DefiningPolynomials(K); // works ONLY for AS extensions, not for ASW
                                 // TODO: fix this!
    if false and #l eq 1 then
      L := [K];
    else
      L := [ FunctionField(x:Check := false) : x in l];
    end if;
    l := [];
    for F in L do
      if FunctionField(p) cmpeq CoefficientField(K) then
        fl, u := IsInArtinSchreierRepresentation(F);
        if fl then
          vprint Complete, 1: "AS case found - taking shortcuts!";
          f := MyGetLowPrecisionExpandAS(F, p:RelPrec := RelPrec, PE := PE);
          assert f;
          Append(~l, F`Components[1]);
          continue;
        else
          vprint Complete, 1: "Decomposition...";
          vtime Complete, 1: P := Decomposition(F, p)[1]; 
        end if;
        //TODO: can we compute
        // - valuations (yes) (no: only when they are totally split! (I
        //   think))
        // - Evaluate/ Lift (I don't know - it's easy if the place is not
        //   an index divisor)
        // WITHOUT computing any maximal orders in F?
        val := func<x|Valuation(Norm(x), p) div (Degree(F) div Degree(P))>;
     //  val := func<x|Valuation(Norm(x), p)>;
        val := func<x|Valuation(x, P)>;
      else
        P := p;
        val := func<x|Valuation(x, P)>;
      end if;
      pi_inv := pi^-1;
      f := DefiningPolynomial(F);
      vprint Complete, 1: "Initial valution";
      vtime Complete, 1: v := val(F.1);
      if v ge 0 then
        y := F.1*pi_inv^v;
      elif v lt 0 then
        y := F.1*pi^-v;
      end if;
      pr := 0;
      y_Ser := [];
      y_start := y;
      if Degree(P) gt 1 then
        q := #ResidueClassField(P);
      else
        q := 1;
      end if;
      done := false;
      repeat
        repeat
          vprint Complete, 1: "Eval(P):";
          vtime Complete, 1: ev := Evaluate(y, P);
          assert pr ne 0 or (ev ne 0 and ev in R);
          Append(~y_Ser, ev);
          pr +:= 1;
          y_ser := elt<R|v, y_Ser, pr>;
          h := hom<PolynomialRing(k) -> PolynomialRing(R) | 
                   map<k -> R | x:-> MyExpand(x, p:RelPrec := 2*pr, PE := pi, Store)>,
                     PolynomialRing(R).1>;
          vtime Complete, 1: hf := h(f);
          vtime Complete, 1: e := Evaluate(hf, y_ser);
          vtime Complete, 1: es := Evaluate(h(Derivative(f)), y_ser);
          //"Valuation(e)", Valuation(e), v, Degree(f), RelativePrecision(y_ser);
          if Valuation(es)+v+2 lt Valuation(e) and not IsWeaklyZero(es) and
            Valuation(e) gt v*Degree(f) 
            then
            //"es:", es, "e:", e, "v:", v;
            done := true;
            break;
          end if;
          // 
          y := (y - Lift(ev, P)^q)*pi_inv;
        until q ne 1 and pr ge q;
        if done then break; end if;
        q *:= #ResidueClassField(P);
        "BAD: increasing q to ", q, " and starting again";
        error"";
        pr := 0;
        y_Ser := [];
        y := y_start;
      until false;
      Append(~l, y_ser);
    end for;
  end if;
  TargetRelPrec := RelPrec;
  repeat
    for i in [1..#l] do
      if RelativePrecision(l[i]) ge TargetRelPrec then
        continue;
      end if;
      vprint Complete, 1: "Lifting l[", i, "]";
      f := DefiningPolynomials(K)[i];
      fs := Derivative(f);
      pr := RelativePrecision(l[i]);
      y := l[i];
      v := Valuation(y);
      vprint Complete, 1: "MyGetLowPrecisionExpand: Starting with ", f, " pr := ", pr, " val := ", v;
      repeat
        ChangePrecision(~y, 2*pr);
        h := hom<PolynomialRing(k) -> PolynomialRing(R) | 
                 map<k -> R | x:-> MyExpand(x, p:RelPrec := 2*pr, PE := pi, Store)>,
                   PolynomialRing(R).1>;
        e := (Evaluate(h(f), y));
        es := (Evaluate(h(fs), y));
        y -:= e/es;
        assert Valuation(y) eq Valuation(l[i]);
        pr_inc := Valuation(e)-Valuation(es)-v;
        pr +:= pr_inc;
  //    until RelativePrecision(y) ge TargetRelPrec;
      until pr_inc + v ge TargetRelPrec;
      l[i] := y;
    end for;

    K`Components := l;

    if IsRationalFunctionField(k) then
      h := hom<K -> R | map<k -> R | 
              x :-> MyExpand(x, p:RelPrec := TargetRelPrec, PE := pi, Store)>, 
                                      ChangePrecision(l[1], TargetRelPrec)>;
    else
      h := hom<K -> R | map<k -> R | 
              x :-> MyExpand(x, p:RelPrec := TargetRelPrec, PE := pi, Store)>, 
                                      [ChangePrecision(x, TargetRelPrec): x in l]>;
    end if;
    ret := h(g);
    TargetRelPrec +:= TargetRelPrec div 10 + 1;
  until RelativePrecision(ret) - Valuation(ret) ge RelPrec;
  return ret;
end intrinsic;

     
intrinsic MyExpand(g::FldFunRatUElt, P::PlcFunElt:RelPrec := 5, Store := false, PE := false) -> RngSerLaurElt
  {}
  k := Parent(g);
  if PE cmpeq false then
    pi := UniformizingElement(P);
  else 
    pi := PE;
  end if;
  R<p> := LaurentSeriesRing(ResidueClassField(P));

  if IsCoercible(ResidueClassField(P), g) then // XXX: does not seem to work...
    return R!g;
  end if;

  if g eq pi then return p; end if;

  if assigned k`CompData then
    if k`CompData[1] cmpne P then
      delete k`CompData;
    end if;
  end if;
  if assigned k`CompData and RelativePrecision(k`CompData[2]) ge RelPrec then
    return ChangePrecision(Evaluate(g, ChangePrecision(k`CompData[2], RelPrec)), RelPrec);
  end if;
  if not assigned k`CompData then 
    x := k.1;
    s_x := MyDumbExpand(FunctionField(P)!x, P, pi:RelPrec := 20);
    f := AbsoluteMinimalPolynomial(pi);
    d := LCM([ Denominator(x) : x in Eltseq(f)]);
    f *:= d;
  else
    s_x := k`CompData[2];
    f := k`CompData[3];
  end if;

  pr := RelativePrecision(s_x);
  vprint Complete, 1: "Main Lifting!";
  while pr lt RelPrec do
    ChangePrecision(~s_x, 2*pr);
    h := hom<Parent(f) -> PolynomialRing(R) | 
      hom<CoefficientRing(f) -> PolynomialRing(R)| PolynomialRing(R).1>, R.1>;
    vtime Complete, 1: hf := h(f);  
    vtime Complete, 1: e := ChangePrecision(Evaluate(hf, s_x), 2*pr);
    vtime Complete, 1: es := ChangePrecision(Evaluate(Derivative(hf), s_x), 2*pr);
    vtime Complete, 1: s_x -:= e/es;
    pr +:= Valuation(e) - Valuation(es) - Valuation(s_x);
    vprint Complete, 1: "pr now ", pr, "( ", Valuation(e),  Valuation(es), Valuation(s_x), ")";
  end while;

  k`CompData := [*P, s_x, f*];
  return ChangePrecision(Evaluate(g, ChangePrecision(s_x, RelPrec)), RelPrec);
end intrinsic;



intrinsic MyExpand(g::FldFunElt, P::PlcFunElt:RelPrec := 5, Store := false, PE := false) -> RngSerLaurElt
  {}
 
//  "MyExpand(", g, ", ", P, ":RelPrec := ", RelPrec, ", Store := ", Store, ", PE := ", PE, ")";
  K := Parent(g);
  k := FunctionField(P);
  if PE cmpeq false then
    pi := UniformizingElement(P);
  else
    pi := PE;
  end if;

  if g eq pi then
    return LaurentSeriesRing(ResidueClassField(P)).1;
  end if;
  if IsCoercible(ResidueClassField(P), g) then 
    return LaurentSeriesRing(ResidueClassField(P))!g;
  end if;

  /* 
   * In the case that k ne K we assume:
   *  - k is the CoefficientField of K
   *  - P is totally split in K (which we do not check! - it's too expensive)
   *  - we want the expansion wrt. to some arbitray, but fixed, place in K
   *    over P
   *  - and we want the UniformizingElement to be in k
   * 
   * For now, we also assume that the degree of P is one.
   * Since I'm lazy, I also use that k is absolute.
   */
   

   //require ResidueClassField(P) eq ConstantField(K):
   //  "Place must be of degree 1 here...";

   if k cmpne K then
     require k cmpeq CoefficientField(K):
       "When using different rings, we cannot step more than one step";
   end if;

   if assigned K`CompData and K`CompData[1] eq P then
     use_stored := true;
   else
     use_stored := false;
   end if;

   if use_stored then
     pos := Position([i[3] : i in K`CompData[2]], g);
     if pos ne 0 and RelativePrecision(K`CompData[2][pos][1]) ge RelPrec then
       return ChangePrecision(K`CompData[2][pos][1], RelPrec);
     end if;
   else 
     pos := 0;
   end if;
//   "========================", g;

   // OK: this means, we have to work. We have 3 different strategies for
   // computing completions:
   // - Eval/ Lift
   // - if the expansion of x and the generators for the field are known, we
   //   can use combinations of those
   // - if the expansion is known to a lower precision, we can do lifting.
   // the first two can also be done by Expand - if K is absolute.
   //
   // It is clear(?) that for LARGE precision the 3rd method is best. It is
   // also clear that the 1st is neccessary to start all the others...
   // The case I'm mainly interested in is
   //  - RelPrec HUGE
   //  - g either in k or K/k a non-simple case. IN the latter we have to
   //  avoid Eval/Lift as the otherwise neccessary MaximalOrder and splitting
   //  information will be too expensive.
   // Let's get initial Precision...


  if pos ne 0 then
    f := K`CompData[2][pos][2];
  end if;
  if g eq CoefficientField(k).1 then
    vtime Complete, 1: f := MinimalPolynomial(pi, CoefficientField(k));
  else
    vprint Complete, 1: "MinPoly... of ", g;
    vtime Complete, 1: f := MinimalPolynomial(g, CoefficientField(k));
  end if;
  d := Lcm([Denominator(x) : x in Eltseq(f)]);
  f := f*d;  // or do something better with denominators.
  pr := 1000;
  R := LaurentSeriesRing(ResidueClassField(P));
  Rx := PolynomialRing(R);
  IndentPush();
  repeat
//    "inner loop for ", g;
    if pos ne 0 then
      s_g := K`CompData[2][pos][1];
      if RelativePrecision(s_g) ge pr then
        pr := RelativePrecision(s_g);
//        "truncating initial approx to ", pr;
      else
        s_g := MyGetLowPrecisionExpand(g, P:RelPrec := pr);
      end if;
    else
      s_g := MyGetLowPrecisionExpand(g, P:RelPrec := pr);
    end if;
    if pr ge RelPrec then
      vprint Complete, 1: "return without store";
      IndentPop();
      return ChangePrecision(s_g, RelPrec);
    end if;
    vprint Complete, 1: "Lifting in MyExpand, starting at ", pr, RelativePrecision(s_g);
    prec := pr;
    repeat
      vprint Complete, 2: "====";
      prec := 2*prec;
      ChangePrecision(~s_g, prec);
      if g eq CoefficientField(k).1 then
        // Expanding g is slightly different than the others
        h := hom<Parent(f) -> Rx | hom<CoefficientRing(f) -> Rx|Rx.1>, R.1>;
      else
        s_x := MyExpand(k!CoefficientField(k).1, P:RelPrec := prec);
        h := hom<Parent(f) -> Rx | hom<CoefficientRing(f) -> R|s_x>, Rx.1>;
      end if; 
      ff := h(f);
      ffp := Derivative(ff);
      vtime Complete, 2: e := Evaluate(ff, s_g);
      vtime Complete, 2: v := Evaluate(ffp, s_g);
      vprint Complete, 2: "MyExpand Lifting: vals are ", Valuation(e), Valuation(v), RelativePrecision(e), RelativePrecision(v);
      if Valuation(v) ge Valuation(e) or IsWeaklyZero(v) then // be careful with negatives here!
        vprint Complete, 1: "increase initial prec";
        vprint Complete, 1: Valuation(e), Valuation(v), s_g;
        pr +:= 50;
        prec := -1;
        break;
      end if;
//      "e:", e;
//      "v:", v;
//      "=================";
      vtime Complete, 2: s_g -:= e/v;
      prec := prec div 2 + Valuation(e) - Valuation(v);
    until prec ge RelPrec;
  until prec ge RelPrec;
  IndentPop();

  if Store then
    if not assigned K`CompData then
      K`CompData := <P,[<s_g, f, g>]>;
    elif pos eq 0 then
      Append(~(K`CompData[2]), <s_g, f, g>);
    else
      K`CompData[2][pos][1] := s_g;
    end if;
  end if;
  return ChangePrecision(s_g, RelPrec);
end intrinsic;
