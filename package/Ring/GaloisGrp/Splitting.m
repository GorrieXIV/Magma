freeze;

/* <example>
 SplittingField(x^5-5, pAdicRing(5));
 SplittingField(DefiningPolynomial(CyclotomicField(21:Sparse)), pAdicRing(7));
*/ 


intrinsic AbsoluteDegree(R::RngPad) -> RngIntElt
  {The degree of R over the p-adic ring}
  d := Degree(R);
  R := CoefficientRing(R);
  while R ne CoefficientRing(R) do
    d *:= Degree(R);
    R := CoefficientRing(R);
  end while;
  return d;
end intrinsic;

function OptimizedRepresentation(R:Map := false)
//intrinsic OptimizedRepresentation(R::RngPad:Map := false) -> RngPad, Map
//  {An optimized representation of R, ie. R as a totally ramified extension over an unramifed extension over Zp.}
  f:=InertiaDegree(R,PrimeRing(R));

  Inf := Precision(R) eq Infinity();
  Prec := 40;
  if Inf then
    R := ChangePrecision(R, Prec);
  end if;

  B := R;
  while B cmpne BaseRing(B) do
    B := BaseRing(B);
  end while;

  FR := ResidueClassField(R);
  if f ne 1 then
    U := UnramifiedExtension(B, f);
    Embed(ResidueClassField(U), FR); // this SHOULD ensure that coercion works.
  else
    U := B;
  end if;
  if f eq AbsoluteDegree(R) and Map cmpeq false then
    return U;
  end if;

  FU := ResidueClassField(U);

  if Map eq false then
    f := CharacteristicPolynomial(UniformizingElement(R), B);
    f := Polynomial(U, f);
    f := Factorisation(f);
    return ext<U|f[1][1]>;
  end if;

  function collapse(R)
    if R cmpeq BaseRing(R) then
      return R, map<R->U | x :-> U!x>;
    else
      BR, mp := collapse(BaseRing(R));
      f := DefiningPolynomial(R);
      nf := Polynomial([mp(x) : x in Eltseq(f)]);
      if IsEisenstein(f) then
        if BaseRing(BR) cmpeq U then
          nR := ext<BR|nf>;
          mp := hom<R -> nR | mp, nR.1>;
          return nR, mp;
        else
          // here's what we know and have:
          // R is an Eisenstein extension over some Eisenstein extension
          // (over unramified, but that's not important here and now)
          // I think that implies that
          //  - R.1 is a Uniformizer of R
          //  - and therefore a primitive element
          nR := ext<BR|nf>;
          f := MinimalPolynomial(nR.1, U);
          nR := ext<BR|f>;
          mp := hom<R -> nR | mp, nR.1>;
          return nR, mp;
        end if;
      else
        // must be inert, and therefore is maped via the unramified part
        r := FU!FR!R.1; // should work because of Embed above
        r := HenselLift(nf, BR!U!r, Prec);
        mp := hom<R -> U | mp, r> ;
        return U, mp;  
      end if;
    end if;
  end function;

  R, mp := collapse(R);
  return R, mp;
end function;

intrinsic RingOfIntegers(R::RngPad) -> RngPad
  {The integers of R, ie. R itself.}
  return R;
end intrinsic;

intrinsic SplittingField(f::RngUPolElt[RngInt], R::RngPad : Opt := true) -> RngPad, []
{The splitting field of f as an extension of R};
	return SplittingField(f, map<CartesianProduct(Integers(), Integers()) -> R | x :-> x[1]>:Opt := Opt);
end intrinsic;

intrinsic SplittingField(f::RngUPolElt[FldRat], R::RngPad: Opt := true) -> RngPad, []
  {The splitting field of f as an extension of R}
  d := LCM([Denominator(x) : x in Eltseq(f)]);
  return SplittingField(Polynomial(Integers(), d*f), R:Opt := Opt);
end intrinsic;  

intrinsic SplittingField(f::RngUPolElt, Rmp::Map:Opt := true) -> RngPad, []
  {The splitting field of f as an extension of R, the codomain of Rmp having
  domain the coefficient ring of f.}

  require Component(Domain(Rmp), 1) cmpeq CoefficientRing(f) or
          Component(Domain(Rmp), 1) cmpeq FieldOfFractions(CoefficientRing(f)): "Domain of argument 2 must be the coefficient ring of argument 1";
  R := Codomain(Rmp);
  require BaseRing(R) cmpeq BaseRing(R):
    "Currently the splitting field can be over Zp only";

  /*
  P := Integers()!UniformizingElement(R);
  assert IsPrime(P);
  */
  char_0_rat_func := Type(CoefficientRing(R)) eq FldPad;
  if char_0_rat_func then
      v := Valuation(Rmp(Discriminant(f), <R`DefaultPrecision, CoefficientRing(R)`DefaultPrecision>));
  else
      v := Valuation(Rmp(Discriminant(f), R`DefaultPrecision));
  end if;

  if Precision(R) cmpeq Infinity() then
    S := ChangePrecision(R, 2*v+1);
    Rmp := map<Domain(Rmp) -> S | x :-> S!Rmp(x[1], S`DefaultPrecision)>;
    Inf := true;
    if char_0_rat_func then
      prec := <2*v + 1, CoefficientRing(R)`DefaultPrecision>;
    else
	prec := 2*v + 1;
    end if;
  else
    require Precision(R) ge 2*v+1:
      "Need at least a precision of ", 2*v+1, "to compute the splitting field";
    S := R;
    Inf := false;
    if char_0_rat_func then
      prec := <Precision(R), Precision(CoefficientRing(R))>;
    else
	prec := Precision(R);
    end if;
  end if;

 
    Rmp_prec := map<CoefficientRing(f) -> S | x :-> Rmp(x, prec)>;
    Rpoly_hom := hom<Parent(f) -> PolynomialRing(S) | Rmp_prec, Polynomial(S, [0, 1])>;
    rf, rfm := ResidueClassField(S);
  rf := Polynomial(rf, [rfm(x) : x in Eltseq(Rpoly_hom(f))]);
  l := Factorisation(rf);
  if Degree(rf) eq Degree(f) and forall{x : x in l | x[2] eq 1} then
    F := Lcm([Degree(x[1]) : x in l]);
    if ISA(Type(R), RngPad) then
	R := UnramifiedExtension(R, F);
    else
	R := ChangeRing(R, ext<CoefficientRing(R) | F>);
    end if;
    return R;
  end if;

    
  _, _, c := Factorisation(Polynomial(S, Rpoly_hom(f)):Certificates);
  F := Lcm([ x`F : x in c]);
  if F ne 1 then
    R := UnramifiedExtension(R, F);
    if Inf then
      S := ChangePrecision(R, 2*Valuation(Rmp_prec(Discriminant(f)))+1);
	Rmp_prec := map<CoefficientRing(f) -> S | x :-> Rmp(x, Precision(S))>;
	Rpoly_hom := hom<Parent(f) -> PolynomialRing(S) | Rmp_prec, Polynomial([0, 1])>;
    else
      S := R;
    end if;
  end if;
  U := S;

    Rhf := Rpoly_hom(f);
    rts := [];
  repeat
//Degree(Rhf);
    time rts cat:= Roots(Rhf, S);
    if #rts eq Degree(f) then
	break;
    end if;
    time lf, _, c := Factorisation(Polynomial(S, Rhf):Certificates, Extensions);
    max_deg := Maximum([Degree(ff[1]) : ff in lf]);
    if max_deg gt 1 then
      assert exists(F){ F: F in [1..#lf] | Degree(lf[F][1]) eq max_deg}; 
      S := c[F]`Extension;
//S, lf;
      split_pol := &*[ff[1] : ff in lf | Degree(ff[1]) gt 1];
	/*
	Rmp_prec := map<CoefficientRing(f) -> S | x :-> Rmp(x, Precision(S))>;
	Rpoly_hom := hom<Parent(f) -> PolynomialRing(S) | Rmp_prec, Polynomial(S, [0, 1])>;
      f := Polynomial(S, Rpoly_hom(f));
      */
      Rhf := Polynomial(S, split_pol);
    else
      break;
    end if;
  until false;
  if U cmpeq S then
    return R;
  end if;
  if Opt then
    A := AbsoluteTotallyRamifiedExtension(S);
    return A;
  else
    return S;
  end if;
end intrinsic;

intrinsic SplittingField(f::RngUPolElt[FldFunRat], R::RngSer:Opt := true) -> RngSerExt, []
  {The splitting field of f as an extension of R.}

  if Precision(R) cmpeq Infinity() then
    S := ChangePrecision(R, 2*Valuation(R!Discriminant(f))+1);
    Inf := true;
  else
    S := R;
    Inf := false;
  end if;
 
  U := S;

  repeat
    lf, _, c := Factorisation(Polynomial(S, f):Certificates, Extensions);
    if exists(F){ F: F in [1..#lf] | Degree(lf[F][1]) gt 1} then
      S := c[F]`Extension;
      f := Polynomial(S, f);
      assert Precision(S) ge 2*Valuation(Discriminant(f))+1;
    else
      break;
    end if;
  until false;
  if U cmpeq S then
    return R;
  end if;
  if Opt then
    return OptimizedRepresentation(S:Map := false);
  else
    return S;
  end if;
end intrinsic;

intrinsic SplittingField(f::[RngUPolElt[FldRat]], R::RngPad) -> RngPad, []
  {The common splitting field of the polynomials in f as an extension of R}
  return SplittingField([Polynomial(Integers(), LCM([Denominator(x) : x in Eltseq(g)])*g) : g in f], R);
end intrinsic;  

intrinsic SplittingField(f::[RngUPolElt[RngInt]], R::RngPad:Opt := true) -> RngPad, []
  {"} // "

  require BaseRing(R) cmpeq BaseRing(R):
    "Currently the splitting field can be over Zp only";

  P := Integers()!UniformizingElement(R);
  assert IsPrime(P);
  v := [Valuation(Discriminant(g), P) : g in f];
  v := &+ [v[i]*&*[Integers()|Degree(f[j]) : j in [1..#f] | i ne j] : i in [1..#f]];

  if Precision(R) cmpeq Infinity() then
    S := ChangePrecision(R, 2*v+1);
    Inf := true;
  else
    require Precision(R) ge 2*v+1:
      "Need at least a precision of ", 2*v+1, "to compute the splitting field";
    S := R;
    Inf := false;
  end if;

 
  l := &cat [Factorisation(Polynomial(ResidueClassField(R), g)) : g in f];
  if forall{x : x in l | x[2] eq 1} then
    F := Lcm([Degree(x[1]) : x in l]);
    R := UnramifiedExtension(R, F);
    return R;
  end if;

  f := [x : x in f | Degree(x) gt 1];

    
  _, _, c := Factorisation(Polynomial(S, f[1]):Certificates);
  F := Lcm([ x`F : x in c]);
  if F ne 1 then
    R := UnramifiedExtension(R, F);
    if Inf then
      S := ChangePrecision(R, 2*Valuation(R!Discriminant(f))+1);
    else
      S := R;
    end if;
  end if;
  U := S;

  np := 1;
  rts := {};
  repeat
    time rts join:= Seqset(Roots(f[np], S));
    if #rts eq Degree(f[np]) then
	lf := [];
    else
	lf, _, c := Factorisation(Polynomial(S, f[np]):Certificates, Extensions);
    end if;
    if exists(F){ F: F in [1..#lf] | Degree(lf[F][1]) gt 1} then
	  S := c[F]`Extension;
	  f := [Polynomial(S, g) : g in f];
//      assert Precision(S) ge 2*Valuation(Discriminant(f))+1;
    else
      np +:=1;
      if np gt #f then
        break;
      end if;
      rts := {};
    end if;
  until false;
  if U cmpeq S then
    return R;
  end if;
  if Opt then
    A := AbsoluteTotallyRamifiedExtension(S);
    return A;
  else
    return S;
  end if;
end intrinsic;
