freeze;

/* Pretest based on factorization patterns.
   Can we exclude some degrees for subfieds.

   Idea of the approach:
   - Subfields are related to block-systems
   - Fixed points lead to fixed blocks
   - Try to derive a contradiction to assumed block-sizes.
   (Similar to the first step of Juergens algorithm) */

// Given the cycle-pattern of a permutation, compute the pattern of its ex power.
function PowerPattern(pat,ex)
 
 gcd_l := [Gcd(a,ex) : a in pat];
 return Sort(&cat [[pat[i] div gcd_l[i] : j in [1..gcd_l[i]]  ] : i in [1..#pat]]);
end function;

// Given a set of factorization patterns of an irreducible polynomial f modulo various primes
// This function computes a list of possible sizes of block-systems of the Galois group
function PossibleBlockSizes(Patterns)
 ls := {&+a : a in Patterns};
 assert #ls eq 1; 
 n := Representative(ls);
 if IsPrime(n) then // No subfields possible
  return [], n;
 end if;

// All patterns that are generated from the above
 p_seq := SetToSequence(Patterns);
 prod_seq := [LCM(a) : a in p_seq];
 GenPatterns := { PowerPattern(p_seq[i],b) : i in [1..#p_seq], b in [1..n] | prod_seq[i] mod b eq 0};
 GenPatterns := [ a : a in GenPatterns | 1 in a]; // can only use patterns with fixed points 
 
 di := Divisors(n);
 di := {a : a in di | not a in {1,n}};

// First stage: A fixed point leads to a fixed block:
 for act in GenPatterns do
  e1 := Index(act,1);
  if e1 gt 0 then  // if we have a fixed point
   b := Remove(act,e1);
   s_sum := {1};
   for tmp in b do
    s_sum := s_sum join {tmp + c : c in s_sum};
   end for; 
// s_sum sizes of fixed sets that contain a fixed point
   di := di meet s_sum; // Only these can be block-sizes
   if #di eq 0 then return [],n; end if;
  end if;
 end for;

// Second stage: In case we have blocks consisting only of fixed points
 for act in GenPatterns do
  if Set(act) ne {1} then  
   m := Min({a : a in act | a gt 1});
   fc := #[a : a in act | a eq 1];
   di := {a : a in di | (a ge m) or (fc mod a eq 0)}; 
   if #di eq 0 then return [],n; end if;
  end if;
 end for;
 
 return Sort(SetToSequence(di)),n;
end function;

// List of possible degrees of subfields is case we have the pattern-list Patterns modulo various primes
// This means other degrees are impossible. The listed degrees have to inspected more closely. 
function PossibleProperSubfieldDegrees(Patterns)

 assert #Patterns gt 0;
 e1,e2 := PossibleBlockSizes(Patterns);
 
 return Sort([e2 div a : a in e1]);
end function;


/* The result is returned by changing atributes of s */
procedure FindPrime(p, s : full := true, with_linear := false)
  if assigned s`UseGalois then
    return;
  end if;
  if not ISA(Type(p), RngElt) then
    p := Minimum(p);
  end if;
//"0 : ", p;
  K := s`Top;
  k := CoefficientField(K);
  if assigned s`Prime then
    delete s`Prime;
  end if;
  if #s`Fields gt 1 then
      full := true;
  end if;

  D := Lcm([Denominator(k!x) : x in Eltseq(DefiningPolynomial(K))]);
  D := Lcm([D, Integers()!Norm(Numerator(k!LeadingCoefficient(DefiningPolynomial(K))))]);
  D := Lcm(D, Denominator(1/Evaluate(Derivative(DefiningPolynomial(K)), K.1)));
//D;
  cycletypes := {};
  repeat
    p := NextPrime(p);
//Valuation(D, p);
//D mod p;
    if D mod p eq 0 then
//"1 :", p;
      continue;
    end if;
    d := 1;
    for i in [2..#s`Fields] do
      h := Eltseq(K!s`Fields[i][1].1);
      d := Lcm([Denominator(x) : x in h]);
      if d mod p eq 0 then
        break;
      end if;
    end for;
    if d mod p eq 0 then
//"2 :", p;
      continue;
    end if;

    if with_linear then
	assert Type(k) eq FldRat;
	Fpt := PolynomialRing(GF(p)); t := Fpt.1;
	if Gcd(t^p - t, Fpt!DefiningPolynomial(K)) eq 1 then
	    continue;
	end if;
    end if;
    
    if Type(k) eq FldRat then
      lp := [p];
    else
      lp := [ x : x in Support(MaximalOrder(k)*p)];
      //lp := [x[1] : x in Decomposition(MaximalOrder(k), p)];
    end if;
    for P in lp do
      C, cm := Completion(k, P);
      if Type(P) eq RngIntElt then
        R := GF(P);
        mR := hom<Rationals() -> R|>;
      else
        R, mR := ResidueClassField(Integers(C));
	mR := cm*mR;
      end if;
      f := Polynomial([x@mR : x in Eltseq(DefiningPolynomial(K))]);
      lf := Factorisation(f);
      if exists{x : x in lf | x[2] ne 1} then
        continue;
      end if;
      degs := [Integers() | Degree(x[1]) : x in lf];
      Include(~cycletypes, degs);
//P;
//[Degree(x[1]) : x in lf];
      lf := Lcm(degs);
//lf;
      if lf gt 1+Degree(K)/2 then continue; end if;
      
      if not full then
	s`Prime := <P, mR, 0, 0, C, cm>;
	if #PossibleProperSubfieldDegrees(cycletypes) eq 0 then
            vprint Subfields,1:"No subfields by shape test.";
	    s`Complete := true;
	    s`GeneratingComplete := true;
	end if;
	return;
      end if;

      C := Integers(ext<C | lf>);
      //RR := ext<R|lf>;
      RR := ResidueClassField(C);
      r := Roots(f, RR);
      assert #r eq Degree(f);
      assert forall{x : x in r | x[2] eq 1};
      r := [x[1] : x in r];
      // Store map into the completion from RR in here
      s`Prime := <P, mR, RR, r, C, cm>;
      s`Fields[1][2] := {{i} : i in [1..#r]};
      redo := false;
      for i in [2..#s`Fields] do
        if Discriminant(Polynomial(
          [x @ s`Prime[2] : x in Eltseq(DefiningPolynomial(s`Fields[i][1]))]))
            eq 0 then
          redo := true;
	  delete s`Prime;
          break;
        end if;
        h := s`Top!s`Fields[i][1].1;
        h := Eltseq(h);
        h := Polynomial([s`Prime[2](x) : x in h]);
        B := [ Evaluate(h, x) :x in s`Prime[4]];
        B := { { i : i in [1..#B] | B[i] eq r} : r in Set(B)};
        assert #B eq Degree(s`Fields[i][1]);
        assert forall{x : x in B | #x eq 
                  Degree(s`Top) div Degree(s`Fields[i][1])};
        s`Fields[i][2] := B;
      end for;
      if redo then
      //"redo";
        continue;
      end if;
      break;
    end for;
  until assigned s`Prime;

    if #PossibleProperSubfieldDegrees(cycletypes) eq 0 then
        vprint Subfields,1:"No subfields by shape test.";
	s`Complete := true;
	s`GeneratingComplete := true;
    end if;
end procedure;

function lattice_create(K)

  s := {1};
  AddAttribute(SetEnum, "Graph");
  AddAttribute(SetEnum, "Fields");
  AddAttribute(SetEnum, "Complete");
  AddAttribute(SetEnum, "GeneratingComplete");
  AddAttribute(SetEnum, "Top");
  AddAttribute(SetEnum, "Prime");
  AddAttribute(SetEnum, "UseGalois");
  AddAttribute(SetEnum, "Roots");
  AddAttribute(SetEnum, "max_comp");
  AddAttribute(SetEnum, "EquationOrder");
  AddAttribute(SetEnum, "FOF(EquationOrder)");

  s`Top := K;
  s`Graph := Digraph<1|  : SparseRep>;
  s`Complete := false;  
  s`GeneratingComplete := false;
  s`Fields := [*<K, {{1}}>*];

  K`SubfieldLattice := s;

  return s;

end function;

/*
Make sure once the lattice is constructed the prime information is NOT 
overwritten
Why : Because L`Roots could then be in an incompatible ring and the coercions
into L`UseGalois`Base will no longer work since the finite fields will have been
constructed independantly even if they look the same
This is why I moved the assigned K`SubfieldLattice check out of lattice_create!
*/

intrinsic InternalGaloisSubfieldLatticeCreate(K::FldFun[FldFunRat], S::GaloisData) -> SetEnum
  {}
  if assigned K`SubfieldLattice then
    return K`SubfieldLattice;
  end if;
  s := lattice_create(K);

  s`UseGalois := S;
    k := CoefficientRing(K);
    // defined over the standard rational
    if Type(k) eq FldFun then
	k := FieldOfFractions(CoefficientRing(EquationOrderInfinite(K)));
    end if;
    if Characteristic(K) eq 0 then
	R := ext<CoefficientRing(k) | S`Prime>;
    else
	R := CoefficientRing(S`Base);
	if not assigned S`Roots then
	    S`GetRoots(S);
	end if;
    end if;
    mIR := hom<Integers(k) -> R | R.1>;
    mIRi := hom<R -> Integers(k) | Integers(k).1>;
    mR := map<k -> R | x :-> mIR(Numerator(x))/mIR(Denominator(x)), y :-> y @ mIRi>;
    RR, mRR := ResidueClassField(S`Ring);
    f := DefiningPolynomial(K);
    if Characteristic(K) eq 0 then
	f := Polynomial([S`BaseMap(x, <1, 1>) : x in Coefficients(f)]);
	RR := ResidueClassField(Integers(RR));
    else
	f := Polynomial([S`BaseMap(x, 1) : x in Coefficients(f)]);
    end if;
    f := Polynomial([mRR(x) : x in Coefficients(f)]);
    assert Degree(f) eq Degree(K);
    f := Polynomial(RR, f);
    assert Degree(f) eq Degree(K);
/*
DefiningPolynomial(K);
Parent(f);
f;
RR;
S`Ring!RR.1;
[S`Ring!x[1] : x in Roots(f, RR)];
*/
    if not assigned S`Roots then
	S`GetRoots(S);
    end if;
    s`Prime := <S`Prime, mR, RR, S`Roots, S`Ring>;
    if assigned S`CycleTypes and #S`CycleTypes gt 0 and #PossibleProperSubfieldDegrees(S`CycleTypes) eq 0 then
        vprint Subfields,1: "No subfields by shape test.";
	s`Complete := true;
	s`GeneratingComplete := true;
    end if;
  return s;
end intrinsic;

intrinsic InternalGaloisSubfieldLatticeCreate(K::FldFun[FldFun[FldFunRat]], S::GaloisData) -> SetEnum
  {}
  if assigned K`SubfieldLattice then
    return K`SubfieldLattice;
  end if;

  s := lattice_create(K);

  s`UseGalois := S;
    k := CoefficientRing(K);
    if Characteristic(K) eq 0 then
	R := ext<CoefficientRing(k) | S`Prime>;
    else
	// This is the residue class field of S`Prime
	R := CoefficientRing(S`Base);
	if not assigned S`Roots then
	    S`GetRoots(S);
	end if;
    end if;
    mR := map< k -> R | x :-> Evaluate(x, Place(S`Prime))>;
    RR, mRR := ResidueClassField(S`Ring);
    f := DefiningPolynomial(K);
    if Characteristic(K) eq 0 then
	f := Polynomial([S`BaseMap(x, <1, 1>) : x in Coefficients(f)]);
	RR := ResidueClassField(Integers(RR));
    else
	f := Polynomial([S`BaseMap(x, 1) : x in Coefficients(f)]);
    end if;
    /*
    Why do we compute this when we don't use it?
    f := Polynomial([mRR(x) : x in Coefficients(f)]);
    assert Degree(f) eq Degree(K);
    f := Polynomial(RR, f);
    assert Degree(f) eq Degree(K);
    */
/*
DefiningPolynomial(K);
Parent(f);
f;
RR;
S`Ring!RR.1;
[S`Ring!x[1] : x in Roots(f, RR)];
*/
    if not assigned S`Roots then
	S`GetRoots(S);
    end if;
    s`Prime := <S`Prime, mR, RR, S`Roots, S`Ring>;
    if assigned S`CycleTypes and #S`CycleTypes gt 0 and #PossibleProperSubfieldDegrees(S`CycleTypes) eq 0 then
        vprint Subfields,1:"No subfields by shape test.";
	s`Complete := true;
	s`GeneratingComplete := true;
    end if;
  return s;
end intrinsic;

import "../GaloisGrp/GalFldFun.m" : first_prime, next_prime, get_primes, get_primes_rel;

intrinsic InternalGaloisSubfieldLatticeCreate(K::FldFun) -> SetEnum
  {}
    // just need a prime, doesn't have to be one that is good for 
    // Galois group computations
    C := CoefficientRing(K);
    // defined over the standard rational
    if Type(C) eq FldFun then
	C := FieldOfFractions(CoefficientRing(EquationOrderInfinite(K)));
    end if;
    prime := first_prime(BaseRing(C));
    f := DefiningPolynomial(K);
    f := Polynomial(C, f);
    _df := Denominator(1/Evaluate(Derivative(f), K.1), MaximalOrderFinite(K));

    primes, min_deg := get_primes(f, Degree(f), []);

    for prime in primes do
	if Characteristic(K) eq 0 then
	    S := InternalGalQt_ComputeRoots(f, prime[1], <1, 1>);
	else
	    S := InternalGalFqt_setup(Polynomial(C, f), prime[1], 1);
	end if;
	if S cmpne false then
	    break;
	end if;
    end for;

    assert S cmpne false and Valuation(_df, S`Prime) eq 0;
    return InternalGaloisSubfieldLatticeCreate(K, S);
end intrinsic;

intrinsic InternalGaloisSubfieldLatticeCreate(K::FldFun[FldFun]) -> SetEnum
  {}
    // just need a prime, doesn't have to be one that is good for 
    // Galois group computations
    prime := first_prime(BaseRing(BaseRing(CoefficientRing(K))));
    f := DefiningPolynomial(K);
    _df := Denominator(1/Evaluate(Derivative(f), K.1), MaximalOrderFinite(K));
    C := CoefficientRing(K);

    primes, min_deg := get_primes_rel(f, Degree(f), []);

    for prime in primes do
	if Characteristic(K) eq 0 then
	    S := InternalGalQt_ComputeRoots(f, prime[1], <1, 1>);
	else
	    S := InternalGalFqt_setup(Polynomial(C, f), prime[1], 1);
	end if;
	if S cmpne false then
	    break;
	end if;
    end for;

    return InternalGaloisSubfieldLatticeCreate(K, S);
end intrinsic;

intrinsic InternalGaloisSubfieldLatticeCreate(K::FldNum) -> SetEnum
  {}
  if assigned K`SubfieldLattice then
    return K`SubfieldLattice;
  end if;

  s := lattice_create(K);
  p := Degree(K);
  FindPrime(p, s);
  return s;
end intrinsic;

function Subset(s, k ,K)
  return forall{x : x in s`Fields[K][2] | exists{y : y in s`Fields[k][2] | x subset y}};
end function;

function Meet(B12)
  B := {};
  A := &join B12;
  while A ne {} do
    r := Representative(A);
    Exclude(~A, r);
    b := {r};
    repeat
      finish := true;
      if exists(r){r : r in B12 | r meet b ne {}} then
        finish := false;
	b join:= r;
	Exclude(~B12, r);
	A diff:= r;
      end if;
    until finish;
    Include(~B, b);
  end while;
  return B;
end function;

function Meet_Fld(s, k, K)
    B12 := s`Fields[k][2] join s`Fields[K][2];
    return Meet(B12);
end function;

function GetBlock(S, h_in)
/* 
h_in is a function field element in the top function field 
(and probably in a subfield too but it has been mapped into the top)
*/
      h := h_in;
      h := Eltseq(h);
      if Type(Universe(h)) eq FldFun then
	  R := RationalExtensionRepresentation(Universe(h));
	  d := Lcm([Denominator(R!x, EquationOrderFinite(R)) : x in h]);
      else
	  d := Lcm([Denominator(x) : x in h]);
      end if;
      h := [x*d :x in h];
      pr := 3;
      B := {};
      repeat
	last_B := B;
        pr +:= 1;
	if Characteristic(S`Ring) eq 0 then
            u_pr := <pr, 2*pr>;
        else
            u_pr := pr;
        end if;
        hh := Polynomial([S`BaseMap(x, u_pr) : x in h]);
        _ := GaloisRoot(1, S:Prec := u_pr);
        r := [ChangePrecision(x, u_pr) : x in S`Roots];
	//assert #Set(r) eq #r;
	assert #Set(S`Roots) eq #S`Roots;
	if false and assigned S`f then //CF: why is this assertion correct?
	    assert &and [RelativePrecision(Evaluate(Polynomial([S`BaseMap(c, u_pr) : c in Coefficients(S`f)]), x)) eq 0 : x in r];
	end if;
        /*CF: note, we cannot use GaloisRoot here we have to use S`Roots.
          * Reason: if S`Scale is set (because S`f = DefiningPolynomial(s`Top)
          * is non-monic, non-integral) then GaloisRoot returns a root
          * of S`f * Scale. On the other hand, the embedding of K into 
          * s`Top (via h) is given in terms of the primitive element of 
          * s`Top thus a "proper", unscaled root.
          */
        if assigned S`Permutation then
          r := PermuteSequence(r, S`Permutation);
        end if;
        B := [ Evaluate(hh, x) :x in r];
	if Characteristic(S`Ring) eq 0 then
	    B := [ChangePrecision(x, pr) : x in B] where
	      pr := <x,x> where x := Minimum([Precision(x)[1] : x in r]);
	else
	    B := [ChangePrecision(x, pr) : x in B] where
	      pr := x where x := Minimum([Precision(x) : x in r]);
	end if;
        B := { { i : i in [1..#B] | B[i] eq r} : r in Set(B)};
//        if #B ne Degree(K) then "LOOP\n\tLOOP\n\t\tLOOP\n\tLOOP\nLOOP";end if;
        if pr gt 10 then error "too much looping"; end if;
      // all blocks have same length
      // block has same length as at lower precision
      until #{#b : b in B} eq 1 and #B eq #last_B;
      assert #B eq Degree(MinimalPolynomial(h_in));

      return B;
end function;

function BlockComposite(blocks)
    B := Rep(blocks);
    Exclude(~blocks, B);
    for b in blocks do
	B := {BB meet bb : BB in B, bb in b};
	B := {BB : BB in B | #BB gt 0};
	// all blocks have same length
	assert #{#BB : BB in B} eq 1;
    end for;
    return B;
end function;

intrinsic InternalGaloisSubfieldLatticeAddField(s::SetEnum, mK::Map[FldFun, FldFun]:B := false) -> BoolElt, .
  {} 
  K := Domain(mK);
  if exists(x){x : x in s`Fields | x[1] cmpeq K} then
    return false, x[2];
  end if;
  assert assigned s`UseGalois;
  S := s`UseGalois;
//"AddField";
  if B cmpeq false then
      h := mK(K.1);
      B := GetBlock(S, h);
  end if;    
  assert #B eq Degree(K);
  assert forall{x : x in B | #x eq Degree(s`Top) div Degree(K)};

//"AddField out";
  if exists{x : x in s`Fields | x[2] eq B} then
    return false, B;
  end if;
  AddVertex(~s`Graph, #s`Fields+1);
  Append(~(s`Fields), <K, B>);
  for i in [1..#s`Fields-1] do
    if Subset(s, #s`Fields, i) then
      AddEdge(~(s`Graph), i, #s`Fields);
    end if;
    if Subset(s, i, #s`Fields) then
      AddEdge(~(s`Graph), #s`Fields, i);
    end if;
  end for;
  return true, B;
end intrinsic;

intrinsic InternalGaloisSubfieldLatticeAddField(s::SetEnum, K::FldFun:B := false) -> BoolElt, .
  {} 
    return InternalGaloisSubfieldLatticeAddField(s, Coercion(K, s`Top));
end intrinsic;

function BlockFromPrimitiveElement(s, elt, deg)
    K := Parent(elt);
    h := s`Top!elt;
    h := Eltseq(h);
    p := s`Prime[1];
    if not ISA(Type(p), RngElt) then
	p := Minimum(p);
    end if;
    vprint Subfields, 3 : "p = ", p;
    prime_changed := false;
    while exists{x : x in h | Valuation(Denominator(x), p) lt 0} or
		    LeadingCoefficient(DefiningPolynomial(K))@s`Prime[2] eq 0 or
		    Discriminant(Polynomial([x @ s`Prime[2] : 
				  x in Eltseq(DefiningPolynomial(K))])) eq 0  do
	FindPrime(s`Prime[1], s); 
	prime_changed := true;
	p := s`Prime[1];
	if not ISA(Type(p), RngElt) then
	    p := Minimum(p);
	end if;
    end while; 
    if prime_changed then
        vprint Subfields, 3 : "Changed Prime to ", s`Prime[1];
        vprint Subfields, 3 : "Now change blocks";
	// top field is always the first element
	for i in [2 .. #s`Fields] do
	    s`Fields[i][2] := BlockFromPrimitiveElement(s, s`Fields[i][1].1, Degree(s`Fields[i][1]));
	end for;
	/* need to redo S`Roots */
	if assigned s`Roots then
	    delete s`Roots;
	end if;
    end if;

    hp := Polynomial([s`Prime[2](x) : x in h]);
    t := PolynomialRing(Integers()).1;
    repeat
	B := [ Evaluate(hp, Evaluate(t, x)) :x in s`Prime[4]];
	B := { { i : i in [1..#B] | B[i] eq r} : r in Set(B)};
	// blocks should have the same length
	// if not : try another prime, more precision, tschirni or different element
	t +:= 1;
    until #{#b : b in B} eq 1 and (#B eq deg or TrailingCoefficient(t) gt Max(5, deg));
    if #B ne deg then
	return false;
    end if;
    return B;
end function;

intrinsic InternalGaloisSubfieldLatticeAddField(s::SetEnum, K::FldNum:B := false) -> BoolElt, .
  {} 
  if exists(x){x : x in s`Fields | x[1] eq K} then
    return false, x[2];
  end if;
  if B cmpeq false then
    B := BlockFromPrimitiveElement(s, K.1, Degree(K));
  end if;
  assert B cmpne false;
  assert #B eq Degree(K);
  assert forall{x : x in B | #x eq Degree(s`Top) div Degree(K)};

  if exists{x : x in s`Fields | x[2] eq B} then
    return false, B;
  end if;
  AddVertex(~s`Graph, #s`Fields+1);
  Append(~(s`Fields), <K, B>);
  for i in [1..#s`Fields-1] do
    if Subset(s, #s`Fields, i) then
      AddEdge(~(s`Graph), i, #s`Fields);
    end if;
    if Subset(s, i, #s`Fields) then
      AddEdge(~(s`Graph), #s`Fields, i);
    end if;
  end for;
  return true, B;
end intrinsic;

intrinsic InternalGaloisSubfieldLatticeFindField(s::SetEnum, mK::Map[FldFun, FldFun]) -> RngIntElt, {}
  {}
  K := Domain(mK);
  if exists(x){x : x in [1..#s`Fields] | s`Fields[x][1] cmpeq K} then
    return x, s`Fields[x][2];
  end if;
  assert assigned s`UseGalois;
  S := s`UseGalois;

  h := mK(K.1);
  assert Evaluate(DefiningPolynomial(K), h) eq 0;
  h := Eltseq(h);
  pr := 1;
  repeat
    if Characteristic(K) eq 0 then
	hh := Polynomial([S`BaseMap(x, <pr, 2*pr>) : x in h]);
	_ := GaloisRoot(1, S:Prec := <pr, 2*pr>);
	r := [ChangePrecision(x, <pr, 2*pr>) : x in S`Roots];
    else 
	hh := Polynomial([S`BaseMap(x, pr) : x in h]);
	_ := GaloisRoot(1, S:Prec := pr);
	r := [ChangePrecision(x, pr) : x in S`Roots];
    end if;
    /*CF: note, we cannot use GaloisRoot here we have to use S`Roots.
      * Reason: if S`Scale is set (because S`f = DefiningPolynomial(s`Top)
      * is non-monic, non-integral) then GaloisRoot returns a root
      * of S`f * Scale. On the other hand, the embedding of K into 
      * s`Top (via h) is given in terms of the primitive element of 
      * s`Top thus a "proper", unscaled root.
      */
    B := [ Evaluate(hh, x) :x in r];
    B_ev := B;
    B := { { i : i in [1..#B] | B[i] eq r} : r in Set(B)};
    pr *:= 2;
    if pr gt 20 then error "too much prec here"; end if;
    assert #B le Degree(K);
  until #B eq Degree(K);
  assert #B eq Degree(K);
  assert forall{x : x in B | #x eq Degree(s`Top) div Degree(K)};
  if exists(x){x : x in [1..#s`Fields] | s`Fields[x][2] eq B} then
    return x, B;
  else
    require false : "error errror errrror";
  end if;

end intrinsic;

intrinsic InternalGaloisSubfieldLatticeFindField(s::SetEnum, K::FldFun) -> RngIntElt, {}
  {}
    return InternalGaloisSubfieldLatticeFindField(s, Coercion(K, s`Top));
end intrinsic;

intrinsic InternalGaloisSubfieldLatticeFindField(s::SetEnum, K::FldNum) -> RngIntElt, {}
  {}
  if exists(x){x : x in [1..#s`Fields] | s`Fields[x][1] eq K} then
    return x, s`Fields[x][2];
  end if;
  h := s`Top!K.1;
  h := Eltseq(h);
  p := s`Prime[1];
  if not ISA(Type(p), RngElt) then
    p := Minimum(p);
  end if;
  while exists{x : x in h | Valuation(Denominator(x), p) lt 0} or
        Discriminant(Polynomial([x @ s`Prime[2] :
                      x in Eltseq(DefiningPolynomial(K))])) eq 0  do
    FindPrime(s`Prime[1], s);
  end while;

  h := Polynomial([s`Prime[2](x) : x in h]);
  B := [ Evaluate(h, x) :x in s`Prime[4]];
  B := { { i : i in [1..#B] | B[i] eq r} : r in Set(B)};
  assert #B eq Degree(K);
  assert forall{x : x in B | #x eq Degree(s`Top) div Degree(K)};
  if exists(x){x : x in [1..#s`Fields] | s`Fields[x][2] eq B} then
    return x, B;
  else
    require false : "error errror errrror";
  end if;

end intrinsic;

intrinsic InternalGaloisSubfieldLatticeGetField(s::SetEnum, i::RngIntElt) -> Fld
  {}
  z := s`Fields[i][1];
  if ISA(Type(z), Map) then
    return Domain(z);
  else
    return z;
  end if;
end intrinsic;

intrinsic InternalGaloisSubfieldLatticeGetFieldMap(s::SetEnum, i::RngIntElt) -> Fld
  {}
  z := s`Fields[i][1];
  if ISA(Type(z), Map) then
    return z;
  else
    return map<z -> s`Top|x :-> s`Top!x>;
  end if;
end intrinsic;


intrinsic InternalGaloisSubfieldLatticeMaximalSubfields(s::SetEnum, i::RngIntElt) -> []
  {}
  V := VertexSet(s`Graph);
  su := OutNeighbours(V!i);
  if #su eq 0 then
    return [];
  end if;
  S, VV := sub<s`Graph| su join {V!i}>;
  ssu := [];
  for i in su do
    I := VV!i;
    if #InNeighbours(I) eq 1 then
      Append(~ssu, i);
    end if;
  end for;
  return [ Index(i) : i in ssu];
end intrinsic;

intrinsic InternalGaloisSubfieldLattice(K::FldFun, S::GaloisData:Current := false) -> SetEnum
  {}
  s := InternalGaloisSubfieldLatticeCreate(K, S);
  ss := Subfields(K);
  for x in ss do
    _ := InternalGaloisSubfieldLatticeAddField(s, x[2]);
  end for;
  s`Complete := false;
  return s, ss;
end intrinsic;

function lattice(K, ss)
  s := InternalGaloisSubfieldLatticeCreate(K);
  for x in ss do
    _ := InternalGaloisSubfieldLatticeAddField(s, x[1]);
  end for;
  return s;
end function;

intrinsic InternalGaloisSubfieldLattice(K::FldFun : Current := false) -> SetEnum
{}
    ss := Subfields(K);
    s := lattice(K, ss);
    return s, ss;
end intrinsic;

intrinsic InternalGaloisSubfieldLattice(K::FldNum:Current := false) -> SetEnum
  {}
  ss := Subfields(K:Current := Current);
  s := lattice(K, ss);
  if Type(CoefficientField(K)) eq FldRat and not Current then
    s`Complete := true;
  end if;
  return s, ss;
end intrinsic;

intrinsic InternalGaloisSubfieldLatticeIsComplete(s::SetEnum) -> BoolElt
  {}
  return s`Complete;
end intrinsic;

intrinsic InternalGaloisSubfieldLatticeSubset(B1::{}, B2::{}) -> BoolElt
  {}
  return forall{x : x in B2 | exists{y : y in B1 | x subset y}};
end intrinsic;

intrinsic InternalGaloisSubfieldLatticeMeet(B1::{}, B2::{}) -> BoolElt
  {}
  return Meet(B1 join B2);
end intrinsic;

intrinsic InternalGaloisSubfieldLatticeFindField(s::SetEnum, B::{}) -> RngIntElt
  {}
  return Position([x[2] : x in s`Fields], B);
end intrinsic;

intrinsic InternalGaloisSubfieldLatticeSubset(s::SetEnum, i::RngIntElt, j::RngIntElt) -> BoolElt
  {}
  return Subset(s, i, j);
end intrinsic;

intrinsic InternalGaloisSubfieldLatticeSubset(s::SetEnum, mK::Map[FldFun, FldFun], mF::Map[FldFun, FldFun]) -> BoolElt
  {}
  return Subset(s, InternalGaloisSubfieldLatticeFindField(s, mK), InternalGaloisSubfieldLatticeFindField(s, mF));
end intrinsic;


intrinsic InternalGaloisSubfieldLatticeSubset(s::SetEnum, K::FldNum, F::FldNum) -> BoolElt
  {}
  return Subset(s, InternalGaloisSubfieldLatticeFindField(s, K), InternalGaloisSubfieldLatticeFindField(s, F));
end intrinsic;

intrinsic InternalGaloisSubfieldLatticeTop(s::SetEnum) -> RngIntElt
  {}
  return 1;
end intrinsic;

intrinsic InternalGaloisSubfieldLatticePrint(s::SetEnum)
  {}
  "Number of fields", #s`Fields;
  "Fields:", [x[1] : x in s`Fields];
end intrinsic;

intrinsic InternalSubfieldLatticeGetGeneratingSubfields(s::SetEnum)->SeqEnum
{}
    n := Degree(s`Top);
    g := [];
    for S in s`Fields do
	if n eq Degree(S[1]) then
	    continue;
	end if;
	if IsPrime(n div Degree(S[1])) then 
	    Append(~g, S[1]);
	else
	    c := [sf[2] : sf in s`Fields | sf ne S and InternalGaloisSubfieldLatticeSubset(S[2], sf[2])];
	    c := Meet(&join c);
	    if c ne S[2] then
		Append(~g, S[1]);
	    end if;
	end if;
    end for;

    return g;
end intrinsic;
