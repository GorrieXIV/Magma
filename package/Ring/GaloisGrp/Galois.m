freeze;

declare attributes GaloisData : Scale, SubfieldLattice, KnownSubgroup,
                                Bound, Time, Maps, MinPrec;
declare attributes FldNum  : GaloisData;
declare attributes GrpPerm : Blocks, Sub2;
declare attributes GSet: WreathS1, WreathS2, WreathD,  WreathD,
                              WreathSm, WreathDSm, RelG, SubG;

import "GalInvar.m" : SLPRGg;

import "Shapes.m" : PossibleBlockSizes, PossibleOrbitSizesOnTwoSets, ScCostEst, IsSnAn;

// Control sieving in GenericStauduhar. Turn sieve of for better testing.
UseSieve := true or IsExport();

//currently not really used. It determines if the function check 
//computes the multivariate polynomial for invariance checks or just tries to
//evaluate at random points...
cheat := true;

//max_cost is the cut-off point for the old generic invariant computation.
//If more than max_cost monomials have to be considered, 
//we use the new method.
max_cost := 250000;
//max_cost := 0000;

// DEFAULT_MAX_PREC is the cut off for precision: if we need more
// than DEFAULT_MAX_PREC, then we assume the decent fails...
DEFAULT_MAX_PREC := Infinity();

//triggers the use of factorisation (over Z_p) for the computation of roots.
UseFactor :=  not true;
//decides if adaptive invariants or classical invariants are used
Classical := false;
 
//decides how expensive the inner invariant in BlockQuotients is allowed to be
MaxInnerInvar := Infinity();
//cut-off for ShortCosets
MaxShortCosets := 50;

// for colorized output...(changes the background color)
if not IsIOWrapped() then
  red := "[41m";
  green := "[42m";
  RED := "[43m";
  blue := "[44m";
  purple := "[45m";
  BLUE := "[46m";
  grey := "[47m";
  normal := "[49m";
else
  red := "";
  green := "";
  RED := "";
  blue := "";
  purple := "";
  BLUE := "";
  grey := "";
  normal := "";
end if;

color_array := [red, green, RED, blue, purple, BLUE, grey, normal];

function _MaxSub_(X:IsTransitive := false)
  vprint GaloisGroup, 3: "Calling maximal subgroups on", X:Magma;
  return MaximalSubgroups(X: IsTransitive := IsTransitive);
end function;

function shallow_copy(G)
  return sub<Sym(Degree(G))|GeneratorsSequence(G)>;
end function;

AddAttribute(RngInt, "UseCache");
AddAttribute(RngInt, "CacheLevel");
AddAttribute(RngInt, "Invar");
AddAttribute(RngInt, "Group");

AddAttribute(RngInt, "Error");
intrinsic PutInZ(A) -> RngIntElt
  {}
  Z := Integers();
  if assigned Z`Error then
    Append(~Z`Error, A);
  else
    Z`Error := [*A*];
  end if;
  return #Z`Error;
end intrinsic;

_Cache:= Random(2^30);
_Z := Integers();
__Cache := ideal<_Z|_Cache>;

function _GetGaloisCacheLevel()
  return ideal<_Z|_Cache>`CacheLevel;
end function;

procedure _SetGaloisCacheLevel(l)
  Cache := ideal<_Z|_Cache>;
  Cache`CacheLevel := l;
  if l gt 0 then
    Cache`UseCache := true;
  else
    Cache`UseCache := false;
  end if;
end procedure;

function UseCache() 
  Cache := ideal<_Z|_Cache>;
  return Cache`UseCache;
end function;

_SetGaloisCacheLevel(0);

inv_fmt := recformat<G:GrpPerm, H:GrpPerm,
                     I:UserProgram,
                     c:RngIntElt>;  
ci_fmt := recformat<Hashes, invs>;

function CacheHasInvar(G,H)
  Cache := ideal<_Z|_Cache>;
  if not assigned Cache`Invar then
    return false, _;
  else
    ci := Cache`Invar;
  end if;
  
  if <G,H> in ci`Hashes then
    p := Position(ci`Hashes, <G, H>);
    assert ci`invs[p]`G eq G and ci`invs[p]`H eq H;
    ci`invs[p]`c +:=1;
    Cache`Invar := ci;
    return true, ci`invs[p]`I;
  end if;
  return false, _;
end function;

procedure CachePutInvar(G, H, I)
  Cache := ideal<_Z|_Cache>;
  if assigned Cache`Invar then
    ci := Cache`Invar;
  else
    ci := rec<ci_fmt|Hashes := {@@}, invs := []>;
  end if;
  if <G, H> in ci`Hashes then
    p := Position(ci`Hashes, <G, H>);
    assert ci`invs[p]`G eq G and ci`invs[p]`H eq H;
    ci`invs[p]`I := I;
  else
    Include(~ci`Hashes, <G, H>);
    Append(~ci`invs, rec<inv_fmt| G := G, H := H, I := I, c := 0>);
  end if;
  Cache`Invar := ci;
  return;
end procedure;

forward GaloisRootAddPermutation;

procedure CacheNormalise(~G, S)
  if Degree(G) le 23 then
    H := TransitiveGroup(a,b) where b,a := TransitiveGroupIdentification(G);
    fl, p := MyIsConjugate(Sym(Degree(G)), H, G);
    assert H^p eq G;
    GaloisRootAddPermutation(S, p);
    G := H;
  end if;
end procedure;


grp_fmt := recformat<G:GrpPerm, S,
                     c:RngIntElt>;  
gi_fmt := recformat<Hashes, grps>;


function CacheHasGroup(G)
  Cache := ideal<_Z|_Cache>;
  if not assigned Cache`Group then
    return false, _;
  else
    ci := Cache`Group;
  end if;
  
  if G in ci`Hashes then
    p := Position(ci`Hashes, G);
    assert ci`grps[p]`G eq G;
    ci`grps[p]`c +:=1;
    Cache`Group := ci;
    return true, ci`grps[p]`S;
  end if;
  return false, _;
end function;

procedure CachePutGroup(G, S)
  Cache := ideal<_Z|_Cache>;
  if assigned Cache`Group then
    ci := Cache`Group;
  else
    ci := rec<gi_fmt|Hashes := {@@}, grps := []>;
  end if;
  if G in ci`Hashes then
    error "should not happen";
  else
    Include(~ci`Hashes, G);
    Append(~ci`grps, rec<grp_fmt| G := G, S := S, c := 0>);
  end if;
  Cache`Group := ci;
  "added group";
  return;
end procedure;

intrinsic InternalPrintGroupIdentification(G::GrpPerm) -> MonStgElt
{Transitive group identification as a string.}

 try 
  id1,id2 := TransitiveGroupIdentification(G); suc := true; catch e; suc := false; 
 end try;
 if suc then
  return Sprintf("TGI: %oT%o",id2,id1);
 end if;
 return "group above database limit";
end intrinsic;

function TestAllPartitions(G)
  local   L, par, par1, f, Im, ker;

  L:=AllPartitions(G);
  L := Sort(SetToSequence(L), func<a,b | #a - #b>);
  L:=[MinimalPartition(G:Block:=x): x in L]; // convert block to blocksystem
  for par in L do
    f, Im, ker:= BlocksAction(G, par);
    par1:=Random(Set(par));
    sub:=OrbitImage(Stabilizer(G,par1),par1);
    vprintf GaloisGroup, 2: "Subfield: %13o rel:%13o\n", InternalPrintGroupIdentification(Im)
                                                   , InternalPrintGroupIdentification(sub);
  end for;
  return true;
end function;

intrinsic WeakValuation(x::RngSerLaurElt[FldPad]) -> RngIntElt
  {}
  a,b,c := Eltseq(x);
  i := 1;
  for i := 1 to #a do
    if not IsWeaklyZero(a[i]) then
      return b+i-1, Minimum([Valuation(a[x]) : x in [1..i]] cat [0]);;
    end if;
  end for;
  return b+#a, Minimum([Valuation(a[x]) : x in [1..#a]]);
end intrinsic;


intrinsic WeakValuation(x::RngSerPowElt[FldPad]) -> RngIntElt
  {}
  a,b,c := Eltseq(x);
  i := 1;
  for i := 1 to #a do
    if not IsWeaklyZero(a[i]) then
      return b+i-1, Minimum([Valuation(a[x]) : x in [1..i]] cat [0]);;
    end if;
  end for;
  return b+#a, Minimum([Valuation(a[x]) : x in [1..#a]]);
end intrinsic;

intrinsic WeakValuation(x::FldReElt) -> RngIntElt
  {}
  if IsWeaklyZero(x) then
    return Infinity();
  end if;
  return -Log(Abs(x));
end intrinsic;
intrinsic WeakValuation(x::FldComElt) -> RngIntElt
  {}
  if IsWeaklyZero(x) then
    return Infinity();
  end if;
  return -Log(Abs(x));
end intrinsic;
 
intrinsic WeakValuation(x::RngElt) -> RngIntElt
  {}
  if IsWeaklyZero(x) then
    return Infinity();
  end if;
  return Valuation(x);
end intrinsic;
    

intrinsic IsInt(x::RngElt, B::RngElt, S::GaloisData:EasyNonInt := false,Epsilon := false) -> BoolElt, RngElt
  {}
  if Type(x) eq RngIntElt then
    error "the int here implies that block-quotient found a wrong invariant";
    return false, _;
  end if;

  if assigned S`IsInt then
    return S`IsInt(x, B, S:EasyNonInt := EasyNonInt);
  elif S`Type eq "Complex" then
    assert AbsoluteValue(x) le B; // The only use of the bound -- here we need an extra Epsilon
    f := Round(Re(x));
    if Epsilon cmpne false then
      return (Re(x) - f)^2 + Im(x)^2 lt Epsilon^2, f;
    else
     if not IsExport() then printf"Epsilon not set for IsInt\n"; end if;
     return (Re(x) - f)^2 + Im(x)^2 lt 10^Round(-0.8*S`Prec), f;
    end if;
  elif S`Type eq "p-Adic" then
    if Precision(Parent(x)) cmpne Infinity() then
      error "wrong ring";
    end if;
    f, y := IsCoercible(S`Base, x);
    if f then
      if EasyNonInt then
        return true;
      end if;
      x := y;
      f := Integers()!x;
      p := Precision(x);
      p := Characteristic(ResidueClassField(S`Base))^p;
//      f := Integers(p)!f;
//      return RationalReconstruction(f);
      if f gt p/2 then
        f := f-p;
      end if;
      fl :=  Abs(f) le B;
      if fl then
        vprint GaloisGroup, 4:  "INT: ", x, "(", f, ")";
      else
        vprint GaloisGroup, 4: "no int - size error";
      end if;
      return fl, f;
    else
      vprint GaloisGroup, 4: "no int - ring error";
      return false, _;
    end if;
  else
    error "not implemented yet";
  end if;
end intrinsic;

/* Check that we are close enought for Newton iternation. 
   see: http://numbers.computation.free.fr/Constants/Algorithms/newton.html    */ 
function CheckNewton(f, x)
 fx := Evaluate(f, x);
 fs := Derivative(f);
 fss := Derivative(fs);
 return Abs(fx/(Evaluate(fs, x))^2*Evaluate(fss, x)) lt 1/2;
end function;

// k is the relative floating point precision in digits.
function InternalHenselLift(f, x, k, R)

  assert CheckNewton(f,x);
  fx := Evaluate(f,x);
  if Abs(fx) ge 1/2 then
    p := Precision(x);
    p := 2*Ceiling(Log(Abs(fx)));
   elif IsWeaklyZero(fx)  then
    p := Precision(x);
  else
    p := Ceiling(-Log(Abs(fx))/Log(10))+1;
  end if;
  f_cancellation := + Ceiling(Log(10+Abs(fx))) + Ilog2(Maximum([Abs(x) : x in Eltseq(f)])) + Degree(f);
  kw := Ceiling(k*1.5) + f_cancellation;
  iter := 0;
  while p lt kw do
    iter := iter+1;
    p := Minimum(2*p, kw);
    C := R(Max(f_cancellation + iter, Ceiling(p*1.5 + 5)));  
    delta :=
        Evaluate(Polynomial(C, f), C!x)/Evaluate(Polynomial(C, Derivative(f)), C!x);
    //Ceiling(-Log(Abs(delta)));
    // it would be nice if we could assume that delta is getting smaller...    
    x := C!x - delta;
    if delta eq 0 then
       delta := 10^-Precision(delta);
   end if;
   if Abs(delta) lt 1 then
// 2nd order term would be 1/2 delta^2 * fss / fs. We use it as an error estimate.
    p := Minimum(Precision(C), 2*Ceiling(-Log(Abs(delta))/Log(10)) + Maximum(1, Ceiling(Log(1+Abs(x)))) + f_cancellation);
   else 
    p := f_cancellation;
   end if;
  end while;
  
  return R(k)!x;
end function;

intrinsic HenselLift(f::RngUPolElt, x::FldReElt, k::RngIntElt) -> FldComElt
  {Lifts the real root x of f to a precision of k}
  return InternalHenselLift(f, x, k, RealField);
end intrinsic;

intrinsic HenselLift(f::RngUPolElt, x::FldComElt, k::RngIntElt) -> FldComElt
  {Lifts the complex root x of f to a precision of k}
  return InternalHenselLift(f, x, k, ComplexField);
end intrinsic;
    

procedure GaloisRootAddPermutation(S, p)
  if assigned S`Permutation then
    S`Permutation := p*S`Permutation;
  else
    S`Permutation := p;
  end if;
end procedure;

intrinsic GaloisRoot(f::RngUPolElt, n::RngIntElt, S::GaloisData:Prec := 20, Bound := false, Scaled := true) -> RngElt
  {Returns the n-th root of f in the ring defined somehow by S with a precision of Prec}
  assert S`f eq f;
  return GaloisRoot(n, S:Prec := Prec, Bound := Bound, Scaled := Scaled);
end intrinsic;

intrinsic FujiwaraBound(f :: RngUPolElt) -> RngElt
  {Returns the Fujiwara bound for the absolute value of the complex roots of f}
   c := Eltseq(f); _n := #c;
   max_comp := Maximum([Abs(c[_n-i]/c[_n])^(1/i) : i in [1.._n-2]] cat [0]);
   max_comp := 2*Maximum(max_comp, Abs(c[1]/2/c[_n])^(1/(_n-1)));
   return max_comp; //Fujiwara bound
end intrinsic;

function PrecisionFromBound(Bound, S)
    if assigned S`GetPrec then
      Prec := S`GetPrec(Bound, S);
    elif S`Type eq "Complex" then
      Prec := Floor((Log(Bound)+20)/Log(10)*1.5);
    elif S`Type eq "p-Adic" then
      if Bound eq 0 then 
        Bound := 1;
      end if;
      Prec := Floor(Log(Bound)/Log(Characteristic(ResidueClassField(S`Base)))+5);
    else
      error "unsupported ring type...";
    end if;
    vprint GaloisGroup, 4: "GaloisRoot: using a prec of ", Prec, 
                           "as computed from the bound ", Bound;
    return Prec;
end function;

function prec_sufficient(prec_stored, prec_required)

 if prec_stored cmpeq Infinity() then return true; end if; 

 assert Type(prec_stored) eq Type(prec_required);

 if Type(prec_stored) eq RngIntElt then
  return prec_stored ge prec_required;
 end if;

 assert #prec_stored eq #prec_required;

 return &and [prec_stored[i] ge prec_required[i] : i in [1..#prec_stored]];
end function;

// Checks that rt is a root with precision at least prec
function CheckRoot(S, rt, prec)

 if not assigned S`f then return true; end if; // can not check the root

 f := S`f;
 if assigned S`BaseMap then
  f := Polynomial([S`BaseMap(a, prec) : a in Coefficients(f)]);
 end if;
 v := Evaluate(f,rt);

 if Type(prec) eq RngIntElt then
  if (Type(rt) eq FldComElt) then // Complex case
   fx := Evaluate(S`f,ComplexField(prec + 100)!rt);
   fs := Evaluate(Derivative(S`f),rt);
   delta := fx/fs;
   return delta eq 0 or Log(10,AbsoluteValue(delta)/AbsoluteValue(rt)) lt 10^-prec; 
  end if;
  return  (Valuation(v) ge prec);  // p-adic case
 end if;

 co := Coefficients(v);
 return &and [Valuation(a) ge prec[2] :  a in co];
end function;

intrinsic GaloisRoot(n::RngIntElt, S::GaloisData:Prec := 20, Bound := false, Scaled := true) -> RngElt
  {Returns the n-th root of f in the ring defined somehow by S with a precision of Prec}

  if assigned S`Permutation then
    n := n^(S`Permutation^1);
  end if;
  if Bound cmpne false then
    Prec := PrecisionFromBound(Bound, S);
  end if;
  if assigned S`MinPrec then
    Prec := Maximum(S`MinPrec, Prec);
  end if;
  if assigned S`Roots then
    if prec_sufficient(Precision(S`Roots[n]), Prec) then
      r := S`Roots[n];
      assert2 CheckRoot(S, r, Prec);
      if Scaled and assigned S`Scale and S`Scale ne 1 then
        if assigned S`BaseMap then
          r *:= S`BaseMap(S`Scale, Prec);
        else
          r *:= S`Scale;
        end if;
      end if;
      r := ChangePrecision(r, Prec);
      return r;
    end if; 
  end if;

// "Recomputing roots with precison",Prec;

// We may have a special function for computing roots:
  if not assigned S`f or assigned S`GetRoots then
    assert assigned S`GetRoots;
    has_old := assigned S`Roots;
    if has_old then old := S`Roots; end if;
    S`GetRoots(S:Prec := Prec);
    if has_old then assert #S`Roots eq #old; end if;
    r := S`Roots[n];
    assert2 CheckRoot(S, r, Prec);
    assert Precision(r) ge Prec;
    if Scaled and assigned S`Scale then
      if assigned S`BaseMap then
        r *:= S`BaseMap(S`Scale, Prec);
      else
        r *:= S`Scale;
      end if;
    end if;
    assert Precision(r) ge Prec;
    r := ChangePrecision(r, Prec);
    assert Precision(r) ge Prec;
    return r;
  end if;


// Roots are not stored with required precision and no special GetRoots-code
// Lift or compute roots here...
  if Parent(Prec) cmpeq Integers() then
   double_Prec := Prec+Prec;    // double precision of coefficients for root computation/lifting 
  else
   double_Prec := Prec;  // in Q(t) case double coefficient precision, keep length of series
   double_Prec[2] := 2*Prec[2] + Max(4,2*Prec[1]);
  end if;
  
  if assigned S`Roots then
    if S`Type eq "Q(t)" then
      InternalQtLiftRoots(S, Prec); 
    else
      f := S`f;
      if S`Type in {"p-Adic", "F_q(t)"} then
        if assigned S`BaseMap then
          g := Polynomial([S`BaseMap(x, double_Prec) : x in Eltseq(f)]);
          R := S`Ring;
          g := Polynomial(R, g);
        else
          R := ChangePrecision(S`Ring, double_Prec); // too crude - but Prec itself
              // may be too low if f is not squarefree mod p
              // which can happen in the reducible polynomial case (coming
              // from SolveByRadicals: f := x^4 - x^3 - 7*x^2 + 2*x + 9, 
              //                   Prime := 7
              // f*CyclotomicPolynomial(3) is mod 7 not squarefree.)
          g := Polynomial(R, f);
        end if;
        vprint GaloisGroup, 2: "Lifting roots in ", R, 
                       " to precision ", Prec;
        vprint GaloisGroup, 4: " starting with ", S`Roots;
        if assigned S`Time then
          rt := Cputime();
        end if;
        if UseFactor and (not assigned S`Scale or S`Scale eq 1) then
          C := ResidueClassField(BaseRing(S`Ring));
          vprint GaloisGroup, 4: "Factorising over the ResidueClassField";
          vtime GaloisGroup, 4: lR := Factorisation(Polynomial(C, f));
          if exists{x : x in lR | x[2] ne 1} then
            vprint GaloisGroup, 3: "Polynomial not square-free over the residue class field";
          end if;
          RR := Integers(BaseRing(R));
          vprint GaloisGroup, 4: "Lifting the factorisation";
          if #lR gt 1 and forall{x : x in lR | x[2] eq 1} then
            vtime GaloisGroup, 4:
            lf := HenselLift(Polynomial(RR, f), [Polynomial(RR, x[1]) : x in lR]);
          else
            lf:=[Polynomial(RR,f)];
            lR := [<Polynomial(C, f), 1>];
          end if;//trivial case, only one factor
          lf := [ Polynomial(R, x) : x in lf];
          C := ResidueClassField(S`Ring);
          lR := [Polynomial(C, x[1]) : x in lR];
          vprint GaloisGroup, 3: "Lifting roots";
          vtime GaloisGroup, 4: S`Roots := [S`Ring |
              HenselLift(lf[[n : n in [1..#lR]|Evaluate(lR[n], C!x) eq 0][1]],
                                 R!x, double_Prec) : x in S`Roots];
          assert #S`Roots eq #Set(S`Roots);
        else
          vprint GaloisGroup, 3: "Lifting roots...";
          if S`Type eq "p-Adic" then
            S`Roots := ChangeUniverse(S`Roots, R);
          end if;
//"This is how we get the roots";
          vtime GaloisGroup, 3: 
            S`Roots := [S`Ring| HenselLift(g, x, Prec) : x in S`Roots];
          assert forall{x : x in S`Roots | Precision(x) ge Prec};
          if Type(Prec) eq RngIntElt then
             assert &and [Valuation(Evaluate(g, r)) ge Prec : r in S`Roots];
          end if;
	// reducible poly with multiple roots will not satisfy this
	// assert #Set(S`Roots) le #S`Roots;
        end if;
        if assigned S`Time then
          S`Time`Lift +:= Cputime(rt);
        end if;
        if Type(Prec) eq Tup then
          S`Ring`DefaultPrecision := Maximum(Prec[1], S`Ring`DefaultPrecision);
        else
          S`Ring`DefaultPrecision := Maximum(Prec, S`Ring`DefaultPrecision);
        end if;
      else // Other types
        if assigned S`BaseMap then
          g := Polynomial([S`BaseMap(x, double_Prec) : x in Eltseq(f)]);
          S`Roots := [ HenselLift(g, x, Prec) : x in S`Roots];
        else
          S`Roots := [ HenselLift(f, x, Prec) : x in S`Roots];
        end if;
        assert forall{x : x in S`Roots | Precision(x) ge Prec};
        assert #Set(S`Roots) eq #S`Roots;
      end if;
      S`Roots := [ChangePrecision(a,Prec) : a in S`Roots]; 
    end if;
    r := S`Roots[n];
    assert2 CheckRoot(S, r, Prec);
    if Scaled and assigned S`Scale then
      if assigned S`BaseMap then
        r *:= S`BaseMap(S`Scale, Prec);
      else
        r *:= S`Scale;
      end if;
    end if;
    r := ChangePrecision(r, Prec);
// Roots lifted up to precsion Prec, but the ring might have even more precision
    return r;
  end if;

// No initial roots. Compute them.

  f := S`f;
  if S`Type eq "Complex" then
    pPrec := Maximum(40, Prec);
/* The floating point approximation of the polynomial does not suffice to get root approximations of the same precision.
   We add some extra digits. */ 
    pPrec2 := Ceiling(Log(10,1+FujiwaraBound(f))) + Degree(f) + 10;
    pPrec := pPrec div 2;
    iter := 0;
    repeat
     iter := iter + 1;
     pPrec := 2*pPrec;
     if iter gt 10 then
      error "Can not initialize GaloisRoot.";
     end if;
     S`Roots := [ChangePrecision(x[1],pPrec) : x in Roots(Polynomial(ComplexField(pPrec2 + pPrec), f))];
     S`Ring := ComplexField(pPrec);
     r := ChangePrecision(S`Roots[n], Prec);
     dist := Min([1] cat [AbsoluteValue(S`Roots[i] - S`Roots[j]) : i,j in [1..#S`Roots] | i lt j]); 
     max := Max([AbsoluteValue(a) : a in S`Roots]);
    until &and [CheckNewton(f,x) : x in S`Roots] and (#S`Roots eq Degree(f)) and (max lt dist * 10^(pPrec - 5 - Degree(f)));
    vprintf GaloisGroup, 2: "Complex roots initialized with precision %o\n",pPrec;
    if Scaled and assigned S`Scale then
      r *:= S`Scale;
    end if;
    S`Prec := pPrec;
    return r;
  elif S`Type eq "p-Adic" then
    if assigned S`Time then
      rt := Cputime();
    end if;
    f := Polynomial(Integers(), f*Lcm([Denominator(x) : x in Eltseq(f)]));
    if not assigned S`Ring then
        vprint GaloisGroup, 3: "Finding splitting field";
	vtime GaloisGroup, 3: R := SplittingField(f, S`Base);
	S`Ring := R;
    else
	R := S`Ring;
    end if;
    vprint GaloisGroup, 3: "Computing initial roots";
    vtime GaloisGroup, 3: S`Roots := [ x[1] : x in Roots(Polynomial(R, f))];
    if assigned S`Time then
      S`Time`Lift +:= Cputime(rt);
    end if;
    S`Ring`DefaultPrecision := Maximum(Prec, S`Ring`DefaultPrecision);
    r := ChangePrecision(S`Roots[n], Prec);
    assert2 CheckRoot(S, r, Prec);
    if Scaled and assigned S`Scale then
      if assigned S`BaseMap then
        r *:= S`BaseMap(S`Scale, Prec);
      else
        r *:= S`Scale;
      end if;
    end if;
    return r;
  else
    error "not implemented yet";
  end if;
end intrinsic;

function My_np(x)
  return NextPrime(x);
end function;

intr_subfields := Subfields;

// Compute a list of primes of good reduction and a corresponding list of shapes
function GetShapes(K:Prime := false, MyNextPrime := false, Count := false) 
 vprint GaloisGroup, 2: "GetShapes started....";
 f := DefiningPolynomial(K);
 mul := LCM([Denominator(a) : a in Coefficients(f)]);
 f := f * mul;
 lc := Integers()!LeadingCoefficient(f);

 if MyNextPrime cmpeq false then
  MyNextPrime := NextPrime;
 end if;

 if Prime cmpeq false then
  p := MyNextPrime(Degree(K));
 else
  p := Prime;
 end if;

 if Count cmpeq false then
  Count := Max(20,5*Degree(K));
 end if;
 
 p_list := []; s_list := [];
 repeat
  if lc mod p ne 0 then
   f_fp := PolynomialRing(GF(p))!f;
   if IsSquarefree(f_fp) then
    dd_fac := DistinctDegreeFactorization(f_fp);
    deg_list := &cat [ [a[1] : i in [1..Degree(a[2]) div a[1]] ] : a in dd_fac];
    Append(~p_list,p);
    Append(~s_list,Sort(deg_list)); 
   end if;
  end if;
  p := MyNextPrime(p); 
 until #p_list ge Count;
 if GetVerbose("GaloisGroup") gt 2 then
  printf"Shapes and primes found:\n";
  s_prl := SetToSequence(Set(s_list));
  Sort(~s_prl, func<a,b | LCM(a) - LCM(b)>);
  for a in s_prl do
   printf"%o %o\n",a,[p_list[i] : i in [1..#p_list] | s_list[i] eq a]; 
  end for;
 end if;
 return p_list,s_list;
end function;

/* Select a prime out of the list Primes with shapes as in Shapes
   Strategy: 1 : Optimal effect on ShortCosets when starting at S_n
             2 : Minimal degree of splitting field
             3 : Compromise for a non-trivial starting group. 

   ToDo: To make this function useable in more general settings
   ===== use the degrees of the primes to make costs of arithmetic more honnest.  

   SubF: List of subfields. Make sure, that p does not divide any of the subfield discriminants */
function SelectPrime(Primes, Shapes, Strategy, SubF)

 if SubF cmpeq false then SubF := []; end if;

 n := &+Shapes[1]; // Degree of field
 dil_lcm := LCM([Discriminant(a[1]) : a in SubF | Degree(a[1]) lt n] cat [1]); // Discriminant of initial field is checked.
 
 ind := [i : i in [1..#Primes] | dil_lcm mod Primes[i] ne 0];
 if #ind eq 0 then
  error "No primes left by subfield discriminant test.\n";
 end if;
 Primes := [Primes[i] : i in ind];
 Shapes := [Shapes[i] : i in ind];

 if Strategy eq 1 then
  kl := [LCM(a)^2 * Max(10, ScCostEst(a)) : a in Shapes]; 
// Costs of arithmetic are quadratic in degree. In case of lt 10 short cosets we will add some.
  m1,m2 := Min(kl);
 end if; 

 if Strategy eq 2 then
  deg_l := [LCM(a) : a in Shapes];
  m1,m2 := Min(deg_l);
 end if;

 if Strategy eq 3 then
// 1st step: Find best prime for each possible splitting field degree
  dl := [LCM(a) : a in Shapes]; 
  deg_l := Sort(SetToSequence(Set(dl))); 
  ind_best := [];
  cost_best := [];
  for d in deg_l do
   ind := [ i : i in [1..#dl] | dl[i] eq d ];
   m1,m2 := Min([ScCostEst(Shapes[i]) : i in ind]);
   Append(~ind_best,ind[m2]); 
   Append(~cost_best,m1);
  end for;

// Take smallest degree with #ShortCosets at most <= Max(10*n, 2*MinmalValue) . 
  e1,e2 := Min(cost_best);
  bnd := Max([2*e1,10*n]);
  m1 := Min([i : i in [1..#deg_l] | cost_best[i] le bnd]);
  m2 := ind_best[m1];
 end if;

 if assigned m2 then
  vprint GaloisGroup, 1: "Choose p= ",Primes[m2]," of type :",Shapes[m2];
  return Primes[m2];
 end if;
 error "Select Prime: Strategy not yet implemented";
end function;



intrinsic InternalBound(S::GaloisData, tschirni::RngUPolElt, inv::RngSLPolElt, 
                idx::RngIntElt: B := false, LowTest := false) -> .
  {}
  //RED, "\nInternslBound called\n\n", normal;

//  printf"Internal Bound: %o %o %o %o\n",S`max_comp, tschirni, TotalDegreeAbstract(inv), idx; 

  if S`Type eq "Complex" then
    nop := NumberOfOperations(inv, "+") + NumberOfOperations(inv, "-") +
           Degree(tschirni) + 1;
//    nop := Minimum(1000, nop); 
  else
    nop := 1;
  end if;

//"assigned", assigned S`Bound;
  if Type(S`max_comp) eq RngIntElt then // The Numberfield case
    if LowTest then
      if S`Type ne "Complex" then return idx * 10^nop; end if;
      idx := 2; // Complex case does not have a good short cut
    end if;
/*
S`max_comp;
Evaluate(tschirni, S`max_comp);
NumberOfOperations(inv, "^"), NumberOfOperations(inv, "+");
Bound(inv, Evaluate(tschirni, S`max_comp));
idx;
*/
    return nop * (2*Bound(inv, Evaluate(tschirni, S`max_comp)))^idx;
  end if;
  if assigned S`Bound then
    //"calling provate bound function";
    x := S`Bound(tschirni, inv, idx: LowTest := LowTest);
    //"returning", x, Type(x), Parent(x);
    return x;
  end if;
  error "case not implemented (yet)";
end intrinsic;

function invar_coeff_ring(S)
    if Characteristic(S`Base) eq 0 then
	return Integers();
    elif ISA(Type(S`Prime), RngElt) then
	return Parent(S`Prime);
    else
	return Parent(Minimum(S`Prime));
    end if;
end function;

function get_tschirni_R(R, coeff_bound, degree_bound, all_tschirni, inv_type)
// in case a linear transformation is proven to be useless, we force degree >= 2.
    if inv_type in ["Intransitive", "Generic-KG", "ProdSum", "Generic-CF(small prim)",  
                    "Generic-CF(prim)", "SetOrbit", "FactorDelta", "PairOrbit"] then
     lo_deg := 2;
     if (degree_bound eq 1) then
      degree_bound := 2; 
     end if;
    else
     lo_deg := 1;
    end if;

    if Characteristic(R) eq 0 then
	repeat
	  tschirni := Polynomial([Random(coeff_bound) : x in [1..Random(degree_bound)]] cat [1]);
	until Degree(tschirni) ge lo_deg and tschirni notin all_tschirni;  
    else
	Fq := CoefficientRing(R);
	repeat
	  tschirni := Polynomial([Polynomial([Random(Fq) : y in [1 .. Random(1, coeff_bound)]]) : x in [1..Random(degree_bound)]] cat [1]);
	until Degree(tschirni) ge lo_deg and tschirni notin all_tschirni;  
    end if;
    return tschirni;
end function;

function get_tschirni(S, coeff_bound, degree_bound, all_tschirni, inv_type)
    return get_tschirni_R(invar_coeff_ring(S), coeff_bound, degree_bound, all_tschirni, inv_type);
end function;

function get_all_tschirni_universe(S)
    if Characteristic(S`Base) eq 0 then
	return PolynomialRing(Integers());
    elif ISA(Type(S`Prime), RngElt) then
	return PolynomialRing(Parent(S`Prime));
    else
	return PolynomialRing(Parent(Minimum(S`Prime)));
    end if;
end function;

function apply_tschirni(S, tschirni, X)
    if Characteristic(S`Base) eq 0 then
	return [Evaluate(tschirni, x) : x in X];
    else
	T := Polynomial([S`BaseMap(c, AbsolutePrecision(X[1])) : c in Coefficients(tschirni)]);
	return [Evaluate(T, x) : x in X];
    end if;
end function;

function eval_invar(S, i, r)
    if Characteristic(S`Base) eq 0 then
	return Evaluate(i, r);
    else
	ii := 1;
    end if;
end function;

// Compute knwon subgroup if not stored in S
function get_frobenius(S,n)
 if not assigned S`KnownSubgroup then

  if S`Type eq "Complex" then 
   pr := 10 + Ceiling(Log(10,1+S`max_comp)); 
   repeat
    r := [ GaloisRoot(i, S: Prec := pr) : i in [1..n]];
    rt := [ ComplexConjugate(x) : x in r];
    p := [ t where _, t := Minimum([Abs(rt[y]-r[x]) : y in [1..#rt]]) : x in [1..#r]];
    pr *:= 2;
    if (pr gt 100+10*Log(10,1+S`max_comp)) then
      error "cannot get Frobenius";
    end if;
   until #Set(p) eq n;  
   cc :=  Sym(n)!p;
   assert Order(cc) in {1,2};
   return cc;
  end if;

/* In case of lack of implementation just return the trivial element. */
  if S`Type in {"Q(t)"} then
   vprintf GaloisGroup, 2: "get_frobenius: Case not implemented. Returning identity."; 
   return [i : i in [1..n]]; 
  end if;

  assert S`Type ne "Complex";
        // we need to compute U = Gal(S`Ring) as a subgroup of H<G
        // and then to implement 5.12 on page 115
        // Lets start with U:
  R, mR := ResidueClassField(S`Ring);
  r := [ GaloisRoot(i, S: Prec := 1)@mR : i in [1..n]];
  rt := [ x^q : x in r] where q := #ResidueClassField(S`Base);
  p := [ Position(rt, x) : x in r];
  vprintf GaloisGroup, 2: "Generator of used local group:\n%o\n", Sym(#p)!p,"Maximal";
 else
  p := S`KnownSubgroup.1; //TODO: think about better groups!
                          //      and better use of them.

// GaloisGroup will do the verbose printing for the known subgroup when it is started. We don't repeat it.
//  vprintf GaloisGroup, 2: "Using a subgroup of size %m:\n%o\n", #S`KnownSubgroup, S`KnownSubgroup,"Maximal";
 end if;
// vprint GaloisGroup, 2: "Using a permutation", p;
 return p;
end function;


/* Compute cosets or short cosets. Add a few cosets in the short if helpfull to detect tschirnhausen-cases. */
function get_cosets(G, H, S, AlwaysTransform, InvCosts)

/* Get Frobenius element first */
  p := G!get_frobenius(S, Degree(G));
  
/* Don't use short cosets in case all cosets are cheap or Frobenius is trivial. */
  if (Index(G,H) lt MaxShortCosets) or (Index(G,H) * InvCosts le 10000) or (Order(p) eq 1) then
/* Using all short cosets and one representative of each Frobenius orbit of then complement 
   will suffice to detect degenerations of resolvents.                                          */ 
    phi := CosetAction(G,H);
    orbs := Orbits(sub<Image(phi) | phi(p) >);
    o1 := [Representative(a) @@ phi : a in orbs | #a eq 1];  // Short cosets
    if #o1 eq 0 then
      vprint GaloisGroup, 2: "no cosets remaining, group not possible";
      return [], false;
    end if;
    o2 := [Representative(a) @@ phi : a in orbs | #a gt 1];  // One representative of each Frobenius orbit 
    cos := o1 cat o2; 
    vprint GaloisGroup, 2: "Long: Have to consider ", #o1, 
                           " short cosets, ", #o2, 
                           " supplemental cosets for subgroup of index ",Index(G,H),"=",Factorization(Index(G,H));
    return cos, false;
  end if; 
 
  vprint GaloisGroup, 1: "use short cosets";

  if IsNormal(G, H) then
if not IsExport() then
 "Large index normal subgroup case in get_cosets";
end if;
     if not G!p in H then
        vprint GaloisGroup, 1: "(normal) subgroup is not possible";
        return [], false;    
     end if;
//JK: For normal subgroups all cosets produce integers or none. Therefore there is an easy algorithm
//to produce ShortCosets, simply take one. In order to use 5.10, add a second one
     vprint GaloisGroup, 2: "normal subgroup";
     gen:={x: x in Generators(G) | not x in H};
     assert #gen gt 0;
     cos := [G.0, Random(gen)];      
  else 
     cos := ShortCosets(G!p, H, G);
     if cos cmpeq false then
S`f, S`Prime, G, H;
IsMaximal(G, H);
        error "Too many short cosets, wrong prime ....";
     end if;
  end if;
  vprint GaloisGroup, 2: "Short: Have to consider", 
                          #cos, "cosets initially";
  if #cos eq 0 then
     vprint GaloisGroup, 1: "no cosets remaining, group not possible";
     return [], false;
  end if;
 
//to give it a chance, try to add some elementes of G\H...
//(to help 5.10)??
  if (#cos lt 10) and (#cos lt Index(G, H)) and not AlwaysTransform  then
     for i in [1..10] do
       g := Random(G);
       if forall(x){x : x in cos | x*g^-1 notin H} then
          Append(~cos, g);
       end if;
     end for;
     vprint GaloisGroup, 2: "supplemented to", #cos;
  end if;

  return cos, (#cos lt Index(G, H));
end function;


/* Choose precision we work with. 
   In case proofs get expensive we reduce to heuristic precision at this point.
   In case one wants to force a heuristic precion one can simply choose index smaller than the subgroup index. */
function choose_prec(index, S, B, tschirni, i, ProofEffort)

/* Keep index_limit not too large since it is used as an upper bound
   to get BB_lift. Increasing index_limit increases BB_lift and so precision
   unnecessarily when the result is not recorded as being proven */

 mult_limit := ProofEffort*10000;
// "mult_limit:",mult_limit; 

  index_limit := 45;
  if S`Type eq "Q(t)" then
     index_limit := index_limit div 3;
  end if;

  pf_flag := true;
  if index gt index_limit then
     pf_flag := false;
     BB_lift := InternalBound(S, tschirni, i, index_limit: B := B);
  else
     BB_lift := InternalBound(S, tschirni, i, index: B := B);
  end if;
  BB_test := InternalBound(S, tschirni, i, 1: B:= B); 
//TotalDegreeAbstract(i), S`max_comp, Index(G, H);
  Prec := PrecisionFromBound(BB_lift, S);
//  Prec;
  if Type(Prec) eq RngIntElt then
    mult_cost := NumberOfOperations(i, "*")*Prec*Log(Prec);
  else
    mult_cost := NumberOfOperations(i, "*")*Prec[1]*Prec[2]*Log(Prec[1])*Log(Prec[2]);
  end if;

  if index gt index_limit and (S`Type eq "Q(t)" or
 	index*mult_cost gt index_limit*mult_limit) then
    pf_flag := false;
    vprintf GaloisGroup, 2: 
    "Large index (%o) subgroup, using a bound of %o instead\n",
            index, index_limit div 3;
    if S`Type ne "Q(t)" then
      BB_lift := InternalBound(S, tschirni, i, index_limit div 3:B := B);
    end if;
  else
  end if;

// "Precision:",PrecisionFromBound(BB_lift, S);
  vprintf GaloisGroup, 3: "Log2 of Bound: %o (%o, %o)\n", 
                                             Ilog2(BB_lift), B, tschirni;
  vprintf GaloisGroup, 3: "Log2 of Bound: %o (%o, %o)\n", 
                                             Ilog2(BB_test), B, tschirni;
  Epsilon := false;
  if S`Type eq "Complex" then // Set precision to be used in IsInt here
     Epsilon := 10.0^-Floor(Log(10,BB_lift) - Log(10,BB_test));
     vprintf GaloisGroup,2 :"Bounds: Test = %o  Lift = %o Eps = %o\n", BB_test*1.0, BB_lift*1.0,Epsilon*1.0;
     BB_lift := 10^10 * BB_lift; 
  end if; 


  return BB_lift, BB_test, pf_flag, Epsilon;
end function;


/* scan_cosets:
   cos     - a list of cosets
   tschirni- the transformation we use
   Epsilon - Epsilon for complex IsInt
   inv     - Invariant
 
   mode    1: Cheap check:
              -- Check only Tschini, early abort in case tschirni is bad.
              -- Exclude cosets by EasyNonInt   
           2: Only disprove cosets, ignore multiplicities:
              -- Exclude costs that are disproved by non-integer values
              -- Return all cosets that  
           3: Full check:
              -- Return simple and multiple zero cosets separately.          */
function scan_cosets(cos, tschirni, inv, is_c, mode, BB_lift, BB_test, Epsilon, S, n)

// "Scan cosets, mode:",mode;
  vprint GaloisGroup, 2:"Scanning",#cos,"cosets in mode",mode,"with tschirni",tschirni;
  vtime GaloisGroup, 2: r := func<|[ GaloisRoot(i, S: Bound := BB_lift) : i in [1..n]]>();
  r := func<|apply_tschirni(S, tschirni, r)>(); 

  prec_lift := PrecisionFromBound(BB_lift, S);
  prec_test := PrecisionFromBound(BB_test, S);

  ir := { };
  ir_int := [];
  foundg := []; 
  dbl := 0;
  cc := 0;

  assert (mode ne 1) or (S`Type ne "Complex"); // mode 1 only useful in the non-archimedian world

  for g in cos do

    if not is_c then
if not IsExport() then
"\n\n\nne Evaluating using base map 1";
end if;
      x := Evaluate(inv, PermuteSequence(r, g), map<CoefficientRing(Parent(inv)) -> Universe(r) | y :-> S`BaseMap(y, prec_lift)>);
    else
      x := Evaluate(inv, PermuteSequence(r, g));
    end if;
    if mode eq 1 then
      if x in ir then dbl +:= 1; end if;
      Include(~ir, x);
      if not IsInt(x, BB_test, S:EasyNonInt, Epsilon := false) then
         Exclude(~cos, g);
         additional := g;
      end if;      
      if dbl gt 5 then
       if assigned additional then return cos, false, additional;
                              else return cos, false, _; 
       end if;
      end if; 
    else

     if S`Type in {"Complex","p-Adic", "p-Adic (rel)"} then 
       isInt, Int := IsInt(x, BB_test, S: Epsilon := Epsilon);
     else
// Reconstruct integer on minimal precision
       isInt, Int := IsInt(ChangePrecision(x,prec_test), BB_test, S: Epsilon := Epsilon);
       if isInt then
// Confirm integer on full precision
         if assigned S`BaseMap then
           isInt := IsWeaklyZero(S`BaseMap(Int, prec_lift) - x);
         else
           isInt := IsWeaklyZero(x - Int);
         end if;
       end if;
     end if;
// Int, b; 
     if isInt then
         Append(~ir_int, Int);
         Append(~foundg, g);  
     end if;
     cc := cc + 1;
     if cc mod 100 eq 0 then
       vprint GaloisGroup, 2: cc, " cosets treated";
     end if;
    end if;   
  end for;
  
  if mode eq 1 then
     if assigned additional then return cos, dbl eq 0, additional;
                            else return cos, dbl eq 0, _; 
     end if; 
  end if;    
 
  if mode eq 2 then
     return foundg;
  end if;

  ms := SequenceToMultiset(ir_int);
  return [foundg[i] : i in [1..#foundg] | Multiplicity(ms, ir_int[i]) eq 1], 
         [foundg[i] : i in [1..#foundg] | Multiplicity(ms, ir_int[i]) ne 1];
end function;


function print_call_stauduhar(G,L,Tschirni)
  vprint GaloisGroup, 2: "Stauduhar: Start with subgroup of index ", Index(G,L),"=", Factorization(Index(G,L));
  if Tschirni cmpne false then
    vprint GaloisGroup, 2: "Stauduhar: Starting with Tschirni ",
                            Tschirni;
  end if;
  if (GetVerbose("GaloisGroup") ge 3) then
    if IsTransitive(L) then
      if IsPrimitive(L) then
        printf"Groups are primitive <%oP%o,%oP%o>.\n",
              Degree(G), PrimitiveGroupIdentification(G), Degree(L), PrimitiveGroupIdentification(L);
      else                        
        printf "Block structure of subgroup:\n";
        _ := TestAllPartitions(L);
      end if;
    else
      vprint GaloisGroup, 2: "(intransitive case)";
    end if;
  end if;  
  if GetVerbose("GaloisGroup") ge 2 and IsTransitive(G) then
     //TransitiveGroupIdent is expensive...
     idH:=InternalPrintGroupIdentification(L);
     idG:=InternalPrintGroupIdentification(G);
     vprintf GaloisGroup, 2: "and number <%o%o, %o%o>\n", 
                      green, idG, idH, normal;
  end if;
  vprint GaloisGroup, 5: "Generators of G ", Generators(G);
  return 0;  
end function;

/* Get and check invariant, manage tschirni  */
function inv_setup(PreCompInvar, G,L,GalRel, AlwaysTransform, Tschirni, AllTschirni, UseInvarEnv, S)

  x := ext<Integers()|>.1;
    if PreCompInvar cmpeq false then
      i := GaloisGroupInvariant(invar_coeff_ring(S), G, L:GalRel := GalRel); 
    else
      assert assigned PreCompInvar`GalInvType;
      i := PreCompInvar;
    end if;
    /*
    CAN CAUSE COERCION ISSUES IN CHECK WHICH WE NEED TO SORT OUT
    assert forall{x : x in Generators(L) | IsInvariant(SLPolynomialRing(CoefficientRing(get_all_tschirni_universe(S)), Rank(Parent(i)) : Global)!i, x)};
    assert exists{x : x in Generators(G) | not IsInvariant(SLPolynomialRing(CoefficientRing(get_all_tschirni_universe(S)), Rank(Parent(i)) : Global)!i, x)};
    */
    R := CoefficientRing(get_all_tschirni_universe(S));
    assert exists{x : x in Generators(G) | not IsInvariant(SLPRGg(R, i), x)};
    assert forall{x : x in Generators(L) | IsInvariant(SLPRGg(R, i), x)};
    assert assigned i`GalInvType;
    vprintf GaloisGroup,2: "Using invar of type %o ", i`GalInvType;
    vprintf GaloisGroup,2: "of degree %o with %o multiplications\n",TotalDegreeAbstract(i), NumberOfOperations(i, "*");
    if AlwaysTransform then
      tschirni := get_tschirni(S, 3, Degree(G), {x}, i`GalInvType);
    elif Tschirni cmpne false and UseInvarEnv then
      tschirni := Tschirni;
    else
      tschirni := x;
    end if;
    if AllTschirni cmpne false then
      all_tschirni := AllTschirni;
    else
      all_tschirni := {get_all_tschirni_universe(S) | x, tschirni};
    end if;

    // When we evaluate at the roots in the splitting field it is easier 
    // for compatibility to have the invariant over the integers if possible
    eval_i := Evaluate(i, [SS.j : j in [1 .. Rank(Parent(i))]]) where SS := SLPolynomialRing(Integers(), Rank(Parent(i)) : Global);
    // don't need a GalInvType for evaluation which is all that is done with eval_i
    is_c := CoefficientRing(Parent(eval_i)) cmpeq Integers();
    //is_c, eval_i := IsCoercible(SLPolynomialRing(Integers(), Rank(Parent(i)) : Global), i);
    if not is_c then
       assert assigned S`BaseMap;
    end if;

    return eval_i, is_c, i, tschirni, all_tschirni;
end function;

intrinsic Stauduhar(G::GrpPerm, H::GrpPerm, 
                    S::GaloisData, B::RngIntElt:
                    AlwaysTransform:= false, Coset := false, 
                    PreCompInvar := false, GalRel := false,
                    Tschirni := false, UseInvarEnv := false,
                    AllTschirni := false, ProofEffort := 10)
                            -> RngIntElt, GrpElt, BoolElt, RngSLPolElt
  {return 1 if the Galois group is contained in H, -1 is it is probably in H and 5.10 was conclusive, -2 if if it probable in H, and 0 otherwise}

//    x := ext<Integers()|>.1;
    n := Degree(G);
   
    _ := print_call_stauduhar(G,H,Tschirni);

    eval_i, is_c, i, tschirni, all_tschirni := inv_setup(PreCompInvar, G,H,GalRel, AlwaysTransform, Tschirni, AllTschirni, UseInvarEnv, S);

    if Coset cmpeq false then 
      cos, UseShort := get_cosets(G, H, S, AlwaysTransform, NumberOfOperations(i, "*"));
      if UseInvarEnv then
         InternalGaloisInvarSetUseShort(S,PreCompInvar,UseShort);
      end if;  
      if #cos eq 0 then return 0, 1, true, _; end if;
    else
      cos := [ g : g in Coset];
      vprint GaloisGroup, 2: "Long: Have to consider ", #cos, 
                             " cosets initially";
      UseShort := #cos lt Index(G,H);
    end if;
//    "Working with",#cos,"cosets";
    success := false;
    all_pf_flag := true;

    repeat
      BB_lift, BB_test, pf_flag, Epsilon := choose_prec(Index(G,H), S, B, tschirni, i, ProofEffort);
 
      all_pf_flag := all_pf_flag and pf_flag;
      inv := i;
      if (Ilog2(BB_lift) gt 300) and (S`Type ne "Complex") and (not false) then

        vprint GaloisGroup, 2: 
          "Numbers are largish, try to check for duplicates first...";
// This test also excludes some cosets!             
// In the Q(t)-case this covers information that could be obtained from specialization.
// In the number field case we ran reduce from Cosets to ShortCosets.    
        repeat
// Have to recompute the bound because of the Q(t) case.
          b := InternalBound(S, tschirni, inv, #cos: B := B, LowTest);
          cos, suc, additional := scan_cosets(cos, tschirni, eval_i, is_c, 1, b, b, false, S, n);
          if #cos eq 0 then
            vprint GaloisGroup, 2: "removed all cosets";
            return 0, _, _, _;
          else
            vprint GaloisGroup, 2: "only", #cos, "are remaining after low prec";
//CF        if #cos eq 2 then return i, tschirni, cos; end if;
          end if;
          if not suc then
            vprint GaloisGroup, 2: "Tschirni - short cut";
	    tschirni := get_tschirni(S, 3, Minimum(Degree(G), 2+#all_tschirni), all_tschirni, i`GalInvType);
            // I guess, one should also check that the new element is actually
            // primitive.
            Include(~all_tschirni, tschirni);
	    if not IsExport() then 
		if #all_tschirni ge 3*Degree(G) then
		    S`f;
		  error "way too many transforms in shortcut!";
		end if;
	    end if;             
          end if;
        until suc;

        if assigned additional then
          Include(~cos, additional);
        end if;
        if UseInvarEnv and (Tschirni cmpne tschirni) then
          vprint GaloisInvarEnv, 1: "Tschirni has changed, returning invariant";
          InternalGaloisInvarEnvChangeInvar(S, inv, tschirni, cos, all_tschirni);
          return 2, _, _, _;
        end if;  
      end if;

      if not IsExport() then
	  max_prec := 2*50000;
      else
	  max_prec := DEFAULT_MAX_PREC;
      end if;

      if Ilog2(BB_lift) gt max_prec then 
Prec := PrecisionFromBound(BB_lift, S);
S`max_comp;
tschirni;
TotalDegreeAbstract(i), NumberOfOperations(i, "*"), NumberOfOperations(i, "+"), NumberOfOperations(i, "^"), NumberOfTerms(i), i`GalInvType;
BB_lift, BB_test, Prec, Index(G, H);
      error "Precision too large?";
        vprintf GaloisGroup, 1:
          "Precision (%o) too large, descent failed.\n", Ilog2(BB_lift);
        vprint GaloisGroup, 1: "Maximal precision is ", max_prec;
        return 0, _, _, _; 
      end if;

      BB_lift, BB_test, pf_flag, Epsilon := choose_prec(Index(G,H), S, B, tschirni, i, ProofEffort);
      cos_cnt := #cos;
/* Do a medium precision test before switching to full precision */
      if ((Ilog2(BB_lift) gt 100) or (S`Type ne "p-Adic")) and (Index(G,H) gt 2) then
// "Doing medium precision test";
        BB_lift_0, BB_test_0 := choose_prec(2,S, B, tschirni, i, ProofEffort);
        Epsilon_0 := false;
        if S`Type eq "Complex" then // Set precision to be used in IsInt here
           Epsilon_0 := 10^-10;
           BB_lift_0 := 10^20 * BB_test_0; 
           vprintf GaloisGroup,2 :"Medium precision test bounds: Test = %o  Lift = %o Eps = %o\n", BB_test_0*1.0, BB_lift_0*1.0,Epsilon_0;
        else
           vprintf GaloisGroup,2 :"Medium precision test bounds: Test = %o  Lift = %o\n", Ilog2(BB_test_0), Ilog2(BB_lift_0);
        end if; 

        no_cos := 0; foundg := [];
        cos := scan_cosets(cos, tschirni, eval_i, is_c, 2, BB_lift_0, BB_test_0, Epsilon_0, S, n);         
        if #cos eq 0 then
          vprint GaloisGroup, 2: "removed all cosets";
          return 0, _, _, _;
        end if;
        vprint GaloisGroup, 2: "Medium precision test reduces to ", #cos, " cosets"; 
      end if;

// "Full precison scan", cos;
      vprintf GaloisGroup,2 :"Full precision test bounds: Test = %o  Lift = %o\n", Ilog2(BB_test), Ilog2(BB_lift);
      c1,c2 := scan_cosets(cos, tschirni, eval_i, is_c, 3, BB_lift, BB_test, Epsilon, S, n);
// c1,c2;
      if #c1 eq 0 and #c2 eq 0 then
        vprint GaloisGroup, 2: "removed all cosets";
        return 0, _, _, _;
      end if;   

      vprint GaloisGroup, 2: "Found",#c1,"cosets as simple zeros and",#c2,"cosets as multiple zeros";
 
// In case a coset remains that is not in short cosets we have proved to require a tschirni.
// As we are using only one coset of each Frobenius orbit the entire orbit would correspond to  
// one zero with high multiplicity.
      p := get_frobenius(S, Degree(G)); 
      if (#c1 gt 0) and (#[x : x in c1 | not (G!p)^(x^-1) in H] eq 0) then
           success := true;
           vprint GaloisGroup, 2: BLUE, "DESCENT", normal;
//"UseShort", UseShort;
           if UseShort and (not IsNormal(G, H)) then 	
// FOR JK : This is what I really wanted to avoid
// As above comments on normal subgroups all cosets give integers or none.
// The Galois group either lies in H or not (when H is normal as all conjugates 
// are the same) so we want to return a definite answer here and stop looking
// as that can be really expensive.
             if (#c1 lt cos_cnt) or (#c1 gt 1) then
	       assert assigned i`GalInvType;
               return -1, c1, pf_flag, i;
             else 
	       assert assigned i`GalInvType;
               return -2, c1, pf_flag, i;
             end if;
           end if;
	   assert assigned i`GalInvType;
           return 1, c1, pf_flag, i;
      else
          cos := c1 cat c2; // according to KG, it's sufficient to consider
                            // the cosets that produced integers at this point.
//	  tschirni := get_tschirni(S, Minimum(3, #all_tschirni), Minimum(Degree(G), #all_tschirni), all_tschirni);
	  tschirni := get_tschirni(S, 3, Minimum(Degree(G), 2+#all_tschirni), all_tschirni, i`GalInvType);
          // I guess, one should also check that the new element is actually
          // primitive.
          Include(~all_tschirni, tschirni);
	  if not IsExport() then 
	      if #all_tschirni ge 100 then
		#all_tschirni;
S`f;
		error "way too many transforms!";
	      end if;
	  end if;
          vprintf GaloisGroup, 1: 
            "Selecting Tschirni %o for next iteration\n",tschirni;
          vprint GaloisGroup, 1: 
            "Number of cosets now ", #cos;
          if UseInvarEnv then
            vprint GaloisInvarEnv, 1: "Tschirni has changed, returning invariant";
            InternalGaloisInvarEnvChangeInvar(S, inv, tschirni, cos, all_tschirni);
            return 2, _, _, _;
          end if;
      end if;
    until false;
    vprint GaloisGroup, 1: "NO DESCENT";
    return 0, _, _, _;
end intrinsic;

function CycStrucToSequence(L)
  LL:=[];
  for a in L do
    for b in [1..a[2]] do
      Append(~LL,a[1]);
    end for;
  end for;
  return Sort(LL);
end function;

function TestShapes(G, shapes)
  if Degree(G) gt 30 and not IsPrimitive(G) then
    return true;
  end if;

//  "Shape test with", TransitiveGroupIdentification(G);
  c:=ConjugacyClasses(G);
  c:={CycleStructure(x[3]):x in c};
  c:={CycStrucToSequence(x):x in c};
  return shapes subset c;  
end function;

/* Driver for Stauduhar:
   G                   the group we start with
   S                   GaloisData
   max_comp            max_comp
   MaxSubGp            computes maximal subgroups
   Sieve               Subgroup sieve
   Subfields           true means: subfields have been used in starting group computation
   SubfieldsComplete   true means: We trust the subfields algorithm. I.e. we sieve out groups leading to more subfields
   Reject              List of rejected groups (only usefull for normal subgroups)
   
 */
function GenericStauduhar(G, S, max_comp, 
                             MaxSubGp, Sieve:
              ShortOK := false, Subfields := true, GalRel := false, 
              SubfieldsComplete := false,
              Reject:=[],Subgrp:=sub<G|>, DivisorOfOrder := 1, ProofEffort := 10);

  vprintf GaloisGroup, 1: "%oStart Generic Stauduhar Algo%o\n", RED, normal;

//"REJECT : ", Reject;
  rejectedNormalSubGroups := Reject;
  repeat
    vprintf GaloisGroup, 1: "%oTrying to descend%o from group of order %o = %o\n",green,normal,Order(G), FactoredOrder(G);

    vprintf GaloisGroup, 2: "Recall: Prime %o of type %o\n",S`Prime, 
                            assigned S`KnownSubgroup select [#a : a in Orbits(S`KnownSubgroup)] else [#a : a in Orbits(Subgrp)];
   
    vprintf GaloisGroup, 3: "Known subgroup f size %m: \n%o\n", #Subgrp, Subgrp, "Maximal";
    if GetVerbose("GaloisGroup") eq 2 then
       printf "%o rejected subgroups\n", #Reject;
    end if;
    vprint GaloisGroup, 3: "Rejected subgroups", Reject;

    if IsTransitive(G) then
      vprint GaloisGroup, 2: "with block structure",TestAllPartitions(G);
    else
      vprint GaloisGroup, 2: "(intransitive case)";
    end if;
    if UseCache() then
      r_a, r_b := GetSeed();
      SetSeed(1,0);
    end if;
    if _GetGaloisCacheLevel() gt 1 then
      fl, LU := CacheHasGroup(G);
      if not fl then
        LU := MaxSubGp(G);
        CachePutGroup(G, LU);
      end if;
    else
      LU := MaxSubGp(G);
    end if;
    if UseCache() then
      SetSeed(r_a, r_b);
    end if;
    LU:=[x:x in LU];
/*
"LU = ", LU;
for x in LU do
if IsTransitive(x) and Degree(x) lt 32 then
TransitiveGroupIdentification(x);
end if;
end for;
*/
    assert G notin LU;
    vprint GaloisGroup, 1: "Have to consider ", #LU, 
                           "subgroups (classes of them) initially";
    InternalGaloisInvarEnvInit(S, G, LU); // maybe add intransitive groups!!

    if UseSieve then 
      InternalGaloisInvarEnvSieve(S, func<x | #x mod DivisorOfOrder eq 0>);
      vprintf GaloisGroup, 2: "Reduce to %o (using divisor of order %o)\n", 
        InternalGaloisInvarEnvNumber(S), DivisorOfOrder;

      InternalGaloisInvarEnvSieve(S, 
        func<x|forall{t : t in rejectedNormalSubGroups | not x subset t}>);
      vprintf GaloisGroup, 2: "Further reduce to %o (using rejected subgroups)\n", 
        InternalGaloisInvarEnvNumber(S);

      InternalGaloisInvarEnvSieve(S, 
        func<x|not IsNormal(G, x) or Subgrp subset x>);
      vprintf GaloisGroup, 2: "Further reduce to %o (using normal and known subgroups)\n", 
        InternalGaloisInvarEnvNumber(S); 

      InternalGaloisInvarEnvSieve(S, Sieve);
      vprintf GaloisGroup, 2: "Further reduce to %o (using sieve)\n", InternalGaloisInvarEnvNumber(S);

   if GetVerbose("GaloisGroup") eq 1 then
     printf"%o subgroup class(es) remain after pretests and list of rejected groups\n", InternalGaloisInvarEnvNumber(S);
   end if;   

/* One could add normal subgroups that are sieved out to the list of rejected groups. 
   However, this would require strict rules for the sieve function.
   I.e. we can not encode a ordering of the descent steps by using the sieve function. */    
  
    end if;
    if InternalGaloisInvarEnvNumber(S) eq 0 then
      InternalGaloisInvarEnvClear(S);
      return G, [GaloisRoot(i, S:Bound := 1) : i in [1..Degree(G)]], S;
    end if;
    no_LU :=0;
    found := false;
    possible := [];
    Res := {};
    repeat
      f, L, I, T := InternalHasGaloisInvarEnvNext(S);
      if not f then break; end if;
      A := T[3];
      C := T[2];
      T := T[1];
      if #C eq 0 then 
       C := false;
      end if;
      if #A eq 0 then A := false; end if;
      vprintf GaloisGroup, 1: "%oDoing Stauduhar for group %o%o of index %o = %o", 
              purple, Position(LU, L), normal, Index(G,L), Factorization(Index(G,L));
      if IsTransitive(L) and GetVerbose("GaloisGroup") ge 1 then
       printf " (%o)", InternalPrintGroupIdentification(L);
      end if;
      vprintf GaloisGroup, 1: " with invariant of type %o\n", I`GalInvType;

if not IsExport() and Characteristic(invar_coeff_ring(S)) ne 0 then 
"ne Using ", I`GalInvType, " : deg < ", TotalDegreeAbstract(I), " : deg(tschirni) = ", Degree(T);
end if;
      vtime GaloisGroup, 1: res, g, pf_flag, invar := 
        Stauduhar(G, L, S, max_comp: GalRel := GalRel, PreCompInvar := I, 
                                                       Tschirni := T,
                                                       Coset := C,  
                                                       AllTschirni := A,  
                                                       UseInvarEnv, 
						       ProofEffort := ProofEffort);
 
      if res in [-2..2] then
       v_text := ["(possible descent)","(possible descent)","(subgroup ruled out)",
                  "(proven descent)","(rerun with Tschirni)"][res + 3];      
      else
       v_text := "";
      end if;

      vprint GaloisGroup, 1: red, "Stauduhar returns ", res, normal, v_text;
      if res eq 2 then continue; end if; // invar was changed.

      if (res in [-1,-2]) and (not InternalGaloisInvarGetUseShort(S, I) ) then
        vprint GaloisGroup,2: "Desent almost proven (tschirni confusion), running confirmation step:"; 
        eval_i, is_c, i := inv_setup(I, G,L, GalRel, false, T, A, false, S);
        for tschirni in A do
         if #g gt 0 then
          BB_lift, BB_test, pf_flag, Epsilon := choose_prec(Index(G,L), S, max_comp, tschirni, i, ProofEffort);
          g := scan_cosets(g, tschirni, eval_i, is_c, 2, BB_lift, BB_test, Epsilon, S, Degree(G));
         end if;   
        end for;
        if #g gt 0 then 
          res := 1;
          vprint GaloisGroup,2: "Descent confirmed";
        else 
          res := 0; 
          vprint GaloisGroup,2: "Group no longer possible";
        end if; 
      end if;  

      if res eq 1 or (ShortOK and res eq -1) then
        assbl:=false;
        if assigned G`Blocks and Subfields and SubfieldsComplete then
           assbl:=true;
           Bl:=G`Blocks;
        end if;
        if (#g gt 1) and (not IsNormal(G,L)) then 
          vprint GaloisGroup, 2: 
                   "multiple descents possible, try to intersect...";
          if UseCache() then
            GaloisRootAddPermutation(S, g[1]);
            g := [x*g[1]^-1 : x in g];
          end if;
          GG := &meet [ L^x : x in g];
	  if A cmpeq false then A := {}; end if;
	  if C cmpeq false then C := []; end if;
	  if not Sieve(GG) then
	      T := get_tschirni(S, 3, Minimum(Degree(G), 2+#A), A, I`GalInvType);
	      Include(~A, T);
	      if not IsExport() then 
		  if #A ge 40 then
    S`f;
		    error "way too many transforms!";
		  end if;
	      end if;
		InternalGaloisInvarEnvChangeInvar(S, I, T, C, A);
	    continue;
	  end if;
	  G := GG;
          if _GetGaloisCacheLevel() gt 1 then
            CacheNormalise(~G, S);
          end if;
          Append(~S`DescentChain, <shallow_copy(G), pf_flag>);
          vprint GaloisGroup, 2: "Size of G ", FactoredOrder(G), 
                                 " without intersect: ", FactoredOrder(L);
          if #L ne #G then
            vprint GaloisGroup, 1: 
              RED, "Intersection reduced to ", FactoredOrder(G), 
                   " from ", FactoredOrder(L), normal;
          end if;

        else
          if UseCache() then
            GaloisRootAddPermutation(S, g[1]);
            G := L;
          else
            G := L^g[1];
          end if;
          Append(~S`DescentChain, <shallow_copy(G), pf_flag>);
        end if;
        found := true;
        if assbl then
          G`Blocks:=Bl;
          assert #Bl eq #AllPartitions(G);
        end if;
	break;
      elif res eq 0 then
        found := false;
        if IsNormal(G, L) then
          Append(~rejectedNormalSubGroups, L);
          vprint GaloisGroup, 1: purple, "added wrong subgroup", normal;
        end if;
      elif res eq -1 or res eq -2 then // should correspond to short cosets
	assert assigned invar`GalInvType;
        Append(~possible, <L,g, pf_flag, invar>);
        Include(~Res, res);
      else
        error "Error: this case should not be possible...";
      end if;
    until false; 

    if GetVerbose("GaloisGroup") ge 1 then
      if (not found) and (#possible gt 0) and (GetVerbose("GaloisGroup") ge 2) then
       "OK, we've tried all maximal subgroups, and here's what we've got:";
      end if;
      if found then
        "A descent was definitely found";
      else
        if #possible gt 0 then
          "No descent is (so far) identified";
          "But there are", &+[#a[2] : a in possible], " possiblilies (through use of short cosets)";
          if -1 in Res then
            "and we KNOW there is a descent possible";
          end if;
        else
          "All subgroups are ruled out.";
        end if;
      end if;
    end if;
    if (not found) and (#possible eq 1) and (#possible[1][2] eq 1) and (-1 in Res) then
      vprint GaloisGroup,1:RED,"Assuming unproven descent",normal,"to group of order",Order(possible[1][1]);
      found := true;
      if assigned G`Blocks and Subfields and SubfieldsComplete then      
         Bl:=G`Blocks;
         G := possible[1][1];
         if UseCache() then
           GaloisRootAddPermutation(possible[1][2][1]);
         else
           G := &meet [ G^x : x in possible[1][2]];
         end if;
       G`Blocks:=Bl;
       assert #Bl eq #AllPartitions(G);
      else
         G:=possible[1][1];
         if UseCache() then
           GaloisRootAddPermutation(possible[1][2][1]);
         else
           G := &meet [ G^x : x in possible[1][2]];
         end if;
      end if;
      Append(~S`DescentChain, <shallow_copy(G), possible[1][3]>);
    end if;

    if (not found) and (&+([#a[2] : a in possible] cat [0]) gt 1) then
      vprintf GaloisGroup, 1:  
        "Sorry, short cosets weren't conclusive trying some transformations\n";
//      vprint GaloisGroup, 1: "still ", #possible, "subgroups possible";  
      IndentPush();
      for i in [1..#possible] do
        no_t := 0;
        s_g := Set(possible[i][2]);
        vprint GaloisGroup, 2: BLUE, 
          "starting with ", #s_g, " possibilities in this group", normal;
        repeat
          IndentPush();
	  assert assigned possible[i][4]`GalInvType;
          res, g, pf_flag := Stauduhar(G, possible[i][1], S, max_comp:
                                    AlwaysTransform, Coset := s_g, 
                                    PreCompInvar := possible[i][4], 
				    ProofEffort := ProofEffort);
          IndentPop();                                                
	  if assigned g then
	      s_g := s_g meet Set(g);
	      no_t +:=1;
	  end if;
// Stop if: Group is eliminated or only one descent remains or 3 trys.
        until (no_t gt 3) or (res eq 0) or (#s_g eq 0) or (&+[#a[2] : a in possible] - #possible[i][2] + #s_g eq 1);
        if res eq 0 or #s_g eq 0 then
          possible[i][2] := [ ];
          vprint GaloisGroup, 1: BLUE, 
            "group no longer possible\n", normal;
        else
          possible[i][2] := [x : x in s_g];
          vprint GaloisGroup, 1: BLUE, 
            "left with", #s_g, "possibilities for group",i,"after",no_t,"transformations", normal;
        end if;
      end for;
      IndentPop();
      possible := [x : x in possible | #x[2] gt 0];


      if (#possible eq 1) and (#possible[1][2] eq 1) then   
        vprint GaloisGroup,1:RED,"Assuming unproven descent",normal,"to group of order",Order(possible[1][1]);
      end if;
      
      if #possible gt 1 then
        vprint GaloisGroup, 2: 
                       "multiple descents possible, try to intersect...";
        L := &meet [ &meet [ x[1]^g : g in x[2]] : x in possible];
        possible := [<L, [L.0], false>];
        vprint GaloisGroup, 1: RED, "Assuming unproven descent.",normal,
          "Intersect all possibilities, size left:", #L;
        assert IsTransitive(G) and #G gt Degree(G);
      end if;

      if #possible eq 1 then
        found := true;
        if assigned G`Blocks and Subfields and SubfieldsComplete then      
           Bl:=G`Blocks;
           G := possible[1][1];
           if UseCache() then
             GaloisRootAddPermutation(possible[1][2]);
           else
//why?	     Exclude(~possible[1][2], G.0);
	     //assert #possible[1][2] eq 1;
             G := G^possible[1][2][1];
           end if;
           G`Blocks:=Bl;
           assert #Bl eq #AllPartitions(G);
        else
           G:=possible[1][1];
           if UseCache() then
             GaloisRootAddPermutation(possible[1][2]);
           else
//why?	     Exclude(~possible[1][2], G.0);
	     //assert #possible[1][2] eq 1;
             G := G^possible[1][2][1];
           end if;
        end if;
        Append(~S`DescentChain, <shallow_copy(G), possible[1][3]>);
      else
        error "Sorry, short cosets weren't conclusive, don't know what to do";
      end if;
    end if;
    if not found then
      //It might be the case that tschirhausen roots are stored in r...
      r := [ GaloisRoot(i, S:Bound := 1) : i in [1..Degree(G)]];
      InternalGaloisInvarEnvClear(S);
      return G, r, S;
    end if;
  until IsCyclic(G);
  //It might be the case that tschirhausen roots are stored in r...
  r := [ GaloisRoot(i, S:Bound := 1) : i in [1..Degree(G)]];
  InternalGaloisInvarEnvClear(S);
  return G, r, S;
end function;


/***************************** Starting group (mostly subfield treatment) ******************************************/

// Check correctness of Stauduhar by comparing subfield information. 
// Note that subfields have been treated by Stauduhar completely.
procedure DebugTestSubfields(G,U)
  if not IsExport() then 
    p0 := MinimalPartitions(G);
    p1 := MinimalPartitions(U);
    assert #p0 eq #p1; // Contradiction, Staudhar found a new subfield.
    for tt in p0 do
      phi := Action(G,tt);
      assert phi(G) eq phi(U); // Contradiction, Stauduhar changed the subfield group.
    end for; 
  end if;
end procedure;

// Get an integral primitive element of L as a polynomial expression of a generator of K.
function get_subfield_embedding(K,L,S)
   L_embed_pol := Polynomial(ElementToSequence(L[2]));
   if assigned S`Scale then
    L_embed_pol := Evaluate(L_embed_pol,Parent(L_embed_pol).1 / BaseRing(Parent(L_embed_pol))!S`Scale);
   end if; 
 
// Scale the generator of L to be an integer. 
   if S`Type ne "F_q(t)" then 
     embed_mul := LCM([Denominator(a) : a in Coefficients(L_embed_pol)]);
   else
     val := Min([Valuation(a,S`Prime) : a in Coefficients(L_embed_pol)]);     
     if Type(S`Prime) eq RngUPolElt then
       embed_mul := S`Prime^(-val);
if not IsExport() and (embed_mul ne 1) then "Scaling (1) in identify blocksystem", embed_mul; end if;
     else
       embed_mul := Generators(S`Prime)[1]^(-val);
if not IsExport() then "Scaling (2) in identify blocksystem", embed_mul; end if;
     end if;
     if val le 0 then embed_mul := 1; end if;
   end if;
  
   L_embed_pol := L_embed_pol * embed_mul;
   if S`Type eq "Q(t)" then // have inner denominators (integers instead of polynomials) to clear
    co := Coefficients(L_embed_pol);
    assert {1} eq {Denominator(a) : a in co};
    mul_2 := LCM([Denominator(b) : b in Coefficients(Numerator(a)), a in co]);
    L_embed_pol := L_embed_pol * mul_2;
    embed_mul := embed_mul * mul_2;
   end if;

   return L_embed_pol, embed_mul;
end function;


// Generate GaloisData compatible to S for the subfield L of K that corresponds to the blocksystem bl_ind 
function GaloisDataFromBlocksystem(S, bl_ind, K, L)

   L_embed_pol, embed_mul := get_subfield_embedding(K,L,S);
   f := Polynomial(BaseField(L[1]), DefiningPolynomial(L[1]));

//   L_embed_pol, embed_mul;

   SS:=InternalGaloisDataCreate(S`Prime);
   for i in GetAttributes(MakeType("GaloisData")) do
    if assigned S``i and (not i in ["Scale", "CycleTypes", "KnownSubgroup"]) then
     if (not ISA(Type(K), FldFun)) or (not i in ["Subfields", "SubfieldLattice", "max_comp", "GetRoots"]) then
      SS``i := S``i;
     end if;
    end if;
   end for;

   SS`f := f;
   if ISA(Type(K), FldFun) then
// Function field case. Setup internal data in SS: 
    if Characteristic(K) eq 0 then
     _ := InternalGalQt_ComputeRoots(SS`f, SS`Prime, <5, 5>:S := SS, pAdic := false);
    else 
     _ := InternalGalFqt_setup(Polynomial(FieldOfFractions(CoefficientRing(SS`f)), SS`f), SS`Prime, 5:S := SS);
    end if;
    assert #Set(SS`Roots) eq #SS`Roots;
   else
// Number field case. Have to set up Scale and max_comp on my own:
    if (not IsMonic(SS`f)) or LCM([Denominator(x) : x in Eltseq(f)]) ne 1 then
       Scale := LCM([Denominator(x) : 
              x in Eltseq(Polynomial(FieldOfFractions(BaseRing(Parent(f))), f)/LeadingCoefficient(f))]);
       SS`Scale := Integers()!Scale;
    else
      Scale := 1;   
    end if; 

    if S`Type eq "p-Adic (rel)" then
      SS`max_comp := Ceiling(Maximum([Abs(Evaluate(L[1].1, x)) : x in InfinitePlaces(L[1])]));
      function MyIsInt(x, B, SSS:EasyNonInt := false)
                   assert IsIdentical(SS,SSS);
                   return S`IsInt(x,B,S:EasyNonInt := EasyNonInt); 
      end function;                    
      SS`IsInt := MyIsInt;
    else 
      SS`max_comp := Ceiling(FujiwaraBound(f));
    end if;
    SS`max_comp := Integers()!(SS`max_comp * Scale);
   end if;
   if assigned SS`GetRoots then
     delete SS`GetRoots;
   end if;


// Overwrite the roots in SS to give them the same order as the block system has.
// Ensure that Hensel-lifting will work. I.d. choose precsion large enough
   if S`Type eq "Complex" then
    bnd := 1+Max([AbsoluteValue(GaloisRoot(i,S)) : i in [1..Degree(K)]]); // max_comp may not be set
    prec := (Log(&+[AbsoluteValue(a) : a in Coefficients(L_embed_pol)])  + Degree(L_embed_pol) * Log(S`max_comp)) / Log(10);
    prec := 20 + Ceiling(1.5 * prec);
    eps := 10^-5;
   else
    prec := 1;
   end if;
   if S`Type eq "Q(t)" then
     prec := <1, 4>;
   end if;
// L_embed_pol is an integral polynomial that gives an primitive element of L when evaluated at a SCALED GaloisRoot
 
   prec_cnt := 0;

   L_embed_pol_0  := L_embed_pol;
   repeat
    suc := true;
    if prec_cnt ge 10 then
     error"GaloisDataFromBlocksystem: Too much (2)";
    end if;
    if assigned S`BaseMap then
     L_embed_pol := Polynomial([S`BaseMap(a,prec) : a in Coefficients(L_embed_pol_0)]);
    end if; 
    r := [GaloisRoot(i,S:Prec := prec) : i in [1..Degree(K)]];
    rr := [Parent(a)!Evaluate(L_embed_pol,a) : a in r];    

    if SS`Type eq "Complex" then
     SS`Roots:= [ rr[a[1]] / embed_mul : a in bl_ind]; 
    else
     if assigned SS`BaseMap then
      SS`Roots:= [ SS`Ring| rr[a[1]] / SS`BaseMap(embed_mul,Precision(rr[a[1]])) : a in bl_ind];
     else
      SS`Roots:= [ SS`Ring| rr[a[1]] / embed_mul : a in bl_ind];
     end if; 
    end if;

    SS`Prec:=Minimum([Precision(x) : x in SS`Roots]);
    vprint GaloisGroup, 2: "Setting root precision to ", SS`Prec;
    ff := DefiningPolynomial(L[1]);
    if assigned S`BaseMap then
     ff := Polynomial([S`BaseMap(x, prec) : x in Eltseq(ff)]);
    end if;

    if exists{x : x in SS`Roots | WeakValuation(Evaluate(ff, x)) lt 0} then
     assert SS`Type eq "Complex";
     prec := prec+prec;
     prec_cnt +:= 1;
     vprint GaloisGroup, 2: "Newton error: Increasing precision to ", prec;
     suc := false;
    else
     ffs := Derivative(ff);
     if SS`Type eq "Q(t)" then
       need_more_prec := exists(x){ x : x in SS`Roots | 
       WeakValuation(Coefficients(Evaluate(ff, x))[1]) le 2*WeakValuation(Coefficients(Evaluate(ffs, x))[1])};
     else
       need_more_prec := exists(x){ x : x in SS`Roots | 
       WeakValuation(Evaluate(ff, x)) le 2*WeakValuation(Evaluate(ffs, x))};
     end if;
     if need_more_prec then
      prec := prec+prec;
      prec_cnt +:= 1;
      vprint GaloisGroup, 2: "Newton error: Increasing precision to ", prec;
      suc := false;
     end if;
    end if;
   until suc;
   assert #Set(SS`Roots) eq #SS`Roots;

     function val(x)
       if S`Type eq "Q(t)" then
         v, vv := WeakValuation(x);
         v := <v, vv>;
       elif S`Type eq "Complex" then
         if IsWeaklyZero(x) then return Infinity(); end if;
         v := -Log(Abs(x))/Log(10);
       else
         v := Valuation(x);
       end if;  
       return v;
     end function;


   assert ISA(Type(K), FldFun) or forall{x : x in [1..#bl_ind] | 
     val(rr[bl_ind[x][1]] - embed_mul*SS`Roots[x]) ge 0.25*Minimum(Precision(rr[bl_ind[x][1]]), SS`Prec)};

   SS`DescentChain := [];

// Finally we need some CycleTypes of the subfield
   if SS`Type in {"Complex", "p-Adic"} then
     pl, sl := GetShapes(L[1]);
     SS`CycleTypes := Set(sl);
   else
// ToDo: Calculate shapes directly instead of a GaloisData structure
     SS`CycleTypes := GaloisData(L[1])`CycleTypes;
   end if;

   return SS;
end function;


/* K: Field, L: subfield, S GaloisData of K.

   returns a block system as a list of blocks. Each block is represented by a list of integer.
 
   L[2] is an primitive element of L in L.

   A block is given by all roots s.t. L[2] (viewed as a polynomial) evaluates to the same.
   I.e. we compare p-adic or complex numbers or power series.
*/
function IdentifyBlockSystem(K, L, S) 
//intrinsic IdentifyBlockSystem(K::FldNum, L::Tup, S::GaloisData 
//     : UseGalois:=false, ShortOK := false) 
//                                   ->GrpPermElt,GrpPerm
//{Identifies the block system of a subfield acting on roots mod p}
//tup is the output of an entry of Subfields
// (almost): tup[2] is the image of the primitive element of the
// subfield in the LARGE field.


   L_embed_pol, embed_mul :=  get_subfield_embedding(K,L,S);
   
   if S`Type eq "Complex" then
    bnd := 1+Max([AbsoluteValue(GaloisRoot(i,S)) : i in [1..Degree(K)]]); // max_comp may not be set
    prec := (Log(&+[AbsoluteValue(a) : a in Coefficients(L_embed_pol)])  + Degree(L_embed_pol) * Log(S`max_comp)) / Log(10);
    prec := 20 + Ceiling(1.5 * prec);
    eps := 10^-5;
   else
    prec := 1;
   end if;
   if S`Type eq "Q(t)" then
     prec := <1, 2>;
   end if;
// L_embed_pol is an integral polynomial that gives an primitive element of L when evaluated at a SCALED GaloisRoot
 
   prec_cnt := 0;
   L_embed_pol_0 := L_embed_pol;
   repeat
    if prec_cnt ne 0 then 
     if S`Type eq "Complex" then eps := eps * 10^-(prec div 2); end if;
     prec := prec + prec; 
    end if;
    prec_cnt := prec_cnt + 1;
    if prec_cnt gt 10 then
     S`f;
     error "IdentiftyBlockSystem: Too much";
    end if;
    if (prec_cnt gt 1) or (GetVerbose("GaloisGroup") gt 2) then 
     vprintf GaloisGroup,2: "Trying to identify the blocksystem with precision %o\n",prec;
    end if;

    if assigned S`BaseMap then
     L_embed_pol := Polynomial([S`BaseMap(a,prec) : a in Coefficients(L_embed_pol_0)]);
    end if; 
    r := [GaloisRoot(i,S:Prec := prec) : i in [1..Degree(K)]];
    rr := [Parent(a)!Evaluate(L_embed_pol,a) : a in r];
    if S`Type eq "Complex" then
     for i in [1..#rr] do
      for j in [i+1..#rr] do
       if AbsoluteValue(rr[i]-rr[j]) lt eps then
        rr[j] := rr[i];
       end if;
      end for;
     end for;
    else
      rr := [ChangePrecision(a,prec) : a in rr];   
    end if;
    rr_s := SetToSequence(Set(rr));
    suc := false;
    if #rr_s eq Degree(L[1]) then // 1st precsion check
     bl_ind := [[i : i in [1..#rr] | rr[i] eq a] : a in rr_s];  //Describe the block by a list of indizes
     if #{#a : a in bl_ind} eq 1 and &+[#a : a in bl_ind] eq #rr and
        #Set(&cat bl_ind) eq #rr then // 2nd precision check: all blocks of the same size, each element in one block. 
      suc := true; 
     end if;
    end if;
   until suc;
   if (not IsExport()) and (S`Type eq "Complex") and (eps lt 10^-5) then
     "Blocksystem found with precision ",prec, "and eps = %o",eps;
   end if;

   return bl_ind;
end function;

// Get a starting group in the primitive case by factoring the 2-sum-resolvent:
// ToDo: Generalize to other types
function StartingGroupFromS2Reslovent(K,S)
/* In case we have no good starting group for K we try to use the 2-sum-resolvent.
   This is only helpful for fields of degree > 4.                                      */
 n := Degree(K); 
 if (n le 4) or (not assigned S`CycleTypes) then
   vprint GaloisGroup,2: "2-sum resolvent skipped for degree",n,"field in starting group";
   return Sym(n);
 end if;
// if false and (not S`Type in {"p-Adic", "p-Adic (rel)", "Q(t)"}) then 
 if S`Type eq "Complex" then
   vprint GaloisGroup,2: "2-sum resolvent skipped for degree",n,"field in starting group";  
   return Sym(n);
 end if;

 if #PossibleOrbitSizesOnTwoSets(S`CycleTypes) eq 1 then
   vprint GaloisGroup,2: "2-sum resolvent is useless by shapetest of degree",n,"field in starting group"; 
   return Sym(n);
 end if;
 
 f := DefiningPolynomial(K);
 if Characteristic(K) ne 0 then
 //"\n\n\nchecking MSum char p\n\n\n";
	//#PrimeRing(CoefficientRing(f));
	if IsPrime(#PrimeRing(CoefficientRing(f))) then
	    isc, f := IsCoercible(PolynomialRing(FunctionField(Integers())), f);
	    if not isc then
	       vprint GaloisGroup,2: "2-sum resolvent skipped for degree",n,"field in starting group";  
	       return Sym(n);
	    end if;
	    f := Polynomial(FunctionField(Rationals()), f);
	else
	   vprint GaloisGroup,2: "2-sum resolvent skipped for degree",n,"field in starting group";  
	   return Sym(n);
	end if;
    try 
    "try\n";
    catch e
    "\n\n\nCAUGHT\n\n\n";
       vprint GaloisGroup,2: "2-sum resolvent skipped for degree",n,"field in starting group";  
       return Sym(n);
    end try;
 //"\n\n\nMSum char p will be used\n\n\n";
 end if;
 
 vprint GaloisGroup,2: "Using 2-sum-resolvent of degree",n,"field in starting group"; 
 vtime GaloisGroup,2: res := MSum(f,2);
 if Characteristic (K) ne 0 then
    res := Polynomial(CoefficientField(K), Polynomial(FunctionField(Integers()), res));
 end if;
 vprint GaloisGroup,2: "Factoring resolvent";
 vtime GaloisGroup,2: fac0 := Factorization(res);
 if #fac0 eq 1 then
       vprint GaloisGroup,2: "2-sum-resolvent is irreducible";  
//"MSum irreducible";
       return Sym(n);
 end if;
 vprint GaloisGroup,2 : "Resolvent has",#fac0,"factors";
 if  S`Type eq "Q(t)" then prec := <1,1>; else prec := 1; end if;
 g_loc := sub<Sym(n) | get_frobenius(S,n)>;
 orb2rem := Orbits(g_loc,GSet(g_loc,Subsets({1..n},2)));
 pat := [[] : i in [1..#fac0]];
 repeat
   if assigned S`BaseMap then
     fac := [<Polynomial([S`BaseMap(b,prec) : b in Coefficients(a[1])]),a[2]> : a in fac0];
   else
     fac := fac0;
   end if;  
   orb2todo := orb2rem;
   orb2rem := [];
   rr := [GaloisRoot(i,S:Scaled := false, Prec := prec) : i in [1..n]];
   if prec cmpeq 1 then
     _, pi := ResidueClassField(Parent(rr[1]));
     rr := [pi(a) : a in rr];
     fac := [<Polynomial([pi(b) : b in Coefficients(a[1])]) ,a[2]>: a in fac];
   end if; 
   for act in orb2todo do
     r := &+[rr[i] : i in Representative(act)]; // one resolvent root
     ind := [i : i in [1..#fac] | IsWeaklyZero(Evaluate(fac[i][1],r))];
     assert #ind gt 0;
     if #ind eq 1 then
       Append(~pat[ind[1]], act);
     else
       Append(~orb2rem,act); // This Frobenius-Orbit needs more precision to be identified.
     end if; 
   end for; 
   if (#orb2rem eq 0) then
    vprint GaloisGroup,2:"Orbits of 2-sets identified by using precision",prec;
   end if;
   prec := prec + prec;
 until #orb2rem eq 0;
 pat := [&join a : a in pat]; // Sequence of sets of 2-sets
 assert [Degree(a[1])*a[2] : a in fac] eq [#a : a in pat];

// We use nauty to compute the stabilizer.
 gr := Graph<n | pat[1]>; // a graph with n vertices and an edge for each pair in the first orbit.
 g := AutomorphismGroup(gr);   
 phi := Action(g,GSet(g,Subsets({1..n},2)));
 for i := 2 to #fac do
   g := Stabilizer(phi(g),pat[i]) @@ phi;
 end for;
//"MSum", g;
 return g;
end function;

// G starting group, L, block_systems description of subfields 
// df discriminant of intial field
// We test all combinations of products of discriminants with IsSquare. 
// Returns a smaller starting group and a list of rejected index 2 subgroups
function AdjustByProductsOfDiscriminants(G,L, block_systems, df)
 ker := G;
 kl := []; 
 dl := [];
 for i := 1 to #L do
  phi := Action(G, GSet(G,{Set(a) : a in block_systems[i]}));
  bg,pi := StandardGroup(Image(phi));
  ker_act := (phi^-1)((pi^-1)(bg meet Alt(Degree(bg))));
  if not ker subset ker_act then
   ker := ker meet ker_act;
   Append(~kl, ker_act);
   Append(~dl, Discriminant(DefiningPolynomial(L[i][1]))); 
  end if;
 end for;
 if not ker subset Alt(Degree(G)) then
  ker := ker meet Alt(Degree(G));
  Append(~kl, G meet Alt(Degree(G)));
  Append(~dl, df);
 end if;

 reject := []; // Store rejected groups
//  Test all product combinations of the discriminants to be a square
 G1 := G;
 for ind in Subsets({1..#dl}) do
  if #ind eq 0 then continue; end if; // need at least one factor
  inds := SetToSequence(ind);
  G2 := kl[inds[1]];
  for k := 2 to #inds do
   G2 := InternalSubgroupSum(G, G2, kl[inds[k]]); 
  end for; 
  if IsSquare(&*[dl[i] : i in inds]) then
   G1 := G1 meet G2;
  else
   Append(~reject,G2);
  end if;
 end for;
 G := G1;
 reject := SetToSequence({a meet G : a in reject});
 vprint GaloisGroup,2:"Reduced order of starting group by using discrimiants to ",Order(G);
 vprint GaloisGroup,2:"Also found",#reject,"rejected normal subgroups";
 return G, reject;
end function;


// K field, L subfield, G starting group of L, bl_ind block-system corresonding to L, S GaloisData of K
// Insect the power K[sqrt( Disc(L/K) )]  / Q to get a better starting group for L
// returns a better starting group and rejected index 2 groups.
// Currently only for p-Adic GaloisData and absolute numberfields
function AdjustByTowerSqrtDisc(K,L,G, reject, bl_ind, S, ShortOK); 

 mp_L := Polynomial(BaseField(L[1]), DefiningPolynomial(L[1]));
 if (S`Type ne "p-Adic") or (LeadingCoefficient(mp_L) ne 1) or (not &and [IsIntegral(a) : a in Coefficients(mp_L)]) or
  (Degree(L[1]) ge Degree(K) div 2) then
  return G, [], true; // Case not implemented or approach useless.
 end if; 

 s1 := Stabilizer(G,Set(bl_ind[1])); 
 phi := Action(s1,GSet(s1,Set(bl_ind[1])));
 std,pi := StandardGroup(Image(phi));
 if (std subset Alt(Degree(std))) then // Auxiliary field is known to be = K. 
  return G, [], true;
 end if;

 aux := (std meet Alt(Degree(std))) @@ pi @@ phi; 
 psi := CosetAction(G,aux);
 G0 := psi(G);
 cand := [u`subgroup : u in MaximalSubgroups(G0)];
 pi_reject := [psi(a) : a in reject | Order(psi(a)) lt Order(G0) ];
 cand := [a : a in cand | not a in pi_reject];  
 pi_block := CosetAction(G0, psi(s1));
 ord_block := Order(Image(pi_block));
 cand := [a : a in cand | Order(pi_block(a)) eq ord_block];  

 if #cand eq 0 then // All decents for our resolvent are alreaddy excluded.
  return G, [], true;
 end if;

// All trivial pretests passed. 
 vprint GaloisGroup,2:"Trying to use L[sqrt(Disc(K/L))] in stating group computation.";


 if not assigned S`Scale then scale := 1; else scale := S`Scale; end if;
 rel_disc := Discriminant(MinimalPolynomial(K.1 * scale,L[1])); 
 shift := -1;
 p := S`Prime;
 r_L := PolynomialRing(L[1]);
 repeat
  repeat
   shift := shift + 1;
   pol := Norm((r_L.1 + shift * L[1].1)^2 - rel_disc);
  until Degree(pol) eq 2*Degree(L[1]) and IsSquarefree(pol);
  assert &and [IsIntegral(a) : a in Coefficients(pol)];
  suc := Discriminant(PolynomialRing(GF(p))!pol) ne 0; 
 until (shift gt 20) or suc;
 if (not suc) then 
// "No good polynomial found";
  vprint GaloisGroup,2:"L[sqrt(Disc(K/L))] construction skipped! Can't find a good defining polynomial.";
  return G,[], true;
 end if;

 vprintf GaloisGroup,1:"Using degree %o resolvent representing L[sqrt(Disc(K/L))] for starting group.\n",Degree(pol);
 if shift ne 0 then
  vprintf GaloisGroup,1:"Resolvent uses shift = %o\n",shift;
 end if;

 vprint GaloisGroup,3:"Resolvent polynomial found. Building GaloisData...";
 SS:=InternalGaloisDataCreate(S`Prime);
 for i in GetAttributes(MakeType("GaloisData")) do
  if assigned S``i and (not i in ["Scale", "CycleTypes", "KnownSubgroup", "Subfields", "SubfieldLattice", "max_comp", "GetRoots"]) then
    SS``i := S``i;
  end if;
 end for;
 SS`f := pol;
 Scale := 1;   
 SS`max_comp := Integers()!Ceiling(FujiwaraBound(pol));

 if assigned S`KnownSubgroup then
  SS`KnownSubgroup := sub<Sym(Degree(pol)) | psi(S`KnownSubgroup.1)>;
 else
  SS`KnownSubgroup := sub<Sym(Degree(pol)) | get_frobenius(SS,Degree(pol))>;
 end if;

 r := [GaloisRoot(i,S:Prec := 5) : i in [1..Degree(K)]];
 sl_r := SLPolynomialRing(Integers(),Degree(G):Global); 
 block_marker := Polynomial(ElementToSequence(L[2](L[1].1)));
 block_marker_sc := Evaluate(block_marker,Parent(block_marker).1 / scale); 
 inv := &*[(sl_r.i - sl_r.j) : i,j in bl_ind[1] | i lt j] - shift * Evaluate(block_marker_sc, sl_r.(bl_ind[1][1]));

 rr := [ Evaluate(inv,PermuteSequence(r,i @@ psi)) : i in [1..Degree(pol)]];    
 assert &and [IsWeaklyZero(Evaluate(pol,a)) : a in rr];
 SS`Roots := rr;

 fac := Factorization(pol);
 assert &and [a[2] eq 1 : a in fac]; 
 if #fac gt 1 then
  assert #fac eq 2;
  vprint GaloisGroup,2:"Resolvent is reducible. Relative extension has even Galois group.";
  ind1 := {i : i in [1..#rr] | IsWeaklyZero(Evaluate(fac[1][1],rr[i]))}; 
  ind2 := {i : i in [1..#rr] | IsWeaklyZero(Evaluate(fac[2][1],rr[i]))}; 
  assert (#(ind1 meet ind2) eq 0) and (#(ind1 join ind2) eq #rr) and (#ind1 eq #ind2);
  G1 := Stabilizer(G0,ind1) @@ psi;
  assert IsTransitive(G1);
  return G1,[], true;
 end if; 

 cand2 := [a : a in cand | IsTransitive(a)]; 
 if #cand2 eq 0 then // No possible decent for the resolvent left over
  return G, [a @@ psi : a in cand | Index(G0,a) eq 2], true;
 end if;

 SS`Prec:=Minimum([Precision(x) : x in SS`Roots]);
 aux_nf := NumberField(pol);
 pl, sl := GetShapes(aux_nf);
 SS`CycleTypes := Set(sl);
 SS`DescentChain := [];
 dogo := InternalDivisorOfGroupOrder(SS`CycleTypes);
 vprint GaloisGroup,2:"Calling Stauduhar in degree",Degree(G0),"with starting group of order",Order(G0);
 IndentPush();
// We sieve out those groups, that would refine the Galois group of L
 H := GenericStauduhar(G0, SS, SS`max_comp, 
                              func<X|[ x`subgroup : x in MaximalSubgroups(X:IsTransitive)]>, 
                              func<X| (Order(X) mod dogo eq 0) and (Order(pi_block(X)) eq ord_block) and 
                                       TestShapes(X, SS`CycleTypes) > :
                              Reject := pi_reject, ShortOK := ShortOK, Subfields := false);
 IndentPop();
 this_proven := &and ([true] cat [a[2] : a in SS`DescentChain]);
 if GetVerbose("GaloisGroup") ge 1 then
  if this_proven then printf"Proven "; else printf"Unproven "; end if;
  printf"resolvent group (%o) of order %o found.\n",InternalPrintGroupIdentification(H),#H; 
 end if;
 G1 :=  H @@ psi;
 rej := [u`subgroup @@ psi : u in SubgroupClasses(H:IndexEqual := 2)];
 return G1, rej, this_proven;
end function; 

function GaloisStartingGroup(K, S: Current := false, ShortOK := false, Subfields := true, EarlyAbortOnTwoGroup := false) 
//intrinsic GaloisStartingGroup(K::FldNum, S::GaloisData: 
//               Subfields := true, ShortOK := false) 
//               -> GrpPerm
//{Computes subgroup G of S_n such that Gal(f) \leq G}
//Now it also returns rejected subgroups, i.e. 
//normal subgroups which do not contain Gal(f)
//returns know automorphisms... (Automorphism of what (K, Galois hull of K or Galois group of K)?) -- maybe later
//returns true is starting group is proven, false otherwise
  
  proven := true;
  if not Subfields then
    return Sym(Degree(K)),[],[], proven;
  end if;

  // _, Subfields := IsIntrinsic("Subfields");
  Subfields := intr_subfields;

  n:=Degree(K);
  df:=Discriminant(DefiningPolynomial(K));
  is_square_df := (Characteristic(K) ne 2) and IsSquare(df);
  if is_square_df then
     G := AlternatingGroup(n);
  else
     G := SymmetricGroup(n);
  end if;

  if (assigned S`CycleTypes) and (#S`CycleTypes gt 0) and (#PossibleBlockSizes(S`CycleTypes) eq 0) then
   vprint GaloisGroup, 1 : "GaloisStartingGroup: No subfields by shape test.";
   G := G meet StartingGroupFromS2Reslovent(K,S);
   vprint GaloisGroup,1:"Starting group has order",Order(G);  
   return G,[],[], proven;   
  end if;

  if assigned S`Subfields then
    L := S`Subfields;
  else
    L := Subfields(K);
  end if;

  //remove trivial subfields:
  L:=[sub: sub in L | Degree(sub[1]) lt n and Degree(sub[1]) gt 1];
  if #L eq 0 then //primitive extension
     vprint GaloisGroup,2:"No subfields for starting group.";
     G := G meet StartingGroupFromS2Reslovent(K,S);
     vprint GaloisGroup,1:"2-sum-resolvent results in starting group has order",Order(G);  
     return G, [], [], proven;
  end if;

  vprint GaloisGroup, 1 : "Degrees of subfields",[Degree(a[1]) : a in L];

/* Get intersection of WreathProducts without deep subfield inspection: */
  deg_l := [Degree(a[1]) : a in L];
  ParallelSort(~deg_l, ~L);  
  L2 := [<s[1], K!(s[1].1)> : s in L];
  block_systems := [ IdentifyBlockSystem(K,s, S) : s in L2];  
  G := G meet IntersectionOfWreathProducts(block_systems);

  if Order(G) eq Degree(K) then
       delete S`Subfields;
       vprint GaloisGroup,1:"Starting group has order",Order(G);
       return G, [], [], proven;
  end if;
  if EarlyAbortOnTwoGroup and (PrimeDivisors(Order(G)) eq [2]) then
       vprint GaloisGroup,2:"Early abort with starting group of order",Order(G);
       return G, [], [], proven;
  end if;
 
  vprint GaloisGroup,2:"Starting group as intersection of wreath products of order",Order(G);

 /* L_ext := [];
  for s in L do
    sub := <s[1], K!(s[1].1)>;
    m:=Degree(sub[1]);
    d:=n div m;
    bl_ind := IdentifyBlockSystem(K,sub,S);
    perm := Sym(n)!(&cat bl_ind);
    disc_s := Discriminant(DefiningPolynomial(s[1]));
    if (Characteristic(K) ne 2) and IsSquare(disc_s) then
      G0 := Alt(m);
    else
      G0 := Sym(m);
    end if;
    W := WreathProduct(SymmetricGroup(d), G0);
    W := W^perm; //Gal(f) is subgroup of W !!
    G := G meet W;
    Append(~L_ext,<bl_ind, disc_s>);
    if Order(G) eq Degree(K) then
       delete S`Subfields;
       vprint GaloisGroup,1:"Starting group has order",Order(G);  
       return G, [], [], proven;
    end if;
    if EarlyAbortOnTwoGroup and (PrimeDivisors(Order(G)) eq [2]) then
       vprint GaloisGroup,2:"Early abort with starting group of order",Order(G);  
       return G, [], [], proven;
    end if;
  end for;
  
  vprint GaloisGroup,2:"Starting group as intersection of wreath products of order",Order(G); */

// Add the field discriminant to the list of subfield-discriminants
/*  if not is_square_df then
    Append(~L_ext,<[ [i] : i  in [1..n] ]  , df>);
  end if; */

  reject := [];
// Use all combinations of discriminants:
  if Characteristic(K) ne 2 then

    G, reject := AdjustByProductsOfDiscriminants(G, L, block_systems, df);
  end if;

  if (Order(G) eq Degree(G)) then 
    if UseCache() then
      CacheNormalise(~G, S);
    end if;
    delete S`Subfields;
    vprint GaloisGroup,1:"Starting group has order",Order(G);  
    return G, reject, [], proven; 
  end if;


// Get better wreath product approximation by computing Galois group of subfield 
  for i := 1 to #L do
    if (Degree(L[i][1]) ge 4) or ((Characteristic(K) eq 2) and (Degree(L[i][1]) ge 3)) then
      phi1 := Action(G,GSet(G,{@ Set(a) : a in block_systems[i] @}));
      G_start, phi2 := StandardGroup(Image(phi1));
      if Order(G_start) gt Degree(G_start) then
        vprint GaloisGroup,2:"Computing group of subfield given by",DefiningPolynomial(L[i][1]);
        SS := GaloisDataFromBlocksystem(S, block_systems[i], K, L2[i]);

// It would be better to get and test the shapes before we build up all the GaloisData.
        ttt := IsSnAn(SS`CycleTypes);
        if (ttt eq 2) or (ttt eq 1 and IsEven(G_start)) then
          vprint GaloisGroup,2:"Subfield is S_n/A_n by shape test. Nothing to do!";
          continue i; 
        end if;

        if assigned S`KnownSubgroup then
          SS`KnownSubgroup := sub<Sym(Degree(G_start)) | phi2(phi1(S`KnownSubgroup.1))>;
        else
          SS`KnownSubgroup := sub<Sym(Degree(G_start)) | get_frobenius(SS,Degree(G_start))>; 
        end if;

        if Alt(Degree(G_start)) subset G_start then
          size_G_start := #G_start;
          G_start := G_start meet StartingGroupFromS2Reslovent(L[i][1],SS);
          if (GetVerbose("GaloisGroup") gt 0) and (#G_start ne size_G_start) then
            printf"2-sum-resolvent leads to degree %o subfield starting group of order %o\n",Degree(G_start),#G_start; 
          end if;
        end if;

        dogo := InternalDivisorOfGroupOrder(SS`CycleTypes);
        rej := SetToSequence({phi2(phi1(r)) meet G_start : r in reject});
        rej := [r : r in rej | r ne G_start];
        max_comp := SS`max_comp;
 // ToDo: Find a better sieve at this point
        vprint GaloisGroup,1:"Calling Stauduhar for subfield of degree",Degree(G_start);
        IndentPush();
        vtime GaloisGroup,2:
        H := GenericStauduhar(G_start, SS, Type(max_comp) eq RngIntElt select max_comp else 1, 
                              func<X|[ x`subgroup : x in MaximalSubgroups(X:IsTransitive)]>, 
                              func<X| (Order(X) mod dogo eq 0) and
                                         (Current or AllPartitions(G_start) eq AllPartitions(X)) and 
                                        TestShapes(X, SS`CycleTypes) > :
                              Reject := rej, ShortOK := ShortOK, Subfields := true);
        this_proven := &and ([true] cat [a[2] : a in SS`DescentChain]);
        proven := proven and this_proven;
        IndentPop();
        if GetVerbose("GaloisGroup") ge 1 then
          if this_proven then printf"Proven "; else printf"Unproven "; end if;
          printf"subfield group (%o) of order %o found.\n", InternalPrintGroupIdentification(H),#H;
        end if;    
        DebugTestSubfields(G_start,H);
/*        perm := Sym(n)!(&cat L_ext[i][1]); 
        W := WreathProduct(SymmetricGroup(#L_ext[i][1][1]), H);
        W := W^perm; //Gal(f) is subgroup of W !!
        G := G meet W; */
        G := (H @@ phi2) @@ phi1;
        reject := SetToSequence({G meet a : a in reject});
      else
        vprintf GaloisGroup,2:"Group of degree %o subfield is already identified as regular.\n",Degree(G_start);
      end if;
    end if;
  end for;  

  vprint GaloisGroup,3:"Reduced order of starting group by using subfield groups to ",Order(G);

  if UseCache() then
    CacheNormalise(~G, S);
  end if;

// Tower approach: K / L / Q -> L[Sqrt(Discr(K/L))] / L / Q only in case of exactly one minimal partition and block-size at least 3
  mp := MinimalPartitions(G);
  if (S`Type eq "p-Adic") and (#mp eq 1) then
   mp := Representative(mp); 
   bl_size := #Representative(mp);
   if (bl_size gt 2) then
    ii := [j : j in [1..#L] | Degree(L[j][1]) * bl_size eq Degree(G)];
    assert #ii eq 1;
    i := ii[1];
    vtime GaloisGroup,2 :
    G,reject2, this_proven := AdjustByTowerSqrtDisc(K,L[i],G, reject, block_systems[i], S, ShortOK); 
    proven := proven and this_proven;
    reject := SetToSequence({G meet a : a in reject} join Set(reject2));
   end if;
  end if;

  delete S`Subfields;
  delete S`SubfieldLattice;
  return G, reject, [], proven;
end function;    


procedure CleanGaloisData(S)
      if assigned S`Permutation then
        delete S`Permutation;
      end if;
      if assigned S`Scale then
        delete S`Scale;
      end if;
      if assigned S`Subfields then
        delete S`Subfields;
      end if;
      if assigned S`SubfieldLattice then
        delete S`SubfieldLattice;
      end if; 
end procedure;

/* Here K is always a simple extension of the rationals. */
function GetGaloisDataOrGroup(K: 
  Ring := false, Type := "p-Adic", Prime := false, Prec := false, 
  ShortOK := false, Subfields := true, Current := false, 
  SOnly := false, Time := false, NextPrime := My_np)

  if ISA(ExtendedType(K), FldCyc) then
    Cyclo := true;
    Subfields := false;
  else
    Cyclo := false;
  end if;
  UserPrime := Prime;
  if Ring cmpne false then
    UserPrime := Ring`Prime;
  end if;

  if Prec cmpeq false then
    Prec := 20;
    MinPrec := false;
  else
    MinPrec := Prec;
  end if;

  PrimeList,ShapeList := GetShapes(K:Prime := Prime,MyNextPrime := NextPrime);
  shapes := Set(ShapeList);
  res_IsSnAn := IsSnAn(shapes);

  sub_f := false;
  if Ring cmpeq false then
    if (assigned K`GaloisData) and                                  // In case we have old GaloisData
       (Type eq K`GaloisData`Type) and                              // of the right type
       ((Prime cmpeq false or Prime cmpeq K`GaloisData`Prime)) then // at the right prime
      S := K`GaloisData;
      CleanGaloisData(S);
      if S`Type ne "Complex" then
        Prime := S`Prime;
        UserPrime := S`Prime;
      end if;
    else
      if Type cmpeq "p-Adic" then
        if Prime cmpeq false then
         if res_IsSnAn gt 0 then
          PrimeList,ShapeList := GetShapes(K:Prime := Prime,MyNextPrime := NextPrime,
                                             Count := 20*Degree(K));
          Prime := SelectPrime(PrimeList,ShapeList,2,[]);
         else
          if Subfields and ((#shapes eq 0) or (#PossibleBlockSizes(shapes) gt 0)) then
           vprint GaloisGroup, 1: "Computing subfields...";
           if GetVerbose("Subfields") eq 0 then
              SetVerbose("Subfields", 0); 
           // Problem is that SetVerbose(Subfields) and SetVerbose(GaloisGroup)
           // have a non-empty intersection, but at least for now, I'm not interested
           // in the printing from c.
           end if;

           vtime GaloisGroup,2: sub_f := intr_subfields(K);
          end if;
          if (sub_f cmpne false) and (#sub_f gt 1) then
           Prime := SelectPrime(PrimeList,ShapeList,3,sub_f); 
          else
           Prime := SelectPrime(PrimeList,ShapeList,1,[]);  
          end if;
         end if;
        end if;
        S := InternalGaloisDataCreate(Prime);
        S`Type := "p-Adic";
        S`Base := pAdicRing(Prime);
        S`Prec := Prec;
      elif Type cmpeq "Complex" then
        S := InternalGaloisDataCreate(4);
        S`Type := "Complex";
        S`Prec := Prec;
        S`Base := GetDefaultRealField();
        if MinPrec cmpne false then
          S`MinPrec := MinPrec;
        end if;
      else
        error "Wrong type, only p-Adic and Complex are supported so far";
      end if;
      K`GaloisData := S;
    end if;
  else
    S := Ring;
  end if;

  if (sub_f cmpne false) then
   S`Subfields := sub_f;
  end if;
  S`CycleTypes := shapes;
  f := DefiningPolynomial(K);
  S`f := f;
  if Time then
    S`Time := rec<recformat<Lift>|Lift := 0.0>;
  end if;
  if (not IsMonic(f)) or LCM([Denominator(x) : x in Eltseq(f)]) ne 1 then
      Scale := LCM([Denominator(x) : 
             x in Eltseq(Polynomial(Rationals(), f)/LeadingCoefficient(f))]);
      S`Scale := Scale;
  else
      Scale := 1;   
  end if; 
  n := Degree(K);
  // Sn/ An test:
  // if there is a cycle of length n/2 < p < n-2 then we are Sn or An
  // (p prime)
  isEven := not (1 in {#[b : b in a | b mod 2 eq 0] mod 2 : a in shapes});
  if isEven then isEven := IsSquare(Discriminant(f)); end if;

  if res_IsSnAn gt 0 then // Prime is already adapted to this, no need to recompute it.
    S`max_comp :=  Ceiling(FujiwaraBound(f) * Scale);
    if isEven then
      vprint GaloisGroup, 1: "An found";
      // Since An is a normal subgroup in Sn (the only index 2 subgroup)
      // the ordering of the roots does not matter
      r := [ GaloisRoot(i, S:Bound := 1) : i in [1..Degree(f)]];
      S`DescentChain := [<Alt(n), true>];
      G := Alt(n); 
    else
      vprint GaloisGroup, 1: "Sn found";
      r := [ GaloisRoot(i, S:Bound := 1) : i in [1..Degree(f)]];
      S`DescentChain := [<Sym(n), true>];
      G := Sym(n); 
    end if;
      if SOnly then
	return S;
      end if;
      return G, r, S;
  end if;

// Complete intitialization by side-effects of GaloisRoot
  r := [ GaloisRoot(i, S:Bound := 1) : i in [1..n]];

  //cyclo test...
  if Cyclo then
    R, mR := UnitGroup(Integers(CyclotomicOrder(K)));
    G := Sym(n);
    g := [];
    C, mC := ResidueClassField(Parent(r[1]));
    rt := [ GaloisRoot(i, S:Bound := 1)@mC : i in [1..n]];
    for i in Generators(R) do
      p := Integers()!(i@mR);
      Append(~g, [Position(rt, x^p) : x in rt]);
    end for;
    S`max_comp := FujiwaraBound(f);
    G := sub<G|g>;
    S`DescentChain := [<G, true>];
    S`KnownSubgroup := G;
    if SOnly then
      return S;
    end if;
    return G, [ GaloisRoot(i, S:Bound := 1) : i in [1..n]], S;
  end if;

//  vprint GaloisGroup, 3: "Computed roots, do complex";
  max_comp := Ceiling(Scale * FujiwaraBound(f)); // Error at most 2 * Degree(f)
  if max_comp le 10^5 then // Try to improve FujiwaraBound by one SQRT-iteration
   max_comp := Min(max_comp,Ceiling(Scale * FujiwaraBound(f * Evaluate(f,-Parent(f).1)) / Sqrt(2)));
    // Error of max_comp at most Sqrt(2 * Degree(f)) 
  end if;
  S`max_comp := max_comp;
//f;
//comp_roots;
//max_comp;

//Compute known subgroup -- last step may have changed the prime
  if not assigned S`KnownSubgroup then
    S`KnownSubgroup := sub<Sym(n)|get_frobenius(S,n) >; // TODO: use automorphisms
  end if;

  if not SOnly and not Cyclo then 
    vprint GaloisGroup, 1: "Compute starting group: ";
    vprint GaloisGroup, 2: "=======================";
    G,reject,aut, proven :=GaloisStartingGroup(K,S:ShortOK := ShortOK,
                                          Current := Current, Subfields := Subfields,
                                          EarlyAbortOnTwoGroup := (S`Type ne "Complex")  and (UserPrime cmpeq false));

/* The Galois group will be a 2-group iff we have a chain of subfields of degree 2,4,8,16,..,n=2^k:
   In that case Stauduhar has to treat only index 2 subgroups. Thus, we can switch of the short cosets.
   A p-group with p <> 2 will only be detected in case we have at least two minimal partitions.
   In that case the starting group is very close the the final result. Thus, recomputation of initial data is not efficient. */    
    if (S`Type ne "Complex")  and (UserPrime cmpeq false) and (PrimeDivisors(Order(G)) eq [2]) then
      vprint GaloisGroup, 1: "p-Group of order ", FactoredOrder(G), 
                             "found, looking for different prime...";
      PrimeList,ShapeList := GetShapes(K:Prime := Prime,MyNextPrime := NextPrime,
                                         Count := 20*Degree(K));
      shapes := Set(ShapeList);
      prime := SelectPrime(PrimeList,ShapeList,2, sub_f);
 
      if prime ne Prime then
        vprint GaloisGroup, 1: "Changing prime to ", prime;
        Prime := prime;
        S`Base := pAdicRing(Prime);
        S`Prime := Prime;
        delete S`Roots;
        delete S`Ring;
        delete S`KnownSubgroup;
// Finish initialization by using side-effects of GaloisRoot
        r := [GaloisRoot(i,S:Bound := 1) : i in [1..n]];     
        S`KnownSubgroup := sub<Sym(n)|get_frobenius(S,n) >; // TODO: use automorphisms
      end if; 
// Compute starting group completely 
      G,reject,aut,proven := GaloisStartingGroup(K, S: ShortOK := ShortOK, Subfields := Subfields, Current := Current);
    end if;
  end if;
 
  if SOnly then
    S`DescentChain := [];
    return S;
  end if;

  S`DescentChain := [<shallow_copy(G), proven>];
  assert IsTransitive(G);

  if GetVerbose("GaloisGroup") ge 1 then 
    if GetVerbose("GaloisGroup") ge 3 then
       printf "Have Starting group %o\n. %o\n",G,InternalPrintGroupIdentification(G);
       printf "=========================";
    else
       v_text := Sprintf("Have Starting group (%o) of order %o.",InternalPrintGroupIdentification(G), Order(G));
       printf "%o\n",v_text;
       vprintf GaloisGroup,2: "%o\n", &cat ["=" : i in [1..Min(79,#v_text)]];
    end if;
  end if;
 
  knownsub:= S`KnownSubgroup;
  vprint GaloisGroup, 3: "known subgroup generated by ", GeneratorsSequence(knownsub),
                         " of order ", FactoredOrder(knownsub);

  dogo :=  InternalDivisorOfGroupOrder(shapes);
  
  if Subfields then
    G_fin,r,S := GenericStauduhar(G, S, max_comp, 
      func<X|[ x`subgroup : x in _MaxSub_(X:IsTransitive)]>,
      func<X|IsEven(X) eq isEven and (Order(X) mod dogo eq 0) and
             (Current or AllPartitions(G) eq AllPartitions(X)) and 
             TestShapes(X, shapes)>:
        ShortOK := ShortOK, Subfields := Subfields, 
        SubfieldsComplete := not Current,  
        Reject:=reject,Subgrp:=knownsub, DivisorOfOrder := dogo);
    DebugTestSubfields(G,G_fin); 
    return G_fin,r,S;
  else
    return GenericStauduhar(G, S, max_comp, 
      func<X|[ x`subgroup : x in _MaxSub_(X:IsTransitive)]>,
      func<X|IsEven(X) eq isEven and TestShapes(X, shapes)>:
        ShortOK := ShortOK, Subfields := Subfields, Reject:=reject,Subgrp:=knownsub, 
        DivisorOfOrder := dogo);
  end if;    
end function;


intrinsic EnterStauduhar(G::GrpPerm,S::GaloisData:Subfields := false,Transitive := false, Proven := false) -> GrpPerm, [], GaloisData
{Enter Galois Group algorithm. Transitive: Result is known to be transitive. Subfields: All subfields are encoded in G.
 Proven: Starting group G will be treated as proven by GaloisProof.}

 S`DescentChain := [ <G,Proven> ];
 max_comp := S`max_comp;
 if assigned S`CycleTypes then 
   return GenericStauduhar(G, S, Type(max_comp) eq RngIntElt select max_comp else 1, 
          func<X|[ x`subgroup : x in MaximalSubgroups(X:IsTransitive:= Transitive)]>,
          func<X|TestShapes(X, S`CycleTypes)>:
          ShortOK := false, Subfields := Subfields); 
 else
   return GenericStauduhar(G, S, Type(max_comp) eq RngIntElt select max_comp else 1, 
          func<X|[ x`subgroup : x in MaximalSubgroups(X:IsTransitive:= Transitive)]>,
          func<X| true>:
          ShortOK := false, Subfields := Subfields); 
 end if;
end intrinsic;

intrinsic EnterStauduhar(G::GrpPerm, K::FldNum:Subfields:=false) -> GrpPerm, [], GaloisData
{Enter Galois Group algorithm}
  S:=K`GaloisData;
  if Subfields then
//time   
    G2:=GaloisStartingGroup(K,S:Subfields:=true);
    GG:= G meet G2;
  else
    GG:=G;
  end if;nummm:=#GG;
// GG;  
  d:=Discriminant(K);
  isEven:=IsSquare(d);
  return GenericStauduhar(GG, S, S`max_comp, 
      func<X|[ x`subgroup : x in MaximalSubgroups(X:IsTransitive)]>,
      func<X|IsEven(X) eq isEven and TestShapes(X, S`CycleTypes)>:
        ShortOK := false, Subfields := Subfields);
end intrinsic;

function galois_group_non_simple(K)

    n := #DefiningPolynomial(K);
    deg := Degree(K);

    prim := PrimitiveElement(K);

    dK := DefiningPolynomial(K);
    G, R, S := GaloisGroup(&*dK);

    // find one root in S for each factor in dK
    ind_factor :=  [[i : i in [1..Degree(G)] | 
	    IsWeaklyZero(Evaluate(f,GaloisRoot(i,S:Scaled := false)))] : f in
	    dK];

    assert &and [#ind_factor[i] eq Degree(dK[i])  : i in [1..#dK]];
    assert #Set(&cat ind_factor) eq Degree(G);

    s1 := Stabilizer(G,[a[1] : a in ind_factor]);
    phi := CosetAction(G,s1);
    gal := Image(phi);

    rr_aux := PolynomialRing(Rationals(),#dK);

    bas := [1];
    for i := 1 to #dK do
	bas := [a * rr_aux.i^e : e in [0..Degree(dK[i])-1], a in bas];
    end for;

    // Write primitive element in terms of the basis bas

    co := ElementToSequence(prim);
    rep_poly := 0;
    for i := 1 to #bas do
	cc := ElementToSequence(Evaluate(bas[i],[K.j : j in [1..#dK]]));
	assert Set(cc) eq {0,1};
	ind := [j : j in [1..#cc] | cc[j] eq 1];
	assert #ind eq 1;
	ind := ind[1];
	rep_poly := rep_poly + bas[i] * co[ind];
    end for;

    tran := [i @@ phi : i in [1..Degree(gal)]];
    // the correct numbering of roots:

    gd := InternalGaloisDataCreate(S`Prime);
    gd`Roots := [ Evaluate(rep_poly,
	 [GaloisRoot(a[1]^s,S:Scaled := false) : a in ind_factor]): s in tran];

    roots := [ Evaluate(rep_poly, [GaloisRoot(
	    a[1]^s,S:Scaled := true, Prec := 1) : a in ind_factor]): s in tran];
    gd`Base := S`Base;
    gd`BaseMap := S`BaseMap;
    gd`DescentChain := [<gal, S`DescentChain[1][2]>];
    gd`Ring := S`Ring;
    gd`Scale := S`Scale;
    gd`Type := S`Type;

    return gal, roots, gd;

end function;

intrinsic GaloisGroup(K::FldNum[FldRat]: 
  Ring := false, Type := "p-Adic", Prime := false, Prec := false, 
  ShortOK := false, Subfields := true, Current := false, Old := false,
  Time := false, NextPrime := My_np)
                           -> Grp, [], GaloisData
  {Computes the galois group of (the normal closure) of the field.}

  if not IsSimple(K) then
    return galois_group_non_simple(K);
  end if;
  require IsSimple(K): "The field must be a simple extension of the rationals";

  if Old then
    if Type eq "p-Adic" then
      Al := "pAdic";
    else
      Al := "Real";
    end if;
    return InternalGaloisGroup(K: Al := Al);
  end if;

  return GetGaloisDataOrGroup(K : Ring := Ring, Type := Type, Prime := Prime, Prec := Prec, ShortOK := ShortOK, Subfields := Subfields, Current := Current, Time := Time, NextPrime := NextPrime, SOnly := false);

end intrinsic;

function galois_data_non_simple(K)
end function;

intrinsic GaloisData(K::FldNum[FldRat]: 
  Prime := false, NextPrime := My_np, Subfields := true, Type := "p-Adic")
                           -> GaloisData
  {Computes the data structure of the galois group of (the normal closure) of the field.}

  require IsSimple(K): "The field must be a simple extension";
  // GaloisData for non-simple extensions - not sure this makes sense on its own given 
  // how we calculate the Galois group of non-simple extensions
  if not IsSimple(K) then
    return galois_data_non_simple(K);
  end if;

  return GetGaloisDataOrGroup(K : Prime := Prime, NextPrime := NextPrime, SOnly := true, Subfields := Subfields, Type := Type);

end intrinsic;

intrinsic GaloisGroup(f::RngUPolElt[FldRat]: Ring := false, 
          Type := "p-Adic", Prime := false, Prec := false, 
          ShortOK := false, NextPrime := My_np)
            -> Grp, [], GaloisData
  {Computes the galois group of the splitting field of f}
  d := Lcm([Denominator(x) : x in Eltseq(f)]);
  return GaloisGroup(Polynomial(Integers(), f*d) : Type := Type,
    Ring := Ring, Prime := Prime, ShortOK := ShortOK, NextPrime := NextPrime,
      Type := Type, Prec := Prec);

end intrinsic;

intrinsic GaloisGroup(f::RngUPolElt[FldAlg]: Ring := false, 
          Prime := false, ShortOK := false, NextPrime := My_np)
            -> Grp, [], GaloisData
  {Computes the galois group of the splitting field of f}
  d := Lcm([Denominator(x) : x in Eltseq(f)]);
  return GaloisGroup(Polynomial(Integers(CoefficientRing(f)), f*d) :
    Ring := Ring, Prime := Prime, ShortOK := ShortOK, NextPrime := NextPrime);

end intrinsic;

forward galois_group, galois_data_copy_for_factor;

intrinsic GaloisGroup(f::RngUPolElt[RngInt]: Ring := false, Type := "p-Adic", 
          Prime := false, ShortOK := false, NextPrime := My_np, Prec := 40)
            -> Grp, [], GaloisData
  {Compute the Galois group of the splitting field of the monic and squarefree
    polynomial.}

  require Degree(f) gt 0: "Polynomial must not be constant";
    return galois_group(f, Ring, Prime, ShortOK, NextPrime:Type := Type, Prec := Prec);
end intrinsic;

intrinsic GaloisGroup(f::RngUPolElt[RngOrd[RngInt]]: Ring := false, 
          Prime := false, ShortOK := false, NextPrime := My_np)
            -> Grp, [], GaloisData
  {Compute the Galois group of the splitting field of the monic and squarefree
    polynomial.}

  require Degree(f) gt 0: "Polynomial must not be constant";
    return galois_group(f, Ring, Prime, ShortOK, NextPrime);
end intrinsic;

intrinsic GaloisGroup(f::RngUPolElt[RngOrd]: Ring := false, 
          Prime := false, ShortOK := false, NextPrime := My_np)
            -> Grp, [], GaloisData
  {Compute the Galois group of the splitting field of the monic and squarefree
    polynomial.}

  require Degree(f) gt 0: "Polynomial must not be constant";
  A := AbsoluteOrder(CoefficientRing(f));
  f := Polynomial(A, f);
  G, R, S := galois_group(f, Ring, Prime, ShortOK, NextPrime);

  return G, R, S;

end intrinsic;

function get_prime(f, llf, lf, lF, ff, next_prime)

      p := Degree(f);
      lp := [];
      np := Maximum(20, Degree(f));
      k := CoefficientRing(f);

    if CoefficientRing(f) cmpeq Integers() then
    fs := &* [x[1] : x in llf | Degree(x[1]) gt 0];
    sub_disc_lcms := [LCM([Discriminant(sf[1]) : sf in Subfields(F)]) : F in lF];
      d := LeadingCoefficient(f);
      d *:= Discriminant(fs);
      while #lp lt 1 and np gt 0 do
        repeat
          p := next_prime(p);
        until d mod p ne 0;
        np -:= 1;
        c :=  Factorization(Polynomial(GF(p), ff));
        if exists{x : x in c | x[1] eq Parent(x[1]).1} then
         //we want the linear factors to not vanish
         //Seems like a good idea....
          continue;
        end if;
	if &or[sub_disc_lcm mod p eq 0 : sub_disc_lcm in sub_disc_lcms] then
	    continue;
	end if;
        c := [Integers()| Degree(x[1]) : x in c];
        c := Sort(c);
        if c notin [x[2] : x in lp] or lp eq [] then
          Append(~lp, <p, c, Lcm(c)>);
        end if;
      end while;
      vprint GaloisGroup, 2: "Found some possible primes: ", lp;
    else 
      f := Polynomial(FieldOfFractions(k), f);
      sub_polys := &cat[[DefiningPolynomial(sf[1]) : sf in Subfields(F)] : F in lF];
      while #lp lt Maximum(1, Degree(ff) div 5) and np gt 0 do
        repeat
          p := next_prime(p);
        until Valuation(Discriminant(EquationOrder(k)), p) eq 0;
	lc := Lcm([Denominator(x) : x in Eltseq(f/LeadingCoefficient(f))]);
	repeat
	    p := next_prime(p);
	until Valuation(lc, p) eq 0 and Valuation(Discriminant(EquationOrder(k)), p) eq 0;
	P := Decomposition(MaximalOrder(k), p);
	if forall(x){x : x in P | Degree(x[1]) gt Maximum(Degree(k) div 3, 1)} then
	    continue;
	end if;
	for j in [1 .. #P] do
	    F, mF := ResidueClassField(P[j][1]);
	    fact := Factorization(Polynomial([mF(x) : x in Eltseq(ff)]));
	    if exists(x){x : x in fact | x[2] gt 1} then
		for LP in lp do
		    if Minimum(LP[1]) eq p then
			Exclude(~lp, LP);
		    end if;
		end for;
		break;
	    end if;
	    for g in sub_polys do
		fact := Factorisation(Polynomial([mF(x) : x in Eltseq(g)]));
		if exists(x){x : x in fact | x[2] gt 1} then
		    for LP in lp do
			if Minimum(LP[1]) eq p then
			    Exclude(~lp, LP);
			end if;
		    end for;
		// "Skip Prime ",Norm(p[1])," because of subfield discriminants";
		  break j;
	        end if;
	    end for;
	    c := [Integers() | Degree(x[1]) : x in fact];
	    Append(~lp, <P[j][1], c, Lcm(c)>);
	end for;
      end while;
   end if;
  l := Maximum([Degree(x[1]) : x in lf] cat [1]) div 6;
  u := Maximum([Degree(x[1]) : x in lf] cat [1]) div 2;
  if not exists(x){x : x in lp | x[3] in [l..u]} then
    _, x := Minimum([x[3] : x in lp]);
    x := lp[x];
  end if;
  Prime := x[1];
  vprint GaloisGroup, 1: "Using Prime", Prime, " of shape ", x[2];
  return Prime;
end function;

forward galois_group_for_all;

function galois_group(f, ring, prime, ShortOK, next_prime:Type := "p-Adic", Prec := 40)

    if IsIrreducible(Polynomial(FieldOfFractions(CoefficientRing(f)), f)) then  
	K:=NumberField(Polynomial(FieldOfFractions(CoefficientRing(f)), f):Check := false, DoLinearExtension);
	// Prec only can be set in the absolute case
	if CoefficientField(K) eq Rationals() then
	    return GaloisGroup(K: Ring := ring, Prime := prime, Type := Type,
			    ShortOK := ShortOK, NextPrime := next_prime,
                            Prec := Prec
			    );
	else
	    return GaloisGroup(K: Ring := ring, Prime := prime, Type := Type,
			    ShortOK := ShortOK, NextPrime := next_prime);
	end if;
    end if;
    if Type ne "p-Adic" then
      error "For reducible polynomials, the Type cannot be set";
    end if;  


    if CoefficientRing(f) cmpne Integers() and not IsMonic(f) then
	lllf, lc := Factorization(Polynomial(FieldOfFractions(CoefficientRing(f)), f));
	llf := [];
	Px := PolynomialRing(CoefficientRing(f));
	for lf in lllf do
	    if IsCoercible(Px, lf[1]) then
		Append(~llf, <Px!lf[1], lf[2]>);
	    else
		Append(~llf, <Px!(lc*lf[1]), lf[2]>);
	    end if;
	end for;
	assert #llf eq #lllf;
    else
	llf, lc := Factorization(f);
    end if;
    lf := [car<Parent(f), Integers()>|x : x in llf | Degree(x[1]) gt 1];  // we'll add the linears later
          // also, since the multiplicity is irrelevant for the group, we
          // deal with this also later..

    ff := &* [Parent(f) | x[1] : x in lf];

    vprintf GaloisGroup, 1: "\n%oIntransitive case!%o\n", green, normal;
    vprint GaloisGroup, 1: 
                  green, "computing Galois groups of factors...", normal;
    IndentPush();

    lF := [];
    for g in lf do
	Append(~lF, NumberField(g[1] : Check := false));
    end for;

    if prime cmpeq false then  
	prime := get_prime(f, llf, lf, lF, ff, next_prime);
    end if;  

    return galois_group_for_all(f, prime, ShortOK, lf, lF, llf, ff);
end function;

function galois_group_for_all(f, prime, ShortOK, lf, lF, llf, ff);

    lG := [];
    if #lf gt 0 then
	S := false;
	if Type(lF[1]) eq FldFun then
	    SC := GaloisData(lF[1]);
	    S := GaloisData(lF[1] : Prime := prime);
	    if assigned SC`DescentChain then
		S`DescentChain := SC`DescentChain;
	    end if;
	    S`CycleTypes := SC`CycleTypes;
	end if;
	G, _, S := GaloisGroup(lF[1] : Prime := prime, ShortOK := ShortOK, Ring := S);
	vprint GaloisGroup, 1 : "Factor 1 = ", InternalPrintGroupIdentification(G);
	if assigned S`Permutation then    
	    Append(~lG, <G^S`Permutation, S>);
	else
	    Append(~lG, <G, S>);
	end if;

	Sall := InternalGaloisGroupProductSetup(S, ff, lf);

	for i in [2 .. #lf] do
	      S := galois_data_copy_for_factor(Sall, lf[i][1]);
	    if Type(lF[1]) eq FldFun then
	      SC := GaloisData(lF[i]);
	      S`CycleTypes := SC`CycleTypes;
		if assigned SC`DescentChain then
		    S`DescentChain := SC`DescentChain;
		end if;
	    end if;
	  G, _, S := GaloisGroup(lF[i]:Prime := prime, Ring := S, ShortOK := ShortOK);
	  vprint GaloisGroup, 1 : "Factor ", i, " = ", InternalPrintGroupIdentification(G);
	  f2 := Polynomial(S`Ring, [S`BaseMap(x, 5) : x in Eltseq(f)]);
//"f2 = ", f2;
//"S`Roots = ", S`Roots;
	  assert &and[Valuation(Evaluate(f2, x)) gt 0 : x in S`Roots];
	  //S`Roots;
	  if assigned S`Permutation then    
	    Append(~lG, <G^S`Permutation, S>);
	  else
	    Append(~lG, <G, S>);
	  end if;
	end for;
    end if;

    IndentPop();

    lin_p := 0;
    if lG ne [] then
      G, R, S := InternalGaloisGroupProduct(Sall, lG, ff, lf:ShortOK := ShortOK);
      //assert not assigned S`GetRoots;
    else
      if exists(i){i : i in [1..#llf] | Degree(llf[i][1]) gt 0} then
        G, R, S := GaloisGroup(llf[i][1]:Prime := prime);
        lin_p := i;
      else
        error "Polynomial must not be constant";
      end if;
    end if;

    if assigned S`BaseMap then
	f1 := Polynomial([S`Ring!S`BaseMap(x, 1) : x in Eltseq(f)]);
    else
	f1 := Polynomial(S`Ring, f);
    end if;
//[Evaluate(f1, x) : x in S`Roots];
    assert &and[Valuation(Evaluate(f1, x)) gt 0 : x in S`Roots];
    /*
    Handle multiple roots and linear factors
    */
    F, mF := ResidueClassField(S`Ring);
    r := [mF(x) : x in S`Roots];
    i := 0;
    pr := 1;
    nG := [G];
    lm := [*hom<G -> G | [G.i : i in [1..Ngens(G)]]>*];
    for j in [1..#llf] do
      if Degree(llf[j][1]) eq 0 then
        continue;
      end if;
      if Degree(llf[j][1]) gt 1 then
        i +:= 1;
	pr +:= Degree(llf[j][1]);
        assert llf[j][1] eq lf[i][1];
      end if;
      if Degree(llf[j][1]) eq 1 then
        if lG eq [] and j eq lin_p then
          s := 2;
        else
          s := 1;
        end if;
        for k in [s..llf[j][2]] do
	  if assigned S`BaseMap then
	      rfb, mrfb := ResidueClassField(S`Base);
	      Append(~r, Roots(Polynomial(F, Polynomial(rfb, [mrfb(S`BaseMap(c, 1)) : c in Coefficients(llf[j][1])])), F)[1][1]);
	  else
	      Append(~r, Roots(Polynomial(F, Polynomial(ResidueClassField(S`Base), Coefficients(llf[j][1]))), F)[1][1]);
	  end if;
          Append(~nG, Sym(1));
          Append(~lm, hom<G-> Sym(1)|[Sym(1).0 : l in [1..Ngens(G)]]>);
	  // Fix max_comp : but HOW? This depends on the coeff ring!
	  // Get a GaloisData for each?
	  _, _, sl := GaloisGroup(llf[j][1] : Prime := prime, Ring := galois_data_copy_for_factor(S, llf[j][1]));
	  S`max_comp := Maximum(S`max_comp, sl`max_comp);
        end for;
      elif llf[j][2] ge 2 then
	pr -:= Degree(llf[j][1]);
        for k in [2..llf[j][2]] do
          r cat:= r[pr..pr+Degree(llf[j][1])-1];
          Append(~nG, lG[i][1]);
          Append(~lm, S`Maps[2][i]);
        end for;
	pr +:= Degree(llf[j][1])*llf[j][2];
      end if;
//f1 := Polynomial([S`Ring!S`BaseMap(x, 1) : x in Eltseq(f)]);
//[Valuation(Evaluate(f1, x)) : x in r];
//assert &and[Valuation(Evaluate(f1, x)) gt 0 : x in r];
    end for;
    nG, inc := DirectProduct(nG);
    h := hom<G -> nG | [&* [ (G.i)@lm[x]@inc[x] : x in [1..#lm] ] : i in [1..Ngens(G)]]>;
    S`Roots := ChangeUniverse(r, S`Ring);
//S`Roots;
    r := [ChangePrecision(x, 1) : x in S`Roots];
    if assigned S`BaseMap then
	f1 := Polynomial([S`Ring!S`BaseMap(x, 1) : x in Eltseq(f)]);
    else
	f1 := Polynomial(S`Ring, f);
    end if;
//[Valuation(Evaluate(f1, x)) : x in S`Roots];
    assert &and[Valuation(Evaluate(f1, x)) gt 0 : x in S`Roots];
    // Need to make sure S`Roots satisfy the hensel condition
    if assigned S`BaseMap then
    g := Polynomial([S`BaseMap(c, 5) : c in Coefficients(f)]);
    dg := Derivative(g);
    pr := 1;
//r;
    //assert &and[Valuation(Evaluate(g, x)) gt 2*Valuation(Evaluate(dg, x)) : x in r]; 
    while false and &or[Valuation(Evaluate(g, x)) le 2*Valuation(Evaluate(dg, x)) : x in r] do
	pr +:= 1;
//pr;
	r := [ChangePrecision(x, pr) : x in S`Roots];
//r;
	if pr gt AbsolutePrecision(LeadingCoefficient(g)) then
	    g := Polynomial([S`BaseMap(c, pr + 5) : c in Coefficients(f)]);
	    dg := Derivative(g);
//g;
	end if;
//[<Valuation(Evaluate(g, x)), 2*Valuation(Evaluate(dg, x))> : x in r];
    end while;
    end if;
    S`Roots := r;
//S`Roots;
    // need to overwrite GetRoots to handle the linears and the multiplicities
    if assigned S`GetRoots and Degree(f) gt Degree(ff) then
	old_get_roots := S`GetRoots;
	procedure GetRoots(SS : Prec := 20)
	    assert #SS`Roots eq Degree(f);
	    if Precision(Representative(SS`Roots)) ge Prec then
		return;
	    end if;

	    //removes roots from linear factors but lifts the rest
	    old_get_roots(SS : Prec := Prec);
	    assert #SS`Roots eq Degree(ff);
	    assert #SS`Roots lt Degree(f);

	    //replace roots from linear factors 
	    pr := 1;
	    for j in [1 .. #llf] do
		if Degree(llf[j][1]) eq 1 then
		    /*
		    Think this is wrong and final assertion is wrong
		    if lG ne [] or j ne lin_p then
			Append(~SS`Roots, Roots(Polynomial(S`Ring, [S`BaseMap(c, Prec) : c in Coefficients(llf[j][1])]))[1][1]);
		    end if;
		    */
		    if lG eq [] and j eq lin_p then
		      s := 2;
		    else
		      s := 1;
		    end if;
		    for k in [s .. llf[j][2]] do
			Append(~SS`Roots, Roots(Polynomial(S`Ring, [S`BaseMap(c, Prec) : c in Coefficients(llf[j][1])]))[1][1]);
		    end for;
		elif llf[j][2] ge 2 then
		    for k in [2 .. llf[j][2]] do
			SS`Roots cat:= SS`Roots[pr .. pr + Degree(llf[j][1]) - 1];
		    end for;
		    pr +:= Degree(llf[j][1])*llf[j][2];
		else
		    pr +:= Degree(llf[j][1]);
		end if;
	    end for;
	    //assert #SS`Roots eq Degree(SS`f);
	end procedure;
	S`GetRoots := GetRoots;
    end if;
    S`f := &* [ x[1] : x in llf];
    assert #Image(h) eq #G;
    G := Image(h);
    S`DescentChain := [<shallow_copy(G), true>];
    // return the scaled version to be consistent with the irreducibles
    return Image(h), [GaloisRoot(n, S : Prec := 1) : n in [1 .. #S`Roots]], S;
end function;

intrinsic InternalGaloisGroupProductSetup(S1::GaloisData, f::RngUPolElt, lf::[]) -> GaloisData
{}
    Prime := S1`Prime;

    S := InternalGaloisDataCreate(Prime);
    S`Base := S1`Base;
    assert not assigned S`BaseMap;
    if not assigned S1`BaseMap then
    // Was using ExtendedReals here as the second factor in the CartesianProduct
    // but it caused problems in the function field cases and I can't find an 
    // example which actually needs it ... yet.
	base_map := map<CartesianProduct(FieldOfFractions(CoefficientRing(f)), Integers()) -> S1`Base | t :-> S1`Base!ChangePrecision(S1`Base, t[2])!t[1]>;
    else 
	if S1`Type eq "Q(t)" then
	    base_map := map<CartesianProduct(FieldOfFractions(CoefficientRing(f)), CartesianProduct(Integers(), Integers())) -> S1`Ring | t :-> S1`BaseMap(t[1], t[2])>;
	else
	    base_map := map<CartesianProduct(FieldOfFractions(CoefficientRing(f)), Integers()) -> S1`Ring | t :-> S1`BaseMap(t[1], t[2])>;
	end if;
    end if;

    S`BaseMap := base_map;
    S`Ring := SplittingField(f, base_map);
    S`Type := S1`Type;
    if assigned S1`Prec then
	S`Prec := S1`Prec;
    end if;
    //S`Scale := LCM([LeadingCoefficient(v[1]) : v in lf]);
    if assigned S1`IsInt then
	function IsInt(x, B, SS : EasyNonInt := false)
	    pr := AbsolutePrecision(x);
	    if pr eq 0 then
	      return true, 0;
	    end if;
	    f, c := IsCoercible(SS`Base, x);
	    if not f then
	      vprint GaloisGroup, 1: "no int - ring error";
	      return false, _;
	    end if;
	    return S1`IsInt(x, B, S1 : EasyNonInt := EasyNonInt);
	end function;
	S`IsInt := IsInt;
    end if;

    if assigned S1`max_comp then
	S`max_comp := S1`max_comp;
    end if;

    // Need this to store the prime
    if assigned S1`S then
	S`S := S1`S;
    end if;

    // This is fine since KQ (and hence the mapping is based on the prime
    // which is common among the factors)
    if assigned S1`mKQ then
	S`mKQ := S1`mKQ;
    end if;
    return S;

end intrinsic;

function galois_data_copy_for_factor(S, f)
    SC := InternalGaloisDataCreate(S`Prime);
    SC`f := f;
    SC`Base := S`Base;
    // this will get overwritten so don't bother confusing self by setting here
    if not false and assigned S`BaseMap then
	SC`BaseMap := S`BaseMap;
    end if;
    if ISA(Type(S`Ring), RngSer) or BaseRing(BaseRing(S`Ring)) eq PrimeRing(S`Ring) then
	SC`Ring := S`Ring;
    else
	SC`Ring := UnramifiedExtension(BaseRing(BaseRing(S`Ring)), InertiaDegree(S`Ring)*InertiaDegree(BaseRing(S`Ring)));
    end if;
    SC`Type := S`Type;
    if assigned S`Prec then
	SC`Prec := S`Prec;
    end if;
    //SC`Scale := S`Scale;

    // NOT SURE ABOUT THIS, ARE THEY REALLY THE SAME? NO, BUT WHAT DO I DO? I
    // NEED TO SET IT TO SOMETHING!
    // RECOMPUTE HERE AS IN QtComputeRoots
    if assigned S`S then
    end if;

    if assigned S`mKQ then
	SC`mKQ := S`mKQ;
	ff := Polynomial([S`mKQ(x) : x in Eltseq(f)]);
	assert IsSquarefree(ff);
	KK := NumberField(ff : Check := false);
	SC`S := GaloisData(KK: Prime := S`S`Prime);
    end if;

    return SC;
end function;

intrinsic InternalGaloisGroupProduct(S::GaloisData, lG::[],f::RngUPolElt, lf::[] : ShortOK := false) -> GrpPerm, [], GaloisData
  {}

    require forall{x : x in lG | x[2]`Prime eq lG[1][2]`Prime} :
      "Primes must agree";
    Prime := lG[1][2]`Prime;
    F, mF := ResidueClassField(S`Ring);

    /*
    Split into factors with disjoint splitting fields to all others
    and factors with possibly non-disjoint splitting fields to some others
    */
    /*
    If the group orders = degree of splitting fields are pairwise coprime then 
    there can be no overlapping of splitting fields.
    */
//[Order(x[1]) : x in lG];
    maybe_coprime := {x : x in [1..#lG], y in [1..#lG] | x ne y and GCD(Order(lG[x][1]), Order(lG[y][1])) ne 1}; 
//maybe_coprime;

    vprint GaloisGroup, 1 : "maybe_coprime by group order", maybe_coprime;
    if #maybe_coprime gt 0 then

	if Type(S`Prime) eq RngIntElt then
	    d := [i in maybe_coprime select Discriminant(lf[i][1]) else 1 : i in [1 .. #lf]];
//d;
	    non_coprime := {x : x in maybe_coprime, y in maybe_coprime | x ne y and GCD(d[x], d[y]) ne 1};
	elif Type(S`Prime) eq RngUPolElt and Characteristic(F) gt 0 then
	    /* 
	    A PREVIOUSLY TROUBLESOME EXAMPLE
	    k := GF(17);
	    K<a> := FunctionField(k);
	    _<y> := PolynomialRing(K);
	    f := y^2 + 3;
	    f *:= Polynomial(K, [a, 0, 0, 0, 0, 1]);
	    G, R, S := GaloisGroup(f);

	    something to do with the exact constant fields of extensions
	    by each factor - could be expensive!!!
	    Otherwise if the GCD of the discriminants is 1 then we need to avoid 
	    the quick check
	    */

	    /*
	    What we need here is to know whether the intersection of the splitting
	    fields is a constant field (unramified) extension 
	    But how do we determine what the constant field extensions in 
	    the splitting fields are?
	    And we have no hope except over a rational function field
	    Only need to bother with this if the discriminants are coprime
	    If the discriminants are not coprime then cannot do anything here
	    */

	    /*
	    I THINK WE STILL NEED TO CHECK THE DISCRIMINANTS ARE PAIRWISE 
	    COPRIME HERE
	    THOSE THAT ARE NOT PAIRWISE COPRIME COULD INTERSECT IN A
	    RAMIFIED EXTENSION WHICH WE DON'T CHECK FOR BELOW
	    WE NEED TO CONTINUE HERE ONLY FOR THOSE FACTORS WHOSE 
	    DISCRIMINANTS ARE COPRIME
	    */
	    d := [i in maybe_coprime select Discriminant(lf[i][1]) else 1 : i in [1 .. #lf]];
//d;
	    disc_non_coprime := {x : x in maybe_coprime, y in maybe_coprime | x ne y and GCD(d[x], d[y]) ne 1};
	    //maybe_coprime diff:= disc_non_coprime;
//"Maybe coprime after disc check : ", maybe_coprime;

	    /*
	    Check whether there is a possibility of an unramified
	    equivalently constant field extension
	    IN THE INTERSECTION OF SPLITTING FIELDS (but first in the intersection
	    of stem fields)
	    */
	    de := [i in maybe_coprime select DimensionOfExactConstantField(FunctionField(lf[i][1])) else 1: i in [1 .. #lf]];
//de;
	    /*
	    really_non_coprime should be those whose stem fields possibly contain
	    an unramified/constant field extension
	    Remove these from non_coprime for the moment (put back in later)
	    and check whether the rest may have an unramified extension in the
	    splitting field
	    */
	    decfst_non_coprime := {x : x in maybe_coprime, y in maybe_coprime | x ne y and GCD(de[x], de[y]) ne 1};
	    vprint GaloisGroup, 1 : "disc_non_coprime ", disc_non_coprime;
	    vprint GaloisGroup, 2 : "decfst_non_coprime ", decfst_non_coprime;
	    non_coprime := disc_non_coprime join decfst_non_coprime;
	    maybe_coprime diff:= non_coprime;
//"Maybe coprime after stem check : ", maybe_coprime;
	    vprint GaloisGroup, 2 : "maybe_coprime after stem check ", maybe_coprime;
	    vprint GaloisGroup, 2 : "non_coprime after stem check ", non_coprime;

	    if #maybe_coprime gt 0 then
		/*
		No constant field extension in intersection of stem fields, what 
		about intersection of splitting fields?
		*/
//[CyclicSubgroups(x[1]) : x in lG];
		/* 
		constant field extension will be cyclic in char p
		but its Galois group will be a normal subgroup of
		the whole Galois group (of the factor) whose quotient
		in the whole Galois group is cyclic with the same order
		*/
		cs := [x in maybe_coprime join non_coprime select CyclicSubgroups(lG[x][1]) else [] : x in [1 .. #lG]];
		maybe_coprime := {x : x in maybe_coprime | #cs[x] ne 0};
		vprint GaloisGroup, 2 : "After cyclic subgroup check : ", maybe_coprime;

		Fq := CoefficientRing(S`Prime);
		still_non_coprime := {};
		non_coprime_tested := {};
		for x in maybe_coprime do
		    r1 := LCM([Integers() | r`order : r in cs[x]]);
		    Fqr1 := ext<Fq | r1>;
		    Include(~non_coprime_tested, x);
//(maybe_coprime diff non_coprime_tested) join non_coprime;
		    for y in (maybe_coprime diff non_coprime_tested) join non_coprime do
			r2 := LCM([Integers() | r`order : r in cs[y]]);
			Fqr2 := ext<Fq | r2>;
			if GCD(r1, r2) ne 1 then
			    still_non_coprime join:= {x, y};
			end if;
			if Fqr1 meet Fqr2 ne Fq then
		    	    still_non_coprime join:= {x, y};
			end if;
		    end for;
		end for;
//still_non_coprime;
		maybe_coprime := still_non_coprime diff non_coprime;
		vprint GaloisGroup, 2 : "After cyclic subgroup check : ", maybe_coprime;

		// Maybe only do this if there is a small proportion of factors 
		// in non_coprime since the normal subgroups could be expensive
		ns := [x in maybe_coprime join non_coprime select NormalSubgroups(lG[x][1]) else [] : x in [1 .. #lG]];
		still_non_coprime := {};
		non_coprime_tested := {};
		for x in maybe_coprime do
		    cqx := [r : r in ns[x] | IsCyclic(lG[x][1]/r`subgroup)];
		    cqxo := [r`order : r in cqx];

		    // If this is 1 then the GCD is 1 below and so the if fails
		    if LCM(cqxo) eq 1 then
			continue;
		    end if;

		    fix_fieldsx := [GaloisSubgroup(lG[x][2], r`subgroup) : r in cqx];
		    if Maximum([Degree(Discriminant(f)) : f in fix_fieldsx]) gt 10000 then
			still_non_coprime join:= {x} join (maybe_coprime diff non_coprime_tested) join non_coprime;
			continue;
		    end if;

		    ecf_dim_x := LCM([DimensionOfExactConstantField(FunctionField(f)) : f in fix_fieldsx]);
		    Include(~non_coprime_tested, x);

		    // If this is 1 then the GCD is 1 below and so the if fails
		    if ecf_dim_x eq 1 then 
			continue;
		    end if;

//(maybe_coprime diff non_coprime_tested) join non_coprime;
		    for y in (maybe_coprime diff non_coprime_tested) join non_coprime do
			cqy := [r : r in ns[y] | IsCyclic(lG[y][1]/r`subgroup)];
			cqyo := [r`order : r in cqy];
			fix_fieldsy := [GaloisSubgroup(lG[y][2], r`subgroup) : r in cqy];
			ecf_dim_y := LCM([DimensionOfExactConstantField(FunctionField(f)) : f in fix_fieldsy]);
/*
x, y;
cqxo, cqyo;
ecf_dim_x, ecf_dim_y;
*/
			if GCD(ecf_dim_x, ecf_dim_y) ne 1 and GCD(LCM(cqxo), LCM(cqyo)) ne 1 then 
			    still_non_coprime join:= {x, y};
			end if;
		    end for;
		end for;
		maybe_coprime := still_non_coprime;
		vprint GaloisGroup, 2 : "maybe_coprime after fixed field test ", maybe_coprime;
	    end if;
	    non_coprime join:= maybe_coprime;
	else
	    non_coprime := maybe_coprime;
	end if;	// Coefficient ring
    else
	non_coprime := maybe_coprime;
    end if; //#maybe_coprime gt 0
vprint GaloisGroup, 1 : "Final non_coprime : ", non_coprime;

    S`Prec := 1;
    if #non_coprime gt 0 then
	Snc := galois_data_copy_for_factor(S, &*[lf[x][1] : x in non_coprime]);
	if assigned S`IsInt then
	    Snc`IsInt := S`IsInt;
	end if;
    end if;
    S`f := f;
    vprint GaloisGroup, 1: green, "computing starting group", normal;

    if assigned lG[1][2]`GetRoots then
      procedure GetRoots(SS:Prec := 20)
        if Precision(Representative(SS`Roots)) ge Prec then
	  return;
        end if;
	// This needs to be done here for the reducible case because of the 
	// different splitting field setup to the irreducible case
        SetPrecision(SS`Ring, Prec);
	  r := [];
	  start_roots := 1;
	  //assert SS`Scale eq 1;
	  for i in [1..#lG] do
	    /*
	    What block in SS`Roots are being lifted? make this r1
	    F1 := ResidueClassField(lG[i][2]`Ring);
	    [SS`Ring|F!F1!x : x in lG[i][2]`Roots];
	    */
	    r1 := SS`Roots[start_roots .. start_roots + Degree(lf[i][1]) - 1];
	    start_roots +:= Degree(lf[i][1]);
	    f1 := Polynomial([S`Ring!S`BaseMap(x, Prec) : x in Eltseq(lf[i][1])]);
	    //f1 := Polynomial([lG[i][2]`Ring!lG[i][2]`BaseMap(x, Prec) : x in Eltseq(lf[i][1])]);
//[Valuation(Evaluate(f1, x)) : x in SS`Roots];
	    r1 := [HenselLift(f1, x, Prec) : x in r1];
	    r cat:= r1;
	  end for;
	    SS`Roots := [SS`Ring|ChangePrecision(SS`Ring!x, Prec) : x in r];
	    f2 := Polynomial([S`Ring!S`BaseMap(x, Prec) : x in Eltseq(f)]);
	    assert &and[Valuation(Evaluate(f2, x)) gt 0: x in SS`Roots];
      end procedure;
      S`GetRoots := GetRoots;
      if #non_coprime gt 0 then
	  procedure GetRoots(SS:Prec := 20)
	    if Precision(Representative(SS`Roots)) ge Prec then
	      return;
	    end if;
	    // This needs to be done here for the reducible case because of the 
	    // different splitting field setup to the irreducible case
	    SetPrecision(SS`Ring, Prec);
	      r := [];
	      start_roots := 1;
	      //assert SS`Scale eq 1;
	      for i in [1..#lG] do
		if i in non_coprime then
		    /*
		    What block in SS`Roots are being lifted? make this r1
		    F1 := ResidueClassField(lG[i][2]`Ring);
		    [SS`Ring|F!F1!x : x in lG[i][2]`Roots];
		    */
		    r1 := S`Roots[start_roots .. start_roots + Degree(lf[i][1]) - 1];
		    start_roots +:= Degree(lf[i][1]);
		    f1 := Polynomial([S`Ring!S`BaseMap(x, Prec) : x in Eltseq(lf[i][1])]);
		    //f1 := Polynomial([lG[i][2]`Ring!lG[i][2]`BaseMap(x, Prec) : x in Eltseq(lf[i][1])]);
    //[Valuation(Evaluate(f1, x)) : x in SS`Roots];
		    r1 := [HenselLift(f1, x, Prec) : x in r1];
		    r cat:= r1;
		else
		    start_roots +:= Degree(lf[i][1]);
		end if;
	      end for;
		SS`Roots := [SS`Ring|ChangePrecision(SS`Ring!x, Prec) : x in r];
		f2 := Polynomial([S`Ring!S`BaseMap(x, Prec) : x in Eltseq(f)]);
		assert &and[Valuation(Evaluate(f2, x)) gt 0: x in SS`Roots];
	  end procedure;
	  Snc`GetRoots := GetRoots;
      end if;
    end if;  
    if assigned lG[1][2]`GetPrec then
	//S`GetPrec := func<B, S|Maximum([i[2]`GetPrec(B, i[2]) : i in lG])>;
	function GP(B, S)
	    precs := {i[2]`GetPrec(B, i[2]) : i in lG};
	    assert #precs eq 1;
	    return Rep(precs);
	end function;
	S`GetPrec := GP;
	if #non_coprime gt 0 then
	function GP(B, S)
	    precs := {lG[i][2]`GetPrec(B, lG[i][2]) : i in non_coprime};
	    assert #precs eq 1;
	    return Rep(precs);
	end function;
	Snc`GetPrec := GP;
	end if;
    end if;
    if assigned lG[1][2]`Bound then
	S`Bound := func<t, inv, idx:LowTest := false|Maximum([i[2]`Bound(t, inv, idx : LowTest := LowTest) : i in lG])>;
	if #non_coprime gt 0 then
	Snc`Bound := func<t, inv, idx:LowTest := false|Maximum([lG[i][2]`Bound(t, inv, idx : LowTest := LowTest) : i in non_coprime])>;
	end if;
    end if;
    scales := [x[2]`Scale : x in lG | assigned x[2]`Scale];
    S`Scale := #scales eq 0 select 1 else LCM(scales);
    if #non_coprime gt 0 then 
    scales := [lG[x][2]`Scale : x in non_coprime | assigned lG[x][2]`Scale];
    Snc`Scale := #scales eq 0 select 1 else LCM(scales);
    end if;
      
    pr := 1;
    r := [];
    rnc := [];
    for i in [1 .. #lG] do
      F1, mF1 := ResidueClassField(lG[i][2]`Ring);
      Embed(F1, F);
//"Product root stuff";
//ResidueClassField(CoefficientRing(lG[i][2]`Ring));
      r1 := [F|mF1(x) : x in lG[i][2]`Roots];
      //check finite field coercion
      assert &and[Evaluate(MinimalPolynomial(mF1(x)), F!mF1(x))  eq 0 : x in lG[i][2]`Roots];
      //check coercion back into p-adic
      assert &and[Valuation(Evaluate(Polynomial(S`Ring, MinimalPolynomial(mF1(x))), S`Ring!F!mF1(x))) gt 0 : x in lG[i][2]`Roots];
      if assigned lG[i][2]`BaseMap then
	  f1 := Polynomial([lG[i][2]`Ring!lG[i][2]`BaseMap(x, pr) : x in Eltseq(lf[i][1])]);
	  assert &and[Valuation(Evaluate(f1, x)) gt 0: x in lG[i][2]`Roots];
	  f1 := Polynomial(F, Polynomial(F1, [mF1(x) : x in Eltseq(f1)]));
	  assert &and[Evaluate(f1, mF1(x)) eq 0: x in lG[i][2]`Roots];
	  assert &and[Evaluate(f1, mF1(x)) eq 0: x in r1];
//"lG[i][2]`Roots ok", i;
      end if;
      f2 := Polynomial([S`Ring!S`BaseMap(x, pr) : x in Eltseq(f)]);
      if assigned S`Roots then
	  assert &and[Valuation(Evaluate(f2, x)) gt 0: x in S`Roots];
	  assert &and[Valuation(Evaluate(f2, x)) gt 0: x in lG[i][2]`Roots];
      end if;
      assert &and[Valuation(Evaluate(f2, S`Ring!x)) gt 0: x in r1];
      assert &and[Valuation(Evaluate(f2, S`Ring!x)) gt 0: x in ChangeUniverse(r1, F1)];
      f2 := Polynomial([S`Ring!S`BaseMap(x, pr) : x in Eltseq(lf[i][1])]);
      //Can't coerce from lG[i][2]`Ring to S`Ring
      //assert &and[Valuation(Evaluate(f2, S`Ring!x)) gt 0: x in lG[i][2]`Roots];
      assert &and[Valuation(Evaluate(f2, S`Ring!x)) gt 0: x in r1];
      if ISA(Type(Domain(mF1)), RngSer) then
	  f2 := Polynomial(F, [mF1(c) : c in Eltseq(f2)]);
	  assert &and[Evaluate(f2, x) eq 0: x in r1];
      else
	  assert &and[Evaluate(Polynomial(F, f2), x) eq 0: x in r1];
	  f2 := Polynomial(F, f2);
      end if;
      if assigned lG[i][2]`BaseMap then
	  assert f1 eq f2;
      end if;
//"r1 roots ok", i;
      r cat:= r1;
      if i in non_coprime then
	rnc cat:= r1;
      end if;
    end for;
    while not assigned S`GetRoots and #Set(r) ne Degree(f) do
      pr +:= 2;
      r := [];
      rnc := [];
      for i in [1 .. #lG] do
	F1 := ResidueClassField(lG[i][2]`Ring);
	r1 := [S`Ring|F!F1!x : x in lG[i][2]`Roots];
	f1 := Polynomial(S`Ring, lG[i][2]`f);
	r1 := [HenselLift(f1, x, pr) : x in r1];
	r cat:= r1;
	if i in non_coprime then
	    rnc cat:= r1;
	end if;
      end for;
    end while;
    S`Roots := [S`Ring|ChangePrecision(S`Ring!x, pr) : x in r];
    if #non_coprime gt 0 then
    Snc`Roots := [Snc`Ring|ChangePrecision(Snc`Ring!x, pr) : x in rnc];
    end if;
    f1 := Polynomial([S`Ring!S`BaseMap(x, pr) : x in Eltseq(f)]);
    assert &and[Valuation(Evaluate(f1, x)) gt 0 : x in S`Roots];

    G, incG, projG := DirectProduct([i[1] : i in lG]);
    if (CoefficientRing(f) cmpeq Integers()) then
	max_comp := Ceiling(Abs(LeadingCoefficient(f))*
        Maximum([ x[2]`max_comp/Abs(LeadingCoefficient(x[2]`f)) : x in lG ]));
	if #non_coprime gt 0 then
	max_compnc := Ceiling(Abs(LeadingCoefficient(f))*
        Maximum([ lG[x][2]`max_comp/Abs(LeadingCoefficient(lG[x][2]`f)) : x in non_coprime ]));
	end if;
    elif Type(S`Scale) eq RngIntElt then
	max_comp := Maximum([x[2]`max_comp/x[2]`Scale : x in lG]);
	max_comp := Integers()!max_comp*S`Scale;
	if #non_coprime gt 0 then
	max_compnc := Maximum([lG[x][2]`max_comp/lG[x][2]`Scale : x in non_coprime]);
	max_compnc := Integers()!max_compnc*Snc`Scale;
	end if;
    elif Type(CoefficientRing(f)) eq RngFunOrd then
	max_comp := 2^30;
	max_compnc := 2^30;
//S`Scale;
	for ip in InfinitePlaces(FunctionField(CoefficientRing(f))) do
	    max_comp := Minimum(max_comp, Minimum([-x[2]`max_comp + Valuation(x[2]`Scale, ip): x in lG]) + Valuation(S`Scale, ip));
	    if #non_coprime gt 0 then
	    max_compnc := Minimum(max_compnc, Minimum([-lG[x][2]`max_comp + Valuation(lG[x][2]`Scale, ip): x in non_coprime]) + Valuation(Snc`Scale, ip));
	    end if;
//Valuation(S`Scale, ip);
//[Valuation(x[2]`Scale, ip) : x in lG];
	end for;
	max_comp := -max_comp;
	max_compnc := -max_compnc;
//"Product max_comp :", max_comp;
    else
	max_comp := Minimum([-(x[2]`max_comp - Degree(x[2]`Scale)) : x in lG]);
	max_comp := -max_comp;
	max_comp +:= Degree(S`Scale);
	assert max_comp ge 0;
	if #non_coprime gt 0 then
	max_compnc := Minimum([-(lG[x][2]`max_comp - Degree(lG[x][2]`Scale)) : x in non_coprime]);
	max_compnc := -max_compnc;
	max_compnc +:= Degree(Snc`Scale);
	end if;
    end if;

//RESET the max_comp of the factors?
for i in [1 .. #lG] do
if assigned lG[i][2]`max_comp then
lG[i][2]`max_comp := Maximum(lG[i][2]`max_comp, max_comp);
end if;
end for;

    S`DescentChain := [<shallow_copy(G), true>];
    if #non_coprime gt 0 then
    Snc`DescentChain := [<shallow_copy(G), true>];
    end if;
    if assigned S`max_comp then
	S`max_comp := Maximum(S`max_comp, max_comp);
    else
	S`max_comp := max_comp;
    end if;
    if #non_coprime gt 0 then 
    if assigned Snc`max_comp then
	Snc`max_comp := Maximum(Snc`max_comp, max_compnc);
    else
	Snc`max_comp := max_compnc;
    end if;
    end if;
    S`Maps := <incG, projG>;

    vprint GaloisGroup, 1 : "starting group order ", #G;
    vprint GaloisGroup, 1: green, "done, and now the descents...", normal;
    if #non_coprime eq 0 then
	return G, S`Roots, S;
    end if;
    coprime := {1 .. #lG} diff non_coprime;
//#coprime gt 0;
    if not false and #coprime gt 0 then
//coprime;
	coprime := Sort(Setseq(coprime));
	non_coprime := Sort(Setseq(non_coprime));
	Gc, incGc, projGc := DirectProduct([lG[i][1] : i in coprime]);
	Gnc, incGnc, projGnc := DirectProduct([lG[i][1] : i in non_coprime]);
	m := map<Gnc -> G | x :-> &*[ incG[non_coprime[i]](projGnc[i](x)): i in [1..#non_coprime]]>;
	hmnc := hom<Gnc -> G | [m(Gnc.i) : i in [1..Ngens(Gnc)]]>;

/*	function Sieve(X)
	  if assigned S`Permutation then
	    p := S`Permutation;
	    X := X^p^-1;
	  end if;
	  return forall{z : z in [1..#non_coprime] | projG[non_coprime[z]](hmnc(X)) eq lG[non_coprime[z]][1]};
	end function;

	_gnc, _rnc, _snc := GenericStauduhar(Gnc, Snc, Type(max_compnc) eq RngIntElt select max_compnc else 1, 
		  func<G|[x`subgroup : x in _MaxSub_(G)]>,
		  Sieve:
		  ShortOK := ShortOK, Subfields := false);

*/

        _gnc := Gnc; _snc := Snc;
        orbs := Orbits(Gnc);
        assert #orbs ge 2;
        for k := 2 to #orbs do    
         phi := Action(_gnc,GSet(_gnc, &join [orbs[j] : j in [1..k]])); 
         phi_inv := phi^-1;
         phi_s1 := Action(_gnc,GSet(_gnc, &join [orbs[j] : j in [1..k-1]])); 
         phi_s2 := Action(_gnc, orbs[k]); 
         ord_1 := Order(Image(phi_s1));
         ord_2 := Order(Image(phi_s2));
         my_msg := func< G | [phi_inv(u`subgroup) : u in _MaxSub_(phi(G))] >;  

         function Sieve(X)
          if (Order(phi_s1(X)) ne ord_1) or (Order(phi_s2(X)) ne ord_2) then return false; end if;
	  if assigned S`Permutation then
	    p := S`Permutation;
	    X := X^p^-1;
	  end if;
	  return forall{z : z in [1..#non_coprime] | projG[non_coprime[z]](hmnc(X)) eq lG[non_coprime[z]][1]};
	 end function; 

         _gnc, _rnc, _snc := GenericStauduhar(_gnc, _snc, Type(max_compnc) eq RngIntElt select max_compnc else 1, 
	  	  my_msg,
		  Sieve:
		  ShortOK := ShortOK, Subfields := false); 
        end for;
    
	/*
	map Gc and gnc back to subgroups of G and take direct product there
	Already done the non-coprime descent so no more descent necessary
	*/
	//hmnc := hom<_gnc -> G | [m(_gnc.i) : i in [1..Ngens(_gnc)]]>;
	_gnc := hmnc(_gnc);

	m := map<Gc -> G | x :-> &*[ incG[coprime[i]](projGc[i](x)): i in [1..#coprime]]>;
	hmc := hom<Gc -> G | [m(Gc.i) : i in [1 .. Ngens(Gc)]]>;
	Gc := hmc(Gc);

if not IsExport() then
"ne Done the map back", Gc, #Gc, _gnc, #_gnc;
end if;
	GG, incGG, projGG := DirectProduct(Gc, _gnc);
	m := map<GG -> G | x :-> &*[ G!(projGG[1](x)), G!(projGG[2](x))]>;
	hm := hom<GG -> G | [m(x) : x in Generators(GG)]>;
	GG := hm(GG);
	/*
	Insert Snc`Roots into S`Roots
"All roots :", S`Roots;
non_coprime;
"Non coprime roots :", Snc`Roots, _rnc;
Snc`Roots are the scaled roots, _rnc are the GaloisRoots
Need to be consistent!
	*/
	root_cnt := 1;
	root_cnt_nc := 1;
	for i in [1 .. #lG] do 
	    if i in non_coprime then
		for j in [1 .. Degree(lf[i][1])] do
		    S`Roots[root_cnt] := Snc`Roots[root_cnt_nc];
		    root_cnt +:= 1;
		    root_cnt_nc +:= 1;
		end for;
	    else
		root_cnt +:= Degree(lf[i][1]);
	    end if;
	end for;
/*
"All roots :", S`Roots;
"All roots :", [ChangePrecision(x, 1) : x in S`Roots];
*/
	return GG, S`Roots, S;
    end if;

/*    function Sieve(X)
      if assigned S`Permutation then
        p := S`Permutation;
        X := X^p^-1;
      end if;
      return forall{z : z in [1..#lG] | projG[z](X) eq lG[z][1]};
    end function;

    return GenericStauduhar(G, S, Type(max_comp) eq RngIntElt select max_comp else 1, 
                  func<G|[x`subgroup : x in _MaxSub_(G)]>,
                  Sieve:
                  ShortOK := ShortOK, Subfields := false); */

 orbs := Orbits(G);
 assert #orbs ge 2;
 for k := 2 to #orbs do    
  phi := Action(G,GSet(G,&join [orbs[j] : j in [1..k]])); 
  phi_inv := phi^-1;
  phi_s1 := Action(G,GSet(G,&join [orbs[j] : j in [1..k-1]])); 
  phi_s2 := Action(G, orbs[k]); 
  ord_1 := Order(Image(phi_s1));
  ord_2 := Order(Image(phi_s2));

  my_msg := func< G | [phi_inv(u`subgroup) : u in _MaxSub_(phi(G))] >;  

  function Sieve(X)
   if (Order(phi_s1(X)) ne ord_1) or (Order(phi_s2(X)) ne ord_2) then return false; end if;
    if assigned S`Permutation then
     p := S`Permutation;
     X := X^p^-1;
    end if;
    return forall{z : z in [1..#lG] | projG[z](X) eq lG[z][1]};
   end function; 

   G, R, S := GenericStauduhar(G, S, Type(max_compnc) eq RngIntElt select max_compnc else 1, 
	  	  my_msg, Sieve: ShortOK := ShortOK, Subfields := false); 
 end for;

 return G,R,S;
end intrinsic;

    

