freeze;

import "../RingExt/extras.m" : RingExtAbsoluteDiscriminant, RingExtDifferent,
				RingExtEltDifferent, RingExtIsAbsoluteOrder,
				RingExtIsInert, RingExtIsInertIdeal,
				RingExtIsRamified, RingExtIsRamifiedIdeal,
				RingExtIsSplit, RingExtIsSplitIdeal,
				RingExtIsTamelyRamified, 
				RingExtIsTamelyRamifiedIdeal, 
				RingExtIsTamelyRamifiedOrder,
				RingExtIsTotallyRamified, 
				RingExtIsTotallyRamifiedIdeal, 
				RingExtIsTotallyRamifiedOrder,
				RingExtIsTotallySplit, 
				RingExtIsTotallySplitIdeal,
				RingExtIsUnramifiedIdeal,
				RingExtIsUnramified,
				RingExtIsUnramifiedOrder,
				RingExtIsWildlyRamified,
				RingExtIsWildlyRamifiedIdeal,
				RingExtIsWildlyRamifiedOrder;

import "../../Geometry/CrvCon/points.m" : small_element;

declare verbose NiceReps, 3;

///////////////////////////////////////////////////////////////////////////////
//   Different                                                               //
///////////////////////////////////////////////////////////////////////////////
intrinsic Different(O::RngOrd) -> RngOrdIdl
{Computes the Different of the maximal order O.}

    require IsAbsoluteOrder(O) or IsMaximal(CoefficientRing(O)) :
	"Coefficient ring must be maximal";

  return RingExtDifferent(O);
end intrinsic;


intrinsic Different(a::RngOrdElt) -> RngOrdElt
{Computes the Different of a.}

    return RingExtEltDifferent(a);
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
//   Conductor                                                               //
///////////////////////////////////////////////////////////////////////////////

intrinsic Conductor(O::RngOrd) -> RngOrdIdl
{Computes the Conductor of O in its MaximalOrder.}
  require Category(BaseRing(O)) eq RngInt or
          IsMaximal(BaseRing(O)) : "BaseRing(O) must be Z or a maximal order.";

  M := MaximalOrder(O);
  FO := FieldOfFractions(O);

  if Category(BaseRing(O)) eq RngInt then
    B := [FO| x: x in Basis(M) ];
    den := LCM([Denominator(x) : x in B ] );
    B := [ Transpose(AbsoluteRepresentationMatrix(O!(x*den))) : x in B ];
    B := VerticalJoin(B);
    B := BasisMatrix(Image(B));
    B := Matrix(FieldOfFractions(BaseRing(O)), B);
    B := B^-1*den;
    B := Matrix(BaseRing(O), B);
    return ideal<O | Transpose(B)>; 
  else
    n := Degree(O);
    k := FieldOfFractions(BaseRing(O));
    B := [FO| x: x in Basis(M) ];
    B := [ Transpose(RepresentationMatrix(x)) : x in B ];
    B := VerticalJoin(B);
    idO := [ x[1] : x in PseudoBasis(Module(O)) ];
    idM := [ x[1] : x in PseudoBasis(Module(M)) ];
    id := [ idM[j] / idO[i] : i in [1..n], j in [1..n] ];
    B := [ car<PowerIdeal(k),
               RSpace(k, n)> |
               <id[i], B[i]> : i in [1..n*n] ];
    B := Module(B);
    B := Dual(B);
    return ideal<O | B>;
  end if;

end intrinsic; 

///////////////////////////////////////////////////////////////////////////////
//   subset                                                                  //
///////////////////////////////////////////////////////////////////////////////

intrinsic 'subset'(I1::RngOrdIdl, I2::RngOrdIdl) -> BoolElt
{True iff I1 is a subset of I2}
  require Order(I1) eq Order(I2) : "Ideals must belong to the same order";

  return I1 meet I2 eq I1;
end intrinsic;  
intrinsic 'subset'(I1::RngOrdFracIdl, I2::RngOrdFracIdl) -> BoolElt
{"} // "
  O := Order(I1);
  require O eq Order(I2) : "Ideals must belong to the same order";
  
  d := Lcm(Denominator(I1), Denominator(I2));
  return (O!!(I1*d))  subset (O!!(I2*d));
end intrinsic;  


///////////////////////////////////////////////////////////////////////////////
//   IsAbsolute                                                              //
///////////////////////////////////////////////////////////////////////////////

intrinsic IsAbsoluteOrder(O::RngOrd)->BoolElt
{Returns true iff the order is absolute, i.e. an extension of Z}
    return RingExtIsAbsoluteOrder(O);
end intrinsic;  

intrinsic IsAbsoluteField(F::FldAlg)->BoolElt
{Returns true iff the field is absolute, i.e. an extension of Q}
  return BaseField(F) cmpeq Rationals();
end intrinsic;  


///////////////////////////////////////////////////////////////////////////////
//   SetClassGroupBounds                                                     //
///////////////////////////////////////////////////////////////////////////////

intrinsic SetGRH()
{SetClassGroupBounds(\"GRH\")}
  SetClassGroupBounds("GRH");
end intrinsic;

intrinsic SetClassGroupBounds(arg::Any)
{Set the proof bound for class group computations in all number fields.
The recommended usage is SetClassGroupBounds(\"GRH\").}

  if Type(arg) eq RngIntElt then
     print "SetClassGroupBounds: for best results use\nSetClassGroupBounds(\"GRH\");";
     m := map< PowerStructure(RngOrd) -> Integers() | R :-> arg >;
     SetClassGroupBoundGenerators(m);
  elif arg eq "GRH" then
     m := map< PowerStructure(RngOrd) -> Integers() | R :-> GRHBound(R) >;
     SetClassGroupBoundGenerators(m);
  elif arg eq "PARI" then
     print "SetClassGroupBounds: PARI option obselete, using GRH bound";
     m := map< PowerStructure(RngOrd) -> Integers() | R :-> GRHBound(R) >;
     SetClassGroupBoundGenerators(m);
  else require false :
     "The given argument must be an integer, or the string \"GRH\""; 
  end if;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
//   Nice reps modulo K^n                                                    //
///////////////////////////////////////////////////////////////////////////////

function LLLBasis(I)
  ZK := Order(I);
  FF := FieldOfFractions(ZK);
  assert IsAbsoluteOrder(ZK);
  bm := LLLBasisMatrix(I);
  basis := [FF! Eltseq(bm[i]) : i in [1..Nrows(bm)]];
  return basis;
end function;


// TO DO: IsIntegral will return the denominator d
function make_integral(x, n)
  s := 1;
  i := 1;
  while not IsIntegral(x) do
    d := Denominator(x^i);
    if d eq 1 then
      i +:= 1;
      continue;
    end if;
    s *:= d;
    x *:= d^n;
  end while;
  return x, s;
end function;


intrinsic NiceRepresentativeModuloPowers(x::FldElt, n::RngIntElt : Effort:=1, FracIdeal:=0)
       -> FldAlgElt, FldAlgElt
{A nice (integral) representative in K^*/(K^*)^n for an element x in a number field K.}

  require n ge 2 : "The second argument should be an integer greater than 1";


if false then // NEW

  F := Parent(x);
  FF := ISA(Type(F), FldOrd) select F else FieldOfFractions(Integers(F));
ZF := Integers(FF);
  xx := FF! x;
  d := Denominator(xx);
  dd := FF! d;
  // PowerProductSimplify assumes the result is integral
printf "PowerProductSimplify: "; time
  g, e := PowerProductSimplify([xx*dd], [1], n);
  if d gt Discriminant(Integers(FF)) then
printf "PowerProductSimplify (denom): "; time
    gd, ed := PowerProductSimplify([dd], [1], n);
    g cat:= gd;
    e cat:= [-i : i in ed];
  elif dd ne 1 then
    Append(~g, dd);
    Append(~e, -1);
  end if;
/*
  h := [Universe(g)| ];
  for i := 2 to #g do
    bool, hi := IsPower(g[i], n);
    assert bool;
    Append(~h, hi);
  end for;
*/
printf "PowerProduct: "; time
  x1 := F! PowerProduct(g, [i mod n : i in e]);
printf "PowerProduct: "; time
  z1 := F! PowerProduct(g, [i div n : i in e]);
  y1 := 1/z1;
assert IsIntegral(x1);
//assert x eq x1*z1^n;
ok := x eq x1*z1^n;
if not ok then err := x1*z1^n/x; assert false; end if;
  return x1, y1;

end if;

  //////////////////////////////////////////////////////////////////////////

  // OLD

  time0 := Cputime();

  F := Parent(x); 
  rat := Type(F) eq FldRat;
  require rat or ISA(Type(F),FldAlg) and BaseField(F) eq Rationals() :
         "The first argument should be an element in a non-relative number field";

  L := rat select F else NumberField(F);
  d := Degree(L);
  alpha := L!x;

  if d eq 1 then 
    fact, sign := FactorizationOfQuotient(Rationals()! alpha);
    alpha1 := sign * &* [F| t[1]^(t[2] mod n) : t in fact];
    Gamma := 1 / &* [F| t[1]^(t[2] div n) : t in fact];
    assert alpha1 eq alpha*Gamma^n;
    return alpha1, Gamma;
  end if;

  // Define bb, a fractional ideal, such that alpha*bb^n is contained in OL
  OL := Integers(L);
  FL := FieldOfFractions(OL);
  FracIdeals := PowerIdeal(FL);
  if FracIdeal cmpeq 0 then
    f := Factorization(alpha*OL);
    e := [-(t[2] div n) : t in f];
    bb := &* [FracIdeals| f[i][1]^e[i] : i in [1..#f] | e[i] ne 0];
  else
    ideal_ok, bb := IsCoercible(FracIdeals, FracIdeal);
    require ideal_ok : "The optional parameter FracIdeal should be a fractional ideal of "
                     * "the number field containing the given element alpha";
  end if;

  size := Max(Flat([ [Abs(Numerator(c)),Denominator(c)] : c in Eltseq(FL!alpha) ]));
  prec := Max([100, GetKantPrecision(), Ilog(10,size) div n]);
 
  vprintf NiceReps: "Computing nice representative mod %o\n", 
                    case< n | 2:"squares", 3:"cubes", default:IntegerToString(n)*"th powers">;
  IndentPush();

  alpha0 := alpha;
  Gamma := L!1;  // records the transformation
  for it := 1 to 100 do  // iterate until the result is nice (shouldn't take many iterations)

      vprintf NiceReps: "Current representative has log size %o\n", Ilog(10,size);

      Bbb := LLLBasis(bb);

      cob1 := Matrix(Rationals(),d,d,[Eltseq(L!x): x in Bbb]);

      // Compute inner product on lattice formed by bb in L tensor Reals
      while true do
        vprintf NiceReps: "Using precision %o for Conjugates\n", prec;
        function powers(x)
          L := [x^0];
          for i := 1 to d-1 do
            Append(~L, L[i]*x);
          end for;
          return L;
        end function;
        pow := [powers(zz) : zz in ChangeUniverse(Conjugates(L.1:Precision:=prec), ComplexField(prec))];
        bb_basis_conjs := [ [ &+[ Eltseq(L!x)[i]*pw[i] : i in [1..d]]
                            : pw in pow]  
                          : x in Bbb ];
        M := Matrix( ComplexField(prec), d,d, bb_basis_conjs);
        alpha_conjs := [&+[ Eltseq(alpha)[i]*pw[i] : i in [1..d]] 
                          : pw in pow];
        D := DiagonalMatrix( RealField(prec), [Abs(x)^(2/n): x in alpha_conjs]);
        M_conj := Matrix(BaseRing(M), [[Conjugate(M[i,j]): j in [1..d]] : i in [1..d]]);
        A := M*D*Transpose(M_conj);
             // Inner product on bb, where for each archimedean absolute value v,
             // the coordinate corresponding to v is weighted by |alpha|_v ^(1/n).
             // Therefore, short vectors will be elements gamma in bb
             // for which |alpha*gamma^n|_v is small for all v.
        // Check if precision was sufficient 
        prec_problem := "Increasing precision for Conjugates in NiceRepresentativeModuloPowers";
        if Max([Abs(Im(x)): x in Eltseq(A)]) gt 10^(-20) then
           vprint NiceReps: prec_problem; prec *:= 2; continue; end if;
        A := Matrix([[ Re(A[i,j]) : j in [1..d]] : i in [1..d]]);  // make A exactly real
        if Max([Abs(x): x in Eltseq(A-Transpose(A))]) gt 10^(-20) then
           vprint NiceReps: prec_problem; prec *:= 2; continue; end if;
        break;  // no precision problems now
      end while;

      // Find short vectors under the quadratic form
      vprint NiceReps: "Doing LLL reduction";
      A := A + Transpose(A);  // make A exactly symmetric
      A_red, cob := LLLGram(A);
      _, idx := Min([ RealField(10)!Abs(A_red[i,i]) : i in [1..d] ]);
      cob := cob*cob1;
      gamma := L! Eltseq(cob[idx]);

      // modify alpha if desirable,
      // update Gamma and size,
      // recurse or return
      alpha_new := alpha*gamma^n;
      newsize := Max([ Abs(Numerator(coeff)) : coeff in Eltseq(FL!alpha_new) ]);
      better := newsize lt size;
      if better then
         alpha := alpha_new;
         Gamma *:= gamma;
         size := newsize;
      end if;
      vprintf NiceReps: "NiceRepresentativeModularPowers time %os\n", Cputime(time0);

assert alpha eq alpha0*Gamma^n;

      if better then
         vprintf NiceReps: "NiceRepresentativeModuloPowers iteration #%o\n", it+1;
         bb *:= ideal< OL | 1/gamma >;
      else
         break;
      end if;

  end for;  // it

assert IsIntegral(alpha); // for now

  alpha, s := make_integral(alpha, n);
  Gamma *:= s;

  assert alpha eq alpha0 * Gamma^n;

  IndentPop();
  return F! alpha, F! Gamma;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
//   pSelmer                                                                 //
///////////////////////////////////////////////////////////////////////////////

intrinsic pSelmerGroup(p::RngIntElt, S::SetEnum :
                       Integral := true, Nice:=true, Raw:=false) 
       -> GrpAb, Map
{Computes the (p, S)-Selmer group of the field containing the prime ideals in S}

  require forall{x : x in S | IsPrime(x)}:
    "S must contain only prime ideals";
  require p gt 1 and IsPrimePower(p) :
    "The first argument must be a prime power";
  if not IsPrime(p) then
    require not Raw: "Raw option is not supported for prime powers"; 
                   // TO DO: maybe Raw does work?
    Nice := false; // TO DO: Nice would only need trivial changes
  end if;

  U := Universe(S);
  if Type(U) eq RngInt then
    O := Integers();
    S := [s*O : s in S];
  elif U cmpeq PowerStructure(RngInt) then
    O := Integers();
  else
    require Type(U) eq PowIdl: "The second argument should be a set of ideals";
    O := Ring(Universe(S));
  end if;
  if Type(O) eq RngInt then 
    require not Raw: "Raw option is not available over Q";
  else 
    require IsAbsoluteOrder(O) and IsMaximal(O):
      "The ideals must be defined in an absolute maximal order";
  end if;

  // degree 1 case
  if Type(O) eq RngInt or AbsoluteDegree(O) eq 1 and not Raw then
    S := Sort([Integers()| Minimum(s) : s in S]);
    if IsEven(p) then 
      G := AbelianGroup([2] cat [p : s in S]);
      S := [Integers()| -1] cat S;
    else
      G := AbelianGroup([p : s in S]);
    end if;

    function fromG(g)
      c := Eltseq(g);
      return &* [O| S[i]^c[i] : i in [1..#c]];
    end function;

    function toG(x)
      x := Rationals()! x;
      seq := [Integers()| ];
      for s in S do 
        if s eq -1 then
          v := (x gt 0) select 0 else 1;
        else
          v := Valuation(x,s) mod p;
        end if;
        Append(~seq, v);
      end for;
      g := G!seq;
      error if not IsPower(x/fromG(g), p), "Element does not belong to the pSelmer group";
      return g;
    end function;

    return G, map< FieldOfFractions(O) -> G | x :-> toG(x), g :-> fromG(g) >;
  end if;

  // step 1: enlarge S to have enough primes to generate the
  // p-part of the class group:
  if Type(O) eq RngOrd then
     C, mC := ClassGroup(O: Proof := "Current");
  else
     C, mC := ClassGroup(O);
  end if;
  Cp := sub<C|[p*C.i : i in [1..Ngens(C)]]>;
  q, mq := quo<C|Cp>;

  SS := {Parent(1*O)|};

  s := sub<q | [ x@@mC @ mq : x in S]>;
  p_Z := 2;
  while s ne q do
    lp := Factorization(p_Z*O);
    lp := [ x[1] : x in lp | Norm(x[1]) le 1000 or Degree(x[1]) eq 1];
    for i in lp do
      if i in S then
        continue;
      end if;
      I := i@@mC@mq;
      if not I in s then
        Include(~SS, i);
        s := sub<q| s, I>;
      end if;
      if s eq q then
        break;
      end if;
    end for;
    p_Z := NextPrime(p_Z);
  end while;

//"S was originally", S;
//"Added primes: ", SS;

  // OK that was easy, now the "Raw" version of the units..
  U, mU, bU := SUnitGroup([Universe(S)| x : x in S join SS]:Raw);

  FB := FactorBasis(O);
  bU_primes := Seqset(FB) join S;

//facts := [Factorization(b*O) : b in Eltseq(bU)];
//for f in facts do assert forall{t: t in f | t[1] in bU_primes}; end for;

  // Now get the subgroup of U/pU that has valuations divisible by p at SS
  // So we form the valuation map from U/pU to a p-group and take the kernel

  if #SS eq 0 then
    k := U;
  else
    pG := AbelianGroup([p : x in SS]);
    vbU := Matrix([[Valuation(x, y) : y in SS] : x in Eltseq(bU)]);
    h := hom<U -> pG | [ pG!Eltseq((U.i@mU) * vbU) : i in [1..Ngens(U)]]>;
    k := Kernel(h);
  end if;

  KpS, mKpS := k / sub<k|p*U>;

  if Integral or p eq 2 then
    // TO DO: without horribly nesting?
    mKpS := map< k -> KpS | x :-> x@mKpS, 
                            x :-> k! [c mod p : c in Eltseq(x@@mKpS)] >;
  end if;

  // Now the painful bit: the maps to and from KpS...
  // We use the indirect, class field theoretic approach for discrete logs
  // and to make things worse, we delay the creation until we have to...

  // Changed codomain to FieldOfFractions of O instead of O
  if Nice then 
    bUseq := Eltseq(bU);
    from_KpS := map<KpS -> FieldOfFractions(O) |
                      x:-> NiceRepresentativesModuloPowers(x @@ mKpS @ mU,  bUseq, p)[1]>;
  else
    from_KpS := map<KpS -> FieldOfFractions(O) | 
                      x:-> PowerProduct(bU, x @@ mKpS @ mU)>;
  end if;

  // TO DO (maybe): the discrete log map when p is a prime power
  if not IsPrime(p) then
    function to_KpS(x) 
      error "Map is not implemented in this direction!\n"*
            "The \"inverse\" direction is implemented, from the pSelmerGroup to K*/(K*)^p";
    end function;          
    return KpS, map< FieldOfFractions(O)->KpS | x:->to_KpS(x), y:->from_KpS(y) >;
  end if;

  Fp := GF(p);
  pG := AbelianGroup([p : x in [1..Ngens(KpS)]]);
  get, set := NewEnv(["Primes"]);
  set("Primes", [car<Parent(1*O), U>|]);
  prod_S := &meet S;

  function to_KpS(x) 
    g,s := NewEnv(["Mat", "Right"]);
    s("Mat", []);
    s("Right", []);

    /*
    Don't check that x is valid, i.e. has p-power valuations outside S.
    This behaviour is documented.

    // Note that x may be large, and may have large valuations
    b := x*O; 
    for s in S do
      b := b / s^Valuation(x,s);
    end for;
    if not IsPower(b, p) then
      error "element must have valuations divisible by ", p, "outside S";
    end if;
    */

    one_ideal := function(P, elt)
      if Denominator(elt) mod Minimum(P) eq 0 then
//        "one_ideal: den";
        return false, _;
      end if;
      FF, map := ResidueClassField(P);
//      o_elt := elt;
      elt := map(elt);
      if elt eq 0 then
//        "one_ideal: rf";
        return false, _;
      end if;
      m1 := #FF - 1;
      mp := m1 div p;
//      assert mp*p + 1 eq Norm(P); // checks Norm(P) is 1 mod p
      elt := elt^mp;
//      assert map(o_elt^mp) eq elt;
      elt := Log(elt);
      // if x is a multiplicative generator for FF, then
      // - x has order Norm(P)-1 in the group
      // - x^((Norm(P)-1)/p) has order p (and is a primitive root of unity)
      // We need Sqrt[p](o_elt)^Norm(P) = zeta_p^r \Sqrt[p](o_elt) mod P 
      // and we need that r!
//      assert Order(PrimitiveElement(FF)) eq m1;
//      assert (o_elt^mp - (PrimitiveElement(FF)@@map)^elt) in P;
//      assert p ne 2 or o_elt^mp - (-1)^Integers()!Fp!((elt * p) div m1) in P;
      return true, Fp!((elt * p) div m1);
    end function;

    ebU := Eltseq(bU);

    // TO DO: Pr should be some kind of array
    procedure process(~Pr, x, P)
//      "process", P;
      i := Position([x[1] : x in Pr], P);
      if i eq 0 then
        // new prime
        // needs to be added to Pr
        S := Matrix(Fp, #ebU, 1, []);
        for j := 1 to #ebU do
          bool, f := one_ideal(P, ebU[j]);
          if not bool then
//            "fail:1";
            return;
          end if;
          S[j,1] := f;
        end for;
        S := [ (mU(U.i)*S)[1] : i in [1..Ngens(U)]];
        S := U!Eltseq(S);
        Append(~Pr, <P, S>);
        set("Primes", Pr);
      else
        S := Pr[i,2];
      end if;

      bool, f := one_ideal(P, x);
      if not bool then
//        "fail:2";
        return;
      end if;

      s("Mat", Append(g("Mat"), Eltseq(S)));
      s("Right", Append(g("Right"), f));
//      "return: ", S, f, P;
    end procedure;

    function done()
      if #g("Mat") eq 0 then
        return false;
      end if;
      return Rank(Matrix(Fp, g("Mat"))) eq Ngens(KpS);
    end function;

    Pr := get("Primes");
    for i in Pr do
      process(~Pr, x, i[1]);
    end for;

    if not done() then
      if #Pr eq 0 then
        p_Z := p;
      else
        p_Z := Maximum([Minimum(x[1]) : x in Pr]);
      end if;
      flag := true;
      while flag do
        p_Z := NextPrime(p_Z);
        lp := Decomposition(O, p_Z);
        for i in lp do
          if Norm(i[1]) mod p eq 1 and
            (Norm(i[1]) lt 1000 or Degree(i[1]) eq 1) then
            process(~Pr, x, i[1]);
            if done() then
              flag := false;
              break;
            end if;
          end if;  
        end for;
      end while;
    end if;

    m1 := Matrix(Fp, g("Mat"));
    m2 := Matrix(Fp, [g("Right")]);
    f, c := IsConsistent(Transpose(m1), m2);
    error if not f,
      "Bad argument in pSelmerGroup map (given element "*
      "does not define an element of the p-Selmer group)";
    c := U!ChangeUniverse(Eltseq(c), Integers());
    return mKpS(c);

  end function; // to_KpS

  if Raw then
    mUofKpS:=[mU(a@@mKpS) : a in OrderedGenerators(KpS)];
    allP := [ x : x in S join SS];
    mbU := Matrix([ [ Valuation(x,p) : p in allP ] : x in Eltseq(bU)]);
    red := Matrix(mUofKpS)*mbU;
    l, t, r := LLL(p*red);
/*
assert not assigned delta;
delta := 0.75;
printf "Using large Delta:=%o\n", delta;
time l, t, r := LLL(p*red : Delta:=delta);  // Added Delta here!!
*/
    l := Submatrix(l, 1, 1, r, Ncols(l));
    red_mUofKpS := 
      [ &+ [ x[i]*p*mUofKpS[i] where x := Eltseq(t[j]):
                                i in [1..Ncols(t)]] : j in [1..r]];

    ext_bU := Eltseq(bU) cat [ UniformizingElement(x) : x in allP];

    function bla(v)
      w := Eltseq(v);
      v := &+[w[i]*mUofKpS[i]:i in [1..#mUofKpS]];
      w := VerticalJoin(l, v*mbU);
      w, t := GramSchmidtReduce(w, Nrows(w)-1);
      v +:= &+ [ x[i]*red_mUofKpS[i] : i in [1..#red_mUofKpS]] 
                              where x := Eltseq(t[Nrows(t)]);
      v := Eltseq(v);
      for i in [1..Ncols(w)] do
        if Integral and w[Nrows(w)][i] lt 0 then
          Append(~v, -p*w[Nrows(w)][i]);
        else
          Append(~v, 0);
        end if;
      end for;
      return Vector(v);
    end function;
    KpStobU:=map<KpS->RSpace(Integers(), #ext_bU)| v:->bla(v)>;

    primes := Setseq(bU_primes join Seqset(allP));

    return KpS, map<FieldOfFractions(O)-> KpS| x:->to_KpS(x), y:->from_KpS(y)>,
           KpStobU, Vector(ext_bU), primes;
  else;
    return KpS, map<FieldOfFractions(O)-> KpS| x:->to_KpS(x), y:->from_KpS(y)>;
  end if;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
//   Ramification                                                            //
///////////////////////////////////////////////////////////////////////////////

intrinsic IsRamified(P::RngOrdIdl) -> BoolElt
{Returns true iff P is ramified over the BaseRing}
  require IsPrime(P) : "The ideal must be a prime ideal";
  return RingExtIsRamifiedIdeal(P);
end intrinsic; 

intrinsic IsRamified(P::RngOrdIdl, O::RngOrd) -> BoolElt
{Returns true iff P is ramified in the extension O of its order}
  require IsPrime(P) : "The ideal must be a prime ideal";
  require IsMaximal(BaseRing(O)) and BaseRing(O) cmpeq Order(P) :
      "The BaseRing(O) must be the same as Order(P) and maximal";
    return RingExtIsRamified(P, O);
end intrinsic; 

intrinsic IsRamified(P::RngIntElt, O::RngOrd) -> BoolElt
{Returns true iff P is ramified in the absolute extension}
  require IsPrime(P) : "The number must be prime";
  require BaseRing(O) cmpeq Integers() :
      "The BaseRing(O) must be Z";
    return RingExtIsRamified(P, O);
end intrinsic; 

///////////////////////////////////////////////////////////////////////////////
//   Total Ramification                                                      //
///////////////////////////////////////////////////////////////////////////////

intrinsic IsTotallyRamified(P::RngOrdIdl) -> BoolElt
{Returns true iff P is totally ramified over the BaseRing}
  require IsPrime(P) : "The ideal must be a prime ideal";
  return RingExtIsTotallyRamifiedIdeal(P);
end intrinsic;

intrinsic IsTotallyRamified(P::RngOrdIdl, O::RngOrd) -> BoolElt
{Returns true iff P is totally ramified in the extension O of its order}
  require IsPrime(P) : "The ideal must be a prime ideal";
  require IsMaximal(BaseRing(O)) and BaseRing(O) cmpeq Order(P) :
      "The BaseRing(O) must be the same as Order(P) and maximal";
  return RingExtIsTotallyRamified(P, O);
end intrinsic;

intrinsic IsTotallyRamified(P::RngIntElt, O::RngOrd) -> BoolElt
{Returns true iff P is totally ramified in the absolute order O}
  require IsPrime(P) : "The number must be prime";
  require BaseRing(O) cmpeq Integers() :
      "The BaseRing(O) must be Z";
  return RingExtIsTotallyRamified(P, O);
end intrinsic;


intrinsic IsTotallyRamified(O::RngOrd) -> BoolElt
{Returns true iff O is totally ramified}
  require IsMaximal(O) : "Order must be maximal"; 
  return RingExtIsTotallyRamifiedOrder(O);
end intrinsic;

intrinsic IsTotallyRamified(K::FldAlg) -> BoolElt
{Returns true iff K is totally ramified}
  O := MaximalOrder(K);
  return IsTotallyRamified(O);
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
//   Wild Ramification                                                       //
///////////////////////////////////////////////////////////////////////////////

intrinsic IsWildlyRamified(P::RngOrdIdl) -> BoolElt
{Returns true iff P is wildly ramified over the BaseRing}
  require IsPrime(P) : "The ideal must be a prime ideal";
  return RingExtIsWildlyRamifiedIdeal(P);
end intrinsic;

intrinsic IsWildlyRamified(P::RngOrdIdl, O::RngOrd) -> BoolElt
{Returns true iff P is wildly ramified in the extension O of its order}
  require IsPrime(P) : "The ideal must be a prime ideal";
  require IsMaximal(BaseRing(O)) and BaseRing(O) cmpeq Order(P) :
      "The BaseRing(O) must be the same as Order(P) and maximal";
  return RingExtIsWildlyRamified(P, O);
end intrinsic;

intrinsic IsWildlyRamified(P::RngIntElt, O::RngOrd) -> BoolElt
{Returns true iff P is wildly ramified in the absolute order O}
  require IsPrime(P) : "The number must be prime";
  require BaseRing(O) cmpeq Integers() :
      "The BaseRing(O) must be Z";
  return RingExtIsWildlyRamified(P, O);
end intrinsic;


intrinsic IsWildlyRamified(O::RngOrd) -> BoolElt
{Returns true iff O is wildly ramified}
  require IsMaximal(O) : "Order must be maximal"; 
  return RingExtIsWildlyRamifiedOrder(O);
end intrinsic;

intrinsic IsWildlyRamified(K::FldAlg) -> BoolElt
{Returns true iff K is wildly ramified}
  O := MaximalOrder(K);
  return IsWildlyRamified(O);
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
//   Tame Ramification                                                       //
///////////////////////////////////////////////////////////////////////////////

intrinsic IsTamelyRamified(P::RngOrdIdl) -> BoolElt
{Returns true iff P is tamely ramified over the BaseRing}
  require IsPrime(P) : "The ideal must be a prime ideal";
  return RingExtIsTamelyRamifiedIdeal(P);
end intrinsic;

intrinsic IsTamelyRamified(P::RngOrdIdl, O::RngOrd) -> BoolElt
{Returns true iff P is tamely ramified in the extension O of its order}
  require IsPrime(P) : "The ideal must be a prime ideal";
  require IsMaximal(BaseRing(O)) and BaseRing(O) cmpeq Order(P) :
      "The BaseRing(O) must be the same as Order(P) and maximal";
  return RingExtIsTamelyRamified(P, O);
end intrinsic;

intrinsic IsTamelyRamified(P::RngIntElt, O::RngOrd) -> BoolElt
{Returns true iff P is tamely ramified in the absolute order O}
  require IsPrime(P) : "The number must be prime";
  require BaseRing(O) cmpeq Integers() :
      "The BaseRing(O) must be Z";
  return RingExtIsTamelyRamified(P, O);
end intrinsic;

intrinsic IsTamelyRamified(O::RngOrd) -> BoolElt
{Returns true iff O is tamely ramified}
  require IsMaximal(O) : "Order must be maximal"; 
  return RingExtIsTamelyRamifiedOrder(O);
end intrinsic;

intrinsic IsTamelyRamified(K::FldAlg) -> BoolElt
{Returns true iff K is tamely ramified}
  return not IsWildlyRamified(K);
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
//   Unramified                                                              //
///////////////////////////////////////////////////////////////////////////////

intrinsic IsUnramified(P::RngOrdIdl) -> BoolElt
{Returns true iff P is unramified over the BaseRing}
  require IsPrime(P) : "The ideal must be a prime ideal";
  return RingExtIsUnramifiedIdeal(P);
end intrinsic;

intrinsic IsUnramified(P::RngOrdIdl, O::RngOrd) -> BoolElt
{Returns true iff P is unramified in the extension O of its order}
  require IsPrime(P) : "The ideal must be a prime ideal";
  require IsMaximal(BaseRing(O)) and BaseRing(O) cmpeq Order(P) :
      "The BaseRing(O) must be the same as Order(P) and maximal";
  return RingExtIsUnramified(P, O);
end intrinsic;

intrinsic IsUnramified(P::RngIntElt, O::RngOrd) -> BoolElt
{Returns true iff P is unramified in the absolute order O}
  require IsPrime(P) : "The number must be prime";
  require BaseRing(O) cmpeq Integers() : "The BaseRing(O) must be Z";
  return RingExtIsUnramified(P, O);
end intrinsic;

intrinsic IsUnramified(O::RngOrd) -> BoolElt
{Returns true iff O is unramified at the finite places}
  require IsMaximal(O) : "Order must be maximal"; 
  return RingExtIsUnramifiedOrder(O);
end intrinsic;

intrinsic IsUnramified(K::FldAlg) -> BoolElt
{Returns true iff K is unramified}
  return IsUnramified(MaximalOrder(K));
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
//   Inert                                                                   //
///////////////////////////////////////////////////////////////////////////////

intrinsic IsInert(P::RngOrdIdl) -> BoolElt
{Returns true iff P is inert over the BaseRing}
  require IsPrime(P) : "The ideal must be a prime ideal";
  return RingExtIsInertIdeal(P);
end intrinsic;

intrinsic IsInert(P::RngOrdIdl, O::RngOrd) -> BoolElt
{Returns true iff P is inert in the extension O of its order}
  require IsPrime(P) : "The ideal must be a prime ideal";
  require IsMaximal(BaseRing(O)) and BaseRing(O) cmpeq Order(P) :
      "The BaseRing(O) must be the same as Order(P) and maximal";
    return RingExtIsInert(P, O);
end intrinsic;

intrinsic IsInert(P::RngIntElt, O::RngOrd) -> BoolElt
{Returns true iff P is inert in the absolute order O}
  require IsPrime(P) : "The number must be prime";
  require BaseRing(O) cmpeq Integers() :
      "The BaseRing(O) must be Z";
    return RingExtIsInert(P, O);
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
//   Split                                                                   //
///////////////////////////////////////////////////////////////////////////////

intrinsic IsSplit(P::RngOrdIdl) -> BoolElt
{Returns true iff P splits over the BaseRing}
  require IsPrime(P) : "The ideal must be a prime ideal";
  return RingExtIsSplitIdeal(P);
end intrinsic;

intrinsic IsSplit(P::RngOrdIdl, O::RngOrd) -> BoolElt
{Returns true iff P splits in the extension O of its order}
  require IsPrime(P) : "The ideal must be a prime ideal";
  require IsMaximal(BaseRing(O)) and BaseRing(O) cmpeq Order(P) :
      "The BaseRing(O) must be the same as Order(P) and maximal";
  return RingExtIsSplit(P, O);
end intrinsic;

intrinsic IsSplit(P::RngIntElt, O::RngOrd) -> BoolElt
{Returns true iff P splits in the absolute order O}
  require IsPrime(P) : "The number must be prime";
  require BaseRing(O) cmpeq Integers() : "The BaseRing(O) must be Z";
  return RingExtIsSplit(P, O);
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
//   Totally Split                                                           //
///////////////////////////////////////////////////////////////////////////////

intrinsic IsTotallySplit(P::RngOrdIdl) -> BoolElt
{Returns true iff P splits totally over the BaseRing}
    require IsPrime(P) : "The ideal must be a prime ideal";
    return RingExtIsTotallySplitIdeal(P);
end intrinsic;

intrinsic IsTotallySplit(P::RngOrdIdl, O::RngOrd) -> BoolElt
{Returns true iff P splits totally in the extension O of its order}
  require IsPrime(P) : "The ideal must be a prime ideal";
  require IsMaximal(BaseRing(O)) and BaseRing(O) cmpeq Order(P) :
      "The BaseRing(O) must be the same as Order(P) and maximal";
  return RingExtIsTotallySplit(P, O);
end intrinsic;

intrinsic IsTotallySplit(P::RngIntElt, O::RngOrd) -> BoolElt
{Returns true iff P splits totally in the absolute order O}
  require IsPrime(P) : "The number must be prime";
  require BaseRing(O) cmpeq Integers() : "The BaseRing(O) must be Z";
  return RingExtIsTotallySplit(P, O);
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
//   AbsoluteDiscriminant                                                    //
///////////////////////////////////////////////////////////////////////////////
intrinsic AbsoluteDiscriminant(O::RngOrd) -> RngIntElt
{Computes the absolute value of the discrimant of O over the integers}
  return Abs(RingExtAbsoluteDiscriminant(O));
end intrinsic;

intrinsic AbsoluteDiscriminant(K::FldAlg) -> RngIntElt
{Computes the absolute value of the discrimant of K over the rationals}
  d := Discriminant(K);
  t := AbsoluteDegree(K);
  while not BaseField(K) cmpeq Rationals() do 
    n := t div AbsoluteDegree(K) * Degree(K);
    K := BaseField(K);
    if BaseField(K) cmpeq Rationals() then
      g := [ ];
    else  
      if ISA(Type(d), RngOrdFracIdl) then
        g := Generators(d); 
      else
        g := [d];
      end if;
      // bad style, but field discriminants will be principal ideals
      // so Generators(D) will have length 1
      // this is neccessary because I can't compute norms of ideals
      // in relative extensions (even number fields) when the coeff.
      // ring is not maximal.
      // perhaps the Discriminant should change for FldNum?
    end if;  
    if #g eq 1 then
      d := Norm(g[1]) * Discriminant(K)^n;
    else
      d := Norm(d) * Discriminant(K)^n;
    end if;  
  end while;
  return Abs(d);
end intrinsic;

function pMaxOrder(O, p)
  f := DefiningPolynomial(O);
  o := CoefficientRing(O);
  v := Valuation(Discriminant(O), p);
  vprint MaximalOrder, 1: "Pauli - pMaximalOrder";
  if v eq 0 then 
    vprint MaximalOrder, 2: "Valuation of initial Disc is 0, done";
    return O; 
  end if;
  C, mC := ResidueClassField(p);
  g := Polynomial([mC(x) : x in Eltseq(f)]);
  //TODO: implement full Dedekind test - or at least bind it...
  if IsSquarefree(g) then
    vprint MaximalOrder, 2: "Defining polynomial is square-free over the residue class field, order maximal by Dedekind, done";
    return O;
  end if;

  C, mC := Completion(FieldOfFractions(o), p);
  // see if we can "improve" on the polynomial, ie. replace x by x/pi if this
  // is still integral:
  g := Eltseq(f);
  assert g[#g] eq 1;
  g := Minimum([Floor(Valuation(g[x], p)/(Degree(f) - x+1)) : x in [1..Degree(f)] | g[x] ne 0]);
  //so we can correct by x -> x/pi^-g

  vg := g;
  _, Pi := TwoElementNormal(p);
  f := Polynomial(FieldOfFractions(o), f);
  f := Evaluate(f, Parent(f).1*Pi^g)/Pi^(Degree(f)*g);
  assert IsMonic(f);
  vd := Valuation(Discriminant(f),p);
  if vd eq 0 then
    return O;
  end if;

  C`DefaultPrecision := 2*vd;
   // too large, we need only 1*Val(), but there might (will) be
   // some precision loss later, so we are careful here...

  g := Polynomial(func<|[mC(x) : x in Eltseq(f)]>());
  lg, _, c := Factorisation(g:Certificates);
  ba := [];
  assert Evaluate(DefiningPolynomial(O), O.2) eq 0;
  for i in [1..#lg] do
    cf := &* func<|[Parent(g)|x[1] : x in lg | x[1] ne lg[i][1]]>();

    t := cf mod lg[i][1];
    t := Eltseq(t);
    j := #t;
    while IsWeaklyZero(t[j]) or Valuation(t[j]) gt vd do j -:= 1; end while;
    t := t[1..j];
    t := Polynomial(t);
    gc, inv, _ := XGCD(t, lg[i][1]);
    //"gcd: ", gc, "should be one";

    cf *:= inv;
    l := LeadingCoefficient(cf);
    v := Valuation(l);
    cf /:= (l/UniformizingElement(C)^v);

    rho := c[i]`Rho;
    pi := c[i]`Pi;

    lb := [rho^k*pi^j mod g: k in [0..c[i]`F-1], j in [0..c[i]`E-1]];
    ba cat:= [x*cf mod g: x in lb]; 
  end for;  
  d := Minimum(func<|[Minimum([Valuation(x) : x in Eltseq(y)]) : y in ba]>());
  if d eq 0 then 
    vprint MaximalOrder, 2: "Transformation is unimodular, thus order is maximal, done";
    return O; 
  end if;
  z := [Integers(C)!0 : i in [1..Degree(O)]];
  
  pi := UniformizingElement(C);
  M := Matrix(Integers(C), func<|[Reverse((Eltseq(x*pi^-d) cat z)[1..Degree(O)]) : x in ba]>());
  E := EchelonForm(M);
  id := [];
  bs := [];
  for x in [1..Nrows(E)] do
    l := Eltseq(E[x]);
    v := Minimum([Valuation(x) : x in l]);
    l := Reverse(func<|[(x/pi^v)@@mC : x in l]>()); // by the looks of it, this is
                                           // the expensive line (@@mC)
    Append(~id, p^(d+v));
    Append(~bs, l);
  end for;
  _h := HermiteForm(PseudoMatrix(id, Matrix(bs)));
  _i := CoefficientIdeals(_h);
  i := [_i[x]*p^(-vg*(x-1)) : x in [1..Degree(f)]];
  h := Matrix(_h);
  Pivg := Pi^vg;
  for i:= 1 to Degree(f) do
    l := Polynomial(Eltseq(h[i]));
    l := Evaluate(l, Parent(l).1/Pivg)*Pivg^Degree(l);
    l := Eltseq(l);
    for j:= 1 to #l do
      h[i][j] := l[j];
    end for;
  end for;
  h := PseudoMatrix(i, Matrix(h));
  h := HermiteForm(h);
  return Order(O, h);
end function;

intrinsic InternalpMaximalOrder(O::RngOrd, p, exp::RngIntElt, flags::RngIntElt) -> RngOrd
  {}
  vprint MaximalOrder, 1: "pMaximalOrder, Pauli-method called with", p, exp;  
  if Type(p) eq RngIntElt then
    if IsEquationOrder(O) then
      vprint MaximalOrder, 2: "Order is absolute, calling Round4 instead";
      return pMaximalOrder(O, p:Al := "Round4");
    else
      vprint MaximalOrder, 2: "Order is absolute, but non equation order";
      return pMaximalOrder(O, p: Al := "Round2");
    end if;
  elif Type(CoefficientRing(CoefficientRing(O))) ne RngInt then
    vprint MaximalOrder, 2: "Order is multiply relative, calling Round2 instead";
    return pMaximalOrder(O, p:Al := "Round2");
  end if;  
  if not IsEquationOrder(O) then
    vprint MaximalOrder, 2: "Order is not an equation order, calling Round2 instead";
    return pMaximalOrder(O, p:Al := "Round2");
  end if;
  return pMaxOrder(O, p);
end intrinsic;


