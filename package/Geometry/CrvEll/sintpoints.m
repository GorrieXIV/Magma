freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//           S-INTEGRAL POINTS ON ELLIPTIC CURVES                 //
//                                                                //
//        Steve Donnelly, last modified November 2009             //
//                                                                //
////////////////////////////////////////////////////////////////////

declare verbose IntegralPoints, 2;

// Intrinsics:                                                   
//   IsSIntegral (for point on elliptic curve)
//   IntegralPoints                                             
//   SIntegralPoints                                             

////////////////////////////////////////////////////////////////////
//                                                                //
//                    IsSIntegral                                 //
//                                                                //
////////////////////////////////////////////////////////////////////

// TO DO: call this directly
function _IsSIntegral(P, s)
   b := true;
   for i := 1 to 2 do
     if b then
       d := Denominator(P[i]);
       g := GCD(s, d);
       while g ne 1 do
         d := d div g;
         g := GCD(s, d);
       end while;
       b := d eq 1;
     end if;
   end for;
   return b;
end function;

intrinsic IsSIntegral(P::PtEll[FldRat], S::Setq) -> BoolElt
{True iff P is not the identity and has S-integral (affine) coordinates}

   if P[3] eq 0 then
     return false;
   end if;
   assert P[3] eq 1;

   s := IsEmpty(S) select 1 else LCM(S);

   return _IsSIntegral(P, s);
end intrinsic;

///////////////////////////////////////////////////////////////////////
//                                                                   //
//             Miscellaneous functions                               //
//                                                                   //
///////////////////////////////////////////////////////////////////////

function MWFreeBasis(E)
    vprintf IntegralPoints: "Determining the Mordell-Weil group of %o:\n", E;

    IndentPush();
    rank_bounds := MordellWeilShaInformation(E : ShaInfo := false,
                              Silent := not IsVerbose("IntegralPoints"));
    gens := E`MWGens;  // torsion-free
    IndentPop();

    rlow, rhigh := Explode(rank_bounds);

    if rlow ne rhigh or #gens lt rlow then 
      printf "WARNING"*
      "\nIntegralPoints could not determine the Mordell-Weil group."*
      "\nAfter applying all available tools,\n    %o <= rank <= %o."* 
      "\nThe known subgroup has rank %o, with generators: \n    %o."*
      "\nOnly integral points contained in this subgroup will be found.\n\n",
      rlow, rhigh, #gens, gens;
    end if;

    return gens;
end function;

// return 2 if some points are on the egg, otherwise 1; also
// return abs of smallest x value of component(s) containing points 

function egg_info(E, points)
  a1,a2,a3,a4,a6 := Explode(Coefficients(E));
  x := PolynomialRing(Rationals()).1;
  f := x^3 + (1/4*a1^2 + a2)*x^2 + (1/2*a1*a3 + a4)*x + 1/4*a3^2 + a6;
  rts := Roots(f, RealField(30)); 
  assert forall{tup: tup in rts | tup[2] eq 1};
  rts := Sort([tup[1] : tup in rts]);
  if #rts eq 1 then
    return 1, Abs(rts[1]);
  else
    assert #rts eq 3;
    if forall{P : P in points | P[1]/P[3] ge rts[3]} then
      return 1, Abs(rts[3]);
    else
      return 2, Max([Abs(r) : r in rts]);
    end if;
  end if;
end function;

///////////////////////////////////////////////////////////////////////
//                                                                   //
//                 Height Difference                                 //
//                                                                   //
///////////////////////////////////////////////////////////////////////

function height(x, R) 
  return Log(R! Max(Denominator(x), Abs(Numerator(x))));
end function;

function height_oo(x, R)
  return Log(R! Max(1, Abs(x)));  
end function;

function height_difference_bounds(E : R:=RealField(100))
   assert forall{c : c in Coefficients(E) | IsIntegral(c)};
   a1,a2,a3,a4,a6 := Explode(Coefficients(E));
   b2 := a1^2 + 4*a2;
   j := jInvariant(E);
   D := Discriminant(E);
   hj := height(j, R);
   hD := height(D, R);
   hj_oo := height_oo(j, R);
   mu := hD/6 + hj_oo/6;
   if b2 ne 0 then 
     mu +:= height_oo(b2/12, R) + Log(R!2);
   end if;
   naive_minus_canon := mu + hj/12 + R!1.922; 
   canon_minus_naive := mu + R!2.14;
   assert Abs(naive_minus_canon - SilvermanBound(E)) lt 10^-10;
   if IsMinimalModel(E) then
     naive_minus_canon := Min(naive_minus_canon, SiksekBound(E));
   end if;
   return naive_minus_canon, canon_minus_naive;
end function;

///////////////////////////////////////////////////////////////////////
//                                                                   //
//      Computing congruence subgroups: E(Q) meet E_k(Q_p)           //
//                                                                   //
///////////////////////////////////////////////////////////////////////

function singular_point(E, p)
  Polp<x,y> := PolynomialRing(GF(p), 2);
  Emodp := Evaluate(DefiningEquation(E), [x,y,1]);
  Emodp := Scheme(AffineSpace(Polp), Emodp);
  return Eltseq(SingularPoints(Emodp)[1]);
end function;

// The subgroup of G consisting elements satisfying the given test
// (this must contain e*G)

function naive_subgroup(G, Gmap, e, test)
  gens := [G.i @ Gmap : i in [1..Ngens(G)]];
  // first compute the orders of the gens in E/E0
  orders := [];
  for P in gens do 
    for d in Sort(Divisors(GCD(e, Order(P)))) do 
      if test(d*P) then
        Append(~orders, d);
        break d;
      end if;
    end for;
  end for;
  assert #orders eq #gens;
  // naively list possible coset reps for E/E0
  combs := CartesianProduct([[i : i in [0..d-1]] : d in orders]);
  combs := [c : c in combs | c ne <0 : d in orders>];
  reps := [];
  for c in combs do 
    P := &+[c[i]*gens[i] : i in [1..#c]];
    if test(P) then
      Append(~reps, &+[c[i]*G.i : i in [1..#c]]);
    end if;
  end for;
  return sub< G | reps cat [orders[i]*G.i : i in [1..Ngens(G)]] >;
end function;

// Intersection of the subgroup G of E(Q) with E_k(Q_p)

function congruence_subgroup(G, GtoE, p, k)
  E := Codomain(GtoE);
  a1,a2,a3,a4,a6 := Explode(Coefficients(E));
  type := ReductionType(E, p);
  if k eq 0 then
    if type eq "Good" then
      return G;
    else
      cp := TamagawaNumber(E, p);
      if cp eq 1 then
        return G;
      else
        // membership test: P is in E0 iff x(P) is congruent to x_sing
        x_sing := Integers()! singular_point(E, p)[1];
        E0_test := func< P | P[3] eq 0 or Valuation(P[1] - x_sing, p) le 0 >;
        return naive_subgroup(G, GtoE, cp, E0_test);
      end if;
    end if;
  elif k eq 1 then
    G0 := congruence_subgroup(G, GtoE, p, 0);
    Q := Rationals();
    Fp := GF(p);
    if type eq "Good" then 
      Emodp := ChangeRing(E, Fp);
      modp := map< E(Q) -> Emodp(Fp) | P :-> Eltseq(P) >;
      A, Amap := MyAbelianGroup(Emodp);
      gens_red := [G.i @GtoE @modp : i in [1..Ngens(G)]];
      gens_A := [g@@Amap : g in gens_red];
      return Kernel(hom< G -> A | [G.i @GtoE @modp @@Amap : i in [1..Ngens(G)]] >); 
    else
      S := singular_point(E, p);
      if type eq "Additive" then
        if p eq 2 then // the formula here fails, would need to get the tangent line,
          np := 2;     // ... but for small p we can just do naive_subgroup
        else
          A := AbelianGroup([p]);
          function toA(P)
            if P[3] eq 0 or Valuation(P[2], p) lt 0 then
              return A.0;
            else
              a := ((P[1] - S[1]) / (P[2] + a1/2*P[1] + a3/2));
              return A! Integers()! Fp! a;
            end if;
          end function;
          return Kernel(hom< G0 -> A | [toA(G0.i @GtoE) : i in [1..Ngens(G0)]] >);
        end if;
      else
        if type eq "Split multiplicative" then
          FF := Fp;
        elif type eq "Nonsplit multiplicative" then
          FF := GF(p^2);
        end if;
        A, Amap := MultiplicativeGroup(FF);
        // get tangent lines at the singular point over FF
        Polp<x,y> := PolynomialRing(GF(p), 2);
        eqn := Evaluate(DefiningEquation(E), [x+S[1],y+S[2],1]);
        coeffs, mons := CoefficientsAndMonomials(eqn);
        assert forall{m : m in mons | Degree(m) ge 2};
        eqn2 := &+ [coeffs[i]*mons[i] : i in [1..#mons] | Degree(mons[i]) eq 2];
        slopes := [FF| tup[1] : tup in Roots(Evaluate(eqn2, [1, PolynomialRing(FF).1]))];
        assert #slopes eq 2;
        function toGmFF(P)
          if P[3] eq 0 or Valuation(P[2], p) lt 0 then 
            return FF! 1;
          else
            xP := FF! P[1];
            yP := FF! P[2];
            assert [xP,yP] ne S;
            return ((yP-S[2]) - slopes[1]*(xP-S[1])) / ((yP-S[2]) - slopes[2]*(xP-S[1]));
          end if;
        end function;
        return Kernel(hom< G0 -> A | [toGmFF(G0.i @GtoE) @@Amap : i in [1..Ngens(G0)]] >);
      end if;
    end if;
    // fallback
    E1_test := func< P | P[3] eq 0 or Valuation(P[2],p) lt 0 and Valuation(P[1],p) - Valuation(P[2],p) ge 1 >;
    return naive_subgroup(G0, GtoE, np, E1_test);
  else
    // we will only use this in the case p = 2, k = 2
    Gk1 := congruence_subgroup(G, GtoE, p, k-1);
    Ek_test := func< P | P[3] eq 0 or Valuation(P[2],p) lt 0 and Valuation(P[1],p) - Valuation(P[2],p) ge k >;
    return naive_subgroup(Gk1, GtoE, p, Ek_test);
  end if;
end function;

/////////////////////////////////////////////////////////////////////////////
//                                                                         //
//  Upper bound for linear forms in elliptic logarithms Weierstrass form   //
//  Emanuel Hermann's code.                                                //
//                                                                         //
/////////////////////////////////////////////////////////////////////////////

function IntPointsUpperBound(E, MWG, lambda)

    if not IsWeierstrassModel(E) then
      W, toW := WeierstrassModel(E);
      return IntPointsUpperBound(W, [P@toW : P in MWG], lambda);
    end if;

    r:= #MWG;
    g := #TorsionSubgroup(E);
    omega1, omega2 := Explode(Periods(E : Precision := 50));
    omega1:=Real(omega1);
    tau:= omega2/omega1;
    if Im(tau) lt 0 then
       omega2prime:= -1*omega2;
       tau:= omega2prime/omega1;
    end if;

    ////////////////////   David's bound  //////////////////

    j:= jInvariant(E);
    j1:= Numerator(j);
    j2:= Denominator(j);
    A:= aInvariants(E)[4];
    B:= aInvariants(E)[5];
    C:= 2.9*10^(6*(r+2))*4^(2*(r+1)^2)*(r+2)^(2*r^2+13*r+23.3);

    h:= Log(Maximum([ 4*Abs(A*j2), 4*Abs(B*j2), Abs(j1) ]));
    PI:= Pi(RealField());
    LogV0:= Maximum([h, 3*PI/Im(tau) ]);
    LogVi:= [LogV0];

    for P in MWG do
        he := CanonicalHeight(P);
        val := Maximum([ he, h,
               3*PI*Norm(EllipticLogarithm(P : Precision := 50))^2
                  /((omega1)^2*Im(tau)) ]);
        Append(~LogVi,val);
    end for;

    k6:= Maximum([ (Log(2*2^(1/2)*(4)^(1/3)*g/omega1)/lambda), 1 ]);
    k7:= Maximum([ C/lambda, 10^9 ])*(h/2)^(r+2) * &*LogVi;

    BOUND:= 2^(r+3)*(k6*k7)^(1/2)*Log(k7*(r+3)^(r+3))^((r+3)/(2));
    prec:= Ceiling(Log(BOUND)/Log(10));
    R:= RealField(prec);
    BOUND_DAVID:= Ceiling(R!BOUND);

    /////////////////////  Hajdu-Herendi bound  /////////////////////

    a:= aInvariants(E)[4];
    b:= aInvariants(E)[5];
    D:= AbsoluteValue(4*a^3+27*b^2); assert D gt 0;

    k3:= 32/3 * D^(1/2)*(8+1/2*Log(D))^4;
    k4:= 10^4*Maximum([16*a^2, 256*D^(2/3) ]);
    k1:= 5*10^64*k3*Log(k3)*(k3+Log(k4));
    k2:= Maximum([Abs(2*a)^(1/2), Abs(4*b)^(1/3), Abs(a^2)^(1/4) ]);

    N0:= ((k1/2+k2)/lambda)^(1/2);
    q := (r+1) * (Floor(Log(N0)/Log(10))+1);
    if q le 13 then
        gamma:= Floor((14-q)/2);
    else
        gamma:= 1;
    end if;

    prec:= Ceiling(Log(N0)/Log(10));
    R:= RealField(prec);
    BOUND_HAJDUL_HERENDI:= Ceiling(R!N0);

    return Min(BOUND_DAVID, BOUND_HAJDUL_HERENDI);
end function;

function SIntegerBound(E, L, MWG, lambda)
    s := #L+1;
    if s eq 1 then
       return IntPointsUpperBound(E, MWG, lambda);
    end if;
    L:= Sort(L);
    Q:= L[s-1];
    Qstar:= Log(Maximum([Log(Q), 1]));

    if IsWeierstrassModel(E) then
        a:= aInvariants(E)[4];
        b:= aInvariants(E)[5];
        Delta0:= AbsoluteValue(4*a^3+27*b^2);

        k2:= Maximum([ AbsoluteValue(2*a)^(1/2),
                       AbsoluteValue(4*b)^(1/3),
                       AbsoluteValue(a^2)^(1/4) ]);
        k3:= 32/3*Sqrt(Delta0)*(8+1/2*Log(Delta0))^4;
        k4:= 10^4*Maximum([16*a^2, 256*Delta0^(3/2)]);
        a:= 0;
    else
        a1:= aInvariants(E)[1];
        a2:= aInvariants(E)[2];
        b2:= AbsoluteValue(bInvariants(E)[1]);
        b4:= AbsoluteValue(bInvariants(E)[2]);
        b6:= AbsoluteValue(bInvariants(E)[3]);
        b8:= AbsoluteValue(bInvariants(E)[4]);
        c4:= cInvariants(E)[1];
        c6:= cInvariants(E)[2];
        Delta1:= AbsoluteValue(-2^2*3^9*(c4^3-c6^2));

        k2:= Maximum([b2, b4^(1/2), b6^(1/3), b8^(1/4)]);
        k3:= 32/3*Sqrt(Delta1)*(8+1/2*Log(Delta1))^4;
        k4:= 20^4*Maximum([3^6*c4^2, 16*Delta1^(3/2)]);
        a:= Maximum([AbsoluteValue(a1), AbsoluteValue(a2)]);
    end if;

    k1:= 7*10^(38*s+49)*s^(20*s+15)*Q^24*Qstar^(4-2*s)*k3*Log(k3)^2*
            ((20*s-19)*k3+Log(Exp(1)*k4))+2*Log(2*a+6);
    N0:= k1/2+k2;
    N0:= Sqrt(N0/lambda);
    pr:= Log(N0)/Log(10);
    pr:= Round(pr)+50;
    R := RealField(pr);
    return Floor(R!N0) + 1;
end function;

//////////////////////////////   REDUCING THE BOUND   /////////////////////////////////

function best_delta(M, height_pairing, canon_height_bound)

    R := BaseRing(M);
    r := Nrows(M) - 1;

    Vol2 := Determinant(height_pairing);

    // Try C = 2^e, optimal should be around C = Height^(r+1)/Vol^2

    function get_delta(e)
      C := Round(2^e);
      G := DiagonalJoin(height_pairing, Matrix(R,1,1,[C]) );
      // TO DO(?) for very large rank, use an LLL estimate for the minimum
      L := LatticeWithBasis(M, G);
      min_norm := Minimum(L);
      // Since Height(P) <= canon_height_bound, we get 
      // C*|log(P)/Omega mod 1/t|^2 >= min_norm - canon_height_bound
      if min_norm le canon_height_bound then
        return -1; 
      end if;
      return Sqrt((min_norm - canon_height_bound)/C);
    end function;

    // Binary search to find the optimal bound, ie the largest delta
    // (empirically, it's monotonic on each side of the local extremum)
    // At each step, store deltas for three values E = [e1,e2,e3]

    ee := Floor( (r+1)*Log(2, canon_height_bound) - Log(2, Vol2) );
    ee := Max(1, ee-10);
    E  := [R| ee-1, ee, ee+1];
    D  := [R| get_delta(e) : e in E];
    counter := 0;
    repeat
      counter +:= 1;
      if D[2] le D[3] then            // shift right
        E := [E[2], E[3], E[3]+1];
        D := [D[2], D[3], get_delta(E[3])];
      elif D[1] gt D[2] then          // shift left
        E := [E[1]-1, E[1], E[2]];
        D := [get_delta(E[1]), D[1], D[2]];
      elif D[1] le D[3] then          // subdivide left side
        e := (E[1]+E[2])/2;
        d := get_delta(e);
        if d lt D[2] then
          E[1] := e;
          D[1] := d;
        else
          E := [E[1], e, E[2]];
          D := [D[1], d, D[2]];
        end if;
      else                            // subdivide right side
        e := (E[2]+E[3])/2;
        d := get_delta(e);
        if d le D[2] then
          E[3] := e;
          D[3] := d;
        else
          E := [E[2], e, E[3]];
          D := [D[2], d, D[3]];
        end if;
      end if;
      error if counter gt 10^4,
           "A bug has occurred!\nPlease send this example to magma-bugs@maths.usyd.edu.au";
    until E[3] - E[1] lt 10^-2 and Max(D) - Min(D) lt 10^-2;

    assert D[2] gt 0;
    return D[2];

end function;
 
function reduce_height_bound_one_step_at_p
         (E, MWL, height_pairing, tlogs, canon_height_bound, naive_height_bound, p 
         : Omega:=0)

  if p cmpeq Infinity() then 

    assert Omega gt 0;
    r:= Dimension(MWL);
    t, logs := Explode(tlogs); 

    // Lattice 
    // Z^(r+1) = {[P,n] : P in MWL, n in Z}
    // with
    // norm([P,n]) = Height(P) + C*|Log(P)/Omega + n/t|^2

    R := Universe(logs);
    M := IdentityMatrix(R, r+1);
    for i in [1..r] do
      M[i][r+1]:= logs[i]/t;  // = Log(P_i)/Omega
    end for;
    M[r+1][r+1]:= 1/t;

    delta := best_delta(M, height_pairing, canon_height_bound);
    delta *:= Omega;

    // Convert lower bound on delta = EllLog(P) to upper bound on Log(x(P))
    if delta lt 10^-20 then 
       // EllipticExponential throws silly bug when too close to 0 
       xbound := 1000 + Round(1/delta^2); 
    else
       deltaC := ComplexField(Precision(Parent(delta)))! delta;
       xbound := Real(EllipticExponential(E, deltaC)[1]); 
    end if;
    newbound := Log(Max(1, xbound)); 
    return newbound;

  else // p is a finite prime
 
    // Determine the largest k such that there exists P in MWL satisfying both
    //  (1) h_canon(P) <= canon_height_bound
    //  (2) the local contribution at p in h_naive(P) equals k*log(p), 
    //      in other words, P belongs to E_k(Q_p)

    k0, Gk0, toMWL, logs := Explode(tlogs); 
    ks := [k0-1, Floor(naive_height_bound/Log(p))]; // possible values of the largest such k
    
    // binary search (but take care of the huge initial bound)
    while ks[1] ne ks[2] do 
      if ks[2] gt ks[1] + 50 then
        k := ks[1] + 50;
      else
        k := Ceiling(&+ks/2); 
      end if;

      // Let MWL_k be the intersection of the Mordell-Weil lattice MWL 
      // with E_k(Q_p) = {P in E(Q_p) | val_p(log_p(P)) >= k}
      Zpk := AbelianGroup([p^k]);
      Gk := Kernel(hom< Gk0 -> Zpk | ChangeUniverse(logs, Integers()) >);
      MWL_k := sub< MWL | [g@toMWL : g in Generators(Gk)] >; 

      if Minimum(MWL_k) gt canon_height_bound then
        ks[2] := k-1;
      else
        ks[1] := k;
      end if;
      assert ks[1] le ks[2];
    end while;
    return 2*ks[1]*Log(p); // p appears at worst 2*k times in the denominator of the x-coordinate

  end if;
end function;

function reduced_canonical_height_bound(E, gens, N0, S)
  r := #gens;
  assert Infinity() notin S;
  S := [* p : p in S *] cat [* Infinity() *]; // use a list to avoid p becoming an ExtReElt
  vprint IntegralPoints: "S =", S;

  // This prec is needed for the first reduction step at the real place
  // TO DO: it can be reduced for the other steps
  prec := 2*(r+1)*Ilog(10, N0) + 100;
  R := RealField(prec);
  RR := RealField(6);

  naive_minus_canon, canon_minus_naive := height_difference_bounds(E : R:=R); 
  height_pairing := HeightPairingMatrix(gens : Precision:=prec);
  eigenvalues := [tup[1] : tup in Eigenvalues(height_pairing)];
  lambda := Min(eigenvalues); 
  assert #eigenvalues eq Nrows(height_pairing) and lambda gt 0;
  MWL := LatticeWithGram(height_pairing);
//RR! Regulator(gens) , RR! Determinant(MWL) , RR! &* eigenvalues , ChangeUniverse(eigenvalues, RR);
//assert Abs(Determinant(MWL) - &* eigenvalues) lt 10 ^ (100 - prec);

  // convert huge bound N0 on coeffs to bound on heights (hardly matters what we get!)
  canon_height_bound := N0^2 * Max(eigenvalues); 
  naive_height_bound := canon_height_bound + naive_minus_canon;

  vprintf IntegralPoints: "The height pairing (with respect to the chosen Mordell-Weil basis) is:\n"; 
  IndentPush();
  vprintf IntegralPoints: "%o\n", ChangeRing(height_pairing, RR);
  IndentPop();
  if r gt 1 then
    vprintf IntegralPoints: "with eigenvalues %o\n", ChangeUniverse(Sort(eigenvalues), RR);
  end if;
  vprintf IntegralPoints: "Bounds on the height difference for E:\n    %o <= h_naive - h_canon <= %o\n",
                           RR! -canon_minus_naive, RR! naive_minus_canon;
  
  // Let G = <gens> + torsion inside E(Q) 
  T, TtoE := TorsionSubgroup(E);
  Tgens := [T.i @ TtoE : i in [1..Ngens(T)]];
  Ggens := gens cat Tgens;
  G := AbelianGroup([0 : P in gens] cat [Order(T.i) : i in [1..Ngens(T)]]);
  GtoE := map< G -> E | g :-> &+[E| gg[i]*Ggens[i] : i in [1..#Ggens]] where gg is Eltseq(g) >;
  // map expressing elements of G in terms of gens, modulo torsion
  toMWL := func< g | Eltseq(G!g)[1..r] >;

  // compute logs of the MW generators at each p in S
  DEBUG := false;
  tlogs := [* *];
  for p in S do 
    if p cmpeq Infinity() then
      t, left_xbound := egg_info(E, gens);
      t := LCM(t, Exponent(T));
      Omega := RealPeriod(E : Precision:=prec); assert Omega gt 0;
      logs := [Real(EllipticLogarithm(t*P : Precision:=prec)) / Omega : P in gens];
      Append(~tlogs, <t, logs>);
    else
      // Let D = domain of log = G intersect E_k(Q_p) = {P in G | val_p(log_p(P)) >= k} 
      k := (p eq 2) select 2 else 1;
      D := congruence_subgroup(G, GtoE, p, k); 
      assert #TorsionSubgroup(D) eq 1;
      // Compute generators of D over Qp, not Q (to avoid blow-up when p is large),
      // taking care to get logs to the required precision 
      pprec := 100 + Floor(Log(p, naive_height_bound));
      logs := [pAdicRing(p, pprec) |
               pAdicEllipticLogarithmOfCombination(Ggens, Eltseq(G!D.i), p : Precision:=pprec) 
               : i in [1..Ngens(D)] ];
      if DEBUG then // check homomorphism property by computing logs of 2*P
        for i := 1 to Ngens(D) do 
          l2 := pAdicEllipticLogarithmOfCombination(Ggens, Eltseq(2*G!D.i), p : Precision:=pprec);
          v := Valuation(2*logs[i] - l2); assert v ge pprec;
        end for;
      end if;
      Append(~tlogs, <k, D, toMWL, logs>);
    end if;
  end for;

  // iterate until we can't reduce the bound any more
  local_bounds := [naive_height_bound : p in S]; // initial values, any correct bound will do 
  while true do 
    if r eq 1 then
      // refine canon_height_bound to be the height of the largest point that satisfies it
      // TO DO: also when r > 1, by enumerating the points ... but only worthwhile in certain cases
      m := Floor(Sqrt(canon_height_bound/height_pairing[1,1]));
      canon_height_bound := m^2 * height_pairing[1,1];
    end if;
    vprint IntegralPoints: "Current bound on canonical height =", RR! canon_height_bound;
    if canon_height_bound lt lambda then
      return 0, []; // the only S-integral points are torsion points
    end if;
    for s := 1 to #S do 
      p := S[s];
      b := reduce_height_bound_one_step_at_p
           (E, MWL, height_pairing, tlogs[s], canon_height_bound, local_bounds[s], p : Omega:=Omega);
      if p cmpeq Infinity() then
        b := Max([b, Log(Max(1, left_xbound))]);
      end if;
      local_bounds[s] := b;
    end for;
    vprint IntegralPoints: "==> bounds on contributions to naive height:", ChangeUniverse(local_bounds, RR);
    naive_height_bound := &+ local_bounds;
    if canon_height_bound gt naive_height_bound + canon_minus_naive + 10^-4 then
       canon_height_bound := naive_height_bound + canon_minus_naive;
    else
       return canon_height_bound, [* <S[i], local_bounds[i]> : i in [1..#S] *];
    end if;
  end while;
end function;

/////////////////// ////////   FINDING THE POINTS   /////////////////////////////////

// Search through points with canonical height <= heightbound

function CheckPointsWithBoundedHeight(E, basis, Tors, height_pairing, heightbound, S : extra:=0, naive:=[])

  pts := [E(BaseRing(E)) | ];

  assert extra ge 0;
  bound := heightbound + extra;
  if bound le 0 then
    return pts;
  end if;

  // Make bound slightly larger to allow for numerical errors
  // (Otherwise will miss points in cases where the heightbound is attained;
  // this sometimes happens eg "1264i1", "1328b1", "1656f1", "1848i1")
  bound *:= 1.001;
    
  RR := RealField(6);
  vprintf IntegralPoints: "Integral points have height at most %o\n", RR! heightbound;
  vprintf IntegralPoints: "Checking points with height up to %o\n",   RR! bound;
  vprintf IntegralPoints: "(Approximately %o points)\n", 
                           Round(V*Sqrt(bound^n/Determinant(height_pairing))/2)
                           where V is Pi(RR)^(n/2)/Gamma(n/2 + 1) where n is #basis;

  MWL := LatticeWithGram(height_pairing);
  r := #basis;
  assert r eq Nrows(height_pairing);

  time0 := Cputime();
  n := 0;

  SVP := ShortVectorsProcess(MWL, bound);
  while not IsEmpty(SVP) do
    n +:= 1;
    v, hv := NextVector(SVP);
    pt0 := &+ [Round(v[i])*basis[i] : i in [1..r]];
    for i := 1 to #Tors do 
      pt := Tors[i] + pt0;
      if IsSIntegral(pt, S) then 
        Append(~pts, pt); 
        if #pts eq 1 then 
          vprintf IntegralPoints: "\nFound S-integral points of height: ";
        end if;
        vprintf IntegralPoints: "%o ", Ceiling(hv);
        // when varargs are given, check pt satisfies all our bounds
        bug := extra gt 0 and hv gt heightbound + 10^-10;
        for tup in naive do 
          p := tup[1];
          if p cmpeq Infinity() then
            hp := Log(Max(1, pt[1]));
          else
            hp := Max(0, -Valuation(pt[1],p)) * Log(p);
          end if;
          bug or:= hp gt tup[2] + 10^-10;
        end for;
        error if bug, "\n\n A serious bug has been detected!"*
          "\n Please send this elliptic curve to magma-bugs@maths.usyd.edu.au\n\n", E, basis, S;
      end if;
    end for;
  end while;

  vprintf IntegralPoints: "\nTime to check %o points: %o\n", n, Cputime(time0);
    
  return pts; 
end function;

///////////////////////////////////////////////////////////////////////
//                S-Integral Points Intrinsics                       //
///////////////////////////////////////////////////////////////////////

// Note
// second and (blank) third return value for backwards compatibility (!)

intrinsic IntegralPoints(E::CrvEll : FBasis:=[], SafetyFactor:=1) 	
	-> SeqEnum, SeqEnum, RngIntElt
{Given an elliptic curve over the rationals, returns a sequence containing
the integral points on E (up to sign: only one of P and -P is listed)}

   require Type(BaseRing(E)) eq FldRat :
          "Argument 1 must be an elliptic curve defined over the rationals.";
   require &and [IsIntegral(ai) : ai in aInvariants(E)] :
          "The given curve must have integral coefficients";
   require SafetyFactor ge 1 : 
          "The SafetyFactor must not be less than 1";

   return SIntegralPoints(E, [] : FBasis:=FBasis, SafetyFactor:=SafetyFactor);
end intrinsic;

intrinsic SIntegralPoints(E::CrvEll, S::Setq[RngIntElt] : FBasis:=[], SafetyFactor:=1) 
       -> SeqEnum, SeqEnum
{Given an elliptic curve over the rationals and a sequence S of primes, 
returns a sequence containing the S-integral points on E 
(up to sign: only one of P and -P is listed)}

    require Type(BaseRing(E)) eq FldRat :
           "Argument 1 must be an elliptic curve defined over the rationals.";
    require &and [IsIntegral(ai) : ai in aInvariants(E)] :
           "The given curve must have integral coefficients";
    require &and [IsPrime(p : Proof := false) : p in S] :
           "Argument 2 must be a sequence of prime integers.";
    require SafetyFactor ge 1 : 
           "The SafetyFactor must not be less than 1";

    if ISA(Type(S), SeqEnum) then
      S := Sort(Setseq(Seqset(S)));
    else
      S := Sort(Setseq(S));
    end if;

    if not IsMinimalModel(E) then
      // use the minimal model and simply throw in the extra primes 
      // TO DO: use bound on valuation of denominator at extra primes  
      Emin, EtoEmin := MinimalModel(E);
      Dmin := Integers()! Discriminant(Emin);
      D := Integers()! Discriminant(E);
      d := Integers()! (D/Dmin);
      extra := [p : p in PrimeDivisors(d)];
      basisEmin := [P @ EtoEmin : P in FBasis];
      ptsEmin := SIntegralPoints(Emin, S cat extra : FBasis:=basisEmin);
      ptsE := [];
      for i := 1 to #ptsEmin do 
        pt := ptsEmin[i] @@ EtoEmin;
        if IsSIntegral(pt, S) then
          Append(~ptsE, pt);
        end if;
      end for;
      return ptsE, [<P,1> : P in ptsE], _;
    end if;

    if IsEmpty(FBasis) then
      basis:= MWFreeBasis(E);
    else
      basis:= ReducedBasis([E!P : P in FBasis]);
      vprint IntegralPoints: "Using given generators, which span group of rank", #basis;
    end if; 
    r := #basis;

    // Torsion points
    tpts := [E(Rationals()) | ];
    T, TtoE := TorsionSubgroup(E);
    Tors := [t @TtoE : t in T];
    Tgens := [T.i @TtoE : i in [1..Ngens(T)]];
    ts := [t : t in T | t ne T!0 and Eltseq(t) le Eltseq(-t)]; // only one of t and -t
    for t in ts do 
      P := t@TtoE;
      if IsSIntegral(P, S) then
        Append(~tpts, P);
      end if;
    end for;

    if r eq 0 then
      pts := tpts;

    else
      height_pairing := HeightPairingMatrix(basis);
      lam := Min([tup[1] : tup in Eigenvalues(height_pairing)]);
      N0 := SIntegerBound(E, S, basis, lam);

      height_bound, naive_height_bounds := reduced_canonical_height_bound(E, basis, N0, S);

      // Search region with volume SafetyFactor times as large
      // (up to height_bound + extra)
      if SafetyFactor eq 1 then
        extra := 0;
      else
        if height_bound eq 0 then  // important to test this case
          height_bound := 10;      // (typical size)
        end if;
        SF := SafetyFactor^(2/#basis) - 1;
        extra := SF * height_bound;
      end if;

      pts := CheckPointsWithBoundedHeight(E, basis, Tors, height_pairing, height_bound, S 
                                         : extra:=extra, naive:=naive_height_bounds);
      pts := tpts cat pts;
    end if;

    xpts := [P[1] : P in pts];
    ParallelSort(~xpts, ~pts);

    return pts, [<P,1> : P in pts], _;

end intrinsic;

