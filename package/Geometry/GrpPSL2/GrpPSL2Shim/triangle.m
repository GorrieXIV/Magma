freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Arithmetic triangle groups
// May 2006, June 2007, John Voight
//
//////////////////////////////////////////////////////////////////////////////

declare attributes GrpPSL2: TriangleBool, TriangleSig, TriangleHRoots, TriangleDRoots,
                            Trianglephip0, Trianglephiq0, Trianglephir0, TriangleSeries,
                            TriangleABC;
import "domain.m" : HistoricShimuraReduceUnit;

//-------------
//
// Creation.
//
//-------------

intrinsic AdmissableTriangleGroups() -> SeqEnum
  {Returns the list of arithmetic triangle groups currently implemented.}

  return [[3,3,4], [3,3,6], [2,5,5], [3,5,5], [3,3,5], [2,3,7],
          [2,3,9], [3,3,8], [5,5,10], [3,3,12], [5,5,15], [3,3,15],
          [4,5,5], [2,3,11]];
end intrinsic;

intrinsic ArithmeticTriangleGroup(p::RngIntElt, q::RngIntElt, r::RngIntElt)
  -> GrpPSL2, Rng
  {Returns the arithmetic triangle group of signature (p,q,r).}

  if [p,q,r] in 
         {[2,4,6],[2,3,8],[2,3,12],[2,4,12],[2,4,5],[2,5,6],[2,3,10],[3,4,6],
          [2,4,18],[2,3,16],[2,5,20],[2,3,24],[2,5,30],[2,3,30],[2,5,8]} then
    error "Arithmetic triangle group not given by units of norm 1, not implemented yet!";
  end if;

  require [p,q,r] in {[3,3,4], [3,3,6], [2,5,5], [3,5,5], [3,3,5], [2,3,7],
                      [2,3,9], [3,3,8], [5,5,10], [3,3,12], [5,5,15], [3,3,15],
                      [4,5,5], [2,3,11]}:
    "The triple (p,q,r) is not arithmetic.";

/*
  if [p,q,r] eq [2,3,9] then
    // Hardcoded for testing purposes
    x := PolynomialRing(Rationals()).1;
    CC<I> := ComplexField(100);
    RR := RealField(CC);
    F := NumberField(x^3-3*x-1);
    Z_F := MaximalOrder(F);
    F := FieldOfFractions(Z_F);
    b := F.2;
    A<alpha,beta,alphabeta> := QuaternionAlgebra<F | -3, b>;
    zeta := 1/6*(2*b^2-b-4)*alpha-b/2;
    omega := -b+(b^2-1)/3*alpha-b*beta+(b^2-1)/3*alphabeta;
    eta := zeta*beta;
    O := Order([1,zeta,omega,eta]);
    G := FuchsianGroup(O);
    G`TriangleBool := true;
    G`TriangleSig := [2,3,9];

    s_p := 1/3*(b^2-1)*alpha + 1/3*(-b^2+b+3)*alphabeta;
    s_r := -zeta;
    s_q := s_p^(-1)*s_r^(-1);
    gammagens := [O | s_p, s_q, s_r];
    Gfree := FreeGroup(3);
    U := quo<Gfree | Gfree.1^2, Gfree.2^3, Gfree.3^9, Gfree.1*Gfree.2*Gfree.3>;
    m := map<U -> O | x :-> &*([A!1] cat [ gammagens[Abs(s)]^Sign(s) : s in Eltseq(x)])>;
    G`ShimGroup := U;
    G`ShimGroupMap := m;

    G`ShimFDDisc := [];

    sa := Sqrt(RR!3);
    brt := RR![z : z in Conjugates(b) | RR!z gt 0][1];
    FinRR := hom<F -> RR | brt>;
    sb := Sqrt(brt);
    Alpha := Matrix(2,2,[0,3,-1,0]);
    Beta := Matrix(2,2,[sb,0,0,-sb]);
    fAlphaBeta := [1, Alpha, Beta, Alpha*Beta];
    f := map<A -> MatrixRing(RR,2) | 
             x :-> &+[ FinRR(Eltseq(x)[i])*fAlphaBeta[i] : i in [1..4]]>;
    G`MatrixRepresentation := f;

    for s in [s_p, s_q, s_r, s_p*s_q*s_p] do
      Append(~G`ShimFDDisc, FixedPoints(G!s, UnitDisc(: Precision := 100))[1]);
    end for;

    return G, O;
  end if;
*/
  // Formula from Takeuchi
  sig := Sort([p,q,r]);
  sig2 := [2*s : s in sig];
  m := Lcm(sig2);
  K := CyclotomicField(m); z := K.1;
  t := [z^(m div s) + 1/z^(m div s) : s in sig2];
  F := sub<K | t[1]^2, t[2]^2, t[3]^2, t[1]*t[2]*t[3]>;
  a := F!(t[2]^2*(t[2]^2-4));
  b := F!(t[2]^2*t[3]^2*(t[1]^2+t[2]^2+t[3]^2+t[1]*t[2]*t[3]-4));
  A := QuaternionAlgebra<F | a,b>;
  O := MaximalOrder(A);

  // Initialize group
  G := FuchsianGroup(O);
  G`TriangleBool := true;
  G`TriangleSig := sig;
  
  if sig[1] eq sig[2] and sig[2] eq sig[3] then
    sig0 := [<sig[1], 3>];
  elif sig[1] eq sig[2] then
    sig0 := [<sig[1], 2>, <sig[3], 1>];
  elif sig[2] eq sig[3] then
    sig0 := [<sig[1], 1>, <sig[2], 2>];
  else
    sig0 := [<sig[1], 1>, <sig[2], 1>, <sig[3], 1>];
  end if;
  G`ShimEllipticInvariants := sig0;

  return G, O;
end intrinsic;

intrinsic IsTriangleGroup(G::GrpPSL2) -> BoolElt
  {Returns true iff G was initialized as an arithmetic triangle group.}

  return assigned G`TriangleBool;
end intrinsic;

//-------------
//
// j-Parameter.
//
//-------------

function ReduceToFD(G, D, z);
  zD := PlaneToDisc(D, UpperHalfPlane()!z);
  gammagens := [(G`ShimGroupMap)(G`ShimGroup.i) : i in [1..3]];
  deltared := HistoricShimuraReduceUnit(BaseRing(G)!1, gammagens, G, D : z0 := zD);
  zD := (G!deltared[1][1])*zD;
  deltared := [HistoricShimuraReduceUnit(BaseRing(G)!1, gammagens, G, D : 
                              z0 := zD, z1 := zr) : zr in G`TriangleDRoots];
  zD := [(G!d[1][1])*zD : d in deltared];
  zin := [ComplexValue(DiscToPlane(UpperHalfPlane(), zDd)) : zDd in zD];
  return zin;
end function;

intrinsic ReduceToTriangleVertices(G::GrpPSL2, z::SpcHypElt) -> SpcHypElt
  {Returns points in the G-orbit of z which are nearest to the vertices
   of the fundamental domain for G a triangle group.}

  D := UnitDisc( : Precision := Precision(ComplexValue(z)));

  H := Parent(z);
  if not assigned G`TriangleDRoots then
    U, m := Group(G);
    prootH := FixedPoints(m(U.1), H)[1];
    qrootH := FixedPoints(m(U.2), H)[1];
    rrootH := FixedPoints(m(U.3), H)[1];

    G`TriangleHRoots := [prootH, qrootH, rrootH];
    G`TriangleDRoots := [PlaneToDisc(D, z) : z in G`TriangleHRoots];
  end if;

  FDv := ReduceToFD(G, D, z);
  return ChangeUniverse(FDv, H);
end intrinsic;

intrinsic jParameter(G::GrpPSL2, z::SpcHypElt : Bound := 200, Precision := 100) -> 
     FldComElt, SeqEnum
  {Returns the value of the map j:X(G) -> P^1 at z for G an arithmetic triangle group.}

  require G`TriangleBool : "G must be an arithmetic triangle group";

  // D := Universe(G`ShimFDDisc);
  D := UnitDisc(: Precision := Precision);
  H := UpperHalfPlane();
  U, m := Group(G);

  if not assigned G`Trianglephip0 then
    CC<I> := ComplexField(Precision);

    p,q,r := Explode(G`TriangleSig);
    prootH := FixedPoints(m(U.1), H)[1];
    qrootH := FixedPoints(m(U.2), H)[1];
    rrootH := FixedPoints(m(U.3), H)[1];
    proot := CC!ComplexValue(prootH : Precision := Precision);
    qroot := CC!ComplexValue(qrootH : Precision := Precision);
    rroot := CC!ComplexValue(rrootH : Precision := Precision);

    // Solve the system to find A, B, C
    C := 1+1/p;
    B := 1/2*(1/p-1/q+1/r+1);
    A := 1/2*(1/p-1/q-1/r+1);

    A2 := A-C+1;
    B2 := B-C+1;
    C2 := 2-C;

    R<t> := PowerSeriesRing(CC,Bound);

    // Calculate psi,phi near t = 0
    Rp<tp> := PuiseuxSeriesRing(CC,Denominator(C)*Bound);

    HypergeometricSeriesAt1 := function(A,B,C);
      return Gamma(CC ! C)*Gamma(CC ! (C-A-B))/
             (Gamma(CC ! (C-A))*Gamma(CC ! (C-B)));
    end function;
  
    Fp1_1 := HypergeometricSeriesAt1(A,B,C);
    Fp2_1 := HypergeometricSeriesAt1(A2,B2,C2);
    c_psip := (qroot-proot)/(qroot-ComplexConjugate(proot))*Fp2_1/Fp1_1;
  
    Fp1 := (Rp ! HypergeometricSeries(A,B,C,t));
    Fp2 := tp^(1-C)*(Rp ! HypergeometricSeries(A2,B2,C2,t));
    psip := (Rp ! c_psip)*Fp1/Fp2;
  
    psipser := R ! (psip/tp^(1/p));
    psipser := psipser^p*t;
    phipser := Reversion(psipser);
  
    // Calculation around t = oo
    rden := Lcm([Denominator(A),Denominator(B),Denominator(A2),
                 Denominator(B2),Denominator(C)]);
    Rr<tr> := PuiseuxSeriesRing(CC,rden*Bound);
  
    HypergeometricSeriesAtoo := function(A,B,C);
      return Gamma(CC ! C)*Gamma(CC ! (B-A))/
             (Gamma(CC ! B)*Gamma(CC ! (C-A)));
    end function;
  
    Fr1 := 
    (Rr ! HypergeometricSeriesAtoo(A,B,C))*(-tr)^A*
    (Rr ! HypergeometricSeries(A,A-C+1,A-B+1,t)) +
    (Rr ! HypergeometricSeriesAtoo(B,A,C))*(-tr)^B*
    (Rr ! HypergeometricSeries(B,B-C+1,B-A+1,t));

    Fr2 := 
    (tr)^(C-1)*
    ((Rr ! HypergeometricSeriesAtoo(A2,B2,C2))*(-tr)^A2*
    (Rr ! HypergeometricSeries(A2,A2-C2+1,A2-B2+1,t)) +
    (Rr ! HypergeometricSeriesAtoo(B2,A2,C2))*(-tr)^B2*
    (Rr ! HypergeometricSeries(B2,B2-C2+1,B2-A2+1,t)));
  
    Fr1_0 := LeadingCoefficient(Fr1);
    Fr1 := Fr1/Fr1_0;
    Fr2_0 := LeadingCoefficient(Fr2);
    Fr2 := Fr2/Fr2_0;
  
    // Equations insist that the ratio of the series are
    // tr^(1/r) times a power series in r
    psir := Fr1-Fr2;

    function CleanSeries(f);
      eps := 10^(Floor(Log(Precision))-Precision);
      while Abs(LeadingCoefficient(f)) lt eps do
        f -:= LeadingTerm(f);
      end while;
      realflag := Abs(Re(LeadingCoefficient(f))) lt eps;
      imflag := Abs(Im(LeadingCoefficient(f))) lt eps;
      d := Degree(LeadingTerm(f));
      if Type(Degree(f)) eq RngIntElt then
        dnum := 0;
        dden := 1;
        bend := Degree(f);
      else
        dden := Denominator(Degree(f));
        dnum := Integers()!(d*dden);
        bend := Numerator(Degree(f));
      end if;
      for i := dnum to bend do
        if i mod dden ne dnum then
          f -:= Coefficient(f, i/dden)*tr^(i/dden);
        elif realflag then
          f -:= Re(Coefficient(f, i/dden))*tr^(i/dden);
        elif imflag then
          f -:= Im(Coefficient(f, i/dden))*I*tr^(i/dden);
        end if;
      end for;
      return f;
    end function;

    psir := CleanSeries(psir);

    rf := Coefficient(Fr1/LeadingTerm(Fr1),1/r)/
          Coefficient(Fr2/LeadingTerm(Fr2),1/r);
    psird := Fr1-rf*Fr2;

    psird := CleanSeries(psird);
    psir /:= psird;
  
    // Uses assumption that A and B have the same denominator
    if Denominator(A) ne Denominator(B) then
      error "A and B do not have the same denominator?!";
    end if;
    zta := Exp(Pi(CC)*I/Denominator(A));
  
    Fr1_1 := 
    HypergeometricSeriesAtoo(A,B,C)*zta^Numerator(A)*
    HypergeometricSeriesAt1(A,A-C+1,A-B+1) +
    HypergeometricSeriesAtoo(B,A,C)*zta^Numerator(B)*
    HypergeometricSeriesAt1(B,B-C+1,B-A+1);
    Fr1_1 /:= Fr1_0;
  
    Fr2_1 := 
    HypergeometricSeriesAtoo(A2,B2,C2)*zta^Numerator(A2)*
    HypergeometricSeriesAt1(A2,A2-C2+1,A2-B2+1) +
    HypergeometricSeriesAtoo(B2,A2,C2)*zta^Numerator(B2)*
    HypergeometricSeriesAt1(B2,B2-C2+1,B2-A2+1);
    Fr2_1 /:= Fr2_0;
  
    c_psir := (qroot-rroot)/(qroot-ComplexConjugate(rroot))*
    (Fr1_1-rf*Fr2_1)/(Fr1_1-Fr2_1);
  
    psir := (Rr ! c_psir)*psir;
    psir /:= tr^(1/r);
    psirseq,psirnum,psirden := Eltseq(psir);
    psirseqout := [];
    for i := 0 to Bound-1 do
      psirseqout[i+1] := psirseq[1+i*psirden];
    end for;
    psirser := R ! psirseqout;
  
    psirser := psirser^r*tr;
    psirserseq := Eltseq(psirser);
    psirser := (R ! psirserseq)*tr;
    psirser := CleanSeries(psirser);
    phirser := Reversion(psirser);
   
    // Calculation around t = 1
    qden := Lcm([Denominator(C-A-B),Denominator(C),Denominator(C2-A2-B2)]);
    Rq<tq> := PuiseuxSeriesRing(CC,qden*Bound);
  
    HypergeometricSeriesAt0 := function(A,B,C);
      return Gamma(CC ! C)*Gamma(CC ! (A+B-C))/
             (Gamma(CC ! A)*Gamma(CC ! B));
    end function;
  
    Fq1 :=
    (Rq ! HypergeometricSeriesAt1(A,B,C))*
    (Rq ! HypergeometricSeries(A,B,A+B-C+1,t)) +
    (tq)^(C-A-B)*
    (Rq ! HypergeometricSeriesAt0(A,B,C))*
    (Rq ! HypergeometricSeries(C-A,C-B,C-A-B+1,t));
    Fq2 :=
    (1-tq)^(1-C)*
    ((Rq ! HypergeometricSeriesAt1(A2,B2,C2))*
    (Rq ! HypergeometricSeries(A2,B2,A2+B2-C2+1,t)) +
    (tq)^(C2-A2-B2)*
    (Rq ! HypergeometricSeriesAt0(A2,B2,C2))*
    (Rq ! HypergeometricSeries(C2-A2,C2-B2,C2-A2-B2+1,t)));
  
    Fq1_0 := LeadingCoefficient(Fq1);
    Fq1 := Fq1/Fq1_0;
    Fq2_0 := LeadingCoefficient(Fq2);
    Fq2 := Fq2/Fq2_0;
  
    // Equations insist that the ratio of the series are
    // tq^(1/q) times a power series in tq
    psiq := Fq1-Fq2;
    psiq := CleanSeries(psiq);
  
    qf := Coefficient(Fq1/LeadingTerm(Fq1),1/q)/
          Coefficient(Fq2/LeadingTerm(Fq2),1/q);
  
    psiqd := Fq1-qf*Fq2;
    psiqd := CleanSeries(psiqd);
  
    psiq /:= psiqd;
  
    c_psiq := (proot-qroot)/(proot-ComplexConjugate(qroot))*qf;
  
    psiq := (Rq ! c_psiq)*psiq;
    psiq /:= tq^(1/q);
    psiqseq,psiqnum,psiqden := Eltseq(psiq);
    psiqseqout := [];
    for i := 0 to Bound-1 do
      psiqseqout[i+1] := psiqseq[1+i*psiqden];
    end for;
    psiqser := R ! psiqseqout;
    
    psiqser := psiqser^q*tq;
    phiqser := Reversion(psiqser);
  
    // Calculate psi,phi near t = 0, oo, 1
    Trianglephip0 := function(z0);
      w0 := (z0-proot)/(z0-ComplexConjugate(proot));
  
      return Evaluate(phipser,w0^p);
    end function;
 
    Trianglephir0 := function(z0);
      w0 := (z0-rroot)/(z0-ComplexConjugate(rroot));
  
      return Evaluate(phirser,w0^r);
    end function;
  
    Trianglephiq0 := function(z0);
      w0 := (z0-qroot)/(z0-ComplexConjugate(qroot));
   
      return Evaluate(phiqser,w0^q);
    end function;
  
    G`Trianglephip0 := Trianglephip0;
    G`Trianglephiq0 := Trianglephiq0;
    G`Trianglephir0 := Trianglephir0;
    G`TriangleSeries := [phipser, phirser, phiqser];
    G`TriangleABC := [[A,B,C], [A2, B2, C2]];

    G`TriangleHRoots := [prootH, qrootH, rrootH];
    G`TriangleDRoots := [PlaneToDisc(D, z) : z in G`TriangleHRoots];
  end if;

  zin := ReduceToFD(G, D, z);
 
  valatp := G`Trianglephip0(zin[1]);
  valatq := G`Trianglephiq0(zin[2]);
  valatr := G`Trianglephir0(zin[3]);
  val := [valatp, valatq, valatr];

  if Abs(valatp) lt Min([2,Abs(valatq),Abs(valatr)]) then
    return valatp, val;
  elif Abs(valatq) lt Min([1,Abs(valatr)]) then
    return 1-valatq, val;
  else
    if IsWeaklyZero(Abs(valatr)) then
      return Infinity(), val;
    else
      return 1/valatr, val;
    end if;
  end if;
end intrinsic;
