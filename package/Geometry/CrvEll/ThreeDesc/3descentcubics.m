freeze;

/////////////////////////////////////////////////////
//                                                 //
//      3-DESCENT ON ELLIPTIC CURVES OVER Q        //
//               "planecubics.m"                   //
//                                                 //
//                T. A. Fisher                     //
//                                                 //
//           Version: 11th April 2006              //
//                                                 //
/////////////////////////////////////////////////////

// This file contains intrinsics :-  
//
//   ThreeDescentCubic(E,alpha)
//   ThreeDescent(E)
//   AddCubics(cubic1,cubic2)

/*******************

  CHANGE LOG 

   +  April 2010, T.A.Fisher : added switch to use TrivializeNew

   +  April 2010, T.A.Fisher : converted to use new TransG1 type

   +  November 2006, Steve:  
        Copied in TAF change to use better basis.
        Also copied in fix for an unspecified bug in Trivialize.            
   
                                                    *************/

declare attributes CrvEll: ThreeDescentAlgebras;
declare verbose ThreeDescent, 3;

Q := Rationals();
P := PolynomialRing(Q); X:=P.1;
MC := MonomialCoefficient;
MD := MonomialsOfDegree;
CD := CremonaDatabase();

function apply(trans, cubic)
  return (trans*GenusOneModel(cubic))`Equation;
end function;

// Given T in E(L), with L = Q(T), find a rational
// function f in Q(E) such that f(T) = L.1.
function ReversePolynomial(T)
  R<x,y> := PolynomialRing(Q,2);
  L := Ring(Parent(T));
  T := [T[1]/T[3],T[2]/T[3]];
  d := Degree(L);
  mat := Matrix(1,d,Eltseq(L!1));
  n := 1;
  bb := [R|1];
  while Rank(mat) lt d do
    n +:= 1;
    if n mod 2 eq 0 then 
      b := x^m where m is ExactQuotient(n,2);
    else
      b := x^m*y where m is ExactQuotient(n-3,2);
    end if;
    bb := bb cat [b];
    row := Eltseq(L!Evaluate(b,T));
    mat := VerticalJoin(mat,Matrix(1,d,row));
  end while;
  vec := Vector(d,Eltseq(L.1));
  soln := Solution(mat,vec);
  f := &+[soln[i]*bb[i] : i in [1..#bb]];
  assert Evaluate(f,T) eq L.1;
  return f;
end function;  

function SlopeToTorsionPoint(E,L,phi)
  a1,a2,a3,a4,a6 := Explode(aInvariants(E));
  b2,b3,b6,b8 := Explode(bInvariants(E));
  c4,c6 := Explode(cInvariants(E));
  x := (phi^2 - b2)/12;
  y := (phi^4 - c4)/(48*phi) - (a1*x + a3)/2;
  return E(L)![x,y];
end function;

function TorsionPointToSlope(T);
  E := Curve(T);
  a1,a2,a3,a4,a6 := Explode(aInvariants(E));
  b2,b3,b6,b8 := Explode(bInvariants(E));
  c4,c6 := Explode(cInvariants(E));
  x := T[1]/T[3];
  y := T[2]/T[3];
  return ((12*x + b2)^2 - c4)/(2*y + a1*x + a3)/24;
end function;

AdditionViaSlopes := func<phi1,phi2,c4|
  -(phi1*phi2*(phi1^2-phi1*phi2+phi2^2)+3*c4)/(2*phi1*phi2*(phi1+phi2))>;

//  We compute some maps between the constituent fields 
//  of R and  R \otimes R. The Weil pairing as an element 
//  of R \otimes R is also computed.

function EtaleAlgebraData(E)
  c4,c6 := Explode(cInvariants(E));
  Delta := Discriminant(E);
  R<x,y> := FunctionField(Q,2);
  torspts := E`ThreeTorsionPoints;
  L := <Ring(Parent(T)): T in torspts>;
  ff := [R | ReversePolynomial(T) : T in torspts];
  gen := func<i,T|Evaluate(ff[i],[T[1]/T[3],T[2]/T[3]])>;
  GaloisType := ThreeTorsionType(E);
  case GaloisType :

  when "Generic" :

    T := torspts[1];
    L := Ring(Parent(T));
    conjL := hom<L->L|gen(1,-T)>;
    PP := PolynomialRing(L); Y := PP.1;
    G := PP!DefiningPolynomial(L);
    M := ext<L|ExactQuotient(G,(Y-L.1)*(Y-conjL(L.1)))>;
    T11 := E(M)!T;
    T12 := E(M)![Evaluate(P!Eltseq(x),M.1) : x in [T[1],T[2]]];
    T10 := -T11 - T12;
    T01 := -T11 + T12;
    zeta3 := WeilPairing(T10,T01,3);
    Lplus,map1 := sub<L|T[1]>;
//    if Optimise eq "true" then 
//      Lnew,map := OptimizedRepresentation(Lplus);
//      map1 := map^(-1)*map1;
//    end if;
    Mplus,map2 := sub<M|T12[1]>;
    LtoMvia10 := hom<L->M|gen(1,T10)>;
    LtoMvia01 := hom<L->M|gen(1,T01)>;
    maps := [conjL,LtoMvia10,LtoMvia01,map1,map2];
    RR := car<Q,L,L,L,L,M>;
    wp := elt<RR|1,1,1,1,1,zeta3>;

  when "2Sylow" :

    flag,D := IsPower(Delta,3); 
    assert flag;
    T := torspts[1];
    L := Ring(Parent(T));
    M<rtm3> := ext<L|X^2+3>; 
    conjL := hom<L->L|gen(1,-T)>;
    phi11 := TorsionPointToSlope(T);
    phi12 := phi11*(phi11^4 - c4 + 48*D)/(rtm3*(phi11^4 - c4));
    phi10 := AdditionViaSlopes(-phi11,-phi12,c4);
    phi01 := AdditionViaSlopes(-phi11,phi12,c4);
    T11 := SlopeToTorsionPoint(E,L,phi11);
    T12 := SlopeToTorsionPoint(E,M,phi12);
    T10 := SlopeToTorsionPoint(E,M,phi10);
    T01 := SlopeToTorsionPoint(E,M,phi01);
    assert E(M)!T eq T11;
    assert T10 eq -T11 - T12;
    assert T01 eq -T11 + T12;
    zeta3 := WeilPairing(T10,T01,3);
    LtoMvia10 := hom<L->M|gen(1,T10)>;
    LtoMvia01 := hom<L->M|gen(1,T01)>;
    LtoMvia12 := hom<L->M|gen(1,T12)>;
    Lplus,map1 := sub<L|T[1]>;
//    if Optimise eq "true" then 
//      Lnew,map := OptimizedRepresentation(Lplus);
//      map1 := map^(-1)*map1;
//    end if;
    maps := [conjL,LtoMvia10,LtoMvia01,LtoMvia12,map1];
    RR := car<Q,L,L,L,L,M,M,M>;
    wp := elt<RR|1,1,1,1,1,zeta3,zeta3^2,zeta3>;

  when "Dihedral" :

    flag,D := IsPower(Delta,3);
    assert flag;
    T1,T2 := Explode(torspts);
    L1 := Ring(Parent(T1));
    L2 := Ring(Parent(T2));
    M1<rt1> := ext<L1|X^2+3>;
    z1 := (-1+rt1)/2;
    M2<rt2> := ext<L2|X^2+3>;  
    z2 := (-1+rt2)/2;
    conjL1 := hom<L1->L1|gen(1,-T1)>; 
    conjL2 := hom<L2->L2|gen(2,-T2)>; 
    phi11 := TorsionPointToSlope(T1);
    phi12 := phi11*(phi11^4 - c4 + 48*D)/(rt1*(phi11^4 - c4));
    phi10 := AdditionViaSlopes(-phi11,-phi12,c4);
    phi01 := AdditionViaSlopes(-phi11,phi12,c4);
    T11 := SlopeToTorsionPoint(E,M1,phi11);
    T12 := SlopeToTorsionPoint(E,M1,phi12);
    T10 := SlopeToTorsionPoint(E,M1,phi10);
    T01 := SlopeToTorsionPoint(E,M1,phi01);
    assert T10 eq -T11 - T12;
    assert T01 eq -T11 + T12;
    L2toM1via10 := hom<L2->M1|gen(2,T10)>;
    L2toM1via01 := hom<L2->M1|gen(2,T01)>;
    L1toM1via12 := hom<L1->M1|gen(1,T12)>;
    phi10 := M2!TorsionPointToSlope(T2);
    phi01 := phi10*(phi10^4 - c4 + 48*D)/(rt2*(phi10^4 - c4));
    phi11 := AdditionViaSlopes(phi10,phi01,c4);
    phi12 := AdditionViaSlopes(phi10,-phi01,c4);
    T11 := SlopeToTorsionPoint(E,M2,phi11);
    T12 := SlopeToTorsionPoint(E,M2,phi12);
    T01 := SlopeToTorsionPoint(E,M2,phi01);
    L1toM2via11 := hom<L1->M2|gen(1,T11)>;
    L1toM2via12 := hom<L1->M2|gen(1,T12)>;
    L2toM2via01 := hom<L2->M2|gen(2,T01)>;
    maps := [conjL1,conjL2,L2toM1via10,L2toM1via01,L1toM1via12,
      L1toM2via11,L1toM2via12,L2toM2via01];
    RR := car<Q,L1,L2,L1,L2,L1,L2,L1,L2,M1,M1,M1,M2,M2,M2>;
    wp := elt<RR|1,1,1,1,1,1,1,1,1,z1,z1^2,z1,z2,z2,z2^2>;

  when  "Z/3Z-nonsplit" :

    T1,T2,T := Explode(torspts);
    L := Ring(Parent(T));
    conjL := hom<L->L|gen(3,-T)>;
    S := E(L)!T1;
    assert 2*S eq E(L)!T2;
    z := WeilPairing(S,T,3);
    map11 := hom<L->L|gen(3,S+T)>; 
    map12 := hom<L->L|gen(3,S-T)>; 
    map21 := hom<L->L|gen(3,-S+T)>; 
    map22 := hom<L->L|gen(3,-S-T)>;
    LL,map1 := sub<L|a+b,a*b> where a is gen(3,T) where b is gen(3,-T);
    assert Degree(LL) eq 3;
    LL,map2 := sub<L|a+b,a*b> where a is gen(3,S+T) where b is gen(3,-S-T);
    assert Degree(LL) eq 3;
    LL,map3 := sub<L|a+b,a*b> where a is gen(3,S-T) where b is gen(3,-S+T);
    assert Degree(LL) eq 3;
    RR := car<Q,Q,Q,L,Q,Q,L,Q,Q,L,Q,Q,L,L,L,L,L,L,L,L,L>;
    maps := [conjL,map11,map12,map21,map22,map1,map2,map3];
    wp := elt<RR|1,1,1,1,1,1,1,1,1,1,1,1,1,z^2,z,z,z^2,z,z^2,z^2,z>;
   
  when "mu3-nonsplit" :

    T1,T2 := Explode(torspts);
    L1 := Ring(Parent(T1));
    L2 := Ring(Parent(T2));
    conjL1 := hom<L1->L1|gen(1,-T1)>;
    M1 := ext<L1|DefiningPolynomial(L2)>;
    map := hom<L2->M1|M1.1>; 
    S := E(M1)!T1;
    T := E(M1)![map(x): x in Eltseq(T2)];
    z1 := WeilPairing(S,T,3);
    map0 := hom<L2->M1|gen(2,T)>;
    sig1 := hom<M1->M1|gen(2,S+T)>; 
    sig2 := hom<M1->M1|gen(2,-S+T)>; 
    M2 := ext<L2|DefiningPolynomial(L1)>;
    map := hom<L1->M2|M2.1>;
    S := E(M2)![map(x): x in Eltseq(T1)];
    T := E(M2)!T2;
    z2 := WeilPairing(S,T,3);
    map10 := hom<L1->M2|gen(1,S)>; 
    map11 := hom<L2->M2|gen(2,S+T)>; 
    map21 := hom<L2->M2|gen(2,-S+T)>;
    conjM2 := hom<M2->M2|gen(1,-S)>;
    RR := car<Q,L1,L2,L2,L1,L2,L2,L1,L2,L2,L1,L2,L2,M1,M1,M2,M2,M2,M2,M2,M2>;
    maps := [conjL1,map0,sig1,sig2,map10,map11,map21,conjM2];
    wp := elt<RR|1,1,1,1,1,1,1,1,1,1,1,1,1,z1^2,z1,z2,z2^2,z2,z2^2,z2^2,z2>;

  when "Generic3Isogeny" :

    T1,T2 := Explode(torspts);
    L1 := Ring(Parent(T1));
    L2 := Ring(Parent(T2));
    conjL1 := hom<L1->L1|gen(1,-T1)>;
    conjL2 := hom<L2->L2|gen(2,-T2)>;
    M1 := ext<L1|DefiningPolynomial(L2)>;
    map := hom<L2->M1|M1.1>; 
    S := E(M1)!T1;
    T := E(M1)![map(x): x in Eltseq(T2)];
    z1 := WeilPairing(S,T,3);
    mapA := hom<L2->M1|gen(2,T)>; 
    mapB := hom<L2->M1|gen(2,S-T)>; 
    M1plus,map2 := sub<M1|a+b,a*b> 
      where a is gen(2,S+T)
      where b is gen(2,-S-T);
    M2 := ext<L2|DefiningPolynomial(L1)>;
    map := hom<L1->M2|M2.1>;
    S := E(M2)![map(x): x in Eltseq(T1)];
    T := E(M2)!T2;
    z2 := WeilPairing(S,T,3);
    map21 := hom<L2->M2|gen(2,-S+T)>; 
    map12 := hom<L2->M2|gen(2,S-T)>; 
    map22 := hom<L2->M2|gen(2,-S-T)>; 
    map10 := hom<L1->M2|gen(1,S)>; 
    RR := car<Q,L1,L2,L1,L2,L1,L2,L1,L2,M2,M2,M1,M2>;
    maps := [conjL1,conjL2,map21,map12,map22,mapA,mapB,map2,map10];
    wp := elt<RR|1,1,1,1,1,1,1,1,1,z2,z2^2,z1^2,z2>;

  when "Diagonal" :

    T1,T2,T3 := Explode(torspts);
    L1 := Ring(Parent(T1));
    L2 := Ring(Parent(T2));
    M := Ring(Parent(T3));
    conjL1 := hom<L1->L1|gen(1,-T1)>;
    conjL2 := hom<L2->L2|gen(2,-T2)>;
    M1 := ext<L1|DefiningPolynomial(L2)>;
    map := hom<L2->M1|M1.1>; 
    S := E(M1)!T1;
    T := E(M1)![map(x): x in Eltseq(T2)];
    z1 := WeilPairing(S,T,3);
    iota1 := hom<M->M1|gen(3,S+T)>;
    M2 := ext<L2|DefiningPolynomial(L1)>;
    map := hom<L1->M2|M2.1>; 
    S := E(M2)![map(x): x in Eltseq(T1)];
    T := E(M2)!T2;
    z2 := WeilPairing(S,T,3);
    iota2 := hom<M->M2|gen(3,S+T)>;
    myeltseq := func<x|&cat[Eltseq(y): y in Eltseq(x)]>;
    gg := iota2(M.1);
    mymat := Matrix(Q,4,4,[myeltseq(gg^i) : i in [0..3]]);
    mymat := mymat^(-1);
    hh := &+[mymat[2,i+1]*M.1^i : i in [0..3]];
    assert iota2(hh) eq L2.1;
    map2 := hom<L2->M|hh>;
    T := E(M)![map2(x): x in Eltseq(T2)];
    S := T3 - T;
    z := WeilPairing(S,T,3);
    assert iota1(z) eq z1;
    assert iota2(z) eq z2;
    jj := gen(1,S);
    assert iota1(jj) eq L1.1;
    map1 := hom<L1->M|jj>;
    map12 := hom<M->M|gen(3,S-T)>;
    map21 := hom<M->M|gen(3,-S+T)>;
    map22 := hom<M->M|gen(3,-S-T)>;
    K3 := CyclotomicField(3);
    mm := hom<K3->M|z>;
    RR := car<Q,L1,L2,M,L1,L2,M,L1,L2,M,L1,L2,M,M,M,
      M1,M1,M2,M2,M,M,M,M,M1,M2>;
    maps := [conjL1,conjL2,map1,map2,iota1,iota2,map12,map21,map22,mm];
    wp := elt<RR|1,1,1,1,1,1,1,1,1,1,1,1,1,z,z^2,z1^2,z1,z2,z2^2,z^2,z,
      z,z^2,z1^2,z2>;
     
  when "mu3+Z/3Z" :

    K := CyclotomicField(3);
    conj := hom<K->K|K.1^2>;
    T,TT,S,T1,T2 := Explode(torspts);
    assert Ring(Parent(T)) eq Q;
    assert Ring(Parent(TT)) eq Q;
    assert Ring(Parent(S)) eq K;
    assert Ring(Parent(T1)) eq K;
    assert Ring(Parent(T2)) eq K;
    assert TT eq -T;
    SS := E(K)![conj(x): x in Eltseq(S)];
    assert SS eq -S;
    assert T1 eq S + E(K)!T;
    assert T2 eq S - E(K)!T;
    z := WeilPairing(S,E(K)!T,3);
    RR := car<Q,Q,Q,K,K,K,Q,Q,K,K,K,Q,Q,K,K,K,Q,Q,K,K,K,K,K,K,
      K,K,K,K,K,K,K,K,K,K,K,K,K,K,K,K,K,K,K,K,K>;
    maps := [conj];
    wp := elt<RR|1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,z,z^2,z^2,
      z,z,z^2,z^2,z,z,z^2,z^2,z,z^2,z,z,z^2,z,z^2,z^2,z,z^2,z,z,z^2>;          
    gen := <Q.1,Q.1,K.1,K.1,K.1>;

  end case;
  return maps,wp;
end function;  // EtaleAlgebraData
 
function TensorMap(GaloisType,RR,r1,r2,maps)
  R := Parent(r1);
  case GaloisType:

  when "Generic" :

    assert NumberOfComponents(R) eq 2;
    assert NumberOfComponents(RR) eq 6;
    a1,b1 := Explode(r1);
    a2,b2 := Explode(r2);
    conjL,LtoMvia10,LtoMvia01 := Explode(maps);
    bb1 := conjL(b1);
    bb2 := conjL(b2);
    c := LtoMvia10(b1)*LtoMvia01(b2);
    ans := elt<RR|a1*a2,b1*a2,a1*b2,bb1*bb2,b1*bb2,c>;

  when "2Sylow" :

    assert NumberOfComponents(R) eq 2;
    assert NumberOfComponents(RR) eq 8;
    a1,b1 := Explode(r1);
    a2,b2 := Explode(r2);
    conjL,LtoMvia10,LtoMvia01,LtoMvia12,map1 := Explode(maps);
    bb1 := conjL(b1);
    bb2 := conjL(b2);
    u := LtoMvia10(b1)*LtoMvia01(b2);
    v := LtoMvia12(b1)*LtoMvia01(bb2);
    w := LtoMvia01(bb1)*LtoMvia12(b2);
    ans := elt<RR|a1*a2,b1*a2,a1*b2,bb1*bb2,b1*bb2,u,v,w>;

  when "Dihedral" :

    assert NumberOfComponents(R) eq 3;
    assert NumberOfComponents(RR) eq 15;
    a,b1,b2 := Explode(r1);
    c,d1,d2 := Explode(r2);
    conjL1,conjL2,L2toM1via10,L2toM1via01,L1toM1via12,
      L1toM2via11,L1toM2via12,L2toM2via01 := Explode(maps);
    bb1 := conjL1(b1);
    dd1 := conjL1(d1);
    bb2 := conjL2(b2);
    dd2 := conjL2(d2);
    u1 := L2toM1via10(b2)*L2toM1via01(d2);
    v1 := L1toM1via12(b1)*L2toM1via01(dd2);
    w1 := L2toM1via01(bb2)*L1toM1via12(d1);
    u2 := L1toM2via11(bb1)*L1toM2via12(dd1);
    v2 := L1toM2via12(b1)*L2toM2via01(d2);
    w2 := L2toM2via01(b2)*L1toM2via12(d1);
    ans := elt<RR|a*c,b1*c,b2*c,a*d1,a*d2,bb1*dd1,bb2*dd2,
                  b1*dd1,b2*dd2,u1,v1,w1,u2,v2,w2>;

  when "Generic3Isogeny" :

    assert NumberOfComponents(R) eq 3; 
    assert NumberOfComponents(RR) eq 13; 
    L1 := R[2];
    L2 := R[3];
    a,b1,b2 := Explode(r1);
    c,d1,d2 := Explode(r2);
    conjL1,conjL2,map21,map12,map22,mapA,mapB,map2,map10 := Explode(maps);
    bb1 := conjL1(b1);
    dd1 := conjL1(d1);
    bb2 := conjL2(b2);
    dd2 := conjL2(d2);
    p := map10(b1)*map21(d2);
    q := map21(b2)*map10(d1);
    r := mapA(b2)*mapB(d2);
    s := map12(b2)*map22(d2);
    ans := elt<RR|a*c,b1*c,b2*c,a*d1,a*d2,bb1*dd1,bb2*dd2,
                  b1*dd1,b2*dd2,p,q,r,s>;

  when "Z/3Z-nonsplit" :

    assert NumberOfComponents(R) eq 4; 
    assert NumberOfComponents(RR) eq 21; 
    L := R[4];
    a1,b1,c1,d1 := Explode(r1);
    a2,b2,c2,d2 := Explode(r2);
    conjL,map11,map12,map21,map22,map1,map2,map3 := Explode(maps);
    dd1 := conjL(d1);
    dd2 := conjL(d2);
    ans := elt<RR|a1*a2,b1*a2,c1*a2,d1*a2,a1*b2,a1*c2,a1*d2,c1*c2,
      b1*b2,dd1*dd2,b1*c2,c1*b2,d1*dd2,d1*map12(d2),d1*map22(d2),
      map12(d1)*map22(d2),map22(d1)*map12(d2),b1*map21(d2),c1*map11(d2),
      map21(d1)*b2,map11(d1)*c2>;

  when "mu3-nonsplit" :

    assert NumberOfComponents(R) eq 4; 
    assert NumberOfComponents(RR) eq 21; 
    a1,b1,c1,d1 := Explode(r1);
    a2,b2,c2,d2 := Explode(r2);
    conjL1,map0,sig1,sig2,map10,map11,map21,conjM2 := Explode(maps); 
    bb1 := conjL1(b1);
    bb2 := conjL1(b2);
    ans := elt<RR|a1*a2,b1*a2,c1*a2,d1*a2,a1*b2,a1*c2,a1*d2,bb1*bb2,
      d1*d2,c1*c2,b1*bb2,c1*d2,d1*c2,map0(c1)*sig2(map0(d2)),
      map0(d1)*sig1(map0(c2)),map21(d1)*map11(d2),map11(c1)*map21(c2),
      map10(b1)*map21(c2),map10(b1)*map11(d2),map21(c1)*map10(b2),
      map11(d1)*map10(b2)>;

  when "Diagonal" :

    assert NumberOfComponents(R) eq 4; 
    assert NumberOfComponents(RR) eq 25; 
    a1,b1,c1,d1 := Explode(r1);
    a2,b2,c2,d2 := Explode(r2);
    conjL1,conjL2,map1,map2,iota1,iota2,map12,map21,map22 := Explode(maps);
    bb1 := conjL1(b1);
    bb2 := conjL1(b2);
    cc1 := conjL2(c1);
    cc2 := conjL2(c2);
    dd1 := map22(d1);
    dd2 := map22(d2);
    ans := elt<RR|a1*a2,b1*a2,c1*a2,d1*a2,a1*b2,a1*c2,a1*d2,bb1*bb2,cc1*cc2,
      dd1*dd2,b1*bb2,c1*cc2,d1*dd2,map1(b1)*map2(c2),map2(c1)*map1(b2),
      iota1(map2(c1)*map12(d2)),iota1(map12(d1)*map2(c2)),
      iota2(map1(b1)*map21(d2)),iota2(map21(d1)*map1(b2)),
      map1(bb1)*map21(d2),map21(d1)*map1(bb2),
      map2(cc1)*map12(d2),map12(d1)*map2(cc2),
      iota1(map21(d1)*map22(d2)),iota2(map12(d1)*map22(d2))>;

  when "mu3+Z/3Z" :

    assert NumberOfComponents(R) eq 6; 
    assert NumberOfComponents(RR) eq 45;
    conj := maps[1];
    a1,b1,c1,d1,e1,f1 := Explode(r1);
    a2,b2,c2,d2,e2,f2 := Explode(r2);
    dd1 := conj(d1);
    dd2 := conj(d2);
    ee1 := conj(e1);
    ee2 := conj(e2);
    ff1 := conj(f1);
    ff2 := conj(f2);
    ans := elt<RR|a1*a2,b1*a2,c1*a2,d1*a2,e1*a2,f1*a2,a1*b2,a1*c2,a1*d2,
      a1*e2,a1*f2,c1*c2,b1*b2,dd1*dd2,ff1*ff2,ee1*ee2,b1*c2,c1*b2,d1*dd2,
      e1*ff2,f1*ee2,d1*b2,b1*d2,d1*c2,c1*d2,f1*b2,b1*f2,e1*c2,c1*e2,e1*dd2,
      dd1*e2,f1*dd2,dd1*f2,dd1*ee2,ee1*dd2,dd1*ff2,ff1*dd2,c1*f2,f1*c2,
      b1*e2,e1*b2,ee1*ff2,ff1*ee2,f1*ff2,e1*ee2>;

  end case;
  return ans;
end function; // TensorMap

function Comultiplication(GaloisType,RR,r)

  case GaloisType :

  when "Generic" :
    a,b := Explode(r);
    ans := elt<RR|a,b,b,b,a,b>;

  when "2Sylow" :
    a,b := Explode(r);
    ans := elt<RR|a,b,b,b,a,b,b,b>;

  when "Dihedral" :
    a,b,c := Explode(r);
    ans := elt<RR|a,b,c,b,c,b,c,a,a,b,b,b,c,c,c>;

  when "Generic3Isogeny" :
    a,b,c := Explode(r);
    ans := elt<RR|a,b,c,b,c,b,c,a,a,c,c,b,c>;

  when "Z/3Z-nonsplit" :
    a,b,c,d := Explode(r);
    ans := elt<RR|a,b,c,d,b,c,d,b,c,d,a,a,a,b,c,d,d,d,d,d,d>;

  when "mu3-nonsplit" :
    a,b,c,d := Explode(r);
    ans := elt<RR|a,b,c,d,b,c,d,b,c,d,a,a,a,b,b,c,d,c,d,c,d>; 

  when "Diagonal" :
    a,b,c,d := Explode(r);
    ans := elt<RR|a,b,c,d,b,c,d,b,c,d,a,a,a,d,d,b,b,c,c,d,d,d,d,b,c>;

  when "mu3+Z/3Z" :
    a,b,c,d,e,f := Explode(r);
    ans := elt<RR|a,b,c,d,e,f,b,c,d,e,f,b,c,d,e,f,a,a,a,a,a,e,e,f,f,d,d,
      d,d,b,b,c,c,e,e,f,f,e,e,f,f,d,d,b,c>;

  end case;
  return ans;
end function; // Comultiplication

function TraceMap(GaloisType,R,rr)

  case GaloisType :

  when "Generic" :
    x1 := rr[1] + Trace(rr[5]);
    x2 := rr[2] + rr[3] + rr[4] + Trace(rr[6]);
    ans := elt<R|x1,x2>;

  when "2Sylow" :
    x1 := rr[1] + Trace(rr[5]);
    x2 := rr[2] + rr[3] + rr[4] + Trace(rr[6] + rr[7] + rr[8]);
    ans := elt<R|x1,x2>;

  when "Dihedral" : 
    x1 := rr[1] + Trace(rr[8]) + Trace(rr[9]);
    x2 := rr[2] + rr[4] + rr[6] + Trace(rr[10] + rr[11] + rr[12]);
    x3 := rr[3] + rr[5] + rr[7] + Trace(rr[13] + rr[14] + rr[15]);
    ans := elt<R|x1,x2,x3>;

  when "Generic3Isogeny" :
    x1 := rr[1] + Trace(rr[8]) + Trace(rr[9]);
    x2 := rr[2] + rr[4] + rr[6] + Trace(rr[12]);
    x3 := rr[3] + rr[5] + rr[7] + Trace(rr[10] + rr[11] + rr[13]);
    ans := elt<R|x1,x2,x3>;

  when "Z/3Z-nonsplit" :
    x1 := rr[1] + rr[11] + rr[12] + Trace(rr[13]);
    x2 := rr[2] + rr[5] + rr[8] + Trace(rr[14]);
    x3 := rr[3] + rr[6] + rr[9] + Trace(rr[15]);
    x4 := &+[rr[i] : i in [4,7,10,16,17,18,19,20,21]];
    ans := elt<R|x1,x2,x3,x4>;

  when "mu3-nonsplit" :
    x1 := rr[1] + Trace(rr[11]) + Trace(rr[12] + rr[13]);
    x2 := rr[2] + rr[5] + rr[8] + Trace(rr[14] + rr[15]);
    x3 := rr[3] + rr[6] + rr[9] + Trace(rr[16] + rr[18] + rr[20]);
    x4 := rr[4] + rr[7] + rr[10] + Trace(rr[17] + rr[19] + rr[21]);
    ans := elt<R|x1,x2,x3,x4>;

  when "Diagonal" :
    x1 := rr[1] + Trace(rr[11]) + Trace(rr[12]) + Trace(rr[13]);
    x2 := rr[2] + rr[5] + rr[8] + Trace(rr[16] + rr[17] + rr[24]);
    x3 := rr[3] + rr[6] + rr[9] + Trace(rr[18] + rr[19] + rr[25]);
    x4 := &+[rr[i] : i in [4,7,10,14,15,20,21,22,23]];
    ans := elt<R|x1,x2,x3,x4>;
  
  when "mu3+Z/3Z" :
    x1 := rr[1] + rr[17] + rr[18] + Trace(rr[19] + rr[20] + rr[21]);
    x2 := rr[2] + rr[7] + rr[12] + Trace(rr[30] + rr[31] + rr[44]);
    x3 := rr[3] + rr[8] + rr[13] + Trace(rr[32] + rr[33] + rr[45]);
    x4 := &+[rr[i] : i in [4,9,14,26,27,28,29,42,43]];
    x5 := &+[rr[i] : i in [5,10,15,22,23,34,35,38,39]];
    x6 := &+[rr[i] : i in [6,11,16,24,25,36,37,40,41]];
    ans := elt<R|x1,x2,x3,x4,x5,x6>;
   
  end case;
  return ans;
end function; // TraceMap

function Partial(GaloisType,RR,r,maps)
  Delta := Comultiplication(GaloisType,RR,r);
  rr := TensorMap(GaloisType,RR,r,r,maps);
  m := NumberOfComponents(RR);
  return RR!<rr[i]/Delta[i] : i in [1..m]>;
end function;

function PointwiseMultiply(r1,r2)
  R := Parent(r1);
  m := NumberOfComponents(R);
  return R!< r1[i]*r2[i] : i in [1..m]>;
end function;

function EtaleAlgebraBasis(R)
  m := NumberOfComponents(R);
  return [R!< i eq j select x else 0 : i in [1..m]>
    : x in IntegralBasis(R[j]), j in [1..m]];  
end function;

function DualBasis(L)
  d := Degree(L);
  B := IntegralBasis(L);
  trmat := Matrix(Q,d,d,[Trace(B[i]*B[j]):i,j in [1..d]]);
  mat := trmat^(-1);
  return [&+[mat[i,j]*B[j]: j in [1..d]]: i in [1..d]];
end function;

// A basis for R = L_1 x ... x L_m as a Q-vector space, 
// dual to that returned by EtaleAlgebraBasis.
function EtaleAlgebraDualBasis(R) 
  m := NumberOfComponents(R);
  return [R!< i eq j select x else 0 : i in [1..m]>
    : x in DualBasis(R[j]), j in [1..m]];   
end function;

// The underlying vector space of R = L_1 x ... x L_m.
function AlgebraToVectorSpace(R)
  m := NumberOfComponents(R);
  n := &+[Degree(R[i]) : i in [1..m]];
  V := VectorSpace(Q,n);
  R2 := <FieldOfFractions(RingOfIntegers(Component(R,i))): i in [1..m]>;
  mapRtoV := func<r|V!(&cat[Eltseq(R2[i]!r[i]): i in [1..m]])>;
  return V,mapRtoV;
end function;

function ThreeDescentAlgebras(E)
  if assigned E`ThreeDescentAlgebras then 
    return E`ThreeDescentAlgebras;
  end if;
  vprintf ThreeDescent, 1 : "Setting up the 3-descent algebras .... \n";
  GaloisType := ThreeTorsionType(E);
  torspts := ThreeTorsionPoints(E);
  E3reps := <E!0>;
  for T in torspts do 
    E3reps := Append(E3reps,T);
  end for;
  R := CartesianProduct(<Ring(Parent(T)): T in E3reps>);
  maps,wp := EtaleAlgebraData(E);  
  RR := Parent(wp);
  B := EtaleAlgebraBasis(R);
  BB := [TensorMap(GaloisType,RR,B[i],B[j],maps):i,j in [1..9] ];
  vprintf ThreeDescent, 1 : " .... done.\n";
  data := <B,BB,maps,wp>;
  E`ThreeDescentAlgebras := data;
  return data;
end function;    

// All cube roots are extracted using the following function.
function CubeRoot(x)
  L := Parent(x);
  d := AbsoluteDegree(L);
  pol := MinimalPolynomial(x);
  vprintf ThreeDescent, 1 :
    "Extracting a cube root in a degree %o number field ... ",d;
  vtime ThreeDescent, 1 :
  if Degree(pol) eq 1 then 
    flag,cbrt := IsPower(x,3); 
// do not use Root, since it returns real numbers when L = Q.
  else    
    K := NumberField(pol);
    flag, rt := HasRoot(PolynomialRing(K)![-K.1, 0, 0, 1]);
    cbrt := Evaluate(Parent(pol)!Eltseq(rt), x);
  end if;
  assert flag;
  assert x eq cbrt^3; // don't remove this --SRD
  return cbrt;
end function;

// Converts alpha in R^* to rho in (R tensor R)^*.

function AlphaToRho(E,alpha,Check)

  GaloisType := ThreeTorsionType(E);
  B,BB,maps := Explode(ThreeDescentAlgebras(E));
  R := Universe(B);
  RR := Universe(BB);
  assert alpha in R;
  assert alpha[1] eq 1;
  case GaloisType : 

  when "Generic" :

    assert NumberOfComponents(R) eq 2;
    assert NumberOfComponents(RR) eq 6;
    conjL,LtoMvia10,LtoMvia01,map1,map2 := Explode(maps);
    b := alpha[2];
    bb := conjL(b);
    s := map1(CubeRoot((b*bb) @@ map1));
    t := map2(CubeRoot((conjL(b)*LtoMvia10(b)*LtoMvia01(b)) @@ map2));
    rho := elt<RR|1,1,1,bb/s,s,t/s>;

  when "2Sylow" :

    assert NumberOfComponents(R) eq 2;
    assert NumberOfComponents(RR) eq 8;
    conjL,LtoMvia10,LtoMvia01,LtoMvia12,map1 := Explode(maps);
    b := alpha[2];
    bb := conjL(b);
    r := map1(CubeRoot((b*bb) @@ map1));
    s := CubeRoot(L!(LtoMvia10(b)*LtoMvia01(b))/b) where L is R[2];
    t := ss*LtoMvia10(ss)*r/b where ss is conjL(s);
    rho := elt<RR|1,1,1,bb/r,r,s,t,t>;

  when "Dihedral" :

    assert NumberOfComponents(R) eq 3; 
    assert NumberOfComponents(RR) eq 15; 
    conjL1,conjL2,L2toM1via10,L2toM1via01,L1toM1via12,
      L1toM2via11,L1toM2via12,L2toM2via01 := Explode(maps);
    _,b,c := Explode(alpha);
    bb := conjL1(b);
    cc := conjL2(c); 
    r := CubeRoot(b*bb); 
    s := CubeRoot(c*cc);
    elt := L2toM1via10(c)*L2toM1via01(c);
    t := CubeRoot((L1!elt)/b) where L1 is R[2];
    elt := L1toM2via11(bb)*L1toM2via12(bb);
    u := CubeRoot((L2!elt)/c) where L2 is R[3]; 
    tt := conjL1(t);
    uu := conjL2(u);
    xi := L2toM1via10(uu)*r*tt/b;
    eta := L1toM2via11(t)*s*uu/c;
    rho := elt<RR|1,1,1,1,1,bb/r,cc/s,r,s,t,xi,xi,u,eta,eta>;

  when "Generic3Isogeny" :

    assert NumberOfComponents(R) eq 3; 
    assert NumberOfComponents(RR) eq 13; 
    conjL1,conjL2,map21,map12,map22,mapA,mapB,map2,map10 := Explode(maps);
    _,b,c := Explode(alpha);
    bb := conjL1(b);
    cc := conjL2(c);
    r := CubeRoot(b*bb); 
    s := CubeRoot(c*cc); 
    t := CubeRoot(map12(c)*map22(c)/c); 
    u := map2(CubeRoot((mapA(c)*mapB(c)/b) @@ map2));
    mapM1toM2 := func<x|&+[map10(seq[i+1])*(L2.1)^i : i in [0..5]]
      where seq is Eltseq(x) where L2 is R[3]>;
    uu := mapM1toM2(u);
    v := map21(s)/uu;
    rho := elt<RR|1,1,1,1,1,bb/r,cc/s,r,s,v,v,u,t>;

  when "Z/3Z-nonsplit" :

    assert NumberOfComponents(R) eq 4; 
    assert NumberOfComponents(RR) eq 21; 
    _,b,c,d := Explode(alpha);
    conjL,map11,map12,map21,map22,map1,map2,map3 := Explode(maps);
    dd := conjL(d);
    r := CubeRoot(c^2/b);
    s := map1(CubeRoot((d*dd) @@ map1)); 
    t := map2(CubeRoot((d*map12(d)/b) @@ map2)); 
    u := map3(CubeRoot((d*map22(d)/c) @@ map3));
    p := map12(u)*map11(s)^2/(map11(d)*u);
    q1 := map12(s)/t;
    q2 := map11(s)/u;
    rho := elt<RR| 1,1,1,1,1, 1,1,r,r*b/c,dd/s, c/r,c/r,s,t,u, p,p,q1,q2,q1, q2>;

  when "mu3-nonsplit" :

    assert NumberOfComponents(R) eq 4; 
    assert NumberOfComponents(RR) eq 21; 
    _,b,c,d := Explode(alpha);
    conjL1,map0,sig1,sig2,map10,map11,map21,conjM2 := Explode(maps); 
    bb := conjL1(b);
    r := CubeRoot(Norm(b));
    s := CubeRoot(c*d);
    t := CubeRoot(sig1(c1)/c1/b) where c1 is map0(c); // free choice
    mapM1toM2 := func<x|&+[map10(seq[i+1])*(L2.1)^i : i in [0..2]]
      where seq is Eltseq(x) where L2 is R[3]>;
    tt := mapM1toM2(t);
    u := Q!(r*Norm(tt)*c);
    p := mapM1toM2(1/sig2(t));
    q := map11(s)/s/tt;
    rho := elt<RR|1,1,1,1,1,1,1,bb/r,d/s,c/s,r,s,s,sig2(t*map0(s)),
       t*map0(s),Norm(s)/s/u,u/s,p,q,p,q>;

  when "Diagonal" :

    assert NumberOfComponents(R) eq 4; 
    assert NumberOfComponents(RR) eq 25; 
    conjL1,conjL2,map1,map2,iota1,iota2,map12,map21,map22,mm := Explode(maps);
    _,b,c,d := Explode(alpha);
    bb := conjL1(b);
    cc := conjL2(c);
    dd := map22(d);
    t := CubeRoot((d*dd) @@ mm); // free choice
    u := CubeRoot(b*Norm(iota1(d)));
    v := CubeRoot(c*Norm(iota2(d)));
    r := Norm(u)/Norm(t);
    s := Norm(v)/Norm(t);
    t := mm(t);
    p := map1(u)*map2(v)/(d*map12(t));
    q1 := iota1(map2(v)/map1(u)*map12(d/t));
    q2 := iota2(map1(u)/map2(v)*map21(d/t));
    r1 := map1(conjL1(u))/t;
    r2 := map2(conjL2(v))/t;
    s1 := conjL1(u/r);
    s2 := conjL2(v/s);
    rho := elt<RR|1,1,1,1,1,1,1,bb/r,cc/s,dd/t,r,s,t,
	       p,p,q1,q1,q2,q2,r1,r1,r2,r2,s1,s2>;

  when "mu3+Z/3Z" :

    assert NumberOfComponents(R) eq 6; 
    assert NumberOfComponents(RR) eq 45; 
    conj := maps[1];
    _,b,c,d,e,f := Explode(alpha);
    dd := conj(d);
    r := CubeRoot(b*c);
    s := CubeRoot(Norm(d));
    p := CubeRoot(b*d/e); // free choice
    q := CubeRoot(c*d/f); // free choice
    pp := conj(p);
    qq := conj(q);
    rho := elt<RR|1,1,1,1,1,1,1,1,1,1,1,c/r,b/r,dd/s,
      c*dd*p/(qq^2*r*s),b*dd*q/(pp^2*r*s),r,r,s,r*s/(p*qq),r*s/(pp*q),
      p,p,q,q,r/q,r/q,r/p,r/p,s/p,s/p,s/q,s/q,dd*p/(s*pp),dd*p/(s*pp),
      dd*q/(s*qq),dd*q/(s*qq),c*p/(r*q),c*p/(r*q),b*q/(r*p),b*q/(r*p),
      r*dd/(pp*qq*s),r*dd/(pp*qq*s),c*s/(q*qq*r),b*s/(p*pp*r)>;

  end case;
  if Check then 
    vprintf ThreeDescent,1 : 
      " .... and checking partial(alpha) = rho^3 .... \n";
    da := Partial(GaloisType,RR,alpha,maps);
    m := NumberOfComponents(RR);
    assert forall{i : i in [1..m] | da[i] eq rho[i]^3};
  end if;
  return rho;
end function;  // AlphaToRho

function EnvelopingAlgebra(E,rho:Check:=true);
  type := ThreeTorsionType(E);
  B,BB,maps,wp := Explode(ThreeDescentAlgebras(E));
  R := Universe(B);
  RR := Universe(BB);   
  V,mapRtoV := AlgebraToVectorSpace(R);
  m := NumberOfComponents(RR);
  multtable := [ mapRtoV(TraceMap(type,R,rr)) 
    where rr is <bb[i] eq 0 select 0 else rho[i]*bb[i] : i in [1..m]> 
      : bb in BB];
  if Check then 
    vprintf ThreeDescent, 1 : " .... and checking associativity ....\n";
  end if;
  A := AssociativeAlgebra< V | multtable : Check := Check >;
  return A;
end function;

// A trivialisation of the algebra A is a sequence of matrices 
// such that A -> Mat_m(K) ; A.i |-> mats[i] is an isomorphism.

IsTrivialisation := func<A,mats| forall{ [i,j] : i,j in [1..n] | 
  mats[i]*mats[j] eq &+[Eltseq(A.i*A.j)[k]*mats[k]: k in [1..n]] }
  where n is Dimension(A) >;

// Returns M in GL_3(L) describing the action of 3-torsion on 
// the plane cubic f(x,y,z) = y^2 z - (x^3 - 27 c4 x z^2 - 54 c6 z^3).
// Scaling is chosen so that M^3 = I and iota M iota^(-1) = M^(-1) 
// where iota : (x, y, z) |-> (x, -y, z).

function TorsionMatrix(T)
  E := Curve(T);
  c4,c6 := Explode(cInvariants(E));
  phi := TorsionPointToSlope(T); 
  if phi ne 0 then 
    M := Matrix(Ring(Parent(T)),3,3,[
      [-18*c4,6*phi^3,-27*phi^2*(phi^4-3*c4)],
      [-27*phi*(phi^4-c4),-9*(phi^4-c4),-81*phi*(phi^6-5*c4*phi^2-4*c6)],
      [-6*phi^2,2*phi,9*(phi^4+c4)]]) / (18*(phi^4-c4));
  else
    assert c4 eq 0;
    a1,a2,a3,a4,a6 := Explode(aInvariants(E));
    b2,b3,b6,b8 := Explode(bInvariants(E));
    y := T[2]/T[3];
    a := -216*(y - a1*b2/24 + a3/2);
    assert a^2 eq -54*c6;
    M := Matrix(Ring(Parent(T)),3,3,[1,0,0,0,-1/2,3*a/2,0,-1/(2*a),-1/2]);
  end if;
  return M;
 end function;

function MyContent(f)
  assert BaseRing(Parent(f)) cmpeq Q;
  return f eq 0 select 0 else RationalGCD(Coefficients(f));
end function;

// Converts (an equation for) a genus one model defined over a number field to a 
// sequence of (equations for) genus one models defined over the rationals.

function RationalProjections(phi)
  flag, model := IsGenusOneModel(phi);
  n := model`Degree;
  L := BaseRing(PolynomialRing(model));
  coeffs := [Eltseq(x): x in ModelToSequence(model)];
  assert BaseField(L) cmpeq Q; // Base field should be the rationals.
  V := VectorSpace(Q,#coeffs);
  U := sub<V|[V![coeffs[i][j]: i in [1..#coeffs]]: j in [1..Degree(L)]]>;
  P<x,y,z> := PolynomialRing(Q,3);
  models := [P|GenusOneModel(n,Eltseq(u))`Equation : u in Basis(U)];
  return [f/MyContent(f) : f in models];
end function;

// Finds the pencil of plane cubics invariant under the 3-torsion matrix M.

function MatrixToPencil(mat)
  L := BaseRing(mat);
  P<x,y,z> := PolynomialRing(L,3);
  x1 := [x,y,z];
  x2 := [&+[mat[i,j]*x1[j]: j in [1..3]]: i in [1..3]];
  x3 := [&+[mat[i,j]*x2[j]: j in [1..3]]: i in [1..3]];
  Xi := Matrix(P,3,3,[x1,x2,x3]);
  cubic := Determinant(Xi);
  return RationalProjections(cubic);
end function;

// Finds all cubics in the given pencil with same j-invariant as E.

function FindInPencil(cubics,E) 
  error if #cubics ne 2, "Pencil should be spanned by two cubics.";
  P<s,t> := PolynomialRing(Q,2);
  R3<x,y,z> := PolynomialRing(P,3);
  pencil := [R3 | cubic : cubic in cubics];
  c4,c6,Delta := Invariants(GenusOneModel(s*pencil[1] + t*pencil[2]));
  poly := c4^3 - jInvariant(E)*Delta;  
//  fibre := Scheme(Proj(P),poly);
//  pts := Points(fibre);   
  R := PolynomialRing(Q); X:=R.1;
  rts := Roots(Evaluate(poly,[X,1]));
  pts  := [[rt[1],1] : rt in rts];
  if Evaluate(poly,[1,0]) eq 0 then 
    pts cat:= [[1,0]];
  end if;
  solns := [pt[1]*cubics[1] + pt[2]*cubics[2]: pt in pts];
  return [cubic/MyContent(cubic) : cubic in solns];
end function;

// Let e be an idempotent in an associative algebra A,
// with e A a field. A subfield F of e A is specified
// by giving the image x of F.1. We compute the the 
// minimal polynomial of a over F.

function MyMinimalPolynomial(F,e,x,a)
  assert e*x eq x;
  assert e*a eq a;
  A := Parent(e);
  n := Dimension(A);
  MyBasisF := [e*x^(i-1): i in [1..Degree(F)]];
  R := PolynomialRing(F); X:=R.1;
  for d in [0..n] do
    elts := [b*a^i : b in MyBasisF, i in [0..d-1]] cat [a^d];
    pols := [b*X^i : b in Basis(F), i in [0..d-1]] cat [X^d];
    mat := Matrix(#elts,n,[Eltseq(x): x in elts]);
    km := KernelMatrix(mat);
    if Nrows(km) eq 1 then break; end if;
  end for;
  poly := &+[pols[i]*km[1,i] : i in [1..#pols]];
  poly /:= LeadingCoefficient(poly);
  assert IsIrreducible(poly);
  return poly;
end function;

// Given e an idempotent in an associative algebra A, with e A a field, 
// we find a primitive element x in this field.

function FieldGenerator(A,e)
  F := Q;
  x := e;
  for a in Basis(A) do
    poly := MyMinimalPolynomial(F,e,x,e*a);
    vprintf ThreeDescent, 1 : " poly = %o\n",poly;
    if Degree(poly) gt 1 then
      d := Degree(F);
      MyBasisF := [e*x^(i-1): i in [1..d]];  
      mapFtoA := func<y|&+[yy[i]*MyBasisF[i]: i in [1..d]] 
        where yy is Eltseq(y)>;
      Frel := NumberField(poly);
      F := AbsoluteField(Frel);
      coeffs := [mapFtoA(y): y in Eltseq(Frel!(F.1))];
      x := &+[coeffs[i]*a^(i-1): i in [1..Degree(poly)]];
    end if;
    if Degree(F) eq Dimension(A) then break; end if;
  end for;
  return x;
end function;

// Given an associative algebra A over Q, known to be a 
// product of number fields, find one of these number fields F
// and the projection map A -> F.

function AlgebraToNumberField(A)
  e := CentralIdempotents(A)[1];
  x := FieldGenerator(A,e);
  f := MyMinimalPolynomial(Q,e,e,x);
  n := Dimension(A);
  F := NumberField(f);
  d := Degree(F);
  MyBasisF := [e*x^(i-1): i in [1..d]]; 
  Fmatrix := Matrix(Q,d,n,[Eltseq(b): b in MyBasisF]);
  mat := Matrix(Q,n,d,[Solution(Fmatrix,vec) 
    where vec is Vector(Q,n,Eltseq(e*a)) : a in Basis(A)]);
//  if F cmpeq Q then
//    print "Trivial element of the Selmer group!!";
//  end if;
  V,isom := VectorSpace(F,Q);
  map := hom<A->V|mat> * isom^(-1);
  return F,map;
end function;

// Given two sequences of n by n matrices [M_1, .. ,M_m] and [N_1, .. ,N_m], 
// finds a non-zero n by n matrix B (assumed unique up to scalars) with
// B M_i = N_i B for all 1 <= i <= m.

function ConjugationMatrix(K,mats1,mats2)
  assert #mats1 eq #mats2;
  m := #mats1;
  n := Nrows(mats1[1]);
  M := MatrixAlgebra(K,n);
  m1 := ChangeUniverse(mats1,M); 
  m2 := ChangeUniverse(mats2,M);
  mat := Matrix(K,n^2,m*n^2,
    [ &cat[Eltseq(Eij*m1[k]-m2[k]*Eij) : k in [1..m]] : Eij in Basis(M)]); 
  km := KernelMatrix(mat);
  assert Nrows(km) eq 1;
  soln := &+[km[1,i]*Basis(M)[i] : i in [1..n^2]];
  assert forall{i: i in [1..m] | soln*m1[i] eq m2[i]*soln};
  return soln;
end function;   

// Equations for C as a curve of degree 9 .....

function proj(L,quad,mons)
  n := Rank(Parent(quad));
  quad := PolynomialRing(L,n)!quad;
  coeffs := [Eltseq(MC(quad,Parent(quad)!mon)) : mon in mons];
  return [&+[coeffs[i][j]*mons[i]: i in [1..#mons]]: j in [1..Degree(L)]];
end function;

function absproj(L,quad,mons)
  AbsEltseq := func<x|&cat[Eltseq(y): y in Eltseq(x)]>;
  n := Rank(Parent(quad));
  quad := PolynomialRing(L,n)!quad;
  coeffs := [AbsEltseq(MC(quad,Parent(quad)!mon)) : mon in mons];
  m := AbsoluteDegree(L);
  return [&+[coeffs[i][j]*mons[i]: i in [1..#mons]]: j in [1..m]];
end function;

function ranges(xx)
  dd := [Degree(Parent(x)): x in xx];
  tt := [0] cat [&+[dd[i] : i in [1..j]]: j in [1..#dd]];
  rr := [[tt[i]+1..tt[i+1]] : i in [1..#dd]];
  assert &cat rr eq [1..8];
  return rr;
end function;  

function quads1(rho,xT,nos,conj,mons,subflag)
  rr := ranges(xT);
  ii := [rr[i]: i in nos];
  L := Parent(xT[nos[1]]);
  m := Degree(L);
  LX := PolynomialRing(L,8);
  zT := &+[LX| IntegralBasis(L)[i]*LX.ii[1][i] : i in [1..m]];
  zmT := &+[LX| conj(IntegralBasis(L)[i])*LX.ii[2][i] : i in [1..m]];
  assert xT[nos[1]] eq conj(xT[nos[2]]);
  eqn := xT[nos[1]] + rho*zT*zmT;
  if subflag then 
    Lplus,map := sub<L|xT[nos[1]]>;
    if not (Lplus cmpeq Q) then
      Embed(Lplus,L,map(Lplus.1));
    end if;
    eqn := PolynomialRing(Lplus,8)!eqn;
    quads := proj(Lplus,eqn,mons);
  else
    quads := proj(L,eqn,mons);
  end if;
  return quads;
end function;

function quads2(rho1,rho2,slopes,nos,conj,map1,map2)
  if #nos eq 3 then nos := nos cat [nos[3]]; end if;
  rr := ranges(slopes);
  ii := [rr[i]: i in nos];
  L := Domain(conj);
  L1 := Domain(map1);
  L2 := Domain(map2);
  m := Degree(L);
  m1 := Degree(L1);
  m2 := Degree(L2);
  M := Codomain(map1);
  MX := PolynomialRing(M,8);
  assert slopes[nos[3]] eq -conj(slopes[nos[4]]);
  zT1 := &+[MX| map1(IntegralBasis(L1)[i])*MX.ii[1][i] : i in [1..m1]];
  zT2 := &+[MX| map2(IntegralBasis(L2)[i])*MX.ii[2][i] : i in [1..m2]];
  zT := &+[MX| IntegralBasis(L)[i]*MX.ii[3][i] : i in [1..m]];
  zmT := &+[MX| conj(IntegralBasis(L)[i])*MX.ii[4][i] : i in [1..m]];
  c := map1(slopes[nos[1]]) + map2(slopes[nos[2]]) + 2*slopes[nos[3]];
  return c*zT - rho1*zmT^2 + rho2*zT1*zT2;
end function;

function Type1Quadrics(E,rho) 
  GaloisAction := ThreeTorsionType(E);
  torspts := ThreeTorsionPoints(E);
  _,_,maps := Explode(E`ThreeDescentAlgebras);
  b2 := bInvariants(E)[1];
  xT := <3*(12*T[1]/T[3] + b2) : T in torspts>;
  P := PolynomialRing(Q,8);
  mons := &join [MD(P,d) : d in [0..2]];
  case GaloisAction :

  when "Generic" :

    q1 := quads1(rho[5],xT,[1,1],maps[1],mons,true);
    quads := [q1[i] : i in [2..4]];  

  when "2Sylow" :

    q1 := quads1(rho[5],xT,[1,1],maps[1],mons,true);
    quads := [q1[i] : i in [2..4]];  

  when "Dihedral" :

    q1 := quads1(rho[8],xT,[1,1],maps[1],mons,true);
    q2 := quads1(rho[9],xT,[2,2],maps[2],mons,true);
    quads := [q1[1]-q2[1],q1[2],q2[2]];

  when "Generic3Isogeny" :

    q1 := quads1(rho[8],xT,[1,1],maps[1],mons,true);
    q2 := quads1(rho[9],xT,[2,2],maps[2],mons,true);
    quads := [q1[1]-q2[1],q2[2],q2[3]];

  when "Z/3Z-nonsplit" :

    idQ := hom<Q->Q|>;
    q1 := quads1(rho[11],xT,[1,2],idQ,mons,false);
    q2 := quads1(rho[13],xT,[3,3],maps[1],mons,true);
    quads := [q1[1]-q2[1],q2[2],q2[3]];

  when "mu3-nonsplit" :
 
    L := Parent(xT[2]);
    idL := hom<L->L|L.1>;
    q1 := quads1(rho[11],xT,[1,1],maps[1],mons,true);
    q2 := quads1(rho[12],xT,[2,3],idL,mons,false);
    quads := [q1[1]-q2[1],q2[2],q2[3]];

  when "Diagonal" :

    q1 := quads1(rho[11],xT,[1,1],maps[1],mons,true);
    q2 := quads1(rho[12],xT,[2,2],maps[2],mons,true);
    q3 := quads1(rho[13],xT,[3,3],maps[9],mons,true);
    quads := [q1[1]-q2[1],q1[1]-q3[1],q3[2]];

  when "mu3+Z/3Z" :

    idQ := hom<Q->Q|>;
    q1 := quads1(rho[17],xT,[1,2],idQ,mons,false);
    q2 := quads1(rho[19],xT,[3,3],maps[1],mons,true);
    q3 := quads1(rho[20],xT,[4,5],maps[1],mons,false);
    quads := [q2[1]-q1[1],q3[1]-q1[1],q3[2]];
   
  end case;
  assert #quads eq 3; 
  return quads;
end function;

function Type2Quadrics(E,rho) 
  GaloisAction := ThreeTorsionType(E);
  torspts := ThreeTorsionPoints(E);
  _,_,maps := Explode(E`ThreeDescentAlgebras);
  la := <TorsionPointToSlope(T): T in torspts>;
  AbsEltseq := func<x|&cat[Eltseq(y): y in Eltseq(x)]>;
  P := PolynomialRing(Q,8);
  mons := &join [MD(P,d) : d in [0..2]];
  case GaloisAction :

  when "Generic" :

    conjL,LtoMvia10,LtoMvia01,map1,map2 := Explode(maps);
    M := Codomain(LtoMvia10);
    eqn := quads2(rho[4],rho[6],la,[1,1,1],conjL,LtoMvia10,LtoMvia01);
    Mplus := Domain(map2);
    Embed(Mplus,M,map2(Mplus.1));
    quads := absproj(Mplus,eqn,mons);

  when "2Sylow" :

    conjL,LtoMvia10,LtoMvia01,LtoMvia12,map1 := Explode(maps); 
    L := Domain(conjL);
    M := Codomain(LtoMvia10);
    eqn := quads2(rho[4],rho[7],la,[1,1,1],conjL,LtoMvia12,conjL*LtoMvia01);
    quads := absproj(M,eqn,mons);
    eqn := quads2(rho[4],rho[6],la,[1,1,1],conjL,LtoMvia10,LtoMvia01);
    quads cat:= proj(L,eqn,mons); 

  when "Dihedral" :

    conjL1,conjL2,L2toM1via10,L2toM1via01,L1toM1via12,
      L1toM2via11,L1toM2via12,L2toM2via01 := Explode(maps);
    L1 := Domain(conjL1);
    L2 := Domain(conjL2);
    M1 := Codomain(L2toM1via10);
    M2 := Codomain(L1toM2via11);
    L1toM2via22 := conjL1*L1toM2via11;
    L1toM2via21 := conjL1*L1toM2via12;  
    L2toM1via02 := conjL2*L2toM1via01;
    eqn := quads2(rho[7],rho[13],la,[1,1,2],conjL2,L1toM2via22,L1toM2via21);
    quads := proj(L2,eqn,mons);
    eqn := quads2(rho[7],rho[14],la,[2,1,2],conjL2,L2toM2via01,L1toM2via12);
    quads cat:= absproj(M2,eqn,mons);
    eqn := quads2(rho[6],rho[10],la,[2,2,1],conjL1,L2toM1via10,L2toM1via01);
    quads cat:= proj(L1,eqn,mons);
    eqn := quads2(rho[6],rho[11],la,[1,2,1],conjL1,L1toM1via12,L2toM1via02);
    quads cat:= absproj(M1,eqn,mons);

  when "Generic3Isogeny" :

    conjL1,conjL2,map21,map12,map22,mapA,mapB,map2,map10 := Explode(maps);
    L1 := Domain(conjL1);
    L2 := Domain(conjL2);
    M1 := Codomain(mapA);
    M2 := Codomain(map21);
    eqn := quads2(rho[6],rho[12],la,[2,2,1],conjL1,mapA,mapB);
    M1plus := Domain(map2);
    Embed(M1plus,M1,map2(M1plus.1));
    quads := absproj(M1plus,eqn,mons);
    eqn := quads2(rho[7],rho[13],la,[2,2,2],conjL2,map12,map22);
    quads cat:= proj(L2,eqn,mons);
    eqn := quads2(rho[7],rho[10],la,[1,2,2],conjL2,map10,map21);
    quads cat:= absproj(M2,eqn,mons);

  when "Z/3Z-nonsplit" :

    conjL,map11,map12,map21,map22,map1,map2,map3 := Explode(maps);
    L := Domain(conjL);
    incl := hom<Q->L|>;
    inclL := hom<L->L|L.1>;
    conjQ := hom<Q->Q|>;
    eqn := quads2(rho[10],rho[16],la,[3,3,3],conjL,map12,map22);
    quads := proj(L,eqn,mons);
    eqn := quads2(rho[10],rho[18],la,[1,3,3],conjL,incl,map21);
    quads cat:= proj(L,eqn,mons);
    eqn := quads2(rho[10],rho[19],la,[2,3,3],conjL,incl,map11);
    quads cat:= proj(L,eqn,mons);
    eqn := quads2(rho[8],rho[14],la,[3,3,1,2],conjQ,inclL,map12);
    L2plus := Domain(map2);
    Embed(L2plus,L,map2(L2plus.1));
    quads cat:= proj(L2plus,eqn,mons);
    eqn := quads2(rho[9],rho[15],la,[3,3,2,1],conjQ,inclL,map22);
    L3plus := Domain(map3);
    Embed(L3plus,L,map3(L3plus.1));
    quads cat:= proj(L3plus,eqn,mons);

  when "mu3-nonsplit" :

    conjL1,map0,sig1,sig2,map10,map11,map21,conjM2 := Explode(maps);
    L1 := Domain(conjL1);
    L2 := Domain(map0);
    M1 := Codomain(map0);
    M2 := Codomain(map10);
    idL2 := hom<L2->L2|L2.1>;
    eqn := quads2(rho[8],rho[14],la,[2,3,1],conjL1,map0,map0*sig2);
    quads := absproj(M1,eqn,mons);
    eqn := quads2(rho[9],rho[16],la,[3,3,2,3],idL2,map21,map11);
    quads cat:= proj(L2,eqn,mons);
    eqn := quads2(rho[10],rho[17],la,[2,2,3,2],idL2,map11,map21);
    quads cat:= proj(L2,eqn,mons);
    eqn := quads2(rho[9],rho[18],la,[1,2,2,3],idL2,map10,map21);
    quads cat:= absproj(M2,eqn,mons);
    eqn := quads2(rho[10],rho[19],la,[1,3,3,2],idL2,map10,map11);
    quads cat:= absproj(M2,eqn,mons);

  when "Diagonal" :

    conjL1,conjL2,map1,map2,iota1,iota2,map12,map21,map22,mm := Explode(maps);
    L1 := Domain(conjL1);
    L2 := Domain(conjL2);
    M := Codomain(map1);
    M1 := Codomain(iota1);
    M2 := Codomain(iota2);
    eqn := quads2(rho[8],rho[16],la,[2,3,1],conjL1,map2*iota1,map12*iota1);
    quads := absproj(M1,eqn,mons);
    eqn := quads2(rho[8],rho[24],la,[3,3,1],conjL1,map21*iota1,map22*iota1);
    quads cat:= proj(L1,eqn,mons);
    eqn := quads2(rho[9],rho[18],la,[1,3,2],conjL2,map1*iota2,map21*iota2);
    quads cat:= absproj(M2,eqn,mons);
    eqn := quads2(rho[9],rho[25],la,[3,3,2],conjL2,map12*iota2,map22*iota2);
    quads cat:= proj(L2,eqn,mons);
    eqn := quads2(rho[10],rho[14],la,[1,2,3],map22,map1,map2);
    quads cat:= absproj(M,eqn,mons);
    eqn := quads2(rho[10],rho[20],la,[1,3,3],map22,conjL1*map1,map21);
    quads cat:= absproj(M,eqn,mons);
    eqn := quads2(rho[10],rho[22],la,[2,3,3],map22,conjL2*map2,map12);
    quads cat:= absproj(M,eqn,mons);

  when "mu3+Z/3Z" :

    idQ := hom<Q->Q|>;
    conj := maps[1];
    K := Domain(conj);
    incl := hom<Q->K|>;
    idK := hom<K->K|K.1>;
    eqn := quads2(rho[15],rho[22],la,[3,1,4,5],conj,idK,incl);
    quads := proj(K,eqn,mons);
    eqn := quads2(rho[16],rho[24],la,[3,2,5,4],conj,idK,incl);
    quads cat:= proj(K,eqn,mons);
    eqn := quads2(rho[14],rho[26],la,[5,1,3],conj,idK,incl);
    quads cat:= proj(K,eqn,mons);
    eqn := quads2(rho[14],rho[28],la,[4,2,3],conj,idK,incl);
    quads cat:= proj(K,eqn,mons);
    eqn := quads2(rho[12],rho[30],la,[4,3,1,2],idQ,idK,conj);
    quads cat:= proj(K,eqn,mons);
    eqn := quads2(rho[13],rho[32],la,[5,3,2,1],idQ,idK,conj);
    quads cat:= proj(K,eqn,mons);
    eqn := quads2(rho[15],rho[34],la,[3,4,4,5],conj,conj,conj);
    quads cat:= proj(K,eqn,mons);
    eqn := quads2(rho[16],rho[36],la,[3,5,5,4],conj,conj,conj);
    quads cat:= proj(K,eqn,mons);
    eqn := quads2(rho[15],rho[38],la,[2,5,4,5],conj,incl,idK);
    quads cat:= proj(K,eqn,mons);
    eqn := quads2(rho[16],rho[40],la,[1,4,5,4],conj,incl,idK);
    quads cat:= proj(K,eqn,mons);
    eqn := quads2(rho[14],rho[42],la,[4,5,3],conj,conj,conj);
    quads cat:= proj(K,eqn,mons);
    eqn := quads2(rho[12],rho[44],la,[5,5,1,2],idQ,idK,conj);
    quads cat:= proj(Q,eqn,mons);
    eqn := quads2(rho[13],rho[45],la,[4,4,2,1],idQ,idK,conj);
    quads cat:= proj(Q,eqn,mons);
  
  end case;
  assert #quads eq 24;
  return quads;
end function;

function ProjectToColumn(quads,triv)
  R<x,y,z>:=PolynomialRing(Q,3);
  RR<y1,y2,y3,x1,x2,x3> := PolynomialRing(Q,6);
  col := Matrix(RR,3,1,[x1,x2,x3]);
  row := Matrix(RR,1,3,[y1,y2,y3]);
  mons := Eltseq(col*row);
  T := Matrix(Q,9,9,[Eltseq(mat):mat in triv]);
  T := Transpose(T)^(-1);
  subst := [&+[T[i,j]*mons[j]: j in [1..9]]: i in [2..9]];
  quads := [Evaluate(q,subst) : q in quads];
  mons3 := MD(R,3);
  monsx := [Evaluate(mon,[x1,x2,x3]): mon in mons3];
  monsy := [Evaluate(mon,[y1,y2,y3]): mon in MD(R,2)];
  mons := [monx*mony : monx in monsx, mony in monsy];
  polys := [x*q : x in [x1,x2,x3], q in quads];
  V := VectorSpace(Q,60);
  U := sub<V|[V![MC(p,mon): mon in mons]: p in polys]>;
  W := sub<V|[V.i : i in [1..10]]>;
  UW := U meet W;
  assert Dimension(UW) eq 1;
  coeffs := Basis(UW)[1];
  cubic := &+[coeffs[i]*mons3[i] : i in [1..10]];
  cubic /:= MyContent(cubic);
  return cubic;
end function;


function ChangeToNewBasis(aa)
  mm := IdentityMatrix(Rationals(),0);
  for a in aa do
    elt := a;
    L := Parent(elt);
    if L cmpeq Rationals() then
      P := PolynomialRing(Rationals()); X:=P.1;
      L := NumberField(X-1:DoLinearExtension);
      elt := L!a;
    end if;
    OL := RingOfIntegers(L);
    myid := ideal<OL|elt>; // * Different(OL) perhaps????
    ff := Factorization(myid);
    FracOL := FieldOfFractions(OL);
    cbrtid := &*[PowerIdeal(FracOL)| f[1]^(-Floor(f[2]/3)): f in ff];
    bb := Basis(cbrtid);
    mm := DiagonalJoin(mm,Matrix(#bb,#bb,[Eltseq(b): b in bb]));
  end for;
  return mm;
end function;


intrinsic ThreeDescentCubic(E::CrvEll[FldRat],alpha::Tup:
    Method := "HessePencil", 
    ThreeTorsPts := ThreeTorsionPoints(E)) 
 -> Crv, MapSch, RngMPolElt
{Computes a plane cubic curve representing the same element of S^(3)(E/Q) as alpha in L^*/(L^*)^3,
where E[3] - \{0\} = Spec L. }

// "\nalpha ="; alpha;

  Check := true;
  torspts := ThreeTorsPts;
  require Method in {"HessePencil","FlexAlgebra","SegreEmbedding"} 
          :"Method should be \"Hesse Pencil\", \"FlexAlgebra\" or \"SegreEmbedding\"";
  
  GaloisType := ThreeTorsionType(E);
  E`ThreeTorsionPoints := torspts;
  L := CartesianProduct(<Ring(Parent(T)) : T in torspts>);
  require alpha in L : "alpha does not belong to the etale algebra.";
  vprintf ThreeDescent, 1 : " ** ThreeDescentCubic **\n";
  if Conductor(E) lt (mm where _,mm is ConductorRange(CD)) then 
    vprintf ThreeDescent, 1 : "E = %o, (#E(Q)_tors = %o), ",
    CremonaReference(E),#TorsionSubgroup(E);
  else 
    vprintf ThreeDescent, 1 : "N = %o, (#E(Q)_tors = %o), ",
    Conductor(E),#TorsionSubgroup(E);
  end if;
  vprintf ThreeDescent, 1 : "Galois action on E[3] is \"%o\".\n",GaloisType;
  vprintf ThreeDescent, 1 : "alpha = %o\n",alpha;
  while true do
    B,BB,maps,eps := Explode(ThreeDescentAlgebras(E));
    R := Universe(B);
    aa := R!Flat(<<1>,alpha>);

    vprintf ThreeDescent,1 : 
      "Converting alpha in R^* to rho in (R tensor R)^* ....\n";
    rho := AlphaToRho(E,aa,Check); 
    vprintf ThreeDescent,1 : "  .... done. \n";

    epsrho := PointwiseMultiply(eps,rho);

    vprintf ThreeDescent,1 : "Computing the obstruction algebra ....\n";
    A := EnvelopingAlgebra(E,epsrho:Check:=Check);
    vprintf ThreeDescent,1 : " .... done.\n";
 
    cob := ChangeToNewBasis(aa);
    assert Nrows(cob) eq 9;
    bas := [&+[cob[i,j]*A.j: j in [1..9]]: i in [1..9]];
    AA := ChangeBasisCSAlgebra(A, Identity(A), bas,true);

    vprintf ThreeDescent,1 : "Trivialising the obstruction algebra ....\n";

    if true then
       // This one was observed to be around twice as fast, 
       // fairly uniformly over all kinds of examples
       // (and produces results that are as good for the subsequent steps)
       //"General maximal"; time
       bb := Basis(MaximalOrder(AA)); 
    else
       //"Stoll maximal"; time
       bb := MaximalOrder(AA, []); 
    end if;
 
    trivmethod := "new";
    // Sticking with the old method for now; see remarks at the top of trivialize1.m
//for trivmethod in ["old","new"] do
    case trivmethod :
      when "old" : 
        //"MS trivial"; time 
        iso := Trivialize(AA,bb);
      when "new" : 
        //"TF trivial"; time 
        iso := TrivializeNew(AA,bb:AdHocReduce:=true);
    end case;
//end for; "";

    if iso cmpne 0 then break; 
    else vprint ThreeDescent,1 : "Trivialize ran into difficulty, starting ThreeDescentCubic again";
    end if;  
  end while;
  mats := [ iso(AA.i) : i in [1..9] ];
  //if Check then error if not IsTrivialisation(AA,mats), "Incorrect trivialisation."; end if;
  cob := cob^(-1);
  mats := [&+[cob[i,j]*mats[j]: j in [1..9]]: i in [1..9]];
  vprintf ThreeDescent, 1 : " .... trivialising done.\n";
  if Check then error if not IsTrivialisation(A,mats), "Incorrect trivialisation."; end if;

  vprintf ThreeDescent, 1 : "Using the \"%o\" method.\n",Method;
  case Method:

  when "HessePencil":

    m := NumberOfComponents(R);
    B := EtaleAlgebraDualBasis(R);
    M := <&+[B[i][j]*mats[i] : i in [1..9]]: j in [1..m]>;
    if Check then 
      vprint ThreeDescent,3 : M;
      error if exists{ MT : MT in M | not IsScalar(MT^3) }, 
        "M^3 should be a scalar matrix.";
      detM := <Determinant(mat): mat in M>;
      error if detM ne aa, "We should find Det(M) = alpha.";
    end if;
    cubics := MatrixToPencil(M[m]);
    assert #cubics eq 2;
    P3<x,y,z> := Universe(cubics);
    vprintf ThreeDescent, 1 : 
       "The cubic sought belongs to the pencil spanned by\n%o\n", cubics;
    cubics := FindInPencil(cubics,E);
    cubics := [c : c in cubics | IsIsomorphic(Jacobian(c),E) ]; 
    error if #cubics ne 1, "We find",#cubics,"cubics with Jacobian E";
    cubic := cubics[1];
    vprintf ThreeDescent, 1 : "The only cubic in this pencil with Jacobian E is\n%o\n", cubic;

  when "FlexAlgebra":

    m := NumberOfComponents(L);
//    require not forall{ i : i in [1..m] | IsPower(aa[i],3) } 
//      : "Element of R^*/(R^*)^3 is trivial.";  
    V,mapRtoV := AlgebraToVectorSpace(R);
    vprintf ThreeDescent, 1 : "Computing the flex algebra ....\n";
    FA := EnvelopingAlgebra(E,rho:Check:=Check);
    vprintf ThreeDescent, 1 : " .... and mapping to a number field ....\n";
    F,mapFAtoF := AlgebraToNumberField(FA); 
    mapVtoF := hom<V->FA|Basis(FA)> * mapFAtoF;
    vprintf ThreeDescent, 1 : " .... done.\n";
    vprintf ThreeDescent, 1 : "Flex field has defining polynomial\n%o\n",DefiningPolynomial(F);
    vprintf ThreeDescent, 1 : "Trivialising the obstruction algebra over the flex field ....\n";
    M := < TorsionMatrix(T) : T in torspts >;
    c4,c6 := Explode(cInvariants(E));
    mats1 := [Matrix(Q,3,3,[Trace(b*M[k][i,j]):i,j in [1..3]])
      : b in IntegralBasis(R[k+1]), k in [1..m]];
    mats1 := [IdentityMatrix(Q,3)] cat mats1;
    MQ := RMatrixSpace(Q,3,3);
    MF := RMatrixSpace(F,3,3);
    mapVtoMQ := hom<V->MQ|mats1>;
    t1 := func<r|mapVtoMQ(mapRtoV(r))>;
    iotaF := func<r|mapVtoF(mapRtoV(r))>;
    B1 := EtaleAlgebraBasis(R);
    B2 := EtaleAlgebraDualBasis(R); 
    matsF := [ &+[ iotaF(B2[i])*MF!t1(PointwiseMultiply(B1[i],B1[j])) 
                    : i in [1..9]] : j in [1..9]];
    if Check then 
      matsFalt := [ &+[iotaF(B1[i])*MF!t1(PointwiseMultiply(B2[i],B1[j]))
		        : i in [1..9]] : j in [1..9]];
      assert matsF eq matsFalt;
      error if not IsTrivialisation(A,matsF), "Incorrect trivialisation.";
    end if;
    vprintf ThreeDescent, 1 : 
      " .... and comparing with trivialisation over the rationals ....\n";
    B := Transpose(ConjugationMatrix(F,mats,matsF));
    vprintf ThreeDescent, 1 : " .... done.\n";
    cubic1 := GenusOneModel(3,[Q|-1,0,54*c6,0,0,0,1,27*c4,0,0])`Equation;
    _,tr1B := IsTransformation(3,<1,B>);
    cubicF := apply(tr1B, ChangeRing(Parent(cubic1),F)!cubic1 );
    cubics := RationalProjections(cubicF);
    error if #cubics ne 1, "We find ",#cubics," cubics.";
    cubic := cubics[1];
    P3<x,y,z> := Parent(cubic);
    vprintf ThreeDescent, 1 : "The cubic sought is\n%o\n",cubic;

  when "SegreEmbedding" :

    vprintf ThreeDescent, 1 : "Computing equations for C_rho .... \n";
    quads1 := Type1Quadrics(E,rho); 
    quads2 := Type2Quadrics(E,rho); 
    vprintf ThreeDescent, 1 : 
      " .... and rewriting as 18 quadrics over Q ....\n";
    PP<[X]> := Universe(quads1);
    quads2 := ChangeUniverse(quads2,PP);
    mons := &join [MD(PP,d): d in [0..2]];
    V := VectorSpace(Q,45);
    U1 := sub<V|[[MC(q,mon):mon in mons]: q in quads1]>;
    U2 := sub<V|[[MC(q,mon):mon in mons]: q in quads2]>;
    W := sub<V|[V.i : i in [10..45]]>;
    U := (U1 + U2) meet W;
    require Dimension(U) eq 18 : "We find ",Dimension(U)," quadrics."; 
    quads := [&+[B[i]*mons[i]: i in [1..45]]: B in Basis(U)];
    vprintf ThreeDescent, 1 : " .... done.\n";

    vprintf ThreeDescent, 1 : "Multipling by fudge factor 1/yT .... \n";
    a1,a2,a3,a4,a6 := Explode(aInvariants(E));
    yT := <216*(T[2] + (a1*T[1] + a3*T[3])/2)/T[3] : T in torspts>;  
    V,mapLtoV := AlgebraToVectorSpace(L); 
    B1 := EtaleAlgebraBasis(L);
    B2 := [PointwiseMultiply(yT,b): b in B1];
    mat1 := Matrix(Q,8,8,[Eltseq(mapLtoV(b)) : b in B1]);
    mat2 := Matrix(Q,8,8,[Eltseq(mapLtoV(b)) : b in B2]);
    mat := Transpose(mat2*mat1^(-1));
    subst := [&+[mat[i,j]*PP.j: j in [1..8]]: i in [1..8]];
    quads := [Evaluate(q,subst) : q in quads];
    vprintf ThreeDescent, 1 : " .... done.\n";

    vprintf ThreeDescent, 1 : "Projecting onto a column .... \n";
    cubic := ProjectToColumn(quads,mats);
    vprintf ThreeDescent, 1 : " .... done.\n";

    P3<x,y,z> := Parent(cubic);
    vprintf ThreeDescent, 1 : "The cubic sought is\n%o\n",cubic;

  end case;

  vprintf ThreeDescent, 1 : "Minimising gives\n";
  cubic := Minimise(cubic);
  vprintf ThreeDescent, 1 : "%o\n", cubic;

  vprintf ThreeDescent, 1 : "Reducing gives\n";
  cubic := Reduce(cubic);
  vprintf ThreeDescent, 1 : "%o\n", cubic;

  C,_,maptoE := nCovering(GenusOneModel(cubic) : E:=E ); 
  return C, maptoE, cubic;

end intrinsic; // ThreeDescentCubic



intrinsic ThreeDescent(E::CrvEll[FldRat] : Method := "HessePencil") 
     ->  SeqEnum[Crv], List
{A list of elements of the 3-Selmer group of E, given as plane cubic curves, 
and a list of the corresponding maps to E. }
  S3,S3map := ThreeSelmerGroup(E);
  vecs := {};
  for v in S3 do
    if -v notin vecs and v ne Parent(v)!0 then 
      vecs := vecs join {v};
    end if;
  end for;
  assert #vecs eq (#S3-1)/2;
  alphas := [S3map(v): v in vecs];

// "\nalphas are"; alphas;
// "\nTheir squares are"; [S3map(-v): v in vecs];

  R<x,y,z> := PolynomialRing(Q,3); 
  cubics := [ ];
  mapstoE := [* *];
  for alpha in alphas do
     cubic, maptoE := ThreeDescentCubic(E,alpha:Method:=Method);
     Append( ~cubics, cubic );
     Append( ~mapstoE, maptoE );
  end for;
  return cubics, mapstoE;
end intrinsic; 
