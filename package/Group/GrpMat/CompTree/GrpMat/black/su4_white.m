freeze;

import "white-prelims.m": ImageInLtilde, norm, trace, form, 
                          CommutatorSpace, IsPowerOfTwo, 
                          IsOrderMoreThanThree, IsMersenne, 
                          IsFermat, Isppdhash, 
                          MyChangeOfBasisMatrix, 
                          ElementHavingPrescribedTrace, 
                          ElementHavingPrescribedNorm, formRest, 
                          OrthogonalComplement, FindHyperbolicPair, 
                          GetVector, GetFpBasisVectors;
import "su3_white.m": writeSLP;

ConstructL := function(G, GG, F, F0, q, P)
    limit1 := 48; // how many times do we attempt to find tau?
    limit2 := 10; // how many times do we attempt to construct L for chosen tau?
    _, p, k := IsPrimePower(q);
    Ggens := [G.i : i in [1..Ngens(G)]];
    //first find tau.
    i := 1;
    repeat
        i +:= 1;
        t, w := Random(P);
        o2 := q^2 -q +1 ;
        a := t^o2;
        ot := Order(t);
        oa := ot div (Gcd(o2, ot));
        cond := Isppdhash(oa, p, 2*k);
        cond2 := exists(z){ e : e in Eigenvalues(a) | e[2] eq 1};
        cond3 := Isppdhash(ot, p, 2*k) and Isppdhash(ot, p, 6*k);
    until (cond3 and cond and cond2) or i eq (limit1 + 1);
    if not(cond and cond2 and cond3 ) then
    return false, _, _, _, _, _, _, _, _ ;
    end if;

    //now construct L.
    worda := w^o2;
    evalue1 := z[1];
    espace1 := Eigenspace(a, evalue1);
    i := 1;
    repeat
        g, w := Random(P); 
        b := a^g; 
        A := sub< GG | [a, b]>;
        L, WL := DerivedGroupMonteCarlo(A);
        S := Generators(L);                                                                     
        Lmod := GModule(L);
        VL := sub<Lmod | espace1.1, espace1.1*g>;
        LL := MatrixGroup<2, F | [ActionGenerator(VL, i) : i in [1..Ngens(L)]]>;
        f := false;
        flag := RecognizeClassical(LL : Case := "unitary");
        ff := false;
        if flag then 
            ff, Ltilde := IsOverSmallerField(LL, k);
            if not ff then
                Ltilde := LL;
            else
                reducedimage := map<Generic(LL) -> Generic(Ltilde) | 
                                   x:-> SmallerFieldImage(LL, x) >;
                subLtilde := sub<Generic(Ltilde) | 
                            [LL.i @ reducedimage : i in [1..Ngens(LL)]]>;
                Ltilde := subLtilde;
            end if;
       	    f, aa, bb, cc, dd := RecognizeSL2(Ltilde, q);
        end if;
        if ff then 
            aa := hom<Generic(LL) -> Generic(SL(2, q)) | 
                        x:->((x @ reducedimage) @ aa)>; 
            bb := hom<Generic(SL(2, q)) -> Generic(LL) | 
                        x:-> Evaluate((( x @ bb) @ cc), Ggens)>;
            cc := hom<Generic(LL) -> Codomain(cc) | 
                        x:->((x @ reducedimage) @ cc) >;
            dd := hom< Domain(dd) -> Generic(LL) | x:-> Evaluate(x, Ggens)>;
        end if;
        i +:= 1;
    until f or i eq (limit2 + 1);
    if not f then 
       return false, _, _, _, _, _, _, _, _ ;
    end if;
    wordb := worda^w;
    wordL := [Evaluate(WL[i], [worda, wordb]) : i in [1..Ngens(L)]];
    return true, L, wordL, VL, Lmod, aa, bb, cc, dd; 
end function;

//====================================================
//      Algorithmic properties of Q(x). Section 6.4.5.
//====================================================
/*
  Note that elements of Q(x) have the form:

  r_1(w, lambda) = [ 1        0     0   0 ]
                   [-b^q      1     0   0 ]
                   [lambda^q  a     1   b ]
                   [ -a^q     0     0   1 ]

  where, w = a*e2 + b*f2 and lambda + lambda^q = -(w, w).
*/

GetVector_SU4 := function(TQ, u)
    E := BaseRing(Parent(u));
    k := Degree(E) div 2;
    p := Characteristic(E);
    F := GF(p);
    V, f := VectorSpace(E, F);
    a := u[3, 2];
    b := u[3, 4];
    va := a @ f;
    vb := b @ f;
    v := [va[i] : i in [1..Ncols(va)]] cat [  vb[i] : i in [1..Ncols(vb)]];
    return v;
end function;

GetFpBasisVectors_SU4 := function(TQ)
    k := Degree(BaseRing(TQ[1])) div 2;
    FpBasis := [TQ[i] : i in [1..4*k]];
    vFpBasis := [GetVector_SU4(TQ, FpBasis[i]) : i in [1..#FpBasis]];
    return vFpBasis;
end function;

GetTVector_SU4 := function(Tgens, t)
    delta := Tgens[1][3, 1];
    E := BaseRing(Parent(t));
    k := Degree(E) div 2;
    p := Characteristic(E);
    FF := GF(p^k);
    F := GF(p);
    V, f := VectorSpace(FF, F);
    v := ((t[3, 1]/delta) @ f) ;
    return v;
end function;

writeQSLP_SU4 := function(TQ, u)
    W := SLPGroup(#TQ);
    E := BaseRing(Parent(u));
    k := Degree(E) div 2;
    p := Characteristic(E);
    F := GF(p);
    FpBasis := [TQ[i] : i in [1..4*k]];
    vFpBasis := [GetVector_SU4(TQ, FpBasis[i]) : i in [1..#FpBasis]];
    Tgens := [TQ[i] : i in [5*k+1..#TQ]];
    vutilde := GetVector_SU4(TQ, u);
    RREF := EchelonForm(Transpose(Matrix(vFpBasis cat [vutilde])));
    vutilde := Transpose(RREF)[#FpBasis+1];
    vutilde := [Integers()!vutilde[i] : i in [1..Ncols(vutilde)]];
    //sigma is a word in TQ that evaluates to utilde in uT.
    sigma := &*[W.i^(vutilde[i]) : i in [1..#vutilde]];
    utilde := Evaluate(sigma, TQ);
    //t in T(x), (x, xperp)-transvections
    t := u*utilde^-1;
    if t ne Identity(Parent(t)) then
        //use linear algebra to find a word for t in Tgens
        vTgens := [GetTVector_SU4(Tgens, Tgens[i]) : i in [1..#Tgens]];
        vt := GetTVector_SU4(Tgens, t);
        RREF := EchelonForm(Transpose(Matrix(vTgens cat [vt])));
        vt := Transpose(RREF)[#Tgens+1];
        vt := [Integers()!vt[i] : i in [1..Ncols(vt)]];
        tau := &*[(W.(i+5*k))^(vt[i]) : i in [1..#Tgens]];
        //note that Evaluate(tau, TQ) = t.
    else 
        tau := Identity(Parent(sigma));
    end if;
    return sigma*tau;
end function;

/* Made for the construction of c:
   input:(1) T1 defined in Section 6.4.6.
   (2) an element t of the group generated by T1
   output:(1) A word in T1 for t.
*/
GetTiWord := function(T1, t)
    W := SLPGroup(#T1);
    E := BaseRing(T1[1]);
    k := Degree(E) div 2;
    p := Characteristic(E);
    F := GF(p);
    if t[1, 2] eq 0 then
        tt := t[2, 1];
        TT1 := [T1[i][2, 1] : i in [1..#T1]];
    else
        tt := t[1, 2];
        TT1 := [T1[i][1, 2] : i in [1..#T1]];
    end if;
    V, f := VectorSpace(E, F);
    vT1 := [ (TT1[i] @ f) : i in [1..#T1]];
    vt := tt @ f;
    RREF := EchelonForm(Transpose(Matrix(vT1 cat [vt])));
    vt := Transpose(RREF)[#T1 +1];
    vt := [Integers()!vt[i] : i in [1..#T1]];
    wt := &*[W.i^(vt[i]) : i in [1..#T1]];
    return wt;
end function;

FindGens_SU4 := function(G, p, k)
    limit1 := 10; // how many times do we attempt to construct L?
    limit2 := 12; // how many times do we attempt to construct natural SU3 subgroups?

    q := p^k;
    GG := Generic(G);
    F := GF(q^2);
    F0 := sub< F | F.1^(q+1)>;                 
    P := RandomProcessWithWords(G);
    counter := 0;
    repeat
        f, L, wordL, VL, Lmod, aa, bb, cc, dd := ConstructL(G, GG, F, F0, q, P);
        counter +:= 1;
    until f or counter eq limit1;
    if not f then
        return false;
    end if;
    S := Generators(L);
    Lgens := [L.i : i in [1..Ngens(L)]];

    //=========================================
    // Some elements of L. Section 6.3.3.
    //=========================================

    B := ClassicalForms(G)`sesquilinearForm;
    //construct a hyperbolic basis
    comLL := CommutatorSpace(F, S);
    comL := sub<Lmod | comLL>;
    e1, f1 := FindHyperbolicPair(F0, F, comL, B, k, Lmod);
    e1 := Lmod!e1; 
    f1 := Lmod!f1;
    efComplement := OrthogonalComplement(comL, Lmod, B, k);
    e2, f2 := FindHyperbolicPair(F0, F, efComplement, B, k, Lmod);
    e2 := Lmod!e2; 
    f2 := Lmod!f2;
    // assert that e1, e2, f1, f2 is a standard basis.
    assert formRest(e1, f1, B, k, Lmod) eq 1
       and formRest(e2, f2, B, k, Lmod) eq 1
       and formRest(e1, e2, B, k, Lmod) eq 0 
       and formRest(f1, f2, B, k, Lmod) eq 0
       and formRest(e1, f2, B, k, Lmod) eq 0
       and formRest(f1, e2, B, k, Lmod) eq 0;
    Basis := [Vector(e1), Vector(e2), Vector(f1), Vector(f2)];
    delta := ElementHavingPrescribedTrace(F, 0);
    deltabar := Frobenius(delta, F0);
    CB := MyChangeOfBasisMatrix(VectorSpace(Lmod), Basis);
    CB := GG!CB;
    // Original generators in new basis.
    gens := [(GG!G.i)^(CB^-1) : i in [1..Ngens(G)]];
    //construct r and t_i defined in Section 6.4.3.
    r := GG![0, 0, deltabar, 0,   0, 1, 0, 0,   delta^-1, 0, 0, 0,   0, 0, 0, 1];
    rtilde := ImageInLtilde(r^CB, comLL);
    wordr := Evaluate((rtilde @ cc), wordL);
    zeta := PrimitiveElement(F0);
    tList := [(GG! [ 1, 0, 0, 0, 0, 1, 0, 0, zeta^(i-1)*delta, 0, 1, 0, 0, 0, 0, 1]) 
                         : i in [1..k]];
    wordtList := [(Evaluate(ImageInLtilde((tList[i])^CB, comLL) @ cc, wordL)) 
                         : i in [1..#tList]];

    //====================================
    //      The subgroup Q. Section 6.4.4.
    //====================================

    //construct J1
    i := 1;
    repeat 
       g1, wordg1 := Random(P); 
       g1 := g1^(CB^-1);
       g1 := GG!g1;
       J1gens := tList cat tList^r cat tList^g1;
       J1 := sub<GG | J1gens>;
       comJ1 := CommutatorSpace(F, J1gens);
       comJ1IsNonsingular := Dimension(comJ1*CB meet 
             OrthogonalComplement(comJ1*CB, Generic(comJ1*CB), B, k)) eq 0;
       if comJ1IsNonsingular then
       	  J1mod := GModule(J1);
	  comJ1mod := sub< J1mod | comJ1>;
	  J1tildegens := [ GL(3, q^2)!ActionGenerator(comJ1mod, i) : i in [1..Ngens(J1)]];
	  J1tilde := sub< Parent(J1tildegens[1]) | J1tildegens>;
	  assert IsIrreducible(J1tilde);
          isit := RecognizeClassical(J1tilde : Case := "unitary");
       end if;
       i +:= 1;
    until (comJ1IsNonsingular and isit) or i eq (limit2+1);
    if not ((comJ1IsNonsingular and isit) or i eq (limit2+1)) then 
        return false;
    end if;
    wordJ1gens := wordtList cat [wordtList[i]^wordr : i in [1..#tList]] 
                        cat [wordtList[i]^wordg1 : i in [1..#tList]];
    f1, a1, b1, c1, d1 := RecogniseSU3(J1tilde, q);
    rec1 := J1tilde`SU3DataStructure;
    X1 := rec1`Mygens;
    wX1 := rec1`wMygens;
    CB1 := rec1`CB;
    //some stuff needed to use writeSLP and hence produce TQ1
    bbgens1 := [X1[i] : i in [1..6*k]];
    wbbgens1 := [wX1[i] : i in [1..6*k]];
    Qgens1 := [X1[i] : i in [1..3*k]];
    wQgens1 := [wX1[i] : i in [1..3*k]];
    J1form := rec1`classicalform;
    r1 := X1[#X1];
    wr1 := wX1[#X1];
    //The following constructs TQ1, a generating list for O_p((J1tilde)_x) 
    alpha := J1form[2, 2];
    alpha := ElementHavingPrescribedNorm(1/alpha, F0, F, q);
    shift1 := Generic(J1tilde)![1, 0, 0, 0, alpha, 0, 0, 0, 1];
    TQ1tilde := Qgens1^shift1;
    TQ1tilde := TQ1tilde^(CB1^-1);
    wTQ1 := [writeSLP(bbgens1, wbbgens1, r1, wr1, TQ1tilde[i]) : i in [1..#TQ1tilde]];
    TQ1 := Evaluate(wTQ1, J1gens);
    wTQ1 := Evaluate(wTQ1, wordJ1gens);
    // construct J2
    i := 1;
    repeat
        g2, wordg2 := Random(P);
        g2 := g2^(CB^-1);
        g2 := GG!g2;
        J2gens := tList cat tList^r cat tList^g2;
        J2 := sub<GG | J2gens>;
        comJ2 := CommutatorSpace(F, J2gens);
        comJ2IsNonsingular := Dimension(comJ2*CB meet
             OrthogonalComplement(comJ2*CB, Generic(comJ2*CB), B, k)) eq 0;
        if comJ2IsNonsingular then
           J2mod := GModule(J2);
           comJ2mod := sub< J2mod | comJ2>;
           J2tildegens := [ GL(3, q^2)!ActionGenerator(comJ2mod, i) : i in [1..Ngens(J2)]];
           J2tilde := sub< Parent(J2tildegens[1]) | J2tildegens>;
           assert IsIrreducible(J2tilde);
           isit := RecognizeClassical(J2tilde : Case := "unitary");
        end if;
        i +:= 1;
    until (comJ2IsNonsingular and isit and comJ2 ne comJ1) or i eq (limit2+1);
    if not (comJ2IsNonsingular and isit and comJ2 ne comJ1) then 
	return false;
    end if;
    wordJ2gens := wordtList cat [wordtList[i]^wordr : i in [1..#tList]] 
                          cat [wordtList[i]^wordg2 : i in [1..#tList]];
    f2, a2, b2, c2, d2 := RecogniseSU3(J2tilde, q);
    rec2 := J2tilde`SU3DataStructure;
    X2 := rec2`Mygens;
    wX2 := rec2`wMygens;
    CB2 := rec2`CB;
    //some stuff needed to use writeSLP and hence produce TQ1
    bbgens2 := [X2[i] : i in [1..6*k]];
    wbbgens2 := [wX2[i] : i in [1..6*k]];
    Qgens2 := [X2[i] : i in [1..3*k]];
    wQgens2 := [wX2[i] : i in [1..3*k]];
    J2form := J2tilde`SU3DataStructure`classicalform;
    r2 := X2[#X2];
    wr2 := wX2[#X2];
    //The following constructs TQ2, a generating list for O_p((J2tilde)_x)
    alpha := J2form[2, 2];
    alpha := ElementHavingPrescribedNorm(1/alpha, F0, F, q);
    shift := Generic(J2tilde)![1, 0, 0, 0, alpha, 0, 0, 0, 1];
    TQ2tilde := Qgens2^shift;
    TQ2tilde := TQ2tilde^(CB2^-1);
    wTQ2 := [writeSLP(bbgens2, wbbgens2, r2, wr2, TQ2tilde[i]) : i in [1..#TQ2tilde]];
    TQ2 := Evaluate(wTQ2, J2gens);
    wTQ2 := Evaluate(wTQ2, wordJ2gens);
    //construct a generating set TQ for Q (in a nice order).
    TQ := [TQ1[i] : i in [1..2*k]] cat [TQ2[i] : i in [1..2*k]] cat 
          [TQ1[i] : i in [2*k+1..#TQ1]] cat [TQ2[i] : i in [2*k+1..#TQ2]];
    wTQ := [wTQ1[i] : i in [1..2*k]] cat [wTQ2[i] : i in [1..2*k]] cat
           [wTQ1[i] : i in [2*k+1..#wTQ1]] cat [wTQ2[i] : i in [2*k+1..#wTQ2]];
    //===========================================
    //      The generating set T. Section 6.4.6.
    //===========================================

    rho := PrimitiveElement(F);
    //my h1
    hhh := SU(3, q)![rho, 0, 0, 0, rho^(q-1), 0, 0, 0, 1/rho^q];
    hhh := hhh^shift1;
    hhh := hhh^(CB1^-1);
    whhh := writeSLP(bbgens1, wbbgens1, r1, wr1, hhh);
    hhh := Evaluate(whhh, J1gens);
    whhh := Evaluate(whhh, wordJ1gens);
    
    T1 := [GG![1, 0, 0, 0, -Frobenius(rho, F0)^i, 1, 0, 0, 0, 0, 1, rho^i, 0, 0, 0, 1] : i in [0..2*k-1]];
    wT1 := [Evaluate(writeQSLP_SU4(TQ, T1[i]), wTQ) : i in [1..#T1]];
    T2 := [GG![1, rho^i, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -Frobenius(rho, F0)^i, 1] : i in [0..2*k-1]];
    T2rinv := T2^(r^-1);
    wT2 := [Evaluate(writeQSLP_SU4(TQ, T2rinv[i]), wTQ) : i in [1..#T2]];
    wT2 := [wT2[i]^wordr : i in [1..#T2]];
    TL := T1 cat T2;
    wTL := wT1 cat wT2;
    //constructing c
    g := T1[1]*T2[1];
    G2 := GL(2, q^2);
    assert g[2, 1] ne 0 and g[1, 2] ne 0;
    //kill g[2, 2]
    if g[2, 2] ne 0 then 
        b := g[1, 2];
        d := g[2, 2];
        x := G2![1, 0, -d/b, 1];
        wx := GetTiWord(T1, x);
        x := Evaluate(wx, T1);
        g := x*g;
        wx := Evaluate(wx, wT1);
    else 
        wx := Identity(Parent(wT1[1]));
    end if;
    //kill g[1, 1]
    if g[1, 1] ne 0 then
        a := g[1, 1];
        c := g[2, 1];
        y := Generic(G2) ! [1, -a/c, 0, 1];
        wy := GetTiWord(T2, y);
        y := Evaluate(wy, T2);
        g := y*g;
        wy := Evaluate(wy, wT2);
    else 
        wy := Identity(Parent(wT2[1]));
    end if;
    wg := wy*wx*wT1[1]*wT2[1];
    c := g;
    wc := wg;
    TE := TQ cat TQ^c;
    wTE := wTQ cat [wTQ[i]^wc : i in [1..#TQ]];
    TF := TQ^r cat TQ^(r*c);
    wTF := [wTQ[i]^wordr : i in [1..#TQ]] cat [wTQ[i]^(wordr*wc) : i in [1..#TQ]];
    TU := [ Generic(G) ! [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, -delta, 0, 1]];
    u := TU[1];
    // u^c is in Q.
    wuc := writeQSLP_SU4(TQ, u^c);
    wuc := Evaluate(wuc, wTQ);
    wu := wuc^(wc^-1);
    wTU := [wu];
    //"c =", c;
    TLtilde := Lgens^(CB^-1);
    wTLtilde := wordL;
    T := TL cat TE cat TF cat TLtilde cat TU cat [r, c, hhh];
    wT := wTL cat wTE cat wTF cat wTLtilde cat wTU cat [wordr, wc, whhh];
    Petersgens := T^(CB);

    ////////////////////////////////////
    // Constructing Eamonn's generators 
    ////////////////////////////////////

    // construct u = v 
    if (q mod 2 eq 1) then
        vv0 := hhh^((q^2-1) div 2);
        wv0 := whhh^((q^2-1) div 2);
    else
        vv0 := Identity (GL (4, q^2));
        wv0 := Identity (WordGroup (G));
    end if;
    v := vv0*c^(-1);
    //"v = ", v;
    u := v;
    wv := wv0 * wc^(-1);
    wu := wv;

    // construct x
    x := (T[2*k + 1])^-1;
    wx := (wT[2*k + 1])^-1;
    //"x = ", x;
    // construct y 
    MatAlg := MatrixAlgebra(F, 4);
    TLmats := [MatAlg!TL[i] : i in [1..#TL]];
    sl2TL := [ExtractBlock(TLmats[i], 1, 1, 2, 2) : i in [1..#TL]];
    sl2TL := [GL(2, q^2)!sl2TL[i] : i in [1..#TL]]; 
    sl2L := sub<GL(2, q^2) | sl2TL>;
    //"L = ", sl2L;
    f, newa, newb, newc, newd := RecogniseSL2(sl2L, q^2);
    assert f;
    yy := GL(2, q^2)![rho^q, 0, 0, rho^(q^2-q-1)];
    //"yy = ", yy;
    assert Determinant(yy) eq 1;
    assert ((yy @ newc) @ newd) eq yy;
    wyy := (yy @ newc);
    //"wyy evaluates to", Evaluate(wyy, sl2TL);
    y := Evaluate(wyy, TL);
    wy := Evaluate(wyy, wTL);
    //"y = ", y;

    E := ClassicalStandardGenerators("SU", 4 , q);
    conj := Generic(G)![0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0];
    E := E^conj;
    E1 := E[1];
    // construct s
    ss := E1;
    //ss;
    ss := ss^c;
    //ss;
    ss := MatAlg!ss;
    ss := ExtractBlock(ss, 1, 1, 3, 3);
    //ss;
    ss := SU(3, q)! ss;
    ss := ss^shift1;
    ss := ss^(CB1^-1);
    wss := writeSLP(bbgens1, wbbgens1, r1, wr1, ss);
    wss := Evaluate(wss, wordJ1gens);
    wss := wss^(wc^-1);
    ws := wss;
   
    gens := [G.i: i in [1..Ngens (G)]];
    mygens := (gens)^(CB^-1);
    // mygens := (UserGenerators(G))^(CB^-1);
    s := Evaluate(wss, mygens);

    // construct t
    tt := E[3];
    tt := tt^c;
    tt := MatAlg!tt;
    tt := ExtractBlock(tt, 1, 1, 3, 3);
    tt := SU(3, q)! tt;
    tt := tt^shift1;
    tt := tt^(CB1^-1);
    wtt := writeSLP(bbgens1, wbbgens1, r1, wr1, tt);
    wtt := Evaluate(wtt, wordJ1gens);
    wtt := wtt^(wc^-1);
    wt := wtt;
    t := Evaluate(wtt, mygens);

    // construct delta 
    dd := E[4];
    dd := dd^c;
    dd := MatAlg!dd;
    dd := ExtractBlock(dd, 1, 1, 3, 3);
    dd := SU(3, q)! dd;
    dd := dd^shift1;
    dd := dd^(CB1^-1);
    
    wdd := writeSLP(bbgens1, wbbgens1, r1, wr1, dd);
    wdd := Evaluate(wdd, wordJ1gens);
    wdd := wdd^(wc^-1);
    wd := wdd;
    d := Evaluate(wdd, mygens);

    assert (d eq E[4]) and (t eq E[3]) and (s eq E[1]) and 
           (y eq E[7]) and (u eq E[2]) and (x eq E[6]);
    LGOWords := [ws, wu, wt, wd, wu, wx, wy];
//change form to standard magma form = [ 0 0 0 1 ]
//                                     [ 0 0 1 0 ] 
//                                     [ 0 1 0 0 ]
//                                     [ 1 0 0 0 ]

//form := MatrixAlgebra(GF(q^2), 4 ) ! [ 0,0,1,0,   0,0,0,1,  1,0,0,0,  0,1,0,0];
CF:= GL(4,q^2)![1,0,0,0,  0,0,1,0,   0,0,0,1,  0,1,0,0];
//CF := TransformForm( form , "unitary") ;
CB:= CF^-1 * CB;
E:=E^CF;



    //Setting up datastructure for G.
    rf := recformat<PetersGens, wPetersGens, CB, classicalform, 
                                Words, LGOImages, Generators>;
    data := rec<rf | PetersGens := Petersgens, wPetersGens := wT, 
       CB := CB, classicalform := B, Words := LGOWords, LGOImages := E, 
       Generators := E>;
    G`SU4DataStructure := data;

    return true;
end function;

classicalwriteSLP := function(q, x, CB , wE, E)
    f, w := ClassicalRewrite(SU(4, q), E, "SU", 4, q, x^(CB^-1));
    assert f;
    w := Evaluate(w , wE);
    return w;
end function;
 
// Constructively recognise a natural copy of SU4
RecogniseSU4White := function (G, q)

    if assigned(G`RecognitionMaps) then 
        maps := G`Recognitionmaps;
        return true, maps[1], maps[2], maps[3], maps[4];
    end if;

    limit := 5;
    _, p, k := IsPrimePower(q);
    i := 0;
    repeat
       flag := FindGens_SU4(G, p, k);
       i +:= 1;
    until (i eq limit) or flag;
    if not flag then
        return false, _, _, _, _;
    end if;
    rec := G`SU4DataStructure;
    wE := rec`Words;
    E := rec`LGOImages;
    CB := rec`CB;
    gen := Generic(G);
    gens := [G.i : i in [1..Ngens(G)]];
    W := WordGroup(G);

    //recognition maps
    phi := hom<gen -> GL(4, q^2) | x:-> x^(CB^-1)>;
    tau := hom<GL(4, q^2) -> gen | x:-> x^CB>;
    gamma := hom<gen -> W | x:-> classicalwriteSLP(q, x, CB, wE, E)>;
    delta := hom<W -> gen | x:-> Evaluate(x, gens)>;
    G`RecognitionMaps := <phi, tau, gamma, delta >;
    G`SU4DataStructure`Generators := E^CB;
    return true, phi, tau, gamma, delta;
end function;
