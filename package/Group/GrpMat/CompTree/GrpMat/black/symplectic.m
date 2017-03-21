freeze;

declare verbose myomega, 1;

import "white-prelims.m": ImageInLtilde, norm, 
                         trace, form, 
                          CommutatorSpace, IsPowerOfTwo, 
                          IsOrderMoreThanThree, IsMersenne, 
                          IsFermat, Isppdhash, 
                          MyChangeOfBasisMatrix, 
                          ElementHavingPrescribedTrace, 
                          ElementHavingPrescribedNorm, formRest, 
                          GetVector, GetFpBasisVectors;
import "bbsporadics.m": SporadicSU3;
import "bbprelims.m": IsHermitianForm, 
                      PGL2ActionOnTransvectionGroups, 
                      SL2NormalisingToralElement, 
                      MyCoordinates;
import "../../classical/recognition/black/odd/base-omega.m" : 
              MyRecogniseOmegaPlus6 , MyRecogniseOmegaMinus6;
import "../../recog/magma/centre.m" : EstimateCentre;

import "recognise-section.m" : RecogniseSection;
///////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////
// functions for even q
////////////////////////////////////////////////////////



//Construct a naturally embedded H = Omega+(6,q)

ConstructH_even := function(G, d, q, P)
    F := GF(q);
    _,p,k := IsPrimePower(q);
    limit1 := 100*d;
    limit2 := 10;
    limit3 := 100;
    i:=0;
    repeat
        i+:=1;
        f := false;
        t,wt := Random(P);
        ot := Order(t);
        f1 := Isppdhash(ot, p, k);
        f2 := Isppdhash(ot, p, k*(d-2));
        f := f1 and f2;
    until (i ge limit1) or f;
    if not f then return false,_,_,_,_; end if;
    n := (d - 2) div 2;
    a := t^(q^n + 1);
    wa := wt^(q^n + 1);
    oa := ot div (Gcd(ot,(q^n + 1)));
    sigma := t^(q-1);
    wsigma := wt^(q-1);
    osigma := ot div Gcd(ot, q-1);
    i:=0;
    repeat
        i+:=1;
        f := false;
        g, wg := Random(P);
        h, wh := Random(P);
        H := sub< G | a, a^g, a^h >;
        Hshouldbe := <"A", 3, q>;
        flag, type := LieType(H, p);
        if not flag then continue; end if;
        if not (type eq Hshouldbe) then continue; end if;
        f := true;
    until f or (i ge limit2);
    if not f then return false,_,_,_,_; end if;
    fH, aH, bH, cH, dH := RecogniseSection(H, "Omega+", 6, q);
    if not fH then return false,_,_,_,_; end if;
    wH := [wa, wa^wg, wa^wh];
    return true, H, wH, sigma, wsigma;
end function;

//Use H = Omega+(6,q) to construct a naturally embedded subgroup J = Sp(4,q).
FindLargeSubgroups_even := function(G, d, q)
     _,p,k := IsPrimePower(q);
    F := GF(q);
    P := RandomProcessWithWords(G);
    f, H, wH, sigma, wsigma := ConstructH_even(G, d, q, P);
    if not f then return false,_,_,_,_; end if;
    fH, aH, bH, cH, dH := ClassicalConstructiveRecognition(H, "Omega+", 6, q);
    //align image of H
    Q := StandardQuadraticForm(6, F);
    V := QuadraticSpace(Q);
    a := H.1;
    aa := a @ aH;
    coma := CommutatorSpace(F, [aa]);
    coma := sub< V | UserGenerators(coma)>;
    split := HyperbolicSplitting(coma)[1][1];
    e1 := split[1]; f1 := split[2];
    comaperp := OrthogonalComplement(V , coma);
    split := HyperbolicSplitting(comaperp);
    bas := &cat split[1];
    bas := [V!e1,V!f1] cat bas;
    CB := MyChangeOfBasisMatrix(V, bas);
    aH := map< Domain(aH) -> Codomain(aH) | x :-> ((x @ aH)^(CB^-1)) >;
    bH := map< Domain(bH) -> Codomain(bH) | x :-> ((x^CB) @ bH) >;
    maps := H`RecognitionMaps;
    maps[1] := aH;
    maps[2] := bH;
    H`RecognitionMaps := maps;

    EmbedOmega4 := function(s,q)
        F := GF(q);
        MA := MatrixAlgebra(F, 6);
        I := Identity(MA);
        ss := Matrix(s);
        I := InsertBlock(I, ss, 3,3);
        ss := GL(6,q)!I;
        return ss;
    end function;

    O4 := ClassicalStandardGenerators("Omega+", 4, q);
    O4 := [ s : s in O4 | s ne Identity(GL(4,q)) ];
    X := [];
    for i in [1..#O4] do
        x := O4[i];
        if not( x in X ) then
            X := X cat [x];
        end if;
    end for;
    O4 := X; 
    O4 := [EmbedOmega4(s, q) : s in O4];
    O4 := [ s @ bH : s in O4];
    wO4 := [s @ Function(cH) : s in O4];
    wO4 := Evaluate(wO4, wH);
    Jgens := O4 cat [sigma];
    wJ := wO4 cat [wsigma];
    J := sub<Generic(G) | Jgens>;
    flag, type := LieType(J, p);
    shouldbe := <"C", 2, q>;
    if not flag then return false,_,_,_,_; end if;
    if not (type eq shouldbe) then return false,_,_,_,_; end if;
    return true, J, wJ, H, wH;
end function;

AlignImageOfJ_even := function(G,J, H,q)
    limit1:=15;
    limit2 := 15;
    _, p, k := IsPrimePower(q);
    F := GF(q);
    fH,aH,bH,cH,dH := ClassicalConstructiveRecognition(H, "Omega+", 6, q);
    i := 0;
    repeat
        endflag := false;
        i+:=1;
        J := sub<Generic(J) | UserGenerators(J)>;
        if i le limit2 then
           fJ, aJ, bJ,cJ, dJ := RecogniseSection(J, "Sp", 4, q);
        else
	   fJ, aJ, bJ ,cJ ,dJ := ClassicalConstructiveRecognition(J, "Sp", 4, q);
        end if;
        JJ := sub< GL(4,q) | UserGenerators(J) @ aJ > ;
        o4 := sub< Generic(JJ) | [JJ.i : i in [1..Ngens(JJ)-1]]>;
        if not( IsIrreducible(o4)) then continue; end if;
        // modify maps so that JmeetH sits as a natural Omega+(4,q) in JJ
        form := ClassicalForms(o4)`quadraticForm;
        cf := TransformForm(form, "orthogonalplus");
        aJ := map< Domain(aJ) -> Codomain(aJ) | x :-> (x @ aJ)^cf>;
        bJ := map< Domain(bJ) -> Codomain(bJ) | x :-> (x^(cf^-1)) @ bJ >;
        Q := StandardQuadraticForm(4, F);
        V := QuadraticSpace(Q);
        e:= OmegaPlus(2,F);
        e:= e.1;
        MA := MatrixAlgebra(F,6);
        ee:= Identity(MA);
        ee[3,3] := e[1,1];
        ee[4,4] := e[2,2];
        eH:= ee;
        e:= eH @ bH;
        eJ := e @ aJ;
        centre:= Eigenspace(eJ, 1) ;
        centre := sub< V | UserGenerators(centre) >;
        m := WittIndex(centre); 
        // if wittindex ne 1 then we have a bad J isomorphism.
        endflag := m eq 1;
    until (i eq limit1) or endflag;
    if not endflag then error "Internal_RecogniseSp6: Failure"; end if;

    values := Eigenvalues(eJ);
    values := [v : v in values | v[2] eq 1];
    e2 := Eigenspace(eJ, values[1][1]);
    f2 := Eigenspace(eJ, values[2][1]);
    e2 := V!(e2.1); f2 := V!(f2.1);
    alpha := InnerProduct(e2, f2);
    e2 := alpha^-1*e2;
    e:= OmegaPlus(2,F);
    e:= e.1;
    ee:= Identity(MA);
    ee[5,5] := e[1,1];
    ee[6,6] := e[2,2];
    eH:= ee;
    e:= eH @ bH;
    eJ := e @ aJ;
    centre:= Eigenspace(eJ, 1) ;
    centre := sub< V | UserGenerators(centre) >;
    m := WittIndex(centre);
    if m ne 1 then return false,_,_; end if;
    values := Eigenvalues(eJ);
    values := [v : v in values | v[2] eq 1];
    e3 := Eigenspace(eJ, values[1][1]);
    f3 := Eigenspace(eJ, values[2][1]);
    e3 := V!(e3.1); f3 := V!(f3.1);
    alpha := InnerProduct(e3, f3);
    e3 := alpha^-1*e3;
    bas := [e2,f2, e3, f3 ];
    cb :=MyChangeOfBasisMatrix(V, bas);
    aJ := map< Domain(aJ) -> Codomain(aJ) | x :-> (x @ aJ)^(cb^-1) >;
    bJ := map< Domain(bJ) -> Codomain(bJ) | x :-> ((x^cb) @ bJ ) >;
/*
    maps := J`RecognitionMaps;
    maps[1] := aJ;
    maps[2] := bJ;
*/
    J`RecognitionMaps := <aJ, bJ, cJ, dJ>;
      //maps;
    return true, J, H;
end function;

ConstructLGOGens_even := function(G,J,wJ, H, wH, q)
    F := GF(q);
    f, aJ,bJ,cJ,dJ := ClassicalConstructiveRecognition(J, "Sp", 4, q);
    f,aH, bH, cH, dH := ClassicalConstructiveRecognition(H, "Omega+", 6, q);
    sJ := ClassicalStandardGenerators("Sp", 4, q);
    SJ := sJ @ bJ;
    wSJ := [s @ Function(cJ) : s in SJ];
    wSJ := Evaluate(wSJ, wJ);
    E := SJ;
    W := wSJ;
    //must change H-maps so that SJ[5] is in line;
    B := StandardQuadraticForm(6, F);
    V := QuadraticSpace(B);
    x := SJ[5];
    xx := x @ aH;
    alpha := xx[3,5];
    bas := [V.1, V.2, V.3, V.4, alpha*(V.5), alpha^-1*(V.6)];
    cb := MyChangeOfBasisMatrix(V, bas);
    aH := map< Domain(aH) -> Codomain(aH) | x :-> ((x @ aH)^(cb^-1))>;
    bH := map< Domain(bH) -> Codomain(bH) | x :-> ((x^cb) @ bH) >;
    maps := H`RecognitionMaps;
    maps[1] := aH;
    maps[2] := bH;
    H`RecognitionMaps := maps;
    //now H should be sufficiently aligned. 
    sH := ClassicalStandardGenerators("Omega+", 6, q);
    s := sH[8] @ bH;
    ws := s @ Function(cH);
    ws := Evaluate(ws , wH);
    E[2] := s;
    W[2] := ws;
    s := SJ[6]^(s);
    ws := wSJ[6]^ws; 
    E[6] := s;
    W[6] := ws;
    w,r := ClassicalStandardPresentation("Sp",6,q);
    n := #Set(Evaluate(r, E));
    if n ne 1 then return false,_,_; end if;
    return true, E, W;
end function;



///////////////////////////////////////////////////////////////////
// functions to handle q odd
///////////////////////////////////////////////////////////////////

ConstructJ_odd := function(G, d, q, P)
    F := GF(q);
    _,p,k := IsPrimePower(q);
    limit1 := 100*d;
    limit2 := 10;

    i:=0;
    repeat
        i+:=1;
        f := false;
        t,wt := Random(P);
        ot := Order(t);
        f1 := Isppdhash(ot, p, k);
        f2 := Isppdhash(ot, p, k*(d-2));
        f := f1 and f2;
    until (i ge limit1) or f;
    if not f then return false,_,_,_,_; end if;
    n := (d - 2) div 2;
    a := t^(q^n + 1);
    wa := wt^(q^n + 1);
    oa := ot div (Gcd(ot,(q^n + 1)));
    sigma := t^(q-1);
    wsigma := wt^(q-1);
    osigma := ot div Gcd(ot, q-1);
    i:=0;
    repeat
        i+:=1;
        f := false;
        g, wg := Random(P);
        J := sub< G | a, a^g>;
        flag, type := LieType(J, p);
        shouldbe:= <"C", 2, q>;
        if not flag then continue; end if;
        if not (type eq shouldbe) then continue; end if;
        f,a,b,c,d :=  RecogniseSection(J, "Sp", 4, q);
        if not f then continue; end if;
    until f or (i ge limit2);
    if not f then return false,_,_,_,_; end if;
    wJ := [wa, wa^wg];
    return true, J, wJ, sigma, wsigma;
end function;

FindLargeSubgroups_odd := function(G, d, q);
    _,p,k := IsPrimePower(q);
    F := GF(q);
    P := RandomProcessWithWords(G);
    f, J, wJ, sigma, wsigma  := ConstructJ_odd(G, d, q, P);
    if not f then return false,_,_,_,_,_,_; end if;
    fJ, aJ, bJ, cJ, dJ := 
              ClassicalConstructiveRecognition(J, "Sp", 4, q );
    if not fJ then return false,_,_,_,_,_,_; end if;
    B := StandardAlternatingForm(4, q);
    V := SymplecticSpace(B);
    a:= J.1;
    aa := a @ aJ;
    wa := wJ[1];
    values:= Eigenvalues(aa);
    values := [x : x in values | x[2] eq 1];
    if #values ne 2 then return false,_,_,_,_,_,_; end if;
    spaces := [Eigenspace(aa, x[1]) : x in values];
    spaces := [s.1 : s in spaces] ;
    alpha := InnerProduct(V!spaces[1], V!spaces[2]);
    spaces[1] := alpha^-1*spaces[1];
    V2 := sub<V | spaces>;
    V2perp := OrthogonalComplement(V,V2);
    E := HyperbolicSplitting(V2perp)[1][1];
    basis := [V2.1, V2.2, E[1], E[2]];
    CB := MyChangeOfBasisMatrix(V, basis);
    aJ := map< Domain(aJ) -> Codomain(aJ) | x :-> (x @ aJ)^(CB^-1) >;
    bJ := map< Domain(bJ) -> Codomain(bJ) | x :-> ((x^(CB)) @ (bJ)) >;
    maps := J`RecognitionMaps;
    maps[1] := aJ;
    maps[2] := bJ;
    J`RecognitionMaps := maps;

    //constructing L
    GG := GL(4, q);
    sp2gens := UserGenerators(Sp(2,q));
 
    EmbedSp2InSp4 := function(x, q);
        MA := MatrixAlgebra(GF(q), 4);
        I := Identity(MA);
        I[3,3] := x[1,1]; I[3,4] := x[1,2]; I[4,3] := x[2,1]; I[4,4] := x[2,2];
        xx:= GL(4,q)!I;
        return xx;
    end function;
    ZZ := [EmbedSp2InSp4(x,q) : x in sp2gens];
    Z := [(x @ Function(bJ)) : x in ZZ];
    wZ := [(x @ Function(cJ)) : x in Z];
    wZ := Evaluate(wZ, wJ);
    Lgens := Z cat [sigma];
    wL := wZ cat [wsigma];
    L := sub< Generic(G) | Lgens >;
    flag, type := LieType(L, p);
    if not flag then return false,_,_,_,_,_,_; end if;
    shouldbe:= <"C", (d-2) div 2, q>;
    if (type ne shouldbe) then "false1"; return false,_,_,_,_,_,_; end if;
    return true, J, wJ, L, wL, sigma, wsigma;
end function;

AlignImageOfL_odd := function(G, q, d, J,  L)
    limit1 := 15;
    F := GF(q);
    B := StandardAlternatingForm(d-2, F);
    V := SymplecticSpace(B);
    fJ, aJ, bJ, cJ, dJ := ClassicalConstructiveRecognition(J, "Sp", 4, q);
    i:=0;
    repeat
        endflag := false;
        i+:=1;
        L := sub<Generic(L) | UserGenerators(L) >;
        fL, aL, bL, cL, dL := RecogniseSection(L, "Sp", 4,q);
//maps := <aL, bL, cL, dL>;
        a := L.1;
        aa := a @ Function(aL);
        values:= Eigenvalues(aa);
        values := [x : x in values | x[2] eq 1];
        if #values ne 2 then "false1"; return false,_; end if;
        spaces := [Eigenspace(aa, x[1]) : x in values];
        spaces := [s.1 : s in spaces] ;
        alpha := DotProduct(V!spaces[1], V!spaces[2]);
        spaces[1] := alpha^-1*spaces[1];
        V2 := sub<V | spaces>;
        V2perp := OrthogonalComplement(V,V2);
        E := HyperbolicSplitting(V2perp)[1][1];
        basis := DotProduct(E[1],E[2]) eq 1 select [V2.1, V2.2, E[1], E[2]] 
                            else [V2.1, V2.2, E[2], E[1]];
        CB := MyChangeOfBasisMatrix(V, basis);
        //aligned?
        xx := (L.2 @ aL)^(CB^-1);
        if xx[1,1] eq 0 then
    	    basis := DotProduct(E[1],E[2]) eq 1 select [V2.2, V2.1, E[2], E[1]] 
                            else [V2.1, V2.2, E[1], E[2]];
            CB := MyChangeOfBasisMatrix(V, basis);
        end if;
        aL := map< Domain(aL) -> Codomain(aL) | x :-> (( x @ aL )^(CB^-1)) >;
        bL := map< Domain(bL) -> Codomain(bL) | x :-> ((x^CB) @ bL) >;
        xx := L.2 @ aL;
        b := xx[1,2];
        endflag := true;
    until endflag or i ge limit1;
    if not endflag then "false2"; return false, _; end if;
    X := GL(d-2,q)![b,0,0,0, 0,1,0,0, 0,0,b,0, 0,0,0,1];
    aL := map< Domain(aL) -> Codomain(aL) | x :-> ((x @ aL)^X) >;
    bL := map< Domain(bL) -> Codomain(bL) | x :-> ((x^(X^-1)) @ bL) >;
//    maps := L`RecognitionMaps;
//    maps[1] := aL;
//    maps[2] := bL;
L`RecognitionMaps := < aL, bL, cL, dL>;
      //maps;
    return true, L;
end function;

ConstructLGOGens_odd := function(G,d,q,J,wJ,L,wL);
    _, p, k := IsPrimePower(q);
    f,aJ,bJ,cJ,dJ := ClassicalConstructiveRecognition(J, "Sp", 4, q);
    f,aL,bL,cL,dL := ClassicalConstructiveRecognition(L, "Sp", d-2, q);
    sJ := ClassicalStandardGenerators("Sp", 4, q);
    sL := ClassicalStandardGenerators("Sp", d-2, q);
    SJ := sJ @ bJ;
    wSJ := [s @ Function(cJ) : s in SJ];
    wSJ := Evaluate(wSJ, wJ);
    SL := sL @ bL;
    wSL := [ s @ Function(cL) : s in SL];
    wSL := Evaluate(wSL, wL);
    cyc := SL[2]*SJ[2];
    wcyc := wSL[2]*wSJ[2];
    E := SJ[1..6];
    E[2] := cyc;
    cyc  := SJ[2]*SL[2];
//E[6] := SJ[6]^cyc;
    E[6] := SL[6];
    wE := wSJ[1..6];
//    wE[2] := wcyc;
    wE[6] := wSL[6];
//wE[6] := wSJ[6]^wcyc;

//check
/*
"maps aligned?";
"L.1 in J"; L.1 @ aJ;
"L.1 in L"; L.1 @ aL;
"L.2 in J"; L.2 @ aJ;
"L.2 in L"; L.2 @ aL;
"do maps satisfy presentation?";
Q,r := ClassicalStandardPresentation("Sp",4,q);
"J?", #Set(Evaluate(r, SJ));
"L?", #Set(Evaluate(r, SL));

*/
    w,r := ClassicalStandardPresentation("Sp", d, q);
    n := #Set(Evaluate(r, E));
    f := n eq 1;
    if not f then "false3"; return false, _, _; end if;
    return f, E, wE;
end function;

intrinsic Internal_RecogniseSp6( G :: Grp, q :: RngIntElt )
-> SeqEnum, SeqEnum
{Kenneth code for Sp6}
    require q gt 3: "Field size must be at least 4";
    if q eq 5 then error "Code does not apply to q = 5"; end if;

    if assigned G`UserGenerators then 
       hold := G`UserGenerators; delete G`UserGenerators; 
    end if;
    limit1 := 10;
    d := 6;
    if IsEven(q) then 
        i := 0;
        repeat
            i+:=1;
            f,J,wJ,H,wH := FindLargeSubgroups_even(G,d,q);
        until f or i ge limit1;
        if not f then return false,_,_; end if;
        i:=0;
        repeat
            i+:=1;
            f,JJ,HH := AlignImageOfJ_even(G,J,H,q);
        until f or i ge limit1;
        if not f then return false,_,_; end if;
        J := JJ; H := HH;
        i:=0;
        repeat
            i+:=1;
            f, E, W := ConstructLGOGens_even(G,J,wJ,H,wH,q);
        until f or i ge limit1; 
    else 
        i := 0;
        repeat
            i+:=1;
            f := false;
            f1,J,wJ,L, wL, sigma, wsigma := FindLargeSubgroups_odd(G,d,q);
            if not f1 then continue; end if;
            f2,LL := AlignImageOfL_odd(G,q,d,J,L);
            if not f2 then continue; end if;
            L := LL;
            f3, E, W := ConstructLGOGens_odd(G,d,q,J,wJ,L,wL);
            f := f1 and f2 and f3;
        until f or i ge limit1;
    end if;
    if assigned hold then G`UserGenerators := hold; end if;
    if not f then return false,_,_; end if;
    return f, E, W;
end intrinsic;
