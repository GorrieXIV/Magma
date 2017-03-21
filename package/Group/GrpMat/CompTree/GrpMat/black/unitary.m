freeze;

declare verbose myomega, 1;

import "white-prelims.m": ImageInLtilde, norm, 
                          trace, form,
                          MyChangeOfBasisMatrix, 
                          CommutatorSpace, IsPowerOfTwo, 
                          IsOrderMoreThanThree, IsMersenne, 
                          IsFermat, Isppdhash, 
                          ElementHavingPrescribedTrace, 
                          ElementHavingPrescribedNorm, formRest, 
                          GetVector, GetFpBasisVectors;
import "bbsporadics.m": SporadicSU3;
import "bbprelims.m": IsHermitianForm, 
                      PGL2ActionOnTransvectionGroups, 
                      SL2NormalisingToralElement, 
                      MyCoordinates;
import "../../classical/recognition/black/odd/base-omega.m" : MyRecogniseOmegaPlus6 , MyRecogniseOmegaMinus6;

import "../../recog/magma/centre.m" : EstimateCentre;

import "recognise-section.m" : RecogniseSection;


ConstructJ := function(G,d,q,F,P )
    n := IsEven(d) select d-3 else d-2;
    limit1 := 32*n;   //finding t
    limit2 := 100;  // using t to construct J \simeq SU(4,q);

    _,p,k := IsPrimePower(q);
    i := 0;
    repeat
        endflag := false;
	i+:=1;
        t, wt := Random(P);
        ot := Order(t);
        f := Isppdhash(ot, p, 2*n*k);
        if not f then continue; end if;
        a:= t^(q^n + 1);
        wa := wt^(q^n + 1);
        oa := ot div (Gcd(ot, q^n + 1 ));
        f1 := Isppdhash(oa, p, k);
        f2 := IsEven(k) select Isppdhash(oa, p, k div 2) else true; 
        endflag := f1 and f2;
    until endflag or (i eq limit1);
    if i eq limit1 then 
        return false,_,_,_,_;
    end if;
    sigma := t^(q^2 - 1);
    wsigma := wt^(q^2 - 1);
    i:=0;
    repeat
        endflag := false;
        i+:=1;
        g, wg := Random(P);
        Jgens := [a, a^g];
        wJgens := [wa, wa^wg];
        J := sub<Generic(G) | Jgens>;
        f, type := LieType(J, p);
        if not f then continue; end if;
        if (type ne <"2A", 3, q>) then continue; end if;
        f,aJ,bJ,cJ,dJ := 
	  RecogniseSection(J, "SU", 4, q);
        endflag := f;      
    until endflag or (i eq limit2);
    if i eq limit2 then
        return false, _, _,_,_;
    else 
        return true, J, wJgens, sigma, wsigma;
    end if;
end function;

FindLargeSubgroups := function(G, d, q)
    _,p,k := IsPrimePower(q);
    F := GF(q);
    P := RandomProcessWithWords(G);
    f, J, wJ, sigma, wsigma  := ConstructJ( G, d, q, F, P);
    if not f then return false,_,_,_,_,_; end if;

    fJ, aJ, bJ, cJ, dJ := 
         ClassicalConstructiveRecognition(J, "SU", 4, q );
    if not fJ then return false,_,_,_,_,_; end if;
    B, phi := StandardHermitianForm(4, q);
    V := UnitarySpace(B, phi);
    a:= J.1;
    aa := a @ aJ;
    wa := wJ[1];
    //line up a so a acts on its 1-dim e spaces.
    values:= Eigenvalues(aa);
    values := [x : x in values | x[2] eq 1];
    if #values ne 2 then return false,_,_,_,_,_; end if;
    spaces := [Eigenspace(aa, x[1]) : x in values];
    spaces := [s.1 : s in spaces] ;
    alpha := DotProduct(V!spaces[1], V!spaces[2]);
    spaces[1] := alpha^-1*spaces[1];
    V2 := sub<V | spaces>;
    V2perp := OrthogonalComplement(V,V2);
    E := HyperbolicSplitting(V2perp)[1][1];
    basis := [spaces[1], E[1], E[2], spaces[2]];
    basis := [V ! b : b in basis];
    CB := MyChangeOfBasisMatrix(V, basis);
    aJ := map< Domain(aJ) -> Codomain(aJ) | x :-> (x @ aJ)^(CB^-1) >;
    bJ := map< Domain(bJ) -> Codomain(bJ) | x :-> ((x^(CB)) @ (bJ)) >;
    maps := J`RecognitionMaps;
    maps[1] := aJ;
    maps[2] := bJ;
    J`RecognitionMaps := maps;
    //constructing L
    GG := GL(4, q^2);
    F := GF(q^2);
    delta := ElementHavingPrescribedTrace(F, 0);
    F0 := sub<F | (F.1)^(q+1) > ;
    zeta := PrimitiveElement(F0);
    deltabar := Frobenius(delta, F0);
    r := GG![1,0,0,0, 0,0,deltabar,0, 0,delta^-1,0,0, 0,0,0,1];
    tList := [(GG![1,0,0,0, 0,1,0,0, 0,zeta^(i-1)*delta,1,0, 0,0,0,1]) : 
        i in [1..k]];
    ttList := tList @ bJ;
    wttList := [tt @ Function(cJ) : tt in ttList];
    wttList := Evaluate(wttList, wJ);
    rr := r @ bJ;
    wrr := rr @ Function(cJ);
    wrr := Evaluate(wrr, wJ);
    Z := ttList cat [tt^rr : tt in ttList];
    wZ := wttList cat [wtt^wrr : wtt in wttList];
    Lgens := Z cat [sigma];
    wLgens := wZ cat [wsigma];
    //cull Lgens for repetition
    LLgens := [];
    wL := [];
    for i in [1..#Lgens] do
        f := not(IsIdentity(Lgens[i]));
        if f and not(Lgens[i] in LLgens) then 
            LLgens := LLgens cat [Lgens[i]];
             wL := wL cat [wLgens[i]];
        end if;
    end for;
    Lgens := LLgens;
    L := sub<Generic(G) | Lgens>;
    flag, type := LieType(L, p);
    if not flag then return false,_,_,_,_,_; end if;
    if d eq 5 then 
        if (type ne <"2A", 2, q>) then return false,_,_,_,_,_; end if;
    elif d eq 7 then 
        if (type ne <"2A", 4, q>) then return false,_,_,_,_,_; end if;
    end if;
    return true, type, J, wJ, L, wL;
end function;

AlignImageOfL := function(G,q,d,type,J,wJ,L,wL)
    _,p,k := IsPrimePower(q);
    F := GF(q^2);
    F0 := sub<F | (F.1)^(q+1) > ;
    f, aJ,bJ,cJ,dJ := ClassicalConstructiveRecognition(J, "SU", 4,q);
    f,aL,bL,cL,dL := 
      RecogniseSection(L, "SU", d-2, q);
    if not f then return false,_; end if;
    Lgens := [L.i : i in [1..Ngens(L)]];
    L1 := L.1 @ aL;
    L2 := (Lgens[k+1]) @ aL;
    B, phi := StandardHermitianForm(d -2 , q);
    V := UnitarySpace(B, phi);
    v := Eigenspace(L1,1) meet Eigenspace(L2,1);
    v:= sub<V | UserGenerators(v)>;
    vperp := OrthogonalComplement(V, v);
    e := Eigenspace(L1,1);
    e := sub< V | UserGenerators(e)>;
    e := e meet vperp;
    e := e.1;
    f := Eigenspace(L2,1);
    f := sub< V | UserGenerators(f)>;
    f := f meet vperp;
    f := f.1;
    alpha := DotProduct(e,f);
    e := alpha^-1*e;
    if d eq 5 then
        vv := v.1;
        alpha := DotProduct(vv, vv);
        x := ElementHavingPrescribedNorm(alpha^-1, F0, F, q);
        vv := x*vv;
        basis := [e,vv,f];
    elif d eq 7 then 
        split := HyperbolicSplitting(v);
        E2 := split[1][1];
        e2 := E2[1];
        f2 := E2[2];
        vv := split[2][1];
        alpha := DotProduct(vv,vv);
        x:=ElementHavingPrescribedNorm(alpha^-1, F0, F, q);
        vv := x*vv;
        basis := [e, e2, vv, f2, f];
    end if;
    CB := MyChangeOfBasisMatrix(V,basis);

    EmbedSU2 := function(g)
        g:= Matrix(g);
        F := BaseRing(g);
        G := GL(4,F);
        I := Identity(G);
        I := Matrix(I);
        I[2,2] := g[1,1];
        I[2,3] := g[1,2];
        I[3,2] := g[2,1];
        I[3,3] := g[2,2];
        gg := G!I;
        return gg;
    end function;
    //out by field?
    b:= SU(2,q).1;
    b := EmbedSU2(b);
    x1 := b;
    b := x1 @ bJ;
    x2 := (b @ aL)^(CB^-1);
    f := exists(n){n : n in [1..2*k] | (x2[1,1])^(p^n) eq x1[2,2]};
    Ca:= Domain(aL);
    Db := Domain(bL);
    aL := map<Domain(aL) -> Codomain(aL) |
		x :-> (FrobeniusImage((x @ Function(aL))^(CB^-1), n)) >;
    bL := map< Domain(bL) -> Codomain(bL) |
		 x :-> (Db!(CB^-1*FrobeniusImage(x, 2*k - n)*CB)) @ Function(bL) >;

     //out by diagonal?
    g:= SU(2,q).2;
    g := EmbedSU2(g);
    a := g @ bJ;
    gg := (a @ aL);
    x := gg[1,d-2]*(g[2,3])^-1;
    beta := ElementHavingPrescribedNorm(x, GF(q), GF(q^2), q);
    alpha := beta*x^-1;
    diag := Identity(Parent(Matrix(gg)));
                 diag[1,1] := alpha ;
                 diag[d-2, d-2] := beta;
    diag := GL(d-2, q^2)!diag;
    aL := map<Domain(aL) -> Codomain(aL) |
        x :-> diag*(x @ Function(aL))*diag^-1 >;
    bL := map< Domain(bL) -> Codomain(bL) |
        x :-> ((diag^-1*x*(diag)) @ Function(bL)) >;
    maps := L`RecognitionMaps;
    maps[1] := aL;
    maps[2] := bL;
    L`RecognitionMaps := maps;

    //are we aligned?
    b := SU(2,q).1;
    b := EmbedSU2(b);
    x1 := b;
    b := x1 @ bJ;
    x2 := b @ aL;
    f1:= (x1[2][2] eq x2[1][1]);
    f2:= x1[2][3] eq x2[1][d-2];
    f3:= x1[3][2] eq x2[d-2][1];
    f4:= x1[3][3] eq x2[d-2][d-2];
    ff := f1 and f2 and f3 and f4;

    x1 := a @ aJ;
    x2 := a @ aL;
    f := d eq 5;
    f1:= (x1[2][2] eq x2[1][1]);
    f2:= x1[2][3] eq x2[1][d-2];
    f3:= x1[3][2] eq x2[d-2][1];
    f4:= x1[3][3] eq x2[d-2][d-2];
    f := f1 and f2 and f3 and f4;
    if not ff and f then return false,_; end if;
    return true, L;
end function;

ConstructLGOGens := function(G,d,q,J,wJ,L, wL);
    _, p, k := IsPrimePower(q);
    f,aJ,bJ,cJ,dJ := ClassicalConstructiveRecognition(J, "SU", 4, q);
    f,aL,bL,cL,dL := ClassicalConstructiveRecognition(L, "SU", d-2, q);
    
    EmbedStandardGeneratorsInJ := function(S)
        if Type(S) ne SeqEnum then
            S := [S];
        end if;
        SS := [];
        F := BaseRing(S[1]);
        q:= #F;
        for s in S do
            ss := Matrix(s);
            ss := ExtractBlock(ss,1,1,4,4);
            CB := GL(4,q)!
                  [1,0,0,0,
                   0,0,0,1,
                   0,1,0,0,
                   0,0,1,0];
            ss:= GL(4,q)!ss;
            ss := ss^(CB);
            SS := SS cat [ss];
        end for;
        return SS;
    end function;

    EmbedStandardGeneratorsInL := function(S)
        if Type(S) ne SeqEnum then
            S := [S];
        end if;
        d := Degree(S[1]);
        k  := d-2;
        SS := [];
        F := BaseRing(S[1]);
        q := #F;
        for s in S do
            ss := Matrix(s);
            ss := ExtractBlock(ss,3,3,k,k);
            if k eq 3 then 
                CB := GL(k,q)!
                        [1,0,0,
                         0,0,1,
                         0,1,0];
            elif k eq 5 then
                 CB := GL(k,q)!
                         [1,0,0,0,0,  
                          0,0,0,0,1,  
                          0,1,0,0,0,  
                          0,0,0,1,0,  
                          0,0,1,0,0];
            end if;
            ss := GL(k,q)!ss;
            ss := ss^(CB);
            SS := SS cat [ss];
        end for ;
        return SS;
    end function;

    S := ClassicalStandardGenerators("SU",d, q);
    SinJ := S[1..5];
    SinJ[2] := (d eq 7) select Identity(Parent(S[1])) else SinJ[2];
    SinJ := EmbedStandardGeneratorsInJ(SinJ);
    SinJ := SinJ @ bJ;
    wSinJ := [gen @ Function(cJ) : gen in SinJ];
    wSinJ := Evaluate(wSinJ, wJ);
    
    SinL := S[6..7];
    SinL := EmbedStandardGeneratorsInL(SinL);

    SinL := SinL @ bL;
    wSinL := [gen @ Function(cL) : gen in SinL];
    wSinL := Evaluate(wSinL, wL);
    SS := SinJ cat SinL;
    wSS := wSinJ cat wSinL;
    if d eq 7 then 
        s := GL(4,q^2)! [0,1,0,0, 1,0,0,0, 0,0,0,1, 0,0,1,0];
        ss := s @ bJ;
        wss := ss @ Function(cJ);
        wss := Evaluate(wss, wJ);
        t := GL(5,q^2)![0,1,0,0,0, 1,0,0,0,0, 0,0,1,0,0, 0,0,0,0,1, 0,0,0,1,0];
        tt:= t @ bL;
        wtt := tt @ Function(cL);
        wtt := Evaluate(wtt, wL);
        SS[2] := tt*ss;
        wSS[2] := wtt*wss;
    end if;
    W , R := ClassicalStandardPresentation("SU", d, q);
    set := Set(Evaluate(R,SS));
    assert #set eq 1;
    assert Evaluate(wSS, [G.i : i in [1..Ngens(G)]]) eq SS;
    return true, SS, wSS;
end function;

intrinsic Internal_RecogniseSU5( G :: Grp, q :: RngIntElt )
-> SeqEnum, SeqEnum
{Kenneth code for SU5}
    require q gt 3: "Field size must be at least 4";
    if assigned G`UserGenerators then 
       hold := G`UserGenerators; delete G`UserGenerators; 
    end if;
    limit1 := 10;
    limit2 := 10;
    i:=0;
    d := 5;
    repeat 
        f,type, J, wJ, L, wL := FindLargeSubgroups(G, d, q);
        if not f then continue; end if;
        j:= 0;
        repeat 
            j+:=1;
            f, LL := AlignImageOfL(G,q,d,type,J,wJ,L,wL);
            L := assigned(LL) select LL else L;
        until f or (j ge limit2);
        f,e,w := ConstructLGOGens(G,d,q,J,wJ,L,wL);        
        i+:=1;
    until i ge limit1 or f;
    if assigned hold then G`UserGenerators := hold; end if;
    if not f then return false,_,_; end if;
    return f,e,w;
end intrinsic;

intrinsic Internal_RecogniseSU7( G :: Grp, q :: RngIntElt )
-> SeqEnum, SeqEnum
{Kenneth code for SU7}
    require q gt 3: "Field size must be at least 4";
    if assigned G`UserGenerators then 
       hold := G`UserGenerators; delete G`UserGenerators; 
    end if;

    limit1 := 10;
    limit2 := 10;
    i:=0;
    d := 7;
    repeat
        f,type, J, wJ, L, wL := FindLargeSubgroups(G, d, q);
        if not f then continue; end if;
        j:= 0;
        repeat
    	    j+:=1;
            f, LL := AlignImageOfL(G,q,d,type,J,wJ,L,wL);
            L := assigned(LL) select LL else L;
        until f or (j ge limit2);
        f,e,w := ConstructLGOGens(G,d,q,J,wJ,L,wL);
        i+:=1;
    until i ge limit1 or f;
    if assigned hold then G`UserGenerators := hold; end if;
    if not f then return false,_,_; end if;
    return f,e,w;
end intrinsic;
