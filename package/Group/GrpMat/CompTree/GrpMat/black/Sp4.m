freeze;

import "bbprelims.m": 
    SL2NormalisingToralElement,
    IsSL2xSL2, 
    PreservesBilinearForm;

import "../../classical/recognition/black/odd/base-omega.m": 
    FactorizeSL2xSL2;

import "bbsporadics.m": SporadicSp4;

import "recognise_su3.m" : 
    SmallestFaithful, 
    MatrixBlocks, 
    ConvertType;

Sp4_EVEN_CONSTRUCT_SL2xSL2 := function (G, proc, q, limit)
    count := 0;
    ord := q^2 - 1;
    found := false;
    while (count lt limit) and (not found) do
        count +:= 1;
        g, w := Random (proc);
        o := Order (g);
        if (o eq ord) then
      	    found := true;
        end if;
    end while;
    if (not found) then
        return false, _, _;
    end if;
    a := g^(q-1);
    wa := w^(q-1);
    found := false;
    count := 0;
    while (count lt limit) and (not found) do
        count +:= 1;
        g, w := Random (proc);
        K := sub < Generic (G) | [a, a^g] >;
        found := IsSL2xSL2 (K, q);
    end while;
    if (not found) then
        return false, _, _;
    end if;
    return true, K, [wa, wa^w];
end function;


Sp4_ODD_CONSTRUCT_SL2xSL2 := function (G, proc, q, limit)
    i:=0;
    repeat
        i+:=1; 
        endflag := false;
        t,wt := Random(proc);
        ot := Order(t);
        f := IsEven(ot);
        if not f then continue; end if;
        inv := t^(ot div 2);
        winv := wt^(ot div 2);
        InvCommutes := [(inv, G.i) eq Identity(G) : i in [1..Ngens(G)]];
        f := &and InvCommutes;
        endflag := not f; 
    until (i eq limit) or endflag;
    if not endflag then return false, _, _; end if;
    K0, wK0 := CentraliserOfInvolution(G, inv, winv);
    if q eq 3 then 
        return true, K0, wK0;
    end if;
    K, wK:= DerivedGroupMonteCarlo(K0);
    wK := Evaluate(wK, wK0);
    return true, K, wK;
end function;

RecogniseSL2Section := function(G,q)
    if Type(G) ne GrpMat then 
        f,a,b,c,d := RecogniseSL2(G,q);
        if f then return f,a,b,c,d, G, 1; else return f, _,_,_,_,G, 1;end if;
    end if;
    f, GG, secnum, sections := SmallestFaithful(G, <"A", 1, q>);
    GG := f select GG else G;
    ff,aa,bb,cc,dd := //MyClassicalConstructiveRecognition(GG, "SL", 2, q);
     RecogniseSL2(GG,q); 
    if not f then
        return ff,aa,bb,cc,dd, GG, 1;
    end if;
    mb := map< Generic(G) -> Generic(GG) | x :-> MatrixBlocks(G, x)[secnum]>;
    a := map< Generic(G) -> Codomain(aa) | x :->
      ((MatrixBlocks(G, x)[secnum]) @ Function(aa)) >;
    b := map< Domain(bb) -> Generic(G) | x :->
      Evaluate((x @ Function(bb)) @ Function(cc), [G.i : i in [1..Ngens(G)]])>;
    c := map< Generic(G) -> Codomain(cc) | x :->
		(((x @ mb)) @ Function(cc))>;
    d := map< Domain(dd) -> Generic(G) | w :->
      Evaluate(w, [G.i : i in [1..Ngens(G)]]) >;
    maps := <a,b,c,d>;
    G`RecognitionMaps := maps;
    return true, a, b, c, d, GG, secnum ;
end function;

FindLGOGens := function(G,q)
    _,p,e := IsPrimePower(q);
    F := GF (q);
    mu := PrimitiveElement (F);
    proc := RandomProcessWithWords (G);
    
    /////////////////////////////////////////////
    // First find a subgroup <K> isomorphic to //
    // SL(2,q) x SL(2,q) and a corresponding   //
    // factorisation: See Section 4.1.         //
    /////////////////////////////////////////////

    limit1 := 50 * e;
    limit2 := 1; 
    if IsOdd(q) then 
        flag, K, wK := Sp4_ODD_CONSTRUCT_SL2xSL2 (G, proc, q, limit1);
    else 
        flag, K, wK := Sp4_EVEN_CONSTRUCT_SL2xSL2(G, proc, q, limit1);
    end if;
    if not flag then // "Sp4:Failure 1"; 
       return false, _, _; end if;
    i:=0;
    repeat
        i+:=1;
        flag0, L1, wL1, L2, wL2 := FactorizeSL2xSL2(K, q: VerifySL2 := false);
    until (i eq limit2) or flag0;
    if (flag0) then
        flag1, phi1, tau1, gamma1, delta1, LL1, secnum := 
            RecogniseSL2Section(L1, q);
        if (flag1) then
            flag2, phi2, tau2, gamma2, delta2 := 
     	      RecogniseSL2Section(L2, q);
            if (flag2) then
                flag := true;
            else 
	      // "L2 not right";
	      return false, _,_;
            end if;
	else 
	    // "L1 not right";
            return false, _,_;
        end if;
    else 
         // "Sp4:Failure 2";
         return false, _,_;
    end if;
    wL1 := [ Evaluate (x, wK) : x in wL1 ];
    wL2 := [ Evaluate (x, wK) : x in wL2 ];


    //////////////////////////////////////////////////////////
    // construct short root element in <Q>, the unipotent   //
    // radical of the normalizer in <G> of a transvection   //
    // group <S1>: See Section 4.2.                         //
    //////////////////////////////////////////////////////////
     
    sM := GL (2, F)![1,0,1,1]; 
    tM := GL (2, F)![1,1,0,1];
    hM := GL (2, F)![ mu , 0 , 0 , 1/mu ]; 
    s1 := sM @ (tau1);   // a transvection in L
    t1 := tM @ (tau1);   // a transvection in L
    h1 := hM @ tau1;   // a normalizing toral element
    wt1 := t1 @ Function(gamma1);  // a word in <wL1>
    wt1 := Evaluate (wt1, wL1);   // a word in defining gens   
    ws1 := s1 @ Function(gamma1);  // a word in <wL1>
    ws1 := Evaluate (ws1, wL1);   // a word in defining gens
    wh1 := h1 @ Function(gamma1);   // a word in <wL>
    wh1 := Evaluate (wh1, wL1);   // a word in defining gens


    // --- find a conjugate of <s1> not in <L1> --- //
    // EOB added next line to ensure inL1 is defined 
    inL1 := false;
    i:=0;
    mylimit := 10;
    repeat
        i+:=1;
        g, w := Random (proc);
        t := s1^g;
        if (Type(G) eq GrpMat) and (LL1 cmpne L1) then
            tt, inL1 := MatrixBlocks(L1, t);
            tt := inL1 select tt[secnum] else tt;
        else 
            tt := t;
            inL1 := true;
        end if;
        wt := ws1^w;
        // Feb 2015 EOB addition -- must recognise SL2 before using SL2ElementToWord
        // I make myL copy because recognition of LL1 causes crash later
        if inL1 then 
           // inL1, _ := SL2ElementToWord (LL1, tt);
           myL := sub<Generic (LL1) | Generators (LL1)>;
           flag := RecogniseSL2 (myL, q);
           inL1, _ := SL2ElementToWord (myL, tt);
        end if;
    until (not inL1) and (t, s1) ne Identity (G) or i eq mylimit;
    if i eq mylimit then
        return false,_,_;
    end if;

    // --- construct a noncentral element of <Q> --- //   
    Lgens := [ s1^(h1^i) : i in [0..e-1] ] cat [ t ];
    L := sub < Generic (G) | Lgens >;
    wL := [ ws1^(wh1^i) : i in [0..e-1] ] cat [ wt ];
    flag, phiL, tauL, gammaL, deltaL := RecogniseSL2Section (L, q);
    h := SL2NormalisingToralElement (L, phiL, tauL, s1, t);
    wh := h @ Function(gammaL);
    wh := Evaluate (wh, wL);
    u0 := (h, h1);
    wu0 := (wh, wh1);

    /////////////////////////////////////////////////////
    // assemble the data structure: See Section 4.3.2. //
    /////////////////////////////////////////////////////
    
    // first elements of <L2> and their images ... Eq (10)
    lM := GL (2, F)![0,1,-1,0];  
    l2 := lM @ tau2;
    wl2 := Evaluate (l2 @ Function(gamma2), wL2);
    s2 := sM @ tau2;
    ws2 := Evaluate (s2 @ Function(gamma2), wL2);
    t2 := tM @ tau2;
    wt2 := Evaluate(t2 @ Function(gamma2), wL2);
    h2 := hM @ tau2;
    wh2 := Evaluate (h2 @ Function(gamma2), wL2);
    I4 := Identity (GL (4, F));
    ll2 := GL (4, F)!InsertBlock (I4, lM, 3, 3);
    ss2 := GL (4, F)!InsertBlock (I4, sM, 3, 3);
    hh2 := GL (4, F)!InsertBlock (I4, hM, 3, 3);
    // next generators for <Q> as <F>-space and their images ... Eq (13)
    u := ((u0, s2), h2); // differ here ? no ^l2?
    wu := ((wu0, ws2), wh2);

    if (u eq Identity (G)) then
        u := (u0, h2);
        wu := (wu0, wh2);
    end if;
    v := u^l2;
    wv := wu^wl2;
    uu := GL (4, F)![1,0,0,0, 0,1,-1,0, 0,0,1,0, -1,0,0,1];
    vv := uu^ll2;
    t := IsOdd(q) select (v,u) else u * (s2, v);;
    tt := IsOdd(q) select (vv,uu) else uu*(ss2, vv); 
    outby := IsOdd(q) select ((t @ phi1)[2,1])/2 else (t @ phi1)[2,1];
    lM := Matrix(lM);
    lM[2,1] := outby*lM[2,1];
    lM[1,2] := outby^-1*lM[1,2];
    lM := GL(2,q)!lM;
    l1 := lM @ tau1;
    wl1 := Evaluate(l1 @ Function(gamma1), wL1);
    x := u^(l2^2);
    wx := wu^(wl2^2);
    y := x^l1;
    wy := wx^wl1;
    xx := x^l2;
    wxx := wx^wl2;
    yy := y^l2;
    wyy := wy^wl2;
    t1 := (y,xx);
    wt1 := (wy, wxx);
    cyc := l2^2*(y^3*t1)^3;
    wcyc := wl2^2*(wy^3*wt1)^3;
    t2 := tM @ tau2;
    wt2 := Evaluate(t2 @ Function(gamma2), wL2);
    E := [ l2, cyc, t2, h2, cyc, x];
    wE := [ wl2, wcyc, wt2, wh2, wcyc, wx];

    assert Evaluate(wE, [G.i : i in [1..Ngens(G)]]) eq E;
    w,r := ClassicalStandardPresentation("Sp",4,q);
    S := Set(Evaluate(r, E));
    f := #S eq 1;
    if not f then 
    // "Sp4:Failure 3";
         return false,_,_;
    else
        return true, E, wE; 
    end if;
end function;

intrinsic Internal_RecogniseSp4( G :: Grp, q :: RngIntElt)
-> SeqEnum, SeqEnum
{Kenneth code for Sp4}
// "*** In new SP4 code ";
    if (q in {2, 3, 5}) then 
       f, alpha, beta, phi, tau := SporadicSp4 (G, q);
       if f then
          E := ClassicalStandardGenerators ("Sp", 4, q);
          S := sub<Universe (E) | E >;
          t := TransformForm (S);
          E := E^t;
          E := [e @ beta: e in E];
          W := [phi (e): e in E];
          return true, E, W;
       else
          return false, _, _;
       end if;
    end if;

    limit := 20;
    i := 0;
    repeat 
        i+:=1;
        f := false;
        f,e,w := FindLGOGens(G,q);
    until f or i eq limit;
    if not f then return false, _, _; end if;
    assert f;
    return true, e,w;
end intrinsic;

function LargeToSmall(G, E, X, type, d, F, g, CB)
    f, w := ClassicalRewrite(G, E, type, d, #F, g);
    return Evaluate(w, X)^CB;
end function;

function SmallToLarge(S, E, X, type, d, F, g, CB)
    f, w := ClassicalRewrite(S, X, type, d, #F, g^(CB^-1));
    return Evaluate(w, E);
end function;

function LargeToWordGroup(G, E, W, type, d, F, g)
    f, w := ClassicalRewrite (G, E, type, d, #F, g);
    return Evaluate(w, W);
end function;

intrinsic RecogniseSp4  (G :: Grp, q :: RngIntElt) ->  
BoolElt, Map, Map, Map, Map , [], []
{ given a central quotient G of Sp(4, q), return a homomorphism from G to (P)Sp (4, q), 
 a homomorphism from (P)Sp(4, q) to G, the map from G to its word group and the
 map from the word group to G.  Also return standard generators for G and SLPs for 
 these in generators of G.}

     require IsPrimePower (q): "Field size is not correct";

     if assigned (G`RecognitionMaps) then
         maps := G`RecognitionMaps;
         return true, maps[1], maps[2], maps[3], maps[4], maps[5], maps[6];
     end if;

     d := 4;  F := GF (q); 

     f, E, W := Internal_RecogniseSp4 (G, q);
     if not f then return false, _,_,_,_,_,_; end if;
     WG := WordGroup (G);

     // find change-of-basis matrix to convert form into Magma form  
     stdGens := ClassicalStandardGenerators ("Sp", 4, q);
     K := sub < GL (4, q) | stdGens>;
     CB := GL(4,q)![1,0,0,0, 0,0,0,1, 0,1,0,0, 0,0,1,0];
//     CB := TransformForm (K);

     S := K^CB;
    
     // set up maps
     generic := Generic (G);
     WG := WordGroup (G);

     type := "Sp";
      phi := hom<Generic(G) -> Generic(K) | x :->
          LargeToSmall(G, E, stdGens, type, d, F, x, CB)>;
      tau := hom<Generic(K) -> Generic(G) | x :->
          SmallToLarge(S, E, stdGens, type, d, F, x, CB)>;
      gamma := hom<Generic (G) -> WG | x :->
            LargeToWordGroup(G, E, W, type, d, F, x)>; 
      delta := hom<WG -> G | x :-> Evaluate(x, [G.i: i in [1 .. Ngens(G)]])>;

     G`RecognitionMaps := < phi, tau, gamma, delta, E, W>;
             
return true, phi, tau, gamma, delta, E, W;
end intrinsic;
