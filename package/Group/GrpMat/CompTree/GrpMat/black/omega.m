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

import "recognise-section.m" : RecogniseSection, GetType;

///////////////////////////////////////////////////////////////////////

//Given a definite line of an orthogonal 2-space (type minus) E, return a standard pair

FindStandardMinusPair := function( E, mu )
    assert Dimension(E) eq 2;
    assert WittIndex(E) eq 0;
    V := Generic(E);
    B := InnerProductMatrix(V);
    Q := QuadraticFormMatrix(V);  
    F:= BaseRing(V);
    q := #F;
    if IsEven(q) then 
        if mu eq 0 then
             W := WittDecomposition(E);
             u := W[#W].1;
             v := W[#W].2;
             return u, v, false;
	 else
	     W := WittDecomposition(E);
             u := W[#W].1;
             v := W[#W].2;
             assert #Roots(Polynomial(GF(q), [mu +QuadraticNorm(v), 1, 1])) eq 2;
             x := Roots(Polynomial(GF(q), [mu +QuadraticNorm(v), 1, 1]));
             v:= x[1][1]*u + v;
             assert QuadraticNorm(v) eq mu;
             return u, v, false;
/*
             assert exists(z){ z : z in CartesianProduct(E, E) |
		 (QuadraticNorm(z[1]) eq 1) and (QuadraticNorm(z[2]) eq mu) and 
		 (InnerProduct(z[1],z[2]) eq 1) };
             return z[1], z[2], false;
*/
      end if;
    else 
        rho := PrimitiveElement(F);
        v1 := E.1; 
        alpha := QuadraticNorm(v1);
        if IsSquare(alpha) then 
            sqrt := Sqrt(alpha);
            flipped:=false;
        else;
            B:= rho*B;
            flipped:=true;
            sqrt := Sqrt(rho*alpha);
            Q:= rho*Q;
            B:= rho*B; 
            V := QuadraticSpace(Q);
            E := sub< V | E.1, E.2>;
            v1 := V!v1;
        end if;
        v1:= sqrt^-1 * v1;
        V1:= sub<V | v1>;
        V1perp := OrthogonalComplement(E, V1);
        assert Dimension(V1perp) eq 1 ;
        v2 := V1perp.1;
        alpha := QuadraticNorm(v2);
        sqrt := (q mod 4) eq 1 select Sqrt(rho^-1*alpha) else Sqrt(alpha);
        v2 := sqrt^-1 * v2;
        return  v1, v2, flipped ;
    end if;
end function;

FindHyperbolicPair := function(E)
    if Type(E) eq SeqEnum then
        E:= sub<Parent(E[1]) | E>;
    end if;
    assert Dimension(E) eq 2;
    assert WittIndex(E) eq 1;
    Q := QuadraticFormMatrix(E);
    t := HyperbolicSplitting(E);
    e := t[1][1][1];
    f := t[1][1][2];
    return e, f ;
end function;

FindHyperbolicBasis := function(E)
    V := Generic(E);
    split := HyperbolicSplitting(E);
    bas := split[1];
    bas := [V!bas[i][1] : i in [1..#bas]] cat 
               [V!bas[#bas - i][2] : i in [0..#bas -1]];
    return bas;
end function;

ConstructJ := function(G,d,q,e,F,P )
    n:= d-3-e;
    limit:= 100*n;//10^5*n;      //finding tau
    limit2:= 2^3;       //constructing OmegaPlus(6,q)
    limit3 := 5; // whole process is wrapped. How many times do you want to do the whole process
    _,p,k:=IsPrimePower(q);
    i:=0;
    list:=[ 0 : i in [1..limit2+2]];
    j:=0;
    Lietypetime := 0;
    repeat 
        j+:=1;
        list[#list] +:=1;
        repeat
            i+:=1;
            flag1:=false; flag2:= false; flag3:=false; flag:=false;
            t,wt:=Random(P);
            ot:= Order(t);
            o1:= q^2 -1;
            o2:= q^(n div 2) +1;
            sigma:=t^o1;
            wsigma:=wt^o1;
            osigma:= ot div (Gcd( ot, o1));
            flag1:= Isppdhash( osigma, p, n*k); 
            if not flag1 then continue; end if;
            b:= t^(o2);
            wb:= wt^o2;
            ob:= (ot div (Gcd( ot, o2)));
            if e eq 1 then
                flag2:= Isppdhash(ob, p, 2*k);
                if not flag2 then continue; end if;
                a:= b^(q+1);
                wa:= wb^(q+1);
                oa:= (ob div (Gcd( ob , q+1)));
       	    else
	        flag2:=true;
    	        a:=b;
                wa:= wb;
                oa:= ob;
            end if;
            if q eq 7 and oa ne 3 then continue; end if;
            flag3:= Isppdhash(oa, p, k);
            if not flag3 then continue; end if;
            flag:= flag1 and flag2 and flag3;
        until i eq limit or flag;
        if i eq limit then
            "exit here";
            return false,_,_,_,_,_,_,_,_,_,_,_,_,_;
        end if;
        i:=0;
        repeat
            i+:=1;
            f:=false;
            g1, wg1:= Random(P);
            g2, wg2:= Random(P);
            ag1:=a^g1;
            ag2:=a^g2;
            J:= sub<Generic(G) |  [a, ag1, ag2] >;
            zxc:= Cputime();
            ff,type:= LieType(J, p);
            Lietypetime +:= Cputime(zxc);
            vprint myomega : "Lietype time so far:", Lietypetime;
            if not ff then continue; end if;
            ff:= type eq <"A", 3, q>;
            if not ff then continue; end if;
            ord := (( q^3 mod 4) eq 1) select 2 else 1;  
            if  p ne 2 then 
                Z:= EstimateCentre(J, 4) ;
//"Letting through J with centre size:", #Z;
                if #Z gt ord then continue; end if;
            end if;
            list[i] +:=1;
            list[#list -1 ] +:=1;
            vprint myomega : list;
            vprint myomega : "time to recognise OmegaPlus(6,q) ";
            f, aJ, bJ, cJ, dJ  := RecogniseSection(J, "Omega+", 6, q);
//            f, aJ, bJ, cJ, dJ, EE, WW  := ClassicalConstructiveRecognition (J, "Omega+", 6, q);
        until i eq limit2 or f;
    until j eq limit3 or f;
    if j eq limit3 then
        return false,_,_,_,_,_,_,_,_,_,_,_,_,_;
    end if;
    wag1:= wa^wg1;
    wag2:= wa^wg2;
    return f,J,a,ag1, ag2, sigma, wa, wag1, wag2, wsigma;
end function;

//embeds an element of GL(4,q) into GL(6,q)
EmbedOmega4q := function(q, i, j, g)
    G:=GL(6,q);
    I:=Identity(G);
    I:=Matrix(I);
    l:=[i,j];
    for a in [1..2] do
        for b in [1..2] do
            I[l[a],l[b]] := g[a,b];
            I[7- l[a], 7- l[b]] := g[ 5-a, 5-b];
            I[7-l[a], l[b]] := g[5-a, b];
            I[l[a], 7 - l[b]] := g[a, 5-b];
        end for;
    end for;
    I:= G ! I;
    return I;
end function;

FindOmegas := function(G,d,q,e,string)
    flag,p,k:=IsPrimePower(q);
    if not flag then
        return false,_,_,_,_,_,_,_,_,_;
    end if;
    F:=GF(q);
    rho:=PrimitiveElement(F);
    P:=RandomProcessWithWords(G);
    flag,J,a,ag1, ag2, sigma, wa, wag1, wag2, wsigma :=  
            ConstructJ(G,d,q,e,F,P);
    if not flag then 
       return false,_,_,_,_,_,_,_,_,_;
    end if;

    f,aJ,bJ,cJ,dJ :=
          ClassicalConstructiveRecognition(J, "Omega+", 6, q);
      //,EE,WW := 
//QQ,RR:= ClassicalStandardPresentation ("Omega+", 6, q);
//assert #Set (Evaluate (RR, EE)) eq 1;

    Q:= StandardQuadraticForm( 6, q);
    V := QuadraticSpace(Q);
    wJgens:= [wa, wag1, wag2];

    //modify maps so that a @ aJ has 1-dim eigenspaces e_{ \pm 1} 
    aa:= a @ (aJ) ;
    values:= Eigenvalues(aa);
    spaces:= [ Eigenspace( aa, v[1] ) : v in values ];
    S:= [s : s in spaces | Dimension(s) eq 1 ];
    if #S ne 2 then 
        // "bad 'a'";
        return false,_,_,_,_,_,_;
    end if;
    E := sub< V | S[1].1, S[2].1>;
    e1,f1 := FindHyperbolicPair(E);
    Eperp := OrthogonalComplement(V, E);
    basis:=FindHyperbolicBasis(Eperp);
    basis := [e1] cat basis cat [f1];
    CB:= MyChangeOfBasisMatrix( V, basis);
    aJ := map < Generic(G)-> GL(6,q ) | x:->  ( x @ (aJ)) ^(CB^-1)  >;
    bJ := map< GL(6,q ) -> Generic(G) | x:-> (x^CB) @ (bJ) > ;
    maps:=J`RecognitionMaps;
    maps := < aJ, bJ, maps[3], maps[4] > ;
    J`RecognitionMaps := maps;

//construct another Omega subgroup L, and DJ = J meet L.
//first construct DJ
    Omega4 := OmegaPlus(4,q);
    Omega4gens := UserGenerators(Omega4);
    DDJgens:= [ EmbedOmega4q(q, 2,3, Omega4gens[i]) : i in [1..#Omega4gens]];
    DJgens:= (DDJgens @ (bJ));
    DJ:=sub<Generic(G) | DJgens>;
    wDJgens := [DJgens[i] @ Function(cJ)  : i in [1..#DJgens]];
    wDJgens := Evaluate(wDJgens,  wJgens);
//now construct L
    Lgens:=[];
    wLgens:=[];
    zxc := Cputime();
    for i in [0..d-2] do
        Lgens:= Lgens cat DJgens^(sigma^i);
        wLgens := wLgens cat [wDJgens[j]^(wsigma^i) : j in [1..#DJgens]] ;
    end for;
    L:= sub< Generic(G) | Lgens >;
    wL :=[];
    for i in [1..#Lgens] do 
        l:=Lgens[i];
        if not wLgens[i] in wL and l ne Identity(G) then  
            wL := wL cat [wLgens[i]];
        end if;
    end for;
    type := GetType(string, d - 2, q);
    flag, actualtype := LieType(L, p);
    if not flag then 
        "L not LieType";
        return false,_,_,_,_,_,_;
    end if;
    if actualtype ne type then
        "L incorrect LieType"; 
        return false,_,_,_,_,_,_;
    end if;
    ZL, wZL := EstimateCentre(L,4);
    if (#ZL gt 2) then
        "L has wrong centre";
        return false,_,_,_,_,_,_;
    end if;

//   fL,aL,bL,cL,dL,EE,WW:=
//           ClassicalConstructiveRecognition (L, string, d - 2, q);
     fL, aL, bL, cL, dL :=   RecogniseSection(L, string, d - 2, q); 
//QQ,RR:= ClassicalStandardPresentation (string, d - 2, q);
//assert #Set (Evaluate (RR, EE)) eq 1;
    if not fL then 
    "failed to recognise L";
        return false,_,_,_,_,_,_;
    end if;
    return true, L,J,DJ, wL,wJgens, wDJgens;
end function;

AlignImageOfL := function(G, J, L, JmeetL,d, q, e, string);
    f,p,k := IsPrimePower(q);
    F := GF(q);
    D:= JmeetL;
    fJ,aJ,bJ,cJ,dJ := 
    ClassicalConstructiveRecognition(J, "Omega+", 6 , q );
 assert fJ;
//  QQ,RR:= ClassicalStandardPresentation ("Omega+", 6, q);
//  assert #Set (Evaluate (RR, EE)) eq 1;

    if string eq "Omega+" then 
        LL := OmegaPlus(6,q);
    elif string eq "Omega-" then
        LL := OmegaMinus(d-2,q);
    elif string eq "Omega" then 
        LL := Omega(5,q);
    end if;
    f,aL,bL,cL,dL  := 
      ClassicalConstructiveRecognition(L, string, d-2, q);
/*
assert f;
 QQ,RR:= ClassicalStandardPresentation (string, d - 2, q);
 assert #Set (Evaluate (RR, EE)) eq 1;
*/
// "TEST OF PRES worked";

    GG:= GL(d-2,q);
    Q := ClassicalForms(LL)`quadraticForm;
    V := QuadraticSpace(Q);
//finding V4, VD, and orthogonalcomeplements
    e:= OmegaPlus(2,F);
    e:= e.1;
    MA := MatrixAlgebra(F,6);
    ee:= Identity(MA);
    ee[2,2] := e[1,1];
    ee[5,5] := e[2,2];
    eJ:= ee;
    e:= eJ @ bJ;
// "Now apply this map";
    eL := e @ aL;
// "Back after this map";

    V4:= Eigenspace(eL, 1) ;
    V4 := sub< V | UserGenerators(V4) >;
    V4perp := OrthogonalComplement(V, V4);
    DLgens := UserGenerators(D) @ aL;
    spaces := [ Eigenspace(s, 1) : s in DLgens ] ;
    VDperp:= &meet spaces;
    VDperp := sub< V | UserGenerators(VDperp)>;
    VD:= OrthogonalComplement(V, VDperp);
//now disect module using VD and V4 and construct std basis
    if string eq "Omega+" then
        e4, f4 := FindHyperbolicPair(VDperp);
        mu := 0;
    elif string eq "Omega-" then
        if d eq 8 then
            e4, f4 , flipped:= FindStandardMinusPair(VDperp, 0);
            mu := QuadraticNorm(f4);
        else
            split := HyperbolicSplitting(VDperp);
            e4f4 := split[1][1];
            e4 := e4f4[1];
            f4 := e4f4[2];
            Minus2Space := sub<V | split[2]>;
            e5, f5, flipped := FindStandardMinusPair(Minus2Space, 0);
            mu := QuadraticNorm(f5);
        end if;
        if flipped then
            V := Generic(Parent(e4));
            VD := sub<V | UserGenerators(VD)>;
            VDperp := sub< V| e4,f4>;
            V4perp := sub<V | UserGenerators(V4perp)>;
            V4 := sub<V | UserGenerators(V4)>;
        end if;
    elif string eq "Omega" then 
        e4 := VDperp.1;
        alpha := QuadraticNorm(e4);
        alpha := Sqrt(alpha);
        e4 := alpha^-1*e4;
        flag := true;
        flipped := false;
        f4 := Zero(V);
        mu := 0;
    end if;
    e2, f2 := FindHyperbolicPair(V4perp);
    E3 := V4 meet VD;
    e3, f3 := FindHyperbolicPair( E3);
    if d eq 10 then 
        basis := [e2,e3,e4,e5,f5,f4,f3,f2];
    else 
        basis := (string eq "Omega") select [e2, e3, e4, f3, f2] else 
            [e2, e3, e4, f4, f3, f2 ];
    end if;
    CB2:= MyChangeOfBasisMatrix(V , basis);
    aL := map<  Generic(G) -> GG | x:-> (x @ aL)^(CB2^-1) >;
    bL := map< GG -> Generic(G) | x :-> (x^CB2) @ Function(bL)> ;
    maps:= L`RecognitionMaps;
    maps := < aL, bL, maps[3], maps[4] >;
    L`RecognitionMaps := maps;
    return true, mu;
end function;

FindLGOGens_OmegaMinus10 := function(G, J, L, JmeetL, wJ, wL, wJmeetL, q)
    d := 10;
    e := -1;
    string := "Omega-";
    _, p, k := IsPrimePower(q);
    F:= GF(q);
    rho := PrimitiveElement(F);
    f, mu :=  AlignImageOfL(G,J,L,JmeetL,d, q,e, string);
    f, aJ, bJ, cJ, dJ  :=
      ClassicalConstructiveRecognition(J, "Omega+", 6,  q);
    f, aL, bL, cL, dL :=
      ClassicalConstructiveRecognition(L, string, d - 2 , q);
    s6 := ClassicalStandardGenerators("Omega+", 6, q);
    s8 := ClassicalStandardGenerators("Omega-",8 , q);
    //change L,J recognition maps so that images are in same basis as std gens
    p6 := GL(6,q)![1,0,0,0,0,0, 0,0,1,0,0,0, 0,0,0,0,1,0,
		0,0,0,0,0,1, 0,0,0,1,0,0, 0,1,0,0,0,0];
    p8 := GL(8,q)![1,0,0,0,0,0,0,0, 0,0,1,0,0,0,0,0, 0,0,0,0,1,0,0,0,
		0,0,0,0,0,0,1,0, 0,0,0,0,0,0,0,1, 0,0,0,0,0,1,0,0,
		0,0,0,1,0,0,0,0, 0,1,0,0,0,0,0,0];
    aJ := map< Domain(aJ) -> Codomain(aJ) | x :-> (x @ aJ)^(p6) >;
    bJ := map< Domain(bJ) -> Codomain(bJ) | x :-> (x^(p6^-1)) @ bJ >;
    aL := map< Domain(aL) -> Codomain(aL) | x :-> (x @ aL)^(p8) >;
    bL := map< Domain(bL) -> Codomain(bL) | x :-> (x^(p8^-1)) @ bL >;
    S := sub<GL(8,q) | s8> ;
    Q := ClassicalForms(S)`quadraticForm;
    V := QuadraticSpace(Q);
    Minus2Space := sub<V | V.7,V.8>;
    v1, v2, flipped := FindStandardMinusPair( Minus2Space, mu ) ;
    V := Generic(Parent(v1));
    E1 := sub<V | V.1, V.2>;
    e1,f1 := FindHyperbolicPair(E1);
    E2 := sub<V | V.3, V.4>;
    e2, f2 := FindHyperbolicPair(E2);
    E3 := sub< V | V.5, V.6>;
    e3,f3 := FindHyperbolicPair(E3);
    bas := [e1,f1,e2,f2,e3,f3,v1,v2];
    cb := MyChangeOfBasisMatrix(V, bas);
    s8 := [s^(cb^-1) : s in s8];
    S8 := [s @ bL : s in s8];
    wS8 := [ s @ Function(cL) : s in S8];
    wS8 := Evaluate(wS8, wL);
    S6 := [s @ bJ : s in s6];
    wS6 := [ s @ Function(cJ) : s in S6];
    wS6 := Evaluate(wS6, wJ);
    E:= S8[1..3] cat [S6[4]] cat [S8[5]*S6[4]];
    W := wS8[1..3] cat [wS6[4]] cat [wS8[5]*wS6[4]];
    w,r := ClassicalStandardPresentation("Omega-", 10, q);
    n :=#Set(Evaluate(r, E));
    f := n eq 1;
    assert Evaluate(W, [G.i : i in [1..Ngens(G)]]) eq E;
    return f, E, W;
end function;

FindLGOGens_OmegaMinus8 := function(G, J, L, JmeetL, wJ, wL, wJmeetL, q )
    d := 8;
    e := -1;
    string := "Omega-";
    _, p, k := IsPrimePower(q);
    F := GF(q);
    rho := PrimitiveElement(F);
    f, mu := AlignImageOfL(G,J,L,JmeetL,d, q,e, string);
    f, aJ, bJ, cJ, dJ  :=
      ClassicalConstructiveRecognition(J, "Omega+", 6,  q);
    f, aL, bL, cL, dL :=
      ClassicalConstructiveRecognition(L, string, d - 2 , q);
    S1 := ClassicalStandardGenerators("Omega-", 6, q);
    S2 := ClassicalStandardGenerators("Omega+", 6, q );
    //change basis to agree with std magma form
    perm2 := GL(6,q)![1,0,0,0,0,0,  0,0,0,0,0,1,  0,1,0,0,0,0,
		   0,0,0,0,1,0, 0,0,1,0,0,0,  0,0,0,1,0,0];
    S2 := S2^perm2;
    SS := sub< GL(6,q) | S1 > ;
    forms := ClassicalForms(SS);
    Q := forms`quadraticForm;
        V := QuadraticSpace(Q);
    V1 := sub< V | V.5, V.6>;
    v1, v2, flipped := FindStandardMinusPair( V1, mu ) ;
    V := Generic(Parent(v1));
   
    E1 := sub<V | V.1, V.2>;
    e1, em1 := FindHyperbolicPair( E1);
    E2 := sub<V | V.3, V.4>;
    e2, em2 := FindHyperbolicPair( E2);
    bas := [e1 , e2 , v1, v2 ,em2, em1];
    CB := MyChangeOfBasisMatrix(V, bas);
    S1 := S1^(CB^-1);
    //now construct Eamonn's gens
    E1 := S1[1..3] @ bL;
    E2 := S2 @ bJ;
    W1 := [E1[i] @ Function(cL) : i in [1..#E1]];
    W2 := [E2[i] @ Function(cJ) : i in [1..#E2]];
    W1 := Evaluate( W1, wL);
    W2:= Evaluate(W2, wJ);
    e4 := GL(6, q)![0,1,0,0,0,0,  -1, 0,0,0,0,0,  0,0,1,0,0,0,
    		 0,0,0,1,0,0,   0,0,0,0,0,-1,   0,0,0,0,1,0];
    e4 := e4 @ bJ;
    w4 := e4 @ Function(cJ);
    E:= E1[1..3] cat [e4] cat [E2[8]];
    W := W1[1..3] cat [Evaluate(w4, wJ)] cat [W2[8]];
    _, R := ClassicalStandardPresentation("Omega-", 8, q);
    assert Evaluate(W, [G.i : i in [1..Ngens(G)]]) eq E;
    flag := #Set(Evaluate(R,E)) eq 1;
    return flag, E, W ;
end function;

FindLGOGens_OmegaPlus8 := function(G, J, L, JmeetL, wJ, wL, wJmeetL, q )
    d := 8;
    e := 1;
    string := "Omega+";
    _, p, k := IsPrimePower(q);
    F:= GF(q);
    rho := PrimitiveElement(F);
    f, mu :=  AlignImageOfL(G,J,L,JmeetL,d, q,e, string);
    f, aJ, bJ, cJ, dJ  :=
      ClassicalConstructiveRecognition(J, "Omega+", 6,  q);
    f, aL, bL, cL ,dL :=
      ClassicalConstructiveRecognition(L, string, d - 2 , q);
    S1 := ClassicalStandardGenerators(string, d - 2, q);
    S2 := ClassicalStandardGenerators("Omega+", 6, q );
    //change basis to agree with std magma form
    perm2 := GL(6,q)![1,0,0,0,0,0,  0,0,0,0,0,1,  0,1,0,0,0,0,
    		   0,0,0,0,1,0, 0,0,1,0,0,0,  0,0,0,1,0,0];
    S2 := S2^perm2;
    S1 := S1^perm2;
    //now construct Eamonn's gens
    E1 := S1 @ bL;
    E2 := S2 @ bJ;
    W1 := [E1[i] @ Function(cL) : i in [1..#E1]];
    W2 := [E2[i] @ Function(cJ) : i in [1..#E2]];
    W1 := Evaluate( W1, wL);
    W2:= Evaluate(W2, wJ);
    c1 := E2[8]; wc1 := W2[8];
    c2 := E1[4]^E1[8]; wc2 := W1[4]^W1[8];
    c :=  c2 * c1;
    wc := wc2 * wc1;
    E := [E2[i]: i in [1..7]] cat [c];
    W := [W2[i]: i in [1..7]] cat [wc];
    _, R := ClassicalStandardPresentation("Omega+", 8, q);
    assert Evaluate(W, [G.i : i in [1..Ngens(G)]]) eq E;
    flag := #Set(Evaluate(R,E)) eq 1 ;
    return flag, E, W ;
end function;

FindLGOGens_Omega7 := function(G, J, L, JmeetL, wJ, wL, wJmeetL, q )
    d := 7;
    e := 0;
    string := "Omega";
    _, p, k := IsPrimePower(q);
    F:= GF(q);
    rho := PrimitiveElement(F);
    GG := GL(d-2, q);
    f, mu :=  AlignImageOfL(G,J,L,JmeetL,d, q,e, string);
    f, aJ, bJ, cJ, dJ  :=
      ClassicalConstructiveRecognition(J, "Omega+", 6,  q);
    f, aL, bL, cL ,dL :=
      ClassicalConstructiveRecognition(L, string, d - 2 , q);
    S1 := ClassicalStandardGenerators(string, d - 2, q);
    // S2 := ClassicalStandardGenerators("Omega+", 6, q );
    S2 := ClassicalStandardGenerators("Omega+", 6, q );
    perm2 := GL(6,q)![1,0,0,0,0,0,  0,0,0,0,0,1,  0,1,0,0,0,0,
    		   0,0,0,0,1,0, 0,0,1,0,0,0,  0,0,0,1,0,0];
    S2 := S2^perm2;
    //Change basis of S1 to agree with standard magma basis.
    perm1 :=  GG![1,0,0,0,0,  0,0,0,0,1,  0,1,0,0,0,
    	       0,0,0,1,0,  0,0,1,0,0];
    S1 := S1^perm1;
    SS := sub<GG | S1 >;
    forms := ClassicalForms(SS);
    Q := forms`quadraticForm;
    V := QuadraticSpace(Q);
    v:= V.3;
    alpha := QuadraticNorm(v);
    sqrt := IsEven(Log(alpha));
    if sqrt then
        alpha := Sqrt(alpha);
        v:= alpha^-1*v;
        bas := [V.1, V.2, v, V.4, V.5];
    else
        Q:= rho*Q;
        alpha := Sqrt(rho*alpha);
        V := QuadraticSpace(Q);
        v:= V!(alpha^-1 *v);
        V1 := sub<V | V.1, V.5>;
        e1, em1 := FindHyperbolicPair(V1);
        V2 := sub<V | V.2, V.4 >;
        e2, em2 := FindHyperbolicPair(V2);
        bas := [e1, e2, v, em2, em1];
    end if;
    CB := MyChangeOfBasisMatrix(V, bas);
    S1 := S1^(CB^-1);
    //now construct Eamonn's gens.
    E1 := S1 @ bL;
    E2 := S2 @ bJ;
    W1 := [E1[i] @ Function(cL) : i in [1..#E1]];
    W2 := [E2[i] @ Function(cJ) : i in [1..#E2]];
    W1 := Evaluate( W1, wL);
    W2:= Evaluate(W2, wJ);
    S := ClassicalStandardGenerators("Omega",7,q);
    SS:= sub<GL(7,q) | S >;
    forms := ClassicalForms(SS);
    Q:= forms`quadraticForm;
    alpha := Q[7,7];
    sqrt := IsEven(Log(alpha));
    if sqrt then
        alpha := Sqrt(alpha);
        CF := GL(7,q) ! [1,0,0,0,0,0,0,  0,0,0,0,0,0,1,
        		  0,1,0,0,0,0,0,  0,0,0,0,0,1,0,
        		  0,0,1,0,0,0,0,  0,0,0,0,1,0,0,  0,0,0,alpha,0,0,0];
    else
        Q:= rho*Q;
        alpha := Sqrt(rho*alpha);
        V := QuadraticSpace(Q);
        E1 := sub<V | V.1, V.2>;
        E2 := sub<V | V.3, V.4>;
        E3:= sub< V | V.5, V.6 >;
        e1, em1 := FindHyperbolicPair(E1);
        e2, em2 := FindHyperbolicPair(E2);
        e3, em3 := FindHyperbolicPair(E3);
        v:= alpha^-1*V.7;
        bas := [e1, e2, e3, v, em3, em2, em1 ];
        CF := MyChangeOfBasisMatrix(V, bas);
        CF := CF^-1;
    end if;
    S:= S^CF;
    SinL := S[1..3];
    SinL := [GL(5,q) ! ExtractBlock(s, 2, 2, 5, 5) : s in SinL];
    SinJ := S[4..5];

    SinJConstructer := function(SinJ)
        newSinJ := [];
        F:= BaseRing(Parent(SinJ[1]));
        for s in SinJ do
            block1 := ExtractBlock(s,1,1,3,3);
            block2 := ExtractBlock(s,5,5,3,3);
            I := Identity(MatrixAlgebra(F, 6));
            I := InsertBlock( I, block1, 1, 1);
            I := InsertBlock(I, block2, 4,4 );
            I := GL(6,q) ! I;
            newSinJ := newSinJ cat [I];
        end for;
        return newSinJ;
    end function;

    SinJ := SinJConstructer(SinJ);
    E:= (SinL @ bL) cat (SinJ @ bJ );
    W := [ Evaluate(E[i] @ Function(cL), wL) : i in [1..3]] cat
        [ Evaluate(E[i] @ Function(cJ), wJ) : i in [4..5]];
    _, R := ClassicalStandardPresentation("Omega", 7 , q);
    assert Evaluate(W, [G.i : i in [1..Ngens(G)]]) eq E;
    flag := #Set(Evaluate(R,E)) eq 1 ;
    return flag, E, W ;
end function;

intrinsic Internal_RecogniseOmegaMinus8( G :: Grp, q :: RngIntElt ) 
-> BoolElt, SeqEnum, SeqEnum
{Kenneth code for O8-}
    if assigned G`UserGenerators then 
       hold := G`UserGenerators; delete G`UserGenerators; 
    end if;
    limit1 := 10;
    e:= -1; 
    string := "Omega-";
    i := 0;
    repeat 
        i+:=1;
        f, L, J, JmeetL, wL, wJ , wJmeetL := FindOmegas(G, 8, q, e, string);
        if not f then continue; end if;  
        f, E, W := FindLGOGens_OmegaMinus8(G, J, L, JmeetL, wJ, wL, wJmeetL,q);
    until f or i eq limit1;
    if assigned hold then G`UserGenerators := hold; end if;
    if not f then return false, _, _; else return f, E, W; end if;
end intrinsic;

intrinsic Internal_RecogniseOmegaPlus8( G :: Grp, q :: RngIntElt) 
-> BoolElt, SeqEnum, SeqEnum 
{Kenneth code for O8+}
    if assigned G`UserGenerators then 
       hold := G`UserGenerators; delete G`UserGenerators; 
    end if;
    limit1:=10;
    e:=1;
    string := "Omega+";
    i:=0;
    repeat
        i+:=1;
        f,L,J,JmeetL, wL,wJ, wJmeetL  := FindOmegas(G, 8, q, e, string);
        if not f then continue; end if;
        f, E, W := FindLGOGens_OmegaPlus8(G, J, L, JmeetL, wJ, wL, wJmeetL,q) ;
    until f or i eq limit1;
    if assigned hold then G`UserGenerators := hold; end if;
    if not f then return false, _, _; else return f, E, W; end if;
end intrinsic;

intrinsic Internal_RecogniseOmega7( G :: Grp, q :: RngIntElt)
-> BoolElt, SeqEnum, SeqEnum
{Kenneth code for O7}
    if assigned G`UserGenerators then 
       hold := G`UserGenerators; delete G`UserGenerators; 
    end if;
    e := 0;
    string := "Omega";
    limit1 := 5;
    i:= 0;
    repeat 
        i+:=1;
        f,L,J,JmeetL,wL,wJ,wJmeetL := FindOmegas(G, 7, q, e, string);
        if not f then continue; end if;
        f, E, W := FindLGOGens_Omega7(G, J, L, JmeetL, wJ, wL, wJmeetL,q);
    until f or i eq limit1;
    if assigned hold then G`UserGenerators := hold; end if;
    if not f then return false, _, _; else return f, E, W; end if;
end intrinsic;

intrinsic Internal_RecogniseOmegaMinus10( G :: Grp, q :: RngIntElt)
-> BoolElt, SeqEnum, SeqEnum
{Kenneth code for O^-10}
    if assigned G`UserGenerators then 
       hold := G`UserGenerators; delete G`UserGenerators; 
    end if;
    limit1 :=10;
    e := -1;
    string := "Omega-";
    i:= 0;
    repeat
        i+:=1;
        f,L,J,JmeetL,wL,wJ,wJmeetL := FindOmegas(G, 10, q, e, string );
        if not f then continue; end if;
        f, E, W := FindLGOGens_OmegaMinus10(G,J,L,JmeetL,wJ,wL,wJmeetL,q);
    until f or i eq limit1;
    if assigned hold then G`UserGenerators := hold; end if;
    if not f then return false, _, _; else return f, E, W; end if;
end intrinsic;
