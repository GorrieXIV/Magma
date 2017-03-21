freeze;

/*
SetDelCheck(true);
SetTrace(1,true);
    Attach("/magma/sergei/tex/svn-dumas/paper-finconjcl/gennorm.mag");
    q := 3;
    F := GF(q);
    E := GF(q,2); w := E.1;
    P := PolynomialRing(E); x := P.1;
    // f is t-irred
    if q eq 5 then
        f := x^7 + w^20*x^6 + w^23*x^5 + w^7*x^4 + 4*x^3 + w^2*x^2 + w^17*x + w^19;
        t := E!2;
        f := x^3 + w^3*x^2 + w^21*x + 3;
        t := E!4;
    elif q eq 3 then
        f := x^4 + w^6*x^3 + w*x^2 + 2*x + w^6;
        f := x^5 + w*x^4 + w^6*x^3 + w^5*x^2 + w^2*x + w^3;
        f := x^3 + x^2 + w^7*x + w^3;
        t := E!2;
    end if;


    e := Degree(f);
    m := 2;
    Afm := quo<P|f^m>;

    starmap := function(g)
        seq := [ s^q : s in Eltseq(g) ];
        xs := Afm!(  (-t/(Coefficient(f,0)^m) * f^m + t) div x  );
        //return Parent(g)!&+[Afm| seq[i] * xs^(i-1) : i in [1..#seq]] ;

        res := Afm!0;
        xsi := xs^0;
        
        for i in [1..#seq] do
            res +:= seq[i] * xsi;
            xsi *:= xs;
        end for;

        return Parent(g)!res;
    end function;


    // START ALGORITHM

    c := P![Random(E):i in [0..m*e]];
    a := P!Afm!(c*starmap(c));
    assert a eq starmap(a);
    delete c;
SetMark(true);
time gn := P!GeneralisedNormOLD(a,f,t,m);gn;
a eq P!Afm!(gn*starmap(gn));
time gn := GeneralisedNorm(a,f,t,m);gn;
a eq P!Afm!(gn*starmap(gn));
clear;
ShowActive();

    SetAssertions(true);
    ProfileReset();
    SetProfile(true);
        time gn := GeneralisedNorm(a,f,t,m);
    SetProfile(false);
    G := ProfileGraph();
    ProfilePrintByTotalTime(G : Max:=10);
    SetAssertions(true);

> ProfilePrintChildrenByTime(G,25);

*/

intrinsic GeneralisedNormOLD( a::., f::., t::., m::. ) -> .
{a is poly fixed by starmap. f is t-irred, m is the m in the expression A_(f,m)}
//"---";
mytime := Cputime();

    /* TODO: check input. assume t-irreducibility in the rest of the function */

    if a eq 0 then return a; end if;

    P<x> := Parent(a);
    assert P eq Parent(f);
    
    E := BaseRing(P);
    assert IsEven(Degree(E));
    F := sub<E|Degree(E) div 2>;
    q := #F;
    
    Af := [ quo<P|f^i> : i in [1..2^Ceiling(Log(2,m))] ];

    x_star := function(n);
    /* X^* in A_{f,n} */
        xs :=  (-t/(Coefficient(f,0)^n) * f^n + t) div x;
        assert Af[n]!x * Af[n]!xs eq Af[n]!t;
        return xs;
    end function;

    starmap := function(g,n)
    /* input  g in PolynomialRing(E);                       */
    /* return g* in A_{f,n} as elt of PolynomialRing(E);    */

        seq := [ s^q : s in Eltseq(g) ];
        xs := Af[n]!x_star(n);
    
        res := Af[n]!0;
        xsi := xs^0;
        
        for i in [1..#seq] do
            res +:= seq[i] * xsi;
            xsi *:= xs;
        end for;

        return Parent(g)!res;
    end function;

    assert starmap(a,m) eq a;

    e := Degree(f);

    if IsEven(e) then
        g,h := Explode( [ c[1] : c in Factorisation(f) ] );
        assert g*h eq f;

        gm := g^m; hm := h^m;

        xx,xa,xb := XGCD(gm,hm);
        assert xx eq 1 and xa*gm + xb*hm eq xx ;

        delta   := Af[m]!xa*Af[m]!gm;
        epsilon := Af[m]!xb*Af[m]!hm;

        c := Af[m]!a*delta+epsilon;

        assert Af[m]!starmap(P!c,m) * c eq Af[m]!a;

        return c;
    end if;
    
    /* from here on f has odd degree and is irreducible */

    L := ext<E|f>;

    inv := function(a,n);
    /* input a in PolynomialRing(E);            */
    /* expect L and f be defined already        */
    /* return inverse of a in Af[n] as elt of P */

        if e eq 1 then
            La := L!Af[1]!a; // L is E and so doesn't know about reduction modulo f. reduce first.
        else
            La := L!a;
        end if;

        assert La ne 0;

        an := Af[n]!a;
        pi_ro_inv := Af[n]!Eltseq((La)^-1,E);

        c := Ceiling(Log(2,n));
        inv := Af[1]!P!pi_ro_inv;
        for i in [1..c] do
            inv := Af[2^i]!P!inv;
            inv := inv + inv - Af[2^i]!P!a*inv^2 ;
        end for;
        an_inv := Af[n]!P!inv;

        assert an_inv * an eq 1;
        return P!an_inv;
    end function;


    /* compute M  */
    M := sub<L|Degree(L) div 2>;
    assert L!gen eq L!starmap( P!Eltseq(L!gen,E), 1 ) where gen is M.1;
    
    if e eq 1 then
        La := L!Af[1]!a; // L is E and so doesn't know about reduction modulo f. reduce first.
    else
        La := L!a;
    end if;
    
    ex,c0 := NormEquation( L, M!La : Deterministic );
    assert ex;
    assert c0 * L!starmap(P!Eltseq(c0,E),1) eq La;

    c0 := P!Eltseq(c0,E);

    b := P!Af[m]!(
             inv(P!(  Af[m]!c0
                    * Af[m]!starmap(c0,m)
                   ),m)
             * a
             - 1
         );

    assert Af[m]!a eq Af[m]!c0 * Af[m]!starmap(c0,m) * ( Af[m]!b + 1 );

    assert Af[1]!b eq 0;

    /* make sure we have a solution y */
//  time   exists(y){ y : y in Af[m] | Af[m]!(P!y + starmap(P!y,m) + P!y * starmap(P!y,m)) eq Af[m]!b  };
//    assert exists(y){ y : y in Af[m] | Af[1]!P!y eq 0 and
//                                       Af[m]!(P!y + starmap(P!y,m) + P!y * starmap(P!y,m)) eq Af[m]!b  };
//    "y = ", P!y;
//  y := P!y;
//    delete y;
    
    
    /* now find it cleverly */

    B := [];
    Q := [];
    Q[m] := b;

    for i in [m-1..1 by -1] do
        B[i],Q[i] := Quotrem(Q[i+1],f^i);
    end for;
    assert Q[1] eq 0;
    assert [P| Af[1]!B[i]  : i in [1..m-1]] eq B; 
    assert b eq &+[P| B[i] * f^i : i in [1..m-1]];


    Y := [P| ]; y := P!0; ysm := P!0;

    if m gt 1 then 
        fi   := f^0;
        fsm  := Af[m]!starmap(f,m);
        fsmi := fsm^0;

        a0q := Coefficient(f,0)^q;
        X_e := (Af[1]!inv(x,1))^e;
        assert X_e * (Af[1]!x)^e  eq  1;
        a0qX_e := P!( a0q*X_e );
        assert   Af[1]!starmap(f,1) eq Af[1]!(a0qX_e*f);

        for i in [1..m-1] do;
// Cputime(mytime);
 
            fi *:= f;  // f^i

            ys := Af[i+1]!ysm;
 
            assert ys eq Af[i+1]!starmap(y,i+1);

            z := Quotrem( P!( ys + Af[i+1]!y*ys ), fi );

            assert P!Af[i+1]!( starmap(y,i+1)+ y*starmap(y,i+1) )
                eq P!Af[i]  !( starmap(y,i)  + y*starmap(y,i  ) ) + z*fi  ;
 
            assert z eq P!Af[1]!z;

            RHS := Vector(Eltseq(
                            L!( B[i] - z ),
                          M));

            A := Matrix(M,
                    [ Eltseq( L!( u + starmap(u,1) * a0qX_e^i ) , M ) where u is P!Eltseq(L.1^j,E) : j in [0..1] ]
                 );
//printf "=== i=%o ============= \n", i;
//A;
//RHS;
            /* now solve (.,.) * A = RHS */
            Y[i] := P!Eltseq(L!Eltseq(Solution(A,RHS)),E);

            fsmi *:= fsm; // fsm^i

            y   +:=                   Y[i]     * fi;
            ysm +:= P!(
                        Af[m]!starmap(Y[i], m) * fsmi
                    );
 
            assert Af[i+1]!(   y + starmap(y,i+1) + y * starmap(y,i+1)   )
                eq Af[i+1]!b ;

        end for;
//Cputime(mytime);

    end if;

    c := Af[m]!c0 * ( 1 + Af[m]!y );

//    assert 
//        Af[m]!starmap(P!c,m) * c eq Af[m]!a;

    return c;

end intrinsic;



intrinsic ConjugatorCU_JordanBlock( G::GrpMat, x::GrpMatElt ) -> GrpMatElt,GrpMatElt
{return the matrix conjugating x to conjucacy class representative}

    require x in G : "x not in G";
    n := Dimension(G);

    E := BaseRing(G);
    dF := Degree(E) div 2;
    F := sub<E| dF >;

    sigma := iso< E -> E | x :-> Frobenius(x,dF), x :-> Frobenius(x,dF) >;

    pols, parts, t := ClassInvariants(G,x);
    
    require #pols eq 1 and #parts[1] eq 1 : "This is for Jordan Blocks only";

    // Use JCF to find a conjugator in GL
    y := ClassRepresentativeFromInvariants( G, pols, parts, t );
    _, g1 := JordanForm( x );
    _, g2 := JordanForm( y );
    g   := g1^-1 * g2;
    g_1 := g2^-1 * g1; // g^-1;
    delete g2;

    // have: g^-1*x*g eq y;

    P := PolynomialRing(E); X := P.1;
    Mat := MatrixAlgebra( E, n );
    Vn := VectorSpace( E, n );

    // The star map for matrices
    J := ZeroMatrix( E, n, n );
    for i in [1..n] do  J[i,n-i+1]:=1;  end for;
    sigmaMat := func< x | Matrix(BaseRing(x),Nrows(x),Ncols(x), [sigma(a) : a in Eltseq(x)] ) >;
    starMat  := func< x | J * sigmaMat(Transpose(x)) * J >;
    delete J, sigmaMat;

    polnr := 1; 
    partnr := 1;
    
        f := pols[polnr];
        m := parts[polnr][partnr];

//        fx := Evaluate(f,Matrix(x));
        e := Degree(f);
        
        Afm := quo<P|f^m>;

        if GetAssertions() gt 0 then

            // inside this intrinsic, starmap is only used in assertions
            starmap := function(g)
                seq := [ sigma(s) : s in Eltseq(g) ];
                xs := Afm!(  (-t/(Coefficient(f,0)^m) * f^m + t) div X );
                return Parent(g)!&+[Afm| seq[i] * xs^(i-1) : i in [1..#seq]] ;
            end function;

        end if;

        // Find a generating element of V as an E[X]-module

//         Vbasis := Basis(Vn);

        if IsOdd(e) then // equiv to IsIrreducible(f) 
            u := g1[1];
        else // IsEven(e), equiv to not IsIrreducible(f);
            // to "general linear" Jordan blocks. take the sum of theiir first rows.
            u := g1[1] + g1[(m*e div 2)+1];
        end if;

        Vbasis := [ u*x^i : i in [0..m*e-1]]; // FIXME trivially speed improvable

        // this will fail if u is not a cyclic generator.
        V := VectorSpaceWithBasis( Vbasis );

        //  Identify the underlying space with the ring A_fm
        Abasis := [Afm| X^i : i in [0..m*e-1]];

        // we actually only need the one way of the map, so only define one.
        // this map is used only once, so maybe just compute the image directly there.
        v := map< V -> Afm |
          w :-> &+[ b[i]*Abasis[i] : i in [1..m*e] ] where b is Coordinates(V,w) >;
        //  a :-> &+[ b[i]*Vbasis[i] : i in [1..m*e] ] where b is Eltseq(a),


        // Find the element a of Afm corresponding to g^-* g^-1
        a := P!( v(u*starMat(g_1)*g_1) );
        assert a eq starmap(a);

        // time 
        c := P!GeneralisedNorm(a,f,t,m);
        assert Afm!(c*starmap(c)) eq Afm!a;

        // Eltseq returns coordinates with respect to the basis [1,X,X^2,X^3...]
        // use corresponding basis for Matrix ring.
        basmat := [Mat| Matrix(x)^i : i in [0..m*e-1]]; // FIXME trivially speed improvable
        h := map< Afm -> Mat |
                   a :-> &+[ b[i]*basmat[i] : i in [1..#b] ] where b is Eltseq(a) >;

        // We now have a conjugating element
        k := h(Afm!c) * g;
                
    assert k^-1*x*k eq y;
    assert k in G;

    return G!k, G!y;
    
end intrinsic;



intrinsic ConjugatorCU( G::GrpMat, x::GrpMatElt ) -> GrpMatElt,GrpMatElt
{return the matrix conjugating x to conjucacy class representative}

    require x in G : "x not in G";

    pols, parts, t := ClassInvariants(G,x);

//  that's just a short cut: 
//    if #pols eq 1 and #parts[1] eq 1 then
//        return ConjugatorCU_JordanBlock(G,x);
//    end if;

    n := Dimension(G);

    E := BaseRing(G);
    dF := Degree(E) div 2;
    F := sub<E| dF >;

    sigma := iso< E -> E | x :-> Frobenius(x,dF), x :-> Frobenius(x,dF) >;
//    T := Transpose;

    P := PolynomialRing(E); X := P.1;
    Mat := MatrixAlgebra( E, n );
    J := ZeroMatrix( E, n, n );
    for i in [1..n] do  J[i,n-i+1]:=1;  end for;

    sigmaMat := func< x | Matrix(BaseRing(x),Nrows(x),Ncols(x), [sigma(a) : a in Eltseq(x)] ) >;
    starMat := map< Mat -> Mat | x :-> J * sigmaMat(Transpose(x)) * J >;
    j := func< u,v | (u*J, Vector([sigma(a):a in Eltseq(v)])) >;
    actionOnBases := function( B, C )
      _, X := IsConsistent( Transpose(Matrix(B)),Transpose(Matrix(C)) );
      return Matrix(Transpose(X));
    end function;

    function MyJordanT(x,J,e,m)
    // x has params [f], [[m,m,m...,m]], t; deg(f) = e
    // that is, its unitary Jordan Form consists of Jordan Blocks of the same multiplicity m,
    // all w.r.t. to the same polynomial of degree e.

        E := BaseRing(x);
        me := m*e;

        function rec_fun(x,J)
            // get size first
            n := Nrows(x);
            j,jT := JordanForm(x);

            if n eq me then
                return jT;
            else

                V := VectorSpaceWithBasis(jT);
 
                // Try Basis of the first direct summand (in even case of both irred components)
                if IsOdd(e) then
                    B1 := Matrix(jT[1..me]);
                else // if IsEven(e) then
                    B1 := Matrix(jT[ [1..me div 2]cat[n div 2+1..n div 2+me div 2] ]);
                end if;
 
                V1 := VectorSpaceWithBasis(B1);
                U  := VectorSpaceWithBasis( sigmaMat(BasisMatrix(
                            NullSpace(Transpose(B1*J))
                      )));

        
                // if this ever happens, have to work around it by choosing a different V1
                while Dimension(U meet V1) ne 0 or U*x ne U do
                    Dimension(U meet V1) eq 0 , U*x eq U;
                    repeat b := Random(V); until b ne 0;
                    B1 := Matrix( [b*x^i : i in [0..me-1]] );
                    V1 := VectorSpaceWithBasis(B1);
                    U  := VectorSpaceWithBasis( sigmaMat(BasisMatrix(
                                NullSpace(Transpose(B1*J))
                          )));
                end while;
        
 
                dU := n-me;
                assert Dimension(U) eq dU;
                assert U*x eq U;
 
                // now have V = V1 \perpsum U

                // restrict  x and J  to  U
 
                xU := Matrix( [ Coordinates(U, U.i*x) : i in [1..dU] ] );
 
                JU := Matrix( [[(U.i*J,Vector([sigma(a):a in Eltseq(U.j)]))  :j in [1..dU] ] : i in [1..dU] ] );
 
                BU := rec_fun(xU,JU);
 
                B2 := BU * BasisMatrix(U);
 
                if IsOdd(e) then
                    return VerticalJoin(B1,B2);
                else
                    // first half of B1, first half of B2, second half of B1, second half of B2
                    return Matrix( B1[1..me div 2]       cat  B2[1..(n-me) div 2] cat 
                                   B1[me div 2 + 1..me]  cat  B2[(n-me) div 2 + 1..n-me] );
                end if;
            end if;

        end function;


        return rec_fun(x,J);

    end function;

    jF, g1, vf := JordanForm( x );

    // compute the offsets of the varios (normal) Jordan Blocks, so 
    // we can find the offsets of the unitary Jordan blocks later
    vf_ext := []; offset := 1;
    for tup in vf do
        Append(~vf_ext, <tup[1],tup[2],offset>);
        offset +:= tup[2]*Degree(tup[1]);
    end for;


    for polnr in [1..#pols] do
        f := pols[polnr];
        e := Degree(f);
        ms := parts[polnr];
        m := 0;
        for partnr in [1..#ms] do;
            if m eq ms[partnr] then
                continue;
            end if;
            m := ms[partnr];
            cnt := #[a:a in ms|a eq m];
            if cnt gt 1 then
                // grab the corresponding lines of g1,
                if IsOdd(e) then // equiv to IsIrreducible(f)
                    ex := exists(pos){ pos : pos in [1..#vf_ext] | tup[1] eq f and tup[2] eq m where tup is vf_ext[pos] };
                    assert ex;
                    offset := vf_ext[pos][3];

                    U := VectorSpaceWithBasis( g1[[offset..offset+m*e*cnt-1]] );

                else // IsEven(e), equiv to not IsIrreducible(f);
                    fac := Factorisation(f);
                    ex := exists(pos1){ pos : pos in [1..#vf_ext] | tup[1] eq fac[1][1] and tup[2] eq m where tup is vf_ext[pos] };
                    assert ex;
                    ex := exists(pos2){ pos : pos in [1..#vf_ext] | tup[1] eq fac[2][1] and tup[2] eq m where tup is vf_ext[pos] };
                    assert ex;

                    offset1 := vf_ext[pos1][3];
                    offset2 := vf_ext[pos2][3];

                    U := VectorSpaceWithBasis( g1[[offset1..offset1+(m*e*cnt div 2)-1] cat
                                                  [offset2..offset2+(m*e*cnt div 2)-1]] );

                end if;
                
                dU := Dimension(U);
                assert dU eq m*e*cnt;
                
                // restrict x and J to that subspace
                xs := Matrix( [ Coordinates(U, U.i*x) : i in [1..dU] ] );
 
                Js := Matrix( [[(U.i*J,Vector([sigma(a):a in Eltseq(U.j)]))  :j in [1..dU] ] : i in [1..dU] ] );
 
                // run the new function on the smaller x and J
                Bs := MyJordanT(xs,Js,e,m);
 
                // rewrite returned vectors to correspond to the old basis
                B2 := Bs * BasisMatrix(U);
                
                // replace lines of g1 by new lines
                if IsOdd(e) then // equiv to IsIrreducible(f)
                    InsertBlock(~g1, B2, offset,1); 
                else // IsEven(e), equiv to not IsIrreducible(f);
                    InsertBlock(~g1, Submatrix(B2,         1,1,dU div 2,n), offset1,1); 
                    InsertBlock(~g1, Submatrix(B2,dU div 2+1,1,dU div 2,n), offset2,1); 
                end if;
                // assert that the modified g1 still conjugates to the JNF
                
                assert g1 *x* g1^-1 eq jF;

            end if;
        end for;
    end for;

    // build a list of vector spaces fixed by the various (unitary) Jordan Blocks
    VS := [[Parent(VectorSpace(E,n))|]:i in [1..#pols]];
    for polnr in [1..#pols], partnr in [1..#parts[polnr]] do
        f := pols[polnr];
        m := parts[polnr][partnr];
        e := Degree(f);
       
        if IsOdd(e) then // equiv to IsIrreducible(f)
            ex := exists(pos){ pos : pos in [1..#vf_ext] | tup[1] eq f and tup[2] eq m where tup is vf_ext[pos] };
            assert ex;
            offset := vf_ext[pos][3];
                      vf_ext[pos][1] := 0; // mark as used

            VS[polnr][partnr] := VectorSpaceWithBasis( g1[[offset..offset+m*e-1]] );

        else // IsEven(e), equiv to not IsIrreducible(f);
            fac := Factorisation(f);
            ex := exists(pos1){ pos : pos in [1..#vf_ext] | tup[1] eq fac[1][1] and tup[2] eq m where tup is vf_ext[pos] };
            assert ex;
            ex := exists(pos2){ pos : pos in [1..#vf_ext] | tup[1] eq fac[2][1] and tup[2] eq m where tup is vf_ext[pos] };
            assert ex;

            offset1 := vf_ext[pos1][3];
            offset2 := vf_ext[pos2][3];
                       vf_ext[pos1][1] := 0; // mark as used
                       vf_ext[pos2][1] := 0; // mark as used

            VS[polnr][partnr] := VectorSpaceWithBasis( g1[[offset1..offset1+(m*e div 2)-1] cat
                                                          [offset2..offset2+(m*e div 2)-1]] );

        end if;
    end for;

    B := Mat!0; // these are built up within the next for loop
    C := Mat!0;
    outer_offset := 1;
    odd_used := false;

    for polnr in [1..#pols], partnr in [1..#parts[polnr]] do
        f := pols[polnr];
        m := parts[polnr][partnr];
        e := Degree(f);
        me := m*e;


        Vsub := VS[polnr][partnr];
        Bsub := Basis(Vsub);

        Jstd := Submatrix(J,1,n-me+1,me,me);
        Jsub := Matrix(E, me,me, [ j(Bsub[i],Bsub[i2]) : i, i2 in [1..me]]);
        // Transform matrix s.t. Tr * Jsub * sigmaMat(Transpose(Tr)) eq Jstd
        Tr := TransformForm(Jsub,"unitary")^-1;
        assert Tr * Jsub * sigmaMat(Transpose(Tr)) eq Jstd;

        Bnew := Matrix(Tr)*Matrix(Bsub); // [ &+[ Bsub[i]*Tr[i,i2] : i in [1..me] ] : i2 in [1..me] ];
        
        // make sure Bnew is a unitary basis.
        assert forall{<i,i2>:i,i2 in [1..me]|j(Bnew[i],Bnew[i2]) eq Jstd[i,i2]};
//      same assertion, but slower, but user readable:
//        assert Jstd eq 
//            Matrix( [[ j(Bnew[i],Bnew[i2]) :i2 in [1..me]]:i in [1..me]] );
        
        // same vector space with a new basis.
        Vnew := VectorSpaceWithBasis(Bnew);
        assert Vnew eq Vsub; 

        xVnew := Matrix( E, me,me, [ Coordinates( Vnew, Vnew.i * x ): i in [1..me] ] );
        Gsub := CU(me,E);
        assert xVnew in Gsub;

        gsub := ConjugatorCU_JordanBlock( Gsub, Gsub!xVnew ) ;
        assert gsub in Gsub;

        gonB := Matrix(gsub) * Matrix(Bnew);


//         if IsOdd(e) and e gt 1 then
//             // we may have to correct the "c" in here.
//             ysub   := CompanionMatrixU(f,F,t);
//             expect := ysub[e div 2 + 2,e div 2 + 1];
//             have   := ((gsub^-1)[e div 2 + 2]*xVnew,Transpose(gsub)[e div 2 + 1]) ;
//         end if;

        /*
         * SH: we have to (re)implement or reuse the square direct sume here.
         *     otherwise the ordering of the different jordan blocks isn't correct.
         */

        if IsOdd(me) then
            if odd_used then
                 error "At the moment at most one odd-dim Jordan block allowed";
            end if;
            odd_used := true;
            // put Bnew in the center of B and gonB in the center of C.
            // assume n is odd. if it is even, we get an error in a later run with odd_used.
            InsertBlock(~B,Matrix(Bnew),(n-me) div 2 + 1, 1); 
            InsertBlock(~C,   gonB,     (n-me) div 2 + 1, 1); 
        else // IsEven(me)
            // put Bnew on the "outside" of B and gonB on the "outside" of C.
            InsertBlock(~B,Matrix(Bnew[1..me div 2]),outer_offset, 1);
            InsertBlock(~C,Matrix(gonB[1..me div 2]),outer_offset, 1);
            InsertBlock(~B,Matrix(Bnew[me div 2+1..me]),n-outer_offset-(me div 2)+2, 1);
            InsertBlock(~C,Matrix(gonB[me div 2+1..me]),n-outer_offset-(me div 2)+2, 1);
            
            outer_offset +:= me div 2;
        end if;

    end for;

    assert B in G; B:=G!B;
    assert C in G; C:=G!C;

    gA := actionOnBases( B, C );
    assert gA in G; gA:=G!gA;

    g := gA * B^-1;

    assert g in G; g := G!g;

    y := ClassRepresentativeFromInvariants(G,pols,parts,t);

    assert G!x^g eq y;

    return g, y;
    
end intrinsic;


/*

time exists(c){ c : c in Afm | c * starmap(c,m) eq Afm!Eltseq(a) };
time exists(c){ c : c in Afm | c * starmap(c,m) eq Afm!Eltseq(a) 
                               and  y mod f eq 0 
                               where y is P!(c*Afm!Eltseq(c0^-1) - 1)  };

*/














