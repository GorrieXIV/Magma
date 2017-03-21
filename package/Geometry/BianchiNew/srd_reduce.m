freeze;

//  Reduction for elements of hyperbolic 3-space
//
//  Steve Donnelly, November 2013


import "../CrvG1/g1reduction_nf.m" :
    covariants_C, 
    get_cd, 
    get_ab;


// h is a Hermitian matrix h over K,
// returns a transformation matrix

// B = basis matrix of image of ZK in C 
//   = [ 1 0 // re(w) im(w) ]


function srd_reduce(h, ZK, B)

    K := NumberField(ZK);
    conj := K`Conjugate;
     
    prec := Precision(BaseRing(B));
    
    hC := Matrix(2, [Conjugate(x, 1 : Precision:=prec) : x in Eltseq(h)]);

    ok, cov := covariants_C([hC], prec);
    assert ok;

    ok, c, d := get_cd([], cov, B, ZK : num:=1, optimize:="height");
    assert ok;
    if not ok then
        return h, IdentityMatrix(ZK, 2);
    end if;
 
    a, b := get_ab(c, d);
    assert a*d - b*c eq 1;

    T1r := Matrix(2, [K| d, -b, -c, a]);
    T1l := Matrix(2, [conj(d), conj(-c), conj(-b), conj(a)]);

    h1 := T1l * h * T1r;

    // translate (easy)

    z := Eltseq(FieldOfFractions(ZK) ! (-h1[2,1] / h1[1,1]));
    z := ZK ! [Round(z[1]), Round(z[2])];

    T2l := Matrix(2, [K| 1, 0, z, 1]);
    T2r := Matrix(2, [K| 1, conj(z), 0, 1]);

    h2 := T2l * h1 * T2r;

/*
"srd_reduce";
Eltseq(h);
Eltseq(T1l);
Eltseq(h1);
Eltseq(T2l);
Eltseq(h2);
*/

    return h2, T2l * T1l;

end function;

