freeze;

/*
Code for Z_4 codes.
Initially by Allan Steel, July 2001.
*/

Z4 := IntegerRing(4);
Z := IntegerRing();

/******************************************************************************
                            Lee Distance
*******************************************************************************/

intrinsic LeeDistance(v::ModTupRngElt, u::ModTupRngElt) -> RngIntElt
{Return the Lee distance between the vectors v and w}
    R := BaseRing(Parent(v));
    require R eq BaseRing(Parent(u)) and #R eq 4 and not IsField(R): 
                                        "Vectors should be over Z4";
    return LeeWeight(v - u);
end intrinsic;


/*******************************************************************************
			    Checks
*******************************************************************************/

over_Z4 := func<C | Alphabet(C) cmpeq Z4>;
over_field := func<C | Type(Alphabet(C)) eq FldFin>;

/*******************************************************************************
			    Hensel stuff
*******************************************************************************/

function Coerce(f, P)
    Z := Integers();
    R := BaseRing(P);
    return &+ [ R!([Z| j : j in Eltseq(c[i])]) * (P.1)^(i-1) : i in [1..#c]]
                                where c := Coefficients(f);
end function;

intrinsic CyclotomicFactors(R::Rng, n::RngIntElt) -> []
{Return the factors of (x^n - 1) over R, a Galois ring (or integers modulo
a prime power). n must be coprime to the characteristic of R.}

    require n ge 1 and GCD(Characteristic(R), n) eq 1 :
                "n must be positive and coprime to the characteristic of R";

    if n eq 1 then
	return [ PolynomialRing(R).1 - 1 ];
    end if;

    case Type(R):
        when RngIntRes:
            require #Factorisation(#R) eq 1:
		"Modulus of integer residue ring must be a prime power";
            x := PolynomialRing(IntegerRing()).1;
            M := #R;
            p := PrimeDivisors(M)[1];
            z := PolynomialRing(GF(p)).1;
            L := [t[1]: t in Factorization(z^n - 1)];
            H := HenselLift(x^n - 1, L, PolynomialRing(R));
            return H;

        when RngGal:
            char_F := Factorisation(Characteristic(R));
            p := char_F[1][1];
            k := char_F[1][2];
            e := Degree(R);
            L := ext<pAdicRing(p, k) | e>;
            P := PolynomialRing(L);
            x := P.1;
            f := x^n - 1;
            F := ResidueClassField(L);
            Facts := Factorisation( PolynomialRing(F)!f);
            h := HenselLift(f, [P| fact[1] : fact in Facts]);

            P1 := PolynomialRing(R);
            return [ Coerce( h[i], P1) : i in [1..#h] ];

        else:   
            require false: "Must be a Galois ring or integer residue ring";
    end case;

end intrinsic;


function Recip(f)
    return Parent(f) ! Reverse(Eltseq(f));
end function;

// RM(1, m) mod 2
function Kerdock(h)
    R := BaseRing(Parent(h));
    m := Degree(h);
    n := 2^m - 1;
    X := PolynomialRing(R).1;
    g := (X^n - 1) div (X - 1);
    assert g mod h eq 0;
    g := g div h;
    g := Recip(g);
    K := CyclicCode(n, g);
    KP := ExtendCode(K);
    return KP;
end function;

function BasicPrimitive(m, n)
        //basic primitive poly of degree m dividing x^n-1
    P := PolynomialRing(GF(2));
    L := CyclotomicFactors(Z4, n);
    return rep{f: f in L | Degree(f) eq m and IsPrimitive(P!f)};
end function;


/*******************************************************************************
                            Kerdock Code
*******************************************************************************/

intrinsic KerdockCode(m::RngIntElt) -> CodeLinRng
{The quaternary Kerdock Code K(m), defined by a default primitive polynomial}
    requirege m, 2;

    P := PolynomialRing(GF(2));
    L := CyclotomicFactors(Z4, 2^m - 1);
    h := rep{f: f in L | Degree(f) eq m and IsPrimitive(P!f)};

    return Kerdock(h);
end intrinsic;

/*******************************************************************************
                            Preperata Code
*******************************************************************************/

// RM(m - 2, m) mod 2
function Preparata(h)
    R := BaseRing(Parent(h));
    m := Degree(h);
    n := 2^m - 1;
    P := CyclicCode(n, h);
    PP := ExtendCode(P);
    return PP;
end function;

intrinsic PreparataCode(m::RngIntElt) -> CodeLinRng
{The quaternary Preparata Code P(m), defined by a default primitive polynomial}
    requirege m, 2;

    P := PolynomialRing(GF(2));
    L := CyclotomicFactors(Z4, 2^m - 1);
    h := rep{f: f in L | Degree(f) eq m and IsPrimitive(P!f)};

    return Preparata(h);
end intrinsic;

/*******************************************************************************
                            Reed-Muller Code
*******************************************************************************/

w2 := func< x | &+ Intseq(x,2,1) >;

function Z4ReedMuller( h, r, m)
    Z4 := Integers(4);
    n := 2^m-1;

    GR := GaloisRing( 4, PolynomialRing(Integers())!h);
    P := PolynomialRing(GR);
    g := &* [P| 1 - P.1*GR.1^j : j in [1..2^m-2] | w2(j) gt r ];
    g := PolynomialRing(Z4) ! [ Eltseq(a)[1] : a in Coefficients(g) ];
    C := ExtendCode( CyclicCode(n, g) );
    return C;
end function;


intrinsic ReedMullerCodeZ4( r::RngIntElt, m::RngIntElt) -> CodeLinRng
{Return the r-th order Reed-Muller code over Z4 of length 2^m}
    requirege m, 2;
    requirerange r, 0, m;

    h := BasicPrimitive(m, 2^m-1);
    return Z4ReedMuller( h, r, m);

end intrinsic;

/*******************************************************************************
                            Goethals Codes
*******************************************************************************/

function PowerBlock( GR, n, inc )
   
    m := Degree(GR);
    G := RMatrixSpace(Z4, m, n)!0;
    for i in [0..n-1] do
        InsertBlock(~G, Matrix(Z4, m, 1, Eltseq(GR.1^(i*inc))), 1, i+1);
    end for;

    return G;
end function;


intrinsic GoethalsCode( m::RngIntElt ) -> CodeLinRng
{Return the Goethals code of length 2^m}
    require ((m mod 2) eq 1) and m ge 3: "m must be an odd integer greater than or equal to 3";

        //r = 1
    return GoethalsDelsarteCode( m, ((m + 1) div 2) - 1);
end intrinsic;


intrinsic DelsarteGoethalsCode( m::RngIntElt, delta::RngIntElt ) -> CodeLinRng
{Return the Delsarte-Goethals Code of length 2^m}
    require ((m mod 2) eq 1) and m ge 3: "m must be an odd integer greater than 
or equal to 3";
    requirerange delta, 1, (m-1) div 2;

    h := BasicPrimitive(m, 2^m-1);
    n := 2^m - 1;
    r := ( (m+1) div 2 ) - delta;

    GR := GaloisRing( 4, PolynomialRing(Integers())!h);

    G := Matrix( Z4, (r+1)*m+1, n+1,
            [1 : i in [1..n+1]] cat [0 : i in [1..(r+1)*m*(n+1)]]);

    InsertBlock(~G, PowerBlock(GR, n, 1), 2, 2);
    for j in [1..r] do
        InsertBlock(~G, 2*PowerBlock(GR, n, 1+2^j), j*m+2, 2);
    end for;

    return LinearCode(G);
end intrinsic;


intrinsic GoethalsDelsarteCode( m::RngIntElt, delta::RngIntElt) -> CodeLinRng
{Return the Goethals-Delsarte code of length 2^m}
    require ((m mod 2) eq 1) and m ge 3: "m must be an odd integer greater than 
or equal to 3";
    requirerange delta, 1, (m-1) div 2;

    return Dual(DelsarteGoethalsCode( m, delta ));
end intrinsic;


/*******************************************************************************
                            Quadratic Residue Code
*******************************************************************************/

intrinsic QRCodeZ4(p::RngIntElt) -> CodeLinRng
{Return the quadratic residue code of length p over Z4}

    require p gt 0 and IsPrime(p): "p must be a positive prime number";
    require (p mod 8) in {1,7} : "2 is not a quadratic residue mod p";

    F := GF(2);
    P := PolynomialRing(F); x := P.1;

    alpha := RootOfUnity(p, F);
    QuadRes := { a^2 mod p : a in [1..(p-1) div 2] };

    SP := PolynomialRing(Parent(alpha));
    g2 := P ! &* [SP.1 - alpha^r : r in QuadRes ];
    h2 := P ! &* [SP.1 - alpha^r : r in {1..p-1} diff QuadRes];

    PP := PolynomialRing(Integers(4)); y := PP.1;
    f := (y^p-1) div (y-1);

    facts := HenselLift(PolynomialRing(Z)!f, [g2, h2], PP);
    g := facts[1]; 
    h := facts[2];

    return CyclicCode(p, g);
end intrinsic;


intrinsic GolayCodeZ4(e::BoolElt) -> CodeLinRng
{Return the Golay Code over Z4. If e is true then return the extended
Golay Code};

    C := QRCodeZ4(23);
    if e then
        C := ExtendCode(C);
    end if;

    return C;
end intrinsic;


/************************************************************************
			    Simplex Codes
*************************************************************************/

function AlphaSimplexMat(k)
    Rows := [];
    len := 2^(2*k);
    for i in [0..k-1] do
        Append(~Rows, Matrix( Z4, 1, len, &cat[&cat[ [l : j in
                    [1..2^(2*(k-i-1))]] : l in [0..3]] : m in [1..2^(2*i)]]));
    end for;

    Gen := VerticalJoin(Rows);

    return Gen;
end function;

intrinsic SimplexAlphaCodeZ4(k::RngIntElt) -> CodeLinRng
{Return the Simplex Alpha Code over Z4 of degree k};

    return LinearCode(AlphaSimplexMat(k));
end intrinsic;

function BetaSimplexMat(k)
    if k eq 2 then
        return  Matrix(Z4, 2, 6, [ 1,1,1,1, 0,2,  0,1,2,3, 1,1]);
    end if;
    len := 2^(k-1)*(2^k-1);
    a := Matrix( Z4, 1, len, [1: j in [1..2^(2*k-2)]] cat
                    &cat[ [l : j in [1..2^(k-2)*(2^(k-1)-1)]] : l in [0,2]]);
    b := HorizontalJoin( <AlphaSimplexMat(k-1),
                    BetaSimplexMat(k-1), BetaSimplexMat(k-1) > );

    Gen := VerticalJoin(a,b);

    return Gen;
end function;

intrinsic SimplexBetaCodeZ4(k::RngIntElt) -> CodeLinRng
{Return the Simplex Beta Code over Z4 of degree k};

    return LinearCode(BetaSimplexMat(k));
end intrinsic;


/*******************************************************************************
			    Standard form auxiliary
*******************************************************************************/

intrinsic StandardForm(C::CodeLin) -> CodeLinRng, Map
{The standard form S of C together with the isomorphism map f: C -> S}
    if over_field(C) then
	return StandardFormField(C);
    end if;
    require over_Z4(C): "Code is not over a field or Z_4";

    S, k1, T, p := StandardFormInfo(C);

    CC := LinearCode(S);
    f := map<C -> CC | v :-> v^p, w :-> w^(p^-1)>;
    return CC, f;
end intrinsic;

/*
function get_ABCTp(C)
    S, k1, T, p := StandardFormInfo(C);

    k2 := Nrows(S) - k1;
    k3 := Ncols(S) - k1 - k2;
    A := Submatrix(S, 1, k1 + 1, k1, k2);
    B := Submatrix(S, 1, k1 + k2 + 1, k1, k3);
    C := Submatrix(S, k1 + 1, k1 + k2 + 1, k2, k3);
    C := Parent(C) ! [Z!x div 2: x in Eltseq(C)];
// "Now C:", C;

    return A, B, C, T, p;
end function;
*/

/*******************************************************************************
			    Gray Map functions
*******************************************************************************/

GraySeq := [[0,0], [0,1], [1,1], [1,0]];
BetaSeq := [0, 0, 1, 1];
GammaSeq := [0, 1, 1, 0];

GrayInvSeq := [0, 3, 1, 2];

map_alpha := func<x | Z!x mod 2>;
map_beta := func<x | BetaSeq[Z!x + 1]>;
map_gamma := func<x | GammaSeq[Z!x + 1]>;

F2 := GF(2);
get_map := func<f |
    func<X | Matrix(F2, Nrows(X), Ncols(X), [f(x): x in Eltseq(X)])>>;
map_alpha_mat := get_map(map_alpha);
map_beta_mat := get_map(map_beta);
map_gamma_mat := get_map(map_gamma);

function GrayVec(v)
    n := Degree(Parent(v));
    return Vector(GF(2), &cat[GraySeq[Z!v[i]+1]: i in [1..n]]);
end function;

function GrayMat(X)
    return Matrix([GrayVec(X[i]): i in [1 .. Nrows(X)]]);
end function;

function GrayMapCodomain(C, V)
    n := Length(C);
    f := map<C -> V |
	x :-> GrayVec(x),
	y :-> C![GrayInvSeq[Z!y[2*i - 1] + 2*Z!y[2*i] + 1]: i in [1 .. n]]
    >;
    return f;
end function;

intrinsic GrayMap(C::CodeLinRng) -> Map
{Return the Gray map for the code C}
    require over_Z4(C): "Code is not over Z_4";
    n := Length(C);
    V := VectorSpace(GF(2), 2*n);
    return GrayMapCodomain(C, V);
end intrinsic;

intrinsic GrayMapImage(C::CodeLinRng) -> []
{Return the image of the Z_4 code C under the Gray map, as a sequence of
vectors}
    require over_Z4(C): "Code is not over Z_4";
    f := GrayMap(C);
    return [f(x): x in C];
end intrinsic;

intrinsic GrayMap(v::ModTupRngElt) -> ModTupFldElt
{Given a Z_4 vector v, return the image of under the Gray map, as a vector
over GF(2)};
    require BaseRing(Parent(v)) cmpeq Z4: "Vector is not over Z_4";
    return GrayVec(v);
end intrinsic;

intrinsic HasLinearGrayMapImage(C::CodeLinRng) -> BoolElt, Code
{Return true iff the image of the Gray map of the Z_4 code C is a linear
GF(2) code; if so, return also the image code}

    require over_Z4(C): "Code is not over Z_4";

    V := AmbientSpace(C);
    B := Basis(C);
    for v in B do
	for w in B do
	    u := V![2*map_alpha(v[i])*map_alpha(w[i]): i in [1 .. Ncols(v)]];
	    if u notin C then
		return false, _;
	    end if;
	end for;
    end for;

    OC := C;

    if #B eq 0 then
	// Zero code, only contains one value (the all-zero vector)
	J := Matrix([ GrayVec(c) : c in C ]);
    else
	J := Matrix(&cat[[GrayVec(v), GrayVec(-v)]: v in B]);
    end if;
    G := LinearCode(J);
    return true, G, GrayMapCodomain(OC, G);

    /*
    A, B, C, T, p := get_ABCTp(C);

    k1 := Nrows(A);
    k2 := Nrows(C);

    Ik1 := MatrixRing(F2, k1) ! 1;
    Ik2 := MatrixRing(F2, k2) ! 1;
    Zk1 := MatrixRing(F2, k1) ! 0;
    Zk2 := MatrixRing(F2, k2) ! 0;
    Zk12 := RMatrixSpace(F2, k1, k2) ! 0;
    Zk21 := RMatrixSpace(F2, k2, k1) ! 0;

    alpha := map_alpha_mat;
    beta := map_beta_mat;
    gamma := map_gamma_mat;

    J1 := HorizontalJoin(< Ik1, alpha(A), alpha(B),  Ik1, alpha(A), alpha(B)>);
    J2 := HorizontalJoin(<Zk21,      Ik2, alpha(C), Zk21,      Ik2, alpha(C)>);
    J3 := HorizontalJoin(< Zk1,     Zk12,  beta(B),  Ik1, alpha(A), gamma(B)>);

    J := VerticalJoin(<J1, J2, J3>);
    G := LinearCode(J);

    return true, G, GrayMapCodomain(OC, G);
    */
end intrinsic;


/******************************************************************************
                           Residue and Torsion derived codes
*******************************************************************************/


intrinsic BinaryResidueCode(C::CodeLinRng) -> Code
{From the quaternary code C, return the binary residue code formed by
taking each codeword in C modulo 2};
    require over_Z4(C): "Code is not over Z_4";
    return LinearCode( Matrix(GF(2),GeneratorMatrix(C)) );
end intrinsic;

intrinsic BinaryTorsionCode(C::CodeLinRng) -> Code
{From the quaternary code C, return the binary torsion code formed by
the support of each codeword in C which is zero modulo 2};
    require over_Z4(C): "Code is not over Z_4";

    KS := KSpace(GF(2),Length(C));
    Gens := {};
    for gen in Generators(C) do
        if IsZero(Matrix(GF(2),gen)) then
            sup := Support(gen);
        else
            sup := Support(2*gen);
        end if;
        new_gen := KS! [ i in sup select 1 else 0 : i in [1..Length(C)]];

        Include(~Gens, new_gen);
    end for;

    return LinearCode< GF(2), Length(C) | Gens>;
end intrinsic;

intrinsic Z4CodeFromBinaryChain( C1::CodeLinFld, C2::CodeLinFld ) -> CodeLinRng
{From the binary subcode chain C1, C2, return a quaternary code such 
that its binary residue code is C1 and its binary torsion code is C2.};

    require Alphabet(C1) eq GF(2) and Alphabet(C2) eq GF(2) :
                "Codes must be over GF(2)";
    require C1 subset C2: "C1 must be a subcode of C2";

    Z := Integers();
    Z4 := Integers(4);
    G := Zero(RMatrixSpace(Z4, Dimension(C2), Length(C2) ));
    InsertBlock(~G, Matrix(Z4,Matrix(Z,GeneratorMatrix(C1))), 1, 1);
    M := BasisMatrix(Complement(RSpace(C2),RSpace(C1)));
    InsertBlock(~G, Matrix(Z4, 2*Matrix(Z, M)), Dimension(C1) + 1, 1);

    return LinearCode(G);

end intrinsic;


/******************************************************************************
                      Correlation 
*******************************************************************************/

intrinsic Correlation(v::ModTupRngElt) -> RngQuadElt
{Return the correlation of the codeword v over the integers modulo 4.
The result is a gaussian integer (see handbook for full definition).};
    require BaseRing(v) eq Z4: "Codeword is not over Z_4";

    content := [Z|0,0,0,0];
    for i in [1..Ncols(v)] do
        content[1+Z!(v[i])] +:= 1;
    end for;

    ZI := GaussianIntegers();

    return (content[1] - content[3]) + ZI.2*(content[2] - content[4]);
end intrinsic;
