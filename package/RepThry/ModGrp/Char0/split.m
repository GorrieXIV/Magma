freeze;

/*
Computing a maximal order of a central split algebra.
Gabi Nebe and Allan Steel, 2008.
*/

/*******************************************************************************
			     Misc
*******************************************************************************/

declare attributes AlgMat: MaximalOrderInfo;

Z := IntegerRing();
Q := RationalField();

FMP := func<X | FactoredMinimalPolynomial(X: Proof := false)>;

function rescale_basis(B)
    max := Max([Norm(v): v in B]);
    return [Round(max / Norm(v))*v: v in B];
end function;

/*******************************************************************************
			    Extend by prime
*******************************************************************************/

function make_module(GFp, RM1)
    // Take both right and left regular reps for twosided ideals:

    RM1 := [Matrix(GFp,X) : X in RM1];
    L := RM1;

    e := Nrows(RM1[1]);
    for i in [1..e] do
	X := Parent(RM1[1]) ! 0;
	for j, k in [1..e] do
	    X[j][k]:=RM1[j][i][k];
	end for;
	Append(~L,X);
    end for;

/*
"first #L:", #L;
"Ech L";
time L:=EchelonForm(Matrix(L));
time L:=[Matrix(e, e, Eltseq(x)): x in Rows(L) | not IsZero(x)];
"now #L:", #L;

A := sub<MatrixRing(GFp,e)|L>;
A;
"dim:";
time d1:=Dimension(A);
d1;
AA := sub<MatrixRing(GFp,e)| [Random(A): i in [1..10]]>;
"new dim:";
time d2:=Dimension(AA);
d2;

if d2 eq d1 then return RModule(AA); end if;
*/

    return RModule(L);
end function;

procedure extend_by_prime(S, Mp, ~RB1, ~RM1, ~new_order)

    GFp := BaseRing(Mp);
    p := #GFp;
    e := Dimension(Mp);
    e2 := e^2;

//Calculate the right idealiser of S

    J := VerticalJoin(Matrix(Z, Morphism(S, Mp)), MatrixRing(Z,e)!p);
    R1 := BasisMatrix(Rowspace(J));
    delete J;
    R1i2, denom := PseudoInverse(Matrix(R1));

    SysEq := [];
    for i in [1..e] do
	X := (R1*RM1[i]*R1i2) div denom;
	X := Transpose(Matrix(GFp, X));
	SysEq cat:= Eltseq(X);
	delete X;
    end for;
    delete R1, R1i2;

    SysEq := KMatrixSpace(GFp,e,e^2) ! SysEq;
    KK := KernelMatrix(SysEq);
    delete SysEq;

    if Nrows(KK) eq 0 then 
	return;
    end if;

    //found submodule that has a bigger idealiser
    J := VerticalJoin(Matrix(Z,KK), MatrixRing(Z,e)!p);
    R := Matrix(BasisMatrix(RowSpace(J)));
    delete J;
    assert Nrows(R) eq e;

    RS1:=(1/p*Matrix(Q,R));
    RB1:=RS1*RB1;

    //RS1i:=RS1^(-1);
    RS1i, denom := PseudoInverse(R);

    //Calculate new regular representation

if 1 eq 1 then
    BB := [];
    for j in [1..e] do
	X := R * RM1[j] * RS1i;
	X := X div denom;
	//BB cat:= Eltseq(X);
	Append(~BB, X);
    end for;
    //BB := Matrix(Z, e, e^2, BB);
    BB := Matrix(BB);

    BB := R*BB;
    RM1 := [Matrix(Z, e, e, Eltseq(BB[i])) div p: i in [1 .. e]];

else

    BBZ:=[];
    for j in [1..e] do
	//X := RS1 * Matrix(Q,RM1[j]) * RS1i;
	X := R * RM1[j] * RS1i;
	X := X div denom;
	Append(~BBZ, Matrix(Z, X));
    end for;

    RM1:=[];

    for j in [1..e] do

	ss:=MatrixRing(Z,e) ! 0;
	for k in [1..e] do ss +:= R[j][k]*BBZ[k]; end for;
	ss := ss div p;
	Append(~RM1, ss);
	//assert s eq ss;

    end for;
end if;

    new_order:=true;
end procedure;

intrinsic FindSplitElement(
    E::AlgMat: DistinctFactors := false, Disc := 0, CentreDim := 0,
    SplitSearch
) -> AlgMatElt
{Try to find element S of E (assuming E is an integral
endomorphism ring) such that the minimal polynomial of S has at least
2 distinct irreducible factors; return 0 if not found.}

    require BaseRing(E) cmpeq Z: "Algebra must be over integers";
    require 1 in E: "Algebra must have 1";

/* 
Calculates a maximal order, a small basis in its regular representation
and tries to find a singular element in the endomorphism ring, if it exists.
*/

    vprint ZMeataxe: "Get Endo dim";
    vtime ZMeataxe: e := Dimension(E);
    vprint ZMeataxe: "Endo dim", e;
    totaldim:=e;
    BE:=Basis(E);

    if CentreDim gt 0 then
	d := CentreDim;
	m := Isqrt(e div d);
	require d*m^2 eq e: "Algebra is not central simple";
	rootofdimKofE := m;
	D := 1;
	K := 0;
    else
	vprint ZMeataxe: "Get Centre";
	vtime ZMeataxe: C := Centre(E);
	d := Dimension(C);
	vprint ZMeataxe: "Centre dim", d;

	m := Isqrt(e div d);
	require d*m^2 eq e: "Algebra is not central simple";
	rootofdimKofE := m;

	vprint ZMeataxe: "rootofdimKofE:", rootofdimKofE;

	is_good := func<X | Degree(MinimalPolynomial(X: Proof := false)) eq d>;
	alpha := 0;
	BC := LLL(Basis(C));
	for X in BC do
	    if is_good(X) then
		alpha := X;
		break;
	    end if;
	end for;
	if alpha eq 0 then
	    range := 1;
	    repeat
		alpha := &+[Random(-range, range)*X: X in BC];
		range +:= 1;
	    until is_good(alpha);
	end if;
	delete BC;

	//Disc:=1;
	f := MinimalPolynomial(alpha);

    //vprint ZMeataxe: "alpha:", alpha;
	 vprint ZMeataxe: "f:", f;
	 // vprint ZMeataxe: "K:", K;

	require IsIrreducible(f): "Algebra is not central simple";
	 K := NumberField(f);
	 if Disc ne 0 then
	    D := Disc;
	 else
	     D := Discriminant(RingOfIntegers(K));
	 end if;
    end if;

     vprint ZMeataxe: "Get algebra";
     vtime ZMeataxe: A, Af := Algebra(E);

     vprint ZMeataxe: "Get regular rep";
     vtime ZMeataxe: ER, ERf := RegularRepresentation(A);

     vprint ZMeataxe: "Get Basis";
     vtime ZMeataxe: B:=Basis(ER);

     /*
     R = ROI(K).
     DR = Discriminant of Mat_m(R).
     */

     DR := D^(m^2);

     vprint ZMeataxe: "D:", D;
     vprint ZMeataxe: "DR:", DR;

       F := MatrixRing(Z, e)!0;
       for i  in [1..e] do
          for j in [i..e] do
           F[i,j] := TraceOfProduct(B[i], B[j]);
           F[j,i] := F[i,j];
          end for;
       end for;
       FF := Parent(F)![ExactQuotient(x, m): x in Eltseq(F)];
     vprint ZMeataxe: "DFF",Determinant(FF);
     DFF := ExactQuotient(Determinant(FF), DR);
     L := Factorization(DFF);

     vprint ZMeataxe: "DFF:", DFF;
     vprint ZMeataxe: "Factorization:", L;

realsi := 0;
//Calculate the real Schur Index, if K is totally real
// realsi = 0, if K is not totally real 
// realsi = 1, if the real Schur Index is 1
// realsi = -1, if the real Schur Index is 2
     if K cmpne 0 and IsTotallyReal(K) then 
         S,T:=OrthogonalizeGram(F);
         dm:=0; dp:=0;
         for i in [1..e] do
           if S[i][i] gt 0 then dp +:=1; end if;
           // if S[i][i] lt 0 then dm +:=1; end if;
         end for;
         mm:= d*m*(m-1) div 2;
         mp:= d*m*(m+1) div 2;
          richtig := false;
         if dp eq mp then realsi := 1; richtig := true; end if;
         if dp eq mm then realsi := -1; richtig := true; end if;
         if not richtig then 
             vprint ZMeataxe: "m :",m;
             vprint ZMeataxe: "d :",d;
             vprint ZMeataxe: "dp :",dp;
             vprint ZMeataxe: "dm :",dm;
         end if;
     end if; 
     vprint ZMeataxe: "RealSchurIndex :",realsi;

     //if Abs(DFF) eq 1 then
       //return E,realsi;
     //end if;

     EO := ER;
     RM1:=B;
     RB1:=MatrixRing(Z,e) ! 1;


     for pt in L do
       p := pt[1];
       GFp := GF(p);

       vprint ZMeataxe: "Prime p:", p;
        number:=0;
        new_order := true;
        while new_order do
          number +:= 1;
        new_order:=false;

	Mp := make_module(GFp, RM1);
	maxsub := MaximalSubmodules(Mp);

           vprint ZMeataxe: "#maxsub:", #maxsub;
            S:=maxsub[1];
            for si in [2..#maxsub] do 
               S:=S meet maxsub[si];
             end for;

	    /*
	    // assert S eq JacobsonRadical(Mp);
	    S := JacobsonRadical(Mp);
	    vprint ZMeataxe: "JacobsonRadical:", S;
	    */

	    extend_by_prime(S, Mp, ~RB1, ~RM1, ~new_order);

        end while;
       vprint ZMeataxe: "Number of Times through 1 :", number;
       vprint ZMeataxe: "for Prime :", p;
     end for; //p in L

     det:=Determinant(RB1);
     vprint ZMeataxe: "det,DFF*d^2";
     vprint ZMeataxe: det,DFF*det^2;
     DFFhereditary:=Z ! (DFF*det^2);
     vprint ZMeataxe: "New DFF:", DFFhereditary;

     //if Abs(DFFhereditary) eq 1 then
       //return 1,realsi;
     //end if;

// "After 1 RM1:", RM1;

     L := Factorization(DFFhereditary);
     vprint ZMeataxe: "New Factorization:", L;

// we know that now the order is hereditary. 
// idealiser of a maximal ideal then yields an overorder. 
     for pt in L do
       p := pt[1];
       GFp := GF(p);

       vprint ZMeataxe: "Prime p:", p;
        number:=0;

        new_order := true;
        while new_order do
          number +:= 1;
        new_order:=false;

	Mp := make_module(GFp, RM1);

           maxsub := MaximalSubmodules(Mp);
           vprint ZMeataxe: "#maxsub:", #maxsub;
            for si in [1..#maxsub] do 
               S:=maxsub[si];

	    extend_by_prime(S, Mp, ~RB1, ~RM1, ~new_order);

             end for; //si
        end while;  // new order found
       vprint ZMeataxe: "Number of Times through 2 :", number;
       vprint ZMeataxe: "for Prime :", p;
    end for; //p in L

// "After 2 RM1:", RM1;
     det:=Determinant(RB1);
     vprint ZMeataxe: "det,DFF*d^2";
     vprint ZMeataxe: det,DFF*det^2;
     DFFmax:=Z ! (DFF*det^2);
     vprint ZMeataxe: "New DFFmax:", DFFmax;

     //if Abs(DFFmax) eq 1 then
       //return 1,realsi;
     //end if;

     L := Factorization(DFFmax);
     vprint ZMeataxe: "New Factorization:", L;

SSP:=[];

    if K cmpne 0 then
     ss := 1; // it is the LCM of the local schurindices
     if realsi eq -1 then ss:=2; end if;
     for pt in L do
       p := pt[1];
       dp := Decomposition(K,p);
       normexponent := ExactQuotient(d, dp[1][2]); // d = deg(K)
       // So normexponent = number of primes over p times the exponent of the norm of one primideal over p 
       m2m := ExactQuotient(pt[2],  normexponent); // should be m(m-tp) 
       m2m:=ExactQuotient(m2m,rootofdimKofE);
       m2m:=-m2m + rootofdimKofE;
//"rootofdimKofE:", rootofdimKofE;
//"m2m:", m2m;
       ssp:=ExactQuotient(rootofdimKofE,m2m);
        Append(~SSP,[p,ssp]);
       ss:=LCM(ssp,ss);
     end for;

	vprint ZMeataxe: "Schur index:", ss;
	vprint ZMeataxe: "Muliplicity with Schur index m:", m;
	vprint ZMeataxe: "Should split:", ss lt m;
    else
	vprint ZMeataxe: "Skip schur index";
	ss := -1;
	m := -1;
    end if;

    if 1 eq 1 then

	denom := LCM([Denominator(x): x in Eltseq(RB1)]);
	RB1 := RB1*denom;

	vprint ZMeataxe: "Maximal order denom:", denom;

	O:=[(&+[RB1[i,j]*B[j]: j in [1..e]]): i in [1..e]];
	O := [x@@ERf: x in O];
	O := [x@@Af: x in O];
	// "Now O:", O;

	M := Matrix([Eltseq(x): x in O]);
	ML, T := LLL(M);
	// "ML:", ML;

	O := [Universe(O) | Eltseq(ML[i]): i in [1.. Nrows(ML)]];
	if 0 eq 1 then
	    vprint ZMeataxe: "LLL maximal order basis:",
		[Matrix(Q, x)/denom: x in O];
	end if;

	should_split := ss lt m;
	multiplicity := m div ss;
	if not SplitSearch then
	    return 0, O, denom, should_split, ss, multiplicity;
	end if;

	if not should_split then
	    return 0, O, denom, false, ss, multiplicity;
	end if;

	for xi := 1 to #O do
	    x := O[xi];
	    mf := FMP(x);
	    if #mf gt 1 or not DistinctFactors and mf[1][2] gt 1 then 
		vprintf ZMeataxe: "GOOD MO basis number %o:\n", xi;
		vprint ZMeataxe: x, mf;
		return x, O, denom, true, ss, multiplicity; // mf
	    end if;
	end for;

	for xi := 1 to #O do
	    x := O[xi];
	    for yi := 1 to xi - 1 do
		y := O[yi];
		p := x*y;
		mf := FMP(p);
		if #mf gt 1 or not DistinctFactors and mf[1][2] gt 1 then 
		    vprintf ZMeataxe: "GOOD prod %o, %o:\n", xi, yi;
		    vprint ZMeataxe: p, mf;
		    return p, O, denom, true, ss, multiplicity; // mf
		end if;

		p := p - y*x;
		mf := FMP(p);
		if #mf gt 1 or not DistinctFactors and mf[1][2] gt 1 then 
		    vprintf ZMeataxe: "GOOD commutator %o, %o:\n", xi, yi;
		    vprint ZMeataxe: p, mf;
		    return p, O, denom, true, ss, multiplicity; // mf
		end if;
	    end for;
	end for;

	return Universe(O)!0, O, denom, true, ss, multiplicity;

	/*
	mp := [FMP(x): x in O];
	mp;
	[[Kernel(Evaluate(mp[i,j,1], O[i])): j in [1 .. #mp[i]]]: i in [1..#mp]];

	return O[1];
	*/
    end if;

SSP:=[];
     ss := 1; // it is the LCM of the local schurindices
     if realsi eq -1 then ss:=2; end if;
     for pt in L do
       p := pt[1];
       dp := Decomposition(K,p);
       normexponent := ExactQuotient(d, dp[1][2]); // d = deg(K)
       // So normexponent = number of primes over p times the exponent of the norm of one primideal over p 
       m2m := ExactQuotient(pt[2],  normexponent); // should be m(m-tp) 
       m2m:=ExactQuotient(m2m,rootofdimKofE);
       m2m:=-m2m + rootofdimKofE;
       ssp:=ExactQuotient(rootofdimKofE,m2m);
        Append(~SSP,[p,ssp]);
       ss:=LCM(ssp,ss);
     end for;

    sing:=MatrixRing(Q,totaldim) ! 0;

if ss lt m then //Try to find a small element in the maximal order
    basisMatrix:=RMatrixSpace(Z,totaldim,totaldim^2) ! 0;
    for i in [1..totaldim] do 
         for j in [1..totaldim] do 
         for k in [1..totaldim] do 
         basisMatrix[i][j+totaldim*(k-1)]:=RM1[i][j][k]; 
         end for; end for;
    end for;
    newbasisMatrix,T:=LLLBasisMatrix(LatticeWithBasis(basisMatrix));
// "basisMatrix:", basisMatrix; "Herm:", HermiteForm(newbasisMatrix);
"LLL newbasisMatrix:", newbasisMatrix;
// lat := Lattice(newbasisMatrix); "gram:", GramMatrix(lat);


/*
rbasis := rescale_basis(Basis(RowSpace(newbasisMatrix)));
newbasisMatrix := Matrix(rbasis);
"rbasis:", rbasis;
"Rescaled gram:", GramMatrix(newbasisMatrix);
lat := Lattice(newbasisMatrix);
*/

    merke:=0;
    fff := 0;

"RB1 before LLL:", RB1;
"T:", T;
    RB1:=T*RB1;
"RB1 after LLL:", RB1;
    newBasis:=[];
    for i in [1..totaldim] do 
	 v := newbasisMatrix[i];
         X:=MatrixRing(Z,totaldim) ! 0;
         for j in [1..totaldim] do 
         for k in [1..totaldim] do 
         X[j][k]:=v[j+totaldim*(k-1)]; 
         end for; end for;
/*
    Append(~newBasis,X);
    end for;
    
    for i in [1..totaldim] do 
       fff:=Factorization(MinimalPolynomial(newBasis[i])); 
*/

       fff:=Factorization(MinimalPolynomial(X));
       if #fff gt 1 or not DistinctFactors and fff[1][2] gt 1 then 
	    vprint ZMeataxe: "GOOD:", i, X;
            merke:=i;
            break i;
       end if;
    end for;
    if merke gt 0 then 
       for i in [1..totaldim] do sing +:= RB1[merke][i]*B[i]; end for;
    end if;
    //Factorization(MinimalPolynomial(sing));
   
end if;

    denom := LCM([Denominator(x): x in Eltseq(sing)]);
    sing := denom*sing;

    sing := sing @@ ERf;
    sing := sing @@ Af;
    return sing, RM1, RB1, det, newbasisMatrix, B;

    //return ss, SSP,realsi;

end intrinsic;

intrinsic MaximalOrderBasis(E::AlgMat: Disc := 0) -> SeqEnum
{A Z-basis of a maximal order of the central simple algebra E over Z}

    if assigned E`MaximalOrderInfo then
	return Explode(E`MaximalOrderInfo);
    end if;

    _, B, d, ss, si, m := FindSplitElement(E: SplitSearch := false);
    B := [Matrix(Q, x)/d: x in B];

    E`MaximalOrderInfo := <B, d, ss, si, m>;
    return B, d, ss, si, m;

end intrinsic;

intrinsic SortByMP(Q::[Mtrx]) -> SeqEnum, SeqEnum
{Sort matrices via minimal polynomial degree}

    T := [<x, MinimalPolynomial(x: Proof := false)>: x in Q];
    cmp := func<t, u | Degree(t[2]) - Degree(u[2])>;
    function cmp(t, u)
	f := t[2];
	g := u[2];
	c := Degree(f) - Degree(g);
	if c ne 0 then return c; end if;
	c := Norm(Vector(Eltseq(f))) - Norm(Vector(Eltseq(g)));
	if c ne 0 then return c; end if;
	if f lt g then return -1;
	elif f gt g then return 1;
	else return 0; end if;
    end function;

    Sort(~T, cmp);
    return [t[1]: t in T], [t[2]: t in T];
end intrinsic;

/*******************************************************************************
			     Split via Conic
*******************************************************************************/

intrinsic SplitViaConic(
    E::AlgMat: GivenField := 0, FieldGen := 0, Opt
) -> AlgMatElt
{Try to split E via conic; if successful, return non-zero X in E so that
MinPoly(X) = x^2 - x}

    d := Dimension(E);

    if GivenField cmpne 0 then
	K := GivenField;
	w := K.1;
	W := w;

	C := Centre(E);
	z := Dimension(C);
	require z eq 1: "Centre must be trivial over field";
	require d eq 4*z: "Algebra is not dimension 4 over centre";
    else
	if FieldGen cmpne 0 then
	    W := FieldGen;
	    f<x> := MinimalPolynomial(W);
	    z := Degree(f);

	    //require d eq 4*z: "Algebra is not dimension 4 over subfield";
	else
	    C := Centre(E);
	    z := Dimension(C);
	    require d eq 4*z: "Algebra is not dimension 4 over centre";

	    CB := LLL(Basis(C));

	    W := 0;
	    for X in CB do
		f<x> := MinimalPolynomial(X);
		if Degree(f) eq z then
		    W := X;
		    break;
		end if;
	    end for;

	    if Opt then
		K<w> := NumberField(f);
		"First K:", K;
		"Get OptimizedRepresentation";
		time OK := OptimizedRepresentation(K);
		OK;
		word := Polynomial(Eltseq(K!OK.1));
		"Move to OK";
		time W := Evaluate(word, W);
		delete word;
		f := DefiningPolynomial(OK);
		assert MinimalPolynomial(W) eq f;
	    end if;
	end if;

	K<w> := NumberField(f);

    end if;

    "Field:", K;

    w_is_square, sqrt_w := IsSquare(w);
    "w_is_square:", w_is_square;
    if w_is_square then
	"sqrt_w:", sqrt_w;
    else
	sqrt_w := 0;
    end if;

    try
	EZ := ChangeRing(E, Z);
	MO := MaximalOrderBasis(E);

	// Sort MO
	dets := [Abs(Determinant(m)) : m in MO];
	Sort(~dets, ~rho);
	MO := [MO[i] : i in Eltseq(rho)];
    catch e
	MO := Basis(E);
	l, NicifyBasisANF := IsIntrinsic("NicifyBasisANF");
	if l then
	    MO := NicifyBasisANF(MO);
	end if;
    end try;

    MOK := BaseRing(MO[1]);
    over_ZQ := Type(MOK) in {RngInt, FldRat};

//"MO:", MO;

    best_prod := Infinity();

    count := 0;
//"HACK", 41; for i1 in [41..#MO], i2 in [1..i1-1] do
    for i1 in [1..#MO], i2 in [1..i1-1] do

        if count gt 10 then break i1; end if;

	X1 := MO[i1];
	X2 := MO[i2];

	MOK := BaseRing(X1);
	nc := Ncols(X1);
	if over_ZQ then
	    p := RandomPrime(23);
	    GFp := GF(p);
	    matsp := [Matrix(GFp, x): x in [X1, X2]];
	else
	    p := RandomPrime(23);
	    p, R := NextANFPrime(p, DefiningPolynomial(MOK));
	    GFp := Universe(R);
	    h := hom<MOK -> GFp | R[1]>;
	    matsp := [Matrix(GFp, nc, [h(c): c in Eltseq(x)]): x in [X1, X2]];
	end if;

	printf "Try generators %o, %o\n", i1, i2;

	A := sub<MatrixRing(GFp, nc) | matsp>;
	dim := Dimension(A);
        if d ne dim then
	    "Do not generate";
	    continue;
	end if;
        count +:= 1;

	"Dim:", dim;

	L := [];

	gens1 := [E!1, X1, X2, X1*X2];
	gens2 := [X2*X1, X1^2, X2^2];
	for X in gens1 do
	    U := X;
	    for i := 0 to z - 1 do
		Append(~L, Eltseq(U));
		U := U*W;
	    end for;
	end for;

	M1 := Matrix(L);

	for X in gens2 do
	    Append(~L, Eltseq(X));
	end for;

	Y := Matrix(Reverse(L));
	N := BasisMatrix(Nullspace(Y));
	ReverseColumns(~N);

	if GivenField cmpne 0 then
	    N := Matrix(K, N);
	end if;

	// "L:", L; "N:", N; Parent(N);

	F<[y]> := FreeAlgebra(K, 2);
	Fgens := [F!1, y[1], y[2], y[1]*y[2], y[2]*y[1], y[1]^2, y[2]^2];

	rels := [];

	function write_over_K(v)
	    r := F!0;
	    for j := 1 to #gens1 do
		if GivenField cmpne 0 then
		    c := K!v[j];
		else
		    c := K![v[k]: k in [(j - 1)*z + 1 .. j*z]];
		end if;
		r := r + c*Fgens[j];
	    end for;
	    return r;
	end function;

	for i := 1 to Nrows(N) do
	    v := N[i];
	    /*
	    r := F!0;
	    for j := 1 to #gens1 do
		c := K![v[k]: k in [(j - 1)*z + 1 .. j*z]];
		r := r + c*Fgens[j];
	    end for;
	    */
	    r := write_over_K(v);
	    for j := 1 to #gens2 do
		c := v[#gens1*z + j];
		r := r + c*Fgens[#gens1 + j];
	    end for;
	    "Rel:", i, r;
	    Append(~rels, r);
	end for;

	rels := Reduce(rels);

	"rels:", rels;

	MOM := Matrix([Eltseq(x): x in MO]);
	S := Solution(M1, MOM);
	delete M1;

	if over_ZQ then
	    SL, ST := LLL(S : Sort);
	    assert Abs(Determinant(ST)) eq 1;
	else
	    SL := S;
	end if;

	"SL:", SL;

	MO_words := [write_over_K(SL[i]): i in [1 .. Nrows(SL)]];

	NCA, NCAf := F/Ideal(rels);
	assert Dimension(NCA) eq 4;

	A, Af := Algebra(NCA);

	procedure try_monomials(a, b, ~pt)

	    pt := 0;

	    function monomial_test(a)
		E := Eltseq(a);
		I := [i: i in [1 .. #E] | E[i] ne 0];
		if #I ne 1 then
		    return 0, 0;
		end if;
		return E[I[1]], I[1] - 1;
	    end function;

	    ac, ae := monomial_test(a);
	    bc, be := monomial_test(b);
	    if ac eq 0 or bc eq 0 then
		return;
	    end if;

	    "Monomial case:", ac, ae, bc, be;

	    if not (w_is_square or ae mod 2 eq 0 and be mod 2 eq 0) then
		"Not square";
		return;
	    end if;

	    if w_is_square then
		ase := sqrt_w^ae;
		bse := sqrt_w^be;
	    else
		ase := w^(ae div 2);
		bse := w^(be div 2);
	    end if;
	    assert ase^2 eq w^ae and bse^2 eq w^be;

	    solvable := false;
	    SF := Subfields(K);
	    SF := SF[1 .. #SF - 1];
	    for t in SF do
		SK := t[1];
		"Try subfield", SK;
		C := Conic([SK | 1, ac, bc]);
		printf "IsLocallySolvable... ";
		time solvable := IsLocallySolvable(C); solvable;
		if solvable then
		    break;
		end if;
	    end for;

	    if not solvable then
		return;
	    end if;

	    "Get Rational Point";
	    time l, pt := HasRationalPoint(C);
	    assert l;
	    "Point over subfield:", pt;

	    assert pt[3] eq 1;

	    //pt := [pt[1], ase*pt[2], bse*pt[3]];
	    pt := [pt[1], 1/ase*pt[2], 1/bse*pt[3]];

	end procedure;

	_, QA, QAf := IsQuaternionAlgebra(A);

	a := Norm(QA.1);
	b := Norm(QA.2);

	na := Norm(a);
	nb := Norm(b);

IndentPush();
"a:", a;
"Norm a:", na;
"Min poly degree a:", Degree(MinimalPolynomial(a));
"b:", b;
"Norm b:", nb;
"Min poly degree b:", Degree(MinimalPolynomial(b));
SK := sub<K | a, b>;
"Subfield for a & b:", SK;
printf "Subfield degree: %o (out of %o)\n", Degree(SK), Degree(K);

	try_monomials(a, b, ~pt);
	if pt cmpne 0 then
	    IndentPop();
	    break i1;
	end if;

        MO_images := [x @NCAf @Af @QAf : x in MO_words];

printf "NicerQuaternionAlgebra ... "; time
//NicerQuaternionAlgebra := 1;

    if 1 eq 1 then
        QA1, QAtoQA1 := NicerQuaternionAlgebra(QA : elements := MO_images);
        QA1f := QAf * QAtoQA1;

	QA := QA1;
	QAf := QA1f;
    else
	//"SKIP NICE";
    end if;

	a := Norm(QA.1);
	b := Norm(QA.2);

	na := Norm(a);
	nb := Norm(b);

"a:", a;
"Norm a:", na;
"Min poly degree a:", Degree(MinimalPolynomial(a));
"b:", b;
"Norm b:", nb;
"Min poly degree b:", Degree(MinimalPolynomial(b));
SK := sub<K | a, b>;
"Subfield for a & b:", SK;
printf "Subfield degree: %o (out of %o)\n", Degree(SK), Degree(K);

	try_monomials(a, b, ~pt);
	if pt cmpne 0 then
	    IndentPop();
	    break i1;
	end if;


        prod := na*nb;
	"prod:", prod;
IndentPop();

	if prod lt best_prod then
	    "NEW BEST!";
	    best_prod := prod;
	    //best_info := <X1, X2, NCA, NCAf, A, Af, QA1, QA1f, a, b>;
	    best_info := <X1, X2, NCA, NCAf, A, Af, QA, QAf, a, b>;

	    if prod eq 1 then
		break;
	    end if;
//"BREAK OUT"; break;
        end if;

    end for;

"Again Field:", K;
    if pt cmpeq 0 then

	X1, X2, NCA, NCAf, A, Af, QA, QAf, a, b := Explode(best_info);

	conic := Conic([K| 1, a, b]);
conic;
	SetVerbose("Conic", 2);
	SetClassGroupBounds("GRH");

	time bool, pt := HasRationalPoint(conic);
	assert bool;
    end if;

    "Point:", pt;

    zd := QA! (Eltseq(pt) cat [0]);
    assert Norm(zd) eq 0;

    MR, mrf := MatrixRing(QA, zd);
    sing := MR.1@@mrf; // Return [1 0 | 0 0], so MP(sing) = x*(x - 1)

//"Sing MP:", MinimalPolynomial(sing);

    Asing := sing @@ QAf;
//"A sing:", Asing;
    sing := Asing @@ Af;
"NCA sing:", sing;

    if GivenField cmpne 0 then
	MA := Parent(ChangeRing(MO[1], K));
	h := hom<K -> MA | x :-> MA!x>;
    else
	MA := Generic(Universe(MO));
	h := hom<K -> MA | W>;

	Q := RationalField();
	//FQ<[s]> := FreeAlgebra(Q, 2);
	//hh := hom<NCA -> FQ | hom<K -> Q | 1>, s>;
    end if;

    XA := [X1, X2];
    coeffs := [h(x): x in Coefficients(sing)];
    mons := [&*[MA | XA[j]: j in Eltseq(m)]: m in Monomials(sing)];
    s := &+[coeffs[i]*mons[i]: i in [1 .. #coeffs]];

    return s;

end intrinsic;

/*******************************************************************************
			     Split via min field
*******************************************************************************/

intrinsic SplitViaMinimalField(M::ModRng) -> []
{Split M via Fieker's minimal field algorithm}

    E := EndomorphismRing(M);
    C := CentreOfEndomorphismRing(M);
    MO := MaximalOrderBasis(E);

    max_d := 0;
    max_X := 0;
    max_mp := 0;
    for X in MO do
	mp := MinimalPolynomial(X: Proof := false);
	if Degree(mp) gt max_d /*and Degree(mp) eq 12*/ then
	    "New best min poly:", mp;
	    max_d := Degree(mp);
	    max_mp := mp;
	    max_X := X;
	end if;
    end for;

    if max_d eq 1 then
      return M;
    end if;
    K<w> := NumberField(max_mp);
K;

    W := max_X - w;
"Get kernel of", Parent(W);
    time ker := BasisMatrix(Kernel(W));

    MK := ImageWithBasis(ker, ChangeRing(M, K));
"MK:", MK;
MK: Maximal;

//return MK;

SetVerbose("Reduce",2);
SetVerbose("ClassGroup",3);
SetVerbose("Cohomology",1);
SetVerbose("KGModule",1);

    MM := AbsoluteModuleOverMinimalField(MK);

return MM, MK;

    S := ExpandZ(MM: DoClean);

    return S;

end intrinsic;

/*******************************************************************************
			     IsDivisionAlgebra
*******************************************************************************/

intrinsic IsDivisionAlgebra(A::AlgMat) -> BoolElt
{Return whether the matrix algebra A over Z or Q is a division algebra.
A must be central simple}

    require 1 in A: "Algebra must have 1";

    R := BaseRing(A);
    if Type(R) eq FldRat then
	return IsDivisionAlgebra(Saturation(A));
    /*
    elif ISA(Type(R), FldNum) then
	return IsDivisionAlgebra(Saturation(A));
    */
    else
	require Type(R) eq RngInt: "Algebra must be over Z or Q at moment";
    end if;

    e := Dimension(A);
    for X in Basis(A) do
	f := MinimalPolynomial(X);
	if not IsIrreducible(f) then
	    return false;
	end if;
	if Degree(f) eq e then
	    return true;
	end if;
    end for;

    C := Centre(A);
    d := Dimension(C);
    if d eq e then
	return true;
    end if;

    m := Isqrt(e div d);
    require d*m^2 eq e: "Noncommutative algebra must be central simple";

    s, B, d, should_split := FindSplitElement(A);
    return not should_split;

end intrinsic;

