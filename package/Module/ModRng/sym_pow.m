freeze;
 
/*
Jon Carlson.
Installed by Allan Steel, July 2003.
Improved by Steve Donnelly, November 2010.
*/

////////////////////////////////////////////////////////////////////
// Original version, with slight syntax improvements

ActionOnGradedModule := function(F,r,M);

    n := Nrows(M);
    theta := hom<F -> F|[&+[F.i*M[j,i]:i in [1 .. n]]:j in [1 .. n]]>;
    Wn := MonomialsOfDegree(F,r);
    m := #Wn;
    V := RSpace(BaseRing(F),m);
    B := Basis(V);
    ff := BaseRing(F);
    M := Matrix(ff,m,m,[]); // zero matrix

    if IsFinite(ff) and #ff eq 2 then
	for i := 1 to m do
	    w := theta(Wn[i]);
	    M[i] := &+[V|B[Index(Wn,y)]:y in Monomials(w)];
	end for;
    else
	for i := 1 to m do
	    w := theta(Wn[i]);
	    v, U := CoefficientsAndMonomials(w);
	    M[i] := &+[V|v[j]*B[Index(Wn,U[j])]:j in [1 .. #U]];
	end for;
    end if;

    return M;

end function;

////////////////////////////////////////////////////////////////////
// This version (for F = RngMPol) is a bit faster

ActionOnHomogeneousPolyRing := function(F,r,M)

    n := Nrows(M);

    // images of generators of F
    images := [F| &+ [M[j,i]*F.i : i in [1..n]] : j in [1..n]];

    mons := MonomialsOfDegree(F, r);
    m := #mons;
    V := RSpace(BaseRing(F), m);
    ff := BaseRing(F);
    M := MatrixAlgebra(ff, m) ! 0;

    // Get images of mons
    mi := [Evaluate(t, images) : t in mons];

    if IsFinite(ff) and #ff eq 2 then
        for i := 1 to m do
            for y in Monomials(mi[i]) do 
                jj := Index(mons, y);
                M[i,jj] := 1;
            end for;
        end for;
    else
        for i := 1 to m do
            C, U := CoefficientsAndMonomials(mi[i]);
            for j := 1 to #U do 
                jj := Index(mons, U[j]);
                M[i,jj] := C[j];
            end for;
        end for;
    end if;

    return M;
end function;

/*****************************************************************
// 2 x 2 case
// This is now in the kernel: intrinsic SymmetricPower2

// Get monomials [X^n, ..., Y^n] via repeated squaring.
// (Optimal for n = 2,3,4: number of mults = 3,6,8 respectively)

function monomials(P, X, Y, n)

    if n eq 1 then
        return [X, Y];
    elif IsEven(n) then
        n2 := n div 2;
        m := monomials(P, X, Y, n2);
        mm := [P | m[1]^2];
        for i := 1 to n2 do 
            mm cat:= [P | m[i]*m[i+1], m[i+1]^2];
        end for;
    else
        n2 := n div 2;
        m := monomials(P, X, Y, n2);
        mm := [P | ];
        for i := 1 to n2 + 1 do 
            si := m[i]^2;
            mm cat:= [P | si*X, si*Y];
        end for;
    end if;

    return mm;
end function;

// Compute in a univariate poly ring R[y] instead of R[x,y]
// ie put [1:y] in place of [x:y]

function InternalSymmetricPower2(A, n)
  
    assert n gt 0;
    R := BaseRing(A);
    P := PolynomialRing(R);
    y := P.1;

    X := A[1,1] + A[1,2]*y;
    Y := A[2,1] + A[2,2]*y;

    mons := monomials(P, X, Y, n);

    An := MatrixAlgebra(R, n+1) ! 0;

    for m := 1 to n+1 do 
        coeffs := Vector(Coefficients(mons[m]));
        InsertBlock(~An, coeffs, m, 1);
    end for;
    
    return An;

end function;

*****************************************************************/

intrinsic SymmetricPower(A::AlgMatElt, n::RngIntElt) -> AlgMatElt
{The n-th symmetric power of A}

    if n eq 1 then 
        return A;
    elif n eq 0 then
        return MatrixRing(BaseRing(A), 1) ! 1;
    end if;

    r := Nrows(A);

    if r eq 2 then
        An := SymmetricPower2(A, n);
    elif r eq 1 then
        An := A;
    else 
        ff := BaseRing(A);
        F := PolynomialRing(ff,r);
        An := ActionOnHomogeneousPolyRing(F, n, A);
    end if;

   /* check
    F := PolynomialRing(BaseRing(A), r);
    An1 := ActionOnGradedModule(F, n, A);
    assert An eq An1;
   */

    return An;

end intrinsic;

intrinsic SymmetricPower(M::ModGrp, n::RngIntElt) -> ModGrp
{The n-th symmetric power of M};

    ff := BaseRing(M);
    G := Group(M);
    r := Dimension(M);
    F := PolynomialRing(ff,r);
    L := [
	ActionOnGradedModule(F,n, ActionGenerator(M,i)): i in [1 .. Ngens(G)]
    ];
    MM := GModule(G,L);

    return MM;

end intrinsic;

