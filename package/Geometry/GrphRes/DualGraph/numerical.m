freeze;
///////////////////////////////////////////////////////////////////////
// numerical.m
//	Contents:
//		singular places data from resolution graphs
//		numerics of the exceptional locus of a resolution graph
//		determinants of resolution graphs
///////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////
//		Places
///////////////////////////////////////////////////////////////////////

intrinsic NumberOfTransverseIntersections(G::GrphRes) -> RngIntElt
{The number of transverse intersections of the birational pullback of
the base germ of G with its vertices}
    t := TransverseIntersections(G);
    nt := &+t;
    return nt;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Exceptional numerics
///////////////////////////////////////////////////////////////////////

intrinsic CartanMatrix(G::GrphRes) -> Mtrx
{The symmetric adjacency matrix of G with selfintersections along the diagonal}
    n := Size(G);
    R := MatrixAlgebra(Rationals(),n);
    si := Selfintersections(G);
    g := UnderlyingGraph(G);
    /* create the matrix */
    m := AdjacencyMatrix(g);
    mt := Transpose(m);
    M := R!(m+mt);
    for i in [1..n] do
        M[i,i] := si[i];
    end for;
    return M;
end intrinsic;

intrinsic ExceptionalSelfIntersection(G::GrphRes) -> RngIntElt
{The selfintersection of the total exceptional locus of G}
    n := Size(G);
    W := VectorSpace(Rationals(),n);
    excl := W ! Multiplicities(G);
    /* take the square of the excl vector in the cartan matrix norm */
    M := CartanMatrix(G);
    si := InnerProduct(excl*M,excl);
    return si;
end intrinsic;

intrinsic ExceptionalCurveIntersection(G::GrphRes) -> RngIntElt
{The intersection of the birational pullback of the base germ of G with
the total exceptional locus}
    n := Size(G);
    W := VectorSpace(Rationals(),n);
    excl := W ! Multiplicities(G);
    branches := W ! TransverseIntersections(G);
    /* intersect branches and excl curve with an ordinary inner product */
    int := InnerProduct(excl,branches);
    return int;
end intrinsic;

intrinsic CanonicalDegree(G::GrphRes) -> RngIntElt
{The degree of the exceptional part of the canonical class on the birational
pullback of the base germ of G}
    kc := 0;
    k := CanonicalClass(G);
    t := TransverseIntersections(G);
    n := Size(G);
    for i in [1..n] do
        kc +:= k[i]*t[i];
    end for;
    return kc;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Determinants
///////////////////////////////////////////////////////////////////////

intrinsic Determinant(G::GrphRes) -> RngIntElt
{The determinant of the Cartan matrix of G}
    M := CartanMatrix(G);
    return Determinant(M);
end intrinsic;

