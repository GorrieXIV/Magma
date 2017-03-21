freeze;

///////////////////////////////////////////////////////////////////////
// jacobian.m
///////////////////////////////////////////////////////////////////////
// Add attributes to LinearSys to identify jacobian pencils.
declare attributes LinearSys:
    subtype_name,
    auxilliary_data,
    ring,
    ring_map,
    value_ring,
    value_map,
    generic_polynomial,
    generating_polynomial,
    affine_ambient,
    projective_polynomial,
    infinite_polynomial,
    resolution_graph,
    regular_splice_diagram,
    generic_genus;

///////////////////////////////////////////////////////////////////////
// Accessory function	
///////////////////////////////////////////////////////////////////////	

function Homogenization(f,z,d)
    // The homogenisation of f in degree d with respect to z
    // if this is possible with the grading on their common
    // parent ring
    R := Generic(Parent(f));
    /* error checking */
    error if not Generic(Parent(z)) cmpeq R,
        "First two arguments must have the same parent";
    error if not IsHomogeneous(z),
        "Second argument must be homogeneous";
    /* homogenise */
    degz := WeightedDegree(z);
    monos := Monomials(f);
    coeffs := Coefficients(f);
    n := #monos;
    g := R!0;
    for i in [1..n] do
        extra := d - WeightedDegree(monos[i]);
        isdivis,q := IsDivisibleBy(extra,degz);
        error if not isdivis,
            "Homogenization impossible with given degrees";
        g := g+coeffs[i]*monos[i]*z^q;
    end for;
    return g;
end function;

///////////////////////////////////////////////////////////////////////
//		 Creation from nothing
///////////////////////////////////////////////////////////////////////	

intrinsic Pencil(A::Aff,f::RngMPolElt) -> LinearSys
{The pencil on the projective closure of A determined by f = a as a varies}
    RA := CoordinateRing(A);
    k := BaseRing(A);
    n := Dimension(A);
    P := ProjectiveClosure(A);
    RP := CoordinateRing(P);
    C := Curve(A,f);
    Cbar := ProjectiveClosure(C);
    fz := Polynomial(Cbar);
    deg := Degree(Cbar);
    require IsField(BaseRing(P)):
	"Scheme is not defined over a field";
    // create the pencil
    L := LinearSystem(P,[Homogenization(h(f),z,deg),z^deg])
	where z is P.(Length(P))
	where deg is TotalDegree(f)
	where h is hom< RA -> RP | [RP.i : i in [1..Dimension(A)]] >;
    // THINK L`sections := [fz,fz - P.(n+1)^deg];
    L`generating_polynomial := f;
    L`affine_ambient := A;
    // set the ring comparison maps
    RAext := PolynomialRing(k,n+1);
    ext_map := hom< RA -> RAext | [ RAext.i : i in [1..n] ] >;
    Rval := PolynomialRing(k);
    val_map := hom< RAext -> Rval | [ Rval | 0 : i in [1..n] ] cat [ Rval.1 ]>;
    L`ring := RAext;
    L`ring_map := ext_map;
    L`value_ring := Rval;
    L`value_map := val_map;
    L`generic_polynomial := ext_map(f) - RAext.(n+1);
    L`subtype_name := "jpencil";
    return L;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Attribute retrieval
///////////////////////////////////////////////////////////////////////

intrinsic IsJacobianPencil(L::LinearSys) -> BoolElt
{True iff L was created using the Pencil(A,f) function}
    return assigned L`subtype_name and L`subtype_name eq "jpencil";
end intrinsic;

intrinsic GeneratingPolynomial(L::LinearSys) -> RngMPolElt
{The polynomial defining L}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    return L`generating_polynomial;
end intrinsic;

intrinsic GenericPolynomial(L::LinearSys) -> RngMPolElt
{The polynomial f - a in the extended ring of L}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    return L`generic_polynomial;
end intrinsic;

intrinsic ProjectivePolynomial(L::LinearSys) -> RngMPolElt
{The homogenisation of the generating polynomial of L}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    if not assigned L`projective_polynomial then
	A := AffineAmbient(L);
	f := GeneratingPolynomial(L);
	fbar := Polynomial(ProjectiveClosure(Curve(A,f)));
	L`projective_polynomial := fbar;
    end if;
    return L`projective_polynomial;
end intrinsic;

intrinsic InfinitePolynomial(L::LinearSys) -> RngMPolElt
{The polynomial defining the infinite fibre of L: z^deg}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    if not assigned L`infinite_polynomial then
	P := Ambient(L);
	n := Dimension(P);
	deg := Degree(L);
	g := P.(n+1)^deg;
	L`infinite_polynomial := g;
    end if;
    return L`infinite_polynomial;
end intrinsic;

intrinsic AffineAmbient(L::LinearSys) -> Aff
{The affine space in which the affine fibres of L lie}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    return L`affine_ambient;
end intrinsic;

intrinsic ExtendedRing(L::LinearSys) -> RngMPol
{The base ring of L extended by a variable value}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    return L`ring;
end intrinsic;

intrinsic RingMap(L::LinearSys) -> Map
{The natural injection from the base ring of L to the extended ring}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    return L`ring_map;
end intrinsic;

intrinsic ValueRing(L::LinearSys) -> RngMPol
{The ring of values of f}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    return L`value_ring;
end intrinsic;

intrinsic ValueMap(L::LinearSys) -> Map
{The map that sets the ambient affine coordinates of L to 0}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    return L`value_map;
end intrinsic;

intrinsic RegularSpliceDiagram(L::LinearSys) -> GrphSpl
{The regular splice diagram at infinity of L}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    if not assigned L`regular_splice_diagram then
	S := CalculateRegularSpliceDiagram(L);
	L`regular_splice_diagram := S;
    end if;
    return L`regular_splice_diagram;
end intrinsic;

intrinsic GenericGenus(L::LinearSys) -> RngIntElt
{The genus of the generic fibre of L}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    if not assigned L`generic_genus then
	S := RegularSpliceDiagram(L);
	g := Genus(S);
    end if;
    return L`generic_genus;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Special fibres of Jacobian pencils
///////////////////////////////////////////////////////////////////////

intrinsic SingularFibres(L::LinearSys) -> SetEnum
{The set of singular fibres of L}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    if HasNonSingularFibres(L) then
	return {};
    end if;
    A := AffineAmbient(L);
    n := Dimension(A);
    Rext := ExtendedRing(L);
    Rval := ValueRing(L);
    surj := ValueMap(L);
/* make the scheme of singular points of fibres of f */
    f := GenericPolynomial(L);
    fx := Derivative(f,1);
    fy := Derivative(f,2);
    I := ideal< Rext | f,fx,fy >;
/* solve for the values of those fibres */
    J := EliminationIdeal(I,n);
    require #Basis(J) eq 1:
	"Something nonfactorial going on.";
    poly := surj(Basis(J)[1]);
    prevals := Roots(poly);
    vals := { r[1] : r in prevals };
    return vals;
end intrinsic;

intrinsic NonReducedFibres(L::LinearSys) -> SeqEnum
{The sequence of nonreduced fibres of L}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    A := AffineAmbient(L);
    n := Dimension(A);
    Rext := ExtendedRing(L);
    Rval := ValueRing(L);
    surj := ValueMap(L);
/* make the scheme of nonreduced fibres */
    f := GenericPolynomial(L);
    fx := Derivative(f,1);
    fy := Derivative(f,2);
    g := GCD(fx,fy);
    I := ideal< Rext | f,g >;
/* solve for the values of those fibres */
    J := EliminationIdeal(I,n);
    require #Basis(J) eq 1:
	"Something nonfactorial going on";
    poly := surj(Basis(J)[1]);
    prevals := Roots(poly);
    vals := { r[1] : r in prevals };
    return vals;
end intrinsic;

intrinsic HasNonSingularFibres(L::LinearSys) -> BoolElt
{True iff all (finite) fibres of L are nonsingular}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    A := AffineAmbient(L);
    RA := CoordinateRing(A);
    f := GeneratingPolynomial(L);
/* make the scheme of singular points of fibres of f */
    fx := Derivative(f,1);
    fy := Derivative(f,2);
    Z := Scheme(A,[fx,fy]);
    return IsEmpty(Z);
end intrinsic;

intrinsic HasReducedFibres(L::LinearSys) -> BoolElt
{True iff all (finite) fibres of L are reduced}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    A := AffineAmbient(L);
    f := GeneratingPolynomial(L);
    fx := Derivative(f,1);
    fy := Derivative(f,2);
    g := GCD(fx,fy);
    b := TotalDegree(g) eq 0;
    return b;
end intrinsic;

intrinsic IsConnectedFibre(L::LinearSys,a::RngElt) -> BoolElt
{True iff the fibre f = a of L is connected}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    A := AffineAmbient(L);
    k := BaseRing(A);
    require IsCoercible(k,a):
	"Second argument does not lie in the base field";
    f := GeneratingPolynomial(L);
    f1 := f - a;
    return IsIrreducible(f1);
end intrinsic;

intrinsic IrreducibleComponents(L::LinearSys,a::RngElt) -> SeqEnum
{The sequence of irreducible components of the fibre f = a of L}
    require IsJacobianPencil(L): "Linear system is not a Jacobian pencil";
    A := AffineAmbient(L);
    k := BaseRing(A);
    require IsCoercible(k,a):
	"Second argument does not lie in the base field";
    f := GeneratingPolynomial(L);
    f1 := f - a;
    fact := Factorisation(f1);
    comps := [];
    dim := Dimension(A);
    if dim eq 2 then
	for r in fact do
	    Append(~comps,Curve(A,r[1]));
	end for;
    else
	for r in fact do
	    Append(~comps,Scheme(A,r[1]));
	end for;
    end if;
    return comps;
end intrinsic;

