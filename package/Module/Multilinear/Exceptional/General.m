freeze;

//********************************************************************************
//
// Octonion algebras.
//
//********************************************************************************

// ----- Tools for *-algebras -----

intrinsic IsStarAlgebra(A::AlgGen) -> BoolElt
{Decides if algebra has an involution, i.e. a *-algebra.}
	try 
		test, star := HasAttribute(A, "Star" );
		return test;	
	catch e
		return false;
	end try;
end intrinsic;

intrinsic Star(A::AlgGen) -> Map
{Returns involution of given *-algebra.}
	test, star := HasAttribute(A, "Star" );
	return star;
end intrinsic;

// ----- Tools for power associative algebras -----


intrinsic GenericMinimumPolynomial(x::AlgGenElt) -> FldElt
{The generic minimum polynomial of an element in a power associative algebra.}
	C := Parent(x);
	K := BaseRing(C);
	d := Dimension(C);	
	M := [Eltseq(C!1)];
	y := C!1; i := 1;
	repeat 
		y *:= x; i +:= 1;
		Append(~M, Eltseq(y) );
		N := NullSpace(Matrix(K, i, d, M));
	until Dimension(N) gt 0;
	coef := N.1;
	coef := coef[i]^(-1)*coef;
	return  PolynomialRing(K)!Eltseq(coef);
end intrinsic;

intrinsic GenericMinimalPolynomial(x::AlgGenElt) -> FldElt
{The generic minimum polynomial of an element in a power associative algebra.}
	return GenericMinimumPolynomial(x);
end intrinsic;

intrinsic GenericNorm(x::AlgGenElt) -> FldElt
{The generic norm of an element in a power associative algebra.}
	m := GenericMinimumPolynomial(x);
	d := Degree(m);
	return (-1)^d*Eltseq(m)[1];
end intrinsic;

intrinsic GenericTrace(x::AlgGenElt) -> FldElt
{The generic trace of an element in a power associative algebra.}
	m := GenericMinimumPolynomial(x);
	d := Degree(m);
	return -1*Eltseq(m)[d];  // arrays start at 1.
end intrinsic;

intrinsic GenericTracelessSubspaceBasis( A::AlgGen) -> .
{Given a power associative algebra return a basis for the elements of generic trace 0}
	T, mu := TensorOnVectorSpaces(Tensor(A));
	V := Domain(T)[2];
	W := KSpace(BaseField(V),1);
	f := hom< V->W | [<x,W!GenericTrace(x@mu)> : x in Basis(V)] >;
	N := Kernel(f);
	return N @@ mu;
end intrinsic;
