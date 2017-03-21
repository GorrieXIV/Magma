freeze;

//**************************************************************************************
//
// Jordan Algebras.
//
//**************************************************************************************

intrinsic JordanTripleProduct( J::AlgGen ) -> TenSpcElt
{Returns the tensor describing the Jordan triple product.}
	f := func< x,y,z | (x*y)*z+(y*z)*x - (z*x)*y >;
	return Tensor( [J, J, J], f );
end intrinsic;

// ALBERT TYPE.

__gen_matrix_prod := function( X, Y, m, s, n )
	A := Parent( X[1] );
	Z := [ A | 0 : i in [1..m*n] ];
	for i in [1..m] do
		for j in [1..n] do
			Z[n*(i-1)+j] := &+[ X[s*(i-1)+k]*Y[n*(k-1)+j] : k in [1..s] ];
		end for;
	end for;
	return Z;
end function;

__herm_to_vector := function( X )
	v := [ X[1][1], X[5][1], X[9][1] ];
	v cat:= X[2];
	v cat:= X[3];
	v cat:= X[6];
	return v;
end function;

intrinsic ExceptionalJordanCSA( O::AlgGen ) -> AlgGen
{The split exceptional Albert Jordan algebra over specified octonions.}
	require not ( Characteristic(BaseRing(O)) eq 2 ) : "Quadratic Jordan algebras are not supported.";
	
	// Idempotents.
	bas := [[ O | 1,0,0, 0,0,0, 0,0,0],[ O | 0,0,0, 0,1,0, 0,0,0],[ O | 0,0,0, 0,0,0, 0,0,1]];
	
	// Corners.
	B := Basis(O);
	star := Star(O);
	bas cat:= [[ O | 0,x,0, x@star,0,0, 0,0,0] : x in B ];
	bas cat:= [[ O | 0,0,x, 0,0,0, x@star,0,0] : x in B ];
	bas cat:= [[ O | 0,0,0, 0,0,x, 0,x@star,0] : x in B ];
//	print bas;
	K := BaseRing(O);

	MS := KSpace( K, 27 );
	str_const := [ MS | 0 : i in [1..27^2]];
	for i in [1..27]  do
		for j in [1..27] do
			xy := Eltseq(__gen_matrix_prod(bas[i],bas[j],3,3,3));
			yx := Eltseq(__gen_matrix_prod(bas[j],bas[i],3,3,3));
			z := [ O | 2^(-1)*(xy[k]+yx[k]) : k in [1..9]];
			m := [ K | z[1][1], z[5][1], z[9][1] ] cat Eltseq(z[2]) cat Eltseq(z[3]) cat Eltseq(z[6]);
			str_const[27*(i-1)+j] := m;
		end for;
	end for;
	return Algebra< MS | str_const >;
end intrinsic;



intrinsic ExceptionalJordanCSA( K::Fld ) -> AlgGen
{The split exceptional Albert Jordan algebra over specified field with split octonions.}
	require not ( Characteristic(K) eq 2 ) : "Quadratic Jordan algebras are not supported.";

	return ExceptionalJordanCSA( SplitOctonionAlgebra(K) );
end intrinsic;

// SPIN TYPE

intrinsic JordanSpinAlgebra( F::TenSpcElt ) -> AlgGen
{Zorn's special Jordan algebra of spin type for given symmetric form.}
	require IsSymmetric(F) : "Jordan spin algebras require symmetric forms.";
	U := F`Domain[2];
	V := F`Domain[1];
	K := BaseRing(F);
	basU := Basis(U);
	basV := Basis(V);
	d := #basU;

	MS := KSpace( K, 1+d );
	str_const := [ MS | 0 : i in [1..(1+d)^2]];
	for i in [0..d] do
		x := (i eq 0 ) select < K!1, Zero(U) > else <K!0, basU[i]>;
		for j in [0..d]  do
			y := (j eq 0 ) select < K!1, Zero(V) > else <K!0, basV[j]>;
			pr := func<x,y | [K| x[1]*y[1]+(<x[2],y[2]>@F)[1]] cat Eltseq(x[1]*y[2]+y[1]*x[2])>;
			str_const[(d+1)*i+j+1] := pr(x,y);
		end for;
	end for;
	return Algebra< MS | str_const >;
end intrinsic;


intrinsic JordanSpinAlgebra( form::. ) -> AlgGen
{Zorn's special Jordan algebra of spin type for given symmetric form.}
	return JordanSpinAlgebra( Tensor([form], 2,1));
end intrinsic;

