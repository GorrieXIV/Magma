freeze;

//********************************************************************************
//
// Octonion algebras.
//
//********************************************************************************




intrinsic CompositionAlgebra(K::Fld, a::SeqEnum[FldElt]) -> AlgGen
{Constructs the composition algebra with specified parameters.}
	require not ( Characteristic(K) eq 2 ) : "Not implemented for even characteristic.";

	case #a :
		when 0 :
			A := Algebra<K,1 | [1] >;
			A`Star := hom<A -> A | u:-> u, u:->u >;
			return A; 
		when 1 :
			A := Algebra<K,2 | [1,0,0,1,0,1,-a[1],0] >;
			A`Star := hom<A -> A | u:->(A!Eltseq(u[1],-u[2])), u:->(A!Eltseq(u[1],-u[2])) >;
			return A;
		when 2 :
			A := QuaternionAlgebra(K,a[1],a[2]);
			A`Star := hom<A -> A | u:->Conjugate(u), u:->Conjugate(u) >;
			return A;
		when 3 :
			return OctonionAlgebra(K, a[1],a[2],a[3]);
	end case;
	error "Cayley-Dickson composition algebras have at most 4 parameters.";
end intrinsic;

intrinsic CompositionAlgebra(K::Fld, a::SeqEnum[RngIntElt]) -> AlgGen
{Constructs the composition algebra with specified parameters.}
	return CompositionAlgebra(K, [K | x : x in a]);
end intrinsic;

intrinsic OctonionAlgebra( K::Fld, a::FldElt, b::FldElt, c::FldElt ) -> AlgGen
{Octonion algebra with specified parameters. }
	require not ( Characteristic(K) eq 2 ) : "Not implemented for even characteristic.";

	Q := QuaternionAlgebra< K | a,b >;
	B := Basis( Q );  // Gives {1,i,j,k}, which matters for conjugate later.
	str_const := [ K!0 : i in [1..8^3] ];
	for i in [1..2*#B] do
		if ( i le #B ) then
			a := <B[i],Q!0>;
		else
			a := <Q!0,B[i-4]>;
		end if;
		for j in [1..2*#B] do
			if ( j le #B ) then
				b := <B[j], Q!0>;
			else
				b := <Q!0, B[j-4]>;
			end if;
			// Cayley-Dickson product
			x := Eltseq(a[1]*b[1] + c*b[2]*Conjugate(a[2]));
			y := Eltseq(Conjugate(a[1])*b[2]+b[1]*a[2]);
			for k in [1..4] do
				str_const[64*(i-1)+8*(j-1)+k] := x[k];
				str_const[64*(i-1)+8*(j-1)+k+4] := y[k];
			end for;
		end for;
	end for;

	A := Algebra<K, 8 | str_const >;
	star := function(x) 
			O := Parent(x);	
			s := Eltseq(x);	
			return O.1*s[1] - &+[O.i*s[i] : i in [2..8]];
		end function;
	A`Star := hom<A -> A | x:->star(x), y:->star(y) >;
	return A;
end intrinsic;

intrinsic OctonionAlgebra( K::Fld, a::RngIntElt, b::RngIntElt, c::RngIntElt ) -> AlgGen
{Octonion algebra with specified parameters. }
	return OctonionAlgebra(K,K!a, K!b, K!c);
end intrinsic;

intrinsic SplitOctonionAlgebra( K:Fld ) -> AlgGen
{Split Octonion algebra over a field.}
	return OctonionAlgebra(K, K!1,K!1,K!1);
end intrinsic;
