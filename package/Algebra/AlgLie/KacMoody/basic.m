freeze;

/* 
 * Affine Kac-Moody Lie algebras.
 *
 * Basic constructors.
 *
 * Dan Roozemond, 2011
 */

import "../../../LieThry/Root/Cartan.m":cartanToType, nameToType;

declare attributes AlgKac: 
		AffineCartanType, 
		FiniteCartanType,
		defaultCartanInj,	/* A sequence representing the injection from the default Cartan matrix 
								of type AffineCartanType to CartanMatrix*/
		stdE, stdF, stdH;	/* Sets of standard generators */


forward setStandardGenerators;

/* This function only does the basics -- some other things still
   need to be set by the caller. See the various intrinsics below. */
function affineLieAlgebra_construct(C, tp, F) //-> AlgKac
	//This is quite evil.
	tpf := &cat[ x : x in Eltseq(tp) | x ne "~" ];
	error if not IsFinite(RootSystem(tpf)), Sprintf("The finite version (%o) is not finite.", tpf);
	
	//Construct things, return.
	C := ChangeRing(C, Integers());
	LSR<t> := LaurentSeriesRing(F);
	Lf := LieAlgebra(tpf, F);
	L := InternalAffineKM(C, F, Lf, LSR);
	
	L`AffineCartanType := tp;
	L`FiniteCartanType := tpf;

	return L;
end function;

intrinsic AffineLieAlgebra(tp::MonStgElt, F::Fld) -> AlgKac
{Construct the affine (Kac-Moody) Lie algebra of type tp over field F}
	C := CartanMatrix(tp);
	assert IsGeneralizedCartanMatrix(C);
	require Seqset(KacMoodyClasses(C)) eq {"b"}: Sprintf("Not an affine type: %o", tp);
	
	//fix tp so that we get nice strings for AffineCartanType & FiniteCartanType
	ntt := nameToType(tp);
	tpstr := &cat[ t[1] cat IntegerToString(#t[2]-1) cat " ": t in ntt ];
	tpstr := tpstr[[1..#tpstr-1]]; //strip last space

	L := affineLieAlgebra_construct(C, tpstr, F);
	
	L`defaultCartanInj := [1..Ncols(C)];
	setStandardGenerators(~L);
	
	return L, L`t;
end intrinsic;
intrinsic AffineLieAlgebra(C::AlgMatElt, F::Fld) -> AlgKac
{Construct the affine (Kac-Moody) Lie algebra with Cartan matrix C over field F}

	tp := cartanToType(C);
	require forall{t : t in tp | t[1][#(t[1])] eq "~" }: "C is not an affine Cartan matrix.";

	tpstr := &cat[ t[1] cat IntegerToString(#t[2]-1) cat " ": t in tp ];
	tpstr := tpstr[[1..#tpstr-1]]; //strip last space
	injinv := &cat[t[2] : t in tp];
	inj := [ Position(injinv, i) : i in [1..#injinv] ]; //the position of the original row of the Cartan matrix in the "default" one.

	L := affineLieAlgebra_construct(C, tpstr, F);
	L`defaultCartanInj := inj;

	setStandardGenerators(~L);
	
	return L, L`t;
end intrinsic;

procedure setStandardGenerators(~L)
	Lf := FiniteLieAlgebra(L);
	t := L`t;
	E, F := ChevalleyBasis(Lf);
	//if type is not irreducible, then E contains first all the simple roots of the various constituents,
	//   and then the nonsimple ones (possibly mixed up).
	EF := E cat F;
	
	Rbig := RootDatum(L`FiniteCartanType);
	tp := nameToType(L`FiniteCartanType);
	offset := 0; es := [L|]; fs :=[L|]; 
	for tpc in tp do
		n := #tpc[2];
		_,injR := sub<Rbig | [ offset+1 .. offset+n ]>;
		R := RootDatum(tpc[1] cat IntegerToString(n));
		NPR := NumPosRoots(R);
		
		subEF := EF[injR];
		
		thetai_e := RootPosition(R, -HighestRoot(R));
		thetai_f := RootPosition(R, HighestRoot(R));

		es cat:= [ elt<L | <[<1, subEF[i]>],0,0>> : i in [1..n] ] cat [ elt<L | <[<t, subEF[thetai_e]>],0,0> > ];
		fs cat:= [ elt<L | <[<1, subEF[NPR+i]>],0,0>> : i in [1..n] ] cat [ elt<L | <[<t^-1, subEF[thetai_f]>],0,0> > ];

		offset +:= Rank(R);
	end for;
	hs := [ es[i]*fs[i] : i in [1..#es] ];
	
	inj := L`defaultCartanInj;
	L`stdE := es[inj];
	L`stdF := fs[inj];
	L`stdH := hs[inj];
end procedure;


intrinsic StandardGenerators(L::AlgKac) -> SeqEnum, SeqEnum, SeqEnum
{ The standard generators for L: sequences of positive, negative, coroots}
	return L`stdE, L`stdF, L`stdH;
end intrinsic;

intrinsic AssignNames(~L::AlgKac, s::SeqEnum[MonStgElt])
{ Internal. }
	assert #s eq 1;
	LSR := LaurentSeriesRing(L);
	AssignNames(~LSR, s);
	return;
end intrinsic;
intrinsic Name(L::AlgKac, i::RngIntElt) -> AlgKacElt
{ Internal }
	return LaurentSeriesRing(L).1;
end intrinsic;

/* Some accessor functions */
intrinsic CartanMatrix(L::AlgKac) -> AlgMatElt
{ The Cartan matrix of L }
	return L`CartanMatrix;
end intrinsic;
intrinsic CartanName(L::AlgKac) -> MonStgElt
{ The type of L }
	return L`AffineCartanType;
end intrinsic;


/* Silly things. */
intrinsic Dimension(L::AlgKac) -> Infty
{ Infinity. }
	return Infinity();
end intrinsic;




