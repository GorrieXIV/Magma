freeze;

/********************************************************************* 
                        Divisors on varieties
			=====================

GDB, MB, AJW 25 Dec 2010

We treat divisors as a sequence of 'factorisation' pairs
	< ideal in the ambient (projective) coordinate ring,
				multiplicity as a rational number >
and use sheaf machinery for RR.

Currently we work only on projective varieties.
We can add the ability to work in affine coordinates with the
projective closure being used implicitly.

N.B. Use the intrinsic IdealFactorisation(D) to access
	 D`ideal_factorisation to handle DivTorElt vs. DivSchElt

			Contents
			========

-- First examples of use; others throughout the file
-- Declare types and attributes
-- Creation of divisor group (as a dumb parent type for divisors)
-- Datatype housekeeping for divisors
-- Creation of divisors
-- Factorisations of defining ideals and applications
-- Arithmetic of divisors
-- Riemann-Roch and applications
-- Base points, mobility and Zariski decomposition
-- Pullback and pushforward of divisors

To do
=====
-- currently incorrect
	IsStrictlyNef(D)
	IsAmple(D)
Also IsNef(D) only applies to effective divisors, which is too weak.
-- currently missing
	EuclideanFactorisation(D)
	IsCartier(D)
	MobilePart(D)
	FixedPart(D)
	LCM(D,E)
	GCD(D,E)

Can we do devissage of a sheaf supported on a reducible curve
in a surface? Is it applicable?


*********************************************************************/


//////////////////////////////////////////////////////////////////////
/*		First example

k := Rationals();
P<x,y,z,t> := ProjectiveSpace(k,3);
X := Scheme(P, x^5 - y^5 + z^5 - t^5);
D := Divisor(X,x-y);
E := Divisor(X,z-t);
L := Divisor(X,[x-y,z-t]);
assert IsEffective(D+E-2*L);
assert IsNef(D+E-2*L);
assert SelfIntersection(D+E-2*L) eq 0;
V,phi := RiemannRochSpace(D+E-2*L);
Q<u,v,w> := ProjectiveSpace(k,Dimension(V)-1);
f := map< X -> Q | phi(Basis(V)) >;

*/
//////////////////////////////////////////////////////////////////////

// Add attributes to schemes to recognise divisor groups.
declare attributes Sch:
	divisor_group;

declare type DivSch[DivSchElt];

// Data type for a divisor group Div.
declare attributes DivSch:
	variety;		// The underlying variety X

// Data type for a divisor D in Div.
declare attributes DivSchElt:
			// Essential attributes:
	divisor_group,		// The parent divisor group of D
	ideal_factorisation,	// [<Ij,nj>] for ideals Ij, ints nj
                                // (we don't know whether nj are meant to be ints or rats)
	sign_split,		// split into [I,J] for integral D and ideals I,J where
				// D = [<I,1>,<J,-1>]. This is useful as it can be wasteful
				// reconstructing the I,J from a fuller ideal factorisation
				// In fact, in general, as well as performing the powerings
				// and multiplications of ideals from the current ideal
				// factorisation, it is also necessary to take the pure codimension
				// 1 part at the end to get rid of spurious lower dimensional
				// primary components (these can arise at points where some Ij factor
				// does not represent a Cartier (effective) divisor). This caused
				// errors in earlier versions.
			// Optional attributes:
	ideal,			// &*Ij^nj if all nj >= 0 (when
				// tidied up) -- only for effective
				// and integral D
	radical_ideal,		// radical of previous -- this is OK
				// even for Q-divisors D
	support,		// schemeZ(Rad(D`radical_ideal)) --
				// only for effective D
	is_prime,		// True iff D is prime
	selfintersection,	// D^2 (possibly rational number)
	is_nef,			// True iff D is nef
	is_strictly_nef,	// True iff D is strictly nef
	is_ample,		// True iff D is ample
	is_cartier,		// True iff D is Cartier
	is_principal,		// True iff D is principal
	principal_function,	// ... f in FF(X) st D = (f)
	sheaf,			// associated divisorial sheaf
	rr_numerators,		// A basis of RR space (in FF(X)) is
	rr_denominator,		//   f/g, where f in nums, g = denom
	rr_space,		// The Riemann-Roch space of D
	rr_space_map,		// RR comparison map: RR(D) -> FF(X)
	base_locus,		// reduced intersection of E in |D|
	negative_components;	// the prime components of effective
				// D that intersect D negatively

//////////////////////////////////////////////////////////////////////
/* Some common notation.
	X	underlying variety
	Xpr	projective closure of X
	P	hgs coord ring of the ambient P^N of Xpr
	I_X	ideal defining Xpr in P^N
*/
//////////////////////////////////////////////////////////////////////

declare verbose DivSch, 1;

forward is_easy_effective, is_easy_integral, zero_divisor_ideal;

//////////////////////////////////////////////////////////////////////
//		Divisor group
//////////////////////////////////////////////////////////////////////

intrinsic Print(G::DivSch,l::MonStgElt)
{Print the divisor group G (at print level l).}
    printf "Divisor group on ";
    print Variety(G):Minimal;
end intrinsic;

intrinsic IsCoercible(G::DivSch, D::.) -> BoolElt, DivSchElt
{True iff D can be coerced into the divisor group G, in which case
the resulting divisor is returned as a second value.}
    if Type(D) eq DivSchElt and IsIdentical(D`divisor_group, G) then
        return true, D;
    end if;
    return false,"Illegal coercion";
end intrinsic;

intrinsic 'in'(D::DivSchElt, G::DivSch) -> BoolElt
{True iff the divisor D can be coerced into the divisor group G}
    return IsIdentical(D`divisor_group, G);
end intrinsic;

intrinsic DivisorGroup(X::Sch) -> DivSch
{The divisor group of the variety X}
    if not assigned X`divisor_group then
        G:=New(DivSch);
        G`variety:=X;
        X`divisor_group:=G;
    end if;
    return X`divisor_group;
end intrinsic;

intrinsic Variety(G::DivSch) -> Sch
{The variety associated with the divisor group G}
    return G`variety;
end intrinsic;

intrinsic 'eq'(G1::DivSch,G2::DivSch) -> BoolElt
{True iff the divisor groups G1 and G2 are those of the same variety}
    return Variety(G1) eq Variety(G2);
end intrinsic;


//////////////////////////////////////////////////////////////////////
//			Divisors
//////////////////////////////////////////////////////////////////////

/* Not necessary - not implemented for curves.
intrinsic DivisorGroup(D::DivSchElt) -> DivSch
{The divisor group containing the divisor D.}
	return D`divisor_group;
end intrinsic;
*/

intrinsic Variety(D::DivSchElt) -> Sch
{The variety on which the divisor D lies.}
	return Variety(D`divisor_group);
end intrinsic;


//////////////////////////////////////////////////////////////////////
//			Housekeeping
//////////////////////////////////////////////////////////////////////

//intrinsic Print(D::DivSchElt,l::MonStgElt,name::MonStgElt)

intrinsic Print(D::DivSchElt,l::MonStgElt)
{Print a description of the divisor D.}
	if l eq "Minimal" then
		printf "Divisor on ";
		print Variety(D):Minimal;
	else
		factn := IdealFactorisation(D);
//		if IsPrime(D) then // Don't compute prime factorisation! -MJB
                if assigned D`is_prime and D`is_prime then
			printf "Prime divisor";
//		elif IsFactorisationPrime(D) then // Don't do that either
//			printf "Divisor with prime factorisation";
		else
			printf "Divisor with factorisation";
		end if;
		for i in [1..#factn] do
			Im := factn[i];
			if i ne 1 then
				printf "\n + ";
			else
				printf "\n   ";
			end if;
			printf "%o * ( ", Im[2];
			for f in Basis(Im[1]) do
				printf "%o = ", f;
			end for;
			printf "0 )";
		end for;
	end if;
end intrinsic;

intrinsic Parent(D::DivSchElt) -> DivSch
{The divisor group containing the divisor D.}
    return D`divisor_group;
end intrinsic;

// THINK: do we like this shortcut to the RR space or not?
// Definitely give it a special name (this is not a standard 'in')

/*

intrinsic HackobjInDivSchElt(f::., D::DivSchElt) -> BoolElt
{True iff the rational function f lies in the Riemann-Roch space of the divisor D, in which case also return the coordinates of f with respect to the fixed basis of that RR space.}
    X := Variety(D);
    FF := FunctionField(Ambient(X));
    iscoer,ff := IsCoercible(FF,f);
    if iscoer then
	    if not assigned D`rr_numerators
		or not assigned D`rr_denominator then
		    _ := RiemannRochSpace(D);  // forces their calculation
	    end if;
	    return compute_rr_coords(X,ff,D);
    else
    	require false: "Argument f must be coercible into the " *
		"function field of the ambient space of the " *
		"variety of the divisor D";
    end if;
end intrinsic;

*/

// THINK: Hash function for divisors?
// intrinsic HackobjHashDivSchElt(D::DivSchElt) -> RngIntElt


//////////////////////////////////////////////////////////////////////
//			Creation
//////////////////////////////////////////////////////////////////////

// Given f in the (scheme) function field of projective space P,
// return a hgs degree 0 rational function in the quotient field
// of the hgs coord ring of P that represents f.
// Isn't this the same as ProjectiveFunction() ? -MJB
function ff2quotfld(P,f)
	R := CoordinateRing(P);
	rk := Rank(R);
	F := FunctionField(P);
	// Check that the homogenisation is R.rk = 1.

	test_elt := F!(R.1/R.rk);
	assert Numerator(test_elt) eq F.1 and
		Denominator(test_elt) eq 1;
	num := Numerator(f);
	den := Denominator(f);
	max_deg := Maximum([Degree(num),Degree(den)]);
	phi := hom< Parent(num) -> R | [R.i : i in [1..rk-1]] >;
	return Homogenization(phi(num),R.rk,max_deg) /
			Homogenization(phi(den),R.rk,max_deg);
end function;

intrinsic Divisor(X::Sch, f::FldFunFracSchElt :
	CheckDimension:=false, CheckSaturated:=false ) -> DivSchElt
{}
	return Divisor(X, ff2quotfld(Ambient(X),f) :
		CheckDimension:=CheckDimension, CheckSaturated:=CheckSaturated);
end intrinsic;

intrinsic Divisor(X::Sch, f::FldFunRatMElt :
	CheckDimension:=false, CheckSaturated:=false ) -> DivSchElt
{}
	if ISA(Type(X),TorVar) and IsField(BaseRing(X)) then
		return Divisor(X, Numerator(f)) - Divisor(X, Denominator(f));
	else
		Dn := Divisor(X, Numerator(f) :
			CheckDimension:=CheckDimension, CheckSaturated:=CheckSaturated);
		Dd := Divisor(X, Denominator(f) :
			CheckDimension:=CheckDimension, CheckSaturated:=CheckSaturated);
		D := New(DivSchElt);
		D`divisor_group := DivisorGroup(X);
		D`ideal_factorisation := [ <Dn`ideal, 1 >, <Dd`ideal, -1> ];
		D`sign_split := [Dn`ideal,Dd`ideal];
		D`is_cartier := true; // Good to set this - mch
		return D;		
	end if;
end intrinsic;

intrinsic Divisor(X::Sch, f::RngMPolElt :
	CheckDimension:=false, CheckSaturated:=false ) -> DivSchElt
{}
	if TotalDegree(f) eq 0 then
		return ZeroDivisor(X);
	else
		D := Divisor(X, Ideal(f)+Ideal(X) : CheckDimension:=CheckDimension,
			CheckSaturated:=CheckSaturated);
		if not (assigned D`is_cartier) then D`is_cartier := true; end if;
		return D;
	end if;
end intrinsic;

intrinsic Divisor(X::Sch, Q::SeqEnum :
	CheckDimension:=false, CheckSaturated:=false, UseCodimensionOnePart := false) -> DivSchElt
{}
	return Divisor(X, Ideal(Q)+Ideal(X) :
		CheckDimension:=CheckDimension, CheckSaturated:=CheckSaturated, UseCodimensionOnePart := UseCodimensionOnePart);
end intrinsic;

intrinsic Divisor(X::Sch, Y::Sch :
	CheckDimension:=false, CheckSaturated:=false ) -> DivSchElt
{}
	return Divisor(X, Ideal(Y) :
		CheckDimension:=CheckDimension, CheckSaturated:=CheckSaturated);
end intrinsic;

intrinsic Divisor(X::Sch, I::RngMPol : CheckDimension:=false,
	CheckSaturated:=false, UseCodimensionOnePart := false ) -> DivSchElt
{The divisor on X defined by (the top dimensional part of) the ideal I (generated by the polynomial or rational function f or sequence of polynomials Q or scheme Y).}
// The parameter 'CheckSaturated' can be set to true if it is known
// that I is saturated w.r.t. the irrelevant ideal. (Only relevant
// when X is projective.)
// The parameter 'CheckDimension' can be set to true if it is known
// that I defines a pure codimension 1 subscheme of X.
// The parameter 'UseCodimensionOnePart' can be set to be true if you
// are happy for the constructor to discard higher codim components of I.

	if IsProjective(X) then
		if not CheckSaturated then
			I := Saturation(I);
		end if;
		if not CheckDimension then
			IX := DefiningIdeal(X);
			P := Generic(IX);
			require Generic(I) eq P: "Ideal I is not defined on the ambient space of scheme X.";
			preZ := Scheme(X,I);
			I := EquidimensionalPart(DefiningIdeal(preZ));
			Z := Scheme(X,I);
			if UseCodimensionOnePart then
			    if Dimension(Z) lt Dimension(X) - 1 then
			    	return ZeroDivisor(X);
			    end if;
			    require Dimension(Z) ne Dimension(X): "The top-dimensional component of the subscheme of scheme X defined by the ideal I is not codimension 1 in X";
			else
			    require Dimension(Z) eq Dimension(X) - 1: "The top-dimensional component of the subscheme of scheme X defined by the ideal I is not codimension 1 in X";
			end if;
		end if;
		D := New(DivSchElt);
		D`divisor_group := DivisorGroup(X);
                D`ideal := I; // Might as well remember it -MJB
		D`ideal_factorisation := [ < I, 1 > ];
		D`sign_split := [I,Generic(I)];
		if (assigned X`Nonsingular) and X`Nonsingular then
		  D`is_cartier := true; // Good to set this - mch
		end if;
		return D;

/* THINK: ability to work on affine patches, etc.
	else	// we work on the projective closure, although
		// I may be an ideal on X or its proj closure.
		IX := DefiningIdeal(X);
		P := Generic(IX);
		if Generic(I) eq P then
		else	// maybe I is an ideal on proj closure of X
		end if;
		require false: "Ideal I does not define a subscheme of
			scheme X (or its projective closure)";
*/
	else
		require false: "Divisors on schemes only implemented on projective schemes";	// THINK: could extend to affine schemes as above
	end if;
end intrinsic;

intrinsic HyperplaneSectionDivisor(X::Sch) -> DivSchElt
{A hyperplane section of the variety X as a divisor on X.}
	return Divisor(X,CoordinateRing(Ambient(X)).1);
end intrinsic;

intrinsic ZeroDivisor(X::Sch) -> DivSchElt
{The zero divisor on the variety X.}
	D := New(DivSchElt);
	D`divisor_group := DivisorGroup(X);
	D`ideal_factorisation := [ Parent(< DefiningIdeal(X),1>) | ];
	D`sign_split := [R,R] where R is CoordinateRing(Ambient(X));
	D`ideal := zero_divisor_ideal(X);
	D`is_cartier := true;
	return D;
end intrinsic;

// added 21/12/12 mch
intrinsic SheafToDivisor(S::ShfCoh) -> DivSchElt
{ A divisor D such that invertible sheaf S on X is isomorphic to O_X(D), effective if possible }

	X := Scheme(S);
	R := CoordinateRing(Ambient(X));
	F := FullModule(S);
	wts := ColumnWeights(F);
	assert #wts gt 0;
	wtsn := [w : w in wts | w le 0];
	w := (#wtsn gt 0) select Max(wtsn) else Min(wts);
	i := Index(wts,w);
	vec := [R!0 : j in [1..#wts]]; vec[i] := R!1;
	s := F!vec;
	if w eq 0 then
	    f := R!1;
	else
	    w1 := Abs(w);
	    k := 0;
	    Saturate(~X);
	    for j in [1..Rank(R)] do
		if not (R.j in Ideal(X)) then
		    k := j; break;
		end if;
	    end for;
	    error if k eq 0, "Base scheme X of S is not a variety";
	    f := (R.k)^w1;
	end if;
	I := Annihilator(quo<F|s>);
	// D is (I) +/- (f) with the sign is -sign(w) 
	D := New(DivSchElt);
	D`divisor_group := DivisorGroup(X);
	if #wtsn gt 0 then
	    if f ne R!1 then
		I := ideal<R|[f*e : e in Basis(I)]>+Ideal(X);
	    end if;
	    I := Saturation(I);
	    D`ideal_factorisation := [ < I, 1 > ];
	    D`sign_split := [I,R];
	    D`ideal := I;
	else
	    I := Saturation(I);
	    J := Ideal(X)+ideal<R|f>;
	    D`ideal_factorisation := [ < I, 1 >, <J,-1> ];
	    D`sign_split := [I,J];
	end if;
	D`is_cartier := true; // S really should be invertible!
	return D;

end intrinsic;

intrinsic CanonicalDivisor(X::Sch) -> DivSchElt
{A canonical divisor for the variety X.}
	return SheafToDivisor(CanonicalSheaf(X));
end intrinsic;

/*intrinsic CanonicalDivisor(X::Sch) -> DivSchElt
{A canonical divisor for the variety X.}
// Idea: take twists n of the canonical sheaf until its DivisorMap
// is nontrivial. Any component of the defining equations of that
// map define the mobile part of K_X + nH.
// THINK: do we need to look for a fixed part?
// To try to keep the modules (and DivisorMap calculations) small,
// start with a negative twist of the canonical sheaf.
	// Estimate an appropriate negative twist d to start with.
	currenttwist := -Degree(X);
	S := Twist(CanonicalSheaf(X),currenttwist);
	repeat
		S := Twist(S,1);
		currenttwist +:= 1;
		mS := DivisorMap(S);
		// compute the number of vars of the codomain
		if Type(mS) eq MapSchGrph then
			codimvars := Rank(Generic(mS`GraphIdeal))
				- Rank(CoordinateRing(Ambient(X)));
		else	// Type(mS) eq MapSch
			codimvars := Rank(CoordinateRing(
				Ambient(Codomain(mS))));
		end if;
	until codimvars ge 2;
	if Type(mS) eq MapSchGrph then
		mS := SchemeGraphMapToSchemeMap(mS);
	end if;
	f := DefiningEquations(mS)[1];
	KX := Divisor(X,f) - currenttwist*HyperplaneSectionDivisor(X);
	assert IsCanonical(KX);	// Check: but this may cost time
	return KX;
end intrinsic;*/

intrinsic FractionalPart(D::DivSchElt) -> DivSchElt
{The effective fractional part of the divisor D, that is, the difference D - rounddown(D).}
	X := Variety(D);
	if IsIntegral(D) then
		return ZeroDivisor(X);
	end if;
	// IsIntegral would have computed a prime (or Eucl)
	// factorisation before it returned false to get here.
	E := New(DivSchElt);
	E`divisor_group := DivisorGroup(X);
	E`ideal_factorisation := [ Parent(< DefiningIdeal(X),1>) |
			< Im[1], Rationals()!(Im[2]-Floor(Im[2]))>
				: Im in IdealFactorisation(D) | not IsZero(Im[2]-Floor(Im[2])) ];
	return E;
end intrinsic;

intrinsic RoundDownDivisor(D::DivSchElt) -> DivSchElt
{The integral divisor whose coefficients of prime components are the round down of those coefficients in the divisor D.}
	if IsIntegral(D) then
		return D;
	end if;
	X := Variety(D);
	// IsIntegral would have computed a prime (or Eucl)
	// factorisation before it returned false to get here.
	E := New(DivSchElt);
	E`divisor_group := DivisorGroup(X);
	E`ideal_factorisation := [ Parent(< DefiningIdeal(X),1>) |
			< Im[1], Rationals()!Floor(Im[2])>
				: Im in IdealFactorisation(D) | not IsZero(Floor(Im[2])) ];
	return E;
end intrinsic;

intrinsic RoundUpDivisor(D::DivSchElt) -> DivSchElt
{The integral divisor whose coefficients of prime components are the round up of those coefficients in the divisor D.}
	if IsIntegral(D) then
		return D;
	end if;
	// IsIntegral would have computed a prime (or Eucl)
	// factorisation before it returned false to get here.
	X := Variety(D);
	E := New(DivSchElt);
	E`divisor_group := DivisorGroup(X);
	E`ideal_factorisation := [ Parent(< DefiningIdeal(X),1>) |
			< Im[1], Rationals()!Ceiling(Im[2])>
				: Im in IdealFactorisation(D) | not IsZero(Ceiling(Im[2])) ];
	return E;
end intrinsic;


//////////////////////////////////////////////////////////////////////
//		Ideals and factorisations
//////////////////////////////////////////////////////////////////////

// added mch -11/13 - for the 0 divisor, I think the ideal should be
//  the maximal ideal of the coordinate ring in the projective case,
//  because Scheme(Ambient(X),ideal) should give the divisor as a
//  subscheme of X and this isn't allowed with 1 in ideal in the proj. case
function zero_divisor_ideal(X)
    R := CoordinateRing(Ambient(X));
    if IsAffine(X) then 
	return ideal<R|R!1>;
    else
	return ideal<R|Setseq(MonomialsOfDegree(R,1))>;
    end if;
end function;

intrinsic IdealFactorisation(D::DivSchElt) -> SeqEnum
{The factorisation of the divisor D into ideals and multiplicities currently recorded and used for D.}
	if not assigned D`ideal_factorisation then
		m := DefiningMonomial(D);
		if Type(m) eq RngMPolElt then
			D`ideal_factorisation := [ <Ideal([m]),1>];
		else
			m1 := Numerator(m);
			m2 := Denominator(m);
			D`ideal_factorisation := [ <Ideal([m1]),1>, <Ideal([m2]),-1>];
		end if;
	end if;
	return D`ideal_factorisation;
end intrinsic;

intrinsic ReducedFactorisation(D::DivSchElt) -> SeqEnum
{A factorisation of the divisor D into radical (but not necessarily prime) ideals and multiplicities.}
	ComputeReducedFactorisation(~D);
	return IdealFactorisation(D);
end intrinsic;

intrinsic PrimeFactorisation(D::DivSchElt) -> SeqEnum
{The factorisation of the divisor D into prime ideals and multiplicities.}
	ComputePrimeFactorisation(~D);
	return IdealFactorisation(D);
end intrinsic;

intrinsic SignDecomposition(D::DivSchElt) ->  DivSchElt, DivSchElt
{Two effective divisors A,B such that D = A - B.}
	factn := IdealFactorisation(D);
	R := CoordinateRing(Ambient(Variety(D)));
	A := New(DivSchElt);
	A`divisor_group := DivisorGroup(Variety(D));
	B := New(DivSchElt);
	B`divisor_group := DivisorGroup(Variety(D));
	if assigned D`sign_split then // D is integral!
	  IA := (D`sign_split)[1];
	  if IsProper(IA) then
	    A`ideal_factorisation := [<IA, 1>];
	    A`ideal := IA;
	    A`sign_split := [IA,R];
	  else
	    A := ZeroDivisor(Variety(D));
	  end if;
	  IB := (D`sign_split)[2];
	  if IsProper(IB) then
	    B`ideal_factorisation := [<IB, 1>];
	    B`ideal := IB;
	    B`sign_split := [IB,R];
	  else
	    B := ZeroDivisor(Variety(D));
	  end if;
	  if assigned D`is_cartier then
	    if assigned A`is_cartier then // A = zero divisor
		B`is_cartier := D`is_cartier;
	    elif assigned B`is_cartier then // B = zero divisor
		A`is_cartier := D`is_cartier;
	    end if;
	  end if;	  
	else
	  A`ideal_factorisation :=
		[ Parent(<R,1/2>) | Im : Im in factn | Im[2] ge 0 ];
	  B`ideal_factorisation := [ Parent(<R,1/2>) |
		<Im[1],-Im[2]> : Im in factn | Im[2] lt 0 ];
	end if;
	return A,B;
end intrinsic;

intrinsic IsFactorisationPrime(D::DivSchElt) -> BoolElt
{True iff all (nontrivial) factors in the factorisation of the divisor D are prime.}
	CombineIdealFactorisation(~D);
	for Im in IdealFactorisation(D) do
		if not IsPrime(Im[1]) then
			return false;
		end if;
	end for;
	return true;
end intrinsic;

intrinsic Ideal(D::DivSchElt) -> RngMPol
{An ideal defining the effective divisor D.}

	// clause added mch - 11/12 - avoids some complications?
	if is_easy_effective(D) and is_easy_integral(D) then
	  if not assigned D`ideal then
	    Dfactn := IdealFactorisation(D);
	    n := &+[Integers()| f[2] : f in Dfactn];
	    if n eq 0 then
	      I := zero_divisor_ideal(Variety(D));
	    elif n eq 1 then
	      I := Dfactn[Index([f[2] : f in Dfactn],1)][1];
	    else
	      if assigned D`sign_split and not IsProper(D`sign_split[2]) then
		I := D`sign_split[1];
	      else
                I := EquidimensionalPart(Ideal(Variety(D)) +
	           &*[Im[1] ^ (Integers()!Im[2]) : Im in Dfactn ]);
	      end if;
	    end if;
	    D`ideal := I;
	  end if;
	  return D`ideal;
	end if;
	require IsEffective(D):
		"The argument D is not an effective divisor";
	require IsIntegral(D):
		"The argument D is not an integral divisor";
	if not assigned D`ideal then
		R := CoordinateRing(Ambient(Variety(D)));
		Dfactn := IdealFactorisation(D);
		if #Dfactn ne 0 then
		  if #Dfactn eq 1 and Dfactn[1][2] eq 1 then
		    D`ideal := Dfactn[1][1];
		  else
		    D`ideal := EquidimensionalPart( Ideal(Variety(D)) +
			    (&*[F[1]^(Integers()!F[2]) : F in Dfactn]));
		  end if;
		else
		  D`ideal := zero_divisor_ideal(Variety(D));
		end if;
	end if;
	return D`ideal;
end intrinsic;

intrinsic IdealOfSupport(D::DivSchElt) -> RngMPol
{An ideal defining the support of the effective Q-divisor D.}
	require IsEffective(D):
		"The argument D is not an effective divisor";
	if not assigned D`radical_ideal then
		if assigned D`ideal then
			D`radical_ideal := Radical(D`ideal);
		else
			R := CoordinateRing(Ambient(Variety(D)));
			Dfactn := IdealFactorisation(D);
			if #Dfactn ne 0 then
				D`radical_ideal := Radical(&*[
					Parent(R) | F[1] :
						F in Dfactn]);
			else
				D`radical_ideal := R;
			end if;
		end if;
	end if;
	return D`radical_ideal;
end intrinsic;

// added mch - 11/12 - avoid the ubiquitous prime factorisation!
//  gives non-definitive answer, but good for quick check
function is_easy_effective(D)
    if not IsOrdinaryProjective(Variety(D)) then return false; end if;
    return &and[ Im[2] ge 0 : Im in D`ideal_factorisation ];
end function;

intrinsic IsEffective(D::DivSchElt) -> BoolElt
{True iff the divisor D is effective.}
	if &and[ Im[2] ge 0 : Im in IdealFactorisation(D) ] then
		return true;
	else
		// THINK: could use only the EuclideanFactorisation
		ComputePrimeFactorisation(~D);
		return &and[ Im[2] ge 0 :Im in IdealFactorisation(D) ];
	end if;
end intrinsic;

intrinsic IsCanonical(D::DivSchElt) -> BoolElt
{True iff the divisor D is a canonical divisor.}
	bool := IsIsomorphic(CanonicalSheaf(Variety(D)),Sheaf(D));
	return bool;	// have thrown away 2nd return value of IsIso
end intrinsic;

intrinsic IsAnticanonical(D::DivSchElt) -> BoolElt
{True iff the divisor D is an anticanonical divisor.}
	bool := IsIsomorphic(
		Dual(CanonicalSheaf(Variety(D))),Sheaf(D));
	return bool;
end intrinsic;

intrinsic IsCanonicalWithTwist(D::DivSchElt) -> BoolElt,RngIntElt
{True iff some (integral) twist by the hyperplane section of the divisor D is a canonical divisor, in which case this integer twist is also returned.}
	bool,n := IsIsomorphicWithTwist(
		CanonicalSheaf(Variety(D)),Sheaf(D));
	if bool then
		return bool,n;
	else
		return bool,_;
	end if;
end intrinsic;

/* Example
P3<x,y,z,t> := ProjectiveSpace(Rationals(),3);
X := Scheme(P3, &+[ P3.i^9 : i in [1..4] ]);
D := Divisor(X,x^2 - y^2);
bool,n := IsCanonicalWithTwist(D);
assert n eq 3;
assert bool;
H := HyperplaneSectionDivisor(X);
assert IsCanonical(D + n*H);
*/

// added mch - 11/12 - avoid the ubiquitous prime factorisation!
//  gives non-definitive answer, but good for quick check
function is_easy_integral(D)
    if not IsOrdinaryProjective(Variety(D)) then return false; end if;
    return &and[ IsCoercible(Integers(),Im[2]) : Im in D`ideal_factorisation ];
end function;

intrinsic IsIntegral(D::DivSchElt) -> BoolElt
{True iff the divisor D is integral (possibly after combining irreducible factors).}
	if &and[ IsCoercible(Integers(),Im[2])
			: Im in IdealFactorisation(D) ] then
		return true;
	else
		// THINK: could use only the EuclideanFactorisation
		ComputePrimeFactorisation(~D);
		return &and[ IsCoercible(Integers(),Im[2])
			: Im in IdealFactorisation(D) ];
	end if;
end intrinsic;

intrinsic IsDivisible(D::DivSchElt) -> BoolElt,RngIntElt
{True iff the divisor D is integral and divisible by an integer n > 1, in which case the integer n is also returned.}
	isint := IsIntegral(D);
	if not isint then
		return false,_;
	end if;
	// THINK: could use only the EuclideanFactorisation
	n := GCD([Integers()| Im[2] : Im in PrimeFactorisation(D)]);
	if n gt 1 then
		return true,n;
	else
		return false,_;
	end if;
end intrinsic;

intrinsic IsPrime(D::DivSchElt) -> BoolElt
{True iff the divisor D is prime.}
	if not assigned D`is_prime then
		if assigned D`ideal then
			D`is_prime := IsPrime(D`ideal);
		else
			// remove any zeros in the factorisation
      			factn := IdealFactorisation(D);
			CombineIdealFactorisation(~D);
                        // THINK: surely need to do at
                        // least Euclidean factorisation here? -MJB
			D`is_prime := #factn eq 1 and factn[1][2] eq 1
				and IsPrime(factn[1][1]);
		end if;
	end if;
	return D`is_prime;
end intrinsic;

intrinsic IsZeroDivisor(D::DivSchElt) -> BoolElt
{True iff the divisor D is the zero divisor.}
	if #IdealFactorisation(D) eq 0 then	// trivial case
		return true;
	end if;
	// THINK: could use only the EuclideanFactorisation
	ComputePrimeFactorisation(~D);
	return #IdealFactorisation(D) eq 0;
end intrinsic;

// Martin Bright - 01/13 - faster version in non-singular/Cartier case.
// Return the maximal m such that I is contained in Saturation(P^m + IX).
// This is equal to the multiplicity of P in I as long as the ambient
// variety defined by IX is locally factorial or P is Cartier. 
// (Otherwise, P^m + IX can have extra components supported at the singular
// points where it is not locally-principal).
// However, this doesn't compute the 'quotient' of I by P^mult
function easyidealmult(X,I,P)
	IX := Ideal(X);
	if IsProjective(X) then
	  vprint DivSch: "Passing to affine piece...";
	  // Move to an affine piece, to avoid need for saturation
	  n := Ngens(P);
	  assert exists(i) { i : i in [1..n] | P.i notin P };
	  R := PolynomialRing(BaseRing(P), n-1, "grevlex");
	  f := hom< Generic(P) -> R |
	        [R.j : j in [1..i-1]] cat [1] cat [R.j : j in [i..n-1]] >; 
	  I := Extension(f,I);
	  P := Extension(f,P);
	  IX := Extension(f,IX);
	end if;
	
	// Now find the power of P containing I
	vprintf DivSch: "Finding multiplicity...";
	m := 0;
	Q := P;
	while I subset Q do
		m +:= 1;
		vprintf DivSch: "%o ", m;
		Q := Q*P + IX; // THINK: compute Groebner basis?
	end while;
	vprint DivSch: ".";
	return m;	
end function;

// P is a prime ideal, I any ideal (in the same poly ring).
// Return the multiplicity of P in the primary decomposition of I.
// (We only use this when I,P are equidimensional of same dim.)
function idealmult(I,P)
	m := -1;
	repeat
		m +:= 1;
		previousI := I;
		I := ColonIdeal(I,P);
	until I eq previousI;
	return m,I;
end function;

intrinsic Multiplicity(D::DivSchElt,E::DivSchElt) -> FldRatElt
{The multiplicity of the prime divisor E in the divisor D. Replaces the
 old factorisation of D with a new one containing E with the multiplicity
 and other terms where the maximal power of E has been divided out.}
	require IsPrime(E):
		"The second argument E must be a prime divisor";
	P := Ideal(E);
	multiplicity := 0;
	oldfactn := IdealFactorisation(D);
	newfactn := [ Universe(oldfactn) | ];
	for Im in oldfactn do
		I := Im[1];
		m := Im[2];
		multP,ImodP := idealmult(I,P);
		multiplicity +:= m * multP;
		Append(~newfactn, < ImodP, m >);
	end for;
	Append(~newfactn, < P, multiplicity >);
	D`ideal_factorisation := newfactn;
	return multiplicity;
end intrinsic;

intrinsic MultiplicityFast(D::DivSchElt,E::DivSchElt) -> FldRatElt
{The multiplicity of the prime divisor E in the divisor D. Requires E to
be Cartier and doesn't update the ideal factorisation of D.}

	require IsPrime(E):
		"The second argument E must be a prime divisor";
	P := Ideal(E);
        // Error if E known non-Cartier. Don't call the intrinsic
        //  to check Cartierness here though.
	require (not assigned E`is_cartier) or E`is_cartier:
		"E is not Cartier";
	multiplicity := 0;
	factn := IdealFactorisation(D);
	X := Variety(D);
	//easyidealmult currently works for affine and ordinary projective vars
	require (IsAffine(X) or IsOrdinaryProjective(X)) :
	   "The variety of D must be affine or ordinary projective";
	for Im in factn do
		I := Im[1];
		m := Im[2];
		multP := easyidealmult(X,I,P);
		multiplicity +:= m * multP;
	end for;
	return multiplicity;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///// Faster version of multiplicity for divisors where all prime divisors ////
/// of the support are already known. Tries to use reduction to dimension   ///
/// 1 by taking random hyperplane sections and then uses curve 		    ///
///    functionality - original version Martin Bright 01/13		    ///
///////////////////////////////////////////////////////////////////////////////

// Assuming IX defines a projective curve X, I a divisor on it, and P a
// sequence of places, find the multiplicities.
// If an element of P is not prime, we'll choose a prime component.
//
//  added - mch 11/13 - in very rare cases X might be reducible (though
//  all components should be one dimensional and reduced). Check this
//  with HasFunctionField weak check which should add no real overhead
//  as the function field is needed anyway. If this fails then have to
//  decompose X into components and do relevant computation on each.
//  Also changed to doing things for I a sequence of ideals of divisors
//  so as not to have to do all the hyperplane section stuff multiple
//  times.

function idealmult_irred_curve(C,Ds,P)
// isolated out code from function below for when we have definitely
//  reduced to the case of an irreducible curve.
	vprintf DivSch: "%o\nGetting multiplicities...\n", Ds;
	v := [[Integers()|] : i in [1..#Ds]];
	for p in P do
	  places, mults := Support(Divisor(C,p));
	  for i in [1..#Ds] do
	    Append(~(v[i]), Integers()!(Valuation(Ds[i],places[1]) / mults[1]));
	  end for;
	end for;
	return v;
end function;

function idealmult_curve(IX,I,P)
	vprintf DivSch: "Creating divisors on curve...";
	Pr := Proj(Generic(IX));
	C := Curve(Pr, IX);
	if HasFunctionField(C) then
	  Ds := [Divisor(C, Ii) : Ii in I];
	  return idealmult_irred_curve(C,Ds,P);
	else
	  Cs := IrreducibleComponents(C);
	  Pinds := [1..#P];
	  v := [[0 : i in Pinds] : j in [1..#I]];
	  for Ci in Cs do
	    ICi := Ideal(Ci);
	    //if Dimension(Ii) eq 0 then //Ii <-> 0 divisor
	    //	continue;
	    //end if;
	    Pis := []; Pcmps := [];
	    for j := #Pinds to 1 by -1 do
		Pi := ICi+P[Pinds[j]];
		if Dimension(Pi) ge 1 then //P[Pinds[j]] meets Ci
		  Append(~Pis, Pinds[j]);
		  Append(~Pcmps,Pi);
		  Remove(~Pinds,j);
		end if;		
	    end for;
	    if #Pis eq 0 then continue; end if;
	    Iinds := []; Icmps := [];
	    if #I gt 1 then
	      for j in [1..#I] do
		Iij := ICi+I[j];
		if Dimension(Iij) ge 1 then //I[j] meets Ci
		  Append(~Iinds, j);
		  Append(~Icmps,Iij);
		end if;		
	      end for;
	    else // only one Ij must meet Ci!
	      Iinds := [1]; Icmps := [ICi+I[1]];
	    end if;
	    if #Pis eq 0 then continue; end if;		
	    vi := idealmult_irred_curve(Ci,
			[Divisor(Ci,Iij) : Iij in Icmps],[P[j] : j in Pis]);
	    for i in [1..#Iinds], j in [1..#Pis] do 
		v[Iinds[i]][Pis[j]] := vi[i][j];
	    end for;
	  end for;
	  assert #Pinds eq 0; // all elts in P now dealt with
	  return v;
	end if;
end function;

// Given a polynomial ring R in n variables, and a vector representing
// a hyperplane in Proj R, return a new polynomial ring in n-1 variables
// and the homorphism corresponding to the inclusion of the hyperplane.
function hyperplane_map(R,v)
	// Choose a variable to represent in terms of the others
	n := Ngens(R);
	assert exists(i) { i : i in [1..n] | v[i] ne 0 };
	S := PolynomialRing(BaseRing(R),n-1,"grevlex");
	// Construct the map
	x := (i gt 1) select &+[ v[j]*S.j : j in [1..i-1]] else S!0;
	if (i lt n) then x +:= &+[ v[j]*S.(j-1) : j in [i+1..n]]; end if;
	x := -x / v[i];
	y := [S.j : j in [1..i-1]] cat [x] cat [S.j : j in [i..n-1]];
	return hom< R -> S | y >;
end function;

// Here P should be the list of all prime ideals in the support of
// the effective integral divisors defined by the list of ideals I.
// Uses a reduction to dimension 1 and
// curve functionality to compute the multiplicities of all p in P.
//
// Extra checks on validity of hyperplane sections added mch - 11/13
function idealmult_slice(IX,I,P)
	d := Dimension(P[1]);

	if d eq 1 then
		return idealmult_curve(IX,I,P);
	end if;

	// Reduce to smaller dimension
	// Choose a hyperplane - we'll just try coordinate
	// hyperplanes for now
	R := Generic(IX);
	n := Ngens(IX);
	L := StandardLattice(n);
	vprint DivSch: "Looking for good hyperplane slice...";
	for i in [1..20] do // could make this an unbounded loop...
		for v in [ v : w in ShortVectors(L,i,i) | Gcd(v) eq 1 where v is Eltseq(w[1]) ] do
			// We want a hyperplane H satisfying:
			//   H doesn't contain any components of X or P_j
			//   No two P_j have a common component after intersecting
			//     with H
			//   After intersecting with H, P_j remains a smooth
			//     place of X
			f := hyperplane_map(R,v);
			Pnew := [ Extension(f,p) : p in P ];
			if exists(p) { p : p in Pnew | Dimension(p) ge d } then
				continue; // Contained a component of some P_j
			end if;
			if exists(j) { j : k in [j+1..#P], j in [1..#P] |
				Dimension(Pnew[j]+Pnew[k]) ge d-1 } then
				continue; // Contained a component of some P_j meet P_k
			end if;
			IXnew := Extension(f,IX);
			if Dimension(IXnew) gt d then
				continue; // Contained a component of X
			end if;
			// mch - 11/13 - need to check that the hyperplane
			// doesn't intersect X in any component 'with multiplicity'.
			// Use check that X is generically non-singular, as the
			// Jacobian ideal is needed for the stronger not_is_singular_at
			// test anyway.
			B := MinimalBasis(IXnew);
			jac := JacobianMatrix(B);
			JXnew := ideal<Generic(IXnew)|Minors(jac, Rank(IXnew)-d)>;
			if Dimension(JXnew+IXnew) ge d then
				continue; // Multiple component of H meet X
			end if;
			// mch - 11/13 - Shouldn't assume that p in P(new) are irreducible,
			// so need a stonger test than the old not is_singular_at. Want
			// no component of any p to lie in the non-smooth component of Xnew.
			// Check with dimension test using JXnew
			if forall(p) { p : p in Pnew | Dimension(JXnew+p) lt d-1 } then
				vprint DivSch: "Using hyperplane", v;
				// Recurse
				return idealmult_slice(IXnew, [Extension(f,Ii): Ii in I], Pnew);
			end if;
		end for;
	end for;
	error "Couldn't find nice hyperplane section";
end function;

intrinsic Multiplicities(D::DivSchElt,P::SeqEnum[DivSchElt]) -> SeqEnum
{ D is a divisor on an ordinary projective variety and P is a sequence of
  prime divisors that should contain all prime divisors in the support of D.
  Returns the sequence of multiplicities of D at the p in P using a reduction
  to dimension 1 via taking iterated hyperplane sections }

	// As this is supposed to be a fast function, we don't do the
        // check that the divisors in P are prime!
	Ps := [Ideal(p) : p in P];
	mults := [0 : i in [1..#P]];
	oldfactn := IdealFactorisation(D);
	newfactn := [ Universe(oldfactn) | ];
	X := Variety(D);
	require IsOrdinaryProjective(X): "variety of D must be ordinary projective";
	Is := [Im[1] : Im in oldfactn];
	ms := [Im[2] : Im in oldfactn];
	mults := idealmult_slice(Ideal(X),Is,Ps);
	mults := [&+[ms[j]*mults[j][i] : j in [1..#Is]] : i in [1..#P]];
	return mults;
end intrinsic;  

intrinsic CombineIdealFactorisation(~D::DivSchElt)
{Simplify the ideal factorisation of the divisor D by combining contributions from identical ideals.}
	oldfactn := IdealFactorisation(D);
	ideals := { F[1] : F in oldfactn };
	newfactn := [ Universe(oldfactn) | ];
	for I in ideals do
		mult := 0;
		for i in [#oldfactn..1 by -1] do
			if oldfactn[i][1] eq I then
				mult +:= oldfactn[i][2];
				Remove(~oldfactn,i);
			end if;
		end for;
		if mult ne 0 then
			Append(~newfactn, < I, mult >);
		end if;
	end for;
	D`ideal_factorisation := newfactn;
end intrinsic;

intrinsic ComputeReducedFactorisation(~D::DivSchElt)
{An ideal factorisation of the divisor D into radical ideals with multiplicities.}
	oldfactn := IdealFactorisation(D);
	newfactn := [ Universe(oldfactn) | ];
	for Im in oldfactn do
		I := Im[1];
		repeat	// find the radical component of highest mult
			Itemp := I;
			J := Radical(I);
			repeat
				Iprevious := Itemp;
				Itemp := ColonIdeal(Itemp,J);
			until Itemp eq Generic(Itemp);
			K := Radical(Iprevious);
				// K is highest mult radical comp of I
			mult,I := idealmult(I,K);
			Append(~newfactn, < K, mult*Im[2] >);
		until I eq Generic(I);
	end for;
	D`ideal_factorisation := newfactn;
	CombineIdealFactorisation(~D);
end intrinsic;

/* THINK
intrinsic EuclideanFactorisation(D::DivSchElt) -> SeqEnum
{The ideal factorisation of the divisor D after combining contributions from common primary components of all ideals, so that ideals which appear in the resulting factorisation are pairwise coprime (but not necessarily prime).}
	return false;
end intrinsic;
*/

// I, J are ideals in the same poly ring.
// return P = GCD(I,J) and multPinI, multPinJ and I:P^mult, J:P^mult.
// Can we just take the codim-1 part of I+J? -MJB
function idealgcd(I,J)
	P := Radical(ColonIdeal(I, Saturation(I,J)));
	multPinI, Inew := idealmult(I,P);
	multPinJ, Jnew := idealmult(J,P);
	return P, multPinI, multPinJ, Inew, Jnew;
end function;

intrinsic ComputePrimeFactorisation(~D::DivSchElt)
{A sequence containing the prime divisors that appear nontrivially in the divisor D.}
	oldfactn := IdealFactorisation(D);
	prime_ideals := [PowerStructure(RngMPol) | ];
	multiplicities := [ Rationals() | ];
	for Im in oldfactn do
		I := Im[1];
		m := Im[2];
		primes := RadicalDecomposition(I);
		for P in primes do
			mult := idealmult(I,P);
			indexP := Index(prime_ideals,P);
			if indexP eq 0 then
				Append(~prime_ideals, P);
				Append(~multiplicities, m*mult);
			else
				multiplicities[indexP] +:= m*mult;
			end if;
		end for;
	end for;
	// Remove any zero contributions
	for i in [#multiplicities..1 by -1] do
		if multiplicities[i] eq 0 then
			Remove(~multiplicities,i);
			Remove(~prime_ideals,i);
		end if;
	end for;
	D`ideal_factorisation := [ CartesianProduct(PowerStructure(RngMPol),Rationals()) |
		< prime_ideals[i], multiplicities[i] > :
				i in [1..#multiplicities] ];
end intrinsic;

intrinsic Support(D::DivSchElt) -> Sch
{The support of the divisor D as a subscheme of its associated variety.}
	if not assigned D`support then
		require IsEffective(D):
			"The divisor D must be effective";
		D`support := Scheme(Variety(D),IdealOfSupport(D));
	end if;
	return D`support;
end intrinsic;


//////////////////////////////////////////////////////////////////////
//			Arithmetic
// Note: if the variety X happens to be a toric variety, then it
// is convenient if we can add and subtract toric divisors to these divisors.
// THINK: maybe we should allow equality testing too - or even type
// change to toric divisors when that is possible.
//////////////////////////////////////////////////////////////////////

/* Example
P<x,y,z,t> := ProjectiveSpace(Rationals(),3);
X := Scheme(P, x*&+[P.i^3:i in [1..4]] - y*(x^2*y+y^2*z+z^2*t+t^2*x));
assert IsNonsingular(X);
L1 := Divisor(X,[x,y]);
L2 := Divisor(X,[x,z]);
H := Divisor(X,x);
C := H - L1 - L2;
assert not L1 eq L2;
D := 2*H - C;
E := H + L1 + L2;
assert D eq E;
*/

/* Example of toric and non-toric divisors.

P2<x,y,z> := ProjectiveSpace(Rationals(),2);
    // NB: not assigned: P2`divisor_group; P2`toric_divisor_group;
Dx := Divisor(P2,x);
Dx;	// Weil divisor Dx with coefficients: 1, 0, 0
    // P2`divisor_group; still not assigned, but
    // P2`toric_divisor_group; is assigned
Dy := Divisor(P2,Ideal([y]));
    // Now both groups are assigned.
Dy;	// Prime divisor 1 * ( y = 0 )
Dx + Dy;	// Divisor with ... 1 * ( y = 0 ) + 1 * ( x = 0 )
Dy - Dx;	// Divisor with ... 1 * ( y = 0 ) + -1 * ( x = 0 )

*/

intrinsic 'eq'(D1::DivSchElt, D2::DivSchElt)-> DivSchElt
{True iff the two divisors D1 and D2 are equal, that is, they have the same prime components with the same multiplicities.}
	X := Variety(D1);
	require Variety(D2) eq X:
		"Arguments must be defined on the same variety.";
        if assigned D1`ideal and assigned D2`ideal then
                return D1`ideal eq D2`ideal;
        end if;
	if IdealFactorisation(D1) eq IdealFactorisation(D2) then
		return true;	// that is just lucky.
	end if;
	// THINK: would it be worth in general sorting through
	// each factor of D1 to identify it in D2 and subtract.
	// Lots of equality testing and some colon ideals, but
	// at least no prime decomposition required.
	Primes1 := PrimeFactorisation(D1);
	Sort(~Primes1);
	D1`ideal_factorisation := Primes1;
	Primes2 := PrimeFactorisation(D2);
	Sort(~Primes2);
	D2`ideal_factorisation := Primes2;
	return Primes1 eq Primes2;
end intrinsic;

intrinsic '+'(D1::DivSchElt, D2::DivSchElt)-> DivSchElt
{The sum D1 + D2 of two divisors D1 and D2.}
	X := Variety(D1);
	require Variety(D2) eq X:
		"Arguments must be defined on the same variety.";
	D := New(DivSchElt);
	D`divisor_group := DivisorGroup(X);
	D`ideal_factorisation := IdealFactorisation(D1) cat
		IdealFactorisation(D2);
	if (assigned D1`is_cartier and D1`is_cartier) and 
		(assigned D2`is_cartier and D2`is_cartier) then
	  D`is_cartier;
	end if;
	return D;
end intrinsic;

intrinsic '-'(D::DivSchElt)-> DivSchElt
{The negative -D of the divisors D.}
	return (-1)*D;
end intrinsic;

intrinsic '-'(D1::DivSchElt, D2::DivSchElt)-> DivSchElt
{The difference D1 - D2 of two divisors D1 and D2.}
	X := Variety(D1);
	require Variety(D2) eq X:
		"Arguments must be defined on the same variety.";
	D := New(DivSchElt);
	D`divisor_group := DivisorGroup(X);
	D`ideal_factorisation := IdealFactorisation(D1) cat
		[ <F[1],-F[2]> : F in IdealFactorisation(D2)];
	if (assigned D1`is_cartier and D1`is_cartier) and 
		(assigned D2`is_cartier and D2`is_cartier) then
	  D`is_cartier;
	end if;
	boo := (assigned D1`ideal) or (assigned D1`sign_split and
			not IsProper(D1`sign_split[2]));
	if boo then
	  I1 := (assigned D1`sign_split) select D1`sign_split[1]
			else D1`ideal;
	  boo := (assigned D2`ideal) or (assigned D2`sign_split and
			not IsProper(D2`sign_split[2]));
	  if boo then
	    I2 := (assigned D2`sign_split) select D2`sign_split[1]
			else D2`ideal;
	    D`sign_split := [I1,I2];
	  end if;
	end if;
	return D;
end intrinsic;

intrinsic '*'(n::RngIntElt, D::DivSchElt)-> DivSchElt
{The product n*D of the divisors D and the rational number n.}
	if n eq 1 then return D; end if;
	E := New(DivSchElt);
	E`divisor_group := DivisorGroup(Variety(D));
	E`ideal_factorisation :=
	    [ <Im[1],Rationals()!Im[2]*n> : Im in IdealFactorisation(D) ];
	if assigned D`is_cartier then
	  if D`is_cartier or (n eq -1) then
	    E`is_cartier := D`is_cartier;
	  end if;
	end if;
	if assigned D`sign_split and (n eq -1) then
	  E`sign_split := Reverse(D`sign_split);
	end if;	  
	return E;
end intrinsic;

intrinsic '*'(n::FldRatElt, D::DivSchElt)-> DivSchElt
{"} // "
	if IsIntegral(n) then return (Integers()!n)*D; end if;
	E := New(DivSchElt);
	E`divisor_group := DivisorGroup(Variety(D));
	E`ideal_factorisation :=
		[ <Im[1],Im[2]*n> : Im in IdealFactorisation(D) ];
	return E;
end intrinsic;

intrinsic '+'(D1::DivSchElt, D2::DivTorElt)-> DivSchElt
{The sum D1 + D2 of two divisors D1 and D2.}
	X := Variety(D1);
	require ToricVariety(Parent(D2)) eq X:
		"Arguments must be defined on the same variety.";
	bool, indx := IsQCartier(D2);
	if bool then
		m := DefiningMonomial(indx*D2);
		if Type(m) eq RngMPolElt then
		    if Degree(m) eq 0 then	// care: m = 1 would give a toric div
			return D1;
		    else
			return (1/indx)*(indx*D1
				+ Divisor(X,Ideal([m]):UseCodimensionOnePart:=true ));
		    end if;
		else	// handle the case where m is a Laurent monomial mnum/mden.
		    mnum := Numerator(m);
		    mden := Denominator(m);
		    return (1/indx)*(indx*D1
				+ Divisor(X,Ideal([mnum]) : UseCodimensionOnePart:=true )
		    	- Divisor(X,Ideal([mden]) : UseCodimensionOnePart:=true ));
		end if;
	else
		m := DefiningMonomial(D2);
		if Type(m) eq RngMPolElt then
		    if Degree(m) eq 0 then	// care: m = 1 would give a toric div
			return D1;
		    else
			return D1 + Divisor(X,Ideal([m]):UseCodimensionOnePart:=true );
		    end if;
		else	// handle the case where m is a Laurent monomial mnum/mden.
		    mnum := Numerator(m);
		    mden := Denominator(m);
		    return D1 + Divisor(X,Ideal([mnum]) : UseCodimensionOnePart:=true )
		    	- Divisor(X,Ideal([mden]) : UseCodimensionOnePart:=true );
		end if;
	end if;
	// NB. Constructors for toric divisors do not include the case
	// where the second arg is an ideal, so we use that to ensure
	// that we get a DivSchElt.
	// NB. We can assert the codim 1 part, since we know m is a monomial
	// and this intrinsic is only called when the underlying X is a
	// toric variety. We need to do this in case m = 1/x, in which case
	// the numerator should contribute the zero divisor.
end intrinsic;

intrinsic '+'(D1::DivTorElt, D2::DivSchElt)-> DivSchElt
{The sum D1 + D2 of two divisors D1 and D2.}
	return D2 + D1;
end intrinsic;

intrinsic '-'(D1::DivSchElt, D2::DivTorElt)-> DivSchElt
{The difference D1 - D2 of two divisors D1 and D2.}
	return D1 + (-1)*D2;
end intrinsic;

intrinsic '-'(D1::DivTorElt, D2::DivSchElt)-> DivSchElt
{The difference D1 - D2 of two divisors D1 and D2.}
	return D2 + (-1)*D1;
end intrinsic;

intrinsic IntegralMultiple(D::DivSchElt) -> DivSchElt,RngIntElt
{An integral divisor E and an integer N for which N*D = E, where the given divisor D may have rational coefficients.}
	// No work done here - just read coefficients brainlessly.
	N := LCM([ Integers() | Denominator(Im[2]) :
			Im in IdealFactorisation(D) ] );
	return N*D,N;
end intrinsic;

// added mch - 11/12 - computes the intersection number of 2 integral,
//  effective divisors D1, D2 on surface X repd by ideals I1,I2 - faster
//  than going through conversion to sheaves!
function int_number(I1,I2,X)
    IX := Ideal(X);
    I12 := IX+(I1*I2); //(non-sat)ideal of D1+D2
    // NB. straight multiplication of I1 and I2 works here as one
    //  at least should be Cartier!
    H1 := HilbertPolynomial(I1);
    H2 := HilbertPolynomial(I2); //should really check if I1 = I2 to save time here
    H12 := HilbertPolynomial(I12);
    return Integers()!Coefficient(H1+H2-H12,0);
end function;

intrinsic IntersectionNumber(D1::DivSchElt, D2::DivSchElt)-> FldRatElt
{The intersection number D1*D2 of two divisors D1 and D2.}
	X := Variety(D1);
	require Variety(D2) eq X:
		"Arguments must be defined on the same variety.";
	require Dimension(X) eq 2: "Variety on which the divisors " *
		"lie must be 2 dimensional";
	/* mch - 11/12 - really don't think it does help speed!
	ComputeReducedFactorisation(~D1);	// THINK: does this
	ComputeReducedFactorisation(~D2);	// help speed?
	*/
	// mch - 08/14 - added the clause for existence of D`ideal or
	// D`sign_split - danger in using a factorisation is that
        // even if D1, say, is known to be Cartier, individual
	// decomposed factors may not be, so the individual 
	// computations using int_number(I,J) may be wrong. This
        // may still apply with using sign_split x sign_split
        // but it should be ok with sign_split x ideal and there
        // is no problem with ideal x ideal.
	if IsZeroDivisor(D1) or IsZeroDivisor(D2) then
		return Rationals() ! 0;
	elif (assigned D1`sign_split or assigned D1`ideal) and
		(assigned D2`sign_split or assigned D2`ideal) then
	  if (assigned D1`ideal) and (assigned D2`ideal) then
		return int_number(D1`ideal,D2`ideal,X);
	  elif assigned D1`ideal then
		return int_number(D1`ideal,D2`sign_split[1],X)
			- int_number(D1`ideal,D2`sign_split[2],X);
	  elif assigned D2`ideal then
		return int_number(D2`ideal,D1`sign_split[1],X)
			- int_number(D2`ideal,D1`sign_split[2],X);
	  else
		return  int_number(D1`sign_split[1],D2`sign_split[1],X) +
		 	int_number(D1`sign_split[2],D2`sign_split[2],X) -
		 	int_number(D1`sign_split[1],D2`sign_split[2],X) -
		 	int_number(D1`sign_split[2],D2`sign_split[1],X);
	  end if;
	elif IsEffective(D1) and IsEffective(D2) then
		// Have to handle non-integral divisors here, because
		// they're fractional info is lost in the corr sheaf.
		// Also, it's *much* quicker to pull out any factors
		// you can before computing the sheaf.
		// changed mch - 11/12 - to use int_number
		return &+[ Im[2]*Jm[2] * int_number(Im[1],Jm[1],X) :
			Im in IdealFactorisation(D1), Jm in IdealFactorisation(D2) ];
	else
		A1,B1 := SignDecomposition(D1);
		A2,B2 := SignDecomposition(D2);
		return IntersectionNumber(A1,A2)
			- IntersectionNumber(A1,B2)
			- IntersectionNumber(A2,B1)
			+ IntersectionNumber(B1,B2);
	end if;
end intrinsic;

intrinsic SelfIntersection(D::DivSchElt)-> FldRatElt
{The self intersection D^2 of the divisor D.}
	if not assigned D`selfintersection then
		require Dimension(Variety(D)) eq 2: "Variety on " *
		    "which the divisors lie must be 2 dimensional";
		D`selfintersection := IntersectionNumber(D,D);
	end if;
	return D`selfintersection;
end intrinsic;

intrinsic IntersectionMatrix(Q::SeqEnum)-> Mtrx
{The symmetric intersection matrix of the divisors in the sequence Q of divisor; the i,j entry of the matrix is the intersection number Q[i]*Q[j]}
	return SymmetricMatrix([ IntersectionNumber(Q[i], Q[j])
	   : i in [1..j], j in [1..#Q] ]);
end intrinsic;

intrinsic Degree(D::DivSchElt)-> FldRatElt
{The degree of the divisor D with respect to the hyperplane section.}
	require Dimension(Variety(D)) eq 2: "Variety on which " *
		"the divisors lie must be 2 dimensional";
	X := Variety(D);
	// Find a linear hyperplane section that does not vanish on X.
	P := Ambient(X);
	i := 0;
	repeat
		i +:= 1;
	until not X subset Scheme(P,P.i);
	H := Divisor(X,P.i);
	return IntersectionNumber(D,H);
end intrinsic;

intrinsic Degree(D::DivSchElt,H::DivSchElt)-> FldRatElt
{The degree of the divisor D with respect to the divisor H, i.e. the intersection number D*H.}
	X := Variety(D);
	require Variety(H) eq X:
		"Arguments must be defined on the same variety.";
	require Dimension(Variety(D)) eq 2: "Variety on which " *
		"the divisors lie must be 2 dimensional";
	return IntersectionNumber(D,H);
end intrinsic;

intrinsic IsNef(D::DivSchElt) -> BoolElt
{True iff the effective divisor D has nonnegative intersection with every curve on the underlying surface.}
	if not assigned D`is_nef then
		// THINK MATHERROR: temporary condition?
		require IsEffective(D):
			"The divisor D must be effective.";
		X := Variety(D);
		return &and [
			IntersectionNumber(D,Divisor(X,I[1])) ge 0 :
				I in PrimeFactorisation(D) ];
	end if;
	return D`is_nef;
end intrinsic;

intrinsic IsNefAndBig(D::DivSchElt) -> BoolElt
{True iff the effective divisor D has nonnegative intersection with every curve on the underlying surface and D^2 > 0.}
	require IsEffective(D): "The divisor D must be effective.";
	return IsNef(D) and SelfIntersection(D) gt 0;
end intrinsic;

/* removed from export for the moment - mch 11/12
intrinsic IsStrictlyNef(D::DivSchElt) -> BoolElt
{True iff the effective divisor D has strictly positive intersection with every curve on the underlying surface.}
	if not assigned D`is_strictly_nef then
		if IsEffective(D) then
			X := Variety(D);
			return &and [
			IntersectionNumber(D,Divisor(X,I[1])) gt 0 :
				I in PrimeFactorisation(D) ];
		else
			bool,E := IsLinearSystemNonEmpty(D);
			if not bool then
				// THINK MATHERROR: don't know yet
				D`is_strictly_nef := false;
			else
				isstrictlynef := IsStrictlyNef(E);
				D`is_strictly_nef := isstrictlynef;
			end if;
		end if;
	end if;
	return D`is_strictly_nef;
end intrinsic;

intrinsic IsAmple(D::DivSchElt) -> BoolElt
{True iff the effective divisor D has strictly positive intersection with every curve on the underlying surface and D^2 > 0.}
	require Dimension(Variety(D)) eq 2: "The underlying variety "
		* "must be 2 dimensional";
	if not assigned D`is_ample then
		if IsEffective(D) then
			D`is_ample := IsStrictlyNef(D) and
				Selfintersection(D) gt 0;
		else
			if Selfintersection(D) le 0 then
				D`is_ample := false;
			else
				bool,E := IsLinearSystemNonEmpty(D);
				if not bool then
				// THINK MATHERROR: don't know yet
					D`is_ample := false;
				else
					isample := IsStrictlyNef(E);
					D`is_ample := isample;
				end if;
			end if;
		end if;
	end if;
	return D`is_ample;
end intrinsic;
*/

// added mch - 11/13 - function to test if the effective divisor
// defined as a closed subscheme on normal, ordinary projective scheme X 
// by the ideal ID is locally principal (Cartier) - that is, if it
// is locally defined by a single equation on X. Used by the intrinsic
// that follows. 
function IsLocallyPrincipal(X,ID)

   // Use criteria that ID is locally princ. iff 
   //  Sheaf(ID)tensor(Sheaf(ID)^-1)) = OX where Sheaf(ID)
   //  is the ideal sheaf of ID and Sheaf(ID)^-1
   //  is Hom_OX(Sheaf(ID),OX) which is represented
   //  as a module by the fractional ideal (ID/IX)^-1
   //  wrt the ring R/IX.

    R := CoordinateRing(Ambient(X));
    Saturate(~X);
    IX := Ideal(X);
    if not (ID subset IX) then
	ID := Saturation(ID);
    end if;

    hD := HilbertSeries(ID);
    hX := HilbertSeries(IX);
    if Degree(Denominator(hX)) ne Degree(Denominator(hD))+1 then
	return false; // ID doesn't define a codimension 1 subscheme
    end if;
    hXD := hX-hD;
    r := Valuation(Numerator(hXD));

    // find an Fr of degree r in ID and not in IX
    BX := GroebnerBasis(IX); 
    Reverse(~BX); 
    if IsEmpty(BX) then
      BX := [Generic(IX)| 0];
    end if;
    BD := GroebnerBasis(ID);
    Reverse(~BD);
      // assumed here that R has a degree ordering
    i := 1; while LeadingTotalDegree(BD[i]) lt r do i +:=1; end while;
    if LeadingTotalDegree(BX[#BX]) ge r then
      j := 1; while LeadingTotalDegree(BX[j]) lt r do j +:=1; end while;
      while (j le #BX) and (BD[i] eq BX[j]) do 
	j +:=1; i +:=1;
      end while;
    end if;
    Fr := BD[i];

    IDm1 := ColonIdeal(IX+ideal<R|Fr>,ID);
    IDxIDm1 := ideal<R|[a*b : a in MinimalBasis(ID), b in MinimalBasis(IDm1)]>;
    boo := (Fr in Saturation(IDxIDm1+IX));
    return boo;

end function;

// added mch -11/13
intrinsic IsCartier(D::DivSchElt) -> BoolElt
{ True iff D is a Cartier divisor (i.e. locally principal). D must be an integral divisor on
  an ordinary projective variety here. }

    if not assigned D`is_cartier then
      X := Variety(D);
      require IsOrdinaryProjective(X): "D must be a divisor on an ordinary projective scheme";
      require is_easy_integral(D) or IsIntegral(D) : "D must be an integral divisor";
      if is_easy_effective(D) then
	D1 := D;
      else // avoid prime decomposition for full effectiveness test
	D1 := EffectiveHypersurfaceTwist(D);	
      end if;
      D`is_cartier := IsLocallyPrincipal(X,Ideal(D1));
    end if;
    return D`is_cartier; 

end intrinsic;

//////////////////////////////////////////////////////////////////////
//			Riemann-Roch
//////////////////////////////////////////////////////////////////////

/*
// THINK: MCH: how does this compare with code for arithmetic genus?
intrinsic Irregularity(X::Sch) -> RngIntElt
{The irregularity h^1(X,O_X) of (the projective closure of) the surface X.}
	require Dimension(X) eq 2 and IsReduced(X):
	    "The argument scheme X must be a 2 dimensional variety";
	Y := ProjectiveClosure(X);
	return CohomologyDimension(StructureSheaf(Y),1,0);
end intrinsic;
*/

intrinsic Sheaf(D::DivSchElt) -> ShfCoh
{The sheaf O_X(D) corresponding to the (Cartier) divisor D on a variety X. (The integral round down of D is used if D is not itself integral.)}
// THINK: why do we need D to be Cartier?
	if not assigned D`sheaf then
		// clause added mch - 11/12 - avoid prime decomposition!
		if is_easy_integral(D) then
		  if is_easy_effective(D) then
			D`sheaf := DivisorToSheaf(Variety(D),Ideal(D));
		  else
			A,B := SignDecomposition(D);
			IA := Ideal(A); IB := Ideal(B);
			if IA eq IB then
			  D`sheaf := StructureSheaf(Variety(D));
			else
			  D`sheaf := IneffectiveDivisorToSheaf(Variety(D),IA,IB);
			end if;
		  end if;
		  return D`sheaf;
		else
		end if;
		if IsIntegral(D) then
			E := D;
		else
			E := RoundDownDivisor(D);
		end if;
		if IsZeroDivisor(E) then
			D`sheaf := StructureSheaf(Variety(D));
		elif IsEffective(E) then
			D`sheaf :=
				DivisorToSheaf(Variety(D),Ideal(E));
		else
			A,B := SignDecomposition(E);
			D`sheaf := IneffectiveDivisorToSheaf(Variety(D),Ideal(A),Ideal(B));
		end if;
	end if;
	return D`sheaf;
end intrinsic;

intrinsic RiemannRochBasis(D::DivSchElt) -> SeqEnum
{A sequence of rational functions on the ambient space of the variety X of the divisor D (or its round down, if not integral) that form a basis of the Riemann-Roch space of D when restricted to X.}
	if IsIntegral(D) then
		E := D;
	else
		E := RoundDownDivisor(D);
	end if;
	A,B := SignDecomposition(E);
	// mch -11/13 - need to handle A or B = 0 divisor correctly!
	X := Variety(D);
	R := CoordinateRing(Ambient(X));
	Azer := #(A`ideal_factorisation) eq 0;
	Bzer := #(B`ideal_factorisation) eq 0;
	if Azer and Bzer then //D=0 obviously
	  D`sheaf := StructureSheaf(X);
	  numbasis := [R!1];
	  denom := R!1;
	elif Azer then //D=-B
	  // compute sheaf?? (the sheaf module is the saturation of ideal of B)
	  // don't both for now.
	  numbasis := [R|];
	  denom := R!1;
	else 
	  IB := Bzer select ideal<R|1> else Ideal(B);
	  numbasis,denom,sheaf := IneffectiveRiemannRochBasis(
					Variety(D),Ideal(A),IB);
	  D`sheaf := sheaf;
	end if;
	D`rr_numerators := numbasis;
	D`rr_denominator := denom;
	return [FunctionField(Ambient(X))|
		f/denom : f in numbasis ];
end intrinsic;

forward compute_rr_coords;

intrinsic RiemannRochCoordinates(f::.,D::DivSchElt) -> BoolElt,SeqEnum
{True iff the rational function f lies in the Riemann-Roch space of the divisor D, in which case also return the coordinates of f with respect to the fixed basis of that RR space.}
	X := Variety(D);
	FF := FunctionField(Ambient(X));
	iscoer,ff := IsCoercible(FF,f);
	if iscoer then
		if not assigned D`rr_numerators
		    or not assigned D`rr_denominator then
		    	_ := RiemannRochSpace(D);  // forces their calculation
		end if;
		bool,coords := compute_rr_coords(X,ff,D);
	else
		require false: "Argument f must be coercible into " *
			"the function field of the ambient space of" *
			" the variety of the divisor D";
	end if;
	if bool then
		// The seq coords is of (const) elts of the coord ring, so...
		ChangeUniverse(~coords,BaseField(X));
		return bool,coords;
	else
		return bool,_;
	end if;
end intrinsic;

/* Example
P<x,y,z,t> := ProjectiveSpace(Rationals(),3);
X := Scheme(P, x*&+[P.i^3:i in [1..4]] - y*(x^2*y+y^2*z+z^2*t+t^2*x));
D := Divisor(X,y);
FF<a,b,c> := FunctionField(Ambient(X));
V,phi := RiemannRochSpace(D);
h := (2*a + 3*b + 5)/b;
h @@ phi;			// (2 3 0 5)
RiemannRochCoordinates(h,D);	// true [ 2, 3, 0, 5 ]
assert h in D;	// THINK: do we like this shortcut?
*/


// X the variety (defined over field k) we want to work on
// h a rational function on the ambient of X
// fs a seq of numerators of rat funs; g is their common denom.
// return true if h in k-span of fs/g (modulo the equns of X),
// in which case also return the vector of coords of h in fs/g.
// Plan: h = sum a_i f_i/g; multiply up denoms, work mod ideal of X.
function map_back(X,h)
	P := Ambient(X);
	FF := FunctionField(P);
	// Find which affine patch rational functions are defined on.
	patch := 1;
	repeat
		A := AffinePatch(P,patch);
	until CoordinateRing(A) cmpeq RingOfIntegers(FF);
	pc := ProjectiveClosureMap(AffinePatch(P,patch));
	return pc(Numerator(h)) / pc(Denominator(h));
end function;

function compute_coords(X,h,fs,g)
	R := CoordinateRing(Ambient(X));
	// get everything into the coords of X
	hh := map_back(X,h);
	a := Numerator(hh);
	b := Denominator(hh);
	LHS := a*g;
	basis := [R| fi*b : fi in fs ] cat DefiningEquations(X);
	J := IdealWithFixedBasis(basis);
	if LHS in J then
		coords := Coordinates(J,LHS);
		return true,coords[1..#fs];
	else
		return false,_;
	end if;
end function;

// A version of the same but with the divisor as argument.
function compute_rr_coords(X,h,D)
	is_function_in_rr_space,coords := compute_coords(X,h,
		D`rr_numerators,D`rr_denominator);
	if is_function_in_rr_space then
		return is_function_in_rr_space,coords;
	else
		return is_function_in_rr_space,_;
	end if;
end function;

function rr_coords(X,h,D)
	is_function_in_rr_space,coords := compute_coords(X,h,
		D`rr_numerators,D`rr_denominator);
	assert is_function_in_rr_space;
	return coords;
end function;

intrinsic RiemannRochSpace(D::DivSchElt) -> ModTupFld, Map
{A vector space and the isomorphism from this space to the Riemann-Roch space of (ambient) function field elements for the divisor D.}
	X := Variety(D);
	k := BaseField(X);
	FFX := FunctionField(Ambient(X));
	basis := RiemannRochBasis(D);
	V := VectorSpace(k, #basis);
	phi := map< V -> FunctionField(Ambient(Variety(D))) |
		v :-> &+[FFX|v[i]*basis[i]:i in [1..Dimension(V)]],
		f :-> rr_coords(Variety(D),f,D) >;
	D`rr_space := V;
	D`rr_space_map := phi;
	return V,phi;
end intrinsic;

intrinsic IsLinearSystemNonEmpty(D::DivSchElt) -> BoolElt,DivSchElt
{True iff there is at least one effective divisor linearly equivalent to the divisor D, in which case also return such an effective divisor as a second value.}
	
	if is_easy_effective(D) then	// get rid of trivial case - easy test
		return true, D;
	end if;
	// added mch - 11/12 - think it is more efficient. the method
	// that follows this gives a divisor not immediately in effective form
	// that has to be factored for effectiveness to be evident.
	if is_easy_effective(D) then	// get rid of trivial case - easy test
		return true, D;
	end if;
	if is_easy_integral(D) then
	  SD := Sheaf(D);
	  h0D := DimensionOfGlobalSections(SD); //this is now fast!
	  if h0D eq 0 then
		return false,_;
	  else
		return true, SheafToDivisor(SD);
	  end if;
	end if;
	if IsEffective(D) then	// get rid of trivial case
		return true, D;
	end if;
	// THINK: should run RR till we find the first element
	// in its space (or until it terminates with nothing)
	// and use that element.
	// For now, just use the whole RR.
	RR := RiemannRochBasis(D);
	if #RR eq 0 then
		return false,_;
	else
		return true, D + Divisor(Variety(D),RR[1]);
	end if;
end intrinsic;

/* Example
P<x,y,z,t> := ProjectiveSpace(Rationals(),3);
X := Scheme(P, x*&+[P.i^3:i in [1..4]] - y*(x^2*y+y^2*z+z^2*t+t^2*x));
H := Divisor(X,y);
L := Divisor(X,[x,y]);
V,phi := RiemannRochSpace(H-2*L);
phi(V!0);		// 0
Parent($1);	// Function Field of Projective Space of dimension 3
		// Variables: x, y, z, t
assert not IsLinearSystemNonEmpty(H-2*L);
*/

intrinsic IsPrincipal(D::DivSchElt) -> Sch, FldFunFracSchElt
{True iff the divisor D is principal, in which case a rational function f for which D = div(f) is returned as a second value.}
	if not assigned D`is_principal then
		if IsIntegral(D) then
			X := Variety(D);
			B := RiemannRochBasis(D);
			// THINK: better way to state cond below?
			if #B eq 1 and D eq -Divisor(X,B[1]) then
				D`is_principal := true;
				D`principal_function := 1/B[1];
			else
				D`is_principal := false;
			end if;
		else
			D`is_principal := false;
		end if;
	end if;
	if D`is_principal then
		return D`is_principal,D`principal_function;
	else
		return D`is_principal,_;
	end if;
end intrinsic;

intrinsic IsLinearlyEquivalent(D::DivSchElt,E::DivSchElt)
	-> Sch, FldFunFracSchElt
{True iff the divisors D and E are linearly equivalent (i.e. iff D - E is principal), in which case a rational function f for which D = E + div(f) is returned as a second value.}
	bool,f := IsPrincipal(D-E);
	if bool then
		return bool,f;
	else
		return bool,_;
	end if;
end intrinsic;

/* Example
P<x,y,z,t> := ProjectiveSpace(Rationals(),3);
X := Scheme(P, x*&+[P.i^3:i in [1..4]] - y*(x^2*y+y^2*z+z^2*t+t^2*x));
H1 := Divisor(X,y);
H2 := Divisor(X,t);
L := Divisor(X,[x,y]);
D1 := H1 - L;
D2 := H2 - L;
bool,fun := IsPrincipal(D1-D2);
assert bool;
assert Divisor(X,fun) - (D1-D2) eq ZeroDivisor(X);
bool2,fun2 := IsLinearlyEquivalent(D1,D2);
assert D1 eq D2 + Divisor(X,fun2);
*/

intrinsic EffectiveHypersurfaceTwist(D::DivSchElt) -> DivSchElt, RngMPolElt
{ D should be integral and defined on an ordinary projective scheme.
  Returns an effective divisor D1 equivalent to D+rH, where r>= 0 and H is the hyperplane
  divisor, and F, the homogeneous polynomial of degree r such that D1=D+(F).
  Just returns D,1 if D has an effective presentation.
  Avoids computing a relatively prime signed decomposition. }

    X := Variety(D);
    require IsOrdinaryProjective(X): 
	"D must be the divisor on an ordinary projective scheme";
    if not is_easy_integral(D) then
	require IsIntegral(D): "D must be an integral divisor";
    end if;
    if is_easy_effective(D) then 
	return D,CoordinateRing(Ambient(X))!1;
    end if;
    A,B := SignDecomposition(D);
    IB := Ideal(B);
    // r will be the smallest degree s.t. there exists non-zero F in IB
    // with F homogeneous of degree r. Then replace -B with rH-B which
    // divisor class contains the effective divisor with ideal (IB:F)
    Saturate(~X);
    IX := Ideal(X);
    IB1 := IB+IX; //guarantee that IB contains IX
    r := Valuation(Numerator(HilbertSeries(IX)-HilbertSeries(IB1)));
    assert r gt 0;
    R := Generic(IB);
    B := Basis(IB);
    // All generators of any sensible basis of IB should be homogeneous
    // as the ideal IB is homogeneous. Just in case, replace
    // any generator by its homogeneous parts
    if not &and[IsHomogeneous(b) : b in B] then
      B := &cat[IsHomogeneous(b) select [b] else 
	[(#T eq 0) select R!0 else Polynomial([LeadingCoefficient(t) : t in T],
	  [LeadingMonomial(t) : t in T]) where T is 
	   [t : t in Terms(b) | LeadingTotalDegree(t) eq r] : r in [m..M]]
	  where m is Min(seq) where M is Max(seq) where seq is
		[LeadingTotalDegree(t) : t in Terms(b)] : b in B];
      B := [b : b in B | not IsZero(b)];
    end if;
    Br := [b : b in B | (not IsZero(b)) and (LeadingTotalDegree(b) eq r)];
    F := R!0;
    for b in Br do
	if b notin IX then F := b; break; end if;
    end for;
    assert not IsZero(F);
    J := ColonIdeal(IX+ideal<R|F>,ideal<R|MinimalBasis(IB1)>);
    Inew := EquidimensionalPart((J*Ideal(A))+IX);
    return Divisor(X,Inew : CheckSaturated := true, CheckDimension := true),r;

end intrinsic;
//////////////////////////////////////////////////////////////////////
//	Base points, mobility and Zariski decomposition
//////////////////////////////////////////////////////////////////////

intrinsic BaseLocus(D::DivSchElt) -> Sch
{The base locus of the linear system |D|, that is, the reduced intersection of all effective divisors linearly equivalent to D.  (Note that linear equivalence is carried out only on the integral round down; the fractional part \{D\} of D can be recovered separately.)}
	if not assigned D`base_locus then
		X := Variety(D);
		E := RoundDownDivisor(D);
		divisors := [ E + Divisor(X,f) :
			f in RiemannRochBasis(E) ];
		D`base_locus := &meet [ Support(E) : E in divisors ];
	end if;
	return D`base_locus;
end intrinsic;

// THINK: need to be more careful about whether {D} is in the
// base locus or whether we are working with Q-divisors and
// Q-equivalence.

intrinsic IsBasePointFree(D::DivSchElt) -> BoolElt
{True iff the base locus of the linear system |D| is empty.}
	return IsEmpty(BaseLocus(D));
end intrinsic;

intrinsic IsMobile(D::DivSchElt) -> BoolElt
{True iff the base locus of the linear system |D| contains no components in codimension 1.}
	return Dimension(BaseLocus(D)) lt Dimension(Variety(D)) - 1;
end intrinsic;

/*
intrinsic FixedDivisor(D::DivSchElt) -> BoolElt,Sch
{The fixed divisor F support on the codimension 1 base locus of the linear system |D|. This has the property that D - F is mobile.}
	// THINK:
	return false;
end intrinsic;

intrinsic MobileDivisor(D::DivSchElt) -> BoolElt,Sch
{The mobile divisor M support on the codimension 1 base locus of the linear system |D|. Thus D = M + F, where F is a fixed divisor, and the Riemann-Roch space of D is that of M.}
	// THINK:
	return false;
end intrinsic;
*/

intrinsic NegativePrimeDivisors(D::DivSchElt) -> SeqEnum
{A sequence of the prime divisors on the underlying variety of the effective divisor D that have negative intersection with D.}
	if not assigned D`negative_components then
		require IsEffective(D):
			"The divisor D must be effective.";
		primes := [ Divisor(Variety(D),I[1]) :
			I in PrimeFactorisation(D) ];
		return [ E : E in primes |
			IntersectionNumber(D,E) lt 0 ];
	end if;
	return D`negative_components;
end intrinsic;

intrinsic ZariskiDecomposition(D::DivSchElt : number_of_steps:=5)
	-> DivSchElt,DivSchElt
{The two divisors P, N of the Zariski decomposition D = P + N of the divisor D (on a surface) into nef Q-divisor P and Q-divisor N which has negative definite support.}
	X := Variety(D);
	require Dimension(X) eq 2:
		"Underlying scheme of divisor D must be a surface";
	P := D;
	N := ZeroDivisor(Variety(D));
	// THINK: wasteful programming - we recompute intersection
	// numbers a lot - all possible C could be seen at first step
	// as the prime (or eucl) components of D.

	count := 0;
	while count lt number_of_steps and not IsNef(P) do
		count +:= 1;
		CC := NegativePrimeDivisors(P);	// a neg def config'n
		intform := SymmetricMatrix(
			[ IntersectionNumber(CC[i],CC[j]) :
				i in [j..#CC], j in [1..#CC] ]);
		targ := Matrix(#CC,[IntersectionNumber(P,C):C in CC]);
		coeffs := Eltseq(Solution(intform,targ));
		correction := &+[ coeffs[i] * CC[i] : i in [1..#CC] ];
		P -:= correction;
		CombineIdealFactorisation(~P);
		N +:= correction;
	end while;
	return P,N;
end intrinsic;

/* Example
P<x,y,z,t> := ProjectiveSpace(Rationals(),3);
X := Scheme(P, x*&+[P.i^3:i in [1..4]] - y*(x^2*y+y^2*z+z^2*t+t^2*x));
assert IsNonsingular(X);
L1 := Divisor(X,[x,y]);
assert not IsNef(L1) and SelfIntersection(L1) eq -2;
H := Divisor(X,x);
D := H + L1;
assert IntersectionNumber(D,L1) eq -1;
assert IntersectionNumber(D,H) eq 5;
P,N := ZariskiDecomposition(D);
assert IsNef(P) and IsEffective(P) and IsEffective(N);
assert IsIrreducible(Support(N)) and SelfIntersection(N) eq -1/2;
// Print N,P to see their fractional coefficients.
L2 := Divisor(X,[x,z]);
assert IsNef(H+L1+L2);
E := H+3*L1+2*L2;
IntersectionNumber(E,L1);	// -3
IntersectionNumber(E,L2);	// 0
C := H - L1 - L2;
IntersectionNumber(E,C);	// 12
ZariskiDecomposition(H+2*L1+2*L2);	// an integral example
ZariskiDecomposition(H+3*L1+2*L2);	// a very fractional example:
	// Could tidy this up a bit with CombineIdealFactorisation.
// Divisor with prime factorisation
//   65/32 * ( x = y = 0 )
// + 33/16 * ( x = z = 0 )
// + 1 * ( y^2 + z*t = x = 0 )
//Divisor with prime factorisation
//   3/2 * ( x = y = 0 )
// + 3/4 * ( x = z = 0 )
// + 3/8 * ( x = y = 0 )
// + 3/16 * ( x = z = 0 )
// + 3/32 * ( x = y = 0 )
ZariskiDecomposition(2*L1+L2);		// another fractional one

assert IsNef(2*L1+2*L2+C);
assert E eq C + 4*L1 + 3*L2;
assert IsZeroDivisor(E - (C + 4*L1 + 3*L2));
*/


//////////////////////////////////////////////////////////////////////
//		Pullback and pushforward of divisors
//////////////////////////////////////////////////////////////////////

/* Pullback doesn't deal with components of the base scheme of the map
   and Pushforward might need a little work. Won't export now - mch -11/12

intrinsic Pullback(f::MapSch,D::DivSchElt) -> DivSchElt
{The pullback of the divisor D (on the codomain of f) by the scheme map f. Note that this only pulls back the defining ideal of D and uses the pure codimension 1 part to construct a preimage divisor - if D is not Cartier, then this does not give the right divisorial pullback.}
	require Variety(D) eq Codomain(f): "The divisor D is not defined " *
		"on the codomain of the scheme map f";
	A,B := SignDecomposition(D);
	preimIA := [ b @@ f : b in Basis(Ideal(A)) ];
	preimIB := [ b @@ f : b in Basis(Ideal(B)) ];
	// The only (other) risk with pullbacks is that the image of f
	// lies inside a component of D. The divisor code will throw an
	// error in this case, since the corresponding ideal will not
	// pullback to something of codim 1.
	return Divisor(Domain(f),Ideal(preimIA) : UseCodimensionOnePart:=true )
		- Divisor(Domain(f),Ideal(preimIB) : UseCodimensionOnePart:=true );
end intrinsic;

// THINK: to extend this intrinsic to generically finite scheme maps, we
// would need to multiply images of divisor components by the degree of the
// field extension at their generic points.
intrinsic Pushforward(f::MapSch,D::DivSchElt : CheckBirational:=true)
	-> DivSchElt
{The pushforward of the divisor D (on the domain of f) by the birational scheme map f.}
	require IsInvertible(f):
		"Pushforward is only implemented for birational maps";
	require Variety(D) eq Domain(f): "The divisor D is not defined " *
		"on the domain of the scheme map f";
	A,B := SignDecomposition(D);
	imIA := [ b @@ Inverse(f) : b in Basis(Ideal(A)) ];
	imIB := [ b @@ Inverse(f) : b in Basis(Ideal(B)) ];
	// The only (other) risk with pullbacks is that the image of f
	// lies inside a component of D. The divisor code will throw an
	// error in this case, since the corresponding ideal will not
	// pullback to something of codim 1.
	return Divisor(Codomain(f),Ideal(imIA) : UseCodimensionOnePart:=true )
		- Divisor(Codomain(f),Ideal(imIB) : UseCodimensionOnePart:=true );
end intrinsic;
*/
