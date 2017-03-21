freeze;
/////////////////////////////////////////////////////////
//			Log Canonical Threshold of a plane curve
/////////////////////////////////////////////////////////
/********************************************************
GDB, AJW 20 Dec 2010

General Background
==================

	For a normal variety V, let D = d1 D1 + ...+ dn Dn be an effective QQ-Cartier
	divisor where the Di are irreducible Weil divisors on V.  Suppose that
	K_V + \Delta$ is QQ-Cartier so that we may consider its numerical pull-back.
	Then for some variety U and a birational morphism f:U -> V with exceptional
	divisors Ei we may write
		K_U + D_U ~ f*(K_V + D) + sum_i (a(Ei;V,D) Ei),
	where K_U, K_V are the canonical divisors on U,V, respectively; ~ is QQ linear
	equivalence; and D_U is	the strict or proper transform of D on U. The number
	a(Ek;V,D) is called the 'discrepancy' of the exceptional divisor Ek w.r.t. the
	log pair (V,D).

	For any such birational morphism f:U -> V, we say that an irreducible divisor
	E on U s.t. the image f(E) has co-dimension two or more is an 'exceptional
	divisor over V' and the image f(E) on V is the 'centre' of E on V.  To get a
	global measure of the singularities of (V,D) we define:

	The 'discrepancy' of the log pair (V,D) is the number
		discrep(V,D) = inf_E { a(E;V,D) | E is an exceptional divisor over V}.

	We impose restrictions on this global measure, defining several classes of
	pairs (V,D).  For more details on these classes and their uses see, for example,
	[Koll{\'a}r 1997, Singularities of pairs] or [Koll{\'a}r 1998, Birational
	geometry of algebraic varieties].

	We say that (V,D), or K_V + D is
	terminal											>   0,
	canonical											>=  0,
	Kawamata log terminal (klt) } if discrep(V,D) is {	>  -1 and RoundDown(D) = 0,
	purely log terminal (plt)							>  -1,
	log canonical (lc)									>= -1.

	For D = 0, we say that V has terminal,canonical,log terminal or log canonical
	singularities if (V,D) has (the definitions for klt and plt coincide when the
	boundary D = 0).

	Rather than working with all birational morphisms over V, to calculate the
	discrepancy of some pair (V,D) and determine which of the above classes is
	belongs, it suffices to understand the log resolution. The 'log resolution' of
	the pair (V,D) is a birational morphism f: U -> V s.t. U is smooth, the
	exceptional divisors of f and all components of the strict transform of D are
	smooth and the support of D is a simple normal crossings divisor.  Hironaka's
	theorem on the resolution of singularities in characteristic zero gives us that
	log resolutions exist for all pairs (V,D).

THINK: is okay over finite characteristic? / probably want F-Pure threshold instead.

	Observe also that either discrep(V,D) = -infinity, or -1 =< discrep(V,D) =< 1.
	That is, if the singularities of the pair (V,D) are worse than log canonical then
	the discrepancy can no longer provide a measure of their severity.

Definition
==========
	Let V be a variety with at worst log canonical singularities, P a point on V
	and D an effective QQ-Cartier divisor on V. Then the 'log canonical threshold'
	(lct) of the log pair (V,D) at P is the number
		lct_P(V,D) = sup{ c in QQ | (V,c D) is lc at P} in QQ union { +infinity}.

	We can also consider the lct of D along the whole of V, lct(V,D);
		lct(V,D) = inf{ lct_P(V,D) | P in V}
				 = sup{ c in QQ | (V, c D) is lc }.

Example
========
	Let C be a cubic curve on the projective plane P2.  Then
		lct(P2,C) =	1 if C is a smooth curve,
					1 if C is a curve with ordinary double points,
					5/6 if C is a curve with one cuspidal point,
					3/4 if C consists of a conic and a line that are tangent,
					2/3 if C consists of three lines intersecting at one point,
					1/2 if the support of C consists of two lines,
					1/3 if the support of C consists of one line.

	For some example code see below.

Contents
========
	We implement log canonical thresholds for affine and projective plane curves
	below, providing the intrinsics:
		* LogCanonicalThresholdAtOrigin(C::Sch)
		* LogCanonicalThreshold(C::Sch,P::Pt) / LCT(C,P)
		* LogCanonicalThreshold(C) / LCT(C)
		* LogCanonicalThresholdOverExtension(C)

To Do
=====
	* THINK: change C::Sch to C::Crv??
	* THINK: can we handle non-planar curves?
	* THINK: okay to look at log resolution over char 0, as it always exists (Hironaka)
			 --- but okay over finite char? (maybe don't want lct, but f-pure thresh.)
*********************************************************/
/////////////////////////////////////////////////////////
//		 Examples
/////////////////////////////////////////////////////////
/*Some affine curves:
	Aff<x,y> := AffineSpace(Rationals(),2);
	A := Curve(Aff,x);
	B := Curve(Aff,x*y);
	C := Curve(Aff,x^5 + y^9);
	D := Curve(Aff,x*y*(x-y));
	E := Curve(Aff,x*(x+y)*(x-y+1)*(y-1));
	curves := [A,B,C,D,E];
	sings := [SingularPoints(curve) : curve in curves];
	[LogCanonicalThresholdAtOrigin(curve) : curve in curves];
	[LCT(curve) : curve in curves];
*/
/////////////////////////////////////////////////////////
/*The projective cubics (see example in header):
	P2<x,y,z> := ProjectiveSpace(Rationals(),2);
	A := Curve(P2,x^3-y^2*z-3*x*z^2);	// smooth curve,
	B := Curve(P2,x^3-y^2*z-3*x*z^2+2*z^3);	// curve with ordinary double points,
	C := Curve(P2,x^3-y^2*z);	// curve with one cuspidal point,
	D := Curve(P2,(x^2+(y-z)^2-z^2)*y);	// conic and a line that are tangent,
	E := Curve(P2,x*y*(x-y));	// three lines intersecting at one (Eckardt) point,
	F := Curve(P2,x^2*y);	// support consists of two lines,
	G := Curve(P2,x^3);	// support consists of one line.
	curves := [A,B,C,D,E,F,G];
	sings := [SingularPoints(curves[i]) : i in [1..5]];
	assert not IsReduced(F) and not IsReduced(G);
	[LCT(curve) : curve in curves];
*/
/////////////////////////////////////////////////////////
/*2 singular anti-canonical divisors on a smooth cubic surface:
	P3<x,y,z,t> := ProjectiveSpace(Rationals(),3);
	X := Scheme(P3,x^3+y^3+z^3+t^3);
	C := Curve(Scheme(X,x+y)); //curve has Eckardt point
	LCT(C);
	D := Curve(Scheme(X,x+y+z+t)); //curve is 3 lines forming a triangle
	LCT(D);
*/
/////////////////////////////////////////////////////////
/*4 non-reduced, non-irreducible curves
	P2<x,y,z> := ProjectiveSpace(Rationals(),2);
	A := Curve(P2,z^2*(x^2*z+y^3)^3);
	assert not IsReduced(A) and not IsIrreducible(A);
	LCT(A);

	B := Curve(P2,x*y*(x-y)*(x+y+z)^10);
	assert not IsReduced(B) and not IsIrreducible(B);
	LCT(B);

	C := Curve(P2,x^62*y^90*z^23*(x^2*z+y^3)^191*(x*y*(x-y))^37);
	assert not IsReduced(C) and not IsIrreducible(C);
	time LCT(C);		// 1/191 (Time: ~30s)

	f := x^5*y^2 + x^4*y^3 + x^2*y^5 + x^4*y^2*z - 841/25*x^5*z^2 -
		 4263/25*x^4*y*z^2 - 2786/25*x^3*y^2*z^2 - 8704/25*x^2*y^3*z^2
		 - 406/5*x*y^4*z^2 - 49/25*y^5*z^2 - 103443/125*x^4*z^3 -
		 190008/125*x^3*y*z^3 - 544326/125*x^2*y^2*z^3 -
		 238224/125*x*y^3*z^3 - 2842/25*y^4*z^3 - 3167206/625*x^3*z^4
		 - 13346061/625*x^2*y*z^4 - 10630627/625*x*y^2*z^4 -
		 1243473/625*y^3*z^4 - 24205662/625*x^2*z^5 -
		 214272184/3125*x*y*z^5 - 48693211/3125*y^2*z^5 -
		 329560147/3125*x*z^6 - 180177116/3125*y*z^6 -
		 6456337657/78125*z^7;
	F := Curve(P2,f);
	assert not IsIrreducible(F) and IsReduced(F);
	LCT(F); // 1/3

	//make non-reduced curve from F
	D := Curve(P2,f*x^5);  // D = F + 5H,  1/5F is lc  => lct(D) = 1/5
	assert not IsIrreducible(D) and not IsReduced(D);
	LCT(D);

	//non-hypersurface example
	P3<x,y,z,t> := ProjectiveSpace(Rationals(),3);
	X := Scheme(P3,x^3+y^3+z^3+t^3);
	E := Curve(Scheme(X,(x+y)^2));
	assert not IsIrreducible(E) and not IsReduced(E);
	assert not IsHypersurface(E);
	LCT(E);

	//affine example
	Aff<a,b> := AffineSpace(Rationals(),2);
	F := Curve(Aff,a^2*(a^4+a^2*b+a*b^2));
	assert not IsIrreducible(F) and not IsReduced(F);
	LCT(F);

*/
/////////////////////////////////////////////////////////
//	Example of curve C s.t:	* C defined over Q,
//							* has extra singularities over splitting field, k
//							* lct(C) (over k) < lct(C) (over Q)
/////////////////////////////////////////////////////////
/*
	P2<x,y,z> := ProjectiveSpace(Rationals(),2);
		//from	C := RandomPlaneCurve(6,[1,2],P2);
	f := x*y^5 + y^6 + x^5*z + x^2*y^3*z + 2095/3402*y^5*z + x^4*z^2 -
    6244382419/8614788*x^3*y*z^2 -
    28401292681/8614788*x^2*y^2*z^2 -
    89017753225/25844364*x*y^3*z^2 -
    243243649115/232599276*y^4*z^2 -
    2798099890675/70354102*x^3*z^3 -
    22754590185549/281416408*x^2*y*z^3 -
    7190675316787/140708204*x*y^2*z^3 -
    75304687887883/7598243016*y^3*z^3 +
    17778098933653/140708204*x^2*z^4 +
    6098447759659/35177051*x*y*z^4 +
    24308031251845/422124612*y^2*z^4 -
    4694415764252/35177051*x*z^5 - 77497995284599/844249224*y*z^5
    + 6592790982389/140708204*z^6;

	C := Curve(P2,f);
	assert IsSingular(C);
	lct := LCT(C);
	assert lct eq 1;
	assert IsNodalCurve(C) eq false;
	//i.e. C must have singularities defined over some field extension

	assert HasSingularPointsOverExtension(C);
	Z := SingularSubscheme(C);
    singpts_k,k := PointsOverSplittingField(Z);
	Ck := ChangeRing(C,k);
	assert LCT(Ck) eq 2/3; //lct(C) < 1 over splitting field
	assert LCT(Ck) eq LogCanonicalThresholdOverExtension(C);
*/
/////////////////////////////////////////////////////////
//			Intrinsics
/////////////////////////////////////////////////////////
forward reduced_subcurve;
forward affine_plane_patch; // not needed till LogCanonicalThreshold(C,P)

intrinsic LogCanonicalThresholdAtOrigin(C::Sch) -> FldRatElt
{The local log canonical threshold of the affine plane curve C computed at the origin.}
	require Characteristic(BaseRing(C)) eq 0:
		"Characteristic of the base field of C must be 0.";
	require IsAffine(C): "The curve C is not affine.";
	A := Ambient(C);
	require (Length(A) eq 2) and (Dimension(C) eq 1): "C is not a plane affine curve";
	origin := Origin(A);
	require origin in C: "The origin is not a point on C.";
	if IsReduced(C) then
		if IsNonsingular(C,origin) or IsNode(C,origin) then
			return 1;
		end if;
		res_grph := ResolutionGraph(C);
		i := Size(res_grph); //number of blowups required
		//For each blowup read multiplicity m_k and canonical multiplicity c_k,
		//calculate l_k=(1+c_k)/m_k and keep track of the minimum value.
		UpdateGraphLabels(res_grph);
			//THINK: this may break at a later stage
			//       --- see comment at the bottom of the document.
		grph := UnderlyingGraph(res_grph);
		seqn := [ Rationals() | ];
		for k in [1..i] do
			res_data_k := VertexLabel(grph,k);
			m_k := res_data_k[2];  //multipicity of E_k
			c_k := res_data_k[3];  //canonical multiplicity of E_k
			l_k := (1+c_k)/m_k;   //discrepancy
			Append(~seqn,l_k);
		end for;
		//compute lct(C)
		min_value, min_index := Minimum(seqn);
		lct :=  min_value;
		return lct;
	else
		//assert not IsReduced(C);
		C_sub,m := reduced_subcurve(C,origin);
		lct_sub := LogCanonicalThresholdAtOrigin(C_sub);
		if (1/m) lt lct_sub then
			//i.e. 1/m is already enough to guarantee that C is lc
			lct := (1/m);
		else
			lct:=lct_sub*(1/m);	//THINK: really....re-think about this:
								//		 could there be cases where lct_sub
								//		 is enough on its own?
		end if;
		return lct;
	end if;
end intrinsic;

intrinsic LogCanonicalThreshold(C::Sch,P::Pt) -> FldRatElt
{The local log canonical threshold of the curve C computed at the point P.}
	require Ambient(C)!P in C: "Point P is not on the curve C.";
	require Dimension(C) eq 1: "Scheme C is not a curve.";
	if IsAffine(C) then
		lct := LogCanonicalThresholdAtOrigin(Translation(C,P)(C));
		return lct;
	elif IsProjective(C) then
		if IsReduced(C) then
			sings := SingularPoints(C);
			if not P in sings then return 1;	end if; //returns 1 if C smooth at P
			if IsNode(C,P) then return 1;	end if;     //returns 1 if P a node of C
			lcts := [Rationals() | ];
			for i in [1..#sings] do
			//THINK: why are you going through
			//		 all the singular points if you want lct(C,P)??
				Q := sings[i];
				map_Qto0 := Translation(C,Q);
				Q0 := map_Qto0(Q);
				C0 := map_Qto0(C);
				P2 := ProjectiveSpace(BaseField(C0),2);
				if Dimension(Ambient(C)) eq 2 then
					Caff,Qaff,chart_no := AffinePatch(C0,Q0);
					assert chart_no eq 1; // we should be on the 1st affine patch
					assert Qaff eq Origin(Ambient(AffinePatch(C0,Q0)));
				else
					//THINK: assuming C plane curve here
					Caff,Qaff := affine_plane_patch(C0,Q0,P2);
				end if;
				Append(~lcts,LogCanonicalThreshold(Caff,Qaff));
			end for;
			lct := Minimum(lcts);
			return lct;
		else
			//assert not IsReduced(C);
			C_sub,m := reduced_subcurve(C,P);
			lct_sub := LogCanonicalThreshold(C_sub,P);
			if (1/m) lt lct_sub then
				//i.e. 1/m is already enough to guarantee that C is lc
				lct := (1/m);
			else
				lct:=lct_sub*(1/m);	//THINK: really....re-think about this:
									//		 could there be cases where lct_sub
									//		 is enough on its own?
			end if;
			return lct;
		end if;
	else
		require IsOrdinaryProjective(ProjectiveClosure(Ambient(C)))
				and Dimension(Ambient(C)) eq 2:
				"Curve should lie in an affine or ordinary projective plane.";
				//THINK: do you need this here?
	end if;
end intrinsic;

// Synonym for LogCanonicalThreshold(C,P)
intrinsic LCT(C::Sch,P::Pt) -> FldRatElt
{The local log canonical threshold of the curve C computed at the point P.}
	lct :=LogCanonicalThreshold(C,P);
	return lct;
end intrinsic;

intrinsic LogCanonicalThreshold(C::Sch) -> FldRatElt
{The log canonical threshold of the curve C computed at its singular k-points, where k is the base field of C.}
	require Dimension(C) eq 1: "Scheme C is not a curve.";
	if IsReduced(C) then
		sings := SingularPoints(C);
		if #sings eq 0 then return 1; end if;
			//returns 1 if C smooth over its base field
		lcts := [LogCanonicalThreshold(C,Q) : Q in sings];
		lct := Minimum(lcts);
	else
		//assert not IsReduced(C);
        C_red := Curve(ReducedSubscheme(C));
			//THINK: I am calc. this twice, once here and once in reduced_subcurve().
		sings := SingularPoints(C_red);
		lcts := [];
		//returns 1/m if C_red smooth over its base field
		if #sings eq 0 then
			n := Degree(C)/Degree(C_red);
			return (1/n);
		end if;
		lcts := [LogCanonicalThreshold(C,Q) : Q in SingularPoints(C_red)];
		lct := Minimum(lcts);
	end if;
	// if Overext then
	// 	if HasSingularPointsOverExtension(C_red) then
	// 		bool := true; else bool := false;
	// 	end if;
	// 	return lct,bool;
	// else
	// 	return lct;
	// end if;
	return lct;
end intrinsic;

// Synonym for LogCanonicalThreshold(C)
intrinsic LCT(C::Sch) -> FldRatElt,BoolElt
{The log canonical threshold of the curve C computed at its singular k-points, where k is the base field of C.}
	lct := LogCanonicalThreshold(C);
	return lct;
end intrinsic;

intrinsic LogCanonicalThresholdOverExtension(C::Sch) -> FldRatElt
{The log canonical threshold of the curve C computed at all singular points, extending the base field of C if necessary.}
	require Dimension(C) eq 1: "Scheme C is not a curve.";
	if IsReduced(C) then
		sings := SingularPoints(C);
		if HasSingularPointsOverExtension(C) then
			Z := SingularSubscheme(C);
			singpts_k,k := PointsOverSplittingField(Z);
			Ck := ChangeRing(C,k);
			lct := LogCanonicalThreshold(Ck);
		else
			lct := LogCanonicalThreshold(C);
		end if;
		return lct;
	else
		//assert not IsReduced(C);
		C_red := Curve(ReducedSubscheme(C));
		sings := SingularPoints(C_red);
		if HasSingularPointsOverExtension(C_red) then
			Z := SingularSubscheme(C_red);
			sings_k,k := PointsOverSplittingField(Z);
			Ck := ChangeRing(C,k);
			lct := LogCanonicalThreshold(Ck);
		else
			lct := LogCanonicalThreshold(C);
		end if;
		return lct;
	end if;
end intrinsic;

/////////////////////////////////////////////////////////
//		Non-reduced curves function
/////////////////////////////////////////////////////////
// For a non-reduced curve C and a point Q in C, returns the reduced subcurve
// C_sub of primes components of C passing through Q along with m the max
// coefficients of the primes components of C passing through Q.
forward curve_components;

function reduced_subcurve(C,Q)
	//assert not IsReduced(C);
	if IsHypersurface(C) then
		C_red := Curve(ReducedSubscheme(C));
		//find the primesC_throughQ := {PrimeComponents(C) that pass through Q}
		primesC_throughQ := [ PrimeComponents(C)[j] : j in [1..#PrimeComponents(C)]
										| Q in PrimeComponents(C)[j] ];
		//find m := {max multi of the primeC_throughQ}
		multi_primesCthroughQ :=[];
		for k in [1..#primesC_throughQ] do
		    _,multi := RemoveHypersurface(C,primesC_throughQ[k]);
		//RemoveHypersurface() simply factors out the eqn of the component
		//to find its multiplicity; cheaper than using colon ideals
		//if C is not a hypersurface
		    Append(~multi_primesCthroughQ,multi);
		end for;
		m := Maximum(multi_primesCthroughQ);
		eqns := [DefiningEquation(primesC_throughQ[l]) :
								 l in [1..#primesC_throughQ]];
		eqn := &*{eqn : eqn in eqns};
		C_sub := Curve(Ambient(C),eqn); //reduced curve
		return C_sub, m;
	else
		prime_fac:= curve_components(C);
		primes := [prime_fac[i][1] : i in [1..#prime_fac]];
		multis := [prime_fac[i][2] : i in [1..#prime_fac]];
		primes_through_Q_indx := [ i : i in [1..#primes]	| Q in C];
		multis_through_Q := [ multis[i] : i in primes_through_Q_indx ];
		m := Maximum(multis_through_Q);
		primes_through_Q := [primes[i] : i in primes_through_Q_indx];
		comps := [Scheme(Ambient(C),primes_through_Q[i])
								: i in [1..#primes_through_Q]];
		for i in [1..(#primes_through_Q_indx - 1)] do
			comps[1] := Union(comps[1],comps[2]);
			Remove(~comps,2);
		end for;
		C_sub := Curve(comps[1]);
		return C_sub,m;
	 end if;
end function;

// //not used
// function find_m(Ccrv,P)
// 	//find the maximum multiplicity of the components of Cdiv passing through P
// 	if IsReduced(Ccrv) then return 1; end if;
// 	prime_fac:= curve_components(Ccrv);
// 	primes := [prime_fac[i][1] : i in [1..#prime_fac]];
// 	multis := [prime_fac[i][2] : i in [1..#prime_fac]];
// 	primes_through_P_indx := [ i : i in [1..#primes] | P in Ccrv];
// 	multis_through_P := [ multis[i] : i in primes_through_P_indx ];
// 	m := Maximum(multis_through_P);
// 	return m;
// end function;

/////////stolen from divisors.m
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

function curve_components(C)
	oldfactn := [ CartesianProduct(PowerStructure(RngMPol),Rationals()) |
		< Ideal(C), 1 > ];
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
	return [ CartesianProduct(PowerStructure(RngMPol),Rationals()) |
		< prime_ideals[i], multiplicities[i] > :
				i in [1..#multiplicities] ];
end function;
/////////////////////////////////////////////////////////
//		Translation P to 0 and affine patch function
/////////////////////////////////////////////////////////
// p in C and C is a plane curve lying in some projective space.
// Return a AA^2 patch of p in C inside the given P2.
function affine_plane_patch(C,p,P2)
	Pi := Span(Ambient(C),C);
	if IsHypersurface(Pi) then		//i.e. Span(Ambient(C),C) ne Ambient(C);
		bool,param := ParametrizeProjectiveHypersurface(Pi,P2);
		assert bool;
		algmap := AlgebraMap(param);
		return AffinePatch( 			//ResolutionGraph needs Crv, hence Curve
				Curve(Scheme(P2,algmap(DefiningEquations(C)))),Pullback(param,p));
	else
		error "Curve C should be planar (or its support smooth).";
		//THINK: can we handle non-planar curves.
	end if;
end function;
/////////////////////////////////////////////////////////
//		Comments on ResolutionGraph() (from Geoff)
/////////////////////////////////////////////////////////
/*
	*	The labels of the resolution graph contain up to four pieces of
		information, depending on what is known at the time.

	*	This information is subject to change when computed (or set by
		the caller), so it cannot be assumed to be simply static.

	*	The labels on the underlying graph are set when the resolution
		graph is printed, using the then-current information.

	*	If the underlying graph does not reflect the current labelling,
		then this is bad.  However, if the underlying graph appears to
		change once more information is known, then this is also bad.

	There is no "right" solution under this model.  Vexing.
*/
/////////////////////////////////////////////////////////
//
/////////////////////////////////////////////////////////
