freeze;

/*********************************************************************
			del Pezzo surfaces
			==================

MB, GDB, SRD, AJW
January, 2011


Definition
==========
A DEL PEZZO SURFACE X is a projective scheme that is:
	2-dimensional
	a variety, i.e. reduced and irreducible
	either nonsingular or having at worst du Val singularities
	-K_X is ample.

Any del Pezzo surface will be treated primarily in its usual
(pluri-)anticanonical embedding, with other representations being
available as they are computed.
In particular, although a given surface Y may satisfy the conditions
of the definition above, the type change to our del Pezzo data type
will return a variety isomorphic to Y in this representation.
(N.B. If Y is a weak del Pezzo surface - i.e. Y is smooth or du Val
and -K_Y is nef and big - then the type change will contract rational
configurations of -2-curves on Y to new du Val singularities. Thus
the resulting del Pezzo surface will not quite be isomorphic to Y,
but it is birational in a well-understood way. But for now, we stick
to the nonsingular case only.)

SrfDelPezzo is a subtype of Sch.  It's special attributes are
defined at package level (in this file).  Degree is an internal 
attribute for general Sch.

*********************************************************************/

declare attributes SrfDelPezzo:
    is_rational,		// true iff X is rational over k, its base field
    parametrisation,            // a param over k if one exists
    is_k_minimal,		// true iff rank(Pic) = 1 (over k)
    P1xP1,                      // for degree 8: true if known to be geometrically
                                // P1 x P1, false if known not to be.
picard_lattice,
picard_lattice_basis,
picard_lattice_basis_lines,

    EckhardtPoints,
    ramification_curve,		// for degrees 1 and 2, the ramification curve 
                                // of the double cover to P112 or P2

    GeometricPicardGroup,       // used by the intrinsic GeometricPicardGroup 
                                // (stores the Galois module, the intersection matrix
    PicardGaloisModule;         // used by the intrinsic PicardGaloisModule


//////////////////////////////////////////////////////////////////////
//			Constructors
//////////////////////////////////////////////////////////////////////

intrinsic DelPezzoSurface(f::RngMPolElt) -> SrfDelPezzo
{The del Pezzo surface of degree 3 defined by the cubic form f}

  P := Parent(f);
  require Rank(P) eq 4 and Degree(f) eq 3 and IsHomogeneous(f):
     "The given polynomial should be a cubic form in 4 variables";

  if not IsField(BaseRing(P)) then
     P := ChangeRing(P, FieldOfFractions(BaseRing(P)));  
     f := P!f;
  end if;

  bool, X := IsDelPezzo(Scheme(ProjectiveSpace(P), f));
  require bool: 
     "The given polynomial does not define a (nonsingular) del Pezzo surface";

  return X;
end intrinsic;

forward has_colinear,has_coconic,has_db_cubic,coconic_pts,lin_sys,del_pezzo_surf;

intrinsic IsDelPezzo(Y::Sch) -> BoolElt, SrfDelPezzo, MapSch
{True iff Y is a del Pezzo surface.  If true, also returns the image X 
of the standard (pluri-)anticanonical embedding of Y, and the map Y -> X}

	if Type(Y) eq SrfDelPezzo then
		return true, Y, IdentityMap(Y);
	end if;

        // THINK: is_obviously_delpezzo? (can use same defining equations)

	if not (IsNonsingular(Y) and IsProjective(Y) and
		Dimension(Y) eq 2) then
			// THINK: need IsDuVal or something
		return false,_,_;
	end if;
	// Otherwise we need to check that -K_Y is ample and compute
	// its embedding.
	K := CanonicalSheaf(Y);
	deg := IntersectionPairing(K,K);
	if deg notin {1..9} then	// can't be dP
		return false,_,_;
	end if;
        deg := Integers()! deg;
	D := Dual(K);
	if deg notin {1,2} then
	    f := DivisorMap(D);
	    if Type(f) eq MapSchGrph then
		f := SchemeGraphMapToSchemeMap(f);
	    end if;
	    h0D := Dimension(Image(f,Y,1)) + 1;
	    if h0D ne deg + 1 then	// not a dP
		return false,_,_;
	    else	// THINK: RR should say that -K_Y is ample now
		if deg eq 3 then
		    X := Image(f,Y,3);
		else
		    X := Image(f,Y,2);
		end if;
		    // THINK: it may be that the image has
		    // already been computed and cached - else
		    // compute as int(quadrics) or cubic by linalg.
		    // if so simply do: X := Image(f);
                X := InternalDelPezzoSurface(Ambient(X), Equations(X));
		X`Degree := deg;
			// THINK: check that g is IM if theory doesn't help
		return true,X,f;
	    end if;
	end if;
	// THINK: to do deg 1,2
end intrinsic;

// THINK: can allow mild singularities for weak del Pezzos (infinitely near points?)

intrinsic DelPezzoSurface(Z::Clstr) -> SrfDelPezzo
{The smooth del Pezzo surface of degree (9-r) obtained as the blowup of the 
r (< 9) points of the zero-dimensional scheme Z in an ordinary projective plane}

	require IsNonsingular(Z): "Z has multiple points.";
        P2 := Ambient(Z);
        F := BaseRing(Z);
	deg := 9 - Degree(Z);
        require deg ge 0: "The argument should have degree at most 9";

        // THINK: check general position now in the case of 3 points 

	X := del_pezzo_surf(P2, [Z], deg);

        // Check general position (only necessary if there are > 2 points)
	require deg ge 7 or IsNonsingular(X): 
               "The specified points are not in general position (the constructed surface is singular)";

	return X;
end intrinsic;

intrinsic DelPezzoSurface(S::Setq[Pt]) -> SrfDelPezzo
{The smooth del Pezzo surface of degree (9-r) obtained as the blowup of the 
r (< 9) points contained in S}

    U := Universe(S);
    if ISA(Type(U), SetPt) then
        P2 := Ambient(Scheme(U));
    elif ISA(Type(U), Sch) then
        P2 := Ambient(U);
    end if;
    require IsProjective(P2) and Gradings(P2) eq [ [1,1,1] ] and Dimension(P2) eq 2:
           "The given points should be in an ordinary projective plane";

    clusters := {Cluster(pt) : pt in S};
    deg := 9 - &+[Integers()| Degree(c) : c in clusters];
    require deg ge 0: "The argument contains more than 9 geometric points";

    SS := {@ pt : pt in S @};
    require PointsInGeneralPosition(P2,SS): "The specified points are not in general position";

    return del_pezzo_surf(P2,S,deg);
end intrinsic;

intrinsic DelPezzoSurface(P2::Prj, S::List) -> SrfDelPezzo
{"} // "
    require IsProjective(P2) and Gradings(P2) eq [ [1,1,1] ] and Dimension(P2) eq 2:
           "The first argument should be an ordinary projective plane";

    SS := [* *];
    F := BaseRing(P2);
    for x in S do 
        c := Eltseq(x);
        bool, pt := IsCoercible(P2(F), c);
        if not bool then
            bool, pt := IsCoercible(P2(Universe(c)), c);
        end if;
        require bool: "The second argument should be a list of points contained in the first argument";
        Append(~SS, pt);
    end for;

    clusters := {Cluster(pt) : pt in SS};
    deg := 9 - &+ [Integers()| Degree(c) : c in clusters];
    require deg ge 0: 
           "The second argument contains more than 9 geometric points (over the base field)";

        // THINK: check general position now in the case of 3 points 

	X := del_pezzo_surf(P2, SS, deg);

        // Check general position (only necessary if there are > 2 points)
	require deg ge 7 or IsNonsingular(X): 
               "The specified points are not in general position (the constructed surface is singular)";

	return X;
end intrinsic;

// Construct the del Pezzo surface as the blow up at the points of S
// THINK: LinearSystem(pt, mult) needs to be implemented for points in extensions

function del_pezzo_surf(P2,S,deg)

	if deg gt 2 then
		Pdeg := ProjectiveSpace(BaseRing(P2),deg);

                K := LinearSystem(P2,3);
                for x in S do
                    K := LinearSystem(K, x);
                end for;

		phi := map< P2 -> Pdeg | Sections(K)>;
		if deg eq 3 then
		    X := Image(phi,P2,3);
		else
		    X := Image(phi,P2,2);
		end if;
		phi := Restriction(phi,P2,X:Check := false);
		//assert BasePoints(phi) eq S;
		bool, phiinv := IsInvertible(phi);
		//assert bool;
		phi := Inverse(phiinv);
	elif deg eq 2 then
		//make |-K| and |-2K|
		K := lin_sys(P2,S,3,1);
		K2:= lin_sys(P2,S,6,2);
		//weight 1 variables for P(1112)
		x1 := Sections(K)[1];
		x2 := Sections(K)[2];
		x3 := Sections(K)[3];
		//weight 2 variable for P(1112)
		L := LinearSystem(K2,[x1^2,x1*x2,x2^2,x2*x3,x3^2,x3*x1]);
		s := Sections(Complement(K2,L))[1];
		//obtain Y
		k := BaseRing(P2);
		WP := ProjectiveSpace(k,[1,1,1,2]);
		phi := map< P2 -> WP | [x1,x2,x3,s]>;
		//THINK: need to compute inverse of phi here for X`rational_param
		Y := Image(phi, P2, 4); //image is the degree 2 del Pezzo
		eqn := DefiningEquation(Y);
		//tidy up eqn of Y
		t := WP.4;
		t2_coeff := &+[ term div t^2 : term in Terms(eqn) | IsDivisibleBy(term,t^2) ];
		eqn := (eqn)/(t2_coeff); //remove t^2 coefficient
		assert &+[ term div t^2 : term in Terms(eqn) | IsDivisibleBy(term,t^2) ] eq 1;
		t_coeff  := &+[ term div t : term in Terms(eqn)
							| IsDivisibleBy(term,t) and not IsDivisibleBy(term,t^2)];
		rem_coeff := &+[ term : term in Terms(eqn) | not IsDivisibleBy(term,t) ];
		//change coordinates by completing the square to get rid of terms in t
		new_t := t + (t_coeff)/2;
		chng_coord := Inverse(map< WP -> WP | [WP.1,WP.2,WP.3,new_t]>);
		X := Scheme(WP,chng_coord(eqn));
	elif deg eq 1 then
		//make |-K|, |-2K| and |-3K|
		K := lin_sys(P2,S,3,1);
		K2:= lin_sys(P2,S,6,2);
		K3:= lin_sys(P2,S,9,3);
		//weight 1 variables for P(1123)
		x1 := Sections(K)[1];
		x2 := Sections(K)[2];
		//weight 2 variable for P(1123)
		L := LinearSystem(K2,[x1^2,x1*x2,x2^2]);
		y1 := Sections(Complement(K2,L))[1];
		//weight 3 variable for P(1123)
		M := LinearSystem(K3,[x1^3,x1^2*x2,x1*x2^2,x2^3,y1*x1,y1*x2]);
		z1 := Sections(Complement(K3,M))[1];
		//obtain Y
		k := BaseRing(P2);
		WP := ProjectiveSpace(k,[1,1,2,3]);
		phi := map< P2 -> WP | [x1,x2,y1,z1]>;
		//THINK: need to compute inverse of phi here for X`rational_param
                Y := Image(phi, P2, 6); //image is the degree 1 del Pezzo
		eqn := DefiningEquation(Y);
		//tidy up eqn of Y
		t := WP.4;
		t2_coeff := &+[ term div t^2 : term in Terms(eqn) | IsDivisibleBy(term,t^2) ];
		eqn := (eqn)/(t2_coeff); //remove t^2 coefficient
		assert &+[ term div t^2 : term in Terms(eqn) | IsDivisibleBy(term,t^2) ] eq 1;
		t_coeff  := &+[ term div t : term in Terms(eqn)
							| IsDivisibleBy(term,t) and not IsDivisibleBy(term,t^2)];
		rem_coeff := &+[ term : term in Terms(eqn) | not IsDivisibleBy(term,t) ];
		//change coordinates by completing the square to get rid of terms in t
		new_t := t + (t_coeff)/2;
		chng_coord := Inverse(map< WP -> WP | [WP.1,WP.2,WP.3,new_t]>);
		X := Scheme(WP,chng_coord(eqn));
	end if;
      
        X := InternalDelPezzoSurface(Ambient(X), Equations(X));
	X`Degree := deg;
	X`is_rational := true;
        X`parametrisation := phi;
	X`picard_lattice := RSpace(IntegerRing(),#S+1);
		//basis of Pic lattice: {l,e1,...,er} e.g.
			//-K := Pic![3,-1,-1,-1,-1,-1,-1];
			//L12 := Pic![1,-1,-1,0,0,0,0];
			//L34 := Pic![1,0,0,-1,-1,0,0];
			//C1 := Pic![2,0,-1,-1,-1,-1,-1];
			//C2 := Pic![2,-1,0,-1,-1,-1,-1];
	return X;
end function;

////////////////////////////////////////////////////////////////////////////////
//			Misc. functions
////////////////////////////////////////////////////////////////////////////////

function lin_sys(P,S,d,m)
//P Ambient(L), S List of pts, d degree of lin sys, m desired multi at pts of S
//returns the sub-lin sys of the complete lin sys of mons of deg d
//that pass through the points of S with multiplicity m.
	L := LinearSystem(P,d);
	for x in S do
		L := LinearSystem(L,x,m);
	end for;
	return L;
end function;

////////////////////////////////////////////////////////////////////////////////
//			Points in general position
////////////////////////////////////////////////////////////////////////////////

//THINK: save conics and lines on P2 to get lines on del Pezzo?

/*Example:
	k := Rationals();
	P2<x,y,z> := ProjectiveSpace(k,2);
	C := Curve(P2,x^3 + 3*x^2*z - y^2*z);
	P := P2![0,0,1];
	assert IsNodalCurve(C);
	assert #SingularPointsOverSplittingField(C) eq 1;
	assert IsNode(C,P);
	pts := {@ [0,0,1],[-3,0,1],[-2,2,1],[1,2,1],
			[1,-2,1],[-2,-2,1],[6,18,1],[6,-18,1] @};
	S := {@ P2!P : P in pts  @};
	for P in S do
		assert P in C;
		//the 8 points of S lie on the cubic C where P is a double point
	end for;
	ColinearPointsOnPlane(P2,S);
	PointsInGeneralPosition(P2,S);
	PointsInGeneralPosition(P2,S:NonGenPts:=true);
*/

forward pts_in_gen_pos_aux,test_pts_over_spliting;

function has_colinear(P2,S)
	//error if #S lt 3, "too few points for line.";
	S2 := SetToIndexedSet(Subsets(IndexedSetToSet(S), 2));
	line_bool := #{Line(P2,S2[i]) : i in [1..#S2]} ne #S2;
	return line_bool;
end function;

function has_coconic(P2,S)
	//error if #S lt 5, "too few points for conic.";
	S_set := IndexedSetToSet(S);
	conic_bool := HasConic(P2,S_set);
	if conic_bool then return conic_bool; end if;
	S5 := SetToIndexedSet(Subsets(S_set, 5));
	conic_bool := #{Conic(P2,S5[i]) : i in [1..#S5]} ne #S5;
	return conic_bool;
end function;

function has_db_cubic(P2,S)
	//error if #S lt 8, "too few points for cubic.";
	Z := Cluster(P2,S);
	cubics := LinearSystem(LinearSystem(P2,3),Z);
	cubics_w_db_pt := [LinearSystem(cubics,P2!P,2) : P in S
			| #Sections(LinearSystem(cubics,P2!P,2)) gt 0];
	cubic_bool := not IsEmpty(cubics_w_db_pt);
	return cubic_bool;
end function;

function coconic_pts(P2,S)
	S_set := IndexedSetToSet(S);
	conic_bool := HasConic(P2,S_set);
	if conic_bool then
		return [ s : s in S_set];
	end if;
	S5 := SetToIndexedSet(Subsets(S_set, 5));
	conics := {Conic(P2,S5[i]) : i in [1..#S5]};
	coco_pts := [];
	for C in conics do
		pts_on_C := [P : P in S | P in C];
		if #pts_on_C gt 5 then
			Append(~coco_pts,pts_on_C);
		end if;
	end for;
	return coco_pts;
end function;

function MaximalSubsets(A) // SetIndx[SetEnum] -> SetIndx
// {The sets of A such that each set in S is a subset contained in it.}
	B := A;
	for i in [1..#A] do
		for j in [a : a in [1..#A] | a ne i] do
			if A[j] subset A[i] then
				B := B diff {@ A[j] @};
			end if;
		end for;
	end for;
	return B;
end function;

intrinsic ColinearPointsOnPlane(P2::Prj,S::SetIndx[Pt]) -> SeqEnum
	{Takes the set of points S and returns enumerated sequences of (3 or more) colinear points.}
	for P in S do
		require P in P2: "The points of S do not lie on P2.";
	end for;
    require Dimension(P2) eq 2 and Gradings(P2) eq [ [1,1,1] ]:
		"P2 is not an ordinary projective plane.";
	PP2,S_aux := test_pts_over_spliting(P2,S);

	colinear_aux := {@ set : set in Subsets(IndexedSetToSet(S_aux))
			| not IsEmpty(set) and #set gt 2 and HasLine(P2,set) @};
	colinear := [ SetToSequence(set) : set in MaximalSubsets(colinear_aux)];
	return colinear;
		  //THINK: this is returning points in the
		  //	   closure of the base ring of P2 (PP2)...
end intrinsic;

intrinsic PointsInGeneralPosition(P2::Prj,S::SetIndx[Pt]:NonGenPts:=false) -> BoolElt,SeqEnum,SeqEnum,SeqEnum
	{True iff the (8 or less) points of S are in general position. 
         General position means: no 3 are colinear, no 6 lie on a conic 
         and no 8 lie on a cubic with a double point at one of them. 
         If the option NonGenPts is true, also returns the sets of colinear points, 
         the sets of co-conic points, and the eight points, if these configurations exist}

//THINK: do we have a use to extend this to larger numbers of points?
	require #S eq #IndexedSetToSet(S): "There are mutliple points in S.";
	require #S lt 9: "Not implemented for more than 8 points in S.";
    require Dimension(P2) eq 2 and Gradings(P2) eq [ [1,1,1] ]:
		"P2 is not an ordinary projective plane.";
	P2_aux,S_aux := test_pts_over_spliting(P2,S);
	return pts_in_gen_pos_aux(P2_aux,S_aux,NonGenPts);
end intrinsic;

function pts_in_gen_pos_aux(P2,S,NonGenPts)
	if #S eq 8 then
		line_bool := has_colinear(P2,S);
	    conic_bool := has_coconic(P2,S);
		cubic_bool := has_db_cubic(P2,S);
		bool := line_bool or conic_bool or cubic_bool;
		if NonGenPts and bool then
			if line_bool then line_pts := ColinearPointsOnPlane(P2,S);
			else line_pts := []; end if;
			if conic_bool then conic_pts := coconic_pts(P2,S);
			else conic_pts := []; end if;
			if cubic_bool then	db_cubic_pts := IndexedSetToSequence(S);
			else db_cubic_pts := []; end if;
			return not bool,line_pts,conic_pts,db_cubic_pts;
 		elif NonGenPts then
			return not bool,[],[],[]; //THINK: better to return "not bool,_,_,_"??
		else
			return not bool;
		end if;
	elif #S lt 8 and #S gt 5 then
		line_bool := has_colinear(P2,S);
	    conic_bool := has_coconic(P2,S);
		bool := line_bool or conic_bool;
		if NonGenPts and bool then
			if line_bool then line_pts := ColinearPointsOnPlane(P2,S);
			else line_pts := []; end if;
			if conic_bool then conic_pts := coconic_pts(P2,S);
			else conic_pts := []; end if;
			return not bool,line_pts,conic_pts,[];
 		elif NonGenPts then
			return not bool,[],[],[];
		else
			return not bool;
		end if;
	elif #S lt 6 then
		bool := has_colinear(P2,S);
		if NonGenPts then
			if bool then line_pts := ColinearPointsOnPlane(P2,S);
			else line_pts := []; end if;
			return not bool,line_pts,[],[];
 		elif NonGenPts then
			return not bool,[],[],[];
		else
			return not bool;
		end if;
	end if;
end function;

function test_pts_over_spliting(P2,S) //S set of points on projective plane P2
	//THINK: need to improve tests
	test1 := &and[ Type(Parent(a)) eq Type(BaseField(P2)) :
						a in { Q: Q in Eltseq(P), P in S } ];
	if test1 then
		test2 := &and[ Parent(a) eq BaseField(P2) :
							a in { Q: Q in Eltseq(P), P in S } ];
		if test2 then
			return P2,S;
		end if;
	else
		S,kk := PointsOverSplittingField(Cluster(P2,S));
		PP2 := BaseChange(P2,kk);
		aux := [ Eltseq(P) :  P in S];
		S_aux := {@ PP2!P : P in aux @};
	    return PP2,S_aux;
	end if;
end function;

//////////////////////////////////////////
//		Eckardt Points
//////////////////////////////////////////

intrinsic EckardtPoints(X::SrfDelPezzo) -> Sch
	{Computes the Eckardt points of the Del Pezzo surface X.  
         (These are the points where three coplanar lines meet.)
         The zero-dimensional scheme of the points is returned.}

        if assigned X`EckhardtPoints then
           return X`EckhardtPoints;
        end if;

	require Degree(X) eq 3: "Only implemented for cubic surfaces.";

	H:= Scheme(Ambient(X),Determinant(HessianMatrix(X)));
	if IsNonSingular(H) then return {@ @}; end if;

	sings_H := SingularSubscheme(H);
	ecks := Intersection(sings_H,X);
	assert Dimension(ecks) lt 1;
        return ecks;
end intrinsic;

/*
function find_cubic_with_Eckardt(P3,k) //k number of Eckardt points
	error if k gt 18, "Maximum possible number of Eckardt points is 18.";
	flag := false;
	numb := 0;
	while not flag do
		bool, S := IsDelPezzo(Scheme(P3, &+[ Random(-1,1)*m
		           : m in MonomialsOfDegree(CoordinateRing(P3),3) ] ));
		flag := bool and IsNonSingular(S) and Degree(EckardtPoints(S)) eq k;
		numb := numb + 1;
		printf "Attempt %o\n", numb;
	end while;
	return S;
end function;
*/

//////////////////////////////////////////
//		Parametrization
//////////////////////////////////////////

// This will call all the other parametrization routines
/*
intrinsic Parametrization(X::SrfDelPezzo) -> MapSch
{A birational parametrization of the Del Pezzo surface X}

	if not assigned X`parametrisation then
	    require false: "This new intrinsic is not finished -- use the existing Parametrization*** intrinsics";
	end if;
 	return X`parametrisation;
end intrinsic;
*/

