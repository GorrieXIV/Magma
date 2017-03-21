freeze;
 
///////////////////////////////////////////////////////////////////////
//			K3 database
// GB Oct 2003
//
// Intrinsics to compute K3 databases from scratch (as sequences).
// Arguments can be the singular rank r of the K3 (r = 19 is the
// correct maximum) and the genus, an integer g >= -1.
///////////////////////////////////////////////////////////////////////

import "../K3/AFR.m": get_AFR;
import "../HilbertSeries/misc.m": is_subseq;
import "../K3/k3.m": k3_degree, k3_hilbert_series;

///////////////////////////////////////////////////////////////////////
//		Outline of the basic steps
///////////////////////////////////////////////////////////////////////

/*
Naming conventions:
		objects		-- lower case	b
    sets or seq of those	-- upper case	B
    sets or seqs of those	-- double upper case	BB

Different parts of the routine split into substeps:

	Part one
	--------
1.	fix genus g
2.	compute or input a set of baskets BB

	Part two
	--------
3.	for B in BB compute d(g,B) = deg(g,B), h(g,B) = hilb(g,B)
	compile DD0 = [ <g,B,d,h,H> ] where H = [first 21 coeffs of h]
4.	sort [ H ] in increasing order calling the result HH
	(for us HH is a sequence; in harder cases it might already be a graph)

	Part three
	----------
5.	make DD from DD0 by sorting it according to its H component
	    DD = [ <g,B,d,h,H,n> ] where n is the natural order, called INDEX
6.	compile PP0 = [ [<p,d1,B1>] ] in parallel with DD where
	    p is any singularity from B
	    d1 is the degree of the image of projection from p
	    B1 is the basket of the image of projection from p
7.	compute PP = [ [<m,p>] ] from PP0 where in the n-th term [<m,p>]:
	    each p runs through those of PP0[n] having positive d1;
	    m is the index of the image --- when searching note that m < n
	    bcs the Hilbert series are in an order which projection respects

	Part four
	---------
8.	create KK, a sequence of K3s with projection data from DD and PP

	Part five
	---------
9.	inductively modify weights in KK using the expected behaviour
	    of Type I projections and assuming that the 95 K3s in
	    codimension 1 are correct
10.	attempt to identify all projections and unprojections
11.	check that ALL Type I projections have the expected behaviour
*/


///////////////////////////////////////////////////////////////////////
//		Main intrinsics:  Steps 1 and 2
///////////////////////////////////////////////////////////////////////

forward
	compute_RR,
	sort_hilb_data,
	compile_preproj_data,
	compute_proj_data,
	build_k3s,
	force_projs,
	check_type1,
	reset_proj_types;

intrinsic CreateK3Data(g::RngIntElt) -> SeqEnum
{}
    return CreateK3Data(g,19);
end intrinsic;

intrinsic CreateK3Data(g::RngIntElt,r::RngIntElt) -> SeqEnum
{}
    require r in [0..19]: "Second argument r must be an integer 0..19";
	tt := Cputime();
	vprintf User1:
	    "Time %o: computing baskets with genus %o and rank at most %o\n",
		Cputime(tt),g,r;
    r +:= 1;	// because that's what K3Baskets expects.
    Bs,gs := K3Baskets(r);
    B := [ Bs[i] : i in [1..#Bs] | gs[i] le g ];
    require #B gt 0: "There are no baskets of the given rank and genus";
	vprintf User1: "Time %o: computing RR for %o baskets\n",Cputime(tt),#B;
    DD0 := compute_RR(g,B);
    DD := sort_hilb_data(DD0);
	bool := &and[ IsDefined(DD,i) : i in [1..#DD0] ];
	require bool: "insufficient precision in the Hilbert series";
	vprintf User1: "Time %o: compiling projection data\n",Cputime(tt);
    PP0 := compile_preproj_data(DD);
    PP,UU := compute_proj_data(DD,PP0);
	vprintf User1: "Time %o: making the K3 surfaces\n",Cputime(tt);
    KK := build_k3s(DD,PP,UU);
	vprintf User1: "Time %o: analysing projections\n",Cputime(tt);
    force_projs(~KK);
    check_type1(~KK);
    reset_proj_types(~KK);
	vprintf User1: "Time %o: building complete.\n",Cputime(tt);
    return KK;
end intrinsic;

intrinsic CreateK3Data(g::RngIntElt,B::SeqEnum) -> SeqEnum
{The K3 database (as a sequence) of K3 surfaces of genus g and singular
rank r or baskets B;  r = 19 if neither is given}
/* THINK: i should run through the B making sure that g is suitable genus.
?? an intrinsic MinimalGenus(basket) ?? */
	tt := Cputime();
	vprintf User1: "Time %o: computing RR for %o baskets\n",Cputime(tt),#B;
    DD0 := compute_RR(g,B);
    DD := sort_hilb_data(DD0);
	bool := &and[ IsDefined(DD,i) : i in [1..#DD0] ];
	require bool: "insufficient precision in the Hilbert series";
	vprintf User1: "Time %o: compiling projection data\n",Cputime(tt);
    PP0 := compile_preproj_data(DD);
    PP,UU := compute_proj_data(DD,PP0);
	vprintf User1: "Time %o: making the K3 surfaces\n",Cputime(tt);
    KK := build_k3s(DD,PP,UU);
	vprintf User1: "Time %o: analysing projections\n",Cputime(tt);
    force_projs(~KK);
    check_type1(~KK);
    reset_proj_types(~KK);
	vprintf User1: "Time %o: building complete.\n",Cputime(tt);
    return KK;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//			Step 3
// Given g,BB = [B1,...] compute DD0 = [ <g,B,d,h,H> ]
// compute_RR(g::RngIntElt,BB::SeqEnum) -> SeqEnum
///////////////////////////////////////////////////////////////////////

function compute_RR(g,BB)
    DD0 := [ ];
    S := PowerSeriesRing(Rationals(),21);
    for B in BB do
    	d := k3_degree(g,B);
	h := k3_hilbert_series(g,B);
	H := Coefficients(S!h);
	Append(~DD0,<g,B,Rationals()!d,h,H>);
    end for;
    return DD0;
end function;


///////////////////////////////////////////////////////////////////////
//			Step 4 and 5
// Return the sequence DD0 of Hilbert data sorted according to its
// Hilbert coefficients component
///////////////////////////////////////////////////////////////////////

function sort_hilb_data(DD0)
    HH := [ d[5] : d in DD0 ];
    Sort(~HH);
    DD := [ ];
    for n in [1..#DD0] do
	D := DD0[n];
	i := Index(HH,D[5]);
    	DD[i] := Append(D,i);
    end for;
    return DD;
end function;

///////////////////////////////////////////////////////////////////////
//			Step 6
// Compile the sequence of projection centres in the form [<p,d1,B1>]
// compile_preproj_data(DD::SeqEnum) -> SeqEnum
///////////////////////////////////////////////////////////////////////

forward proj_basket;
function compile_preproj_data(DD)
    PP0 := [ ];
    for D in DD do
	preproj := [];
	g := D[1];
    	B := D[2];
	Bred := SetToSequence(SequenceToSet(B));
	d := D[3];
	for p in Bred do
	    // compute the image basket
	    i := Index(B,p);
	    extra := proj_basket(p);
	    B1 := Sort(Remove(B,i) cat extra);
	    // compute the image degree
	    d1 := d - 1/&*[r,a,r-a] where r is p[1] where a is p[2];
	    centre := <p,d1,B1>;
	    Append(~preproj,centre);
	end for;
	Append(~PP0,preproj);
    end for;
    return PP0;
end function;

function proj_basket(p)
    r := p[1];
    a := p[2];
    if r eq 2 then
        return [];
    elif a eq 1 then
        return [ [r-1,1] ];
    else
        a1 := Minimum([ra, a - ra]) where ra is r mod a;
        a2 := Minimum([raa, (r-a) - raa]) where raa is r mod (r-a);
        return [ [a,a1], [r-a,a2] ];
    end if;
end function;

///////////////////////////////////////////////////////////////////////
//			Step 7
// Using PP0, compute all projections [<m,p>] from the terms of DD
// Recall that
//	DD = [ <g,B,d,h,H,n> ],		PP0 = [ [<p,d1,B1>] ]
// compute_proj_data(DD::SeqEnum,PP0::SeqEnum) -> SeqEnum
///////////////////////////////////////////////////////////////////////

function compute_proj_data(DD,PP0)
    PP := [ ];
    for n in [1..#PP0] do
	nthprojs := [ ];
	P := PP0[n];
	for pdata in P do
	    centre := pdata[1];
	    targdeg := pdata[2];
	    targbask := pdata[3];
	    for m in [1..n-1] do
		D := DD[m];
		// the test in the next line is done intelligently
		if D[3] eq targdeg and D[2] eq targbask then
		    Append(~nthprojs,<m,centre>);
		    continue pdata;
		end if;
	    end for;
	end for;
	Append(~PP,nthprojs);
    end for;
    // make unprojection data
    UU := [ [Parent(<1,[2,1]>) | ] : n in [1..#PP] ];
    for n in [1..#PP] do
	P := PP[n];
	for pr in P do
	    m := pr[1];
	    p := pr[2];
		// this is projection X_n -> X_m from centre p
	    temp := UU[m];
	    Append(~temp,<n,p>);
	    UU[m] := temp;
	end for;
    end for;
    return PP,UU;
end function;

///////////////////////////////////////////////////////////////////////
//			Step 8
// Turn the data so far into a sequence of K3 surfaces that contains all
// the information.
// Recall that
//	DD = [ <g,B,d,h,H,n> ],  PP0 = [ [<p,d1,B1>] ],  PP = [ [<m,p>] ]
///////////////////////////////////////////////////////////////////////

function build_k3s(DD,PP,UU)
    K3s := [];
    for i in [1..#DD] do
	D := DD[i];
	X := HackobjCreateRaw(GRK3);
	X`genus := D[1];
	X`rawbasket := D[2];
	X`degree := D[3];
	X`hilbert := D[4];
	X`coeffs := D[5];
	X`number := D[6];
	X`dim := 2;

	W := FindFirstGenerators(X`hilbert : Precision:=100);
	_,W := CheckBasket(Basket(X),W);
	Sort(~W);
	X`weights := W;
	X`firstw := W;
	X`num := HilbertNumerator(X`hilbert,W);

	projs := [];
	P := PP[i];
	for pr in P do
	    p := pr[2];
	    pp := Point(p[1],[p[2],p[1]-p[2]]);
	    Append(~projs, <pr[1],0,pp,0,0> );
		// for X->Y: <no.Y, codimY, centre on X, type of proj, subtype>
	end for;
	X`proj := projs;

	unprojs := [];
	U := UU[i];
	for pr in U do
	    p := pr[2];
	    pp := Point(p[1],[p[2],p[1]-p[2]]);
	    Append(~unprojs, <pr[1],0,pp,0> );
	end for;
	X`unproj := unprojs;

	// set AFR for codim 1 K3s
	// This next line could make bad mistakes, but it turns out to
	// be fine:  the point is that by this stage the only K3s that
	// appear to be in codim 1 are those that really are in codim 1.
	if #W eq 4 then
	    X`afr := get_AFR(W,D[2]);
	end if;

	Append(~K3s,X);
    end for;
    return K3s;
end function;


///////////////////////////////////////////////////////////////////////
//			Step 9
// Correct the weights using Type I, II_1, II_2 unprojections as necessary.
///////////////////////////////////////////////////////////////////////

forward change_W, is_typeII;
procedure force_projs(~KK)
    for n in [1..#KK] do
	X := KK[n];
	WX := Weights(X);
	projections := X`proj;
	if #projections eq 0 then
	    continue n;
	end if;
	// We run through projections pr : X -> Y and assume inductively that
	// the weights WY of Y are right.
	// We suppose that pr is be type 1 if the seq W = WY cat [Index(p)]
	// contains the current weights of X; in that case, set the
	// weights of X to be W.

	// try to find a type I projection on which to do the induction
	if Codimension(X) eq 1 then
	    continue;
	end if;
	for pr in projections do
	    p := pr[3];
	    WY := Weights(KK[pr[1]]);
	    W := Sort(WY cat [Index(p)]);
	    if is_subseq(Polarisation(p),WY) then
		if is_subseq(Weights(X),W) then
		    change_W(~X,W);
		else
		    // oh no!  WX already contains more than it should.
		    printf "Problem at number %o with weights %o\n",n,WX;
		end if;
		continue n;	// no need to try other projections
	    end if;
	end for;

	// try to find a type II projection instead
	for st in [1..5] do
	    if Codimension(X) le Minimum(3,(st+1)) then
		// we just wave small codim examples through at this point,
		// although early on we do give them a chance to be tested.
		continue n;
	    end if;
	    for pr in projections do
		p := pr[3];
		WY := Weights(KK[pr[1]]);
		bool,Wnew := is_typeII(WX,WY,Index(p),Polarisation(p),st);
		if bool then
		    change_W(~X,Wnew);
		    continue n;
		end if;
	    end for;
	end for;
    end for;
end procedure;

procedure change_W(~X,W)
    X`weights := W;
    X`num := HilbertNumerator(HilbertSeries(X),W);
end procedure;

function is_typeII(WX,W,r,P,k)
    // X -> Y is the projection from centre 1/r(P).
    // WX is Weights(X), W is Weights(Y).
    // assuming a,b not both in W, ie projection is not type I.
    // WX is used only to remove spurious integral closure weights
    // when Y is in codim 1.
    if #W eq 4 then
	W := [ w : w in W | w in WX ];
    end if;
    a := P[1];
    b := P[2];
    if a in W then
	W1 := Remove(W,Index(W,a));
	if (k+1)*b in W1 then
	    return true, Sort(W cat [ r+i*b : i in [0..k] ]);
	end if;
    elif b in W then
	W1 := Remove(W,Index(W,b));
	if (k+1)*a in W1 then
	    return true, Sort(W cat [r+i*a : i in [0..k] ]);
	end if;
    end if;
    return false,_;
end function;


///////////////////////////////////////////////////////////////////////
//			Step 10
// Identify all projections and unprojections
///////////////////////////////////////////////////////////////////////

/*
p = 1/r(a,r-a), W = weights of X (\owns p).
        Type, subtype   property
            1,0         [r,a,r-a] subseq W
            2,n         [r,a,r-a+n*r] subseq W for minimal n (or [r,a+n*r,r-a])
            4,0         neither a nor r-a in W.
Type 4 really needs a cluster as its subtype, so I ignore it for now.
Return zeros for any bad behaviour.
*/

forward find_type;
procedure reset_proj_types(~D)
    // identify the projections: p \in X -> Y
    D1 := [];
    for i in [1..#D] do
        X := D[i];
        P := Projections(X);
        newP := [ Parent(<1,2,Point(2,[1,1]),1,1>) | ];
        for pr in P do
	    p := pr[3];
	    Y := D[pr[1]];
            cod := Codimension(Y);
	    if Index(p) in Weights(X) then
		type,subtype := find_type(Weights(Y),Polarisation(p));
		Append(~newP,<pr[1],cod,p,type,subtype>);
	    else
		Append(~newP,<pr[1],cod,p,0,0>);
	    end if;
        end for;
        X`proj := newP;
        Append(~D1,X);
    end for;
    D := D1;

    // identify the unprojections: X <- Y \owns p
    D1 := [];
    for i in [1..#D] do
        X := D[i];
        U := Unprojections(X);
        newU := [ Parent(<1,2,Point(2,[1,1]),1,1>) | ];
        for pr in U do
	    p := pr[3];
	    Y := D[pr[1]];
            cod := Codimension(Y);
	    if Index(p) in Weights(Y) then
		type,subtype := find_type(Weights(X),Polarisation(p));
		Append(~newU,<pr[1],cod,p,type,subtype>);
	    else
		Append(~newU,<pr[1],cod,p,0,0>);
	    end if;
        end for;
        X`unproj := newU;
        Append(~D1,X);
    end for;
    D := D1;
end procedure;

function find_type(W,P);
    // W is weights of target of projection, P is polarisation of centre
    max := Maximum(W);
    a := P[1];
    b := P[2];
    if is_subseq([a,b],W) then
	return 1,0;
    elif a in W then
	W1 := Remove(W,Index(W,a));
	n := 1;
	repeat
	    if n*b in W1 then
		return 2,n-1;
	    end if;
	    n +:= 1;
	until n*b gt max;
	return 2,0;
    elif b in W then
	W1 := Remove(W,Index(W,b));
	n := 1;
	repeat
	    if n*a in W1 then
		return 2,n-1;
	    end if;
	    n +:= 1;
	until n*a gt max;
	return 2,0;
    else
	return 4,0;
    end if;
end function;


///////////////////////////////////////////////////////////////////////
//			Step 11
// Check all Type I projections
///////////////////////////////////////////////////////////////////////

procedure check_type1(~KK)
    n := 0;
    for X in KK do
	n +:= 1;
	if Codimension(X) eq 1 then
	    continue;
	end if;
	for pr in X`proj do
	    p := pr[3];
	    WX := Weights(X);
	    W := Sort(Weights(KK[pr[1]]) cat [Index(p)]);
	    if is_subseq(WX,W) and not WX eq W then
		print "Problem at number",n;
	    end if;
	end for;
    end for;
end procedure;

