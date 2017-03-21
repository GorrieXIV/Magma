freeze;
 
///////////////////////////////////////////////////////////////////////
//			K3 database
// GB Oct 2003
///////////////////////////////////////////////////////////////////////

import "../K3/k3.m": k3_hilbert_series, k3_degree;

/*
A K3 DATABASE D is a collection of K3 surfaces, each of which also
records those K3s that are projections from it, and those that project
to it.
*/

/*
K3Surface intrinsic in the 2.10 version:

Intrinsic 'K3Database'
Signatures:
    (<MonStgElt> t) -> SeqEnum
        The database of numerical K3 surfaces; the string t will be the variable
        name of Hilbert series.
    (<RngIntElt> n, <MonStgElt> t) -> SeqEnum
        The database of numerical K3 surfaces having codimension at most n; the 
        string t will be the variable name of Hilbert Series.
    () -> SeqEnum
        The database of numerical K3 surfaces.
    (<RngIntElt> n) -> SeqEnum
        The database of numerical K3 surfaces having codimension at most n.
*/


/////////////////////////////////////////////////////////////////////
//	Main raw version (incorporated in the kernel db return)
/////////////////////////////////////////////////////////////////////

function tup_to_k3(x)
// x is a tuple of data as returned by the k3 database (before
// it converts the data to a GRK3).
    X := HackobjCreateRaw(GRK3);
    X`dim := 2;
    X`number := x[1];
    X`coeffs := [1] cat x[2];
    X`weights := x[3];
    X`rawbasket := x[4];
    X`numinfo := x[5];
    X`noetherw := x[6];
    X`noethernseq := x[7];
    projinds := x[8];
    projdata := x[9];
    projs := [];
    for i in [1..#projinds] do
        pr := projdata[i];
        p := Point(r,[a,r-a]) where r is pr[2] where a is pr[3];
        Append(~projs, <projinds[i],pr[1],p,pr[4],pr[5]>);
    end for;
    PI := [ i : i in [1..#projinds] | projinds[i] lt X`number ];
    X`proj := [ projs[i] : i in PI ];
    X`unproj := [ projs[i] : i in [1..#projinds] | i notin PI ];
    return X;
end function;

intrinsic K3SurfaceFromRawData(x::Tup) -> GRK3
{Return a K3 surface with data from the database-style tuple of data x}
    return tup_to_k3(x);
end intrinsic;


/////////////////////////////////////////////////////////////////////
//		Trivial wrappers
/////////////////////////////////////////////////////////////////////

// THINK:  should this go?
intrinsic K3Database(t::MonStgElt) -> DB
{The database of K3 surfaces}
    R := PolynomialRing(Rationals()); t := R.1;
    return K3Database();
end intrinsic;


/////////////////////////////////////////////////////////////////////
//		Getting hold of K3 surfaces
/////////////////////////////////////////////////////////////////////

intrinsic K3Surface(D::DB,g::RngIntElt,i::RngIntElt) -> GRK3
{}
    require NumberOfK3Surfaces(D,[g+1]) ge i:
	"Second argument too large; maximum value",NumberOfK3Surfaces(D,[g+1]);
    x := K3SurfaceRawData(D,[g+1],i);
    return tup_to_k3(x);
end intrinsic;

intrinsic K3Surface(D::DB,g1::RngIntElt,g2::RngIntElt,i::RngIntElt) -> GRK3
{The i-th K3 surface in the K3 database D among those with
genus g >= -1, or genus g1 and 2-genus g2, or index suite Q = [g1+1,g2+1,...]}
    require NumberOfK3Surfaces(D,[g1+1]) ge i:
	"Second argument too large; maximum value",NumberOfK3Surfaces(D,[g1+1]);
    require NumberOfK3Surfaces(D,[g1+1,g2+1]) ge i:
	"Third argument too large; maximum value",NumberOfK3Surfaces(D,[g2+1]);
    x := K3SurfaceRawData(D,[g1+1,g2+1],i);
    return tup_to_k3(x);
end intrinsic;

intrinsic K3SurfaceWithCodimension(D::DB,c::RngIntElt,i::RngIntElt) -> GRK3
{The i-th K3 surface in the K3 database D among those with codimension c}
    if c eq 1 then
	require i in [1..95]: "There are only 95 K3 surfaces of codimension 1";
	Q := [ 4, 5, 18, 21, 22, 23, 24, 48, 49, 59, 60, 61, 62, 64, 65, 162,
	    167, 168, 169, 170, 184, 185, 186, 187, 188, 189, 191, 192, 194,
	    200, 420, 544, 551, 552, 553, 555, 556, 580, 581, 608, 609, 610,
	    611, 612, 614, 615, 617, 623, 627, 628, 630, 820, 1611, 1612,
	    4282, 4283, 4284, 4293, 4294, 4295, 4304, 4305, 4306, 4307, 4317,
	    4318, 4358, 4359, 4360, 4361, 4362, 4373, 4374, 4376, 4432, 4530,
	    4531, 4532, 4534, 4535, 4548, 4549, 4553, 4637, 5075, 5076,
	    10761, 10762, 10763, 10780, 10781, 10878, 17388, 17389, 24016 ];
	j := Q[i];
	x := K3SurfaceRawData(D,j);
	return tup_to_k3(x);
    elif c eq 2 then
	require i in [1..84]: "There are only 84 K3 surfaces of codimension 2";
	Q := [ 1, 9, 25, 50, 63, 66, 67, 68, 130, 171, 190, 193, 195, 196, 197, 199, 201, 202, 269, 421, 545, 554, 557, 560, 582, 589, 613, 616, 618, 619, 620, 622, 624, 629, 631, 632, 633, 639, 647, 703, 821, 1613, 1619, 1629, 2577, 4285, 4296, 4308, 4319, 4320, 4329, 4363, 4375, 4377, 4378, 4379, 4398, 4433, 4533, 4536, 4550, 4551, 4552, 4554, 4555, 4557, 4590, 4638, 4641, 4841, 5077, 5081, 5094, 5920, 10764, 10782, 10783, 10799, 10879, 11156, 17390, 17408, 24017, 24052 ];
	j := Q[i];
	x := K3SurfaceRawData(D,j);
	return tup_to_k3(x);
    elif c eq 3 then
	require i in [1..70]: "There are only 70 K3 surfaces of codimension 3";
	Q := [ 26, 42, 94, 131, 172, 198, 203, 219, 270, 422, 558, 566, 621, 625, 634, 636, 648, 652, 704, 706, 822, 825, 827, 840, 1614, 1630, 4286, 4297, 4309, 4321, 4330, 4364, 4380, 4381, 4399, 4434, 4436, 4445, 4537, 4556, 4558, 4569, 4591, 4639, 4642, 4644, 4647, 4677, 4842, 5078, 5082, 5095, 5102, 5186, 5921, 10765, 10784, 10800, 10880, 10882, 10897, 11157, 11702, 17391, 17409, 17506, 24018, 24023, 24053, 24073 ];
	j := Q[i];
	x := K3SurfaceRawData(D,j);
	return tup_to_k3(x);
    elif c eq 4 then
	require i in [1..142]: "There are only 142 K3 surfaces of codimension 4";
	Q := [ 12, 33, 43, 54, 69, 75, 95, 132, 163, 173, 174, 204, 205, 220, 221, 225, 228, 271, 273, 274, 277, 423, 426, 432, 546, 559, 561, 567, 583, 590, 626, 635, 637, 640, 649, 650, 651, 653, 654, 680, 705, 707, 710, 785, 823, 826, 828, 832, 836, 841, 844, 1130, 1615, 1620, 1631, 1632, 1637, 1648, 1714, 2578, 4287, 4298, 4310, 4322, 4331, 4332, 4339, 4365, 4382, 4390, 4400, 4401, 4409, 4435, 4437, 4446, 4448, 4483, 4538, 4559, 4570, 4571, 4592, 4593, 4603, 4640, 4643, 4645, 4646, 4648, 4658, 4678, 4680, 4681, 4763, 4843, 4846, 4856, 5079, 5083, 5096, 5097, 5099, 5103, 5104, 5107, 5145, 5187, 5194, 5403, 5922, 5927, 5939, 6976, 10766, 10785, 10801, 10802, 10816, 10881, 10883, 10898, 10900, 10983, 11158, 11161, 11175, 11703, 12547, 17392, 17410, 17411, 17427, 17507, 17784, 24019, 24024, 24034, 24054, 24058, 24074, 24086 ];
	j := Q[i];
	x := K3SurfaceRawData(D,j);
	return tup_to_k3(x);
    elif c eq 5 then
	require i in [1..163]: "There are only 163 K3 surfaces of codimension 5";
	Q := [ 8, 13, 19, 27, 55, 76, 77, 96, 97, 100, 133, 175, 206, 222, 223, 226, 227, 272, 275, 278, 279, 282, 424, 433, 568, 570, 591, 638, 655, 657, 681, 708, 711, 712, 724, 824, 829, 830, 831, 833, 834, 837, 842, 845, 847, 849, 856, 863, 923, 1131, 1616, 1633, 1638, 1649, 1650, 1715, 2579, 3301, 4288, 4299, 4311, 4323, 4333, 4340, 4366, 4383, 4391, 4402, 4410, 4438, 4447, 4449, 4450, 4451, 4464, 4484, 4539, 4560, 4572, 4573, 4594, 4604, 4649, 4659, 4660, 4679, 4682, 4683, 4684, 4701, 4703, 4764, 4844, 4847, 4857, 4861, 4909, 5080, 5084, 5098, 5100, 5105, 5108, 5118, 5146, 5188, 5190, 5191, 5195, 5197, 5202, 5246, 5404, 5408, 5705, 5923, 5928, 5940, 5950, 6030, 6977, 10767, 10786, 10803, 10817, 10884, 10899, 10901, 10902, 10903, 10928, 10984, 11159, 11162, 11176, 11180, 11264, 11704, 11708, 11721, 12548, 13603, 17393, 17412, 17428, 17508, 17510, 17525, 17785, 18330, 24020, 24025, 24026, 24029, 24035, 24044, 24055, 24059, 24065, 24075, 24078, 24087, 24093 ];
	j := Q[i];
	x := K3SurfaceRawData(D,j);
	return tup_to_k3(x);
    else
	count := 0;
	j := 0;
	repeat
	    j +:= 1;
	    x := K3SurfaceRawData(D,j);
	    if #x[3] eq c + 3 then
		count +:= 1;
	    end if;
	until count eq i;
	return tup_to_k3(x);
    end if;
end intrinsic;


/////////////////////////////////////////////////////////////////////
//		Searching for K3 with given weights
/////////////////////////////////////////////////////////////////////

forward k3_from_W;
intrinsic K3Surface(D::DB,W::SeqEnum) -> GRK3
{}
    // We will work out some genuses from the weights W.  Problem is
    // that we don't know the degrees of the equations so, e.g.
    // W = [1,1,1,2,4,5,6] would have genuses [3,7,13] if there were
    // no equations of degree 3, or [3,7,12] with 1 eqn of deg 3, etc.
    // So we guess that there are no small equations that hold between
    // the first 5 weights, and deduce some genuses from those.
    // If that fails, we have to try again using fewer weights.
    // But first we sort out the cases in which there is no ambiguity.
    //
    // NB there are c.6000 K3s with given g1 <= 3: this is the main thing
    // we want to avoid searching through:  fixing possible g2 is the
    // least we can do to avoid it; in notation below, ensure 'min > 0'.
    Sort(~W);
    if W[1] ge 3 then
	g3 := #[ w : w in W | w eq 3 ];
	g4 := #[ w : w in W | w eq 4 ];
	g5 := #[ w : w in W | w eq 5 ];
	Q := [0,0,g3,g4,g5];	// this is accurate so works if K3 exists
	bool,X := k3_from_W(D,Q,W);
	if bool then
	    return X;
	else
	    require false: "No K3 surface in the K3 database with weights",W;
	end if;
    elif W[1] eq 2 then
	// First attempt
	g2 := #[ w : w in W | w eq 2 ];		// this is accurate
	g3 := #[ w : w in W | w eq 3 ];		// this is accurate
	g4 := #[ w : w in W | w eq 4 ] + Binomial(g2+1,2);
			// this is an estimate, but is usually right
	g5 := #[ w : w in W | w eq 5 ] + g2*g3;
	n := 5;
	Q := [0,g2,g3,g4,g5];
	repeat
	    Q := Q[1..n];
	    bool,X := k3_from_W(D,Q,W);
	    if bool then
		return X;
	    end if;
	    n -:= 1;
	until n eq 2;
	require false: "No K3 surface in the K3 database with weights",W;
    else
	// make case divisions on the size of g1 now
	g1 := #[ w : w in W | w eq 1 ];		// this is accurate
	n2 := #[ w : w in W | w eq 2 ];
	g2 := Binomial(g1+1,2) + n2;
	n3 := #[ w : w in W | w eq 3 ];
	g3 := Binomial(g1+2,3) + g1*n2 + n3;
	g4 := Binomial(g1+3,4) + Binomial(g1+1,2)*n2 +
			Binomial(n2+1,2) + g1*n3 + #[ w : w in W | w eq 4 ];
	Q := [g1,g2,g3,g4];
	n := #Q;
	// if g1 = 1,2 then g2 is accurate so don't do Q = [g1] check.
	if g1 eq 1 then
	    // indeed, only need to check once we get at least 3 monos in 1 deg
	    if Q[1..2] eq [1,1] then	// i.e. W = [1, >=3, ...]
		// no irredble eqns in deg <= 4 so Q is accurate
		min := 3;
	    else
		// no irredble eqns in deg <= 3 so Q is accurate up to 3rd term
		min := 2;
	    end if;
	elif g1 eq 2 then
	    // g3 is an upper bound for the actual value (which could be g3-1)
	    // Do this case separately.
	    Q := [g1,g2,g3];
	    bool,X := k3_from_W(D,Q,W);
	    if bool then
		return X;
	    end if;
	    Q := [g1,g2,g3-1];
	    bool,X := k3_from_W(D,Q,W);
	    if bool then
		return X;
	    end if;
	    require false: "No K3 surface in the K3 database with weights",W;
	elif g1 eq 3 then
	    // g2 is an upper bound for the actual value (which could be g2-1)
	    // Do this case separately.
	    Q := [g1,g2];
	    bool,X := k3_from_W(D,Q,W);
	    if bool then
		return X;
	    end if;
	    Q := [g1,g2-1];
	    bool,X := k3_from_W(D,Q,W);
	    if bool then
		return X;
	    end if;
	    require false: "No K3 surface in the K3 database with weights",W;
	else
	    min := 0;
	end if;
	repeat
	    Q := Q[1..n];
	    bool,X := k3_from_W(D,Q,W);
	    if bool then
		return X;
	    end if;
	    n -:= 1;
	until n eq min;
	require false: "No K3 surface in the K3 database with weights",W;
    end if;
end intrinsic;

function k3_from_W(D,Q,W);
    for i in [1..NumberOfK3Surfaces(D,Q)] do
	X := K3Surface(D,Q,i);
	if Weights(X) eq W then
	    return true,X;
	end if;
    end for;
    return false,_;
end function;


/////////////////////////////////////////////////////////////////////
//		Searching for K3 with given basket
/////////////////////////////////////////////////////////////////////

intrinsic K3Surface(D::DB,g::RngIntElt,B::GRBskt) -> GRK3
{}
    return K3Surface(D,g,
	[ Parent([2,1]) | [Index(p),Polarisation(p)[1]] : p in Points(B) ]);
end intrinsic;

// This is an absurd, unprincipled, disorganised search; could do better.
forward k3_from_gB;
intrinsic K3Surface(D::DB,g::RngIntElt,B::SeqEnum) -> GRK3
{The K3 surface in the K3 database D either with weights W, or with
genus g >= -1 and basket of singularities B (as a basket type or in
raw sequence format)}
    // Essentially we simply search through K3s with genus g for the
    // one with this basket, but we can use the hilbert series to speed up
    // this search.

    // check the genus
    require g ge -1: "Second argument, genus g, must be >= -1";

    // tidy up the basket, just to be safe.
    // this requirement is satisfied for free if B came from a GRBskt type.
    if #B eq 0 then
	B := [ Parent([Integers()|2,1]) | ];
    else
	require (Type(B[1]) eq SeqEnum and &and[#b eq 2: b in B]
	    and &and[IsCoercible(Integers(),b) : b in &cat B]):
		"Third argument, basket B, must be a sequence of " *
			    "length 2 sequences of integers";
	ChangeUniverse(~B,Parent([Integers()|2,1]));
	Sort(~B);
    end if;
    require &+ [ b[1]-1 : b in B ] le 19: "The singular rank of the given "
			* "basket must be <= 19";

    // check the degree:  if <= 0 then certainly no K3.
    require k3_degree(g,B) gt 0:
	"Given <genus,basket> data has negative degree";

    // calculate some weights to estimate higher genuses, pinning down
    // the search a bit.
    h := k3_hilbert_series(g,B);
    W := FindFirstGenerators(h);
    N := #W;

    // let the search begin.
    if #W eq g then	// W = [1,1,...(g times)]: we have to search naively
	if #B eq 0 then
	    // do empty basket case separately
	    for i in [1..NumberOfK3Surfaces(D,[g+1])] do
		X := K3Surface(D,g,i);
		if #RawBasket(X) eq 0 then
		    return X;
		end if;
	    end for;
	    require false:
		"No K3 surface in the K3 database of given genus and basket";
	else

	    bool,X := k3_from_gB(D,[g+1],B);
	    if bool then
		return X;
	    else
		require false:
		"No K3 surface in the K3 database of given genus and basket";
	    end if;
	end if;
    else
	if g eq -1 then
	    g1 := 0;		// this is accurate
	    w1 := W[1];
	    Nw1 := #[ w : w in W | w eq w1 ];
	    if w1 eq 2 then
		if Nw1 eq N then
		    // no choice but to search
		    g2 := Nw1;
		    repeat
			bool,X := k3_from_gB(D,[g1,g2],B);
			if bool then
			    return X;
			else
			    g2 +:= 1;
			end if;
		    until NumberOfK3Surfaces(D,[g1,g2]) eq 0;
		    require false: "No K3 surface in the K3 database "
				* "of given genus and basket";
		else
		    g2 := Nw1;		// this is accurate
		    w2 := W[Nw1+1];
		    Nw2 := #[ w : w in W | w eq w2 ];
		    // now i simply search:  could go deeper into W though
		    if w2 eq 3 then
			g3 := Nw2;
		    else
			g3 := 0;
		    end if;
		    repeat
			bool,X := k3_from_gB(D,[g1,g2,g3],B);
			if bool then
			    return X;
			else
			    g3 +:= 1;
			end if;
		    until NumberOfK3Surfaces(D,[g1,g2,g3]) eq 0;
		    require false: "No K3 surface in the K3 database "
				* "of given genus and basket";
		end if;
	    else
		g2 := 0;
		g3 := #[ w : w in W | w eq 3 ];
		repeat
		    bool,X := k3_from_gB(D,[g1,g2,g3],B);
		    if bool then
			return X;
		    else
			g3 +:= 1;
		    end if;
		until NumberOfK3Surfaces(D,[g1,g2,g3]) eq 0;
		require false: "No K3 surface in the K3 database "
				* "of given genus and basket";
	    end if;
	else	// g >= 0
	    g1 := g+1;		// this is accurate, and i know
				// that W contains more than just 1s.
	    w2 := W[g1+1];
	    Nw2 := #[ w : w in W | w eq w2 ];
	    if g1 + Nw2 eq N then
		// no choice but to search with what i've got
		if w2 eq 2 then
		    g2 := Binomial(g1+1,2)+Nw2;
		    repeat
			bool,X := k3_from_gB(D,[g1,g2],B);
			if bool then
			    return X;
			else
			    g2 +:= 1;
			end if;
		    until NumberOfK3Surfaces(D,[g1,g2]) eq 0;
		    require false: "No K3 surface in the K3 database "
			    * "of given genus and basket";
		elif w2 eq 3 then
		    g2 := Binomial(g1+1,2);
		    g3 := Binomial(g1+2,3) + Nw2;
		else
		    g2 := Binomial(g1+1,2);
		    g3 := Binomial(g1+2,3);
		end if;
		repeat
		    bool,X := k3_from_gB(D,[g1,g2,g3],B);
		    if bool then
			return X;
		    else
			g3 +:= 1;
		    end if;
		until NumberOfK3Surfaces(D,[g1,g2,g3]) eq 0;
		require false: "No K3 surface in the K3 database "
			    * "of given genus and basket";
	    else
		if w2 eq 2 then
		    g2 := Binomial(g1+1,2)+Nw2;	// this is accurate
		    w3 := W[g1+Nw2+1];
		    Nw3 := #[ w : w in W | w eq w3 ];
		    // now i simply search:  could go deeper into W though
		    if w3 eq 3 then
			g3 := Binomial(g1+2,3) + g1*Nw2 + Nw3;
		    else
			g3 := Binomial(g1+2,3) + g1*Nw2;
		    end if;
		    repeat
			bool,X := k3_from_gB(D,[g1,g2,g3],B);
			if bool then
			    return X;
			else
			    g3 +:= 1;
			end if;
		    until NumberOfK3Surfaces(D,[g1,g2,g3]) eq 0;
		    require false: "No K3 surface in the K3 database "
				* "of given genus and basket";
		elif w2 eq 3 then
		    g2 := Binomial(g1+1,2);
		    g3 := Binomial(g1+2,3) + Nw2;	// this is accurate
		else
		    g2 := Binomial(g1+1,2);
		    g3 := Binomial(g1+2,3);	// this is accurate
		end if;
		bool,X := k3_from_gB(D,[g1,g2,g3],B);
		if bool then
		    return X;
		else
		    require false: "No K3 surface in the K3 database "
			    * "of given genus and basket";
		end if;
	    end if;
	end if;
    end if;
end intrinsic;

function k3_from_gB(D,Q,B)
    for i in [1..NumberOfK3Surfaces(D,Q)] do
	X := K3Surface(D,Q,i);
	BX := RawBasket(X);
	ChangeUniverse(~BX,Parent([Integers()|2,1]));
	if BX eq B then
	    return true,X;
	end if;
    end for;
    return false,_;
end function;


/////////////////////////////////////////////////////////////////////
//			Other tests
/////////////////////////////////////////////////////////////////////

intrinsic Codimension(D::DB,i::RngIntElt) -> GRK3
{The codimension of the i-th K3 surface in the K3 database D}
    bool,g,j := K3Surface(D,i);
    require bool: "Second argument i must be >= 1 and <= ",#D;
    x := K3SurfaceRawData(D,[g+1],j);
    return #x[3] - 3;
end intrinsic;

intrinsic Number(D::DB,X::GRK3) -> RngIntElt,GRK3
{The number of the K3 surface in the K3 database D that has the same
Hilbert series as X, or zero if X is not in D; the matching K3 surface
is a second return value}
    h := HilbertSeries(X);
    Q := InitialCoefficients(X)[2..6];
    for i in [1..NumberOfK3Surfaces(D,Q)] do
	Y := K3Surface(D,Q,i);
	if h eq HilbertSeries(Y) then
	    return Number(Y),Y;
	end if;
    end for;
    return 0,_;
end intrinsic;

intrinsic Index(D::DB,X::GRK3) -> RngIntElt,GRK3
{The index of the K3 surface in the K3 database D that has the same
Hilbert series as X, or zero if X is not in D; the matching K3 surface
is a second return value}
    N,Y := Number(D,X);
    if N ne 0 then
	// convert the number of Y into its index in D
	for j in [0..Genus(Y)] do
	    N +:= NumberOfK3Surfaces(D,[j]);
	end for;
	return N,Y;
    else
	return 0,_;
    end if;
end intrinsic;


/////////////////////////////////////////////////////////////////////
//		Information attributes
/////////////////////////////////////////////////////////////////////

intrinsic NumberOfK3Surfaces(D::DB,g::RngIntElt) -> RngIntElt
{The number of K3 surfaces in the K3 database D of genus g >= -1}
    return NumberOfK3Surfaces(D,[g+1]);
end intrinsic;

intrinsic GenusDistribution(D::DB) -> SeqEnum
{A sequence recording the number of K3 surfaces of genus g = -1, 0, 1,...}
    gd := [Integers()|]; 
    N := #D;
    g := 0;
    repeat
	Append(~gd,NumberOfK3Surfaces(D,[g]));
	g +:= 1;
    until &+ gd eq N;
    return gd;
end intrinsic;

intrinsic SingularRankPerCodimension(D::DB,g::RngIntElt) -> Mtrx
{}
    rows := [ Parent([Integers()|]) | ]; 
    Ng := NumberOfK3Surfaces(D,[g+1]);
    require Ng ge 1: "There are no K3 surfaces in database of the given genus";
    for i in [1..Ng] do
	X := K3Surface(D,[g+1],i);
	sr := SingularRank(X) + 1;	// to account for empty baskets
	cod := Codimension(X);
	if not IsDefined(rows,cod) then
	    rows[cod] := [ ];
	    rows[cod][sr] := 1;
	elif not IsDefined(rows[cod],sr) then
	    rows[cod][sr] := 1;
	else
	    rows[cod][sr] +:= 1;
	end if;
    end for;
    length := Maximum([ #r : r in rows ]);
    for j in [1..#rows] do
	if not IsDefined(rows,j) then
	    rows[j] := [Integers()|];
	end if;
	r := rows[j];
	for i in [1..length] do
	    if not IsDefined(r,i) then
		r[i] := 0;
	    end if;
	end for;
	rows[j] := r;
    end for;
    return Matrix(rows);
end intrinsic;


