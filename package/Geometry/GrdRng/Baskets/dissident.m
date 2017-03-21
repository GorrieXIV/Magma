freeze;
 
///////////////////////////////////////////////////////////////////////
//              Finding suitable dissident points
///////////////////////////////////////////////////////////////////////

// The intrinsics here use only dimension, transverse index and
// index of a curve.

///////////////////////////////////////////////////////////////////////
//	Points that must appear as dissidents on a particular curve
///////////////////////////////////////////////////////////////////////

forward lcmis;
intrinsic CanonicalDissidentPoints(C::GRCrvS) -> SeqEnum
{A sequence of sequences of points, each of which minimally accounts for
the index of C (although may need further curves to make sense)}
    require Dimension(C) eq 3:
        "Singular curve argument must be a 3-dimensional";
    r := TransverseIndex(C);
    t := Index(C);
    result := [ Parent([PowerStructure(GRPtS) | ]) | ];
    // We need to make points 1/s*r(r,a,b) with r + a + b mod s*t = 0,
    // r,a,b pairwise coprime and so that the LCM of the s's is t.
    inds_of_p := lcmis(t);
    // we need to make the possible polarisations now for each index.
    inds := SetToSequence(&join inds_of_p);
    avail_sings := [ Parent([PowerStructure(GRPtS) | ]) | ];
    for s in inds do
        S := [PowerStructure(GRPtS) | ];
        sr := s * r;
        // st := s * t;
        for a in [1..Round((sr-r)/2)] do
            if GCD([a,r]) eq 1 then
                Append(~S,Point(sr,[r,a,sr-r-a]));
            end if;
        end for;
        Append(~avail_sings,S);
    end for;
    // now we make combinations of singularities as indicated by inds_of_p
    for I in inds_of_p do
        I1 := SetToSequence(I);
        // there must be a singularity for each index we want to use
        sizes := [ #avail_sings[Index(inds,i)] : i in I1 ];
        if &*sizes eq 0 then
            continue I;
        end if;
        basket := [PowerStructure(GRPtS) | ];
        for J in CartesianProduct([Integers(n) : n in sizes]) do
            JZ := [ (Integers()!j)+1 : j in J ];
            basket := [ avail_sings[Index(inds,I1[k])][JZ[k]] : k in [1..#I1] ];
            Append(~result,basket);
        end for;
    end for;
    return result;
end intrinsic;

intrinsic SimpleCanonicalDissidentPoints(C::GRCrvS) -> SeqEnum
{A sequence of sequences of points, each of which minimally accounts for
the index of C and which does not allow further curves to meet C}
    require Dimension(C) eq 3:
        "Singular curve argument must be a 3-dimensional";
    r := TransverseIndex(C);
    t := Index(C);
    result := [ Parent([PowerStructure(GRPtS) | ]) | ];
    // We need to make points 1/s*r(r,a,b) with r + a + b mod s*t = 0,
    // r,a,b pairwise coprime and so that the LCM of the s's is t.
    inds_of_p := lcmis(t);
    // we need to make the possible polarisations now for each index.
    inds := SetToSequence(&join inds_of_p);
    avail_sings := [ Parent([PowerStructure(GRPtS) | ]) | ];
    for s in inds do
        S := [PowerStructure(GRPtS) | ];
        sr := s * r;
        // st := s * t;
        for a in [1..Round((sr-r)/2)] do
            if GCD([a,r]) eq 1 and GCD([a,sr]) eq 1 then
                Append(~S,Point(sr,[r,a,sr-r-a]));
            end if;
        end for;
        Append(~avail_sings,S);
    end for;
    // now we make combinations of singularities as indicated by inds_of_p
    for I in inds_of_p do
        I1 := SetToSequence(I);
        // there must be a singularity for each index we want to use
        sizes := [ #avail_sings[Index(inds,i)] : i in I1 ];
        if &*sizes eq 0 then
            continue I;
        end if;
        basket := [PowerStructure(GRPtS) | ];
        for J in CartesianProduct([Integers(n) : n in sizes]) do
            JZ := [ (Integers()!j)+1 : j in J ];
            basket := [ avail_sings[Index(inds,I1[k])][JZ[k]] : k in [1..#I1] ];
            Append(~result,basket);
        end for;
    end for;
    return result;
end intrinsic;

// This would be terrible if t was large and divisible, but it never
// is so this is fine.
function lcmis(t)
    results := [ {t} ];
    n := #Factorization(t);
    poss := { a : a in [2..t-1] | IsDivisibleBy(t,a) };
    k := 1;
    repeat
        more := [ Q : Q in Subsets(poss,k) | LCM(Q) eq t and
                        &and[ not T subset Q : T in results ]  ];
        results cat:= more;
        k +:= 1;
    until k gt n;
    return results;
end function;

///////////////////////////////////////////////////////////////////////
//	Points that may appear as dissidents on a particular curve
///////////////////////////////////////////////////////////////////////

forward make_points;
intrinsic PossibleCanonicalDissidentPoints(C::GRCrvS) -> SeqEnum
{A sequence of points, each of may appear on C as a dissident point}
    require Dimension(C) eq 3:
        "Singular curve argument must be a 3-dimensional";
    return make_points(C,true);
end intrinsic;

intrinsic PossibleSimpleCanonicalDissidentPoints(C::GRCrvS) -> SeqEnum
{A sequence of points, each of may appear on C as a dissident point
but which is not at the intersection of C with another curve}
    require Dimension(C) eq 3:
        "Singular curve argument must be a 3-dimensional";
    return make_points(C,false);
end intrinsic;

// if bool is false then only make isolated points.
function make_points(C,bool)
    r := TransverseIndex(C);
    t := Index(C);
    // get hold of the possible indices of points p on C.
    factors := [ n : n in [1..t] | IsDivisibleBy(t,n) ];
    inds := [ r*n : n in factors ];
    // build singularities for each index.
    sings := [ PowerStructure(GRPtS) | ];
    for s in inds do
	for a in [1..Round((s-r)/2)] do
	    // a,r must be coprime otherwise 3-fold has 2-diml singular locus.
	    // if a,s also coprime then no other curves pass through this point.
	    if GCD(a,r) eq 1 and (bool or GCD(s,a) eq 1) then
		Append(~sings,Point(s,[r,a,s-r-a]));
	    end if;
	end for;
    end for;
    return sings;
end function;

