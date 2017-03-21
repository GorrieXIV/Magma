freeze;

/////////////////////////////////////////////////////////////////////////
// hyperplane.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 27239 $
// $Date: 2010-06-09 17:18:51 +1000 (Wed, 09 Jun 2010) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for calculating with hyperplanes and half-spaces.
/////////////////////////////////////////////////////////////////////////
// By "hyperplane" we mean pair:
//    < normal, height >
// where 'normal' is a lattice point in Dual(L), and 'height' is
// an integer such that:
//    u in hyperplane iff u * normal = height.
//
// Note: We normalise the normal and the height so that they are both
// integral with gcd(normal,height) = 1 and height >= 0. Thus two hyperplanes
// are equal iff < normal1, height1 > = < normal2, height2 >.
//
// By "half-space" we mean a pair:
//    < hyperplane, orientation >
// where 'hyperplane' is a hyperplane, and 'orientation' is either +1
// or -1 and denotes which side of the hyperplane the half-space
// includes.
/////////////////////////////////////////////////////////////////////////

import "point.m": change_lattice_point_parent;

/////////////////////////////////////////////////////////////////////////
// Hyperplane functions
/////////////////////////////////////////////////////////////////////////

// Returns the normalised hyperplane given by the normal and height. If the
// sign of the normal remains unchanged, also returns +1, otherwise returns
// -1. (Note: The sign of the height is also changed, however if the height
// is zero then you may need to know this information if, for example, you
// are constructing a half-space.)
function to_hyperplane(normal,height)
    r:=LCM(Denominator(normal),Denominator(height));
    normal *:= r;
    height:= Integers() ! (height * r);
    vals:=Eltseq(normal);
    Append(~vals,height);
    r:=GCD(vals);
    normal /:= r;
    height /:= r;
    sign:=1;
    if height lt 0 then
        height:=-height;
        normal:=-normal;
        sign:=-1;
    elif height eq 0 and normal lt -normal then
        normal:=-normal;
        sign:=-1;
    end if;
    return <normal,height>,sign;
end function;

// If the set of points S spans a hyperplane H, returns true,H.
// If S does not span a hyperplane then returns false.
function is_hyperplane(S)
    L:=Universe(S);
    v:=Representative(S);
    K:=Kernel(Transpose(Matrix(Rationals(),[L | s - v : s in S])));
    if Dimension(K) ne 1 then return false,_; end if;
    normal:=LatticeVector(Dual(L),Eltseq(K.1));
    height:=normal * v;
    H:=to_hyperplane(normal,height);
    return true,H;
end function;

// Returns -1, 0, or +1 depending on which side of the hyperplane H the
// point v lies on.
function cmp_hyperplane_and_point(H,v)
    return Sign(v * H[1] - H[2]);
end function;

// Returns true iff H is a supporting hyperplane of conv(S). If true, also
// returns the orientation of H relative to S, and the indices of the points
// in S that lie on H.
function is_supporting_hyperplane(H,S)
    orientation:=0;
    indices:=[Integers()|];
    for i in [1..#S] do
        cmp:=cmp_hyperplane_and_point(H,S[i]);
        if cmp eq 0 then
            Append(~indices,i);
        else
            if orientation eq 0 then
                orientation:=cmp;
            elif orientation ne cmp then
                return false,_,_;
            end if;
        end if;
    end for;
    if #indices eq 0 then
        return false,_,_;
    else
        return true,orientation,indices;
    end if;
end function;

// Returns true iff the set of points of S indexed by I gives a defining
// hyperplane H of the convex hull of S. If true, also return H, the
// orientation of H relative to S, and the indices of the points in S that
// lie on H.
function defines_supporting_hyperplane(I,S)
    bool,H:=is_hyperplane([Universe(S) | S[i] : i in I]);
    if not bool then return false,_,_,_; end if;
    bool,orientation,indices:=is_supporting_hyperplane(H,S);
    if not bool then return false,_,_,_; end if;
    return true,H,orientation,indices;
end function;

// Returns true iff there exists a point in the set (or sequence) of points
// S not contained in the hyperplane H. If true, also returns such a point.
function exists_point_not_in_hyperplane(H,S)
    for v in S do
        if cmp_hyperplane_and_point(H,v) ne 0 then return true,v; end if;
    end for;
    return false,_;
end function;

// Returns the Gorenstein contribution for this hyperplane (i.e. the heigh)
function hyperplane_gorenstein_contribution(H)
    return H[2];
end function;

// Returns the image of the hyperplane under the mapping emb(u) + trans.
function hyperplane_image(H,emb,trans)
    normal:=H[1] @@ Dual(emb);
    height:=H[2] + normal * trans;
    return to_hyperplane(normal,height);
end function;

// Returns the image of the hyperplane under the pulback of emb(u) + trans.
function hyperplane_image_pullback(H,emb,trans)
    normal:=Dual(emb)(H[1]);
    height:=H[2] - H[1] * trans;
    return to_hyperplane(normal,height);
end function;

// Returns a new hyperplane given by the translation H + Q.
function hyperplane_translation(H,Q)
    return to_hyperplane(H[1],H[2] + H[1] * Q);
end function;

// Returns the hyperplane -H
function hyperplane_negation(H)
    return to_hyperplane(-H[1],H[2]);
end function;

// Returns a new hyperplane given by changing the ambient to L.
function hyperplane_change_ambient(H,L)
    H[1]:=change_lattice_point_parent(H[1],Dual(L));
    return H;
end function;

/////////////////////////////////////////////////////////////////////////
// Half-space functions
/////////////////////////////////////////////////////////////////////////

// Returns a the halfspace defined by the given normal, height, and orientation
function to_halfspace(normal,height,orientation)
    H,sign:=to_hyperplane(normal,height);
    return <H,orientation * sign>;
end function;

// If the set of points S spans a hyperplane H, and the point v does not lie
// in that hyperplane (and so fixes a halfspace) returns true,halfspace.
// If S does not span a hyperplane, or if v lies in the hyperplane spanned by S,
// then returns false.
function is_halfspace(S,v)
    bool,H:=is_hyperplane(S);
    if not bool then return false,_; end if;
    orientation:=cmp_hyperplane_and_point(H,v);
    if orientation eq 0 then return false,_; end if;
    return true,<H,orientation>;
end function;

// Returns true iff the hyperplane H together with the point v define a
// half-space. If so, also returns the half-space.
function hyperplane_to_halfspace(H,v)
    orientation:=cmp_hyperplane_and_point(H,v);
    if orientation eq 0 then return false,_; end if;
    return true,<H,orientation>;
end function;

// Returns true iff the halfspace is a supporting halfspace of conv(S). If
// true, also returns the indices of the points in S that lie on the halfspace.
function is_supporting_halfspace(halfspace,S)
    indices:=[Integers()|];
    for i in [1..#S] do
        cmp:=cmp_hyperplane_and_point(halfspace[1],S[i]);
        if cmp eq 0 then
            Append(~indices,i);
        elif cmp ne halfspace[2] then
            return false,_;
        end if;
    end for;
    if #indices eq 0 then
        return false,_;
    else
        return true,indices;
    end if;
end function;

// Returns true iff the point v is contained in the halfspace.
function point_in_halfspace(halfspace,v)
    orientation:=cmp_hyperplane_and_point(halfspace[1],v);
    return orientation eq 0 or orientation eq halfspace[2];
end function;

// Returns true iff the point v is strictly contained in the halfspace.
function point_strictly_in_halfspace(halfspace,v)
    return cmp_hyperplane_and_point(halfspace[1],v) eq halfspace[2];
end function;

// Returns true iff the points in S are all strictly contained in the halfspace.
function points_strictly_in_halfspace(halfspace,S)
    return &and[cmp_hyperplane_and_point(halfspace[1],v) eq halfspace[2] :
                                                                        v in S];
end function;

// Returns true iff the point v is on the boundary of the halfspace.
function point_on_halfspace_boundary(halfspace,v)
    return cmp_hyperplane_and_point(halfspace[1],v) eq 0;
end function;

// Returns true iff the points in S all lie on the boundary of the halfspace.
function points_on_halfspace_boundary(halfspace,S)
    return &and[cmp_hyperplane_and_point(halfspace[1],v) eq 0 : v in S];
end function;

// Returns the indices I of the points of S not contained in the halfspace.
function points_not_in_halfspace(halfspace,S)
    return [Integers() | i :
                         i in [1..#S] | not point_in_halfspace(halfspace,S[i])];
end function;

// Returns the Gorenstein contribution for this half-space (i.e. the heigh)
function halfspace_gorenstein_contribution(halfspace)
    return halfspace[1][2];
end function;

// Returns the image of the halfspace under the mapping emb(u) + trans.
function halfspace_image(halfspace,emb,trans)
    H:=halfspace[1];
    orientation:=halfspace[2];
    normal:=H[1] @@ Dual(emb);
    height:=H[2] + normal * trans;
    return to_halfspace(normal,height,orientation);
end function;

// Returns the image of the halfspace under the pullback of emb(u) + trans.
function halfspace_image_pullback(halfspace,emb,trans)
    H:=halfspace[1];
    orientation:=halfspace[2];
    normal:=Dual(emb)(H[1]);
    height:=H[2] - H[1] * trans;
    return to_halfspace(normal,height,orientation);
end function;

// Returns a new halfspace given by the translation by Q.
function halfspace_translation(halfspace,Q)
    H:=halfspace[1];
    height:=H[2] + H[1] * Q;
    return to_halfspace(H[1],height,halfspace[2]);
end function;

// Returns -halfspace
function halfspace_negation(halfspace)
    return to_halfspace(-halfspace[1][1],halfspace[1][2],halfspace[2]);
end function;

// Returns a new halfspace given by changing the ambient to L.
function halfspace_change_ambient(halfspace,L)
    halfspace[1][1]:=change_lattice_point_parent(halfspace[1][1],Dual(L));
    return halfspace;
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic IsSupportingHyperplane(v::TorLatElt,h::RngIntElt,S::SeqEnum[TorLatElt])
    -> BoolElt,RngIntElt
{}
    require not IsNull(S): "Illegal null sequence";
    require IsInDual(v,Universe(S)):
        "Argument 1 must lie in the dual to the universe of argument 3";
    return IsSupportingHyperplane(v,Rationals()!h,S);
end intrinsic;

intrinsic IsSupportingHyperplane(v::TorLatElt,h::FldRatElt,S::SeqEnum[TorLatElt])
    -> BoolElt,RngIntElt
{True iff the hyperplane defined by v * u = h is a supporting hyperplane of the sequence S. If so, also gives the sign o such the hyperplane is a support of S (i.e. o in \{-1,0,+1\} such that Sign(v * u - h) is either 0 or o for all u in S). If S is contained within the hyperplane, then o will be 0.}
    require not IsNull(S): "Illegal null sequence";
    require IsInDual(v,Universe(S)):
        "Argument 1 must lie in the dual to the universe of argument 3";
    bool,orientation:=is_supporting_hyperplane(to_hyperplane(v,h),S);
    if bool then
        return true,orientation;
    else
        return false,_;
    end if;
end intrinsic;

intrinsic IsHyperplane(S::SeqEnum[TorLatElt]) -> BoolElt,TorLatElt,RngIntElt
{True iff the sequence S of toric lattice points span a hyperplane. If so, then also gives a vector v in the dual lattice and an integer h such that v * u = h for all u in S. v and h are normailsed so that they are integral, have no common factors, and h is non-negative.}
    require not IsNull(S): "Illegal null sequence";
    bool,H:=is_hyperplane(S);
    if bool then
        return true,H[1],H[2];
    else
        return false,_,_;
    end if;
end intrinsic;

intrinsic Hyperplane(S::SeqEnum[TorLatElt]) -> TorLatElt,RngIntElt
{Assuming that the sequence S of toric lattice points span a hyperplane, gives a vector v in the dual lattice and an integer h such that v * u = h for all u in S. v and h are normailsed so that they are integral, have no common factors, and h is non-negative.}
    require not IsNull(S): "Illegal null sequence";
    bool,H:=is_hyperplane(S);
    require bool: "Sequence does not define a hyperplane";
    return H[1],H[2];
end intrinsic;
