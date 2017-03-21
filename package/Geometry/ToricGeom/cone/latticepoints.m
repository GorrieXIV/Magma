freeze;

////////////////////////////////////////////////////////////////////////
// latticepoints.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 36857 $
// $Date: 2012-01-09 07:02:03 +1100 (Mon, 09 Jan 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for calculating lattice points in cones.
/////////////////////////////////////////////////////////////////////////

import "../lattice/point.m": row_matrix_to_lattice_vector;
import "../polyhedron/attributes.m": integral_representative;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns all possible sums of "total" points from "pts" (allowing repeats).
procedure distribute_sum_over_recurse(vals,nums,perm,n,pts,~sums)
    if #vals eq 0 then
        P:=Matrix(1,n,[Integers() | c - 1 : c in perm]) * pts;
        Include(~sums,P);
    else
        for i in [1..#vals] do
            if nums[i] eq 1 then
                newvals:=Remove(vals,i);
                newnums:=Remove(nums,i);
            else
                newvals:=vals;
                newnums:=nums;
                newnums[i] -:= 1;
            end if;
            $$(newvals,newnums,Append(perm,vals[i]),n,pts,~sums);
        end for;
    end if;
end procedure;

function distribute_sum_over(pts,total)
    sums:={};
    n:=NumberOfRows(pts);
    for partition in Partitions(total + n,n) do
        vals:=SetToSequence(SequenceToSet(partition));
        nums:=[Integers() | #[Integers() | 1 : s in partition | s eq val] :
                                                                   val in vals];
        distribute_sum_over_recurse(vals,nums,[Integers()|],n,pts,~sums);
    end for;
    return sums;
end function;

// Given a knapsack result, reconstructs all possible lattice points.
procedure rebuild_point(~results,solution,points)
    // We build up a sequence of partial sums
    partsum:={};
    for height in Seqset(solution) do
        // Create the possibilities
        subsum:=distribute_sum_over(points[height[1]],height[2]);
        // Add them to the partial sums we're building
        if #partsum eq 0 then
            partsum:=subsum;
        else
            partsum:={A + B : A in partsum, B in subsum};
        end if;
    end for;
    // Finally merge the results
    results join:= partsum;
end procedure;

// Performs a knapsack on the hights, allowing for repeats. The results are
// stored as a pair [n,repeats], where, for example, [2,4] means than 2 should
// be repeated 4 times. Each result is passed to rebuild_point for conversion
// into the corresponding lattice point(s). The set of all constructable points
// are returned.
procedure heights_knapsack_repeats_recurse(~results,working,Q,h,points)
    Q:=[Integers() | c : c in Q | c le h];
    while #Q gt 1 do
        b:=Q[1];
        Remove(~Q,1);
        num:=0;
        for i in [1..h div b] do
            newh:=h - i * b;
            if newh eq 0 then
                rebuild_point(~results,Append(working,[b,i]),points);
            elif #Q gt 1 or IsDivisibleBy(newh,Q[1]) then
                $$(~results,Append(working,[b,i]),Q,newh,points);
            end if;
        end for;
    end while;
    if #Q eq 1 and IsDivisibleBy(h,Q[1]) then
        rebuild_point(~results,Append(working,[Q[1],h div Q[1]]),points);
    end if;
end procedure;

function heights_knapsack_repeats(L,points,h)
    results:={};
    Q:=Reverse(Sort(Setseq(Keys(points))));
    if #Q eq 0 then
        return results;
    end if;
    // Perform the knapsack
    heights_knapsack_repeats_recurse(~results,[PowerSequence(Integers())|],
                                                                    Q,h,points);
    // Finally we need to cast the results back into the toric lattice
    return {L | row_matrix_to_lattice_vector(L,A) : A in results};
end function;

// Returns the set of lattice points of C contained in the hyperplane H at
// height h. Assumes that the intersection is compact.
function points_in_hyperplane(C,H,h)
    // Reduce H to a primitive lattice point and scale h accordingly
    if not IsPrimitive(H) then
        den:=Denominator(H);
        H *:= den;
        h *:= den;
        num:=GCD(Eltseq(H));
        if num ne 1 then
            H /:= num;
            h /:= num;
        end if;
    end if;
    // If h isn't integral then there's nothing to do
    bool,h:=IsCoercible(Integers(),h);
    if not bool then return {Ambient(C)|}; end if;
    // Deal with the special 1-dimensional case (since here we can allow rays
    // either side of H and still have a compact intersection)
    if Dimension(C) eq 1 then
        gen:=Representative(Exclude(Seqset(RGenerators(C)),Zero(Ambient(C))));
        point:=(h / (gen * H)) * gen;
        return IsIntegral(point) select {Ambient(C) | point} else {Ambient(C)|};
    end if;
    // Orient the hyperplane so that the height is in the positive direction
    if h lt 0 then
        h:=-h;
        H:=-H;
    end if;
    // Calculate the height data
    points:=AssociativeArray(Integers());
    for gen in ZGenerators(C) do
        height:=Integers() ! (gen * H);
        if IsDefined(points,height) then
            Append(~points[height],gen);
        else
            points[height]:=[Ambient(C) | gen];
        end if;
    end for;
    // Convert the sequences of points into matrices
    mats:=AssociativeArray(Integers());
    for height in Keys(points) do
        mats[height]:=Matrix(Integers(),points[height]);
    end for;
    // Reconstruct the sums from the knapsack solutions on heights
    return heights_knapsack_repeats(Ambient(C),mats,h);
end function;

/////////////////////////////////////////////////////////////////////////
// Point Membership
/////////////////////////////////////////////////////////////////////////

intrinsic 'in'(Q::TorLatElt,C::TorCon) -> BoolElt
{True iff the point Q lies in the interior of the cone C}
    require Parent(Q) cmpeq Ambient(C):
        "Argument 1 must live in the ambient of argument 2";
    // This is faster if the answer is false and the inequality that fails is
    // somewhere in the middle or begining of the sequence
    return &and[Q * ineq ge 0 : ineq in Inequalities(C)];
    /*
    // This version works faster if the answer is positive or in the
    // pessimistic case that the inequality that fails is at the end of the
    // sequence. Generally it is beter to use the code above. 
    ineqs:=ChangeRing(MatrixOfInequalities(C), Rationals());
    QQ:=ChangeRing(Transpose(Matrix([Q])), Rationals());
    res:=ineqs*QQ;
    return &and[res[i][1] ge 0 : i in [1..NumberOfRows(res)]];
     */
end intrinsic;

intrinsic IsInInterior(Q::TorLatElt,C::TorCon) -> BoolElt
{True iff the point Q lies strictly in the relative interior of the cone C}
    require Parent(Q) cmpeq Ambient(C):
        "Argument 1 must live in the ambient of argument 2";
    if Q in C then
        // Move to the sublattice in which C is of maximal dimension...
        C,emb:=ConeInSublattice(C);
        Q:=Q @@ emb;
        // ...and now ask the question
        return &and[Q * ineq gt 0 : ineq in Inequalities(C)];
    end if;
    return false;
end intrinsic;

intrinsic IsOnBoundary(Q::TorLatElt,C::TorCon) -> BoolElt
{True iff the point Q lies on the relative boundary of the cone C}
    require Parent(Q) cmpeq Ambient(C):
        "Argument 1 must live in the ambient of argument 2";
    if Q in C then
        // Move to the sublattice in which C is of maximal dimension
        C,emb:=ConeInSublattice(C);
        Q:=Q @@ emb;
        // and now ask the question
        boundary:=false;
        for ineq in Inequalities(C) do
            cmp:=Q * ineq;
            if cmp eq 0 then
                boundary:=true;
            elif cmp lt 0 then
                return false;
            end if;
        end for;
        return boundary;
    end if;
    return false;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Point Listing Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic Points(C::TorCon,H::TorLatElt,h::RngIntElt) -> SetEnum[TorLatElt]
{}
    // Sanity check on the hyperplane
    require IsInDual(H,Ambient(C)):
        "Argument 2 must lie in the dual to the ambient of argument 1";
    gens:=Exclude(Seqset(RGenerators(C)),Zero(Ambient(C)));
    if Dimension(C) eq 1 then
        require h ne 0 or &and[gen * H ne 0 : gen in gens]:
            "The intersection of the hyperplane and cone must be compact";
    else
        sgns:={Integers() | Sign(gen * H) : gen in gens};
        if 0 in sgns then
            Exclude(~sgns,0);
            require h ne 0 and (#sgns eq 0 or
                (#sgns eq 1 and Representative(sgns) ne Sign(h))):
                "The intersection of the hyperplane and cone must be compact";
        else
            require #sgns ne 2:
                "The intersection of the hyperplane and cone must be compact";
        end if;
    end if;
    // Is there anything to do?
    if h eq 0 then return {Ambient(C) | Zero(Ambient(C))}; end if;
    if assigned sgns then
        if not Sign(h) in sgns then return {Ambient(C)|}; end if;
    else
        sgn:=Sign(h);
        if &and[Sign(gen * H) ne sgn : gen in gens] then
            return {Ambient(C)|};
        end if;
    end if;
    // Return the result
    return points_in_hyperplane(C,H,Rationals() ! h);
end intrinsic;

intrinsic Points(C::TorCon,H::TorLatElt,h::FldRatElt) -> SetEnum[TorLatElt]
{The integral lattice points in the cone C contained in the hyperplane slice H at height h. The intersection of H with C must be compact.}
    // Sanity check on the hyperplane
    require IsInDual(H,Ambient(C)):
        "Argument 2 must lie in the dual to the ambient of argument 1";
    gens:=Exclude(Seqset(RGenerators(C)),Zero(Ambient(C)));
    if Dimension(C) eq 1 then
        require h ne 0 or &and[gen * H ne 0 : gen in gens]:
            "The intersection of the hyperplane and cone must be compact";
    else
        sgns:={Integers() | Sign(gen * H) : gen in gens};
        if 0 in sgns then
            Exclude(~sgns,0);
            require h ne 0 and (#sgns eq 0 or
                (#sgns eq 1 and Representative(sgns) ne Sign(h))):
                "The intersection of the hyperplane and cone must be compact";
        else
            require #sgns ne 2:
                "The intersection of the hyperplane and cone must be compact";
        end if;
    end if;
    // Is there anything to do?
    if h eq 0 then return {Ambient(C) | Zero(Ambient(C))}; end if;
    if assigned sgns then
        if not Sign(h) in sgns then return {Ambient(C)|}; end if;
    else
        sgn:=Sign(h);
        if &and[Sign(gen * H) ne sgn : gen in gens] then
            return {Ambient(C)|};
        end if;
    end if;
    // Return the result
    return points_in_hyperplane(C,H,h);
end intrinsic;

intrinsic BoxElements(C::TorCon) -> SetEnum[SeqEnum[FldRatElt]]
{For a simplicial cone C, gives the coefficients of the points in the fundamental domain generated by the rays of C, with respect to the rays}
    // Sanity check
    require IsSimplicial(C): "The cone must be simplicial";
    // If necessary move to the maximum dimensional cone
    C:=ConeInSublattice(C);
    // Create the quotient group generated by the rays
    pts:=[PowerSequence(Integers()) | Eltseq(v) : v in Rays(C)];
    d:=Dimension(C);
    G:=FreeAbelianGroup(d);
    gens:=[&+[pt[i] * G.i : i in [1..d]] : pt in pts];
    GG,proj:=quo<G | gens>;
    // Calculate the coefficients
    N:=Matrix(Rationals(),[Eltseq(g @@ proj) : g in GG]);
    M:=Matrix(Rationals(),pts);
    coeffs:=RowSequence(N * M^-1);
    return {PowerSequence(Rationals()) | [Rationals() | FractionalPart(c) :
                                                c in coeff] : coeff in coeffs};
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Ehrhart Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic EhrhartCoefficient(C::TorCon,k::RngIntElt) -> RngIntElt
{The number of lattice points in the cone C at height k in the direction of the ambient grading}
    // Sanity check
    P:=Polyhedron(C);
    require IsPolytope(P):
        Sprintf("The grading %o does not yield a polytope at height 1",
                Grading(C));
    // Return the coefficient
    return EhrhartCoefficient(P,k);
end intrinsic;

intrinsic EhrhartCoefficient(C::TorCon,H::TorLatElt,k::RngIntElt) -> RngIntElt
{The number of lattice points in the cone C at height k in the direction H, where H is a primitive lattice point in the dual lattice}
    // Sanity check on H
    require IsInDual(H,Ambient(C)):
        "Argument 2 must lie in the dual to the ambient of argument 1";
    require IsPrimitive(H):
        "Argument 2 must be a primitive lattice point";
    // Sanity check on P
    P:=Polyhedron(C,H,1);
    require IsPolytope(P):
        Sprintf("The grading %o does not yield a polytope at height 1",H);
    // Return the coefficient
    return EhrhartCoefficient(P,k);
end intrinsic;

intrinsic EhrhartCoefficients(C::TorCon,l::RngIntElt) -> SeqEnum[RngIntElt]
{The first l+1 coefficients of the Ehrhart series for the cone C in the direction of the ambient grading}
    // Sanity check
    require l ge 0: "l must be a non-negative integer";
    P:=Polyhedron(C);
    require IsPolytope(P):
        Sprintf("The grading %o does not yield a polytope at height 1",
                Grading(C));
    // Return the coefficients
    return EhrhartCoefficients(P,l);
end intrinsic;

intrinsic EhrhartCoefficients(C::TorCon,H::TorLatElt,l::RngIntElt) -> SeqEnum[RngIntElt]
{The first l+1 coefficients of the Ehrhart series for the cone C in the direction H, where H is a primitive lattice point in the dual lattice}
    // Sanity check on l
    require l ge 0: "l must be a non-negative integer";
    // Sanity check on H
    require IsInDual(H,Ambient(C)):
        "Argument 2 must lie in the dual to the ambient of argument 1";
    require IsPrimitive(H):
        "Argument 2 must be a primitive lattice point";
    // Sanity check on P
    P:=Polyhedron(C,H,1);
    require IsPolytope(P):
        Sprintf("The grading %o does not yield a polytope at height 1",H);
    // Return the coefficients
    return EhrhartCoefficients(P,l);
end intrinsic;

intrinsic EhrhartDeltaVector(C::TorCon) -> SeqEnum[RngIntElt]
{The Ehrhart delta-vector for the cone C in the direction of the ambient grading}
    // Sanity check
    P:=Polyhedron(C);
    require IsPolytope(P):
        Sprintf("The grading %o does not yield a polytope at height 1",
                Grading(C));
    // Return the delta-vector
    return EhrhartDeltaVector(P);
end intrinsic;

intrinsic EhrhartDeltaVector(C::TorCon,H::TorLatElt) -> SeqEnum[RngIntElt]
{The Ehrhart delta-vector for the cone C in the direction H, where H is a primitive lattice point in the dual lattice}
    // Sanity check on H
    require IsInDual(H,Ambient(C)):
        "Argument 2 must lie in the dual to the ambient of argument 1";
    require IsPrimitive(H):
        "Argument 2 must be a primitive lattice point";
    // Sanity check on P
    P:=Polyhedron(C,H,1);
    require IsPolytope(P):
        Sprintf("The grading %o does not yield a polytope at height 1",H);
    // Return the delta-vector
    return EhrhartDeltaVector(P);
end intrinsic;

intrinsic EhrhartPolynomial(C::TorCon) -> SeqEnum[RngUPolElt]
{The Ehrhart (quasi-)polynomial for the cone C in the direction of the ambient grading}
    // Sanity check
    P:=Polyhedron(C);
    require IsPolytope(P):
        Sprintf("The grading %o does not yield a polytope at height 1",
                Grading(C));
    // Return the Ehrhart polynomial
    return EhrhartPolynomial(P);
end intrinsic;

intrinsic EhrhartPolynomial(C::TorCon,H::TorLatElt) -> SeqEnum[RngUPolElt]
{The Ehrhart (quasi-)polynomial for the cone C in the direction H, where H is a primitive lattice point in the dual lattice}
    // Sanity check on H
    require IsInDual(H,Ambient(C)):
        "Argument 2 must lie in the dual to the ambient of argument 1";
    require IsPrimitive(H):
        "Argument 2 must be a primitive lattice point";
    // Sanity check on P
    P:=Polyhedron(C,H,1);
    require IsPolytope(P):
        Sprintf("The grading %o does not yield a polytope at height 1",H);
    // Return the Ehrhart polynomial
    return EhrhartPolynomial(P);
end intrinsic;

intrinsic EhrhartSeries(C::TorCon) -> FldFunRatUElt
{The rational generating function of the Ehrhart series for the cone C in the direction of the ambient grading}
    // Sanity check
    P:=Polyhedron(C);
    require IsPolytope(P):
        Sprintf("The grading %o does not yield a polytope at height 1",
                Grading(C));
    // Return the Ehrhart series
    return EhrhartSeries(P);
end intrinsic;

intrinsic EhrhartSeries(C::TorCon,H::TorLatElt) -> FldFunRatUElt
{The rational generating function of the Ehrhart series for the cone C in the direction H, where H is a primitive lattice point in the dual lattice}
    // Sanity check on H
    require IsInDual(H,Ambient(C)):
        "Argument 2 must lie in the dual to the ambient of argument 1";
    require IsPrimitive(H):
        "Argument 2 must be a primitive lattice point";
    // Sanity check on P
    P:=Polyhedron(C,H,1);
    require IsPolytope(P):
        Sprintf("The grading %o does not yield a polytope at height 1",H);
    // Return the Ehrhart series
    return EhrhartSeries(P);
end intrinsic;
