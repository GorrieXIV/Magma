freeze;

/////////////////////////////////////////////////////////////////////////
// demazure.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 41411 $
// $Date: 2012-12-04 17:27:41 +1100 (Tue, 04 Dec 2012) $
// $LastChangedBy: allan $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for working with Demazure root systems of fans.
/////////////////////////////////////////////////////////////////////////

declare attributes TorFan:
    demazure_ss,        // The semistable Demazure roots of F
    demazure_uni;       // The unipotent Demazure roots of F

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns true iff the given set S of roots has a linearly independent subset
// of size d.
function has_linearly_indep_subset(S,d)
    for I in Subsets(S,d) do
        if Rank(Matrix(SetToSequence(I))) eq d then return true; end if;
    end for;
    return false;
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic DemazureRoots( F::TorFan ) -> SetEnum[TorLatElt],SetEnum[TorLatElt]
{The Demazure roots of the complete fan F. The roots are partitioned into two sets: the semistable roots and the unipotent roots.}
    if not assigned F`demazure_ss then
        // Sanity check
        require IsComplete(F): "The fan must be complete";
        // First we extract the root
        rays:=Rays(F);
        cs:=[-1,1] cat ZeroSequence(Integers(),#rays - 1);
        roots:={Dual(Ambient(F))|};
        for idx in [1..#rays] do
            I:=[rays[idx],-rays[idx]] cat [rays[i] : i in [1..#rays] | i ne idx];
            P:=PolyhedronWithInequalities(I,cs);
            roots join:= Points(P);
        end for;
        // Now we partition them into semistable and unipotent sets
        F`demazure_ss:={Universe(roots) | m : m in roots | -m in roots};
        F`demazure_uni:={Universe(roots) | m : m in roots | not -m in roots};
    end if;
    return F`demazure_ss,F`demazure_uni;
end intrinsic;

intrinsic NumberOfRoots( F::TorFan ) -> RngIntElt
{The number of Demazure foots of the complete fan F}
    require IsComplete(F): "The fan must be complete";
    return #ss + #uni where ss,uni:=DemazureRoots(F);
end intrinsic;

intrinsic IsSemistable( F::TorFan ) -> BoolElt
{True if and only if the complete fan F is semistable}
    require IsComplete(F): "The fan must be complete";
    return IsEmpty(uni) where _,uni:=DemazureRoots(F);
end intrinsic;

intrinsic IsReductive( X::TorVar ) -> BoolElt
{True if and only if the automorphism group of the projective variety X is reductive}
    require IsField(BaseRing(X)): "Base ring must be a field";
    require IsProjective(X): "The toric variety must be projective";
    return IsSemistable(Fan(X));
end intrinsic;

intrinsic IsIsomorphicToProductProjectiveSpace( X::TorVar ) -> BoolElt
{True if and only if the complete toric variety X is isomorphic to a product of projective spaces}
    // Sanity check
    require IsField(BaseRing(X)): "Base ring must be a field";
    require IsComplete(X): "The toric variety must be complete";
    // Extract the semisimple roots
    ss:=DemazureRoots(Fan(X));
    // Do there exist d linearly independent semisimple roots?
    return has_linearly_indep_subset(ss,Dimension(X));
end intrinsic;

intrinsic IsIsomorphicToProjectiveSpace( X::TorVar ) -> BoolElt
{True if and only if the complete toric variety X is isomorphic to projective space}
    // Sanity check
    require IsField(BaseRing(X)): "Base ring must be a field";
    require IsComplete(X): "The toric variety must be complete";
    // Extract the semisimple roots
    ss:=DemazureRoots(Fan(X));
    // X \comp PP^d if and only if #ss = d^2 + d
    d:=Dimension(X);
    return #ss eq d^2 + d;
end intrinsic;
