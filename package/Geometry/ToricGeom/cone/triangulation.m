freeze;

////////////////////////////////////////////////////////////////////////
// triangulation.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 27125 $
// $Date: 2010-06-04 12:14:46 +1000 (Fri, 04 Jun 2010) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Calculates the simplicial subdivision of a cone.
/////////////////////////////////////////////////////////////////////////
// * The function cone_simplicial_subdivision(C) returns a sequence
//   of sequences of rays (represented by toric lattice elements in the
//   ambient of C) such that each sequence of rays generates a cone in
//   the simplicial subdivision of C.
//      eg. Cs:=[Cone(rays) : rays in cone_simplicial_subdivision(C)];
//
// * Alternatively, the intrinsic SimplicialSubdivision(C) will return
//   the subdivision packaged up as a fan.
//      eg. Cs:=Cones(SimplicialSubdivision(C));
/////////////////////////////////////////////////////////////////////////
// Note: The subdivision is NOT cached, so repeated calls should be
// avoided.
/////////////////////////////////////////////////////////////////////////

import "../utilities/functions.m": seq_of_k_subsets;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Recursivly calculates a sequence of rays of simplicial cones subdividing the
// cone C in the case when C is strictly convex.
// Returns the rays as indices of the sequence of lattice points "pts".
// Note: Intended for internal use only. You should call the function
// cone_simplicial_subdivision(C) if you require the subdivision.
function cone_subdivision_recurse(D,pts,rays,d,depth)
    // Is this a simplicial cone? This is the bottom of the recursion.
    if #rays eq d then
        // Build the boundary data if we're not the top level too
        if depth ne 0 then
            norms:=[D|];
            boundary:=[PowerSet(Integers())|];
            for i in [1..d] do
                sub_rays:=Remove(rays,i);
                n:=D ! Kernel(Transpose(Matrix([PowerSequence(Rationals()) |
                                           Eltseq(pts[j]) : j in sub_rays]))).1;
                if n * pts[rays[i]] lt 0 then n *:= -1; end if;
                Append(~norms,n);
                Append(~boundary,SequenceToSet(sub_rays));
            end for;
            // Return the rays and boundary data
            return [rays],norms,boundary;
        else
            return [rays],_,_;
        end if;
    end if;
    // The inductive step:
    // Remove a generator so that the cone stays of the same dimension
    i:=0;
    repeat
        i +:= 1;
        ray:=rays[i];
        sub_rays:=Remove(rays,i);
    until Rank(Matrix([PowerSequence(Rationals()) | Eltseq(pts[j]) :
                                                         j in sub_rays])) eq d;
    // Recurse to obtain a simplicial subdivision of the sub-cone
    sub_div,norms,boundary:=$$(D,pts,sub_rays,d,depth + 1);
    // Now we need to calculate the extension over all bounday facets
    if depth ne 0 then
        // If we're not at the top level of the recursion then we also refine
        // the boundary facet data...
        new_norms:=[D|];
        new_boundary:=[PowerSet(Integers())|];
        excluded:={PowerSet(Integers())|};
        for i in [1..#norms] do
            if norms[i] * pts[ray] lt 0 then
                // Record the new cone
                facet:=SetToSequence(boundary[i]);
                Append(~sub_div,Append(facet,ray));
                // Update the boundary data over this facet
                for j in [1..d - 1] do
                    sub_rays:=Remove(facet,j);
                    Append(~sub_rays,ray);
                    sub_rays_set:=SequenceToSet(sub_rays);
                    idx:=Index(new_boundary,sub_rays_set);
                    if idx ne 0 then
                        Remove(~new_norms,idx);
                        Remove(~new_boundary,idx);
                        Include(~excluded,sub_rays_set);
                    elif not sub_rays_set in excluded then
                        n:=D ! Kernel(Transpose(Matrix(
                                        [PowerSequence(Rationals()) |
                                        Eltseq(pts[j]) : j in sub_rays]))).1;
                        if n * pts[facet[j]] lt 0 then n *:= -1; end if;
                        Append(~new_norms,n);
                        Append(~new_boundary,sub_rays_set);
                    end if;
                end for;
            else
                Append(~new_norms,norms[i]);
                Append(~new_boundary,boundary[i]);
            end if;
        end for;
        // Return the subdivision and boundary data
        return sub_div,new_norms,new_boundary;
    else
        // ...otherwise we do the minimum amount of calculation
        for i in [1..#norms] do
            if norms[i] * pts[ray] lt 0 then
                Append(~sub_div,Append(SetToSequence(boundary[i]),ray));
            end if;
        end for;
        // Return the subdivision
        return sub_div,_,_;
    end if;
end function;

// Returns a sequence of rays of simplicial cones subdividing the (not
// necessarily strictly convex) cone C.
function cone_simplicial_subdivision(C)
    // Is there anything to do?
    if IsSimplicial(C) then return [MinimalRGenerators(C)]; end if;
    // We need to check whether the cone is strictly convex or not
    subspace:=LinearSubspaceGenerators(C);
    L:=Ambient(C);
    if IsEmpty(subspace) then
        // If C is strictly convex, then we recursively subdivide
        gens:=MinimalRGenerators(C);
        Cs:=cone_subdivision_recurse(Dual(L),gens,[1..#gens],Dimension(C),0);
        return [PowerSequence(L) | [L | gens[i] : i in rays] : rays in Cs];
    else
        // Otherwise we strip out the linear space and recurse
        C,phi:=ConeQuotientByLinearSubspace(C);
        gens:=MinimalRGenerators(C);
        Cs:=cone_subdivision_recurse(Dual(Ambient(C)),gens,[1..#gens],
                                                                Dimension(C),0);
        gens:=gens @@ phi;
        Cs:=[PowerSequence(L) | [L | gens[i] : i in rays] : rays in Cs];
        Append(~subspace,-&+subspace);
        subspace:=[subspace[Remove([1..#subspace],i)] : i in [1..#subspace]];
        return [PowerSequence(L) | s cat q : s in Cs, q in subspace];
    end if;
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

// Note: The fan generated by the simplicial subdivision is NOT cached
intrinsic SimplicialSubdivision(C::TorCon) -> TorFan
{A simplicial fan subdividing the cone C}
    // Get the easy case out of the way
    if IsSimplicial(C) then return Fan(C); end if;
    // Calculate the subdivision
    Cs:=[PowerStructure(TorCon)|];
    d:=Dimension(C);
    for rays in cone_simplicial_subdivision(C) do
        // Create and set the sub-cone's data
        subC:=Cone(rays);
        subC`is_simplicial:=true;
        subC`is_linear_space:=false;
        subC`dim:=d;
        subC`are_Rgens_minimal:=true;
        // Add the sub-cone to the subdivision
        Append(~Cs,subC);
    end for;
    // Return the fan
    return Fan(Cs : define_fan:=true, max_cones:=true);
end intrinsic;
