freeze;

////////////////////////////////////////////////////////////////////////
// singularities.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 36857 $
// $Date: 2012-01-09 07:02:03 +1100 (Mon, 09 Jan 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for calculating Gorenstein and singularity data for a cone.
/////////////////////////////////////////////////////////////////////////

import "../lattice/lattice.m": lattice_get_Zlattice, lattice_from_cache;

declare attributes TorCon:
    gorenstein_hyperplane,  // If C is Q-Gorenstein, this is the hyperplane...
    gorenstein_index,       // ...and this is the Gorenstein index
    is_smooth,              // Is this cone smooth?
    is_isolated,            // Is this cone isolated?
    is_terminal,            // Is this cone terminal?
    is_canonical;           // Is this cone canonical?

/////////////////////////////////////////////////////////////////////////
// Local Functions
/////////////////////////////////////////////////////////////////////////

// Copies the data from "C" to "dC".
procedure singularities_copy(C,dC)
    if assigned C`gorenstein_hyperplane then
        dC`gorenstein_hyperplane:=C`gorenstein_hyperplane; end if;
    if assigned C`gorenstein_index then
        dC`gorenstein_index:=C`gorenstein_index; end if;
    if assigned C`is_smooth then
        dC`is_smooth:=C`is_smooth; end if;
    if assigned C`is_terminal then
        dC`is_terminal:=C`is_terminal; end if;
    if assigned C`is_canonical then
        dC`is_canonical:=C`is_canonical; end if;
end procedure;

// Sets the data of "dC" equal to minus "C".
procedure singularities_minus(C,dC)
    if assigned C`gorenstein_hyperplane then
        dC`gorenstein_hyperplane:=-C`gorenstein_hyperplane; end if;
    if assigned C`gorenstein_index then
        dC`gorenstein_index:=C`gorenstein_index; end if;
    if assigned C`is_smooth then
        dC`is_smooth:=C`is_smooth; end if;
    if assigned C`is_terminal then
        dC`is_terminal:=C`is_terminal; end if;
    if assigned C`is_canonical then
        dC`is_canonical:=C`is_canonical; end if;
end procedure;

// Sets the data of "dC" equal to "C", but with the ambient changed to "L".
procedure singularities_change_ambient(C,dC,L)
    if assigned C`gorenstein_hyperplane then
        dC`gorenstein_hyperplane:=Dual(L) ! C`gorenstein_hyperplane; end if;
    if assigned C`gorenstein_index then
        dC`gorenstein_index:=C`gorenstein_index; end if;
    if assigned C`is_smooth then
        dC`is_smooth:=C`is_smooth; end if;
    if assigned C`is_terminal then
        dC`is_terminal:=C`is_terminal; end if;
    if assigned C`is_canonical then
        dC`is_canonical:=C`is_canonical; end if;
end procedure;

// Sets the cone's Gorenstein index and hyperplane if the cone is Gorenstein,
// otherwise it sets the Gorenstein index to -1
procedure calculate_gorenstein_data(C)
    cone,phi1:=ConeQuotientByLinearSubspace(C);
    cone,phi2:=ConeInSublattice(cone);
    rays:=MinimalRGenerators(cone);
    if IsEmpty(rays) then
        H:=Zero(Ambient(C));
    else
        origin:=Representative(rays);
        rays2:=LinearSpanEquations([Universe(rays)|ray - origin : ray in rays]);
        if #rays2 eq 1 then
            ray:=Representative(rays2);
            H:=(((1 / (ray * origin)) * ray) @@ Dual(phi2)) * phi1;
        else
            C`gorenstein_index:=-1;
            return;
        end if;
    end if;
    C`gorenstein_hyperplane:=H;
    C`gorenstein_index:=LCM([Integers() | Denominator(i) : i in Eltseq(H)]); 
end procedure;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic IsQFactorial(C::TorCon) -> BoolElt 
{True iff the cone C is simplicial (i.e. the corresponding affine variety is Q-Factorial)}
    return IsSimplicial(C);
end intrinsic;

intrinsic PointToBlowUp(C::TorCon) -> TorLatElt
{If C is smooth or not simplicial, then gives the primitive vector of the sum of all MinimalRGenerators of C. Otherwise gives a point such that the blow up at this point will decrease the index of the singularities.}
    if not IsSimplicial(C) or IsNonsingular(C) then
        return PointInInterior(C);
    end if;
    CC,emb:=ConeInSublattice(C);
    M:=Matrix(MinimalRGenerators(CC));
    det:=Index(CC);
    M_mod_det:=ChangeRing(M,quo<Integers() | det>);
    B:=Kernel(M_mod_det).1;
    point:=ChangeRing(B,Integers());
    point:=Ambient(CC) ! RowSequence(Matrix([point]) * M)[1];
    point:=emb(point) / det;
    return point;
end intrinsic;

intrinsic IsGorenstein(C::TorCon) -> BoolElt
{True iff the cone C has rays contained in one affine hyperplane such that the equation of this hyperplane (which takes unit on each primitive vector of the rays) is integral (i.e. iff the corresponding affine variety is Gorenstein)}
    if not assigned C`gorenstein_index then
        calculate_gorenstein_data(C);
    end if;
    return C`gorenstein_index eq 1;
end intrinsic;

intrinsic IsQGorenstein(C::TorCon) -> BoolElt
{True iff the cone C has rays contained in one affine hyperplane (i.e. iff the corresponding affine variety is Q-Gorenstein)}
    if not assigned C`gorenstein_index then
        calculate_gorenstein_data(C);
    end if;
    return C`gorenstein_index gt 0;
end intrinsic;

intrinsic GorensteinIndex(C::TorCon) -> RngIntElt, TorLatElt
{The Gorenstein index of the affine variety corresponding to the cone C (assuming that it is Q-Gorenstein). Also gives the equation of the hyperplane.}
    if (not assigned C`gorenstein_index) or
        (C`gorenstein_index gt 0 and not assigned C`gorenstein_hyperplane) then
        calculate_gorenstein_data(C);
    end if;
    require C`gorenstein_index gt 0: "The cone is not Q-Gorenstein";
    return C`gorenstein_index, C`gorenstein_hyperplane;
end intrinsic;

intrinsic OuterNormal(C::TorCon) -> TorLatElt
{For a Gorenstein cone C (i.e. the primitive generators r_i of the rays of C lie in a common hyperplane), gives an element n in the dual lattice such that n * r_i = 1.}
    if (not assigned C`gorenstein_index) or
        (C`gorenstein_index gt 0 and not assigned C`gorenstein_hyperplane) then
        calculate_gorenstein_data(C);
    end if;
    require C`gorenstein_index gt 0: "The cone is not Q-Gorenstein";
    return C`gorenstein_hyperplane;
end intrinsic;

intrinsic InnerNormal(C::TorCon) -> TorLatElt
{For a Gorenstein cone C (i.e. the primitive generators r_i of the rays of C lie in a common hyperplane), gives an element n in the dual lattice such that n * r_i = -1.}
    if (not assigned C`gorenstein_index) or
        (C`gorenstein_index gt 0 and not assigned C`gorenstein_hyperplane) then
        calculate_gorenstein_data(C);
    end if;
    require C`gorenstein_index gt 0: "The cone is not Q-Gorenstein";
    return -C`gorenstein_hyperplane;
end intrinsic;

intrinsic IsIsolated(C::TorCon) -> BoolElt
{True iff the singularity of the affine variety associated to cone C is isolated}
    if not assigned C`is_isolated and (assigned C`is_smooth or
       (not assigned C`is_smooth and not IsNonsingular(C))) then
        if assigned C`is_terminal and C`is_terminal and Dimension(C) le 3 then
            C`is_isolated:=true;
        else
            C`is_isolated:=&and[IsNonsingular(CC) : CC in Facets(C)];
        end if;
    end if;
    return C`is_isolated;
end intrinsic;

intrinsic IsTerminal(C::TorCon) -> BoolElt
{True iff the singularity of the affine variety associated to cone C is (at worst) terminal}
    if not assigned C`is_terminal and (assigned C`is_smooth or
       (not assigned C`is_smooth and not IsNonsingular(C))) then
        cone:=ConeInSublattice(ConeQuotientByLinearSubspace(C));
        // If the cone isn't Q-Gorenstein then we're done
        if not IsQGorenstein(cone) then
            C`is_terminal:=false;
            C`is_canonical:=false;
        else
            // If we already know the Z generators then this is easy
            if assigned cone`Zgens then
                _,H:=GorensteinIndex(cone);
                C`is_terminal:=&and[v * H gt 1 : v in ZGenerators(cone) |
                                            not v in MinimalRGenerators(cone)];
            // Otherwise we avoid calculating them
            else
                // If the cone is simplicial, we can use the box elements
                if IsSimplicial(cone) then
                    C`is_terminal:=&and[c gt 1 :
                                c in [&+pt : pt in BoxElements(cone)] | c ne 0];
                // Otherwise we exploit the polytope point counting code
                else
                    P:=Polytope([Zero(Ambient(cone))] cat
                                  MinimalRGenerators(cone) : areVertices:=true);
                    C`is_terminal:=NumberOfPoints(P) eq NumberOfVertices(P);
                end if;
            end if;
            // If we were terminal, then we can set the canonical flag too
            if C`is_terminal then
                C`is_canonical:=true;
            end if;
        end if;
    end if;
    return C`is_terminal;
end intrinsic;

intrinsic IsCanonical(C::TorCon) -> BoolElt
{True iff the singularity of the affine variety associated to cone C is (at worst) canonical}
    if not assigned C`is_canonical and (assigned C`is_smooth or
       (not assigned C`is_smooth and not IsNonsingular(C))) then
        cone:=ConeInSublattice(ConeQuotientByLinearSubspace(C));
        // If the cone isn't Q-Gorenstein then we're done
        if not IsQGorenstein(cone) then
            C`is_terminal:=false;
            C`is_canonical:=false;
        else
            r,H:=GorensteinIndex(cone);
            // If the Gorenstein index is 1 then this is trivial
            if r eq 1 then
                C`is_canonical:=true;
            // If we already know the Z generators then this is easy
            elif assigned cone`Zgens  then
                C`is_canonical:=&and[v * H ge 1 : v in ZGenerators(cone)];
            // Otherwise we avoid calculating them
            else
                // If the cone is simplicial, we can use the box elements
                if IsSimplicial(cone) then
                    C`is_canonical:=&and[c ge 1 :
                                c in [&+pt : pt in BoxElements(cone)] | c ne 0];
                // Otherwise we exploit the polytope point counting code
                else
                    P:=Polytope([Zero(Ambient(cone))] cat [Ambient(cone) |
                        ((r - 1) / r) * gen : gen in MinimalRGenerators(cone)] :
                                                             areVertices:=true);
                    C`is_canonical:=NumberOfPoints(P) eq 1;
                end if;
            end if;
            // If we weren't canonical then we can't be terminal either
            if not C`is_canonical then
                C`is_terminal:=false;
            end if;
        end if;
    end if;
    return C`is_canonical;
end intrinsic;

intrinsic IsSingular(C::TorCon) -> BoolElt
{True iff the affine variety associated to the cone C is singular}
    return not IsNonsingular(C);
end intrinsic;

intrinsic IsNonSingular(C::TorCon) -> BoolElt
{True iff the affine variety associated to the cone C is nonsingular}
    return IsNonsingular(C);
end intrinsic;

intrinsic IsNonsingular(C::TorCon) -> BoolElt
{True iff the affine variety associated to the cone C is nonsingular}
    if not assigned C`is_smooth then
        cone:=ConeInSublattice(ConeQuotientByLinearSubspace(C));
        if IsSimplicial(cone) and Index(cone) eq 1 then
            C`is_smooth:=true;
            C`is_isolated:=true;
            C`is_terminal:=true;
            C`is_canonical:=true;
        else
            C`is_smooth:=false;
        end if;
    end if;
    return C`is_smooth;
end intrinsic;

intrinsic QuotientGenerators(C::TorCon) -> SetEnum[SeqEnum[FldRatElt]]
{A sequence of generators of the torsion of the ambient lattice of the simplicial toric cone C divided by the sublattice generated by the rays of C; the generators are expressed in the basis given by the rays of C}
    require IsSimplicial(C): "The cone must be simplicial";
    require IsMaximumDimensional(C):
        "The cone must be of maximum dimension in its ambient toric lattice";
    // Map to the quotient Z-module by the rays of C
    L:=Ambient(C);
    quolat,proj:=quo<lattice_get_Zlattice(L) | [ Eltseq(v) : v in Rays(C) ]>;
    // Pull back a basis of torsion to the lattice of C
    gens:=Generators(TorsionSubmodule(quolat));
    gens_in_L:=gens @@ proj;
    // Put these into the lattice of C (although not necessarily in C)
    ChangeUniverse(~gens_in_L,L);
    // Pull back C to the first quadrant of another lattice
    LL:=lattice_from_cache(Dimension(L));
    emb:=hom<LL -> L | Rays(C)>;
    // Pull back the torsion generators to the new lattice and move them into
    // the unit cube (the kernel of the map to the quotient module is simply the
    // integral lattice itself).
    gens_in_LL:=gens_in_L @@ emb;
    return {PowerSequence(Rationals()) | [Rationals() | FractionalPart(c) :
                                            c in Eltseq(v)] : v in gens_in_LL};
end intrinsic;
