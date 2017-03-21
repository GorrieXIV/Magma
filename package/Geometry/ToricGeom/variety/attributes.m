freeze;

/////////////////////////////////////////////////////////////////////////
// attributes.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 43426 $
// $Date: 2013-06-13 22:42:23 +1000 (Thu, 13 Jun 2013) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Attributes and properties of toric varieties.
/////////////////////////////////////////////////////////////////////////

import "../utilities/functions.m": variables_of_scheme;
import "../lattice/lattice.m": lattice_from_cache;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns the irrelevant ideal of X. This is a bug fix for the more
// general schemes machinery in Magma.
function irrelevant_ideal(X)
    // If this is a toric variety then the answer is correct
    if Type(X) eq TorVar then
        return IrrelevantIdeal(X);
    end if;
    // Otherwise we might need to fix this
    R:=CoordinateRing(X);
    I:=IrrelevantIdeal(X);
    if I cmpeq R then
        // Projective space
        if Type(X) eq Prj then
            I:=Ideal([R | R.i : i in [1..Rank(R)]]);
        // Product projective space
        elif Type(X) eq PrjProd then
            I:=R;
            for grad in Gradings(X) do
                I *:= Ideal([R | R.i : i in [1..#grad] | grad[i] ne 0]);
            end for;
        end if;
    end if;
    // Return what we have
    return I;
end function;
     
/////////////////////////////////////////////////////////////////////////
// Attributes
/////////////////////////////////////////////////////////////////////////

intrinsic CoxRing(X::TorVar) -> RngCox
{The Cox ring of the toric variety X}
    if not assigned X`Cox_ring then
        require IsField(BaseRing(X)): "Base ring must be a field";
        R:=CoordinateRing(X);
        if Length(X) eq 0 then
            X`Cox_ring:=CoxRing(R,ZeroFan(lattice_from_cache(0)));
        else        
            B:=[irrelevant_ideal(X)];
            Z:=Gradings(X);
            Q:=QuotientGradings(X);
            X`Cox_ring:=CoxRing(R,B,Z,Q);
            if (ISA(Type(X), Prj) and Dimension(X) gt 0) 
                   or ISA(Type(X), Aff) then
                X`Cox_ring`is_toric:=true;
            end if;
        end if;
    end if;
    return X`Cox_ring;
end intrinsic;

intrinsic Fan(X::TorVar) -> TorFan
{The fan associated with the toric variety X}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return Fan(CoxRing(X));
end intrinsic;

intrinsic Rays(X::TorVar) -> SeqEnum[TorLatElt]
{The rays of fan associated with the toric variety X}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return Rays(CoxRing(X));
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Combinatorial properties
/////////////////////////////////////////////////////////////////////////

intrinsic OneParameterSubgroupsLattice(X::TorVar) -> TorLat
{The 1-parameter subgroups lattice of the torus of X, i.e. the lattice containing the fan of X}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return  OneParameterSubgroupsLattice(CoxRing(X));
end intrinsic;

intrinsic MonomialLattice(X::TorVar) -> TorLat
{The mononial lattice of the torus of X, i.e. the lattice containing the polytopes of sections of divisors on X}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return MonomialLattice(CoxRing(X));
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Geometric properties
/////////////////////////////////////////////////////////////////////////

intrinsic IsComplete(X::TorVar) -> BoolElt, DivTorElt
{True iff X is a complete variety}
    require IsField(BaseRing(X)): "Base ring must be a field";
    if IsFakeWeightedProjectiveSpace(X) then
        return true;
    end if;
    return IsComplete(Fan(X));
end intrinsic;

// THINK: Might be worth storing in X`is_projective; then propagate or assign
// in certain situations (such as if X is a Proj(D))
intrinsic ToricIsProjective(X::TorVar) -> BoolElt, DivTorElt
{True iff X is a projecive variety. The second value is an ample cartier divisor. In combinatorial terms, first it checks if fan of X is complete and if yes, then calculates the dimension of the nef cone. If the dimension is maximal, then it returns true. Then the ample divisor is obtained as the primitive element in the semi-line spanned by the union of all rays of the Nef cone.}
    require IsField(BaseRing(X)): "Base ring must be a field";
    if Dimension(X) eq 0 then 
        return true, ZeroDivisor(X);
    end if;
    if not IsComplete(X) then
        return false, _;
    end if;
    if &or[IsZero(i) : i in IntersectionForms(X)] then
        return false, _;
    end if;
    nef_cone:=NefCone(X);
    if Dimension(nef_cone) eq Dimension(Ambient(nef_cone)) and
                                                   Dimension(nef_cone) gt 0 then
        ray:=PrimitiveLatticeVector(&+MinimalRGenerators(nef_cone));
        ample:=Representative(X,ray);
        _:=IsCartier(ample);
        return true, ample;
    end if;
    return false, _;
end intrinsic;

intrinsic ToricIsAffine(X::TorVar) -> BoolElt
{True iff X is an affine variety.}
    if Dimension(X) eq 0 then 
        return true;
    end if;
    if  IsEmpty(IrrelevantComponents(X))  then
        return true;
    end if;
    if  {#i : i in IrrelevantGenerators(X)} eq {1}  then
        return true;
    end if;
    return false;
end intrinsic;

intrinsic IsGorenstein(X:: TorVar) -> BoolElt
{True iff  X is Gorenstein}
    require IsField(BaseRing(X)): "Base ring must be a field";
    bool,wts:=IsFakeWeightedProjectiveSpace(X);
    if bool then
        h:=&+wts;
        if not &and[IsDivisibleBy(h,wt) : wt in wts] then
            return false;
        end if;
        if NumberOfQuotientGradings(X) eq 0 then
            return true;
        end if;
    end if;
    return IsGorenstein(Fan(X));
end intrinsic;

intrinsic IsQGorenstein(X::TorVar) -> BoolElt
{True iff X is QGorenstein}
    require IsField(BaseRing(X)): "Base ring must be a field";
    if IsFakeWeightedProjectiveSpace(X) then
        return true;
    end if;
    return IsQGorenstein(Fan(X));
end intrinsic;

intrinsic IsQFactorial(X::TorVar) -> BoolElt
{True iff X is Q-factorial}
    require IsField(BaseRing(X)): "Base ring must be a field";
    if IsFakeWeightedProjectiveSpace(X) then
        return true;
    end if;
    return IsQFactorial(Fan(X));
end intrinsic;

intrinsic IsIsolated(X::TorVar) -> BoolElt
{True iff X has only isolated singularities}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return IsIsolated(Fan(X));
end intrinsic;

intrinsic IsTerminal(X::TorVar) -> BoolElt
{True iff X has only terminal singularities}
    require IsField(BaseRing(X)): "Base ring must be a field";
    // If this is a (fake) wps we might be able to answer without needing to
    // create the fan.
    bool,wts:=IsFakeWeightedProjectiveSpace(X);
    if bool then
        // We use the test in:
        //   A. M. Kasprzyk, "Classifying terminal weighted projective space",
        //   arXiv:1304.3029 [math.AG]
        n:=#wts - 1;
        h:=&+wts;
        for k in [2..h - 2] do
            s:=&+[(wt * k) mod h : wt in wts];
            if s lt 2 * h or s gt (n - 1) * h then
                return false;
            end if;
        end for;
        if NumberOfQuotientGradings(X) eq 0 then
            return true;
        end if;
    end if;
    // If we're here then we'll need to make use of the fan
    return IsTerminal(Fan(X));
end intrinsic;

intrinsic IsCanonical(X::TorVar) -> BoolElt
{True iff X has only canonical singularities}
    require IsField(BaseRing(X)): "Base ring must be a field";
    bool,wts:=IsFakeWeightedProjectiveSpace(X);
    if bool then
        n:=#wts - 1;
        h:=&+wts;
        for k in [2..h - 2] do
            s:=&+[(wt * k) mod h : wt in wts];
            if s lt h or s gt (n - 1) * h then
                return false;
            end if;
        end for;
        if NumberOfQuotientGradings(X) eq 0 then
            return true;
        end if;
    end if;
    return IsCanonical(Fan(X));
end intrinsic;

intrinsic IsSingular(X::TorVar) -> BoolElt
{True iff X is singular}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return not IsNonsingular(X);
end intrinsic;

intrinsic IsNonSingular(X::TorVar) -> BoolElt
{True iff X is non-singular}
    require IsField(BaseRing(X)): "Base ring must be a field";
     return IsNonsingular(X);
end intrinsic;

intrinsic IsNonsingular(X::TorVar) -> BoolElt
{True iff X is non-singular}
    require IsField(BaseRing(X)): "Base ring must be a field";
    if IsFakeWeightedProjectiveSpace(X) then
        return IsOrdinaryProjective(X);
    end if;
    return IsNonsingular(Fan(X));
end intrinsic;

intrinsic Resolution(X::TorVar : deterministic:=true) -> TorVar,TorMap
{A resolution of singularities of the toric variety X and the natural morphism. If the optional parameter 'deterministic' (default: true) is set to false then a non-deterministic algorithm will be used to calculate the resolution.}
    require IsField(BaseRing(X)): "Base ring must be a field";
    if IsSingular(X) then
        Y:=ToricVariety(BaseRing(X),
                        Resolution(Fan(X) : deterministic:=deterministic));
    else
        Y:=X;
    end if;
    // THINK: Is it worth adding Y`is_smooth?
    return Y,ToricVarietyMap(Y,X);
end intrinsic;

intrinsic Terminalisation(X::TorVar) -> TorVar,TorMap
{A Q-factorial terminal blowup of the toric variety X and the natural morphism}
    require IsField(BaseRing(X)): "Base ring must be a field";
    if not IsTerminal(X) then
        Y:=ToricVariety(BaseRing(X),Terminalisation(Fan(X)));
    else
        Y:=X;
    end if;
    // THINK: Is it worth adding Y`is_terminal?
    return Y,ToricVarietyMap(Y,X);
end intrinsic;

intrinsic Canonicalisation(X::TorVar) -> TorVar,TorMap
{A Q-factorial canonical blowup of the toric variety X and the natural morphism}
    require IsField(BaseRing(X)): "Base ring must be a field";
    if not IsCanonical(X) then
        Y:=ToricVariety(BaseRing(X),Canonicalisation(Fan(X)));
    else
        Y:=X;
    end if;
    // THINK: Is it worth adding Y`is_canonical?
    return Y,ToricVarietyMap(Y,X);
end intrinsic;

intrinsic QFactorialisation(X::TorVar) -> TorVar, TorMap
{A Q-Factorialisation of X together with the natural morphism}
    require IsField(BaseRing(X)): "Base ring must be a field";
    if not IsQFactorial(X) then
        Y:=ToricVariety(BaseRing(X),SimplicialSubdivision(Fan(X)));
    else
        Y:=X;
    end if;
    // THINK: Is it worth adding Y`is_Qfactorial?
    // THINK: Add good description of the map to be the identity
    psi:=ToricVarietyMap(Y,X);
    S:=variables_of_scheme(Y);
    ChangeUniverse(~S, FamilyOfMultivaluedSections(Y));
    psi`description:=S;
    psi`is_description_good:=true;
    return Y, psi;
end intrinsic;

intrinsic IsWeakFano(X::TorVar) -> BoolElt
{True iff X is a weak Fano}
    require IsField(BaseRing(X)): "Base ring must be a field";
    if IsFakeWeightedProjectiveSpace(X) then
        return true;
    end if;
    rays:=Rays(X);
    if Dimension(X) ne Dimension(Universe(rays)) then
        return false;
    end if;
    P:=Polytope(rays);
    return IsFano(P) and &and[IsOnBoundary(r,P) : r in rays] and IsComplete(X);
end intrinsic;

intrinsic IsFano(X::TorVar) -> BoolElt
{True iff X is Q-Fano (i.e. if the anticanonical divisor is ample)}
    require IsField(BaseRing(X)): "Base ring must be a field";
    if IsFakeWeightedProjectiveSpace(X) then
        return true;
    end if;
    rays:=Rays(X);
    if Dimension(X) ne Dimension(Universe(rays)) then
        return false;
    end if;
    P:=Polytope(rays);
    if NumberOfVertices(Polytope(rays)) eq #rays and IsFano(P) and
       NumberOfFacets(P) eq #Cones(Fan(X)) then
        F:=Fan(X);
        if not assigned F`is_complete then
            F`is_complete:=SequenceToSet(ConeIndices(F)) eq
                                SequenceToSet(FacetIndices(P));
        end if;
        return F`is_complete;
    end if;
    return false;
end intrinsic;

intrinsic IsFakeWeightedProjectiveSpace(X::TorVar) -> BoolElt,SeqEnum[RngIntElt]
{True iff X is isomorphic to a fake weighted projective space (i.e. a quotient of a weighted projectve space by a finite Abelian group acting coordinate wise). If true, also gives the integer weights in the order indicated by the variables.}
    if NumberOfGradings(X) ne 1 or #IrrelevantComponents(X) ne 1 then
        return false,_;
    end if;
    B:=Representative(IrrelevantGenerators(X));
    return Seqset(B) eq Seqset(variables_of_scheme(X)),
           Representative(Gradings(X));
end intrinsic;

intrinsic IsWeightedProjectiveSpace(X::TorVar) -> BoolElt,SeqEnum[RngIntElt]
{True iff X is isomorphic to a weighted projective space. If true, also gives the weights in the order indicated by the variables.}
    if NumberOfQuotientGradings(X) ne 0 then  
        return false, _;
    end if;
    bool, grading:=IsFakeWeightedProjectiveSpace(X);
    if bool then 
        return true, grading;
    end if;
    return false, _;
end intrinsic;
