freeze;

/////////////////////////////////////////////////////////////////////////
// divisor.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 48810 $
// $Date: 2014-11-01 22:14:16 +1100 (Sat, 01 Nov 2014) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Calculations with divisors on toric varieties.
/////////////////////////////////////////////////////////////////////////

import "../utilities/functions.m": remove_repetitions;
import "../utilities/strings.m": seq_to_string;
import "../lattice/lattice.m": lattice_from_cache,lattice_get_Zlattice;
import "../lattice/map.m": space_map, preimage_for_module_map;
import "../fan/fan.m": construct_fan_from_rays;

// Cache attributes on the toric variety
declare attributes TorVar:
    Pic_basis_representatives,  // The divisors rep. generators of Pic
    divisor_group;              // The divisor group is cached on X

// The divisor group (although it's a Z-module in practice)
declare type DivTor [DivTorElt]: DivSch;
declare attributes DivTor:
    variety,                   // The associated toric variety
    divisor_cache,             // A cache of known divisors
    curves,                    // Codimension 1 faces of fan of X
    curves_intersection_forms; // Intersection forms in the order of the above

// The divisors
declare type DivTorElt: DivSchElt;
declare attributes DivTorElt:
    // Essential attributes:
    divisor_group,      // The parent divisor group
    weil,               // The element in the dual to weight lattice of variety
    // Optional attributes:
    cartier,            // Sequence of forms on the fan lattice of the variety
    h0_cone,            // Cone of sections of multiples of this divisor
    h0_polyhedron,      // Polyhedron associated to D`h0_cone
    is_ample,           // true if D is ample.
    proj,               // TorVar which is Proj(sum H^0(O(mD)).
    proj_lattice_map,   // map between the Amb(Fan(X)) and Amb(Fan(Proj(D))).
                        // Usually, if Proj has the same dimension, this is id.
    relative_proj;      // TorVar which is (the sheaf) Proj(\oplus O(mD)).

///////////////////////////////////////////////////////////////////////
// Local functions
///////////////////////////////////////////////////////////////////////

// Gets the divisor from the cache, or create a new divisor if it is not there.
// Does NOT assign Cartier information to a new divisor.
function divisor_from_cache(X,S)
    Dgrp:=DivisorGroup(X);
    if not assigned Dgrp`divisor_cache then
        Dgrp`divisor_cache:=AssociativeArray(Dual(RayLattice(X)));
    end if;
    if IsDefined(Dgrp`divisor_cache,S) then
        D:=Dgrp`divisor_cache[S];
    else
        D:=New(DivTorElt);
        D`divisor_group:=Dgrp;
        D`weil:=S;
        Dgrp`divisor_cache[S]:=D;
    end if;
    return D;
end function;

// Converts the given Q-Cartier data to Weil data on the given toric variety
function cartier_to_weil(X,cartier)
    fan:=Fan(X);
    rays:=Rays(fan);
    cones:=ConeIndices(fan);
    weil:=[Rationals()|];
    for i in [1..#rays] do
        j:=Index([i in cone: cone in cones], true);
        Append(~weil, -(rays[i] * cartier[j]));
    end for;
    return Dual(RayLattice(X)) ! weil;
end function;

// Constructs the graded cone from the given combinatorial data of the divisor
function graded_cone_from_combinatorial_data(rays,weil,pure_ray_indices)
    L:=Dual(Universe(rays));
    GL:=GradedToricLattice(L);
    _,_,projs:=Summands(GL);
    ray_basis:=Basis(Dual(Parent(weil)));
    inequalities:=[(ScalarLattice() ! [ray_basis[i] * weil]) * projs[1] +
                                rays[i] * projs[2] : i in pure_ray_indices];
    return ConeWithInequalities(inequalities);
end function;

// Returns the polyhedron associated with the given divisor
function get_rational_polyhedron(D)
    if not assigned D`h0_polyhedron then
        if IsWeil(D) and not IsZero(D) then
            v:=Weil(D);
            gcd:=GCD(Eltseq(v));
            DD:=(1 / gcd) * D;
            C:=GradedCone(DD);
        else
            C:=GradedCone(D);
            gcd:=1;
        end if;
        D`h0_polyhedron:=Polyhedron(C : level:=gcd);
        D`h0_polyhedron`dual_fan_divisor:=D;
    end if;
    return D`h0_polyhedron;
end function;

// Given a divisor D and a codimension one face C of Fan(Variety(D)), returns
// the intersection number D times the curve corresponding to C.
function intersect_divisor_with_cone(D,C)
    F:=Fan(Variety(D));
    C_indices:=ConeIndices(F,C);
    cone_indices:=ConeIndices(F);
    important_cones:=[Integers() | i : i in [1..#cone_indices] |
         C_indices subset cone_indices[i] and not C_indices eq cone_indices[i]];
    if #important_cones le 1 then return 0; end if;
    assert #important_cones eq 2;
    L,phi:=Quotient(C);
    cartier:=[cart[i] :  i in important_cones] where cart is Cartier(D);
    cartier:=(cartier[2] - cartier[1]) @@ Dual(phi);
    r:=PrimitiveLatticeVector(phi(Ray(F,Representative(
                            cone_indices[important_cones[1]] diff C_indices))));
    return cartier * r;
end function;

// Returns a sequence of representatives for a basis for Pic(X)
function representatives_of_basis_of_Pic(X)
    if not assigned X`Pic_basis_representatives then
        pic_lattice:=PicardLattice(X);
        X`Pic_basis_representatives:=[Representative(X,b : effective:=false) :
                                                       b in Basis(pic_lattice)];
    end if;
    return X`Pic_basis_representatives;
end function;

// Returns the curves in the divisor group of X corresponding to the codimension
// one cones of Fan(X)
function get_curves(X)
    G:=DivisorGroup(X);
    if not assigned G`curves then
        G`curves:=ConesOfCodimension(Fan(X),1);
    end if;
    return G`curves;
end function;

// The i-th intersection form on X
function intersection_form(X,i)
    G:=DivisorGroup(X);
    if not assigned G`curves_intersection_forms then
        G`curves_intersection_forms:=[Dual(PicardLattice(X))|];
    end if;
    if not IsDefined(G`curves_intersection_forms,i) then
        C:=get_curves(X)[i];
        Ds:=representatives_of_basis_of_Pic(X);
        G`curves_intersection_forms[i]:= Dual(PicardLattice(X)) !
                     [Rationals() | intersect_divisor_with_cone(D,C) : D in Ds];
    end if;
    return G`curves_intersection_forms[i];
end function;

///////////////////////////////////////////////////////////////////////
// Divisor group of a toric variety
///////////////////////////////////////////////////////////////////////

intrinsic Print(G::DivTor,l::MonStgElt)
{Print the Divisor group G of a toric variety (to level l)}
    printf "Group of divisors of the toric variety ";
    print ToricVariety(G):Minimal;
end intrinsic;

intrinsic IsCoercible(G::DivTor, S::.) -> BoolElt, RngMRadElt
{Can the given element be coerced into the toric divisor group G}
    if Type(S) eq DivTorElt then
        bool:=Variety(S) eq ToricVariety(G);
        if bool then
            return true, S;
        end if;
    elif (ISA(Type(S), RngMPolElt) and S in R)
      or (ISA(Type(S),  FldFunRatElt) and S in FieldOfFractions(R))
      where R:=CoordinateRing(ToricVariety(G)) then
        return true, Divisor(ToricVariety(G), S);
    end if;
    return false,"Illegal coercion";
end intrinsic;

intrinsic 'in'(x::., G::DivTor) -> BoolElt
{Is the given element a member of the toric divisor group G}
    require Type(x) eq DivTorElt: "Incompatible type";
    bool:=IsCoercible(G,x);
    return bool;
end intrinsic;

intrinsic DivisorGroup(X::TorVar) -> DivTor
{The divisor group of the toric variety X}
    if not assigned X`divisor_group then
        require IsField(BaseRing(X)): "Base ring must be a field";
        D:=New(DivTor);
        D`variety:=X;
        X`divisor_group:=D;
    end if;
    return X`divisor_group;
end intrinsic;

intrinsic ToricVariety(D::DivTor) -> TorVar
{The toric variety associated with the divisor group D}
    return D`variety;
end intrinsic;

intrinsic 'eq'(G1::DivTor,G2::DivTor) -> BoolElt
{True iff G1 and G2 are the divisor group of the same toric variety}
    return ToricVariety(G1) eq ToricVariety(G2);
end intrinsic;

///////////////////////////////////////////////////////////////////////
// Divisors of a toric variety
///////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////
// Printing, Parent, and Hash Value
///////////////////////////////////////////////////////////////////////

intrinsic PrintNamed(D::DivTorElt,l::MonStgElt,name::MonStgElt)
{Output a description of the toric divisor D}
    // Create a string describing the type of divisor
    if assigned D`cartier and IsQCartier(D) then
        if IsCartier(D) then
            div_text:="Cartier divisor";
        elif IsIntegral(D`weil) then
            div_text:="Weil Q-Cartier divisor";
        else
            div_text := "Q-Cartier divisor";
        end if;
    elif IsIntegral(D`weil) then
        div_text:="Weil divisor";
    else
        div_text:="Q-Weil divisor";
    end if;
    // Add the name, if specified
    if name ne "$" then
        div_text cat:= " " cat name;
    end if;
    // Adjust for the level of output
    if l ne "Minimal" then
        prefix:="    ";
        div_text cat:= Sprintf(" with coefficients:\n%o%o",prefix,
                                        seq_to_string(Eltseq(Weil(D)),"",","));
    end if;
    // Output the description
    printf div_text;
end intrinsic;

intrinsic Parent(D::DivTorElt) -> DivTor
{The divisor group containing the divisor D}
    return D`divisor_group;
end intrinsic;

intrinsic Hash(D::DivTorElt) -> RngIntElt
{The hash value of the toric divisor}
    return Hash(Weil(D));
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Creation
/////////////////////////////////////////////////////////////////////////

intrinsic Divisor(X::TorVar, S::SeqEnum[RngIntElt]) -> DivTorElt
{}
    require IsField(BaseRing(X)): "Base ring must be a field";
    require #S eq Length(X):
        "Sequence must have length equal to the number of coordinates of the toric variety";
    return divisor_from_cache(X,Dual(RayLattice(X)) ! S);
end intrinsic;

intrinsic Divisor(X::TorVar, S::SeqEnum[FldRatElt]) -> DivTorElt
{}
    require IsField(BaseRing(X)): "Base ring must be a field";
    require #S eq Length(X):
        "Sequence must have length equal to the number of coordinates of the toric variety";
    return divisor_from_cache(X,Dual(RayLattice(X)) ! S);
end intrinsic;

intrinsic Divisor(G::DivTor, S::SeqEnum[RngIntElt]) -> DivTorElt
{}
    X:=ToricVariety(G);
    require #S eq Length(X):
        "Sequence must have length equal to the number of coordinates of the toric variety";
    return divisor_from_cache(X,Dual(RayLattice(X)) ! S);
end intrinsic;

intrinsic Divisor(G::DivTor, S::SeqEnum[FldRatElt]) -> DivTorElt
{The (Q-)Weil divisor on the toric variety X (or its divisor group G) whose multiplicity on i-th coordinate divisor is S[i]}
    X:=ToricVariety(G);
    require #S eq Length(X):
        "Sequence must have length equal to the number of coordinates of the toric variety";
    return divisor_from_cache(X,Dual(RayLattice(X)) ! S);
end intrinsic;

intrinsic Divisor(X::TorVar, i::RngIntElt) -> DivTorElt
{}
    require IsField(BaseRing(X)): "Base ring must be a field";
    requirerange i, 1, Length(X);
    return divisor_from_cache(X,Dual(RayLattice(X)).i);
end intrinsic;

intrinsic Divisor(G::DivTor, i::RngIntElt) -> DivTorElt
{The Weil divisor on the toric variety X (or its divisor group G) given by the vanishing of the i'th coordinate}
    X:=ToricVariety(G);
    requirerange i, 1, Length(X);
    return divisor_from_cache(X,Dual(RayLattice(X)).i);
end intrinsic;

intrinsic Divisor(X::TorVar, m::TorLatElt) -> DivTorElt
{If m is in the monomial lattice of the toric variety X, then gives the principal divisor on X coresponding to the monomial m. If m is a form on the ray lattice of X, then gives the Weil divisor corresponding to m.}
    require IsField(BaseRing(X)): "Base ring must be a field";
    is_in_monomial_lattice:=m in MonomialLattice(X);
    is_in_ray_lattice:=m in Dual(RayLattice(X));
    require is_in_monomial_lattice or is_in_ray_lattice:
        "Argument 2 must lie in either the monomial lattice of argument 1 or in the dual to the ray lattice of argument 1";
    if is_in_monomial_lattice then
        D:=divisor_from_cache(X,Dual(RayLattice(X))![m*r : r in Rays(Fan(X))]);
        if not assigned D`cartier then
          D`cartier:=[m : i in Cones(Fan(X))];
        end if;
    else
        D:=divisor_from_cache(X,m);
    end if;
    return D;
end intrinsic;

intrinsic Divisor(X::TorVar, f::RngMPolElt) -> DivTorElt
{}
    require IsField(BaseRing(X)): "Base ring must be a field";
    require f in CoordinateRing(X):
        "Argument 2 must lie in the coordinate ring of argument 1";
    return Divisor(X, Exponents(LeadingMonomial(f)));
end intrinsic;

intrinsic Divisor(X::TorVar, f::FldFunRatElt) -> DivTorElt
{The divisor D on the toric variety X defined by f. If f is monomial, then D is this divisor. If f is general, then D is linearly equivalent to f; more precisely, D is the divisor defined by the leading monomials of the numerator and denominator of f.}
    require IsField(BaseRing(X)): "Base ring must be a field";
    num:=Numerator(f);
    den:=Denominator(f);
    require num in CoordinateRing(X) and den in CoordinateRing(X):
        "Argument 2 must lie in the coordinate ring of argument 1";
    return Divisor(X,num) - Divisor(X,den);
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Useful shortcut creation functions
/////////////////////////////////////////////////////////////////////////

intrinsic ZeroDivisor(X::TorVar) -> DivTorElt
{The zero divisor on the toric variety X}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return Divisor(X,Zero(Dual(RayLattice(X))));
end intrinsic;

// THINK: To be extended when we introduce PicardGroup
intrinsic Representative(X::TorVar, m::ModEDElt : effective:=true) -> DivTorElt
{If m is an element of the divisor class group of the toric variety X, then gives a divisor D on X whose class modulo linear equivalence is m. Unless the parameter 'effective' is set to false, D will be effective if possible.}
    require IsField(BaseRing(X)): "Base ring must be a field";
    require Parent(m) cmpeq DivisorClassGroup(X):
        "Argument 2 must lie in the divisor class group of argument 1";
    require Type(effective) eq BoolElt: "'effective' must be a boolean";
    if effective then
        w:=preimage_for_module_map(m,WeilToClassGroupsMap(X),
                                 PositiveQuadrant(Dual(RayLattice(X))));
    else
        w:=Dual(RayLattice(X)) ! (m @@ WeilToClassGroupsMap(X));
    end if;
    return Divisor(X,w);
end intrinsic;

intrinsic Representative(X::TorVar, m::TorLatElt : effective:=true) -> DivTorElt
{If m is an element of the Picard lattice or divisor class lattice of the toric variety X, then gives a divisor D on X whose class modulo linear equivalence and torsion is m. Unless the parameter 'effective' is set to false, D will be effective if possible.}
    require IsField(BaseRing(X)): "Base ring must be a field";
    bool:=m in PicardLattice(X);
    require bool or m in DivisorClassLattice(X):
        "Argument 2 must lie in either the Picard lattice or the divisor class lattice of argument 1";
    require Type(effective) eq BoolElt: "'effective' must be a boolean";
    if bool then
        w:=PicardToClassLatticesMap(X) * m;
    else
        w:=m;
    end if;
    if effective then
        ww:=Preimage(w,WeilToClassLatticesMap(X),
		                         PositiveQuadrant(Dual(RayLattice(X))));
    else
        ww:=w @@ WeilToClassLatticesMap(X);
    end if;
    D:=Divisor(X,ww);
    if bool then
        _:=Cartier(D);
    end if;
    return D;
end intrinsic;

intrinsic CanonicalDivisor(X::TorVar) -> DivTorElt
{The canonical divisor of the toric variety X}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return Divisor(X,[-1 : i in AllRays(Fan(X))]);
end intrinsic;

// THINK: To be extended, when we introduce PicardGroup
intrinsic CanonicalClass(X::TorVar : group:="Pic") -> DivTorElt
{The class of canonical divisor of the toric variety X in: the Picard lattice (if group:="Pic", default), X must be QGorenstein; the divisor class lattice (if group:="Cl"); the divisor class group (if group:="ClZ").}
    require IsField(BaseRing(X)): "Base ring must be a field";
    KX:=CanonicalDivisor(X);
    require IsQCartier(KX) or not group eq "Pic":
        "Toric variety must be Q-Gorenstein";
    if group eq "Pic" then
        return PicardClass(KX);
    elif group eq "Cl" then
        return WeilToClassLatticesMap(X) * Weil(KX);
    elif group eq "ClZ" then
        return WeilToClassGroupsMap(X)(Eltseq(Weil(KX)));
    end if;
    require false: "'group' must be one of \"Pic\", \"Cl\", or \"ClZ\"";
end intrinsic;

///////////////////////////////////////////////////////////////////////
// Arithmetic operations on divisors
///////////////////////////////////////////////////////////////////////

intrinsic '+'(D1::DivTorElt, D2::DivTorElt)-> DivTorElt
{The sum of two divisors D1 and D2}
//  require Variety(D1) eq Variety(D2) :
//      "Arguments must be defined on the same variety.";
    D:=divisor_from_cache(Variety(D1),D1`weil + D2`weil);
    if assigned D1`cartier and assigned D2`cartier and
        IsQCartier(D1) and IsQCartier(D2) then
        D`cartier:=[Cartier(D1)[i] + Cartier(D2)[i] : i in [1..#Cartier(D1)]];
    end if;
    return D;
end intrinsic;

intrinsic '*'(n::RngIntElt, D::DivTorElt)-> DivTorElt
{}
    return (Rationals() ! n) * D;
end intrinsic;

intrinsic '*'(n::FldRatElt, D::DivTorElt)-> DivTorElt
{The multiple n * D}
    nD:=divisor_from_cache(Variety(D),n * D`weil);
    if assigned D`cartier and IsQCartier(D) then
        nD`cartier:=[n * cart : cart in Cartier(D)];
    end if;
    return nD;
end intrinsic;

intrinsic '-'(D::DivTorElt)-> DivTorElt
{The negation of D}
    return (-1) * D;
end intrinsic;

intrinsic '-'(D1::DivTorElt, D2::DivTorElt)-> DivTorElt
{The difference of two divisors D1 and D2}
    return D1 + (-D2);
end intrinsic;

intrinsic '*'(D::DivTorElt, v::TorLatElt)-> RngIntElt
{Given a Q-Cartier divisor D, evaluates the piecewise linear function corresponding to D at v}
    require v in OneParameterSubgroupsLattice(Variety(D)):
        "Argument 2 must be in 1-parameter subgroup lattice of the variety of argument 1";
    require IsQCartier(D): "Argument 1 must be Q-Cartier.";
    bool,i:=IsInSupport(v,Fan(Variety(D)));
    require bool: "Argument 2 must be in the support of fan of variety of argument 1";
    return -Cartier(D)[i] * v;
end intrinsic;

///////////////////////////////////////////////////////////////////////
// Recover or create attributes
///////////////////////////////////////////////////////////////////////

intrinsic Variety(D::DivTorElt) -> TorVar
{The toric variety where the divisor D is defined}
    return ToricVariety(Parent(D));
end intrinsic;

intrinsic Weil(D:: DivTorElt) -> TorLatElt
{The element in the ray lattice defining the given Q-Weil divisor D}
    return D`weil;
end intrinsic;

intrinsic Cartier(D::DivTorElt) -> SeqEnum[TorLatElt]
{The sequence of vectors in the monomial lattice whose i-th element corresponds to the i-th cone of the underlying fan. The divisor D must be Q-Cartier.}
    require IsQCartier(D): "The divisor is not Q-Cartier";
    return D`cartier;
end intrinsic;

intrinsic IsWeil(D::DivTorElt) -> BoolElt
{True iff the divisor D is Weil}
    return IsIntegral(Weil(D));
end intrinsic;

intrinsic IsQCartier(D::DivTorElt) -> BoolElt, RngIntElt
{True iff the divisor D is Q-Cartier, and if so, also return the Cartier index of D.}
    if not assigned D`cartier then
        ray_lattice_basis:=Basis(RayLattice(Variety(D)));
        ray_map:=RayLatticeMap(Variety(D));
        Cartier:=[];
        for idxs in ConeIndices(Fan(Variety(D))) do
            basis_here:=[Universe(ray_lattice_basis) | ray_lattice_basis[i] :
                                                                    i in idxs];
            LL:=lattice_from_cache(#idxs);
            phi:=Dual(LatticeMap(LL,basis_here));
            lat_phi:=space_map(Dual(ray_map) * phi);
            if not (Codomain(lat_phi)!Eltseq(phi*D`weil)) in Image(lat_phi) then
                D`cartier:=false;
                return false;
            end if;
            Append(~Cartier,-(phi * D`weil) @@ (Dual(ray_map) * phi));
        end for;
        D`cartier:=Cartier;
    end if;
	bool:=Type(D`cartier) eq SeqEnum;
	if bool then
		n:=LCM([Integers() | Denominator(cart) : cart in D`cartier]);
	    return bool,n;
	else
		return bool,_;
	end if;
end intrinsic;

intrinsic IsCartier(D::DivTorElt) -> BoolElt
{True iff the divisor D is Cartier}
     if not IsQCartier(D) then
        return false;
     end if;
     return IsIntegral(Cartier(D));
end intrinsic;

intrinsic IsZero(D::DivTorElt) -> BoolElt
{True iff the divisor D is the trivial divisor}
    return IsZero(Weil(D));
end intrinsic;


intrinsic IsQPrincipal(D::DivTorElt) -> BoolElt
{True iff any multiple of the divisor D is a principal divisor}
    return IsInImage(Weil(D), Dual(RayLatticeMap(Variety(D))): integral:=false);
end intrinsic;

intrinsic IsPrincipal(D::DivTorElt) -> BoolElt,FldFunRatElt
{True iff the divisor D is a principal divisor, in which case a rational function f for which D = div(f) is returned as a second value.}
    if IsInImage(Weil(D), Dual(RayLatticeMap(Variety(D))): integral:=true) then
        return true,DefiningMonomial(D);
    else
        return false,_;
    end if;
end intrinsic;

intrinsic IsEffective(D::DivTorElt) -> BoolElt
{True iff D is an effective divisor}
    return &and[a ge 0 : a in Eltseq(Weil(D))];
end intrinsic;

intrinsic IsLinearlyEquivalentToCartier(D::DivTorElt) -> BoolElt, DivTorElt
{True iff the divisor D is Q-linearly equivalent a Cartier divisor. If true, then an equivalent Cartier divisor is also given.}
    if not IsQCartier(D) then
        return false,_;
    end if;
    d:=PicardClass(D);
    if IsIntegral(d) then
        return true, Representative(Variety(D),d: effective:=false);
    end if;
    return false,_;
end intrinsic;

intrinsic 'eq'(D::DivTorElt, E::DivTorElt) -> BoolElt
{True iff the  divisors D and E are equal}
    return Weil(D) eq Weil(E);
end intrinsic;

intrinsic AreLinearlyEquivalent(D::DivTorElt, E::DivTorElt) -> BoolElt
{True iff the difference of the divisors D and E is principal, in which case a rational function f for which D = E + div(f) is returned as a second value.}
    bool,f := IsPrincipal(D - E);
    if bool then
        return true,f;
    else
        return false,_;
    end if;
end intrinsic;

intrinsic IsLinearlyEquivalent(D::DivTorElt, E::DivTorElt) -> BoolElt,FldFunRatElt
{True iff the difference of the divisors D and E is principal, in which case a rational function f for which D = E + div(f) is returned as a second value.}
    bool,f := IsPrincipal(D - E);
    if bool then
        return true,f;
    else
        return false,_;
    end if;
end intrinsic;

intrinsic LinearlyEquivalentDivisorWithNoSupportOn(D::DivTorElt,
    S::SeqEnum[RngMPolElt]) -> DivTorElt
{A divisor linearly equivalent to D, with no support on the locus defined by S. S should be a sequence of variables on the variety of D. If S has more than just variables, the other polynomials will be ignored.}
    X:=Variety(D);
    require Universe(S) cmpeq CoordinateRing(X):
        "Argument 2 must consist of elements in the coordinate ring of the variety of argument 1";
    RL:=RayLattice(X);
    w:=Weil(D);
    is_zero_seq:=[X.i in S : i in [1..Length(X)]];
    B:=[lattice_get_Zlattice(Dual(RL)).i : i in [1..Dimension(RL)] |
                                                            not is_zero_seq[i]];
    BD:=[Basis(RL,i) : i in [1..Dimension(RL)] | not is_zero_seq[i]];
    if &and[alpha * w eq 0 : alpha in BD] then return D; end if;
    phi:=WeilToClassGroupsMap(X);
    LL,phi2:=sub<lattice_get_Zlattice(Dual(RL)) | B>;
    phi3:=hom<LL->Codomain(phi) | (phi2 * phi)(Basis(LL))>;
    q:=Denominator(w);
    new_w:=phi2(phi(Eltseq(q * w)) @@ phi3);
    return Divisor(X,(1 / q) * Dual(RL) ! new_w);
end intrinsic;

intrinsic DefiningMonomial(D::DivTorElt) -> RngMPolElt
{The monomial (if D is effective) or rational monomial defining the divisor D}
    require IsWeil(D): "Argument must be an integral Weil divisor.";
    vars:=CoordinateRing(Variety(D));
    exps:=Eltseq(Weil(D));
    return &*[Power(vars.i, exps[i]) : i in [1..#exps]];
end intrinsic;

intrinsic LatticeElementToMonomial(D::DivTorElt,v::TorLatElt) -> RngMPolElt
{The monomial corresponding to v with respect to the Weil divisor D (i.e. the monomial defining D + (v), where (v) is the principal divisor corresponding to v). v must be an integral element of the monomial lattice of the variety associated with D.}
    require v in MonomialLattice(Variety(D)) and IsIntegral(v):
        "Argument 2 must lie in the monomial lattice of the toric variety associated with argument 1";
    require IsWeil(D) : "Argument 1 must be a Weil divisor";
    return DefiningMonomial(D + Divisor(Variety(D),v));
end intrinsic;

// THINK: Could it be cheaper to check i*PicClass(D) gt 0?
// Possibly not: there might be plenty of intersection forms. Whereas nef cone
// might actually be pretty small, and the reduction might have been already
// made. Also make sure this is mathematically correct.
// How about extreme case (X=pt)?
intrinsic IsAmple(D::DivTorElt) -> BoolElt
{True iff the divisor D is ample}
    if not assigned D`is_ample then
        D`is_ample:=IsQCartier(D) and IsComplete(Variety(D)) and
                        not &or[IsZero(i) : i in IntersectionForms(Variety(D))]
                        and IsInInterior(PicardClass(D),NefCone(Variety(D)));
    end if;
    return D`is_ample;
end intrinsic;

/*
//THINK: is this OK? What about the non-normal polytope?
intrinsic IsVeryAmple(D::DivTorElt) -> BoolElt
{True iff the divisor D is very ample}
    return IsCartier(D) and IsAmple(D);
end intrinsic;
*/

intrinsic IsNef(D::DivTorElt) -> BoolElt
{True iff the divisor D is nef}
    return IsQCartier(D) and PicardClass(D) in NefCone(Variety(D));
end intrinsic;

intrinsic IsBig(D::DivTorElt) -> BoolElt
{True iff the divisor D is big}
    C:=GradedCone(D);
    return Dimension(C meet ConeWithInequalities([Grading(C)])) eq
                                                        Dimension(Ambient(C));
end intrinsic;

intrinsic PicardClass(D::DivTorElt) -> TorLatElt
{The class in the Picard lattice corresponding to the Q-Cartier divisor D}
    require IsQCartier(D): "The divisor must be Q-Cartier";
    X:=Variety(D);
    v:=WeilToClassLatticesMap(X) * Weil(D);
    return v @@ PicardToClassLatticesMap(X);
end intrinsic;

///////////////////////////////////////////////////////////////////////
// Sections of divisors
///////////////////////////////////////////////////////////////////////

intrinsic Degree(D::DivTorElt) -> FldRatElt
{The degree D^n of the nef and big divisor D on its associated
complete toric variety X, where n is the dimension of X.}
    require IsComplete(Variety(D)):
        "The variety associated to the divisor must be complete";
    require IsNef(D) and IsBig(D): "The divisor is not nef and big";
    return Volume(get_rational_polyhedron(D));
end intrinsic;

intrinsic GradedCone(D::DivTorElt) -> TorCon
{The graded cone of sections of multiples of the divisor D (i.e. integral points in i-th grading represent sections of i * D)}
    if not assigned D`h0_cone then
        X:=Variety(D);
        F:=Fan(X);
        D`h0_cone:=graded_cone_from_combinatorial_data(Rays(F),Weil(D),
                                                            PureRayIndices(F));
    end if;
    return D`h0_cone;
end intrinsic;

intrinsic Polyhedron(D::DivTorElt) -> TorPol
{The integral polyhedron whose integral points corresponds to sections of the divisor D}
    return IntegralPart(get_rational_polyhedron(D));
end intrinsic;

intrinsic HilbertCoefficient(D::DivTorElt,k::RngIntElt) -> RngIntElt
{The value h0(k*D) for the divisor D. The space of sections of D must be finite dimensional.}
    P:=get_rational_polyhedron(D);
    require IsPolytope(P):
        "Vector space of sections of the divisor is infinite dimensional";
    return EhrhartCoefficient(P,k);
end intrinsic;

intrinsic HilbertCoefficients(D::DivTorElt,l::RngIntElt) -> SeqEnum[RngIntElt]
{The first l+1 coefficients of the Hilbert series Hilb(D) for the divisor D (i.e. the values h0(0*D) up to and including h0(l*D)). The space of sections of D must be finite dimensional.}
    P:=get_rational_polyhedron(D);
    require IsPolytope(P):
        "Vector space of sections of the divisor is infinite dimensional";
    return EhrhartCoefficients(P,l);
end intrinsic;

intrinsic HilbertDeltaVector(D::DivTorElt) -> SeqEnum[RngIntElt]
{The Hilbert delta-vector for the divisor D. The space of sections of D must be finite dimensional.}
    P:=get_rational_polyhedron(D);
    require IsPolytope(P):
        "Vector space of sections of the divisor is infinite dimensional";
    return EhrhartDeltaVector(P);
end intrinsic;

intrinsic HilbertPolynomial(D::DivTorElt) -> SeqEnum[RngUPolElt]
{The Hilbert (quasi-)polynomial for the divisor D. The space of sections of D must be finite dimensional.}
    P:=get_rational_polyhedron(D);
    require IsPolytope(P):
        "Vector space of sections of the divisor is infinite dimensional";
    return EhrhartPolynomial(P);
end intrinsic;

intrinsic HilbertSeries(D::DivTorElt) ->FldFunRatUElt
{The rational generating function of Hilb(D) for the divisor D. The space of sections of D must be finite dimensional.}
    P:=get_rational_polyhedron(D);
    require IsPolytope(P):
        "Vector space of sections of the divisor is infinite dimensional";
    return EhrhartSeries(P);
end intrinsic;

intrinsic MovablePart(D::DivTorElt) -> DivTorElt
{The movable part of the divisor D}
    vertices:=Vertices(Polyhedron(D));
    return Divisor(Variety(D),[-Min([ray * point: point in vertices]) :
                                            ray in PureRays(Fan(Variety(D)))]);
end intrinsic;

intrinsic ResolveLinearSystem(D::DivTorElt) -> DivTorElt
{The toric variety X whose fan lives in the same lattice as the fan of the variety of D, such that X resolves the map given by the linear system of D}
    P:=Polyhedron(D);
    F1:=DualFan(P);
    F2:=ResolveFanMap(Fan(Variety(D)),F1);
    return ToricVariety(BaseField(Variety(D)),F2);
end intrinsic;

intrinsic ImageFan(D::DivTorElt) -> TorFan
{The dual fan to the rational polyhedron of sections. For complete varieties, this will give the fan of Proj of the ring of sections of positive powers of the divisor D.}
    P:=get_rational_polyhedron(D);
    require not IsEmpty(P):
        "Argument and its higher multiples have no non-zero sections.";
    F,phi:= DualFan(P);
    return F,phi;
end intrinsic;

intrinsic Proj(D::DivTorElt) -> TorVar, Map[TorLat,TorLat]
{Proj (as a toric variety) of the ring of sections of the divisor D. The map of underlying lattices which determines the map Variety(D) -> Proj(D) is also given.}
    if not assigned D`proj then
        P:=get_rational_polyhedron(D);
        require not IsEmpty(P):
            "Argument and its multiples have no non-zero sections.";
        F, phi:=ImageFan(D);
        if F eq Fan(Variety(D)) then
	     D`proj_lattice_map:=IdentityMap(Ambient(F));
             D`proj:=Variety(D);
        else
             D`proj_lattice_map:=phi;
             D`proj:=ToricVariety(BaseRing(Variety(D)),F);
        end if;
    end if;
    return D`proj, D`proj_lattice_map;
end intrinsic;

intrinsic RelativeProj(D::DivTorElt) -> TorFan
{The relative (sheaf) Proj of sections of the divisor D. If D is Q-Cartier, then the identity will be constructed; for non Q-Cartier divisors, a partial Q-factorialisation will be given.}
    if not assigned D`relative_proj then
        X:=Variety(D);
        if IsQCartier(D) then
            D`relative_proj:=X;
        else
            F:=Fan(X);
            weil:=Weil(D);
            conesF:=Cones(F);
            cone_indices_non_simplicial:=[Sort(Setseq(ci[i])) : i  in [1..#ci] |
                        not IsSimplicial(conesF[i])] where ci is ConeIndices(F);
            graded_cones:=[graded_cone_from_combinatorial_data(Rays(F),weil,
                                   cone) : cone in cone_indices_non_simplicial];
            polyhedrons:=[Polyhedron(C) : C in graded_cones];
            dual_fans:=[DualFan(P) : P in polyhedrons];
            cones:=&cat[Cones(FF): FF in dual_fans] cat
                                            [C : C in conesF | IsSimplicial(C)];
            remove_repetitions(~cones);
            rays:=&cat[MinimalRGenerators(C) : C in cones];
            remove_repetitions(~rays);
            raysF:=Rays(F);
            i:=1;
            while i le #raysF do
                j:=Index(rays, raysF[i]);
                if j eq 0 then
                    Remove(~raysF,i);
                else
                    Remove(~rays,j);
                    i+:=1;
                end if;
            end while;
            bool,new_fan:=construct_fan_from_rays(raysF cat rays,cones :
                                                               max_cones:=true);
            require bool: new_fan;
            D`relative_proj:=ToricVariety(BaseRing(X),new_fan);
        end if;
    end if;
    return D`relative_proj;
end intrinsic;

///////////////////////////////////////////////////////////////////////
// Riemann-Roch space
///////////////////////////////////////////////////////////////////////

intrinsic RiemannRochPolytope(D::DivTorElt) -> TorPol
{The Riemann-Roch space of the divisor D as a polytope in the monomial lattice of the underlying toric variety}
    return Polyhedron(D);
end intrinsic;

intrinsic RiemannRochBasis(D::DivTorElt) -> SeqEnum[RngMPolElt]
{A basis of the Riemann-Roch space of the divisor D as monomials in the Cox ring of the underlying toric variety}
    return [LatticeElementToMonomial(D,v) :
                                v in Points(get_rational_polyhedron(D))];
end intrinsic;

intrinsic RiemannRochDimension(D::DivTorElt) -> RngIntElt
{The dimension of the Riemann-Roch space of the divisor D}
    return NumberOfPoints(get_rational_polyhedron(D));
end intrinsic;

///////////////////////////////////////////////////////////////////////
// Monomials
///////////////////////////////////////////////////////////////////////

intrinsic MonomialsOfWeightedDegree(X::TorVar,d::ModEDElt)
    -> SeqEnum[RngMPolElt]
{The degree d monomials in the Cox ring of the toric variety X. If there are not finitely many monomials, then any monomial of the given degree can be obtained by multiplying by any product from the sequence MonomialsOfDegreeZero(X).}
    require IsField(BaseRing(X)): "Base ring must be a field";
    require Parent(d) cmpeq DivisorClassGroup(X):
        "Argument 2 must lie in the divisor class group of argument 1";
    D:=Representative(X,d:effective:=false);
    P:=CompactPart(Polyhedron(D));
    return [LatticeElementToMonomial(D,v) : v in Points(P)];
end intrinsic;

intrinsic MonomialsOfDegreeZero(X::TorVar) -> SeqEnum[RngMPolElt]
{The generators of monomials of degree 0 in the Cox ring of the toric variety X}
    require IsField(BaseRing(X)): "Base ring must be a field";
    D:=ZeroDivisor(X);
    C:=InfinitePart(Polyhedron(D));
    return [LatticeElementToMonomial(D,v) : v in ZGenerators(C)];
end intrinsic;

///////////////////////////////////////////////////////////////////////
// Intersection theory
///////////////////////////////////////////////////////////////////////

intrinsic IntersectionForm(X::TorVar,C::TorCon) -> TorLatElt
{The form on the Picard lattice of the toric variety X which defines the intersection form with the curve corresponding to the codimension one face C in the fan of X}
    require IsField(BaseRing(X)): "Base ring must be a field";
    i:=Index(get_curves(X),C);
    require i ne 0:
        "Argument 2 must be a codimension one face in the fan of argument 1";
    return intersection_form(X,i);
end intrinsic;

intrinsic IntersectionForms(X::TorVar) -> SeqEnum[TorLatElt]
{The sequence of forms on the Picard lattice of the toric variety X which define the intersection forms with all torus invariant curves}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return [Dual(PicardLattice(X)) | intersection_form(X,i) :
                                                      i in [1..#get_curves(X)]];
end intrinsic;
