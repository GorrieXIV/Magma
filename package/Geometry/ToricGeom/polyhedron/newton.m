freeze;

/////////////////////////////////////////////////////////////////////////
// newton.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 48810 $
// $Date: 2014-11-01 22:14:16 +1100 (Sat, 01 Nov 2014) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Tools for working with Newton polytopes and Laurent polynomials.
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Data Store
/////////////////////////////////////////////////////////////////////////
// Rather than add a new attribute to polynomials to keep track of the
// Newton polytopes, we keep a small cache of the past max_cache_size
// Newton polytopes that have been computed.
/////////////////////////////////////////////////////////////////////////

// The store for the temporary cache of Newton polytopes.
newton_store:=NewStore();
max_cache_size:=200;

// Clears the cache
procedure newton_clear_cache()
    StoreClear(newton_store);
end procedure;

// Returns (and bumps) the current cache stamp.
function newton_cache_stamp()
    bool,stamp:=StoreIsDefined(newton_store,"stamp");
    if not bool then stamp:=1; end if;
    StoreSet(newton_store,"stamp",stamp + 1);
    return stamp;
end function;

// Bumps the cache stamp for the given key.
procedure bump_newton_stamp(key)
    // First we bump the stamp
    stamp:=newton_cache_stamp();
    bool,polystamps:=StoreIsDefined(newton_store,"polystamps");
    if not bool then polystamps:=AssociativeArray(); end if;
    polystamps[key]:=stamp;
    // Now, if necessary, we refresh the stamps
    if stamp ge 32767 then
        keys:=SetToSequence(Keys(polystamps));
        curstamps:=[Integers() | polystamps[key] : key in keys];
        Sort(~curstamps,~perm);
        newstamps:=Eltseq(perm^-1);
        for i in [1..#keys] do
            polystamps[keys[i]]:=newstamps[i];
        end for;
        StoreSet(newton_store,"stamp",Max(newstamps) + 1);
    end if;
    // Update the cache
    StoreSet(newton_store,"polystamps",polystamps);
end procedure;

// Adds the given polytope to the cache.
procedure add_to_newton_cache(P,key)
    // Fetch the polytope cache
    bool,polys:=StoreIsDefined(newton_store,"polytopes");
    if not bool then polys:=AssociativeArray(); end if;
    // If there are too many polytopes in the cache, delete some
    if #Keys(polys) ge max_cache_size then
        // Recover the stamps
        bool,polystamps:=StoreIsDefined(newton_store,"polystamps");
        if not bool then polystamps:=AssociativeArray(); end if;
        // Calculate the entries to keep
        keys:=SetToSequence(Keys(polystamps) meet Keys(polys));
        stamps:=[Integers() | polystamps[k] : k in keys];
        ParallelSort(~stamps,~keys);
        start:=#keys - Floor(max_cache_size / 2);
        keys:=keys[start..#keys];
        // Update the stamps and polytopes
        newpolystamps:=AssociativeArray();
        newpolys:=AssociativeArray();
        for k in keys do
            newpolystamps[k]:=polystamps[k];
            newpolys[k]:=polys[k];
        end for;
        StoreSet(newton_store,"polystamps",newpolystamps);
        polys:=newpolys;
    end if;
    // Add this polytope to the cache
    polys[key]:=P;
    StoreSet(newton_store,"polytopes",polys);
    bump_newton_stamp(key);
end procedure;

// Returns true if there exists a cached polytope for the given vertex set,
// false otherwise. If true, bumps the count and returns the cached polytope.
function is_newton_cached(key)
    // Recover the cache of Newton polytopes
    bool,polys:=StoreIsDefined(newton_store,"polytopes");
    if not bool then return false,_; end if;
    // Is the polytope there?
    bool,P:=IsDefined(polys,key);
    if bool then
        // It's there, so we bump the stamp for this polytope and return success
        bump_newton_stamp(key);
        return true,P;
    else
        // Not so lucky -- we'll hunt through the keys
        for k in Keys(polys) do
            if k subset key then
                P:=polys[k];
                if &and[v in P : v in ChangeUniverse(key,Ambient(P))] then
                    // Excellent -- we found it
                    bump_newton_stamp(k);
                    return true,P;
                end if;
            end if;
        end for;
        return false,_;
    end if;
end function;

// Fetches (or creates) the Newton polytope supported on the given sequence of
// exponents.
function newton_polytope(monos)
    // Maybe we're lucky
    key:={PowerSequence(Integers()) | Eltseq(v) : v in monos};
    bool,Q:=is_newton_cached(key);
    if bool then return Q; end if;
    // Nope -- we missed the cache
    // Create a polytope and add it to the cache
    P:=Polytope(monos);
    key:={PowerSequence(Integers()) | Eltseq(v) : v in Vertices(P)};
    add_to_newton_cache(P,key);
    // Return the polytope
    return P;
end function;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Given a sequence S of integers and a function field R, returns the
// corresponding monomial. Note: This assumes that the rank is compatible with
// the length of S.
function seq_to_monomial(R,S)
    m:=R ! 1;
    for i in [1..#S] do
        if S[i] gt 0 then
            m *:= R.i^S[i];
        elif S[i] lt 0 then
            m *:= 1/(R.i^-S[i]);
        end if;
    end for;
    return m;
end function;

// Returns a monomial in R with exponents given by pt. Note: This assumes that
// the rank is compatible with the dimension of the ambient lattice.
function point_to_monomial(R,pt)
    return seq_to_monomial(R,Eltseq(pt));
end function;

// Returns a sequence of coefficients, and a sequence of monomial exponents
// for the given Laurent polynomial.
function coefficients_and_exponents(f)
    coeffs,monos:=CoefficientsAndMonomials(Numerator(f));
    monos:=[PowerSequence(Integers()) | Exponents(m) : m in monos];
    d:=Coefficients(Denominator(f))[1];
    if not Denominator(f) in CoefficientRing(Parent(f)) then
        den:=Exponents(Monomials(Denominator(f))[1]);
        monos:=[PowerSequence(Integers()) |
                      [Integers() | m[i] - den[i] : i in [1..#m]] : m in monos];
    end if;
    coeffs:=[FieldOfFractions(Universe(coeffs)) | c / d : c in coeffs];
    return coeffs,monos;
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic IsLaurent( f::FldFunRatMElt ) -> BoolElt
{True iff the rational function can be regarded as a Laurent polynomial}
    return Denominator(f) in CoefficientRing(Parent(f)) or
           #Monomials(Denominator(f)) eq 1;
end intrinsic;

intrinsic NewtonPolytope( f::FldFunRatMElt : return_coeffs:=false )
    -> TorPol,SeqEnum
{The Newton polytope P of the rational function f (regarded as a Laurent polynomial). Set 'return_coeffs' to true to also return the coefficients associated with the points of P. The coefficients are placed in bijection with Sort(SetToSequence(Points(P))).}
    // Sanity check
    require IsLaurent(f): "The rational function must be a Laurent polynomial";
    require Type(return_coeffs) eq BoolElt:
        "The parameter 'return_coeffs' must be a boolean";
    // Get the degenerate case out of the way
    if IsZero(f) then
        R:=Parent(f);
        if return_coeffs then
            return EmptyPolyhedron(Rank(R)),[FieldOfFractions(BaseRing(R))|];
        else
            return EmptyPolyhedron(Rank(R)),_;
        end if;
    end if;
    // Extract the coefficients and exponents
    coeffs,monos:=coefficients_and_exponents(f);
    // Create the polytope
    P:=newton_polytope(monos);
    // Do we need to return the coefficients?
    if return_coeffs then
        // Reorder the coefficients as necessary
        ChangeUniverse(~monos,Ambient(P));
        pts:=Sort(SetToSequence(Points(P)));
        newcoeffs:=ZeroSequence(Universe(coeffs),#pts);
        for i in [1..#coeffs] do
            newcoeffs[Index(pts,monos[i])]:=coeffs[i];
        end for;
        // Return the polytope and coefficients
        return P,newcoeffs;
    else
        // Return the polytope
        return P,_;
    end if;
end intrinsic;

intrinsic PolytopeToLaurent( P::TorPol, coeffs::SeqEnum : sortpts:=false )
    -> FldFunRatMElt
{Interprets the polytope P as a Laurent polynomial with given coefficients. The coefficients should be in bijection with 'sortpts', which defaults to Sort(SetToSequence(Points(P))).}
    // Sanity check
    require IsPolytope(P) and IsIntegral(P):
        "The polyhedron must be an integral polytope";
    if sortpts cmpeq false then
        sortpts:=Sort(SetToSequence(Points(P)));
    else
        require Type(sortpts) eq SeqEnum and Universe(sortpts) eq Ambient(P):
            "Parameter 'sortpts' should be a sequence of distinct points in the polytope";
        tmp:=SequenceToSet(sortpts);
        require #tmp eq #sortpts and tmp subset Points(P):
            "Parameter 'sortpts' should be a sequence of distinct points in the polytope";
    end if;
    require #coeffs eq #sortpts:
        "The coefficients should be in bijective correspondence with the points";
    // Return the Laurent polynomial
    R:=FieldOfFractions(PolynomialRing(Universe(coeffs),Dimension(Ambient(P))));
    return &+[R | coeffs[i] * point_to_monomial(R,sortpts[i]) :
                                                        i in [1..#coeffs]];
end intrinsic;

// Alias for PointsToLaurent below
intrinsic LaurentPolynomial( ex::SeqEnum[TorLatElt], cs::SeqEnum )
    -> FldFunRatMElt
{The Laurent polynomial with coefficients 'cs' and exponents 'ex'}
    // Sanity check
    require #cs eq #ex:
        "Arguments 1 and 2 must be sequences of the same length";
    require not IsNull(ex) and not IsNull(cs): "Illegal null sequence";
    require IsIntegral(ex): "Argument 1 must be a sequence of integral points";
    // Return the Laurent polynomial
    R:=FieldOfFractions(PolynomialRing(Universe(cs),Dimension(Universe(ex))));
    return &+[R | cs[i] * point_to_monomial(R,ex[i]) : i in [1..#cs]];
end intrinsic;

intrinsic PointsToLaurent( ex::SeqEnum[TorLatElt], cs::SeqEnum )
    -> FldFunRatMElt
{The Laurent polynomial with coefficients 'cs' and exponents 'ex'}
    // Sanity check
    require #cs eq #ex:
        "Arguments 1 and 2 must be sequences of the same length";
    require not IsNull(ex) and not IsNull(cs): "Illegal null sequence";
    require IsIntegral(ex): "Argument 1 must be a sequence of integral points";
    // Return the Laurent polynomial
    R:=FieldOfFractions(PolynomialRing(Universe(cs),Dimension(Universe(ex))));
    return &+[R | cs[i] * point_to_monomial(R,ex[i]) : i in [1..#cs]];
end intrinsic;

intrinsic Monomial( F::FldFunRat, E::TorLatElt ) -> FldFunRatMElt
{}
    k:=Rank(F);
    require Dimension(Parent(E)) eq k:
        Sprintf("Argument 2 should lie in a toric lattice of dimension %o",k);
    require IsIntegral(E): "Argument 2 must be an integral lattice point";
    return point_to_monomial(F,E);
end intrinsic;

intrinsic Monomial( F::FldFunRat, E::SeqEnum[RngIntElt] ) -> FldFunRatMElt
{The monomial in F whose exponents are given by E}
    k:=Rank(F);
    require #E eq k: Sprintf("Sequence should have length %o",k);
    return seq_to_monomial(F,E);
end intrinsic;

intrinsic WriteNewtonPolytopeToPSFile( f::FldFunRatMElt, F::MonStgElt :
    scale:=1, lattice:="points", padding:=0, fontsize:=9, mark_origin:=true )
{Writes the Newton polygon of the rational function f (regarded as a Laurent polynomial) to a PostScript file F. Optional parameter 'lattice' can be used to select an output style for the lattice. Valid styles are "points", "grid", and "none".}
    // Sanity check
    require IsLaurent(f): "The rational function must be a Laurent polynomial";
    require (Type(scale) eq RngIntElt or Type(scale) eq FldReElt or
             Type(scale) eq FldRatElt) and scale gt 0:
        "Parameter 'scale' must be greater than zero";
    require Type(lattice) eq MonStgElt and lattice in {"points","grid","none"}:
        "Parameter 'lattice' must be one of \"points\", \"grid\", or \"none\"";
    require (Type(padding) eq RngIntElt and padding ge 0) or
            (Type(padding) eq SeqEnum and #padding eq 2 and
             Universe(padding) cmpeq Integers() and
             padding[1] ge 0 and padding[2] ge 0):
        "Parameter 'padding' must be a positive integer, or a sequence of two positive integers";
    require Type(fontsize) eq RngIntElt and fontsize gt 0:
        "Parameter 'fontsize' must be a positive integer";
    require Type(mark_origin) eq BoolElt:
        "Parameter 'mark_origin' must be a boolean";
    // Create the Newton polygon
    P:=NewtonPolytope(f);
    require IsPolytope(P) and Dimension(P) eq 2:
        "The Newton polytope must two dimensional";
    require IsMaximumDimensional(P):
        "The Newton polygon must be of maximum dimension in the ambient lattice";
    // Create the array of coefficients
    A:=AssociativeArray(Ambient(P));
    coeffs,monos:=coefficients_and_exponents(f);
    ChangeUniverse(~monos,Ambient(P));
    for i in [1..#coeffs] do
        if coeffs[i] ne 0 then
            A[monos[i]]:=coeffs[i];
        end if;
    end for;
    // Output the PS file
    WritePolytopeToPSFile( P, F : scale:=scale, lattice:=lattice,
        padding:=padding, point_labels:=A, fontsize:=fontsize,
        mark_origin:=mark_origin );
end intrinsic;
