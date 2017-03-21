freeze;

/////////////////////////////////////////////////////////////////////////
// creation.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 36871 $
// $Date: 2012-01-10 09:04:42 +1100 (Tue, 10 Jan 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// The main intrinsics for creating toric varieties.
/////////////////////////////////////////////////////////////////////////

import "../lattice/lattice.m": lattice_from_cache;
import "../geometry/coxring.m": cox_ring_irrelevant_ideals;

declare attributes TorVar:
    Cox_ring;               // The Cox ring associated with X

/////////////////////////////////////////////////////////////////////////
// Data Store
/////////////////////////////////////////////////////////////////////////

// The data store for the cache of 0-dimensional toric varieties. Do not
// access directly!
tor_var_store:=NewStore();

intrinsic CacheClearToricVariety()
{Clear the internal toric variety cache}
    StoreClear(tor_var_store);
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Generic creation
/////////////////////////////////////////////////////////////////////////

intrinsic ToricVariety(k::Rng) -> TorVar
{The zero-dimensional toric variety over k}
    require IsField(k): "Argument must be a field";
    bool,zerodim_cache:=StoreIsDefined(tor_var_store,"0 dim cache");
    if not bool then
        zerodim_cache:=[PowerStructure(TorVar)|];
    end if;
    for X in zerodim_cache do
        if BaseRing(X) cmpeq k then
            return X;
        end if;
    end for;
    X:=ToricVariety(PolynomialRing(k,0),[],[],[]);
    X`Cox_ring:=CoxRing(k,ZeroFan(lattice_from_cache(0)));
    Append(~zerodim_cache,X);
    StoreSet(tor_var_store,"0 dim cache",zerodim_cache);
    return X;
end intrinsic;

intrinsic ToricVariety(R::RngMPol,I::SeqEnum[RngMPol],
    Z::SeqEnum[SeqEnum[RngIntElt]]) -> TorVar
{The toric variety with irrelevant ideal defined by I and gradings Z}
    // Sanity check
    require &and[II subset R : II in I]:
        "The components of the irrelevant ideal must lie in the polynomial ring";
    require &and[#ZZ eq Rank(R) : ZZ in Z]:
        "The gradings must be of length equal to the rank of the polynomial ring";
    require IsField(BaseRing(R)): "The base ring must be a field";
    // Return the toric variety
    return ToricVariety(R,I,Z,[PowerSequence(Rationals())|]);
end intrinsic;

intrinsic ToricVariety(C::RngCox) -> TorVar
{The toric variety associated with the Cox ring C}
    X:=ToricVariety(UnderlyingRing(C), cox_ring_irrelevant_ideals(C),
                                              Gradings(C), QuotientGradings(C));
    X`Cox_ring:=C;
    return X;
end intrinsic;

intrinsic ToricVariety(k::Rng, F::TorFan : positive:=true) -> TorVar
{The toric variety defined over k with fan F}
    require IsField(k): "Argument 1 must be a field";
    return ToricVariety(CoxRing(k,F : positive:=positive));
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Weighted and fake weighted projective space
/////////////////////////////////////////////////////////////////////////

// The following intrinsics all create P^n
intrinsic ToricVariety(k::Rng, n::RngIntElt) -> TorVar
{n-dimensional projective space over the field k, as a toric variety}
    require n gt 0: "The dimension must be a positive integer";
    require IsField(k): "Argument 1 must be a field";
    return ToricVariety(k,FanOfWPS([Integers() | 1 : i in [1..n + 1]]));
end intrinsic;

intrinsic ProjectiveSpaceAsToricVariety(k::Rng, n::RngIntElt) -> TorVar
{n-dimensional projective space over the field k, as a toric variety}
    require n gt 0: "The dimension must be a positive integer";
    require IsField(k): "Argument 1 must be a field";
    return ToricVariety(k,FanOfWPS([Integers() | 1 : i in [1..n + 1]]));
end intrinsic;

intrinsic WeightedProjectiveSpace(k::Rng, n::RngIntElt) -> TorVar
{n-dimensional projective space over the field k, as a toric variety}
    require n gt 0: "The dimension must be a positive integer";
    require IsField(k): "Argument 1 must be a field";
    return ToricVariety(k,FanOfWPS([Integers() | 1 : i in [1..n + 1]]));
end intrinsic;

intrinsic WPS(k::Rng, n::RngIntElt) -> TorVar
{n-dimensional projective space over the field k, as a toric variety}
    require n gt 0: "The dimension must be a positive integer";
    require IsField(k): "Argument 1 must be a field";
    return ToricVariety(k,FanOfWPS([Integers() | 1 : i in [1..n + 1]]));
end intrinsic;

// The following intrinsics all create P(w1,...,wn)
intrinsic ToricVariety(k::Rng, W::SeqEnum[RngIntElt]) -> TorVar
{The weighted projective space over the field k with weights W, as a toric variety}
    require #W ge 1: "Number of weights must be at least 2";
    require &and[w ge 0 : w in W]: "Weights must be non-negative";
    require IsField(k): "Argument 1 must be a field";
    return ToricVariety(k,FanOfWPS(W));
end intrinsic;

intrinsic ProjectiveSpaceAsToricVariety(k::Rng, W::SeqEnum[RngIntElt]) -> TorVar
{The weighted projective space over the field k with weights W, as a toric variety}
    require #W ge 1: "Number of weights must be at least 2";
    require &and[w ge 0 : w in W]: "Weights must be non-negative";
    require IsField(k): "Argument 1 must be a field";
    return ToricVariety(k,FanOfWPS(W));
end intrinsic;

intrinsic WeightedProjectiveSpace(k::Rng, W::SeqEnum[RngIntElt]) -> TorVar
{The weighted projective space over the field k with weights W, as a toric variety}
    require #W ge 1: "Number of weights must be at least 2";
    require &and[w ge 0 : w in W]: "Weights must be non-negative";
    require IsField(k): "Argument 1 must be a field";
    return ToricVariety(k,FanOfWPS(W));
end intrinsic;

intrinsic WPS(k::Rng, W::SeqEnum[RngIntElt]) -> TorVar
{The weighted projective space over the field k with weights W, as a toric variety}
    require #W ge 1: "Number of weights must be at least 2";
    require &and[w ge 0 : w in W]: "Weights must be non-negative";
    require IsField(k): "Argument 1 must be a field";
    return ToricVariety(k,FanOfWPS(W));
end intrinsic;

// The following intrinsics all create fake w.p.s.
intrinsic ToricVariety(k::Rng, W::SeqEnum[RngIntElt],
    Q::SeqEnum[SeqEnum[FldRatElt]]) -> TorVar
{The fake weighted projective space over the field k with the sequence of integer weights W and sequence of sequences of rational quotient weights Q, as a toric variety}
    require #W ge 1: "Number of weights must be at least 2";
    qq:={#q : q in Q}; 
    require #qq eq 1 and #W eq Representative(qq):
        "Weights must have the same length";
    require &and[w ge 0 : w in W]: "Weights must be non-negative";
    require IsField(k): "Argument 1 must be a field";
    return ToricVariety(k,FanOfFakeProjectiveSpace(W,Q));
end intrinsic;

intrinsic FakeProjectiveSpace(k::Rng, W::SeqEnum[RngIntElt],
    Q::SeqEnum[SeqEnum[FldRatElt]]) -> TorVar
{The fake weighted projective space over the field k with the sequence of integer weights W and sequence of sequences of rational quotient weights Q, as a toric variety}
    require #W ge 1: "Number of weights must be at least 2";
    qq:={#q : q in Q}; 
    require #qq eq 1 and #W eq Representative(qq):
        "Weights must have the same length";
    require &and[w ge 0 : w in W]: "Weights must be non-negative";
    require IsField(k): "Argument 1 must be a field";
    return ToricVariety(k,FanOfFakeProjectiveSpace(W,Q));
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Scrolls
/////////////////////////////////////////////////////////////////////////

intrinsic ToricVariety(k::Rng,M::SeqEnum[SeqEnum[RngIntElt]],
    v::SeqEnum[RngIntElt]) -> TorVar
{A rank 2 toric variety defined over the field k using data of a torus quotient: M is a sequence of two integer sequences of the same length (at least 4) whose columns generate a cone with vertex and v is an integer sequence of length 2 thought of as a column that lies in the interior of the cone in a strong sense.}
    // Sanity check
    require #M eq 2 and #M[1] ge 4 and #M[1] eq #M[2]:
        "Argument 1 must be a sequence containing two sequences of integers of the same length (at least 4)";
    require #v eq 2: "Argument 2 must be a sequence of exactly two integers";
    require IsField(k): "Argument 1 must be a field";
    // Build the Cox ring data
    N1:=lattice_from_cache(2);
    cols:=[N1 | PrimitiveLatticeVector(N1![M[1][i],M[2][i]]) : i in [1..#M[1]]];
    EffCone:=Cone(cols);
    bdy:=Rays(EffCone);
    intcols:=Remove(cols,Index(cols,bdy[1]));
    Remove(~intcols,Index(intcols,bdy[2]));
    MobCone:=Cone(intcols);
    // Check what we've built is sensible
    require Dimension(MobCone) eq 2:
        "The mobile cone implicit in the columns of argument 1 must be two dimensional";
    polarisation:=N1 ! v;
    require polarisation in MobCone and IsInInterior(polarisation,EffCone):
    	"Argument 2 must be in the mobile cone and in the strict interior of the effective cone implicit in the columns of argument 1";
    // In good shape - build that Cox ring
    n:=#M[1];
    R:=PolynomialRing(k,n);
    coneleft:=Cone([bdy[1],polarisation]);
    coneright:=Cone([polarisation,bdy[2]]);
    Bleft:=[R.i : i in [1..#cols] | cols[i] in coneleft];
    Bright := [R.i : i in [1..#cols] | cols[i] in coneright];
    B:=[Bleft,Bright];
    CR:=CoxRing(R,B,M,[]);
    CR`is_toric:=true;
    return ToricVariety(CR);
end intrinsic;

intrinsic HirzebruchSurface(k::Fld,n::RngIntElt) -> TorVar
{The Hirzebruch surface F_n defined over the field k}
    require IsField(k): "Argument 1 must be a field";
    require n ge 0: "Argument 2 must be a non-negative integer";
    return ToricVariety(k,[[1,1,0,-n],[0,0,1,1]],[1,1]);
end intrinsic;

intrinsic RuledSurface(k::Fld,a1::RngIntElt,a2::RngIntElt) -> TorVar
{The rational ruled surface over k with gradings [1, 1, -a1, -a2] and [0, 0, 1, 1]}
    require IsField(k): "Argument 1 must be a field";
    require a1 ge 0: "Argument 2 must be a non-negative integer";
    require a2 ge 0: "Argument 3 must be a non-negative integer";
    wts := [ [1,1,-a1,-a2], [0,0,1,1] ];
    R := PolynomialRing(k,4);
    B := [ Ideal([R.1,R.2]), Ideal([R.3,R.4]) ];
    return ToricVariety(R,B,wts);
end intrinsic;

intrinsic RuledSurface(k::Fld,n::RngIntElt) -> TorVar
{The rational ruled surface over k with negative section -n, or more precisely having the gradings [1, 1, -n, 0] and [0, 0, 1, 1] on four variables.}
    require IsField(k): "Argument 1 must be a field";
    require n ge 0: "Argument 2 must be a non-negative integer";
    wts := [ [1,1,-n,0], [0,0,1,1] ];
    R := PolynomialRing(k,4);
    B := [ Ideal([R.1,R.2]), Ideal([R.3,R.4]) ];
    return ToricVariety(R,B,wts);
end intrinsic;

intrinsic RationalScroll(k::Fld,s::RngIntElt,A::SeqEnum[RngIntElt]) -> TorVar
{The fibre bundle of projective r-spaces over projective s-space, where #A = [a0,...,ar] is a sequence of non-negative integers of length at least 2, that is Proj O(a0) + ... + O(ar).}
    require IsField(k): "Argument 1 must be a field";
    require s ge 1: "Argument 2 must be a positive integer";
    require #A ge 2: "Argument 3 must be a sequence of length at least two";
    wts1 := [ 1 : i in [1..s+1] ] cat [-a : a in A];
    wts2 := [ 0 : i in [1..s+1] ] cat [ 1 : i in [1..#A] ];
    return ToricVariety(k,[wts1,wts2],[1,1]);
end intrinsic;

intrinsic AbsoluteRationalScroll(k::Fld,S::SeqEnum[RngIntElt]) -> TorVar
{The #S-dimensional rational scroll over k with having gradings [1, 1] cat -S and [0, 0, 1, ..., 1]}
    require IsField(k): "Argument 1 must be a field";
    require &and[s ge 0 : s in S]:
        "Argument 2 must be a sequence of non-negative integers";
    N := #S;
    wts := [ [1,1] cat [-s : s in S], [0,0] cat [1 : i in [1..N]] ];
    R := PolynomialRing(k,2 + N);
    B := [ Ideal([R.1,R.2]), Ideal([R.(i + 2) : i in [1..N]]) ];
    return ToricVariety(R,B,wts);
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// More exotic creation
/////////////////////////////////////////////////////////////////////////

intrinsic Blowup(X::TorVar, v::TorLatElt) -> TorVar, TorMap
{The toric variety given by the blowup of the fan of the toric variety X at the toric lattice point v; also returns the map of the blowup.}
    require v in OneParameterSubgroupsLattice(X): 
        "Argument 2 must be in the 1-parameter subgroups lattice of argument 1";
    F:=Fan(X);
    F2:=Blowup(F,v);
    X2:=ToricVariety(BaseRing(X),F2);
    return X2, ToricVarietyMap(X2,X);
end intrinsic;
