freeze;

import "../RingExt/extras.m": RingExtAbsoluteDiscriminant, RingExtDifferent,
				RingExtEltDifferent, RingExtIsAbsoluteOrder,
				RingExtIsInert, RingExtIsInertIdeal,
				RingExtIsRamified, RingExtIsRamifiedIdeal,
				RingExtIsSplit, RingExtIsSplitIdeal,
				RingExtIsTamelyRamified, 
				RingExtIsTamelyRamifiedIdeal, 
				RingExtIsTamelyRamifiedOrder,
				RingExtIsTotallyRamified,
				RingExtIsTotallyRamifiedIdeal,
				RingExtIsTotallyRamifiedOrder,
				RingExtIsTotallySplit, 
				RingExtIsTotallySplitIdeal,
				RingExtIsUnramified,
				RingExtIsUnramifiedIdeal,
				RingExtIsUnramifiedOrder,
				RingExtIsWildlyRamified,
				RingExtIsWildlyRamifiedIdeal,
				RingExtIsWildlyRamifiedOrder;

intrinsic AbsoluteDiscriminant(O::RngFunOrd) -> RngElt
{Computes the discrimant of O over the denominator ring}
    return RingExtAbsoluteDiscriminant(O);
end intrinsic;

intrinsic Basis(O::RngFunOrd, R::Rng) -> SeqEnum
{Returns the basis of O as elements of R}

    c, B := CanChangeUniverse(Basis(O), R);
    if (c) then
	return B;
    end if;

    require c : "Cannot coerce basis over given ring";
end intrinsic;

intrinsic Different(O::RngFunOrd) -> RngFunOrdIdl
{Returns the different of O}
    require RingExtIsAbsoluteOrder(O) or IsMaximal(CoefficientRing(O)) :
	"Coefficient ring must be maximal";
    return RingExtDifferent(O);
end intrinsic;

intrinsic Different(a::RngFunOrdElt) -> RngFunOrdElt
{Returns the different of a}
    return RingExtEltDifferent(a);
end intrinsic;

intrinsic IsAbsoluteOrder(O::RngFunOrd)->BoolElt
{Returns true if O is an extension of a polynomial ring or valuation ring}
    return RingExtIsAbsoluteOrder(O);
end intrinsic;

intrinsic IsInert(P::RngUPolElt, O::RngFunOrd) -> BoolElt
{Returns whether the prime P is inert in O}
    require IsPrime(P) : "Polynomial must be prime";
    require CoefficientRing(O) eq Parent(P) : 
		"Order must be an extension of the parent of the element";
    return RingExtIsInert(P, O);
end intrinsic;

intrinsic IsInert(P::RngValElt, O::RngFunOrd) -> BoolElt
{Returns whether P is inert in O}
    require Valuation(P) eq 1 : "Valuation ring element must have valuation 1";
    require IsIdentical(CoefficientRing(O), Parent(P)) : 
		"Order must be an extension of the parent of the element";
    return RingExtIsInert(P, O);
end intrinsic;

intrinsic IsInert(P::RngFunOrdIdl, O::RngFunOrd) -> BoolElt
{Returns whether P is inert in the extension O of its order}
    require IsPrime(P) : "Ideal must be prime";
    require IsMaximal(CoefficientRing(O)) : "Coefficient ring of the order must be maximal";
    require CoefficientRing(O) eq Order(P) : "Coefficient ring of the order must be the order of the ideal";
    return RingExtIsInert(P, O);
end intrinsic;

intrinsic IsInert(P::RngFunOrdIdl) -> BoolElt
{Returns  whether P is inert}
    require IsPrime(P) : "Ideal must be prime";
    return RingExtIsInertIdeal(P);
end intrinsic;

intrinsic IsRamified(P::RngUPolElt, O::RngFunOrd) -> BoolElt
{Returns whether P is ramified in O}
    require IsPrime(P) : "Polynomial must be prime";
    require CoefficientRing(O) eq Parent(P) : 
		"Order must be an extension of the parent of the element";
    return RingExtIsRamified(P, O);
end intrinsic;

intrinsic IsRamified(P::RngValElt, O::RngFunOrd) -> BoolElt
{Returns whether P is ramified in O}
    require Valuation(P) eq 1 : "Valuation ring element must have valuation 1";
    require IsIdentical(CoefficientRing(O), Parent(P)) : 
		"Order must be an extension of the parent of the element";
    return RingExtIsRamified(P, O);
end intrinsic;

intrinsic IsRamified(P::RngFunOrdIdl, O::RngFunOrd) -> BoolElt
{Returns whether P is ramified in the extension O of its order}
    require IsPrime(P) : "Ideal must be prime";
    require IsMaximal(CoefficientRing(O)) : "Coefficient ring of the order must be maximal";
    require CoefficientRing(O) eq Order(P) : "Coefficient ring of the order must be the order of the ideal";
    return RingExtIsRamified(P, O);
end intrinsic;

intrinsic IsRamified(P::RngFunOrdIdl) -> BoolElt
{Returns whether P is ramified}
    require IsPrime(P) : "Ideal must be prime";
    return RingExtIsRamifiedIdeal(P);
end intrinsic;

intrinsic IsSplit(P::RngFunOrdIdl) -> BoolElt
{Returns whether P splits over the base ring of its order}
    require IsPrime(P) : "Ideal must be prime";
    return RingExtIsSplitIdeal(P);
end intrinsic;

intrinsic IsSplit(P::RngFunOrdIdl, O::RngFunOrd) -> BoolElt
{Returns whether P splits in extension O of its order}
    require IsPrime(P) : "Ideal must be prime";
    require IsMaximal(BaseRing(O)) and BaseRing(O) cmpeq Order(P) : 
"The base ring of the order must be the order of the ideal and must be maximal";
    return RingExtIsSplit(P, O);
end intrinsic;

intrinsic IsSplit(P::RngUPolElt, O::RngFunOrd) -> BoolElt
{Returns whether P splits in O}
    require IsPrime(P) : "Polynomial must be prime";
    require BaseRing(O) eq Parent(P) : 
	    "The base ring of the order must be the parent of the polynomial";
    return RingExtIsSplit(P, O);
end intrinsic;

intrinsic IsSplit(P::RngValElt, O::RngFunOrd) -> BoolElt
{Returns whether P splits in O}
    require Valuation(P) eq 1 : "Element must have valuation 1";
    require IsIdentical(BaseRing(O), Parent(P)) : "The base ring of the order must be the parent of the element";
    return RingExtIsSplit(P, O);
end intrinsic;

intrinsic IsTamelyRamified(P::RngFunOrdIdl) -> BoolElt
{Returns whether P is tamely ramified over the base ring of its order}
    require IsPrime(P) : "Polynomial must be prime";
    return RingExtIsTamelyRamifiedIdeal(P);
end intrinsic;

intrinsic IsTamelyRamified(P::RngFunOrdIdl, O::RngFunOrd) -> BoolElt
{Returns whether P is tamely ramified in the extension O of its order}
    require IsPrime(P) : "Ideal must be prime";
    require IsMaximal(BaseRing(O)) and BaseRing(O) cmpeq Order(P) :
	"The base ring of the order must be maximal and equal to the order of the ideal";
    return RingExtIsTamelyRamified(P, O);
end intrinsic;

intrinsic IsTamelyRamified(P::RngUPolElt, O::RngFunOrd) -> BoolElt
{Returns whether P is tamely ramified in O}
    require IsPrime(P) : "Ideal must be prime";
    require BaseRing(O) eq Parent(P) : 
		"Base ring of the order must be the parent of the polynomial";
    return RingExtIsTamelyRamified(P, O);
end intrinsic;

intrinsic IsTamelyRamified(P::RngValElt, O::RngFunOrd) -> BoolElt
{Returns whether P is tamely ramified in O}
    require Valuation(P) eq 1 : "Element must have valuation 1";
    require IsIdentical(BaseRing(O), Parent(P)) : 
			"Base ring of order must be the parent of the element";
    return RingExtIsTamelyRamified(P, O);
end intrinsic;

intrinsic IsTamelyRamified(O::RngFunOrd) -> BoolElt
{Returns whether O is tamely ramified}
    require IsMaximal(O) : "Order must be maximal";
    return RingExtIsTamelyRamifiedOrder(O);
end intrinsic;

intrinsic IsTotallyRamified(P::RngFunOrdIdl) -> BoolElt
{Returns whether P is totally ramified over the base ring of its order}
    require IsPrime(P) : "The ideal must be prime";
    return RingExtIsTotallyRamifiedIdeal(P);
end intrinsic;

intrinsic IsTotallyRamified(P::RngFunOrdIdl, O::RngFunOrd) -> BoolElt
{Returns whether P is totally ramified in the extension O of its order}
    require IsPrime(P) : "The ideal must be prime";
    require IsMaximal(BaseRing(O)) and BaseRing(O) cmpeq Order(P) : 
    "Base ring of the order must be maximal and equal to the order of the ideal";
    return RingExtIsTotallyRamified(P, O);
end intrinsic;

intrinsic IsTotallyRamified(P::RngUPolElt, O::RngFunOrd) -> BoolElt
{Returns whether P is totally ramified in O}
    require IsPrime(P) : "Polynomial must be prime";
    require BaseRing(O) eq Parent(P) : 
	"Base ring of the order must be the parent of the polynomial";
    return RingExtIsTotallyRamified(P, O);
end intrinsic;

intrinsic IsTotallyRamified(P::RngValElt, O::RngFunOrd) -> BoolElt
{Returns whether P is totally ramified in O}
    require Valuation(P) eq 1 : "Element must have valuation 1";
    require IsIdentical(BaseRing(O), Parent(P)) : 
	"Base ring of the order must be the parent of the polynomial";
    return RingExtIsTotallyRamified(P, O);
end intrinsic;

intrinsic IsTotallyRamified(O::RngFunOrd) -> BoolElt
{Returns whether O is totally ramified}
    require IsMaximal(O) : "Order must be maximal";
    return RingExtIsTotallyRamifiedOrder(O);
end intrinsic;

intrinsic IsTotallySplit(P::RngFunOrdIdl) -> BoolElt
{Returns whether P splits totally over the base ring of its order}
    require IsPrime(P) : "Ideal must be prime";
    return RingExtIsTotallySplitIdeal(P);
end intrinsic;

intrinsic IsTotallySplit(P::RngFunOrdIdl, O::RngFunOrd) -> BoolElt
{Returns whether P splits totally in the extension O of its order}
    require IsPrime(P) : "Ideal must be prime";
    require IsMaximal(BaseRing(O)) and BaseRing(O) cmpeq Parent(P) : 
	"Base ring of the order must be maximal and the order of the ideal";
    return RingExtIsTotallySplit(P, O);
end intrinsic;

intrinsic IsTotallySplit(P::RngUPolElt, O::RngFunOrd) -> BoolElt
{Returns whether P splits totally in O}
    require IsPrime(P) : "Polynomial must be prime";
    require BaseRing(O) eq Parent(P) : 
	"Base ring of the order must be the parent of the polynomial";
    return RingExtIsTotallySplit(P, O);
end intrinsic;

intrinsic IsTotallySplit(P::RngValElt, O::RngFunOrd) -> BoolElt
{Returns whether P splits totally in O}
    require Valuation(P) eq 1 : "Element must have valuation 1";
    require IsIdentical(BaseRing(O), Parent(P)) : 
	"Base ring of the order must be the parent of the polynomial";
    return RingExtIsTotallySplit(P, O);
end intrinsic;

intrinsic IsUnramified(P::RngFunOrdIdl) -> BoolElt
{Returns whether P is unramified over the base ring of its order}
    require IsPrime(P) : "Ideal must be prime";
    return RingExtIsUnramifiedIdeal(P);
end intrinsic;

intrinsic IsUnramified(P::RngFunOrdIdl, O::RngFunOrd) -> BoolElt
{Returns whether P is unramified in the extension O of its order}
    require IsPrime(P) : "Ideal must be prime";
    require IsMaximal(BaseRing(O)) and BaseRing(O) cmpeq Order(P) :
    "Base ring of the order must be maximal and equal to the order of the ideal";
    return RingExtIsUnramified(P, O);
end intrinsic;

intrinsic IsUnramified(P::RngUPolElt, O::RngFunOrd) -> BoolElt
{Returns whether P is unramified in O}
    require IsPrime(P) : "Polynomial must be prime";
    require BaseRing(O) eq Parent(P) : 
	"Base ring of the order must be the parent of the polynomial";
    return RingExtIsUnramified(P, O);
end intrinsic;

intrinsic IsUnramified(P::RngValElt, O::RngFunOrd) -> BoolElt
{Returns whether P is unramified in O}
    require Valuation(P) eq 1 : "Element must have valuation 1";
    require IsIdentical(BaseRing(O), Parent(P)) : 
	"Base ring of the order must be the parent of the element";
    return RingExtIsUnramified(P, O);
end intrinsic;

intrinsic IsUnramified(O::RngFunOrd) -> BoolElt
{Returns whether O is unramified at the finite places if O is finite or the infinite places if O is infinite}
    require IsMaximal(O) : "Order must be maximal";
    return RingExtIsUnramifiedOrder(O);
end intrinsic;

intrinsic IsWildlyRamified(P::RngFunOrdIdl) -> BoolElt
{Returns whether P is wildly ramified over the base ring of its order}
    require IsPrime(P) : "Ideal must be prime";
    return RingExtIsWildlyRamifiedIdeal(P);
end intrinsic;

intrinsic IsWildlyRamified(P::RngFunOrdIdl, O::RngFunOrd) -> BoolElt
{Returns whether P is wildly ramified in the extension O of its order}
    require IsPrime(P) : "Ideal must be prime";
    require IsMaximal(BaseRing(O)) and BaseRing(O) cmpeq Order(P) : 
    "Base ring of order must be maximal and equal to the order of the ideal";
    return RingExtIsWildlyRamified(P, O);
end intrinsic;

intrinsic IsWildlyRamified(P::RngUPolElt, O::RngFunOrd) -> BoolElt
{Returns whether P is wildly ramified in O}
    require IsPrime(P) : "Polynomial must be prime";
    require BaseRing(O) eq Parent(P) : 
		"Base ring of the order must be the parent of the polynomial";
    return RingExtIsWildlyRamified(P, O);
end intrinsic;

intrinsic IsWildlyRamified(P::RngValElt, O:: RngFunOrd) -> BoolElt
{Returns whether P is wildly ramified in O}
    require Valuation(P) eq 1 : "Element must have valuation 1";
    require IsIdentical(BaseRing(O), Parent(P)) : 
		"Base ring of the order must be the parent of the element";
    return RingExtIsWildlyRamified(P, O);
end intrinsic;

intrinsic IsWildlyRamified(O::RngFunOrd) -> BoolElt
{Returns whether O is wildly ramified}
    require IsMaximal(O) : "Order must be maximal";
    return RingExtIsWildlyRamifiedOrder(O);
end intrinsic;

intrinsic Flat(e::FldFunElt) -> SeqEnum
{Returns the coefficients over the base field}
  l := [e];
  repeat
    l := &cat [ Eltseq(x) : x in l];
  until Type(l[1]) eq FldFunRatUElt;
  return l;
end intrinsic;

intrinsic Eltseq(e::FldFunElt, K::FldFunG) -> SeqEnum
{Returns the coefficients over K, K must occur as a coefficient field}
  l := [e];
  repeat
    l := &cat [ Eltseq(x) : x in l];
  until Parent(l[1]) eq K;
  return l;
end intrinsic;

intrinsic AbsoluteMinimalPolynomial(e::FldFunElt) -> RngUPolElt
  {The minimal polynomial of e over the rational function field}
    F := Parent(e);
    require IsFinite(Degree(F)) : "Element must belong to a finite degree extension";
    while Type(F) eq FldFun and IsFinite(Degree(F)) do
	F := CoefficientField(F);
    end while;
    return MinimalPolynomial(e, F);
end intrinsic;

intrinsic PseudoMatrix(M::Mtrx[RngFunOrd]) -> PMat
  {The pseudomatrix with trivial ideals and matrix M.}
  C := CoefficientRing(M);
  C := MaximalOrder(C);
  return PseudoMatrix([1*C : i in [1..Nrows(M)]], M);
end intrinsic;

intrinsic PseudoMatrix(M::Mtrx[FldFunOrd]) -> PMat
  {The pseudomatrix with trivial ideals and matrix M.}
  C := CoefficientRing(M);
  C := MaximalOrder(Order(C));
  return PseudoMatrix([1*C : i in [1..Nrows(M)]], M);
end intrinsic;

