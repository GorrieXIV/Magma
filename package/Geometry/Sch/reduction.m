freeze;
///////////////////////////////////////////////////////////////////////////////////
///   Intrinsics to compute the reduction mod p of the flat closure of a        ///
///    scheme defined over a number field or the reduction of a divisor         ///
///                        on such a scheme.					///
///      Written by Martin Bright. Added to package library 11/13               ///
///////////////////////////////////////////////////////////////////////////////////

intrinsic Reduction(I::RngMPol, p::Any : parent := false) -> RngMPol
  { Given an ideal I in a graded polynomial ring over a number field and
  p, a place or a prime ideal of an order in that number field, compute the
  reduction of I mod p - that is, the defining ideal of the flat
  completion of the corresponding projective scheme. }

  RK := Generic(I);
  K := BaseRing(RK);
  if Type(K) eq FldRat then
    RZ := ChangeRing(RK,Integers());
    if ISA(Type(parent), RngMPol) then
      require BaseRing(parent) eq GF(p) : "parent should be a polynomial ring over GF(p)";
      R := parent;
    else
      require parent cmpeq false : "parent should be a polynomial ring";
      R := ChangeRing(RK,GF(p));
    end if;
    gens := [ RZ | ];
    // Clear denominators
    for f in Generators(I) do
      d := Gcd([Denominator(c) : c in Coefficients(f)]);
      Append(~gens, f*d);
    end for;
    // Make it flat at p by removing any extra components lying over p
    J := ideal< RZ | gens >;
    J := ColonIdeal(J, RZ!p); // actually does saturation, not colon ideal
    return ideal<R | Basis(J)>;
  else
    require ISA(Type(K), FldNum) : "Ideal must be over a number field";
    // Find the Hilbert polynomial of the ideal
    P := HilbertPolynomial(I);
    
    // Form the ambient ring over the residue field
    require (Type(p) cmpeq RngOrdIdl) or (Type(p) cmpeq PlcNumElt):
	"p should be a number field place or the prime ideal of an order";
    pi := UniformizingElement(p);
    if Type(p) cmpeq RngOrdIdl then
      F,m := ResidueClassField(p);
    else
      F := ResidueClassField(p);
      m := func<x|Evaluate(x,p)>; // the reduction mod p map
    end if;
    if ISA(Type(parent), RngMPol) then
      require BaseRing(parent) eq F : "Parameter `parent' should be a ring over the residue field";
      R := parent;
    else
      R := ChangeRing(RK,F);
    end if;
    
    // Now clear denominators
    gens := [ f/pi^v where v is Min([Valuation(c,p) : c in Coefficients(f)])
      : f in Basis(I) ];
    
    // Try reducing mod p, and see what we get
    pgens := [ R | ];
    for g in gens do
      C,M := CoefficientsAndMonomials(g);
      Append(~pgens, Polynomial( [m(c) : c in C], [R!x : x in M] ));
    end for;
    Ip := ideal<R | pgens>;
    // If it has the correct Hilbert polynomial, then our model is flat
    if HilbertPolynomial(Ip) eq P then
      return Ip;
    end if;
    
    // Otherwise, we need to do some saturation.  We can't do this
    // over the number ring, but we can do it over a p-adic residue
    // ring of sufficient precision.
    O := Order(p);
    Op,mp := Completion(O,p);
    pi := UniformizingElement(Op);
    
    // Find a starting precision - maximum valuation of the coefficients,
    // or 10, whichever is greater.
    prec := Max([ Max([ Valuation(c,p) : c in Coefficients(f)]) : f in gens ] cat [10] );
    // Maybe we should try for ever...
    for tries in [1..10] do
      // Form the quotient ring and base change everything
      S := quo< Op | pi^prec >;
      RS := ChangeRing(RK,S);
      Sgens := [RS | ];
      for f in gens do
	C,M := CoefficientsAndMonomials(f);
	Append(~Sgens, Polynomial( [S!mp(c) : c in C], [RS!x : x in M] ));
      end for;
      IS := ideal<RS|Sgens>;
      // TODO: is this identical to the previous F, or just isomorphic?
      F,q := ResidueClassField(S);
      // Take colon ideals until we get a flat model, or we run out
      // of precision
      for i in [1..prec] do
	IS := ColonIdeal(IS, ideal<RS|pi>);
	Fgens := [];
	for f in Basis(IS) do
	  C,M := CoefficientsAndMonomials(f);
	  Append(~Fgens, Polynomial( [q(c) : c in C], [R!x : x in M] ));
	end for;
	Ip := ideal<R | Fgens >;
	if HilbertPolynomial(Ip) eq P then
	  return Ip;
	end if;
      end for;
      // No luck - increase the precision
      prec +:= 10;
    end for;
    error "Couldn't find flat completion up to precision", prec-10;
  end if;
end intrinsic;

intrinsic Reduction(X::Sch, p::Any : ambient := false) -> Sch
  { Given a variety X over a number field and p, a place or prime ideal of
  an order in that number field, compute the reduction of X mod p.
  The optional parameter `ambient' specifies an ambient space over
  the residue field inside which the result should be returned.}
  
  K := BaseRing(X);
  if Type(K) eq FldRat then
    if ISA(Type(ambient), Sch) then
      require IsAmbient(ambient) : "Parameter `ambient' should be an ambient scheme";
      require BaseRing(ambient) eq GF(p) : "Parameter `ambient' should be over the residue field";
      Pp := ambient;
    else
      Pp := ChangeRing(Ambient(X), GF(p));
    end if;
  else
    require ISA(Type(K), FldNum) : "Variety must be defined over a number field";
    F := ResidueClassField(p);
    if ISA(Type(ambient), Sch) then
      require IsAmbient(ambient) : "Parameter `ambient' should be an ambient scheme";
      require BaseRing(ambient) eq F : "Parameter `ambient' should be over the residue field";
      Pp := ambient;
    else
      Pp := ChangeRing(Ambient(X),F);
    end if;
   end if;
  return Scheme(Pp, Reduction(Ideal(X), p : parent := CoordinateRing(Pp)));
end intrinsic;

// Given a divisor D on a scheme X defined over a number field, and
// a prime p, reduce D modulo p to get a divisor on (X mod p).  If
// parent is given, it should be the reduction of X mod p.
intrinsic Reduction(D::DivSchElt, p::Any : parent := false) -> DivSchElt
  { Compute the reduction of the D divisor modulo p.  D should be the divisor
   on a scheme defined over the rationals or a number field K, and p a prime
   or place of K or prime ideal in an order of K. If the reduction of the ambient
   variety mod p is already known, it can be given as parent. }

  if parent cmpeq false then
    Xp := Reduction(Variety(D),p);
  else
    require Type(parent) eq Sch : "parent should be a scheme";
    Xp := parent;
  end if;

  // The only subtlety here is that we need to intersect with X and
  // then reduce, rather than the other way round.
  IX := Ideal(Variety(D));
  R := CoordinateRing(Ambient(Xp));
  fact := IdealFactorisation(D);
  return &+[ x[2]*Divisor(Xp, Reduction(x[1]+IX, p : parent := R))
    : x in fact ];
end intrinsic;
