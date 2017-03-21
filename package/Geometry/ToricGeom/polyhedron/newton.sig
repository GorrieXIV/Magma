174,1
S,IsLaurent,True iff the rational function can be regarded as a Laurent polynomial,0,1,0,0,0,0,0,0,0,237,,36,-38,-38,-38,-38,-38
S,NewtonPolytope,The Newton polytope P of the rational function f (regarded as a Laurent polynomial). Set 'return_coeffs' to true to also return the coefficients associated with the points of P. The coefficients are placed in bijection with Sort(SetToSequence(Points(P))),0,1,0,0,0,0,0,0,0,237,,TorPol,82,-38,-38,-38,-38
S,PolytopeToLaurent,"Interprets the polytope P as a Laurent polynomial with given coefficients. The coefficients should be in bijection with 'sortpts', which defaults to Sort(SetToSequence(Points(P)))",0,2,0,0,0,0,0,0,0,82,,0,0,TorPol,,237,-38,-38,-38,-38,-38
S,LaurentPolynomial,The Laurent polynomial with coefficients 'cs' and exponents 'ex',1,0,1,82,0,TorLatElt,2,0,0,0,0,0,0,0,82,,0,0,82,,237,-38,-38,-38,-38,-38
S,PointsToLaurent,The Laurent polynomial with coefficients 'cs' and exponents 'ex',1,0,1,82,0,TorLatElt,2,0,0,0,0,0,0,0,82,,0,0,82,,237,-38,-38,-38,-38,-38
S,Monomial,,0,2,0,0,0,0,0,0,0,TorLatElt,,0,0,239,,237,-38,-38,-38,-38,-38
S,Monomial,The monomial in F whose exponents are given by E,1,1,1,82,0,148,2,0,0,0,0,0,0,0,82,,0,0,239,,237,-38,-38,-38,-38,-38
S,WriteNewtonPolytopeToPSFile,"Writes the Newton polygon of the rational function f (regarded as a Laurent polynomial) to a PostScript file F. Optional parameter 'lattice' can be used to select an output style for the lattice. Valid styles are ""points"", ""grid"", and ""none""",0,2,0,0,1,0,0,0,0,298,,0,0,237,,-38,-38,-38,-38,-38,-38
