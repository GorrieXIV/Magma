174,1
V,WeilPolynomials,2
S,HasAllRootsOnUnitCircle,We check that all complex roots of the rational polynomial f are of absolute value 1. The computation is based on a resolvent construction and does not involve floating-point computations,0,1,0,0,0,0,0,0,0,312,,36,-38,-38,-38,-38,-38
S,FrobeniusTracesToWeilPolynomials,A list of all possible characteristic polynomials of degree 'deg' of the Frobenius x -> x^q on H^i computed from the Frobenius traces. If a factor of the polynomial is known it can be added as KnownFactor,0,4,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,0,0,82,,82,-38,-38,-38,-38,-38
S,WeilPolynomialToRankBound,Given a Weil polynomial f this routine counts the number of roots that are q*zeta for zeta a root of unity. This is an upper bound for the geometric Picard rank of a surface over F_q,0,2,0,0,0,0,0,0,0,148,,0,0,312,,148,-38,-38,-38,-38,-38
S,ArtinTateFormula,"Given a polynomial f that is the characteristic polynomial of the Frobenius on H^2 of a surface with given Hodge number h^2,0 over F_q, this function returns the arithmetic Picard rank and the value of #Br * discriminant for the surface, as predicted by the Artin-Tate conjecture",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,312,,148,148,-38,-38,-38,-38
S,WeilPolynomialOverFieldExtension,"Given a Weil polynomial f this returns a polynomial of the same degree, whose roots are the dth powers r^d of the roots r of f",0,2,0,0,0,0,0,0,0,148,,0,0,312,,312,-38,-38,-38,-38,-38
S,CheckWeilPolynomial,"Given a polynomial f this routine tests whether f satisfies several properties that must hold for the characteristic polynomial of the Frobenius on H^2 of a surface whose Hodge number h^{2,0} is h20. If the degree of the surface is specified, additional tests are done. (For information about the tests being done, set the verbose flag 'WeilPolynomials' to level 1)",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,312,,36,-38,-38,-38,-38,-38