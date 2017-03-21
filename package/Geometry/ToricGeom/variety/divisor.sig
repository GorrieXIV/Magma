174,1
A,TorVar,2,Pic_basis_representatives,divisor_group
T,DivTor,DivTorElt,1,DivSch
A,DivTor,4,variety,divisor_cache,curves,curves_intersection_forms
T,DivTorElt,-,1,DivSchElt
A,DivTorElt,9,divisor_group,weil,cartier,h0_cone,h0_polyhedron,is_ample,proj,proj_lattice_map,relative_proj
S,Print,Print the Divisor group G of a toric variety (to level l),0,2,0,0,1,0,0,0,0,298,,0,0,DivTor,,-38,-38,-38,-38,-38,-38
S,IsCoercible,Can the given element be coerced into the toric divisor group G,0,2,0,0,0,0,0,0,0,-1,,0,0,DivTor,,36,RngMRadElt,-38,-38,-38,-38
S,in,Is the given element a member of the toric divisor group G,0,2,0,0,0,0,0,0,0,DivTor,,0,0,-1,,36,-38,-38,-38,-38,-38
S,DivisorGroup,The divisor group of the toric variety X,0,1,0,0,0,0,0,0,0,243,,DivTor,-38,-38,-38,-38,-38
S,ToricVariety,The toric variety associated with the divisor group D,0,1,0,0,0,0,0,0,0,DivTor,,243,-38,-38,-38,-38,-38
S,eq,True iff G1 and G2 are the divisor group of the same toric variety,0,2,0,0,0,0,0,0,0,DivTor,,0,0,DivTor,,36,-38,-38,-38,-38,-38
S,PrintNamed,Output a description of the toric divisor D,0,3,0,0,1,0,0,0,0,298,,0,0,298,,0,0,DivTorElt,,-38,-38,-38,-38,-38,-38
S,Parent,The divisor group containing the divisor D,0,1,0,0,0,0,0,0,0,DivTorElt,,DivTor,-38,-38,-38,-38,-38
S,Hash,The hash value of the toric divisor,0,1,0,0,0,0,0,0,0,DivTorElt,,148,-38,-38,-38,-38,-38
S,Divisor,,1,1,1,82,0,148,2,0,0,0,0,0,0,0,82,,0,0,243,,DivTorElt,-38,-38,-38,-38,-38
S,Divisor,,1,1,1,82,0,267,2,0,0,0,0,0,0,0,82,,0,0,243,,DivTorElt,-38,-38,-38,-38,-38
S,Divisor,,1,1,1,82,0,148,2,0,0,0,0,0,0,0,82,,0,0,DivTor,,DivTorElt,-38,-38,-38,-38,-38
S,Divisor,The (Q-)Weil divisor on the toric variety X (or its divisor group G) whose multiplicity on i-th coordinate divisor is S[i],1,1,1,82,0,267,2,0,0,0,0,0,0,0,82,,0,0,DivTor,,DivTorElt,-38,-38,-38,-38,-38
S,Divisor,,0,2,0,0,0,0,0,0,0,148,,0,0,243,,DivTorElt,-38,-38,-38,-38,-38
S,Divisor,The Weil divisor on the toric variety X (or its divisor group G) given by the vanishing of the i'th coordinate,0,2,0,0,0,0,0,0,0,148,,0,0,DivTor,,DivTorElt,-38,-38,-38,-38,-38
S,Divisor,"If m is in the monomial lattice of the toric variety X, then gives the principal divisor on X coresponding to the monomial m. If m is a form on the ray lattice of X, then gives the Weil divisor corresponding to m",0,2,0,0,0,0,0,0,0,TorLatElt,,0,0,243,,DivTorElt,-38,-38,-38,-38,-38
S,Divisor,,0,2,0,0,0,0,0,0,0,63,,0,0,243,,DivTorElt,-38,-38,-38,-38,-38
S,Divisor,"The divisor D on the toric variety X defined by f. If f is monomial, then D is this divisor. If f is general, then D is linearly equivalent to f; more precisely, D is the divisor defined by the leading monomials of the numerator and denominator of f",0,2,0,0,0,0,0,0,0,-41,,0,0,243,,DivTorElt,-38,-38,-38,-38,-38
S,ZeroDivisor,The zero divisor on the toric variety X,0,1,0,0,0,0,0,0,0,243,,DivTorElt,-38,-38,-38,-38,-38
S,Representative,"If m is an element of the divisor class group of the toric variety X, then gives a divisor D on X whose class modulo linear equivalence is m. Unless the parameter 'effective' is set to false, D will be effective if possible",0,2,0,0,0,0,0,0,0,188,,0,0,243,,DivTorElt,-38,-38,-38,-38,-38
S,Representative,"If m is an element of the Picard lattice or divisor class lattice of the toric variety X, then gives a divisor D on X whose class modulo linear equivalence and torsion is m. Unless the parameter 'effective' is set to false, D will be effective if possible",0,2,0,0,0,0,0,0,0,TorLatElt,,0,0,243,,DivTorElt,-38,-38,-38,-38,-38
S,CanonicalDivisor,The canonical divisor of the toric variety X,0,1,0,0,0,0,0,0,0,243,,DivTorElt,-38,-38,-38,-38,-38
S,CanonicalClass,"The class of canonical divisor of the toric variety X in: the Picard lattice (if group:=""Pic"", default), X must be QGorenstein; the divisor class lattice (if group:=""Cl""); the divisor class group (if group:=""ClZ"")",0,1,0,0,0,0,0,0,0,243,,DivTorElt,-38,-38,-38,-38,-38
S,+,The sum of two divisors D1 and D2,0,2,0,0,0,0,0,0,0,DivTorElt,,0,0,DivTorElt,,DivTorElt,-38,-38,-38,-38,-38
S,*,,0,2,0,0,0,0,0,0,0,DivTorElt,,0,0,148,,DivTorElt,-38,-38,-38,-38,-38
S,*,The multiple n * D,0,2,0,0,0,0,0,0,0,DivTorElt,,0,0,267,,DivTorElt,-38,-38,-38,-38,-38
S,-,The negation of D,0,1,0,0,0,0,0,0,0,DivTorElt,,DivTorElt,-38,-38,-38,-38,-38
S,-,The difference of two divisors D1 and D2,0,2,0,0,0,0,0,0,0,DivTorElt,,0,0,DivTorElt,,DivTorElt,-38,-38,-38,-38,-38
S,*,"Given a Q-Cartier divisor D, evaluates the piecewise linear function corresponding to D at v",0,2,0,0,0,0,0,0,0,TorLatElt,,0,0,DivTorElt,,148,-38,-38,-38,-38,-38
S,Variety,The toric variety where the divisor D is defined,0,1,0,0,0,0,0,0,0,DivTorElt,,243,-38,-38,-38,-38,-38
S,Weil,The element in the ray lattice defining the given Q-Weil divisor D,0,1,0,0,0,0,0,0,0,DivTorElt,,TorLatElt,-38,-38,-38,-38,-38
S,Cartier,The sequence of vectors in the monomial lattice whose i-th element corresponds to the i-th cone of the underlying fan. The divisor D must be Q-Cartier,0,1,0,0,0,0,0,0,0,DivTorElt,,82,-38,-38,-38,-38,-38
S,IsWeil,True iff the divisor D is Weil,0,1,0,0,0,0,0,0,0,DivTorElt,,36,-38,-38,-38,-38,-38
S,IsQCartier,"True iff the divisor D is Q-Cartier, and if so, also return the Cartier index of D",0,1,0,0,0,0,0,0,0,DivTorElt,,36,148,-38,-38,-38,-38
S,IsCartier,True iff the divisor D is Cartier,0,1,0,0,0,0,0,0,0,DivTorElt,,36,-38,-38,-38,-38,-38
S,IsZero,True iff the divisor D is the trivial divisor,0,1,0,0,0,0,0,0,0,DivTorElt,,36,-38,-38,-38,-38,-38
S,IsQPrincipal,True iff any multiple of the divisor D is a principal divisor,0,1,0,0,0,0,0,0,0,DivTorElt,,36,-38,-38,-38,-38,-38
S,IsPrincipal,"True iff the divisor D is a principal divisor, in which case a rational function f for which D = div(f) is returned as a second value",0,1,0,0,0,0,0,0,0,DivTorElt,,36,-41,-38,-38,-38,-38
S,IsEffective,True iff D is an effective divisor,0,1,0,0,0,0,0,0,0,DivTorElt,,36,-38,-38,-38,-38,-38
S,IsLinearlyEquivalentToCartier,"True iff the divisor D is Q-linearly equivalent a Cartier divisor. If true, then an equivalent Cartier divisor is also given",0,1,0,0,0,0,0,0,0,DivTorElt,,36,DivTorElt,-38,-38,-38,-38
S,eq,True iff the divisors D and E are equal,0,2,0,0,0,0,0,0,0,DivTorElt,,0,0,DivTorElt,,36,-38,-38,-38,-38,-38
S,AreLinearlyEquivalent,"True iff the difference of the divisors D and E is principal, in which case a rational function f for which D = E + div(f) is returned as a second value",0,2,0,0,0,0,0,0,0,DivTorElt,,0,0,DivTorElt,,36,-38,-38,-38,-38,-38
S,IsLinearlyEquivalent,"True iff the difference of the divisors D and E is principal, in which case a rational function f for which D = E + div(f) is returned as a second value",0,2,0,0,0,0,0,0,0,DivTorElt,,0,0,DivTorElt,,36,-41,-38,-38,-38,-38
S,LinearlyEquivalentDivisorWithNoSupportOn,"A divisor linearly equivalent to D, with no support on the locus defined by S. S should be a sequence of variables on the variety of D. If S has more than just variables, the other polynomials will be ignored",1,1,1,82,0,63,2,0,0,0,0,0,0,0,82,,0,0,DivTorElt,,DivTorElt,-38,-38,-38,-38,-38
S,DefiningMonomial,The monomial (if D is effective) or rational monomial defining the divisor D,0,1,0,0,0,0,0,0,0,DivTorElt,,63,-38,-38,-38,-38,-38
S,LatticeElementToMonomial,"The monomial corresponding to v with respect to the Weil divisor D (i.e. the monomial defining D + (v), where (v) is the principal divisor corresponding to v). v must be an integral element of the monomial lattice of the variety associated with D",0,2,0,0,0,0,0,0,0,TorLatElt,,0,0,DivTorElt,,63,-38,-38,-38,-38,-38
S,IsAmple,True iff the divisor D is ample,0,1,0,0,0,0,0,0,0,DivTorElt,,36,-38,-38,-38,-38,-38
S,IsNef,True iff the divisor D is nef,0,1,0,0,0,0,0,0,0,DivTorElt,,36,-38,-38,-38,-38,-38
S,IsBig,True iff the divisor D is big,0,1,0,0,0,0,0,0,0,DivTorElt,,36,-38,-38,-38,-38,-38
S,PicardClass,The class in the Picard lattice corresponding to the Q-Cartier divisor D,0,1,0,0,0,0,0,0,0,DivTorElt,,TorLatElt,-38,-38,-38,-38,-38
S,Degree,"The degree D^n of the nef and big divisor D on its associated complete toric variety X, where n is the dimension of X",0,1,0,0,0,0,0,0,0,DivTorElt,,267,-38,-38,-38,-38,-38
S,GradedCone,The graded cone of sections of multiples of the divisor D (i.e. integral points in i-th grading represent sections of i * D),0,1,0,0,0,0,0,0,0,DivTorElt,,TorCon,-38,-38,-38,-38,-38
S,Polyhedron,The integral polyhedron whose integral points corresponds to sections of the divisor D,0,1,0,0,0,0,0,0,0,DivTorElt,,TorPol,-38,-38,-38,-38,-38
S,HilbertCoefficient,The value h0(k*D) for the divisor D. The space of sections of D must be finite dimensional,0,2,0,0,0,0,0,0,0,148,,0,0,DivTorElt,,148,-38,-38,-38,-38,-38
S,HilbertCoefficients,The first l+1 coefficients of the Hilbert series Hilb(D) for the divisor D (i.e. the values h0(0*D) up to and including h0(l*D)). The space of sections of D must be finite dimensional,0,2,0,0,0,0,0,0,0,148,,0,0,DivTorElt,,82,-38,-38,-38,-38,-38
S,HilbertDeltaVector,The Hilbert delta-vector for the divisor D. The space of sections of D must be finite dimensional,0,1,0,0,0,0,0,0,0,DivTorElt,,82,-38,-38,-38,-38,-38
S,HilbertPolynomial,The Hilbert (quasi-)polynomial for the divisor D. The space of sections of D must be finite dimensional,0,1,0,0,0,0,0,0,0,DivTorElt,,82,-38,-38,-38,-38,-38
S,HilbertSeries,The rational generating function of Hilb(D) for the divisor D. The space of sections of D must be finite dimensional,0,1,0,0,0,0,0,0,0,DivTorElt,,238,-38,-38,-38,-38,-38
S,MovablePart,The movable part of the divisor D,0,1,0,0,0,0,0,0,0,DivTorElt,,DivTorElt,-38,-38,-38,-38,-38
S,ResolveLinearSystem,"The toric variety X whose fan lives in the same lattice as the fan of the variety of D, such that X resolves the map given by the linear system of D",0,1,0,0,0,0,0,0,0,DivTorElt,,DivTorElt,-38,-38,-38,-38,-38
S,ImageFan,"The dual fan to the rational polyhedron of sections. For complete varieties, this will give the fan of Proj of the ring of sections of positive powers of the divisor D",0,1,0,0,0,0,0,0,0,DivTorElt,,TorFan,-38,-38,-38,-38,-38
S,Proj,Proj (as a toric variety) of the ring of sections of the divisor D. The map of underlying lattices which determines the map Variety(D) -> Proj(D) is also given,0,1,0,0,0,0,0,0,0,DivTorElt,,243,175,-38,-38,-38,-38
S,RelativeProj,"The relative (sheaf) Proj of sections of the divisor D. If D is Q-Cartier, then the identity will be constructed; for non Q-Cartier divisors, a partial Q-factorialisation will be given",0,1,0,0,0,0,0,0,0,DivTorElt,,TorFan,-38,-38,-38,-38,-38
S,RiemannRochPolytope,The Riemann-Roch space of the divisor D as a polytope in the monomial lattice of the underlying toric variety,0,1,0,0,0,0,0,0,0,DivTorElt,,TorPol,-38,-38,-38,-38,-38
S,RiemannRochBasis,A basis of the Riemann-Roch space of the divisor D as monomials in the Cox ring of the underlying toric variety,0,1,0,0,0,0,0,0,0,DivTorElt,,82,-38,-38,-38,-38,-38
S,RiemannRochDimension,The dimension of the Riemann-Roch space of the divisor D,0,1,0,0,0,0,0,0,0,DivTorElt,,148,-38,-38,-38,-38,-38
S,MonomialsOfWeightedDegree,"The degree d monomials in the Cox ring of the toric variety X. If there are not finitely many monomials, then any monomial of the given degree can be obtained by multiplying by any product from the sequence MonomialsOfDegreeZero(X)",0,2,0,0,0,0,0,0,0,188,,0,0,243,,82,-38,-38,-38,-38,-38
S,MonomialsOfDegreeZero,The generators of monomials of degree 0 in the Cox ring of the toric variety X,0,1,0,0,0,0,0,0,0,243,,82,-38,-38,-38,-38,-38
S,IntersectionForm,The form on the Picard lattice of the toric variety X which defines the intersection form with the curve corresponding to the codimension one face C in the fan of X,0,2,0,0,0,0,0,0,0,TorCon,,0,0,243,,TorLatElt,-38,-38,-38,-38,-38
S,IntersectionForms,The sequence of forms on the Picard lattice of the toric variety X which define the intersection forms with all torus invariant curves,0,1,0,0,0,0,0,0,0,243,,82,-38,-38,-38,-38,-38
