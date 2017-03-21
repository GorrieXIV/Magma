174,1
A,TorVar,1,identity_map
T,TorMap,-,0
A,TorMap,13,domain,codomain,is_zero_seq,is_zero_cone,principals,pullback_of_principals,is_description_good,description,graph,is_regular,lattice_map,inverse,indeter_locus
S,Print,,0,2,0,0,1,0,0,0,0,298,,0,0,TorMap,,-38,-38,-38,-38,-38,-38
S,ToricVarietyMap,,1,2,1,82,0,RngMRadElt,3,0,0,0,0,0,0,0,82,,0,0,243,,0,0,243,,TorMap,-38,-38,-38,-38,-38
S,ToricVarietyMap,,1,2,1,82,0,63,3,0,0,0,0,0,0,0,82,,0,0,243,,0,0,243,,TorMap,-38,-38,-38,-38,-38
S,ToricVarietyMap,The map X -> Y with defining equations S,1,2,1,82,0,237,3,0,0,0,0,0,0,0,82,,0,0,243,,0,0,243,,TorMap,-38,-38,-38,-38,-38
S,ToricVarietyMap,,1,2,2,175,0,TorLat,0,TorLat,3,0,0,0,0,0,0,0,175,,0,0,243,,0,0,243,,TorMap,-38,-38,-38,-38,-38
S,ToricVarietyMap,"Rational map between toric varieties X1 --> X2 determined by phi on big torus. Fans of X and Y must live in the domain and codomain of phi respectively. If phi is not specified, it is assumed to be identity (so Fans of X and Y must live in the same lattice)",0,2,0,0,0,0,0,0,0,243,,0,0,243,,TorMap,-38,-38,-38,-38,-38
S,*,Composition of maps,0,2,0,0,0,0,0,0,0,TorMap,,0,0,TorMap,,TorMap,-38,-38,-38,-38,-38
S,ToricIdentityMap,The identity map of X,0,1,0,0,0,0,0,0,0,243,,TorMap,-38,-38,-38,-38,-38
S,AnyDescription,"If psi stores any description, returns this description. Otherwise calculates some description without bothering about quality",0,1,0,0,0,0,0,0,0,TorMap,,82,-38,-38,-38,-38,-38
S,CompleteDescription,Good (or complete) description of psi,0,1,0,0,0,0,0,0,0,TorMap,,82,-38,-38,-38,-38,-38
S,GoodDescription,Good (or complete) description of psi,0,1,0,0,0,0,0,0,0,TorMap,,82,-38,-38,-38,-38,-38
S,MonomialToCoxMonomialsLattice,,0,2,0,0,0,0,0,0,0,63,,0,0,243,,TorLatElt,-38,-38,-38,-38,-38
S,MonomialToCoxMonomialsLattice,Given a monomial on X returns the element in the Cox Monomials Lattice (dual to Ray Lattice) corresponding to f,0,2,0,0,0,0,0,0,0,237,,0,0,243,,TorLatElt,-38,-38,-38,-38,-38
S,BasisOfDegree0CoxMonomials,Returns a basis of the rational function field of X expressed in terms of lattice points of Cox monomials lattice,0,1,0,0,0,0,0,0,0,243,,82,-38,-38,-38,-38,-38
S,BasisOfRationalFunctionField,A basis of the rational function field of X expressed in terms of rational monomials of Cox Ring,0,1,0,0,0,0,0,0,0,243,,82,-38,-38,-38,-38,-38
S,UnderlyingToriMap,The map of the big tori of domain and codomain. The image of psi must not be contained in any toric stratum,0,1,0,0,0,0,0,0,0,TorMap,,TorMap,-38,-38,-38,-38,-38
S,Domain,The domain of psi,0,1,0,0,0,0,0,0,0,TorMap,,243,-38,-38,-38,-38,-38
S,Codomain,The codomain of psi,0,1,0,0,0,0,0,0,0,TorMap,,243,-38,-38,-38,-38,-38
S,IndeterminacyLocus,"Returns a sequence of schemes, whose union is the indeterminacy locus of psi",0,1,0,0,0,0,0,0,0,TorMap,,82,-38,-38,-38,-38,-38
S,IsRegular,Returns true iff psi is a regular map,0,1,0,0,0,0,0,0,0,TorMap,,36,-38,-38,-38,-38,-38
S,Inverse,"Inverse of psi, provided it is known",0,1,0,0,0,0,0,0,0,TorMap,,TorMap,-38,-38,-38,-38,-38
S,IsIdentity,true if psi is equal to identity map of some toric variety,0,1,0,0,0,0,0,0,0,TorMap,,36,-38,-38,-38,-38,-38
S,IsTorusInvariant,"True iff psi is described by monomials (without coefficients). Then also returns the underlying map of lattices. If any of the variables is pulled back to 0, then returns false",0,1,0,0,0,0,0,0,0,TorMap,,36,175,-38,-38,-38,-38
S,*,,0,2,0,0,0,0,0,0,0,63,,0,0,TorMap,,63,-38,-38,-38,-38,-38
S,*,,0,2,0,0,0,0,0,0,0,237,,0,0,TorMap,,237,-38,-38,-38,-38,-38
S,*,Pulls f back by map psi. f must be in the Cox ring of codomain of psi,0,2,0,0,0,0,0,0,0,RngMRadElt,,0,0,TorMap,,237,-38,-38,-38,-38,-38
S,Pullback,"D must be Q-Cartier. If psi is torus-invariant, then returns the pull-back of D by psi. Otherwise return a torus-invariant divisor, which is linearly equivalent to the pull-back of D. psi should be regular in codim 1, or otherwise, there will be component, which has unpredictable multiplicity",0,2,0,0,0,0,0,0,0,DivTorElt,,0,0,TorMap,,DivTorElt,-38,-38,-38,-38,-38
S,eq,Equality test for maps between Toric Varieties,0,2,0,0,0,0,0,0,0,TorMap,,0,0,TorMap,,36,-38,-38,-38,-38,-38
