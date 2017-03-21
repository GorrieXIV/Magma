174,1
A,GrpMat,5,RandomProcess,SuzukiRecognitionData,SuzukiReductionData,SuzukiStandardGenerators,SuzukiMaximals
V,SuzukiGeneral,10
S,RecogniseSz,"G is absolutely irreducible and defined over minimal field. Constructively recognise G as a Suzuki group. If G is isomorphic to Sz(q) where q is the size of the defining field of G, then return: 1. Isomorphism from G to Sz(q). 2. Isomorphism from Sz(q) to G. 3. Map from G to the word group of G. 4. Map from the word group of G to G. The isomorphisms are composed of maps that are defined by rules, so Function can be used on each component. The word group is the GrpSLP which is the parent of the elements returned from SzElementToWord. In general this is not the same as WordGroup(G), but is created from it using AddRedundantGenerators. If Verify is true, then it is checked that G really is isomorphic to Sz(q), otherwise this is not checked. In that case, the FieldSize must be set to the correct value of q. Constructive recognition of 2.Sz(8) is also handled",0,1,0,0,0,0,0,0,0,178,,36,175,175,175,175,-38
S,SuzukiResetRandomProcess,"G is isomorphic to Sz(q) and RecogniseSz(G) has returned true. Resets the random process used in the constructive membership, so that the SLPs are again short",0,1,0,0,0,0,0,0,0,178,,36,-38,-38,-38,-38,-38
S,RecognizeSz,See RecogniseSz,0,1,0,0,0,0,0,0,0,178,,36,175,175,175,175,-38
S,SzElementToWord,"If G has been constructively recognised as a Suzuki group, and if g is an element of G, then return GrpSLPElt from word group of G which evaluates to g, else false. This facilitates membership testing in G",0,2,0,0,0,0,0,0,0,180,,0,0,178,,36,137,-38,-38,-38,-38
S,SzSLPCoercion,"Return the SLP coercion map, which is a homomorphism from the word group of G to WordGroup(G)",0,1,0,0,0,0,0,0,0,178,,175,-38,-38,-38,-38,-38
S,SzRedundantSLPGenerators,"If G has been constructively recognised as a Suzuki group, return the extra generators in the word group of G",0,1,0,0,0,0,0,0,0,178,,82,-38,-38,-38,-38,-38
S,SzPresentation,q = 2^(2m + 1) with m > 0. Return a presentation of Sz(q) on the Magma standard generators,0,1,0,0,0,0,0,0,0,148,,121,141,-38,-38,-38,-38
S,SzPresentation,#F = 2^(2m + 1) with m > 0. Return relations of Sz(F) on the standard generators,0,1,0,0,0,0,0,0,0,84,,82,-38,-38,-38,-38,-38
S,SatisfiesSzPresentation,G is constructively recognised as Sz(q). Verify that it satisfies a presentation for this group,0,2,0,0,0,0,0,0,0,148,,0,0,178,,36,-38,-38,-38,-38,-38
S,SatisfiesSzPresentation,G is constructively recognised as Sz(q) for some q. Verify that it satisfies a presentation for this group,0,1,0,0,0,0,0,0,0,178,,36,-38,-38,-38,-38,-38
S,SuzukiReduction,"G leq GL(d, q) is isomorphic to Sz(q). Compute explicit inverse isomorphisms to Sz(q). This is the Sz constructive recognition engine",0,1,0,0,0,0,0,0,0,178,,175,175,-38,-38,-38,-38
S,SuzukiConstructiveMembership,"G leq GL(d, q) is isomorphic to Sz(q) and g in GL(d, q). Determine if g in G and express g as SLP in generators of G",0,2,0,0,0,0,0,0,0,180,,0,0,178,,36,137,-38,-38,-38,-38
S,IsSuzukiGroup,See SuzukiRecognition,0,1,0,0,0,0,0,0,0,178,,36,148,-38,-38,-38,-38
S,SuzukiRecognition,"Determine (non-constructively) if G is isomorphic to Sz(q) for some q. The corresponding q is also returned. If G is in odd characteristic or has degree greater than 4, the Monte Carlo algorithm of LieType is used. If G has degree 4 and has characteristic 2, then a fast Las Vegas algorithm is used",0,1,0,0,0,0,0,0,0,178,,36,148,-38,-38,-38,-38
S,SuzukiGeneralRecogniser,Monte-Carlo check if G is isomorphic to Sz(q). Also returns q,0,1,0,0,0,0,0,0,0,178,,36,148,-38,-38,-38,-38
S,SuzukiStabiliser,"G leq GL(4, q) and G is a conjugate of Sz(q). P is in the ovoid w.r.t G. Returns list of generators for stabiliser of <P> in G. Each list entry is a tuple with two elements: an SLP for the generator and then the generator. Also returns the time spent in discrete logarithm computations",0,2,0,0,0,0,0,0,0,160,,0,0,178,,82,148,-38,-38,-38,-38
S,SuzukiPointStabiliser,"G leq GL(d, q) and G is isomorphic to Sz(q). Returns generating set of a stabiliser of some point in the ovoid corresponding to G, SLPs of the generators in the generators of G, and the point that is stabilised. Only feasible for small q. Does not work for odd q",0,1,0,0,0,0,0,0,0,178,,178,82,159,-38,-38,-38
S,SuzukiPermutationRepresentation,"G leq GL(d, q) and G is isomorphic to Sz(q). Returns an isomorphism to a permutation group on q^2 + 1 points as well as the permutation group itself. Also returns a stabiliser of a point. Only feasible for small q. Does not work for odd q",0,1,0,0,0,0,0,0,0,178,,175,224,224,-38,-38,-38
