174,1
A,GrpMat,3,ReeRecognitionData,ReeReductionData,ReeMaximals
V,ReeGeneral,10
S,RecogniseRee,"Constructively recognise G as a Ree group. If G is isomorphic to Ree(q) where q is the size of the defining field of G, then return: 1. Isomorphism from G to Ree(q). 2. Isomorphism from Ree(q) to G. 3. Map from G to the word group of G. 4. Map from the word group of G to G. The isomorphisms are composed of maps that are defined by rules, so Function can be used on each component. The word group is the GrpSLP which is the parent of the elements returned from ReeElementToWord. In general this is not the same as WordGroup(G), but is created from it using AddRedundantGenerators. If Verify is true, then it is checked that G really is isomorphic to Ree(q), otherwise this is not checked. In that case, the FieldSize must be set to the correct value of q",0,1,0,0,0,0,0,0,0,178,,36,175,175,175,175,-38
S,ReeResetRandomProcess,"G is isomorphic to Ree(q) and RecogniseRee(G) has returned true. Resets the random process used in the constructive membership, so that the SLPs are again short",0,1,0,0,0,0,0,0,0,178,,36,-38,-38,-38,-38,-38
S,RecognizeRee,See RecogniseRee,0,1,0,0,0,0,0,0,0,178,,36,175,175,175,175,-38
S,ReeElementToWord,"If G has been constructively recognised as a Ree group, and if g is an element of G, then return GrpSLPElt from word group of G which evaluates to g, else false. This facilitates membership testing in G",0,2,0,0,0,0,0,0,0,180,,0,0,178,,36,137,-38,-38,-38,-38
S,ReeSLPCoercion,"Return the SLP coercion map, which is a homomorphism from the word group of G to WordGroup(G)",0,1,0,0,0,0,0,0,0,178,,175,-38,-38,-38,-38,-38
S,ReeRedundantSLPGenerators,"If G has been constructively recognised as a Ree group, return the extra generators in the word group of G",0,1,0,0,0,0,0,0,0,178,,82,-38,-38,-38,-38,-38
S,Ree,|F| = 3^(2m + 1) with m > 0. Return Ree(F) on its standard generators,0,1,0,0,0,0,0,0,0,84,,178,-38,-38,-38,-38,-38
S,ReeGroup,|F| = 3^(2m + 1) with m > 0. Return Ree(F) on its standard generators,0,1,0,0,0,0,0,0,0,84,,178,-38,-38,-38,-38,-38
S,Ree,q = 3^(2m + 1) with m > 0. Return Ree(q) on its standard generators,0,1,0,0,0,0,0,0,0,148,,178,-38,-38,-38,-38,-38
S,ReeGroup,q = 3^(2m + 1) with m > 0. Return Ree(q) on its standard generators,0,1,0,0,0,0,0,0,0,148,,178,-38,-38,-38,-38,-38
S,Ree,"Given a 7-dimensional vector space V over the finite field GF(q), where q = 3^(2m + 1) with m > 0, return Ree(V) on its standard generators",0,1,0,0,0,0,0,0,0,191,,178,-38,-38,-38,-38,-38
S,ReeGroup,"Given a 7-dimensional vector space V over the finite field GF(q), where q = 3^(2m + 1) with m > 0, return Ree(V) on its standard generators",0,1,0,0,0,0,0,0,0,191,,178,-38,-38,-38,-38,-38
S,ReeGeneralRecogniser,Monte-Carlo check if G is isomorphic to Ree(q). Also returns q,0,1,0,0,0,0,0,0,0,178,,36,148,-38,-38,-38,-38
S,IsReeGroup,See ReeRecognition,0,1,0,0,0,0,0,0,0,178,,36,148,-38,-38,-38,-38
S,ReeRecognition,"G leq GL(d, q). Determine (non-constructively) if G is isomorphic to Ree(q). The corresponding q is also returned. If G is in characteristic not 3 or has degree greater than 7, the Monte Carlo algorithm of LieType is used. If G has degree 7 and has characteristic 3, then a fast Las Vegas algorithm is used",0,1,0,0,0,0,0,0,0,178,,36,148,-38,-38,-38,-38
S,ReeReduction,"G leq GL(d, q) is isomorphic to Ree(q). Compute explicit inverse isomorphisms to Ree(q). This is the Ree constructive recognition engine",0,1,0,0,0,0,0,0,0,178,,175,175,-38,-38,-38,-38
S,ReeConstructiveMembership,"G leq GL(d, q) is isomorphic to Ree(q) and g in GL(d, q). Determine if g in G and express g as SLP in generators of G",0,2,0,0,0,0,0,0,0,180,,0,0,178,,36,137,-38,-38,-38,-38
S,ReePermutationRepresentation,"G leq GL(d, q) and G is isomorphic to Ree(q). Returns an isomorphism to a permutation group on q^3 + 1 points as well as the permutation group itself. Only feasible for small q. Works only when q is an odd power of 3",0,1,0,0,0,0,0,0,0,178,,175,224,-38,-38,-38,-38
S,ReePointStabiliser,"G leq GL(d, q) and G is isomorphic to Ree(q). Returns generating set of a stabiliser of some point in the ovoid corresponding to G, SLPs of the generators in the generators of G, and the point that is stabilised. Only feasible for small q. Works only when q is an odd power of 3",0,1,0,0,0,0,0,0,0,178,,178,159,-38,-38,-38,-38
