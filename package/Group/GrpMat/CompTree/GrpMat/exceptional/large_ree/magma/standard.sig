174,1
V,LargeReeStandard,10
S,LargeRee,|F| = 2^(2m + 1) with m > 0. Return LargeRee(F) on its standard generators,0,1,0,0,0,0,0,0,0,84,,178,-38,-38,-38,-38,-38
S,LargeReeGroup,|F| = 2^(2m + 1) with m > 0. Return LargeRee(F) on its standard generators,0,1,0,0,0,0,0,0,0,84,,178,-38,-38,-38,-38,-38
S,LargeRee,q = 2^(2m + 1) with m > 0. Return LargeRee(q) on its standard generators,0,1,0,0,0,0,0,0,0,148,,178,-38,-38,-38,-38,-38
S,LargeReeGroup,q = 2^(2m + 1) with m > 0. Return LargeRee(q) on its standard generators,0,1,0,0,0,0,0,0,0,148,,178,-38,-38,-38,-38,-38
S,LargeRee,"Given a 26-dimensional vector space V over the finite field GF(q), where q = 2^(2m + 1) with m > 0, return LargeRee(V) on its standard generators",0,1,0,0,0,0,0,0,0,191,,178,-38,-38,-38,-38,-38
S,LargeReeGroup,"Given a 26-dimensional vector space V over the finite field GF(q), where q = 2^(2m + 1) with m > 0, return LargeRee(V) on its standard generators",0,1,0,0,0,0,0,0,0,191,,178,-38,-38,-38,-38,-38
S,LargeReeIrreducibleRepresentation,"F has size q = 2^(2 * m + 1), m > 0, and twists is a sequence of distinct pairs of integers [i, j], where i is in [26, 246, 4096] and j is in the range [0 .. 2m]. Return an absolutely irreducible representation of BigRee(q), a tensor product of twisted powers of the basic representations of dimensions 26, 246 and 4096, where the twists are given by the input sequence",1,1,1,82,1,82,0,148,2,0,0,0,0,0,0,0,82,,0,0,84,,178,-38,-38,-38,-38,-38
S,LargeReeDiagonalisation,Diagonalise g of split torus type in LargeRee(q). Return diagonal matrix and change of basis matrix,0,1,0,0,0,0,0,0,0,180,,180,180,-38,-38,-38,-38
S,LargeReeInvolutionClass,Return the conjugacy class (2A or 2B) of the involution g in a conjugate of LargeRee(q),0,1,0,0,0,0,0,0,0,180,,298,-38,-38,-38,-38,-38
S,IsValidLargeReeOrder,"Returns true if LargeRee(q) has an element of order o, false otherwise",0,2,0,0,0,0,0,0,0,148,,0,0,148,,36,-38,-38,-38,-38,-38
S,LargeReeStandardMembership,Non-explicit membership test for LargeRee(q),0,1,0,0,0,0,0,0,0,180,,36,-38,-38,-38,-38,-38
S,LargeReeStandardRecogniser,"G leq GL(26, q). Determine (non-constructively) if G = LargeRee(q)",0,1,0,0,0,0,0,0,0,178,,36,-38,-38,-38,-38,-38
S,GeneralReeTorusElement,return general torus element of 2F4 in dimension 26,0,3,0,0,0,0,0,0,0,-1,,0,0,-1,,0,0,148,,180,-38,-38,-38,-38,-38
S,StandardGeneratorsForLargeRee,return list of standard generators for 2F4(q) where q = 2^(2m + 1),0,1,0,0,0,0,0,0,0,148,,82,-38,-38,-38,-38,-38
S,calculateBigReeTwistingMapCBMs,Calculate the necessary change of basis matrices for the twisting map. Print out as indices of positive coordinates in corresponding Hom-spaces,0,1,0,0,0,0,0,0,0,148,,-1,-38,-38,-38,-38,-38
S,calculateAlbertAlgebra,Calculate and print Albert algebra multiplication table of standard Big Ree copy,0,1,0,0,0,0,0,0,0,148,,-1,-38,-38,-38,-38,-38
