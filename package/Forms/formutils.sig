174,1
V,ExtendIsometry,3
V,PolarSpace,3
A,ModTupFld,2,Involution,hSplit
S,DotProduct,The inner product of u and v,0,2,0,0,0,0,0,0,0,160,,0,0,160,,-25,-38,-38,-38,-38,-38
S,ConjugateTranspose,The transpose of sigma(M),0,2,0,0,0,0,0,0,0,175,,0,0,-34,,-34,-38,-38,-38,-38,-38
S,DotProductMatrix,"The matrix of inner products of the vectors in S, taking into account any attached field automorphism",1,0,1,82,0,160,1,0,0,0,0,0,0,0,82,,177,-38,-38,-38,-38,-38
S,Discriminant,"The discriminant of the inner product space V; 0 if the determinant of the form is a square, 1 if a non-square",0,1,0,0,0,0,0,0,0,159,,148,-38,-38,-38,-38,-38
S,OrthogonalComplement,The (left) orthogonal complement of X in V,0,2,0,0,0,0,0,0,0,159,,0,0,159,,159,-38,-38,-38,-38,-38
S,Radical,The (left) radical of the inner product space V,0,1,0,0,0,0,0,0,0,159,,159,-38,-38,-38,-38,-38
S,IsNondegenerate,True iff the matrix of inner products of V is nonsingular,0,1,0,0,0,0,0,0,0,159,,36,-38,-38,-38,-38,-38
S,IsPolarSpace,Check if V is a quadratic space or the Gram matrix of V is a reflexive form,0,1,0,0,0,0,0,0,0,159,,36,-38,-38,-38,-38,-38
S,PolarSpaceType,The type of the polar space V,0,1,0,0,0,0,0,0,0,159,,36,-38,-38,-38,-38,-38
S,UnitarySpace,"The n-dimensional unitary space over the base ring F of J, where sigma is an automorphism of F of order 2 and where J is an n by n hermitian or skew-hermitian matrix with respect to sigma",0,2,0,0,0,0,0,0,0,175,,0,0,177,,159,-38,-38,-38,-38,-38
S,IsUnitarySpace,Test if the ambient space carries a form which is hermitian or skew-hermitian when restricted to W,0,1,0,0,0,0,0,0,0,159,,36,148,-38,-38,-38,-38
S,SymplecticSpace,The n-dimensional symplectic space over the base ring F of J; J must be alternating,0,1,0,0,0,0,0,0,0,177,,191,-38,-38,-38,-38,-38
S,IsSymplecticSpace,Test if the space carries an alternating form,0,1,0,0,0,0,0,0,0,159,,36,-38,-38,-38,-38,-38
S,IsPseudoSymplecticSpace,Test if the space carries a pseudo-alternating form,0,1,0,0,0,0,0,0,0,159,,36,-38,-38,-38,-38,-38
S,IsIsometry,True if the map f is an isometry from U to V with respect to the attached forms,0,3,0,0,0,0,0,0,0,175,,0,0,159,,0,0,159,,36,-38,-38,-38,-38,-38
S,IsIsometry,True if the map f is an isometry from its domain to its codomain,0,1,0,0,0,0,0,0,0,175,,36,-38,-38,-38,-38,-38
S,IsIsometry,True if g is an isometry of V with respect to the attached form,0,2,0,0,0,0,0,0,0,-34,,0,0,159,,36,-38,-38,-38,-38,-38
S,IsSimilarity,True if the map f is a similarity from U to V with respect to the attached forms,0,3,0,0,0,0,0,0,0,175,,0,0,159,,0,0,159,,36,-25,-38,-38,-38,-38
S,IsSimilarity,True if the map f is a similarity from its domain to its codomain,0,1,0,0,0,0,0,0,0,175,,36,-25,-38,-38,-38,-38
S,IsSimilarity,True if g is a similarity of V with respect to the attached form,0,2,0,0,0,0,0,0,0,-34,,0,0,159,,36,-25,-38,-38,-38,-38
S,IsTotallyIsotropic,True if the polar space V is totally isotropic,0,1,0,0,0,0,0,0,0,159,,36,-38,-38,-38,-38,-38
S,HasIsotropicVector,"Determine whether the polar space V contains an isotropic vector; if it does, assign a representative as the second return value",0,1,0,0,0,0,0,0,0,159,,36,160,-38,-38,-38,-38
S,HyperbolicPair,Extends a singular or isotropic vector u to a hyperbolic pair provided u is not in the radical,0,2,0,0,0,0,0,0,0,160,,0,0,159,,160,-38,-38,-38,-38,-38
S,HyperbolicSplitting,A maximal list of pairwise orthogonal hyperbolic pairs and a basis for the orthogonal complement of the subspace they span,0,1,0,0,0,0,0,0,0,159,,82,82,-38,-38,-38,-38
S,SymplecticBasis,"Given a polar space V, which is the direct sum of totally isotropic subspaces U and W, each of dimension m, return a symplectic basis e1, f1, e2, f2, ... for V such that e1, e2, ... is a basis for U and f1, f2, ... is a basis for W",0,3,0,0,0,0,0,0,0,159,,0,0,159,,0,0,159,,82,-38,-38,-38,-38,-38
S,IsIsometric,"Determine whether the polar spaces V1 and V2 are isometric; if they are, return an isometry (as a map)",0,2,0,0,0,0,0,0,0,159,,0,0,159,,36,175,-38,-38,-38,-38
S,IsSimilar,"Determine whether the polar spaces V1 and V2 are similar; if they are, return a similarity (as a map)",0,2,0,0,0,0,0,0,0,159,,0,0,159,,36,175,-38,-38,-38,-38
S,IsometryGroup,The group of isometries of the polar space V,0,1,0,0,0,0,0,0,0,159,,178,-38,-38,-38,-38,-38
S,SimilarityGroup,The group of similarities of the polar space V,0,1,0,0,0,0,0,0,0,159,,178,-38,-38,-38,-38,-38
S,WittDecomposition,"The Witt decomposition [R,P,N,D] of the space V such that V is the orthogonal sum of R, P+N and D where R is the radical, P+N is hyperbolic and D is anisotropic",0,1,0,0,0,0,0,0,0,159,,82,-38,-38,-38,-38,-38
S,WittIndex,The Witt index of the space V,0,1,0,0,0,0,0,0,0,159,,148,-38,-38,-38,-38,-38
S,MaximalTotallyIsotropicSubspace,A representative maximal totally isotropic subspace of the polar space V,0,1,0,0,0,0,0,0,0,159,,159,-38,-38,-38,-38,-38
S,CommonComplement,A common complement to the subspaces U1 and U2 in the vector space V. The subspaces must have the same dimension,0,3,0,0,0,0,0,0,0,159,,0,0,159,,0,0,159,,159,-38,-38,-38,-38,-38
S,ExtendIsometry,"An extension of the isometry f : U -> V to an isometry V -> V, where V carries a symplectic, unitary or quadratic form",0,3,0,0,0,0,0,0,0,175,,0,0,159,,0,0,159,,175,-38,-38,-38,-38,-38
S,WallForm,The space of the Wall form of the isometry f and its embedding in V,0,2,0,0,0,0,0,0,0,-34,,0,0,159,,159,175,-38,-38,-38,-38
S,GeneralisedWallForm,The space of the generalised Wall form of the similarity f and its embedding in V,0,2,0,0,0,0,0,0,0,-34,,0,0,159,,159,175,-38,-38,-38,-38
S,WallIsometry,"The inverse of WallForm: an isometry corresponding to the embedding mu : I -> V, where V is a quadratic, symplectic or unitary space",0,3,0,0,0,0,0,0,0,175,,0,0,159,,0,0,159,,-34,-38,-38,-38,-38,-38
