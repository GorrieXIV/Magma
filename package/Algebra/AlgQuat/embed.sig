174,1
A,AlgAssVOrd,1,pMatrixRings
S,!!,,0,2,0,0,0,0,0,0,0,319,,0,0,215,,217,-38,-38,-38,-38,-38
S,InternalConjugatingElement,Finds a basis of elements nu such that nu^(-1)*alpha*nu = beta,0,2,0,0,0,0,0,0,0,18,,0,0,18,,18,-38,-38,-38,-38,-38
S,HasEmbedding,"Determine if there exists an embedding of the quadratic extension K into A; and if so and ComputeEmbedding is true, return an embedding; if not, return a witness place",0,2,0,0,0,0,0,0,0,17,,0,0,-24,,36,-1,-1,-38,-38,-38
S,IsSplittingField,"Determine if there exists an embedding of the quadratic extension K into A; and if so and ComputeEmbedding is true, return an embedding; if not, return a witness place",0,2,0,0,0,0,0,0,0,17,,0,0,-24,,36,-1,-1,-38,-38,-38
S,Embed,"Find an embedding of the quadratic extension K into A. The default algorithm ""NormEquation"" works by solving a conic (the algorithm for this does not involve solving a norm equation, in most cases) the other option Al:=""Search"" performs a brute-force search. The optional parameter Basis may be used to specify a Z-basis to be used for the search; otherwise, an LLL basis for a maximal order is used",0,2,0,0,0,0,0,0,0,17,,0,0,-24,,18,175,-38,-38,-38,-38
S,Embed,"Find an embedding of the quadratic order Oc into the quaternion order O. First, it finds an embedding of algebras K -> A, then conjugates into O; the optional parameters are passed to Embed(K, A)",0,2,0,0,0,0,0,0,0,435,,0,0,215,,436,175,-38,-38,-38,-38
S,QuadraticNormForm,"Returns the norm form as a quadratic form on the elements in B, with coefficients modulo the prime p if specified",1,0,1,82,0,18,1,0,0,0,0,0,0,0,82,,63,-38,-38,-38,-38,-38
S,InternalCriticalPrimes,Return the sequence of primes p such that mu is not in O_p,0,2,0,0,0,0,0,0,0,18,,0,0,435,,82,-38,-38,-38,-38,-38
S,PseudoMatrix,Returns an artificially constructed pseudobasis of O,0,1,0,0,0,0,0,0,0,19,,438,-38,-38,-38,-38,-38
S,InternalCriticalValuation,Returns the valuation e needed to conjugate mu into O at p,0,3,0,0,0,0,0,0,0,217,,0,0,18,,0,0,435,,148,-38,-38,-38,-38,-38
S,InternalCriticalValuation,Returns the valuation e needed to conjugate mu into O at p,0,3,0,0,0,0,0,0,0,148,,0,0,18,,0,0,19,,148,-38,-38,-38,-38,-38
S,InternalConjugatingElement,Returns an element nu such that nu*mu*nu^(-1) is in O,0,2,0,0,0,0,0,0,0,18,,0,0,435,,36,18,-38,-38,-38,-38
S,InternalpConjugatingElement,Returns an element nu such that nu*mu*nu^(-1) is in O_p,0,3,0,0,0,0,0,0,0,217,,0,0,18,,0,0,435,,36,18,-38,-38,-38,-38
S,InternalpConjugatingElement,Returns an element nu such that nu*mu*nu^(-1) is in O_p,0,3,0,0,0,0,0,0,0,148,,0,0,18,,0,0,19,,36,18,-38,-38,-38,-38
S,pMatrixRing,"If p splits A, returns M_2(F_p), a map A -> M_2(F_p), and the embedding F -> F_p",1,0,1,17,1,27,0,262,2,0,0,0,0,0,0,0,217,,0,0,17,,176,175,175,-38,-38,-38
S,pMatrixRing,"If p splits A, returns M_2(F_p), a map A -> M_2(F_p), and the embedding F -> F_p",0,2,0,0,0,0,0,0,0,-45,,0,0,17,,176,175,175,-38,-38,-38
S,pMatrixRing,"If p splits O, returns M_2(F_p), a map A -> M_2(F_p) such that O |-> M_2(Z_F,p), and the embedding F -> F_p",1,0,1,435,1,215,0,319,2,0,0,0,0,0,0,0,217,,0,0,435,,176,175,175,-38,-38,-38
S,pMatrixRing,"Given a R-order in a quaternion algebra B over F, returns an embedding of B into M_2(F_p) which induces an isomorphism of O_p with M_2(R_p) or a suitable subring",0,2,0,0,0,0,0,0,0,-45,,0,0,19,,176,175,175,-38,-38,-38
S,pMatrixRing,Computes an embedding of B into M_2(Q_p) which induces an isomorphism of O_p with M_2(Z_p) or a suitable subring,1,0,1,19,0,319,2,0,0,0,0,0,0,0,319,,0,0,19,,176,175,175,-38,-38,-38
S,IsTriangulable,Returns a matrix m such that m*MM*m^-1 is contained in the algebra of upper triangluar matrices. All matrices must be 2x2 and defined over a field,1,0,1,176,0,-24,1,0,0,0,0,0,0,0,176,,36,177,-38,-38,-38,-38
