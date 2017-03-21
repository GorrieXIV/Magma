174,1
A,AlgQuat,2,NormSpace,ExtensionField
A,AlgQuatOrd,4,ReducedMatrix,ReducedGram,NormSpace,LeftIdealBases
S,QuaternionAlgebra,"Same as QuaternionAlgebra<F|a,b>. This is the quaternion algebra over F spanned by 1,i,j and i*j satisfying i^2=a, j^2=b and i*j=-j*i",0,3,0,0,0,0,0,0,0,-45,,0,0,-45,,0,0,-24,,17,-38,-38,-38,-38,-38
S,QuaternionAlgebra,"Returns a rational quaternion algebra of discriminant N, where N is squarefree. If Al is set to ""Random"", then a faster, probablistic algorithm is used; if Al is set to ""TraceValues"", an algebra basis also gives a basis for a maximal order (of discriminant N)",0,1,0,0,0,0,0,0,0,148,,17,-38,-38,-38,-38,-38
S,QuaternionAlgebra,"Returns a quaternion algebra over F_q(x) of discriminant N, where N in F_q[x] is squarefree",0,1,0,0,0,0,0,0,0,312,,17,-38,-38,-38,-38,-38
S,MaximalOrder,A maximal quaternion order in K,1,0,1,17,0,262,1,0,0,0,0,0,0,0,17,,19,-38,-38,-38,-38,-38
S,MaximalOrder,A maximal quaternion order in K,1,0,1,17,0,239,1,0,0,0,0,0,0,0,17,,19,-38,-38,-38,-38,-38
S,MaximalOrder,A maximal quaternion order containing O,1,0,1,19,0,319,1,0,0,0,0,0,0,0,19,,19,-38,-38,-38,-38,-38
S,MaximalOrder,A maximal quaternion order containing O,1,0,1,19,0,311,1,0,0,0,0,0,0,0,19,,19,-38,-38,-38,-38,-38
S,QuaternionOrder,"Quaternion order generated by S, preserving S if it constitutes a basis with initial element 1",1,0,1,82,1,18,0,262,1,0,0,0,0,0,0,0,82,,19,-38,-38,-38,-38,-38
S,QuaternionOrder,"Quaternion order generated by S, preserving S if it constitutes a basis with initial element 1",1,0,1,82,1,18,0,239,1,0,0,0,0,0,0,0,82,,19,-38,-38,-38,-38,-38
S,QuaternionOrder,Returns a quaternion order of level M in K,1,0,1,17,0,262,2,0,0,0,0,0,0,0,148,,0,0,17,,19,-38,-38,-38,-38,-38
S,QuaternionOrder,Returns a maximal order in the rational quaternion algebra of discrinant N,0,1,0,0,0,0,0,0,0,148,,19,-38,-38,-38,-38,-38
S,QuaternionOrder,Returns a quaternion order of level M in the rational quaternion algebra of discrinant N,0,2,0,0,0,0,0,0,0,148,,0,0,148,,19,-38,-38,-38,-38,-38
S,Order,Returns an order of level Lvl in O. The level of O and Lvl must be coprime,0,2,0,0,0,0,0,0,0,-45,,0,0,19,,19,-38,-38,-38,-38,-38
S,NormSpace,The inner product space of A with respect to the norm,0,1,0,0,0,0,0,0,0,17,,156,175,-38,-38,-38,-38
S,NormSpace,The inner product subspace with respect to the norm generated by the sequence B,1,0,1,82,0,18,1,0,0,0,0,0,0,0,82,,159,175,-38,-38,-38,-38
S,NormSpace,The inner product module of A with respect to the norm,0,1,0,0,0,0,0,0,0,19,,191,175,-38,-38,-38,-38
S,NormModule,The inner product space of A with respect to the norm,0,1,0,0,0,0,0,0,0,19,,191,175,-38,-38,-38,-38
S,CharacteristicPolynomial,The characteristic polynomial of x,0,1,0,0,0,0,0,0,0,18,,312,-38,-38,-38,-38,-38
S,CharacteristicPolynomial,The characteristic polynomial of x,0,1,0,0,0,0,0,0,0,20,,312,-38,-38,-38,-38,-38
S,Coordinates,The coordinates of x with respect to the basis of its parent,0,1,0,0,0,0,0,0,0,18,,82,-38,-38,-38,-38,-38
S,Conductor,"The conductor of the quaternion order, defined to be the index in a maximal order of its quaternion algebra",0,1,0,0,0,0,0,0,0,19,,-45,-38,-38,-38,-38,-38
S,Level,The index of O in a maximal order,1,0,1,19,0,311,1,0,0,0,0,0,0,0,19,,312,-38,-38,-38,-38,-38
S,IsIsomorphic,True if A is isomorphic to B,0,2,0,0,0,0,0,0,0,17,,0,0,17,,36,-38,-38,-38,-38,-38
S,IsDefinite,"True if and only if K is ramified at infinity, where K must be a quaternion algebra over the rationals",1,0,1,17,0,262,1,0,0,0,0,0,0,0,17,,36,-38,-38,-38,-38,-38
S,IsDefinite,"True if and only if K is ramified at the infinite place, where K must be a quaternion algebra over F_q(X)",1,0,1,17,0,239,1,0,0,0,0,0,0,0,17,,36,-38,-38,-38,-38,-38
S,BasisMatrix,,0,1,0,0,0,0,0,0,0,19,,177,-38,-38,-38,-38,-38
S,ReducedBasis,"A Minkowski-reduced basis for I, unique up to isomorphism",1,0,1,344,0,319,1,0,0,0,0,0,0,0,344,,82,-38,-38,-38,-38,-38
S,ReducedBasis,A basis for I such that the Gram matrix is reduced. It is unique if the enveloping algebra is definite and Canonical is set,1,0,1,344,0,311,1,0,0,0,0,0,0,0,344,,82,-38,-38,-38,-38,-38
S,ReducedGramMatrix,A reduced Gram matrix of the quaternion ideal I. It is unique if the enveloping algebra is definite and Canonical is set,1,0,1,344,0,311,1,0,0,0,0,0,0,0,344,,177,82,-38,-38,-38,-38
S,ReducedBasis,"A Minkowski-reduced basis for A, unique up to isomorphism if A is definite",1,0,1,19,0,319,1,0,0,0,0,0,0,0,19,,82,-38,-38,-38,-38,-38
S,ReducedGramMatrix,A canonical Minkowski-reduced Gram matrix for the norm inner product on A,1,0,1,19,0,319,1,0,0,0,0,0,0,0,19,,177,-38,-38,-38,-38,-38
S,ReducedGramMatrix,A Gram matrix for the norminner product on O which is in dominant diagonal form. It is unique if O is definite and Canonical is set,1,0,1,19,0,311,1,0,0,0,0,0,0,0,19,,177,82,-38,-38,-38,-38
S,ReducedBasis,A basis B of O such that the Gram matrix for the norminner product w.r.t. B is in dominant diagonal form,1,0,1,19,0,311,1,0,0,0,0,0,0,0,19,,82,-38,-38,-38,-38,-38
S,LeftIdeal,Left ideal of A with generator sequence S,0,2,0,0,0,0,0,0,0,82,,0,0,19,,344,-38,-38,-38,-38,-38
S,RightIdeal,Right ideal of A with generator sequence S,0,2,0,0,0,0,0,0,0,82,,0,0,19,,344,-38,-38,-38,-38,-38
S,PrimeIdeal,The unique two-sided ideal over p,0,2,0,0,0,0,0,0,0,-45,,0,0,19,,344,-38,-38,-38,-38,-38
S,CommutatorIdeal,The ideal of A generated by elements of the form x*y - y*x,0,1,0,0,0,0,0,0,0,19,,344,-38,-38,-38,-38,-38
S,Units,The units in the quaternion order S over the integers,1,0,1,19,0,319,1,0,0,0,0,0,0,0,19,,82,-38,-38,-38,-38,-38
S,UnitGroup,A permutation group G isomorphic to the unit group of a definite quaternion order O over the integers. The second return value is a map G -> O^*,1,0,1,19,0,319,1,0,0,0,0,0,0,0,19,,224,175,-38,-38,-38,-38
S,pMaximalOrder,A p-maximal order containing O,0,2,0,0,0,0,0,0,0,-45,,0,0,19,,19,-38,-38,-38,-38,-38
