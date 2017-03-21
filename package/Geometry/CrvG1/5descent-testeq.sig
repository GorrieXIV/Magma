174,1
A,CrvEll,1,FiveTorsionPoints
S,FiveTorsionPoints,Same as FiveTorsionOrbits,1,0,1,334,0,262,1,0,0,0,0,0,0,0,334,,303,-38,-38,-38,-38,-38
S,FiveTorsionOrbits,"Computes <T_1, ... , T_r> where the T_i are representatives for the Galois orbits on E[5] - {O}",1,0,1,334,0,262,1,0,0,0,0,0,0,0,334,,303,-38,-38,-38,-38,-38
S,FiveTorsionMatrices,"Given a genus one model of degree 5 with Jacobian E, computes the action of E[5] on the model",1,0,1,334,0,262,2,0,0,0,0,0,0,0,493,,0,0,334,,303,-38,-38,-38,-38,-38
S,FiveSelmerElement,"Given a genus one model of degree 5 with Jacobian E, returns an element in (the algebra associated to) the 5-Selmer group of E, corresponding to the model",1,0,1,334,0,262,2,0,0,0,0,0,0,0,493,,0,0,334,,303,-38,-38,-38,-38,-38
S,FiveCoveringDependenceInformation,"Given a sequence of genus one models of degree 5, all with Jacobian E, determines what relations they might satisfy in H^1(Q,E[5]), on the basis of reducing modulo a few primes. The subgroup of H^1(Q,E[5]) spanned by the given models has dimension at least the number of rows of the matrix returned",1,0,1,334,0,262,2,0,0,0,0,0,0,0,82,,0,0,334,,155,-38,-38,-38,-38,-38
S,IsEquivalentFive,Determines whether genus one models of degree 5 defined over Q are equivalent and if so also returns the transformation relating them,0,2,0,0,0,0,0,0,0,493,,0,0,493,,36,TransG1,-38,-38,-38,-38
S,AddFiveCoverings,"Given a sequence of d genus one models all with the same Jacobian, and defined over Q, adds the 5-coverings as specified by vectorlist. This second argument should be a sequence of elements in VectorSpace(GF(5),d). In the case of non-trivial obstruction a zero model is returned",2,0,1,82,0,493,1,1,82,0,160,2,0,0,0,0,0,0,0,82,,0,0,82,,82,-38,-38,-38,-38,-38
