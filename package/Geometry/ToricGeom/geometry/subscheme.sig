174,1
A,Sch,9,is_stratum,face,stratum_map,stratum_scheme,binomial_map,binomial_scheme,blow_up_map,restr_to_torus,restr_to_torus_map
S,Scheme,Returns the toric stratum corresponding to C. C must be a face of fan of X,0,2,0,0,0,0,0,0,0,TorCon,,0,0,243,,380,-38,-38,-38,-38,-38
S,IsStratum,True iff Z is defined by vanishing of variables and is non-empty,0,1,0,0,0,0,0,0,0,380,,36,-38,-38,-38,-38,-38
S,Face,"If Z is a stratum, returns the corresponding cone in the fan",0,1,0,0,0,0,0,0,0,380,,36,-38,-38,-38,-38,-38
S,@@,Preimage of Z under psi,0,2,0,0,0,0,0,0,0,TorMap,,0,0,380,,380,-38,-38,-38,-38,-38
S,Stratum,"Returns the pullback of scheme Z to minimal toric stratum containing Z, together with the map giving embedding of ambients",0,1,0,0,0,0,0,0,0,380,,380,TorMap,-38,-38,-38,-38
S,BinomialToricEmbedding,"Takes binomial equations in the ideal of Z and construct toric variety, which is the normalisation of the closure of subtorus described by those binomials. Returns the pullback of scheme Z and the normalisation map into the ambient of Z",0,1,0,0,0,0,0,0,0,380,,380,TorMap,-38,-38,-38,-38
S,Blowup,"If S is defined by a monomial ideal, then returns the Blow up of this ideal, together with the map",0,1,0,0,0,0,0,0,0,380,,243,TorMap,-38,-38,-38,-38
S,NonQFactorialLocus,Returns the monomial reduced subscheme of X whose points are non Q-factorial points of X,0,1,0,0,0,0,0,0,0,243,,380,-38,-38,-38,-38,-38
S,DimensionOfNonQFactorialLocus,Dimension of the locus of non-Q-factorial points,0,1,0,0,0,0,0,0,0,243,,148,-38,-38,-38,-38,-38
S,InternalDimensionForSchemesInToricVarieties,For internal use only --- gives the dimension of a subscheme taking into account components contained in non-Q-factorial locus,0,1,0,0,0,0,0,0,0,380,,148,-38,-38,-38,-38,-38
S,RestrictionToSubtorus,The restriction of Z to the biggest subtorus of the ambient containing Z,0,1,0,0,0,0,0,0,0,380,,380,TorMap,-38,-38,-38,-38
