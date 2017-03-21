174,1
S,SwapElements,Swap elements at indices i and j in S,0,3,0,0,1,0,0,0,0,148,,0,0,148,,1,1,82,,-38,-38,-38,-38,-38,-38
S,RandomConjugate,Return random conjugate of G in Generic(G),0,1,0,0,0,0,0,0,0,224,,224,-38,-38,-38,-38,-38
S,RandomConjugate,Return random conjugate of G in Generic(G),0,1,0,0,0,0,0,0,0,178,,178,-38,-38,-38,-38,-38
S,UserGenerators,Return the sequence of generators that defined V,0,1,0,0,0,0,0,0,0,191,,82,-38,-38,-38,-38,-38
S,UserGenerators,Return the sequence of generators that defined W,0,1,0,0,0,0,0,0,0,136,,82,-38,-38,-38,-38,-38
S,UserGenerators,Return the sequence of generators that defined G,0,1,0,0,0,0,0,0,0,127,,82,-38,-38,-38,-38,-38
S,UserGenerators,Return supplied or defining generators of G,0,1,0,0,0,0,0,0,0,178,,82,-38,-38,-38,-38,-38
S,UserGenerators,Return supplied or defining generators of G,0,1,0,0,0,0,0,0,0,129,,82,-38,-38,-38,-38,-38
S,UserGenerators,Return supplied or defining generators of G,0,1,0,0,0,0,0,0,0,107,,82,-38,-38,-38,-38,-38
S,UserGenerators,Return the sequence of generators that defined F,0,1,0,0,0,0,0,0,0,121,,82,-38,-38,-38,-38,-38
S,UserGenerators,Return the sequence of generators that defined G,0,1,0,0,0,0,0,0,0,132,,82,-38,-38,-38,-38,-38
S,Generic,"The generic version of G, ie G itself",0,1,0,0,0,0,0,0,0,129,,129,-38,-38,-38,-38,-38
S,Generic,"The generic version of G, ie G itself",0,1,0,0,0,0,0,0,0,107,,107,-38,-38,-38,-38,-38
S,WordGroup,An SLP group on the same number of generators as A,0,1,0,0,0,0,0,0,0,107,,107,-38,-38,-38,-38,-38
S,WordGroup,An SLP group on the same number of generators as A,0,1,0,0,0,0,0,0,0,129,,136,-38,-38,-38,-38,-38
S,WordGroup,An SLP group on the same number of generators as A,0,1,0,0,0,0,0,0,0,132,,136,-38,-38,-38,-38,-38
S,IsIdentity,True iff g is the identity element,0,1,0,0,0,0,0,0,0,137,,36,-38,-38,-38,-38,-38
S,IsIdentity,True iff x is the identity matrix,0,1,0,0,0,0,0,0,0,177,,36,-38,-38,-38,-38,-38
S,InnerProduct,Return the inner product matrix of V,0,1,0,0,0,0,0,0,0,159,,-34,-38,-38,-38,-38,-38
S,FrobeniusImage,"Frobenius twist of matrix group G, i.e. returns the matrix group where each generator of G has been FrobeniusTwist'ed. Also returns inclusion homomorphism into the general linear group",0,2,0,0,0,0,0,0,0,148,,0,0,178,,178,-38,-38,-38,-38,-38
S,FrobeniusImage,"Frobenius twist of vector v, i.e. returns the vector where the entries have been raised to the power p^r, where p is the characteristic of the underlying field",1,0,1,160,0,84,2,0,0,0,0,0,0,0,148,,0,0,160,,160,-38,-38,-38,-38,-38
S,FrobeniusImage,"Frobenius twist of vector space V, i.e. returns the vector space where each basis element of V has been FrobeniusTwist'ed. Also returns inclusion homomorphism into the full vector space",1,0,1,159,0,84,2,0,0,0,0,0,0,0,148,,0,0,159,,159,175,-38,-38,-38,-38
S,FrobeniusImage,"Frobenius twist of vector v, i.e. returns the vector where the entries have been raised to the power p^r, where p is the characteristic of the underlying field",0,2,0,0,0,0,0,0,0,148,,0,0,104,,104,-38,-38,-38,-38,-38
S,FrobeniusImage,"Frobenius twist of module M, i.e. returns the module where each generator of M has been FrobeniusTwist'ed",0,2,0,0,0,0,0,0,0,148,,0,0,181,,181,-38,-38,-38,-38,-38
S,FrobeniusImage,"Frobenius twist of module M, i.e. returns the module where each generator of M has been FrobeniusTwist'ed",0,3,0,0,0,0,0,0,0,148,,0,0,178,,0,0,103,,103,-38,-38,-38,-38,-38
S,KroneckerDelta,Return 1 if i = j and 0 otherwise,0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,RandomWord,construct a random element of G and return it both as a element and as straight-line program,0,1,0,0,0,0,0,0,0,-27,,180,137,-38,-38,-38,-38
S,Normalise,Multiply g by the scalar which makes the first non-zero entry 1,0,1,0,0,0,0,0,0,0,-34,,-34,-38,-38,-38,-38,-38
S,WriteOverLargerField,"Return the embedding H of G <= GL(d, q) inside GL(d, q^e). If Scalars is true, then return Z.H where Z = Centre(GL(d, q^e))",0,2,0,0,0,0,0,0,0,148,,0,0,178,,178,-38,-38,-38,-38,-38
S,Embed,return isomorphic copy of G defined over standard copy of defining field,1,0,1,178,0,84,1,0,0,0,0,0,0,0,178,,178,-38,-38,-38,-38,-38
S,Embed,return isomorphic copy of G defined over F,1,0,1,178,0,84,2,0,0,0,0,0,0,0,84,,0,0,178,,178,-38,-38,-38,-38,-38
S,Embed,return copy of g defined over standard copy of defining field,1,0,1,180,0,84,1,0,0,0,0,0,0,0,180,,180,-38,-38,-38,-38,-38
S,Embed,return copy of g defined over F,1,0,1,180,0,84,2,0,0,0,0,0,0,0,84,,0,0,180,,180,-38,-38,-38,-38,-38
S,IsStandardGF,"if F is standard copy of this field return true, else false",0,1,0,0,0,0,0,0,0,84,,36,-38,-38,-38,-38,-38
S,HasBSGS,"does G already know a BSGS? if so, return true and basic orbit lengths, else false",1,0,1,178,0,84,1,0,0,0,0,0,0,0,178,,36,-38,-38,-38,-38,-38
