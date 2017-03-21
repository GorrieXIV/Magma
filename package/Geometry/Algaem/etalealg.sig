174,1
A,RngUPolRes,2,AbsoluteMap,LocalData
V,EtaleAlg,1
S,AbsoluteAlgebra,"Given a semi-simple algebra over an absolute number field or the rationals, returns the isomorphic direct sum of absolute fields as a cartesian product and the isomorphism to this product. The optional parameter Fields enables the user to suggest representations of the absolute fields. If this function needs a field isomorphic to one occurring in the supplied list, then it will use the given field. Otherwise it will construct a field itself. The isomorphism is returned as a second argument. If called twice on the same algebra, it will recompute if the Fields argument is given. Otherwise it will return the result computed the first time",0,1,0,0,0,0,0,0,0,65,,38,175,-38,-38,-38,-38
S,AbsoluteAlgebra,"Given a semi-simple algebra over an absolute number field or the rationals, returns the isomorphic direct sum of absolute fields as a cartesian product and the isomorphism to this product. The optional parameter Fields enables the user to suggest representations of the absolute fields. If this function needs a field isomorphic to one occurring in the supplied list, then it will use the given field. Otherwise it will construct a field itself. The isomorphism is returned as a second argument. If called twice on the same algebra, it will recompute if the Fields argument is given. Otherwise it will return the result computed the first time",0,1,0,0,0,0,0,0,0,313,,38,175,-38,-38,-38,-38
S,SUnitGroup,Returns the S-Unit group of a semisimple algebra over a number field. The set S should contain prime ideals related to the base field of A,0,2,0,0,0,0,0,0,0,83,,0,0,313,,107,175,-38,-38,-38,-38
S,pSelmerGroup,"Returns the p-Selmer group of a semi-simple algebra A over a field F, for the set S of primes of F. This combines the pSelmerGroup and map for each field in the direct sum decomposition of A",0,3,0,0,0,0,0,0,0,83,,0,0,148,,0,0,313,,107,175,-38,-38,-38,-38
S,LocalTwoSelmerMap,"Direct product of the LocalTwoSelmerMaps of the direct summands of the semisimple algebra A. The second returned value is for technical use only, and is a sequence of records. Each record contains fields i,p,map, and vmap: here i is an index in the field decomposition of A, p is a prime extending P to the i-th field, map is LocalTwoSelmerMap(p), and vmap is the corresponding valuation map on the field",0,2,0,0,0,0,0,0,0,-1,,0,0,313,,175,82,-38,-38,-38,-38
S,RealExtensions,"Find the maps of A into the real field, extending the given place",0,2,0,0,0,0,0,0,0,332,,0,0,313,,82,-38,-38,-38,-38,-38
S,RealExtensions,"Find the maps of A into the real field, extending the given place",0,2,0,0,0,0,0,0,0,147,,0,0,313,,82,-38,-38,-38,-38,-38
