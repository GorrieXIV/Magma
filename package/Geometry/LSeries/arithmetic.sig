174,1
S,eq,"true iff L1 and L2 are L-series associated to the same object, except false for modular forms over number fields, and isogenous elliptic curves over Q are also checked",0,2,0,0,0,0,0,0,0,LSer,,0,0,LSer,,36,-38,-38,-38,-38,-38
S,ne,"true iff L1 and L2 are not associated to the same object, except always true for modular forms over number fields, and isogenous elliptic curves over Q are always checked",0,2,0,0,0,0,0,0,0,LSer,,0,0,LSer,,36,-38,-38,-38,-38,-38
S,IsOne,true iff the L-series was defined to be identically 1,0,1,0,0,0,0,0,0,0,LSer,,36,-38,-38,-38,-38,-38
S,LSeries,LSeries(1) returns the L-series which is identically 1,0,1,0,0,0,0,0,0,0,148,,LSer,-38,-38,-38,-38,-38
A,LSer,1,embed
S,/,"Quotient of two L-series with weakly multiplicative coefficients, provided that this quotient makes sense and (this is not checked!) is again an L-series with finitely many poles. Specify poles and residues if you happen to know them",0,2,0,0,0,0,0,0,0,LSer,,0,0,LSer,,LSer,-38,-38,-38,-38,-38
S,*,Product of two L-series with weakly multiplicative coefficients. Specify poles and residues if you happen to know them,0,2,0,0,0,0,0,0,0,LSer,,0,0,LSer,,LSer,-38,-38,-38,-38,-38
S,LProduct,Return the product of a sequence of L-series,1,0,1,82,0,303,1,0,0,0,0,0,0,0,82,,LSer,-38,-38,-38,-38,-38
S,LProduct,Return the product of a sequence of L-series,1,0,1,82,0,LSer,1,0,0,0,0,0,0,0,82,,LSer,-38,-38,-38,-38,-38
S,^,Take a power of an L-series,0,2,0,0,0,0,0,0,0,148,,0,0,LSer,,LSer,-38,-38,-38,-38,-38
S,Factorization,"If an L-series is known to be a product of other L-series, return them and their exponents [<L1,n1>,...]. Otherwise returns [<L,1>]",0,1,0,0,0,0,0,0,0,LSer,,82,-38,-38,-38,-38,-38
S,ArithmeticLSeries,"Given an LSeries of ""arithmetic"" type, attempt to factor off zeta-factors and determine whether it is primitive",0,1,0,0,0,0,0,0,0,LSer,,LSer,148,-38,-38,-38,-38
S,MomentData,"Given an L-series and a set of primes, compute the moment data up to n. Returned as the mean, and then an array of even powers up to n, and the proportion of prime coefficients that are zero",1,1,1,82,0,148,3,0,0,0,0,0,0,0,148,,0,0,82,,0,0,LSer,,148,82,148,-38,-38,-38
S,InnerProduct,"Given two L-series and a set of primes, compute the inner product on them",1,2,1,82,0,148,3,0,0,0,0,0,0,0,82,,0,0,LSer,,0,0,LSer,,402,-38,-38,-38,-38,-38
S,ChangeEulerFactor,"Given an L-series, a prime, and a polynomial, create an L-function with the given Euler factor at said prime",0,3,0,0,0,0,0,0,0,312,,0,0,148,,0,0,LSer,,LSer,-38,-38,-38,-38,-38
S,ChangeLocalInformation,"Given an L-series, a prime, the new local conductor, and a polynomial, create an L-function with the given Euler factor at said prime",0,4,0,0,0,0,0,0,0,312,,0,0,148,,0,0,148,,0,0,LSer,,LSer,-38,-38,-38,-38,-38
S,ChangeLocalInformation,"Given an L-series and local information <p,f,eul>, create a new L-function",0,2,0,0,0,0,0,0,0,168,,0,0,LSer,,LSer,-38,-38,-38,-38,-38
S,BadPrimeData,"Given an L-series, return an array of its bad prime data",0,1,0,0,0,0,0,0,0,LSer,,82,-38,-38,-38,-38,-38
S,CopyCoefficients,"Given two L-series the first with stored coefficients, copy them from the first to the second",0,2,0,0,1,0,0,0,0,LSer,,0,0,LSer,,-38,-38,-38,-38,-38,-38
