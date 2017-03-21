174,1
S,RationalPuiseux,"Given a univariate polynomial 'poly' over a multivariate polynomial ring, assuming that it is quasi-ordinary, return a complete set of rational parametrizations (if 'Duval' is 'true'). The parameter 'Gamma' can be used to specify the exponent lattice of 'poly'. If 'subs' is passed, it has to be a sequence of series in a common domain and internally the variables of 'poly' will be substituted by the corresponding series. If 'Duval' is 'false' then the function returns a set of representatives of actual Puiseux series roots of 'poly', i.e., Duval's trick is not applied. If 'OnlySingular' is 'true' then only parametrizations corresponding to singular branches are returned. If the ground field has to be extended, the algebraic elements will be displayed as 'ExtName_i' where 'i' starts from 'ExtCount'. The first return value is the exponent lattice of 'poly', the second is the sequence of parametrizations and the last value is 'ExtCount' plus the number of field extensions that have been introduced during the computation",0,1,0,0,0,0,0,0,0,312,,303,82,148,-38,-38,-38