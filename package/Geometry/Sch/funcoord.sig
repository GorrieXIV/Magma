174,1
A,Sch,1,nonemptypatch
S,MyEval,"Evaluate a multivariate polynomial or a multivariate function field element in a point, represented by a sequence of values",1,1,1,82,0,-45,2,0,0,0,0,0,0,0,82,,0,0,-1,,-45,-38,-38,-38,-38,-38
S,RestrictionToPatch,"Takes an element f of the FunctionField of X and returns a representative of f on Xi, the ith affine patch of X (in the field of fractions of the coordinate ring of the ambient of the patch)",0,2,0,0,0,0,0,0,0,380,,0,0,427,,421,-38,-38,-38,-38,-38
S,Degrees,Return the degrees of f with respect to the gradings of X. f is required to be homogeneous with respect to all gradings of X,0,2,0,0,0,0,0,0,0,63,,0,0,380,,82,-38,-38,-38,-38,-38
S,IntegralSplit,Returns num and den in the coordinate ring of Ambient(X) that represent f as num/den on X,0,2,0,0,0,0,0,0,0,380,,0,0,427,,63,63,-38,-38,-38,-38
S,Numerator,Returns the first argument of IntegralSplit,0,2,0,0,0,0,0,0,0,380,,0,0,427,,63,-38,-38,-38,-38,-38
S,Denominator,Returns the first argument of IntegralSplit,0,2,0,0,0,0,0,0,0,380,,0,0,427,,63,-38,-38,-38,-38,-38
S,Restriction,"Given a function f in the function field of X, returns the restriction of f to Y as an element of the function field of Y. If f has a pole along Y, then Infty() is returned. It is an error if f is not defined along Y",0,2,0,0,0,0,0,0,0,380,,0,0,427,,427,-38,-38,-38,-38,-38
S,ProjectiveMap,Returns the projective map defined by the functions in L,1,0,1,82,0,427,2,0,0,0,0,0,0,0,379,,0,0,82,,376,-38,-38,-38,-38,-38
S,ProjectiveMap,Returns the projective map X->Y defined by the functions in L,1,0,1,82,0,427,1,0,0,0,0,0,0,0,82,,376,-38,-38,-38,-38,-38
S,ProjectiveMap,Returns the projective map X->Y defined by f,0,2,0,0,0,0,0,0,0,379,,0,0,427,,376,-38,-38,-38,-38,-38
S,ProjectiveMap,Returns the projective map defined by f,0,1,0,0,0,0,0,0,0,427,,376,-38,-38,-38,-38,-38
S,GenericPoint,"Returns a generic point on X, i.e., a point over the function field of X if a function field is available. Otherwise, an affine coordinate ring of X is chosen such that the intersection of X with the infinite hyperplane is of strictly lower dimension than X (if X is equidimensional, this means none of the components lie at infinity). A point is returned in an appropriate affine algebra over a multivariate rational function field. If NoFunctionField is supplied then the latter strategy is followed even for curves and ambient spaces",0,1,0,0,0,0,0,0,0,380,,377,-38,-38,-38,-38,-38
S,FormalPoint,Returns a power series expansion around the given point,0,1,0,0,0,0,0,0,0,377,,377,-38,-38,-38,-38,-38
S,EvaluateByPowerSeries,Uses power series expansion around a point P to evaluate mp at P if P is in the base scheme of mp,0,2,0,0,0,0,0,0,0,377,,0,0,376,,377,-38,-38,-38,-38,-38
S,UniformizingElement,Uniformizing element,0,1,0,0,0,0,0,0,0,288,,285,-38,-38,-38,-38,-38
S,UniformizingElement,Uniformizing element,0,1,0,0,0,0,0,0,0,289,,286,-38,-38,-38,-38,-38
