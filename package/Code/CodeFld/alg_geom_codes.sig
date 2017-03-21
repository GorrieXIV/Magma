174,1
V,AGCode,2
A,Code,6,IsWeaklyAG,IsWeaklyAGDual,Divisor,GeometricSupport,RiemannRochBasis,GoppaDesignedDistance
S,HermitianCode,"Given an integer q, builds the Hermitian code with support all places of degree one of the curve x^(q+1) + y^(q+1) + z^(q+1) over GF(q^2), except the place over (1:1:0), and divisor divisor r*P",0,2,0,0,0,0,0,0,0,148,,0,0,148,,-39,-38,-38,-38,-38,-38
S,AGCode,The (weakly) algebraic-geometric code build by evaluating functions of the Riemann-Roch space of D on the support S of places of degree 1 together with this basis. The degree of D need not be bounded by #S,1,0,1,82,0,232,2,0,0,0,0,0,0,0,61,,0,0,82,,-39,-38,-38,-38,-38,-38
S,AlgebraicGeometricCode,The (weakly) algebraic-geometric code build by evaluating functions of the Riemann-Roch space of D at the points of S. The degree of D need not be bounded by #S,1,0,1,82,0,232,2,0,0,0,0,0,0,0,61,,0,0,82,,-39,-38,-38,-38,-38,-38
S,AGCode,The (weakly) algebraic-geometric code build by evaluating functions of the Riemann-Roch space of D on the support S of places of degree 1 together with this basis. The degree of D need not be bounded by #S,1,0,1,82,0,230,2,0,0,0,0,0,0,0,59,,0,0,82,,-39,-38,-38,-38,-38,-38
S,AlgebraicGeometricCode,The (weakly) algebraic-geometric code build by evaluating functions of the Riemann-Roch space of D at the points of S. The degree of D need not be bounded by #S,1,0,1,82,0,230,2,0,0,0,0,0,0,0,59,,0,0,82,,-39,-38,-38,-38,-38,-38
S,AlgebraicGeometricDualCode,"Return the differential algebraic-geometric code, obtained by computing residues of differential forms. These are dual to the codes constructed using AlgebraicGeometricCode",1,0,1,82,0,232,2,0,0,0,0,0,0,0,61,,0,0,82,,-39,-38,-38,-38,-38,-38
S,AlgebraicGeometricDualCode,"Return the differential algebraic-geometric code, obtained by computing residues of differential forms. These are dual to the codes constructed using AlgebraicGeometricCode",1,0,1,82,0,230,2,0,0,0,0,0,0,0,59,,0,0,82,,-39,-38,-38,-38,-38,-38
S,AGDualCode,"Return the differential algebraic-geometric code, obtained by computing residues of differential forms. These are dual to the codes constructed using AlgebraicGeometricCode",1,0,1,82,0,232,2,0,0,0,0,0,0,0,61,,0,0,82,,-39,-38,-38,-38,-38,-38
S,IsWeaklyAG,"Return true if and only if C is a weakly algebraic-geometric code, i.e. constructed as an algebraic-geometric code with respect to a divisor of any degree",0,1,0,0,0,0,0,0,0,42,,36,-38,-38,-38,-38,-38
S,IsWeaklyAGDual,Return true if and only if C is constructed as the dual of a weakly algebraic-geometric code,0,1,0,0,0,0,0,0,0,42,,36,-38,-38,-38,-38,-38
S,IsAlgebraicGeometric,"Return true if and only if C is of algebraic-geometric construction of length n, built from a divisor D with deg(D) < n",0,1,0,0,0,0,0,0,0,42,,36,-38,-38,-38,-38,-38
S,IsStronglyAG,Return true iff C is an algebraic-geometric code of length n built from a divisor D with 2g-2 < deg(D) < n,0,1,0,0,0,0,0,0,0,42,,36,-38,-38,-38,-38,-38
S,Curve,"Given an algebraic-geometric code, returns the curve from which is was defined",0,1,0,0,0,0,0,0,0,42,,371,-38,-38,-38,-38,-38
S,GeometricSupport,"Given an algebraic-geometric code, returns the sequence of places from which forms its support",0,1,0,0,0,0,0,0,0,42,,61,-38,-38,-38,-38,-38
S,Divisor,"Given an algebraic-geometric code, returns the divisor from which C was constructed",0,1,0,0,0,0,0,0,0,42,,61,-38,-38,-38,-38,-38
S,GoppaDesignedDistance,"Given an algebraic-geometric code built with a divisor D, returns the Goppa designed distance: n - deg(D)",0,1,0,0,0,0,0,0,0,42,,148,-38,-38,-38,-38,-38
S,AGDecode,Decode a dual Algebraic Geometric code up to the designated distance. Requires an input divisor Fd whose support is disjoint from the divisor defining the curve,0,3,0,0,0,0,0,0,0,61,,0,0,160,,0,0,42,,160,36,-38,-38,-38,-38
