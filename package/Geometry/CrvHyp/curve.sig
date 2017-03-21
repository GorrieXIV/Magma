174,1
A,CrvHyp,2,Discriminant,BadPrimes
S,HyperellipticCurve,The hyperelliptic curve given by the polynomial sequence s,1,0,1,82,0,312,1,0,0,0,0,0,0,0,82,,338,-38,-38,-38,-38,-38
S,HyperellipticCurve,The hyperelliptic curve given by y^2 + h y = f,0,2,0,0,0,0,0,0,0,-45,,0,0,312,,338,-38,-38,-38,-38,-38
S,HyperellipticCurve,The hyperelliptic curve given by y^2 + h y = f,0,2,0,0,0,0,0,0,0,312,,0,0,-45,,338,-38,-38,-38,-38,-38
S,HyperellipticCurve,The hyperelliptic curve given by y^2 = f,0,1,0,0,0,0,0,0,0,312,,338,-38,-38,-38,-38,-38
S,HyperellipticCurveOfGenus,The hyperelliptic curve of genus g given by y^2 + h y = f,0,3,0,0,0,0,0,0,0,312,,0,0,312,,0,0,148,,338,-38,-38,-38,-38,-38
S,HyperellipticCurveOfGenus,The hyperelliptic curve of genus g given by y^2 + s[2] y = s[1],1,1,1,82,0,312,2,0,0,0,0,0,0,0,82,,0,0,148,,338,-38,-38,-38,-38,-38
S,HyperellipticCurveOfGenus,The hyperelliptic curve of genus g given by y^2 + h y = f,0,3,0,0,0,0,0,0,0,-45,,0,0,312,,0,0,148,,338,-38,-38,-38,-38,-38
S,HyperellipticCurveOfGenus,The hyperelliptic curve of genus g given by y^2 + h y = f,0,3,0,0,0,0,0,0,0,312,,0,0,-45,,0,0,148,,338,-38,-38,-38,-38,-38
S,HyperellipticCurveOfGenus,The hyperelliptic curve of genus g given by y^2 = f,0,2,0,0,0,0,0,0,0,312,,0,0,148,,338,-38,-38,-38,-38,-38
S,HyperellipticCurve,Returns the curve C as a hyperelliptic curve,0,1,0,0,0,0,0,0,0,326,,338,376,-38,-38,-38,-38
S,HyperellipticCurve,"The hyperelliptic curve E specified by the elliptic curve C, followed by the morphism E -> C and its inverse",0,1,0,0,0,0,0,0,0,334,,338,376,376,-38,-38,-38
S,IsHyperellipticCurve,"Returns true if and only if the equation y^2 + s[2]*y = s[1] defines a hyperelliptic curve. In this case, the curve is returned as a second value",1,0,1,82,0,312,1,0,0,0,0,0,0,0,82,,36,338,-38,-38,-38,-38
S,IsHyperellipticCurveOfGenus,"Returns true if and only if the equation y^2 + s[2]*y = s[1] defines a hyperelliptic curve of genus g. In this case, the curve is returned as a second value",1,1,1,82,0,312,2,0,0,0,0,0,0,0,82,,0,0,148,,36,338,-38,-38,-38,-38
S,EvaluatePolynomial,"Evaluates the homogeneous defining polynomial of C at s = [a,b,c]",0,4,0,0,0,0,0,0,0,-45,,0,0,-45,,0,0,-45,,0,0,338,,-45,-38,-38,-38,-38,-38
S,EvaluatePolynomial,"Evaluates the homogeneous defining polynomial of C at s = [a,b,c]",1,1,1,82,0,-45,2,0,0,0,0,0,0,0,82,,0,0,338,,-45,-38,-38,-38,-38,-38
S,IsPoint,"Returns true if and only if S specifes a point on C, and, if so, returns the point as a second value",0,2,0,0,0,0,0,0,0,82,,0,0,338,,36,336,-38,-38,-38,-38
S,Involution,The application of the hyperelliptic involution to P,0,1,0,0,0,0,0,0,0,336,,336,-38,-38,-38,-38,-38
S,-,The application of the hyperelliptic involution to P,0,1,0,0,0,0,0,0,0,336,,336,-38,-38,-38,-38,-38
S,Discriminant,The discriminant of the curve C,0,1,0,0,0,0,0,0,0,338,,-45,-38,-38,-38,-38,-38
S,BadPrimes,"Returns the sequence of primes where the given model of C has bad reduction. C must be defined over a number field, and the defining polynomials must have integral coefficients. If C is defined over the rationals, the parameter Badness can be given; then only primes are returned such that the valuation of the discriminant at the prime is at least Badness",0,1,0,0,0,0,0,0,0,338,,82,-38,-38,-38,-38,-38
S,RationalPoints,"Same as Points(C,x)",0,2,0,0,0,0,0,0,0,-45,,0,0,338,,151,-38,-38,-38,-38,-38
S,RationalPoints,"Same as Points(C,x)",0,2,0,0,0,0,0,0,0,147,,0,0,338,,151,-38,-38,-38,-38,-38
S,Points,Returns the indexed set of all rational points on the hyperelliptic curve C with x-coordinate equal to x (where rational means rational over the base field of C),0,2,0,0,0,0,0,0,0,-45,,0,0,338,,151,-38,-38,-38,-38,-38
S,Points,Returns the rational points at infinity on C,0,2,0,0,0,0,0,0,0,147,,0,0,338,,151,-38,-38,-38,-38,-38
S,#,The number of rational points on the curve over a finite field,1,0,1,338,0,84,1,0,0,0,0,0,0,0,338,,148,-38,-38,-38,-38,-38
S,ZetaFunction,"The zeta function of C, with finite base field, as a rational function of one variable",1,0,1,338,0,84,1,0,0,0,0,0,0,0,338,,238,-38,-38,-38,-38,-38
S,ZetaFunction,"The zeta function of the base extension of C to K, as a rational function of one variable",1,0,1,338,0,262,2,0,0,0,0,0,0,0,84,,0,0,338,,238,-38,-38,-38,-38,-38
S,Random,"Find a random point on C. Base field must be finite. If the set of all points on C has already been computed, this gives a truly random point, otherwise the ramification points have a slight advantage",1,0,1,338,0,84,1,0,0,0,0,0,0,0,338,,336,-38,-38,-38,-38,-38
