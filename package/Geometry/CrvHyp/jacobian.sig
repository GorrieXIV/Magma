174,1
A,JacHyp,9,EulerFactor,Order,FactoredOrder,Group,TwoTorsion,TorsionGroup,TorsionMap,TorsionBound,HeightConst
S,Dimension,The dimension of the jacobian J as a variety,0,1,0,0,0,0,0,0,0,152,,148,-38,-38,-38,-38,-38
S,BadPrimes,"Returns the sequence of primes where the given model of the curve of J has bad reduction. J must be defined over a number field, and the defining polynomials of its curve must have integral coefficients",0,1,0,0,0,0,0,0,0,152,,82,-38,-38,-38,-38,-38
S,BaseField,The base field of the Jacobian J,0,1,0,0,0,0,0,0,0,152,,-44,-38,-38,-38,-38,-38
S,BaseRing,The base field of the Jacobian J,0,1,0,0,0,0,0,0,0,152,,-44,-38,-38,-38,-38,-38
S,BaseExtend,Extends the base field of the Jacobian J to F,0,2,0,0,0,0,0,0,0,-44,,0,0,152,,152,-38,-38,-38,-38,-38
S,BaseExtend,Extends the base field of the Jacobian J by applying j,0,2,0,0,0,0,0,0,0,175,,0,0,152,,152,-38,-38,-38,-38,-38
S,BaseExtend,Extends the finite base field of the Jacobian J to its degree n extension,0,2,0,0,0,0,0,0,0,148,,0,0,152,,152,-38,-38,-38,-38,-38
S,JacobianPoint,"The point on the Jacobian J (of a hyperelliptic curve C) associated to the divisor D on C. If D does not have degree 0, then a suitable multiple of the divisor at infinity is subtracted. When the divisor at infinity on C has even degree, D is required to have even degree",0,2,0,0,0,0,0,0,0,61,,0,0,152,,153,-38,-38,-38,-38,-38
S,Point,For internal use only,0,2,0,0,0,0,0,0,0,153,,0,0,152,,153,-38,-38,-38,-38,-38
S,IsPoint,"True iff pt is coercible into Jacobian J; if true, also return J!pt",0,2,0,0,0,0,0,0,0,153,,0,0,152,,36,153,-38,-38,-38,-38
S,RationalPoints,"Returns all rational points on the Jacobian J over a finite field, or all points on a Jacobian of a genus 2 curve of the form y^2 = f(x), defined over the rationals, up to a bound on the naive Kummer surface height set by the parameter Bound",0,1,0,0,0,0,0,0,0,152,,151,-38,-38,-38,-38,-38
S,Points,"Returns all rational points on the Jacobian J over a finite field, or all points on a Jacobian of a genus 2 curve of the form y^2 = f(x), defined over the rationals, up to a bound on the naive Kummer surface height set by the parameter Bound",0,1,0,0,0,0,0,0,0,152,,151,-38,-38,-38,-38,-38
S,RationalPoints,Find all points on J with first component a and degree d. So far only for genus 2 and curve of the form y^2 = f(x),0,3,0,0,0,0,0,0,0,148,,0,0,312,,0,0,152,,151,-38,-38,-38,-38,-38
S,Points,Find all points on J with first component a and degree d. So far only for genus 2 and curve of the form y^2 = f(x),0,3,0,0,0,0,0,0,0,148,,0,0,312,,0,0,152,,151,-38,-38,-38,-38,-38
S,-,Returns the divisor class [P1 - P2] as a point on the Jacobian,0,2,0,0,0,0,0,0,0,336,,0,0,336,,153,-38,-38,-38,-38,-38
S,JacobianPoint,For internal use only,2,0,1,82,0,336,1,1,82,0,336,2,0,0,0,0,0,0,0,82,,0,0,82,,153,-38,-38,-38,-38,-38
S,JacobianPoint,The difference of the two points in the Jacobian (for internal use only),0,2,0,0,0,0,0,0,0,336,,0,0,336,,153,-38,-38,-38,-38,-38
S,EulerFactor,"The Euler factor of a Jacobian over a finite field, i.e. the reciprocal characteristic polynomial of Frobenius acting on H^1(J)",0,1,0,0,0,0,0,0,0,152,,312,-38,-38,-38,-38,-38
S,EulerFactor,"The Euler factor of the base extension of J to K, where the base field of J is the rationals",0,2,0,0,0,0,0,0,0,84,,0,0,152,,312,-38,-38,-38,-38,-38
S,#,The number of rational points on the Jacobian over a finite field,0,1,0,0,0,0,0,0,0,152,,148,-38,-38,-38,-38,-38
S,FactoredOrder,"The order of the group of rational points of J, over a finite field, in factored form",0,1,0,0,0,0,0,0,0,152,,82,-38,-38,-38,-38,-38
S,TorsionBound,"A bound on the size of the rational torsion subgroup by looking at the first n good primes, where the base field of J is the rationals: The best known result based on the first n primes of good reduction AND any previously computed torsion bound",0,2,0,0,0,0,0,0,0,148,,0,0,152,,148,-38,-38,-38,-38,-38
S,Order,"The order of the point on the Jacobian, over a finite field or the rationals. Returns 0 if the point has infinite order",0,1,0,0,0,0,0,0,0,153,,148,-38,-38,-38,-38,-38
S,HasOrder,Returns true iff n is the order of the Jacobian point P. Maybe expensive over infinite fields when n is large,0,2,0,0,0,0,0,0,0,148,,0,0,153,,36,-38,-38,-38,-38,-38
