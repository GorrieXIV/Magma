174,1
A,GrpPSL2Elt,1,DIntersect
S,SetPrecision,Sets the complex precision of z to prec,0,2,0,0,1,0,0,0,0,148,,1,1,SpcHydElt,,-38,-38,-38,-38,-38,-38
S,ComplexValue,The complex value of the argument,0,1,0,0,0,0,0,0,0,SpcHydElt,,172,-38,-38,-38,-38,-38
S,Imaginary,The imaginary part of z,0,1,0,0,0,0,0,0,0,SpcHydElt,,402,-38,-38,-38,-38,-38
S,Real,The real part of z,0,1,0,0,0,0,0,0,0,SpcHydElt,,402,-38,-38,-38,-38,-38
S,AbsoluteValue,The absolute value of z,0,1,0,0,0,0,0,0,0,SpcHydElt,,402,-38,-38,-38,-38,-38
S,Argument,The argument of z,0,1,0,0,0,0,0,0,0,SpcHydElt,,402,-38,-38,-38,-38,-38
S,Distance,Returns the hyperbolic distance between z and w,0,2,0,0,0,0,0,0,0,SpcHydElt,,0,0,SpcHydElt,,402,-38,-38,-38,-38,-38
S,Geodesic,Returns the center and radius of the geodesic containing z and w,0,2,0,0,0,0,0,0,0,SpcHydElt,,0,0,SpcHydElt,,-45,-45,-38,-38,-38,-38
S,TangentAngle,The angle of the tangent at x of the geodescic from x to y,0,2,0,0,0,0,0,0,0,SpcHydElt,,0,0,SpcHydElt,,402,-38,-38,-38,-38,-38
S,Angle,"Given two sequences e1 = [z1,z2] and e2 = [z1,z3], returns the angle between the geodesics at z1",2,0,1,82,0,SpcHydElt,1,1,82,0,SpcHydElt,2,0,0,0,0,0,0,0,82,,0,0,82,,402,-38,-38,-38,-38,-38
S,InternalTangentAngle,The angle in the hyperbolic disk,0,2,0,0,0,0,0,0,0,172,,0,0,172,,-1,-38,-38,-38,-38,-38
S,InternalAngle,The angle in the hyperbolic disk,0,5,0,0,0,0,0,0,0,SpcHyd,,0,0,402,,0,0,172,,0,0,402,,0,0,172,,-1,-38,-38,-38,-38,-38
S,ArithmeticVolume,"The volume of the convex region specified the sequence of elements of the unit disc. The volume is normalized ""arithmetic"" volume, so the usual volume is divided by 2*pi; this gives an ideal triangle volume 1/2",1,0,1,82,0,SpcHydElt,1,0,0,0,0,0,0,0,82,,402,-38,-38,-38,-38,-38
S,InternalIntersection,Intersection of geodesics in the hyperbolic disk,0,5,0,0,0,0,0,0,0,SpcHyd,,0,0,-45,,0,0,-45,,0,0,402,,0,0,172,,-1,-38,-38,-38,-38,-38
S,GeodesicsIntersection,"Returns the intersection in the unit disc of the two geodesics x1, x2, where x and y are specified by their end points. If more than one intersection exists, returns a sequence",2,0,1,82,0,SpcHydElt,1,1,82,0,SpcHydElt,2,0,0,0,0,0,0,0,82,,0,0,82,,-1,-38,-38,-38,-38,-38
S,BoundaryIntersection,Computes the intersection of the geodesic x with the boundary of the unit disc,1,0,1,82,0,SpcHydElt,1,0,0,0,0,0,0,0,82,,82,-38,-38,-38,-38,-38
S,BoundaryIntersection,Returns the intersection of the isometric circle of gamma with the boundary of the unit disc D,0,2,0,0,0,0,0,0,0,SpcHyd,,0,0,GrpPSL2Elt,,-1,-38,-38,-38,-38,-38
