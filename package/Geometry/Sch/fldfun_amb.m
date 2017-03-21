freeze;

///////////////////////////////////////////////////////////////////////
// fldfun_amb.m
//	coercions for ambient function fields
//
// Gavin Brown, November 2000
///////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////
//		Function field coercions
// Rings/Fields:
//	FA = ff(affine n space) = FldFunRat in n vars
//	RA = coordring(affine n space) = poly ring in n vars
//	FP = ff(proj n space) = FldFunRat in n vars
//           (equals that of first patch)
//	RP = coordring(proj n space) = graded poly ring in n+1 vars
//	FC = ff(curve in the plane)
//	FF = general FldFunRat in n vars, eg FP, FieldOfFractions(RA), FA
// Recall the basic internal C function:
//	RationalFunction(f):	FC -> FF
// Functions:
//	GenericToFOF(f,P):	FF -> FieldOfFractions(RP)
//	GenericToFF(f,P/A):	FF -> FP/FA
//	FFCurveToPlane(f):	FC -> FP/FA
//	FFPlaneToCurve(C,f):	FP/FA -> FC
//	CurveFFElt(C,f):	FP/FA or FieldOfFractions(RP) -> FC
//	AmbientFFElt(A/P,f):	FP/FA or FieldOfFractions(RP) -> FP/FA
// The last function takes a relevant FF elt and puts it in the ambient ff
// changing type only if necessary. The point is that if f,g are homogeneous
// elts of the coord ring of P then f/g should be interpreted as a FP elt,
// which at the moment it won't be. The argument could also be any scheme, in
// which case this all applies to its ambient space.
// There are also IsCurveFFElt and IsAmbientFFElt to test the latter.
///////////////////////////////////////////////////////////////////////
