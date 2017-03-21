174,1
A,Sch,2,scheme_of_lines,lines_over_internal_field
S,UnionOfLines,"A scheme in the projective space P which is the (scheme-theoretic) union of the lines in L. The lines should be given in parametrized form, each line as a sequence of linear polynomials (the coefficients may be in an extension of the base field of P). The lines are assumed to be distinct",1,1,1,-52,0,311,2,0,0,0,0,0,0,0,-52,,0,0,379,,380,-38,-38,-38,-38,-38
S,LinesInScheme,"Computes the geometric lines contained in the scheme X. Returns a list of schemes whose points correspond to lines, together with a corresponding list of parametrized lines (one line for each scheme, expressed generically using the coordinates of that scheme). There may be infinitely many lines",0,1,0,0,0,0,0,0,0,380,,82,168,-38,-38,-38,-38
S,IntersectionMatrix,A matrix giving the intersection numbers of the (geometric) lines on the del Pezzo surface X,0,1,0,0,0,0,0,0,0,66,,-34,-38,-38,-38,-38,-38
S,NumberOfLines,The number of geometric lines in (the standard pluri-canonical embedding of) the Del Pezzo surface X,0,1,0,0,0,0,0,0,0,66,,148,-38,-38,-38,-38,-38
S,GaloisActionOnLines,A permutation group which gives the Galois action on the (finite) set of lines in the scheme X,0,1,0,0,0,0,0,0,0,380,,224,-38,-38,-38,-38,-38
S,PicardGroupGeometric,"The Picard group of the Del Pezzo surface X (over the algebraic closure of its base field), returned as a Z-module. Also returns a matrix giving the intersection pairing on the geometric Picard group",0,1,0,0,0,0,0,0,0,66,,181,-34,-38,-38,-38,-38
S,GeometricPicardGroup,"The Picard group of the Del Pezzo surface X (over the algebraic closure of its base field), returned as a Z-module. Also returns a matrix giving the intersection pairing on the geometric Picard group",0,1,0,0,0,0,0,0,0,66,,181,-34,-38,-38,-38,-38
S,PicardIntersectionPairing,A matrix giving the intersection pairing on the GeometricPicardGroup of X,0,1,0,0,0,0,0,0,0,66,,-34,-38,-38,-38,-38,-38
S,PicardGaloisModule,A G-module giving the Galois action on the GeometricPicardGroup of X,0,1,0,0,0,0,0,0,0,66,,103,-38,-38,-38,-38,-38
