174,1
S,RandomSLnZ,"A random element in SL(n,Z), obtained as the product of l matrices each with a single nondiagonal entry of absolute value at most k",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,177,-38,-38,-38,-38,-38
S,RandomGLnZ,"A random element in GL(n,Z), obtained as the product of l matrices each with a single nondiagonal entry of absolute value at most k",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,177,-38,-38,-38,-38,-38
S,IsGenusOneModel,"Determines whether f specifies a genus one model of degree n = 2 or n = 3; if true the model is also returned. A genus one model of degree 2 is a binary quartic. A genus one model of degree 3 is a ternary cubic. A genus one model of degree 2 may also be given in the form y^2 + f(x,z) y - g(x,z) where f and g homogenous of degrees 2 and 4, and the variables x, z, y are assigned degrees 1, 1, 2",0,1,0,0,0,0,0,0,0,63,,36,493,-38,-38,-38,-38
S,IsGenusOneModel,"Determines whether f specifies a genus one model of degree n = 2 or n = 3; if true the model is also returned. A genus one model of degree 2 is a binary quartic. A genus one model of degree 3 is a ternary cubic. A genus one model of degree 2 may also be given in the form y^2 + f(x,z) y - g(x,z) where f and g homogenous of degrees 2 and 4, and the variables x, z, y are assigned degrees 1, 1, 2",0,1,0,0,0,0,0,0,0,312,,36,493,-38,-38,-38,-38
S,IsGenusOneModel,Determines whether phi defines a genus one model of degree 4; if true the model is also returned. The input should be a sequence of 2 quadratic forms in 4 variables,1,0,1,82,0,63,1,0,0,0,0,0,0,0,82,,36,493,-38,-38,-38,-38
S,IsGenusOneModel,Determines whether phi defines a genus one model of degree 5; if true the model is also returned. The input should be a 5 by 5 alternating matrix whose entries are linear forms in 5 variables,0,1,0,0,0,0,0,0,0,-34,,36,493,-38,-38,-38,-38
S,Degree,The degree of the given genus one model,0,1,0,0,0,0,0,0,0,493,,148,-38,-38,-38,-38,-38
S,BaseRing,The coefficient ring of the given genus one model,0,1,0,0,0,0,0,0,0,493,,-44,-38,-38,-38,-38,-38
S,PolynomialRing,The polynomial ring used to define the given genus one model,0,1,0,0,0,0,0,0,0,493,,64,-38,-38,-38,-38,-38
S,ModelParent,Obsolete,0,1,0,0,0,0,0,0,0,148,,-1,-38,-38,-38,-38,-38
S,GenusOneModel,"Converts a sequence of coefficients to a genus one model of degree n, where n = 2,3,4 or 5",1,0,1,82,0,-45,1,0,0,0,0,0,0,0,82,,493,-38,-38,-38,-38,-38
S,GenusOneModel,"Converts a sequence of coefficients to a genus one model of degree n, where n = 2,3,4 or 5",1,2,1,82,0,-45,3,0,0,0,0,0,0,0,82,,0,0,148,,0,0,-44,,493,-38,-38,-38,-38,-38
S,GenusOneModel,"Converts a sequence of coefficients to a genus one model of degree n, where n = 2,3,4 or 5",1,1,1,82,0,-45,2,0,0,0,0,0,0,0,82,,0,0,148,,493,-38,-38,-38,-38,-38
S,ModelToSequence,The sequence of coefficients determining the given model,0,1,0,0,0,0,0,0,0,493,,82,-38,-38,-38,-38,-38
S,Eltseq,The sequence of coefficients determining the given model,0,1,0,0,0,0,0,0,0,493,,82,-38,-38,-38,-38,-38
S,GenusOneModel,"Converts a string of coefficients to a genus one model of degree n, where n = 2,3,4 or 5",0,2,0,0,0,0,0,0,0,298,,0,0,148,,493,-38,-38,-38,-38,-38
S,ModelToString,Converts a genus one model to a string of coefficients,0,1,0,0,0,0,0,0,0,493,,298,-38,-38,-38,-38,-38
S,GenericModel,"The generic genus one model of degree n, where n is 2,3,4 or 5",0,1,0,0,0,0,0,0,0,148,,493,-38,-38,-38,-38,-38
S,RandomGenusOneModel,"A random genus one model of degree n, where n = 2,3,4 or 5",0,1,0,0,0,0,0,0,0,148,,493,-38,-38,-38,-38,-38
S,RandomModel,Same as RandomGenusOneModel,0,1,0,0,0,0,0,0,0,148,,493,-38,-38,-38,-38,-38
S,ChangeRing,The genus one model obtained by coercing the coefficients of the given model into B,0,2,0,0,0,0,0,0,0,-44,,0,0,493,,493,-38,-38,-38,-38,-38
S,CompleteTheSquare,"Given a genus one model y^2 + P(x,z)y = Q(x,z) returns the binary quartic P(x,z)^2 + 4 Q(x,z) obtained by completing the square. If the input is a binary quartic then this is immediately returned. The second returned argument is a transformation tr such that tr*oldmodel = newmodel",0,1,0,0,0,0,0,0,0,493,,493,TransG1,-38,-38,-38,-38
S,RemoveCrossTerms,"Given a genus one model y^2 + P(x,z)y = Q(x,z) returns the binary quartic (1/4)*P(x,z)^2 + Q(x,z) obtained by completing the square. If the input is a binary quartic then this is immediately returned. The second returned argument is a transformation tr such that tr*oldmodel = newmodel",0,1,0,0,0,0,0,0,0,493,,493,TransG1,-38,-38,-38,-38
S,AddCrossTerms,Converts a genus one model of degree 2 from the format without cross terms to the format with cross terms,0,1,0,0,0,0,0,0,0,493,,493,-38,-38,-38,-38,-38
S,Matrices,Converts a genus one model of degree 4 to a pair of 4 by 4 symmetric matrices,0,1,0,0,0,0,0,0,0,493,,82,-38,-38,-38,-38,-38
S,GenusOneModel,Converts a pair of 4 by 4 symmetric matrices to a genus one model of degree 4,1,0,1,82,0,177,1,0,0,0,0,0,0,0,82,,493,-38,-38,-38,-38,-38
S,GenusOneModel,The genus one model of degree 5 defined by the given 5 by 5 matrix,0,1,0,0,0,0,0,0,0,-34,,493,-38,-38,-38,-38,-38
S,Matrix,The defining matrix of the given genus one model of degree five,0,1,0,0,0,0,0,0,0,493,,177,-38,-38,-38,-38,-38
S,DefiningMatrix,The defining matrix of the given genus one model of degree five,0,1,0,0,0,0,0,0,0,493,,177,-38,-38,-38,-38,-38
S,Equation,"The defining equation of the given genus one model, which must have degree 2 or 3",0,1,0,0,0,0,0,0,0,493,,82,-38,-38,-38,-38,-38
S,DefiningEquation,"The defining equation of the given genus one model, which must have degree 2 or 3",0,1,0,0,0,0,0,0,0,493,,82,-38,-38,-38,-38,-38
S,DefiningEquations,A sequence containing defining equations for the given genus one model,0,1,0,0,0,0,0,0,0,493,,82,-38,-38,-38,-38,-38
S,Equations,A sequence containing defining equations for the curve (or scheme) associated to the given genus one model,0,1,0,0,0,0,0,0,0,493,,82,-38,-38,-38,-38,-38
S,Curve,The curve defined by the given genus one model,0,1,0,0,0,0,0,0,0,493,,371,-38,-38,-38,-38,-38
S,HyperellipticCurve,The hyperelliptic curve defined by a genus one model of degree 2,0,1,0,0,0,0,0,0,0,493,,338,-38,-38,-38,-38,-38
S,QuadricIntersection,The curve defined by a genus one model of degree 4,0,1,0,0,0,0,0,0,0,493,,371,-38,-38,-38,-38,-38
S,GenusOneModel,The genus one model of degree 2 specified by the given polynomial of degree 4,0,1,0,0,0,0,0,0,0,312,,493,-38,-38,-38,-38,-38
S,GenusOneModel,"The genus one model of degree 2 or 3 specified by the given polynomial, which can be a binary quartic or a ternary cubic",0,1,0,0,0,0,0,0,0,63,,493,-38,-38,-38,-38,-38
S,GenusOneModel,The genus one model of degree 4 or 5 determined by the given sequence of polynomials,1,0,1,82,0,63,1,0,0,0,0,0,0,0,82,,493,-38,-38,-38,-38,-38
S,GenusOneModel,The genus one model determined by the defining equation of the given curve,0,1,0,0,0,0,0,0,0,371,,493,-38,-38,-38,-38,-38
S,+,The vector sum of two genus one models,0,2,0,0,0,0,0,0,0,493,,0,0,493,,493,-38,-38,-38,-38,-38
S,*,The given genus one model with coefficients multiplied through by lambda,0,2,0,0,0,0,0,0,0,493,,0,0,-45,,493,-38,-38,-38,-38,-38
S,IsTransformation,True iff g is a transformation of the space genus one models of degree n. If true the transformation is also returned,0,2,0,0,0,0,0,0,0,303,,0,0,148,,36,TransG1,-38,-38,-38,-38
S,Tuple,The tuple defining the transformation,0,1,0,0,0,0,0,0,0,TransG1,,303,-38,-38,-38,-38,-38
S,Determinant,"The ""determinant"" of the given transformation of genus one models. The discriminant of a model is multiplied by the 12th power of this factor",0,1,0,0,0,0,0,0,0,TransG1,,-45,-38,-38,-38,-38,-38
S,ScalingFactor,"The ""determinant"" of the given transformation of genus one models. The discriminant of a model is multiplied by the 12th power of this factor",0,1,0,0,0,0,0,0,0,TransG1,,-45,-38,-38,-38,-38,-38
S,ScalingFactor,"The ""determinant"" of the given transformation of genus one models (of degree n). The discriminant of a model is multiplied by the 12th power of this factor",0,2,0,0,0,0,0,0,0,TransG1,,0,0,148,,-45,-38,-38,-38,-38,-38
S,RandomTransformation,A random transformation of the space of genus one models of degree n,0,1,0,0,0,0,0,0,0,148,,TransG1,-38,-38,-38,-38,-38
S,*,The composition tr1*tr2 of two transformations of genus one models,0,2,0,0,0,0,0,0,0,TransG1,,0,0,TransG1,,TransG1,-38,-38,-38,-38,-38
S,ComposeTransformations,The composition tr1*tr2 of two transformations of genus one models,0,2,0,0,0,0,0,0,0,TransG1,,0,0,TransG1,,TransG1,-38,-38,-38,-38,-38
S,MultiplyTransformations,The composition tr1*tr2 of two transformations of genus one models,0,2,0,0,0,0,0,0,0,TransG1,,0,0,TransG1,,TransG1,-38,-38,-38,-38,-38
S,Inverse,The inverse of a transformation of genus one models,0,1,0,0,0,0,0,0,0,TransG1,,TransG1,-38,-38,-38,-38,-38
S,InverseTransformation,The inverse of a transformation of genus one models,0,1,0,0,0,0,0,0,0,TransG1,,TransG1,-38,-38,-38,-38,-38
S,IdentityTransformation,"The identity transformation on genus one models of degree n, defined over R",0,2,0,0,0,0,0,0,0,-44,,0,0,148,,TransG1,-38,-38,-38,-38,-38
S,^,Computes the nth power of the transformation,0,2,0,0,0,0,0,0,0,148,,0,0,TransG1,,TransG1,-38,-38,-38,-38,-38
S,ApplyTransformation,Apply the transformation trans to the given genus one model,0,2,0,0,0,0,0,0,0,493,,0,0,TransG1,,493,-38,-38,-38,-38,-38
S,ChangeRing,The transformation of genus one models obtained by coercing into the ring B,0,2,0,0,0,0,0,0,0,-44,,0,0,TransG1,,TransG1,-38,-38,-38,-38,-38
S,*,Apply the transformation trans to the given genus one model,0,2,0,0,0,0,0,0,0,493,,0,0,TransG1,,493,-38,-38,-38,-38,-38
S,GenusOneModel,"A genus one model of degree n describing the image C of |n.O| : E -> P^{n-1}, where n is 2,3,4 or 5. Also returns the curve C and maps E -> C and C -> E",0,2,0,0,0,0,0,0,0,334,,0,0,148,,493,371,175,175,-38,-38
S,HesseModel,A genus one model of degree n invariant under the standard representation of the Heisenberg group,0,2,0,0,0,0,0,0,0,82,,0,0,148,,493,-38,-38,-38,-38,-38
S,DiagonalModel,A genus one model of degree n invariant under the diagonal action of mu_n,0,2,0,0,0,0,0,0,0,82,,0,0,148,,493,-38,-38,-38,-38,-38
S,SL4Invariants,The SL_4-invariants of a genus one model of degree 4,0,1,0,0,0,0,0,0,0,493,,82,-38,-38,-38,-38,-38
S,DoubleSpaceQuartic,A special case (degree 4) of DoubleGenusOneModel,0,1,0,0,0,0,0,0,0,493,,493,-38,-38,-38,-38,-38
S,SL4Covariants,"Given a genus one model (Q1,Q2) of degree 4 returns a sequence of 4 quadrics [Q1,T1,T2,Q2] where T1 and T2 are the classical covariants used in FourToTwoCovering",0,1,0,0,0,0,0,0,0,493,,82,-38,-38,-38,-38,-38
S,FourToTwoCovering,"The curves C4, C2 and the 2-covering C4 -> C2, from the given genus one model of degree 4, or from a given curve C4, which must be an intersection of quadrics",0,1,0,0,0,0,0,0,0,371,,371,371,376,-38,-38,-38
S,FourToTwoCovering,"The curves C4, C2 and the 2-covering C4 -> C2, from the given genus one model of degree 4, or from a given curve C4, which must be an intersection of quadrics",0,1,0,0,0,0,0,0,0,493,,371,371,376,-38,-38,-38
S,aInvariants,"The invariants [a1, a2, a3, a4, a6] of the given genus one model (which must have degree 2, 3 or 4)",0,1,0,0,0,0,0,0,0,493,,82,-38,-38,-38,-38,-38
S,bInvariants,"The invariants [b2, b4, b6, b8] of the given genus one model (of degree 2 or 3)",0,1,0,0,0,0,0,0,0,493,,82,-38,-38,-38,-38,-38
S,cInvariants,"The invariants [c4, c6] of the given genus one model",0,1,0,0,0,0,0,0,0,493,,82,-38,-38,-38,-38,-38
S,Invariants,"Invariants c4, c6 and Delta of the genus one model determined by the given polynomial",0,1,0,0,0,0,0,0,0,63,,-45,-45,-45,-38,-38,-38
S,Invariants,"Invariants c4, c6 and Delta of the given genus one model",0,1,0,0,0,0,0,0,0,493,,-45,-45,-45,-38,-38,-38
S,Discriminant,The discriminant Delta of the given genus one model,0,1,0,0,0,0,0,0,0,493,,-45,-38,-38,-38,-38,-38
S,Jacobian,The Jacobian of the genus one model determined by the given polynomial,0,1,0,0,0,0,0,0,0,63,,334,-38,-38,-38,-38,-38
S,Jacobian,"The Jacobian of the curve C, which must be a genus one normal curve of degree 2,3,4 or 5",0,1,0,0,0,0,0,0,0,371,,334,-38,-38,-38,-38,-38
S,Jacobian,The Jacobian of the given genus one model,0,1,0,0,0,0,0,0,0,493,,334,-38,-38,-38,-38,-38
S,Hessian,The Hessian of the genus one model determined by the given polynomial,0,1,0,0,0,0,0,0,0,63,,63,-38,-38,-38,-38,-38
S,Hessian,The Hessian H of the given genus one model,0,1,0,0,0,0,0,0,0,493,,493,-38,-38,-38,-38,-38
S,CoveringCovariants,The covariants defining the n-covering map from the given genus one model,0,1,0,0,0,0,0,0,0,493,,82,-38,-38,-38,-38,-38
S,nCovering,"The curve C, Jacobian E, and n-covering map C -> E, determined by the given genus one model",0,1,0,0,0,0,0,0,0,493,,371,334,376,-38,-38,-38
S,CoveringMap,"The n-covering map C -> E, determined by the given genus one model",0,2,0,0,0,0,0,0,0,334,,0,0,493,,376,-38,-38,-38,-38,-38
S,CoveringMap,"Given a genus one curve C defined by a genus one model of degree n = 2,3,4 or 5, computes the n-covering map C -> E, where E is the Jacobian of C",0,2,0,0,0,0,0,0,0,334,,0,0,371,,376,-38,-38,-38,-38,-38
S,Contravariants,The contravariants P and Q of the given genus one model,0,1,0,0,0,0,0,0,0,493,,493,493,-38,-38,-38,-38
S,HesseCovariants,"Covariants describing a twist of the Hesse family, for a given genus one model",0,2,0,0,0,0,0,0,0,148,,0,0,493,,493,493,-38,-38,-38,-38
S,DoubleGenusOneModel,"Given a genus one model of degree 4 or 5, this function computes 2 times the associated element in the Weil-Chatelet group, and returns the associated genus one model",0,1,0,0,0,0,0,0,0,493,,493,-38,-38,-38,-38,-38
