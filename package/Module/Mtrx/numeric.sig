174,1
S,NumericalEigenvectors,"Given a numerical approximation to an eigenvalue of a square matrix (coercible into C), attempt to find eigenvectors corresponding to it. The usual concerns about numerical linear algebra should apply. This function is for cases that are numerically nice",0,2,0,0,0,0,0,0,0,172,,0,0,-34,,82,-38,-38,-38,-38,-38
S,DiagonalisingMatrix,"Given a square matrix M coercible into C, numerically find a matrix T for which TMT^(-1) is diagonal. Fails if Jordan form is not diagonal, or numerical difficulties arise",0,1,0,0,0,0,0,0,0,-34,,-34,-38,-38,-38,-38,-38
S,ConditionNumber,"The condition number of M, ie. the largest eigenvalue of M^t*M times 1/ the smallest. This is a measure for the stability of linear algebra",0,1,0,0,0,0,0,0,0,-34,,-45,-38,-38,-38,-38,-38
S,SpectralRadius,"The square root of then largest (and of the smallest) eigenvalue of M^t * M, ie. the smallest admissible operator norm for M wrt to L_2",0,1,0,0,0,0,0,0,0,-34,,-45,-45,-38,-38,-38,-38
S,SchurNorm,"The Schur norm, ie. the sqrt of the sum of the squares of all entries",0,1,0,0,0,0,0,0,0,-34,,-45,-38,-38,-38,-38,-38
S,MaximumNorm,The maximal entry of M,0,1,0,0,0,0,0,0,0,-34,,-45,-38,-38,-38,-38,-38
S,OperatorNorm,The subordinate matrix norm of M wrt to the L_norm norm,0,1,0,0,0,0,0,0,0,-34,,-45,-38,-38,-38,-38,-38
S,NumericalKernel_old,"Given a real or complex matrix, compute its numerical kernel. Also returns singular value approximations as a measure of stability",0,1,0,0,0,0,0,0,0,-34,,82,82,-38,-38,-38,-38
S,QLDecomposition_old,"Given a real/complex matrix, return a QL decomposition. Here Q is orthogonal/unitary and L is *lower* triangular",0,1,0,0,0,0,0,0,0,-34,,-34,-34,-38,-38,-38,-38
S,QLDecomposition,"Given a real/complex matrix, return a QL decomposition. Here Q is orthogonal/unitary of determinant 1 and L is *lower* triangular",0,1,0,0,0,0,0,0,0,-34,,177,-34,-38,-38,-38,-38
S,NumericalPseudoinverse,"Given a real/complex matrix, return the pseudoinverse",0,1,0,0,0,0,0,0,0,-34,,-34,-38,-38,-38,-38,-38
S,Subdiagonal,"Given a square matrix, return its subdiagonal elements",0,1,0,0,0,0,0,0,0,-34,,82,-38,-38,-38,-38,-38
S,NumericalSchurForm,"Given a real/complex square matrix, compute its Schur form S and an orthogonal/unitary matrix Q such that QMQ^T is equal to S",0,1,0,0,0,0,0,0,0,-34,,-34,-34,-38,-38,-38,-38
S,ParlettReinschBalancing,"Given a real/complex square matrix, return its Parlett-Reinsch balancing, that is, a matrix P such that P=DMD^(-1) for some (diagonal) matrix D, so that M and P have the same eigenvalues, with P numerically more suitable to computations. Also returns D as a second argument",1,0,1,-34,0,-76,1,0,0,0,0,0,0,0,-34,,-34,-34,-38,-38,-38,-38
S,NumericalEigenvalues,"Given a real/complex square matrix, compute approximations to its eigenvalues",1,0,1,-34,0,-76,1,0,0,0,0,0,0,0,-34,,82,-38,-38,-38,-38,-38
S,NumericalBidiagonalForm,"Given a real/complex matrix M, return B,U,V with B upper bidiagonal and M=UBV* when rows<=cols, and B lower bidiagonal in the alternative case. In the complex case, B still has real entries (all imag parts 0)",1,0,1,-34,0,-76,1,0,0,0,0,0,0,0,-34,,-34,-34,-34,-38,-38,-38
S,NumericalSingularValueDecomposition,"Given a real/complex matrix M, return S,U,V with UMV* = S, where S is the singular value matrix (diagonal), with entries the C-norms of eigenvalues",1,0,1,-34,0,-76,1,0,0,0,0,0,0,0,-34,,-34,-34,-34,-38,-38,-38
S,Pseudoinverse,Abbreviation for NumericalPseudoinverse,1,0,1,-34,0,-76,1,0,0,0,0,0,0,0,-34,,-34,-38,-38,-38,-38,-38
S,SchurForm,Abbreviation for NumericalSchurForm,1,0,1,-34,0,-76,1,0,0,0,0,0,0,0,-34,,-34,-34,-38,-38,-38,-38
S,Eigenvalues,"Abbreviation for NumericalEigenvalues, though for backwards compatibility the return type is a sequence of <eigenvalues,multiplicities> rather than just eigenvalues. The ""multiplicities"" should not be taken too seriously, due to numerical constraints. Also, only real eigenvalues are returned for a real input",1,0,1,-34,0,-76,1,0,0,0,0,0,0,0,-34,,82,-38,-38,-38,-38,-38
S,BidiagonalForm,Abbreviation for NumericalBidiagonalForm,1,0,1,-34,0,-76,1,0,0,0,0,0,0,0,-34,,-34,-34,-34,-38,-38,-38
S,SingularValueDecomposition,Abbreviation for NumericalSingularValueDecomposition,1,0,1,-34,0,-76,1,0,0,0,0,0,0,0,-34,,-34,-34,-34,-38,-38,-38
S,HessenbergForm,Abbreviation for NumericalHessenbergForm,1,0,1,-34,0,-76,1,0,0,0,0,0,0,0,-34,,-34,-34,-38,-38,-38,-38
S,Signature,"Abbreviation for NumericalSignature.					 Given a real symmetric matrix, determine its signature. May fail if numerically unstable",1,0,1,-34,0,-76,1,0,0,0,0,0,0,0,-34,,148,148,-38,-38,-38,-38
S,Inverse,Abbreviation for NumericalInverse,1,0,1,-34,0,-76,1,0,0,0,0,0,0,0,-34,,-34,-38,-38,-38,-38,-38
