174,1
T,SuMatRng,SuMat,0
A,SuMatRng,3,R,r,c
A,SuMat,2,S,M
S,SuMatrixSpace,"Given a S^nu_u slope ring, construct the matrix space with r rows and c cols",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,SuRng,,SuMatRng,-38,-38,-38,-38,-38
S,ZeroMatrix,The zero matrix of a S^nu_u matrix ring,0,1,0,0,0,0,0,0,0,SuMatRng,,SuMat,-38,-38,-38,-38,-38
S,IdentityMatrix,The identity matrix of a S^nu_u matrix ring (of square dimensions),0,1,0,0,0,0,0,0,0,SuMatRng,,SuMat,-38,-38,-38,-38,-38
S,IdentityMatrix,The n-by-n identity matrix for a S^nu_u ring,0,2,0,0,0,0,0,0,0,148,,0,0,SuRng,,SuMat,-38,-38,-38,-38,-38
S,ZeroMatrix,The n-by-n zero matrix for a S^nu_u ring,0,2,0,0,0,0,0,0,0,148,,0,0,SuRng,,SuMat,-38,-38,-38,-38,-38
S,ZeroMatrix,The r-by-c zero matrix for a S^nu_u ring,0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,SuRng,,SuMat,-38,-38,-38,-38,-38
S,eq,Whether or not two matrix rings are equal,0,2,0,0,0,0,0,0,0,SuMatRng,,0,0,SuMatRng,,36,-38,-38,-38,-38,-38
S,ne,Whether or not two matrix rings are not equal,0,2,0,0,0,0,0,0,0,SuMatRng,,0,0,SuMatRng,,36,-38,-38,-38,-38,-38
S,SuMatrix,"Given a sequence of equal-length sequences of S^nu_u elements, make a matrix",1,0,1,82,1,82,0,SuElement,1,0,0,0,0,0,0,0,82,,SuMat,-38,-38,-38,-38,-38
S,SuMatrix,"Given a sequence of equal length vectors over S^nu_u, construct a matrix",1,0,1,82,0,SuVec,1,0,0,0,0,0,0,0,82,,SuMat,-38,-38,-38,-38,-38
S,SuMatrix,"Given a sequence of r*c S^nu_u elements, construct the r-by-c matrix",1,2,1,82,0,SuElement,3,0,0,0,0,0,0,0,82,,0,0,148,,0,0,148,,SuMat,-38,-38,-38,-38,-38
S,Transpose,The transpose matrix,0,1,0,0,0,0,0,0,0,SuMat,,SuMat,-38,-38,-38,-38,-38
S,eq,Whether inputs are equal,0,2,0,0,0,0,0,0,0,SuMat,,0,0,SuMat,,36,-38,-38,-38,-38,-38
S,eq,Generic equality (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SuMat,,36,-38,-38,-38,-38,-38
S,eq,Generic equality (tries coercion),0,2,0,0,0,0,0,0,0,SuMat,,0,0,-1,,36,-38,-38,-38,-38,-38
S,ne,Whether inputs are not equal,0,2,0,0,0,0,0,0,0,SuMat,,0,0,SuMat,,36,-38,-38,-38,-38,-38
S,ne,Generic nonequality (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SuMat,,36,-38,-38,-38,-38,-38
S,ne,Generic nonequality (tries coercion),0,2,0,0,0,0,0,0,0,SuMat,,0,0,-1,,36,-38,-38,-38,-38,-38
S,Print,,0,1,0,0,1,0,0,0,0,SuMat,,-38,-38,-38,-38,-38,-38
S,Print,,0,1,0,0,1,0,0,0,0,SuMatRng,,-38,-38,-38,-38,-38,-38
S,Rows,The sequence of rows of the matrix,0,1,0,0,0,0,0,0,0,SuMat,,82,-38,-38,-38,-38,-38
S,Eltseq,The sequence of elements of the matrix,0,1,0,0,0,0,0,0,0,SuMat,,82,-38,-38,-38,-38,-38
S,LeadingTerms,The matrix of leading terms (as Laurent series) of a S^nu_u matrix,0,1,0,0,0,0,0,0,0,SuMat,,-34,-38,-38,-38,-38,-38
S,WeierstrassTerms,The matrix of Weierstrass terms (as Laurent series) of a S^nu_u matrix,0,1,0,0,0,0,0,0,0,SuMat,,-34,-38,-38,-38,-38,-38
S,GaussValuations,A sequence of sequences of Gauss valuations for S^nu_u matrix elements,0,1,0,0,0,0,0,0,0,SuMat,,82,-38,-38,-38,-38,-38
S,WeierstrassDegrees,A sequence of sequences of Weierstrass degrees for S^nu_u matrix elements,0,1,0,0,0,0,0,0,0,SuMat,,82,-38,-38,-38,-38,-38
S,Parent,The parent ring of the matrix,0,1,0,0,0,0,0,0,0,SuMat,,SuMatRng,-38,-38,-38,-38,-38
S,Nrows,The number of rows of the matrix,0,1,0,0,0,0,0,0,0,SuMat,,148,-38,-38,-38,-38,-38
S,Ncols,The number of columns of the matrix,0,1,0,0,0,0,0,0,0,SuMat,,148,-38,-38,-38,-38,-38
S,IsWeaklyZero,Whether the matrix is weakly zero,0,1,0,0,0,0,0,0,0,SuMat,,36,-38,-38,-38,-38,-38
S,+,The sum of the inputs,0,2,0,0,0,0,0,0,0,SuMat,,0,0,SuMat,,SuMat,-38,-38,-38,-38,-38
S,-,The negation of the input,0,1,0,0,0,0,0,0,0,SuMat,,SuMat,-38,-38,-38,-38,-38
S,-,The difference of the inputs,0,2,0,0,0,0,0,0,0,SuMat,,0,0,SuMat,,SuMat,-38,-38,-38,-38,-38
S,*,The product of the inputs,0,2,0,0,0,0,0,0,0,SuMat,,0,0,SuMat,,SuMat,-38,-38,-38,-38,-38
S,*,Multiplication by a scalar,0,2,0,0,0,0,0,0,0,SuMat,,0,0,SuElement,,SuMat,-38,-38,-38,-38,-38
S,*,Multiplication by a scalar,0,2,0,0,0,0,0,0,0,SuElement,,0,0,SuMat,,SuMat,-38,-38,-38,-38,-38
S,*,Generic mult (tries coercion),0,2,0,0,0,0,0,0,0,SuMat,,0,0,-1,,SuMat,-38,-38,-38,-38,-38
S,*,Generic mult (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SuMat,,SuMat,-38,-38,-38,-38,-38
S,/,Division by a scalar,0,2,0,0,0,0,0,0,0,SuElement,,0,0,SuMat,,SuMat,-38,-38,-38,-38,-38
S,/,Generic div (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SuMat,,SuMat,-38,-38,-38,-38,-38
S,^,The nth power of x,0,2,0,0,0,0,0,0,0,148,,0,0,SuMat,,SuMat,-38,-38,-38,-38,-38
S,IsCoercible,,0,2,0,0,0,0,0,0,0,-1,,0,0,SuMatRng,,-1,-38,-38,-38,-38,-38
S,EchelonForm,"The echelon form E of M, with an optional transform T such that E=TM",0,1,0,0,0,0,0,0,0,SuMat,,SuMat,SuMat,-38,-38,-38,-38
S,HermiteForm,"The Hermite form H of M, with an optional transform T such that H=TM",0,1,0,0,0,0,0,0,0,SuMat,,SuMat,SuMat,-38,-38,-38,-38
S,SmithForm,"The Smith form S of M, with optional transforms P,Q with S=PMQ",0,1,0,0,0,0,0,0,0,SuMat,,SuMat,SuMat,SuMat,-38,-38,-38
S,Submatrix,"Return the r-by-c submatrix of M whose first entry is the [i,j]-th entry",0,5,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,0,0,148,,0,0,SuMat,,SuMat,-38,-38,-38,-38,-38
S,HorizontalJoin,The horizontal join of two matrices with the same number of rows,0,2,0,0,0,0,0,0,0,SuMat,,0,0,SuMat,,SuMat,-38,-38,-38,-38,-38
S,VerticalJoin,The vertical join of two matrices with the same number of columns,0,2,0,0,0,0,0,0,0,SuMat,,0,0,SuMat,,SuMat,-38,-38,-38,-38,-38
S,Kernel,"The kernel of a matrix over S^nu_u, given as an S^nu_u module",0,1,0,0,0,0,0,0,0,SuMat,,SuSpc,-38,-38,-38,-38,-38
S,Image,"The image of a matrix over S^nu_u, given as an S^nu_u module",0,1,0,0,0,0,0,0,0,SuMat,,SuSpc,SuMat,-38,-38,-38,-38
S,Inverse,The inverse of a matrix,0,1,0,0,0,0,0,0,0,SuMat,,SuMat,-38,-38,-38,-38,-38
S,IsInvertible,Whether the matrix inverts,0,1,0,0,0,0,0,0,0,SuMat,,36,SuMat,-38,-38,-38,-38
