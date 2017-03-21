174,1
T,SpMatRng,SpMat,0
A,SpMatRng,3,R,r,c
A,SpMat,2,S,M
S,SpMatrixSpace,"Given a S^nu_p slope ring, construct the matrix space with r rows and c cols",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,SpRng,,SpMatRng,-38,-38,-38,-38,-38
S,ZeroMatrix,The zero matrix of a S^nu_p matrix ring,0,1,0,0,0,0,0,0,0,SpMatRng,,SpMat,-38,-38,-38,-38,-38
S,IdentityMatrix,The identity matrix of a S^nu_p matrix ring (of square dimensions),0,1,0,0,0,0,0,0,0,SpMatRng,,SpMat,-38,-38,-38,-38,-38
S,IdentityMatrix,The n-by-n identity matrix for a S^nu_p ring,0,2,0,0,0,0,0,0,0,148,,0,0,SpRng,,SpMat,-38,-38,-38,-38,-38
S,ZeroMatrix,The n-by-n zero matrix for a S^nu_p ring,0,2,0,0,0,0,0,0,0,148,,0,0,SpRng,,SpMat,-38,-38,-38,-38,-38
S,ZeroMatrix,The r-by-c zero matrix for a S^nu_p ring,0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,SpRng,,SpMat,-38,-38,-38,-38,-38
S,eq,Whether or not two matrix rings are equal,0,2,0,0,0,0,0,0,0,SpMatRng,,0,0,SpMatRng,,36,-38,-38,-38,-38,-38
S,ne,Whether or not two matrix rings are not equal,0,2,0,0,0,0,0,0,0,SpMatRng,,0,0,SpMatRng,,36,-38,-38,-38,-38,-38
S,SpMatrix,"Given a sequence of equal-length sequences of S^nu_p elements, make a matrix",1,0,1,82,1,82,0,SpElement,1,0,0,0,0,0,0,0,82,,SpMat,-38,-38,-38,-38,-38
S,SpMatrix,"Given a sequence of equal length vectors over S^nu_p, construct a matrix",1,0,1,82,0,SpVec,1,0,0,0,0,0,0,0,82,,SpMat,-38,-38,-38,-38,-38
S,SpMatrix,"Given a sequence of r*c S^nu_p elements, construct the r-by-c matrix",1,2,1,82,0,SpElement,3,0,0,0,0,0,0,0,82,,0,0,148,,0,0,148,,SpMat,-38,-38,-38,-38,-38
S,Transpose,The transpose matrix,0,1,0,0,0,0,0,0,0,SpMat,,SpMat,-38,-38,-38,-38,-38
S,HasUniverse,"Whether a sequence has a universe. If so, return said universe",0,1,0,0,0,0,0,0,0,82,,36,-1,-38,-38,-38,-38
S,eq,Whether inputs are equal,0,2,0,0,0,0,0,0,0,SpMat,,0,0,SpMat,,36,-38,-38,-38,-38,-38
S,eq,Generic equality (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SpMat,,36,-38,-38,-38,-38,-38
S,eq,Generic equality (tries coercion),0,2,0,0,0,0,0,0,0,SpMat,,0,0,-1,,36,-38,-38,-38,-38,-38
S,ne,Whether inputs are not equal,0,2,0,0,0,0,0,0,0,SpMat,,0,0,SpMat,,36,-38,-38,-38,-38,-38
S,ne,Generic nonequality (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SpMat,,36,-38,-38,-38,-38,-38
S,ne,Generic nonequality (tries coercion),0,2,0,0,0,0,0,0,0,SpMat,,0,0,-1,,36,-38,-38,-38,-38,-38
S,Print,,0,1,0,0,1,0,0,0,0,SpMat,,-38,-38,-38,-38,-38,-38
S,Print,,0,1,0,0,1,0,0,0,0,SpMatRng,,-38,-38,-38,-38,-38,-38
S,Rows,The sequence of rows of the matrix,0,1,0,0,0,0,0,0,0,SpMat,,82,-38,-38,-38,-38,-38
S,Eltseq,The sequence of elements of the matrix,0,1,0,0,0,0,0,0,0,SpMat,,82,-38,-38,-38,-38,-38
S,LeadingTerms,The matrix of leading terms (as power series) of a S^nu_p matrix,0,1,0,0,0,0,0,0,0,SpMat,,-34,-38,-38,-38,-38,-38
S,WeierstrassTerms,The matrix of Weierstrass terms (as power series) of a S^nu_p matrix,0,1,0,0,0,0,0,0,0,SpMat,,-34,-38,-38,-38,-38,-38
S,GaussValuations,A sequence of sequences of Gauss valuations for S^nu_p matrix elements,0,1,0,0,0,0,0,0,0,SpMat,,82,-38,-38,-38,-38,-38
S,WeierstrassDegrees,A sequence of sequences of Weierstrass degrees for S^nu_p matrix elements,0,1,0,0,0,0,0,0,0,SpMat,,82,-38,-38,-38,-38,-38
S,Parent,The parent ring of the matrix,0,1,0,0,0,0,0,0,0,SpMat,,SpMatRng,-38,-38,-38,-38,-38
S,Nrows,The number of rows of the matrix,0,1,0,0,0,0,0,0,0,SpMat,,148,-38,-38,-38,-38,-38
S,Ncols,The number of columns of the matrix,0,1,0,0,0,0,0,0,0,SpMat,,148,-38,-38,-38,-38,-38
S,IsWeaklyZero,Whether the matrix is weakly zero,0,1,0,0,0,0,0,0,0,SpMat,,36,-38,-38,-38,-38,-38
S,+,The sum of the inputs,0,2,0,0,0,0,0,0,0,SpMat,,0,0,SpMat,,SpMat,-38,-38,-38,-38,-38
S,-,The negation of the input,0,1,0,0,0,0,0,0,0,SpMat,,SpMat,-38,-38,-38,-38,-38
S,-,The difference of the inputs,0,2,0,0,0,0,0,0,0,SpMat,,0,0,SpMat,,SpMat,-38,-38,-38,-38,-38
S,*,The product of the inputs,0,2,0,0,0,0,0,0,0,SpMat,,0,0,SpMat,,SpMat,-38,-38,-38,-38,-38
S,*,Multiplication by a scsalar,0,2,0,0,0,0,0,0,0,SpMat,,0,0,SpElement,,SpMat,-38,-38,-38,-38,-38
S,*,Multiplication by a scsalar,0,2,0,0,0,0,0,0,0,SpElement,,0,0,SpMat,,SpMat,-38,-38,-38,-38,-38
S,*,Generic mult (tries coercion),0,2,0,0,0,0,0,0,0,SpMat,,0,0,-1,,SpMat,-38,-38,-38,-38,-38
S,*,Generic mult (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SpMat,,SpMat,-38,-38,-38,-38,-38
S,/,Division by a scalar,0,2,0,0,0,0,0,0,0,SpElement,,0,0,SpMat,,SpMat,-38,-38,-38,-38,-38
S,/,Generic div (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SpMat,,SpMat,-38,-38,-38,-38,-38
S,^,The nth power of x,0,2,0,0,0,0,0,0,0,148,,0,0,SpMat,,SpMat,-38,-38,-38,-38,-38
S,IsCoercible,,0,2,0,0,0,0,0,0,0,-1,,0,0,SpMatRng,,-1,-38,-38,-38,-38,-38
S,EchelonForm,"The echelon form E of M, with an optional transform T such that E=TM",0,1,0,0,0,0,0,0,0,SpMat,,SpMat,SpMat,-38,-38,-38,-38
S,HermiteForm,"The Hermite form H of M, with an optional transform T such that H=TM",0,1,0,0,0,0,0,0,0,SpMat,,SpMat,SpMat,-38,-38,-38,-38
S,SmithForm,"The Smith form S of M, with optional transforms P,Q with S=PMQ",0,1,0,0,0,0,0,0,0,SpMat,,SpMat,SpMat,SpMat,148,-38,-38
S,Submatrix,"Return the r-by-c submatrix of M whose first entry is the [i,j]-th entry",0,5,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,0,0,148,,0,0,SpMat,,SpMat,-38,-38,-38,-38,-38
S,HorizontalJoin,The horizontal join of two matrices with the same number of rows,0,2,0,0,0,0,0,0,0,SpMat,,0,0,SpMat,,SpMat,-38,-38,-38,-38,-38
S,VerticalJoin,The vertical join of two matrices with the same number of columns,0,2,0,0,0,0,0,0,0,SpMat,,0,0,SpMat,,SpMat,-38,-38,-38,-38,-38
S,Kernel,"The kernel of a matrix over S^nu_p, given as an S^nu_p module",0,1,0,0,0,0,0,0,0,SpMat,,SpSpc,-38,-38,-38,-38,-38
S,Image,"The image of a matrix over S^nu_p, given as an S^nu_p module",0,1,0,0,0,0,0,0,0,SpMat,,SpSpc,SpMat,-38,-38,-38,-38
S,Inverse,The inverse of a S^nu_p matrix. An error occurs if it is not invertible,0,1,0,0,0,0,0,0,0,SpMat,,SpMat,-38,-38,-38,-38,-38
S,IsInvertible,"Whether a square S^nu_p matrix is invertible, and if so the inverse",0,1,0,0,0,0,0,0,0,SpMat,,36,SpMat,-38,-38,-38,-38
