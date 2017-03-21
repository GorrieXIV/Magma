174,1
T,SuSpc,SuVec,0
A,SuSpc,3,R,d,M
A,SuVec,3,S,v,d
S,SuSpace,"Given an S^nu_u slope ring R, construct the module space R^n",0,2,0,0,0,0,0,0,0,148,,0,0,SuRng,,SpSpc,-38,-38,-38,-38,-38
S,ZeroVector,The zero vector of a S^nu_u space,0,1,0,0,0,0,0,0,0,SuSpc,,SpVec,-38,-38,-38,-38,-38
S,Ambient,"The ambient R^n for the S^nu_u space, where R is the slope ring",0,1,0,0,0,0,0,0,0,SuSpc,,SuSpc,-38,-38,-38,-38,-38
S,SuSpace,The S^nu_u space associated to the rows of the S^nu_u matrix M,0,1,0,0,0,0,0,0,0,SuMat,,SuSpc,-38,-38,-38,-38,-38
S,SuSpace,The S^nu_u space associated to the sequence of S^nu_u vectors v,1,0,1,82,0,SuVec,1,0,0,0,0,0,0,0,82,,SuSpc,-38,-38,-38,-38,-38
S,SuVector,The S^nu_u vector associated to the sequence of S^nu_u elements,1,0,1,82,0,SuElement,1,0,0,0,0,0,0,0,82,,SuVec,-38,-38,-38,-38,-38
S,SubConstr,,1,1,1,82,0,SuVec,2,0,0,0,0,0,0,0,82,,0,0,SuSpc,,SuSpc,-38,-38,-38,-38,-38
S,IsCoercible,,0,2,0,0,0,0,0,0,0,-1,,0,0,SuSpc,,-1,-38,-38,-38,-38,-38
S,.,The i-th basis element,0,2,0,0,0,0,0,0,0,148,,0,0,SuSpc,,SuVec,-38,-38,-38,-38,-38
S,Parent,The parent Su space,0,1,0,0,0,0,0,0,0,SuVec,,SuSpc,-38,-38,-38,-38,-38
S,Print,,0,1,0,0,1,0,0,0,0,SuSpc,,-38,-38,-38,-38,-38,-38
S,Print,,0,1,0,0,1,0,0,0,0,SuVec,,-38,-38,-38,-38,-38,-38
S,Basis,The basis of the space (row sequence),0,1,0,0,0,0,0,0,0,SuSpc,,82,-38,-38,-38,-38,-38
S,BasisMatrix,The basis matrix of the space,0,1,0,0,0,0,0,0,0,SuSpc,,SpMat,-38,-38,-38,-38,-38
S,Dimension,The dimension of a S^nu_u space,0,1,0,0,0,0,0,0,0,SuSpc,,148,-38,-38,-38,-38,-38
S,Degree,The degree of a S^nu_u space,0,1,0,0,0,0,0,0,0,SuSpc,,148,-38,-38,-38,-38,-38
S,Eltseq,Elements of the vector as a sequence,0,1,0,0,0,0,0,0,0,SuVec,,82,-38,-38,-38,-38,-38
S,GaussValuations,"Given an S^nu_u vector, return the sequence of GaussValuations",0,1,0,0,0,0,0,0,0,SuVec,,82,-38,-38,-38,-38,-38
S,WeierstrassDegrees,"Given an S^nu_u vector, return the sequence of WeierstrassDegrees",0,1,0,0,0,0,0,0,0,SuVec,,82,-38,-38,-38,-38,-38
S,LeadingTerms,"The leading terms of the constituents of a S^nu_p vector, as Laurent series",0,1,0,0,0,0,0,0,0,SuVec,,192,-38,-38,-38,-38,-38
S,WeierstrassTerms,"The Weierstrass terms of the S^nu_p vector constituents, as Laurent series",0,1,0,0,0,0,0,0,0,SuVec,,192,-38,-38,-38,-38,-38
S,+,The sum of the inputs,0,2,0,0,0,0,0,0,0,SuVec,,0,0,SuVec,,SuVec,-38,-38,-38,-38,-38
S,-,The difference of the inputs,0,2,0,0,0,0,0,0,0,SuVec,,0,0,SuVec,,SuVec,-38,-38,-38,-38,-38
S,-,Negation of the input,0,1,0,0,0,0,0,0,0,SuVec,,SuVec,-38,-38,-38,-38,-38
S,*,Scalar multiplication,0,2,0,0,0,0,0,0,0,SuElement,,0,0,SuVec,,SuVec,-38,-38,-38,-38,-38
S,*,Scalar multiplication,0,2,0,0,0,0,0,0,0,SuVec,,0,0,SuElement,,SuVec,-38,-38,-38,-38,-38
S,*,Generic scalar mult (tries coercion),0,2,0,0,0,0,0,0,0,SuVec,,0,0,-1,,SuVec,-38,-38,-38,-38,-38
S,*,Generic scalar mult (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SuVec,,SuVec,-38,-38,-38,-38,-38
S,IsWeaklyZero,Whether the input is weakly zero,0,1,0,0,0,0,0,0,0,SuVec,,36,-38,-38,-38,-38,-38
S,eq,Equality of the inputs,0,2,0,0,0,0,0,0,0,SuVec,,0,0,SuVec,,36,-38,-38,-38,-38,-38
S,ne,Nonequality of the inputs,0,2,0,0,0,0,0,0,0,SuVec,,0,0,SuVec,,36,-38,-38,-38,-38,-38
S,+,Sum of the input spaces,0,2,0,0,0,0,0,0,0,SuSpc,,0,0,SuSpc,,SuSpc,-38,-38,-38,-38,-38
S,meet,Intersection of the inputs,0,2,0,0,0,0,0,0,0,SuSpc,,0,0,SuSpc,,SuSpc,-38,-38,-38,-38,-38
S,eq,"Equality of inputs, also returns a basis transformation if so",0,2,0,0,0,0,0,0,0,SuSpc,,0,0,SuSpc,,36,SuMat,-38,-38,-38,-38
S,ne,,0,2,0,0,0,0,0,0,0,SuSpc,,0,0,SuSpc,,36,-38,-38,-38,-38,-38
S,in,Whether v is in S,0,2,0,0,0,0,0,0,0,SuSpc,,0,0,SuVec,,36,SuVec,-38,-38,-38,-38
S,IsSubspace,"Return whether A is a subspace of B, and if so an inclusion map",0,2,0,0,0,0,0,0,0,SuSpc,,0,0,SuSpc,,36,SuMat,-38,-38,-38,-38
S,IsConsistent,"Return whether x*M=v is solvable, and if so a solution vector",0,2,0,0,0,0,0,0,0,SuVec,,0,0,SuMat,,36,SuVec,-38,-38,-38,-38
S,IsConsistent,"Return whether x*M=v is sovable for all v in e, and if so a sequence of solution vectors",1,1,1,82,0,SuVec,2,0,0,0,0,0,0,0,82,,0,0,SuMat,,36,82,-38,-38,-38,-38
S,IsConsistent,"Return whether X*M=W is solvable, and if so a solution matrix and the kernel",0,2,0,0,0,0,0,0,0,SuMat,,0,0,SuMat,,36,SuMat,SuMat,-38,-38,-38
S,DirectSum,Direct sum of inputs,0,2,0,0,0,0,0,0,0,SuSpc,,0,0,SuSpc,,SuSpc,-38,-38,-38,-38,-38
S,*,Vector-times-matrix multiplication,0,2,0,0,0,0,0,0,0,SuMat,,0,0,SuVec,,SuVec,-38,-38,-38,-38,-38
S,*,Transformation of space by matrix,0,2,0,0,0,0,0,0,0,SuMat,,0,0,SuSpc,,SuSpc,-38,-38,-38,-38,-38
