174,1
T,SpSpc,SpVec,0
A,SpSpc,3,R,d,M
A,SpVec,3,S,v,d
S,SpSpace,"Given an S^nu_p slope ring R, construct the module space R^n",0,2,0,0,0,0,0,0,0,148,,0,0,SpRng,,SpSpc,-38,-38,-38,-38,-38
S,ZeroVector,The zero vector of a S^nu_p space,0,1,0,0,0,0,0,0,0,SpSpc,,SpVec,-38,-38,-38,-38,-38
S,Ambient,"The ambient R^n for the S^nu_p space, where R is the slope ring",0,1,0,0,0,0,0,0,0,SpSpc,,SpSpc,-38,-38,-38,-38,-38
S,SpSpace,The S^nu_p space associated to the rows of the S^nu_p matrix M,0,1,0,0,0,0,0,0,0,SpMat,,SpSpc,-38,-38,-38,-38,-38
S,SpSpace,The S^nu_p space associated to the sequence of S^nu_p vectors v,1,0,1,82,0,SpVec,1,0,0,0,0,0,0,0,82,,SpSpc,-38,-38,-38,-38,-38
S,SpVector,The S^nu_p vector associated to the sequence of S^nu_p elements,1,0,1,82,0,SpElement,1,0,0,0,0,0,0,0,82,,SpVec,-38,-38,-38,-38,-38
S,SubConstr,,1,1,1,82,0,SpVec,2,0,0,0,0,0,0,0,82,,0,0,SpSpc,,SpSpc,-38,-38,-38,-38,-38
S,IsCoercible,,0,2,0,0,0,0,0,0,0,-1,,0,0,SpSpc,,-1,-38,-38,-38,-38,-38
S,.,The i-th basis element,0,2,0,0,0,0,0,0,0,148,,0,0,SpSpc,,SpVec,-38,-38,-38,-38,-38
S,Parent,The parent Sp space,0,1,0,0,0,0,0,0,0,SpVec,,SpSpc,-38,-38,-38,-38,-38
S,Print,,0,1,0,0,1,0,0,0,0,SpSpc,,-38,-38,-38,-38,-38,-38
S,Print,,0,1,0,0,1,0,0,0,0,SpVec,,-38,-38,-38,-38,-38,-38
S,Basis,The basis of the space (row sequence),0,1,0,0,0,0,0,0,0,SpSpc,,82,-38,-38,-38,-38,-38
S,BasisMatrix,The basis matrix of the space,0,1,0,0,0,0,0,0,0,SpSpc,,SpMat,-38,-38,-38,-38,-38
S,Dimension,The dimension of a S^nu_p space,0,1,0,0,0,0,0,0,0,SpSpc,,148,-38,-38,-38,-38,-38
S,Degree,The degree of a S^nu_p space,0,1,0,0,0,0,0,0,0,SpSpc,,148,-38,-38,-38,-38,-38
S,Eltseq,Elements of the vector as a sequence,0,1,0,0,0,0,0,0,0,SpVec,,82,-38,-38,-38,-38,-38
S,GaussValuations,"Given an S^nu_p vector, return the sequence of GaussValuations",0,1,0,0,0,0,0,0,0,SpVec,,82,-38,-38,-38,-38,-38
S,WeierstrassDegrees,"Given an S^nu_p vector, return the sequence of WeierstrassDegrees",0,1,0,0,0,0,0,0,0,SpVec,,82,-38,-38,-38,-38,-38
S,LeadingTerms,"The leading terms of the constituents of a S^nu_p vector, as power series",0,1,0,0,0,0,0,0,0,SpVec,,192,-38,-38,-38,-38,-38
S,WeierstrassTerms,"The Weierstrass terms of the constituents of a S^nu_p vector, as power series",0,1,0,0,0,0,0,0,0,SpVec,,192,-38,-38,-38,-38,-38
S,+,The sum of the inputs,0,2,0,0,0,0,0,0,0,SpVec,,0,0,SpVec,,SpVec,-38,-38,-38,-38,-38
S,-,The difference of the inputs,0,2,0,0,0,0,0,0,0,SpVec,,0,0,SpVec,,SpVec,-38,-38,-38,-38,-38
S,-,Negation of the input,0,1,0,0,0,0,0,0,0,SpVec,,SpVec,-38,-38,-38,-38,-38
S,*,Scalar multiplication,0,2,0,0,0,0,0,0,0,SpElement,,0,0,SpVec,,SpVec,-38,-38,-38,-38,-38
S,*,Scalar multiplication,0,2,0,0,0,0,0,0,0,SpVec,,0,0,SpElement,,SpVec,-38,-38,-38,-38,-38
S,*,Generic scalar mult (tries coercion),0,2,0,0,0,0,0,0,0,SpVec,,0,0,-1,,SpVec,-38,-38,-38,-38,-38
S,*,Generic scalar mult (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SpVec,,SpVec,-38,-38,-38,-38,-38
S,IsWeaklyZero,Whether the input is weakly zero,0,1,0,0,0,0,0,0,0,SpVec,,36,-38,-38,-38,-38,-38
S,eq,Equality of inputs,0,2,0,0,0,0,0,0,0,SpVec,,0,0,SpVec,,36,-38,-38,-38,-38,-38
S,ne,Nonequality of inputs,0,2,0,0,0,0,0,0,0,SpVec,,0,0,SpVec,,36,-38,-38,-38,-38,-38
S,+,Sum of the input spaces,0,2,0,0,0,0,0,0,0,SpSpc,,0,0,SpSpc,,SpSpc,-38,-38,-38,-38,-38
S,meet,Intersection of the inputs,0,2,0,0,0,0,0,0,0,SpSpc,,0,0,SpSpc,,SpSpc,-38,-38,-38,-38,-38
S,eq,"Equality of inputs, also returns a basis transformation if so",0,2,0,0,0,0,0,0,0,SpSpc,,0,0,SpSpc,,36,SpMat,-38,-38,-38,-38
S,ne,Nonequality of inputs,0,2,0,0,0,0,0,0,0,SpSpc,,0,0,SpSpc,,36,-38,-38,-38,-38,-38
S,in,Whether v is in S,0,2,0,0,0,0,0,0,0,SpSpc,,0,0,SpVec,,36,SpVec,-38,-38,-38,-38
S,IsSubspace,"Return whether A is a subspace of B, and if so an inclusion map",0,2,0,0,0,0,0,0,0,SpSpc,,0,0,SpSpc,,36,SpMat,-38,-38,-38,-38
S,IsConsistent,"Return whether x*M=v is solvable, and if so a solution vector",0,2,0,0,0,0,0,0,0,SpVec,,0,0,SpMat,,36,SpVec,-38,-38,-38,-38
S,IsConsistent,"Return whether x*M=v is sovable for all v in e, and if so a sequence of solution vectors",1,1,1,82,0,SpVec,2,0,0,0,0,0,0,0,82,,0,0,SpMat,,36,82,-38,-38,-38,-38
S,IsConsistent,"Return whether X*M=W is solvable, and if so a solution matrix and the kernel",0,2,0,0,0,0,0,0,0,SpMat,,0,0,SpMat,,36,SpMat,SpMat,-38,-38,-38
S,DirectSum,Direct sum of inputs,0,2,0,0,0,0,0,0,0,SpSpc,,0,0,SpSpc,,SpSpc,-38,-38,-38,-38,-38
S,*,Vector-times-matrix multiplication,0,2,0,0,0,0,0,0,0,SpMat,,0,0,SpVec,,SpVec,-38,-38,-38,-38,-38
S,*,Transformation of space by matrix,0,2,0,0,0,0,0,0,0,SpMat,,0,0,SpSpc,,SpSpc,-38,-38,-38,-38,-38
