174,1
A,AlgBasGrpP,3,Group,PCGroup,PCMap
S,BasicAlgebra,Given a finite p-group G and a field k of characteristic p and returns the group algebra kG in the form of a basic algebra,0,2,0,0,0,0,0,0,0,84,,0,0,129,,284,-38,-38,-38,-38,-38
S,BasicAlgebra,Given a finite p-group G and a field k of characteristic p and returns the group algebra kG in the form of a basic algebra,0,2,0,0,0,0,0,0,0,84,,0,0,224,,284,-38,-38,-38,-38,-38
S,BasicAlgebra,Given a finite p-group G and a field k of characteristic p and returns the group algebra kG in the form of a basic algebra,0,2,0,0,0,0,0,0,0,84,,0,0,107,,284,-38,-38,-38,-38,-38
S,Group,The group which defines A,0,1,0,0,0,0,0,0,0,284,,-27,-38,-38,-38,-38,-38
S,PCGroup,The internal PC group of A,0,1,0,0,0,0,0,0,0,284,,-27,-38,-38,-38,-38,-38
S,PCMap,The map from Group(A) to PCGroup(A),0,1,0,0,0,0,0,0,0,284,,-27,-38,-38,-38,-38,-38
S,BasicAlgebra,"Creates a basic algebra from a minimal set of relations. The input is a free algebra, the number of idempotents, a list of the right and left idempotents corresponding to the nonidempotent generators of the algebra and a list of relations. The function creates the extra relations that are natural to the idempotents and the multiplications of the idempotents on the nonidempotent generators. Thus the user needs only supply the relations among the nonidempotent generators",0,4,0,0,0,0,0,0,0,82,,0,0,82,,0,0,148,,0,0,87,,34,-38,-38,-38,-38,-38
S,TensorProduct,Creates the tensor product of two basic algebras,0,2,0,0,0,0,0,0,0,34,,0,0,34,,34,-38,-38,-38,-38,-38
S,ZeroModule,The zero A-module,0,1,0,0,0,0,0,0,0,34,,25,-38,-38,-38,-38,-38
S,ZeroMap,The zero map from M to N,0,2,0,0,0,0,0,0,0,25,,0,0,25,,155,-38,-38,-38,-38,-38
A,Grp,1,BasicAlgebra
S,GModule,The standard module of A as a module over Group(A) and as a module over PCgroup(A),0,1,0,0,0,0,0,0,0,284,,103,103,-38,-38,-38,-38
S,AModule,Converts a GModule over a p-group to a module over the basic algbra of that group,0,1,0,0,0,0,0,0,0,103,,343,-38,-38,-38,-38,-38
S,GModule,Converts a module for the basic algebra of a p-group into a module over the p-group,0,1,0,0,0,0,0,0,0,25,,103,-38,-38,-38,-38,-38
S,BasicAlgebra,The basic algebra of the p-group G over the prime field of characteristic p,0,1,0,0,0,0,0,0,0,-27,,284,-38,-38,-38,-38,-38
S,BasicAlgebraGrpPToBasicAlgebra,Converts the a basic algebra of a p-group to the type AlgBas,0,1,0,0,0,0,0,0,0,284,,34,-38,-38,-38,-38,-38
