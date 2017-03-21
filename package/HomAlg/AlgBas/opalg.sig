174,1
S,PathTreeCyclicModule,,0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,181,,25,-38,-38,-38,-38,-38
S,OppositeAlgebra,"Given a basic algebra A, creates the opposite algebra. This is the algebra with the same set of elements but with multiplication * given by x*y = yx",0,1,0,0,0,0,0,0,0,34,,34,-38,-38,-38,-38,-38
S,BaseChangeMatrix,"Given a basic algebra A and its opposite algebra O, creates the change of basis matrix B from the vector space of A to the vector space of O, so that if x, y are in A then (xy)B is the same as (yB)(xB) in O",0,1,0,0,0,0,0,0,0,34,,155,-38,-38,-38,-38,-38
S,Dual,Returns the dual of a module M over a basic algebra A as a module over the algebra O which is the opposite algebra of A,0,1,0,0,0,0,0,0,0,25,,25,-38,-38,-38,-38,-38
S,Dual,"Given a homomorphism between two modules over a basic algebra A, returns the dual homomorphism between the dual modules over the opposite algebra O of A",0,1,0,0,0,0,0,0,0,155,,155,-38,-38,-38,-38,-38
S,InjectiveModule,The injective hull of the nth simple A-module,0,2,0,0,0,0,0,0,0,148,,0,0,34,,25,-38,-38,-38,-38,-38
S,InjectiveModule,"The injective module that is the injective hull of direct sum of S[1] copies of the first simple module for the algebra, S[2] copies of the second simple module, etc",0,2,0,0,0,0,0,0,0,82,,0,0,34,,25,-38,-38,-38,-38,-38
S,InjectiveHull,"Given a module M over a basic algebra A, returns the injective hull I of M as an A-module and the inclusion homomorphism theta: M --> I",0,1,0,0,0,0,0,0,0,25,,25,155,82,155,155,-38
