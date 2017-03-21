174,1
S,CondensedAlgebra,"Returns the algebra eAe where e is a sum of primitive idempotents, one for each simple A-module. The user has two choices of randomization. The default is ""PartSpin"", which begins a spin and takes random linear combinations as the rendom elements. This should work for all algebra. The second is ""Meataxe"", which evaluated small polynomials on the generators. The user can choose the maximum degree of the monomals in the polynomial (""limprod"") and the maximum number of terms in the polynomial (""limsum""). The defaults are 7 and 8 respectively. The ""Meataxe"" method is faster for many algebras such as actions of groups on modules, but it may fail completely in other cases",0,1,0,0,0,0,0,0,0,176,,176,-38,-38,-38,-38,-38
S,CondensedAlgebraSimpleModules,Returns the sequence of simple modules for the the algebra B which is the condensed algebra of the matrix algebra A,0,2,0,0,0,0,0,0,0,176,,0,0,176,,34,-38,-38,-38,-38,-38