174,1
A,RngMPol,1,quotient_module
A,ModMPol,1,canonical_module
S,ModuleProjectM,,0,2,0,0,0,0,0,0,0,64,,0,0,67,,67,82,-38,-38,-38,-38
S,ModuleProject,,0,2,0,0,0,0,0,0,0,64,,0,0,64,,67,82,-38,-38,-38,-38
S,GenModuleProject,,0,1,0,0,0,0,0,0,0,67,,67,82,175,-38,-38,-38
S,StoRModule,,0,4,0,0,0,0,0,0,0,175,,0,0,82,,0,0,64,,0,0,67,,67,-38,-38,-38,-38,-38
S,ImageFromMat,,0,4,0,0,0,0,0,0,0,148,,0,0,380,,0,0,64,,0,0,-34,,380,474,-38,-38,-38,-38
S,MyGradedMap,convenience function,0,4,0,0,0,0,0,0,0,148,,0,0,-34,,0,0,270,,0,0,270,,270,-38,-38,-38,-38,-38
S,GradedDualComplex,Returns the dual complex of a graded module complex adding a weight twist,0,2,0,0,0,0,0,0,0,148,,0,0,270,,270,-38,-38,-38,-38,-38
S,GradedDual,"Computes the graded dual Hom(M,can_R/I) where I is the annihilator of equidimensional module M over polynomial ring R",0,2,0,0,0,0,0,0,0,64,,0,0,270,,270,175,-38,-38,-38,-38
S,GradedDualWithHoms,"Computes the graded dual M*=Hom(M,can_R/I) where I is the annihilator of equidimensional module M over polynomial ring R. The map returned takes elements of M* to the correponding module homomorphism. hms is a sequence of endomorphisms f:M->M and the function also computes and returns the sequence of corresponding dual endomorphisms f*:M*->M*",0,3,0,0,0,0,0,0,0,82,,0,0,64,,0,0,270,,270,175,82,-38,-38,-38
S,DoubleDual,"Computes the graded double dual M** = Hom(Hom(M,can_R/I), R/I) where I is the annihilator of equidimensional module M over polynomial ring R. This gives the ""saturation"" of M. If retMap is true then the natural map M->M** is also computed and returned",0,3,0,0,0,0,0,0,0,36,,0,0,64,,0,0,270,,270,175,-38,-38,-38,-38
S,ModuleSaturation,,0,1,0,0,0,0,0,0,0,67,,67,-38,-38,-38,-38,-38
S,CanonicalModule,"I is a homogeneous ideal (for the usual grading) of k[x0,..,xn]. Returns a module KX giving the canonical sheaf on X, the scheme in P^n defined by I. NB: It is assumed that X is an equidimensional CM scheme. If Saturate is true, then the module returned is always the maximal module giving KX. The second return value gives whether KX is definitely saturated in any case",0,1,0,0,0,0,0,0,0,64,,67,36,-38,-38,-38,-38
