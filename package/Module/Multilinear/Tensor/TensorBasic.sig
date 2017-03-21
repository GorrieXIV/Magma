174,1
S,Domain,Returns the Cartesian factors in the domain of t,0,1,0,0,0,0,0,0,0,TenSpcElt,,168,-38,-38,-38,-38,-38
S,Codomain,Returns the codomain of t,0,1,0,0,0,0,0,0,0,TenSpcElt,,-1,-38,-38,-38,-38,-38
S,Valence,Returns the valence of t,0,1,0,0,0,0,0,0,0,TenSpcElt,,148,-38,-38,-38,-38,-38
S,Frame,Returns the frame of t,0,1,0,0,0,0,0,0,0,TenSpcElt,,168,-38,-38,-38,-38,-38
S,TensorCategory,Returns the tensor category of t,0,1,0,0,0,0,0,0,0,TenSpcElt,,TenCat,-38,-38,-38,-38,-38
S,IsContravariant,Decides if the tensor is contravariant,0,1,0,0,0,0,0,0,0,TenSpcElt,,36,-38,-38,-38,-38,-38
S,IsCovariant,Decides if the tensor is covariant,0,1,0,0,0,0,0,0,0,TenSpcElt,,36,-38,-38,-38,-38,-38
S,ChangeTensorCategory,Returns the given tensor in the given category,0,2,0,0,0,0,0,0,0,TenCat,,0,0,TenSpcElt,,TenSpcElt,-38,-38,-38,-38,-38
S,ChangeTensorCategory,Returns the given tensor in the given category,0,2,0,0,1,0,0,0,0,TenCat,,1,1,TenSpcElt,,-38,-38,-38,-38,-38,-38
S,BaseRing,"For the tensor t, where each Vi is a R-bimodule, returns R. If Vi is not an R-bimodule, then returns false",0,1,0,0,0,0,0,0,0,TenSpcElt,,-44,-38,-38,-38,-38,-38
S,BaseField,"For the tensor t, where each Vi is a F-vector space, returns F. If Vi is not an F-vector space, then returns false",0,1,0,0,0,0,0,0,0,TenSpcElt,,-24,-38,-38,-38,-38,-38
S,Image,Returns the image of t as a subspace of the codomain,0,1,0,0,0,0,0,0,0,TenSpcElt,,191,175,-38,-38,-38,-38
S,StructureConstants,Returns the structure constants of t,0,1,0,0,0,0,0,0,0,TenSpcElt,,82,-38,-38,-38,-38,-38
S,Eltseq,Returns the structure constants of t,0,1,0,0,0,0,0,0,0,TenSpcElt,,82,-38,-38,-38,-38,-38
S,Slice,Returns the sequence of the tensor with the given grid,1,1,1,82,0,83,2,0,0,0,0,0,0,0,82,,0,0,TenSpcElt,,82,-38,-38,-38,-38,-38
S,InducedTensor,Returns the tensor induced by the grid,1,1,1,82,0,83,2,0,0,0,0,0,0,0,82,,0,0,TenSpcElt,,TenSpcElt,-38,-38,-38,-38,-38
S,Compress,Compress all 1-dimensional spaces in the domain,0,1,0,0,0,0,0,0,0,TenSpcElt,,TenSpcElt,-38,-38,-38,-38,-38
S,AsMatrices,Returns the sequence of matrices,0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,TenSpcElt,,82,-38,-38,-38,-38,-38
S,SystemOfForms,Returns the system of forms for the given 2-tensor,0,1,0,0,0,0,0,0,0,TenSpcElt,,82,-38,-38,-38,-38,-38
S,Foliation,Foliates along the ith component,0,2,0,0,0,0,0,0,0,148,,0,0,TenSpcElt,,-34,-38,-38,-38,-38,-38
S,NondegenerateTensor,Returns the associated nondegenerate tensor of M along with a homotopism. Note that the domain and codomain of the returned tensor will be vector spaces,0,1,0,0,0,0,0,0,0,TenSpcElt,,TenSpcElt,Hmtp,-38,-38,-38,-38
S,IsNondegenerate,Decides if M is nondegenerate,0,1,0,0,0,0,0,0,0,TenSpcElt,,36,-38,-38,-38,-38,-38
S,FullyNondegenerateTensor,Returns the fully nondegenerate tensor of M,0,1,0,0,0,0,0,0,0,TenSpcElt,,TenSpcElt,Hmtp,-38,-38,-38,-38
S,IsFullyNondegenerate,Decides if M is fully nondegenerate,0,1,0,0,0,0,0,0,0,TenSpcElt,,36,-38,-38,-38,-38,-38
S,AssociatedForm,"If M : Vn x ... x V1 >-> V0, returns the associated form F : Vn x ... x V0 >-> K as vector spaces",0,1,0,0,0,0,0,0,0,TenSpcElt,,TenSpcElt,-38,-38,-38,-38,-38
S,IsAntisymmetric,Decides if M is antisymmetric,0,1,0,0,0,0,0,0,0,TenSpcElt,,36,-38,-38,-38,-38,-38
S,IsAlternating,Decides if t is alternating,0,1,0,0,0,0,0,0,0,TenSpcElt,,36,-38,-38,-38,-38,-38
S,IsSymmetric,Decides if M is symmetric,0,1,0,0,0,0,0,0,0,TenSpcElt,,36,-38,-38,-38,-38,-38
S,Subtensor,Returns the smallest submap of M containing the Cartesian product of D in the domain and C in the codomain,0,3,0,0,0,0,0,0,0,-1,,0,0,168,,0,0,TenSpcElt,,TenSpcElt,-38,-38,-38,-38,-38
S,Subtensor,"Returns the smallest submap of M containing S. The first v entries of S are contained in the domain of M, and the last entry of S is contained in the codomain of M",0,2,0,0,0,0,0,0,0,168,,0,0,TenSpcElt,,TenSpcElt,-38,-38,-38,-38,-38
S,IsSubtensor,Decides if N is a subtensor of M,0,2,0,0,0,0,0,0,0,TenSpcElt,,0,0,TenSpcElt,,36,-38,-38,-38,-38,-38
S,LocalIdeal,"Returns the smallest submap of M which is a local ideal containing D in the domain and C in the codomain. Here, I is a subset of integers corresponding to the Cartesian factors in the domain",1,3,1,83,0,148,4,0,0,0,0,0,0,0,83,,0,0,-1,,0,0,168,,0,0,TenSpcElt,,TenSpcElt,-38,-38,-38,-38,-38
S,LocalIdeal,"Returns the smallest submap of M which is a local ideal containing S. Here, I is a subset of integers corresponding to the Cartesian factors in the domain",1,2,1,83,0,148,3,0,0,0,0,0,0,0,83,,0,0,168,,0,0,TenSpcElt,,TenSpcElt,-38,-38,-38,-38,-38
S,LocalIdeal,"Returns the smallest submap of M which is a local ideal containing N. Here, I is a subset of integers corresponding to the Cartesian factors in the domain",1,2,1,83,0,148,3,0,0,0,0,0,0,0,83,,0,0,TenSpcElt,,0,0,TenSpcElt,,TenSpcElt,-38,-38,-38,-38,-38
S,IsLocalIdeal,"Decide if N is a local ideal of M. Here, S is a subset of integers corresponding to the Cartesian factors in the domain",1,2,1,83,0,148,3,0,0,0,0,0,0,0,83,,0,0,TenSpcElt,,0,0,TenSpcElt,,36,-38,-38,-38,-38,-38
S,Ideal,Returns the smallest submap of M containing D in the domain and C in the codomain that is an ideal of M,0,3,0,0,0,0,0,0,0,-1,,0,0,168,,0,0,TenSpcElt,,TenSpcElt,-38,-38,-38,-38,-38
S,Ideal,Returns the smallest submap of M containing S that is an ideal of M,0,2,0,0,0,0,0,0,0,168,,0,0,TenSpcElt,,TenSpcElt,-38,-38,-38,-38,-38
S,Ideal,Returns the smallest submap of M containing N that is an ideal of M,0,2,0,0,0,0,0,0,0,TenSpcElt,,0,0,TenSpcElt,,TenSpcElt,-38,-38,-38,-38,-38
S,IsIdeal,Decides if N is an ideal of M,0,2,0,0,0,0,0,0,0,TenSpcElt,,0,0,TenSpcElt,,36,-38,-38,-38,-38,-38
S,LocalQuotient,"Returns the local quotient of M by the local ideal N. Here, S is a subset of integers corresponding to the Cartesian factors in the domain",0,3,0,0,0,0,0,0,0,83,,0,0,TenSpcElt,,0,0,TenSpcElt,,TenSpcElt,Hmtp,-38,-38,-38,-38
S,Quotient,Returns the quotient of M by the ideal N,0,2,0,0,0,0,0,0,0,TenSpcElt,,0,0,TenSpcElt,,TenSpcElt,Hmtp,-38,-38,-38,-38
S,/,Returns the quotient M/N,0,2,0,0,0,0,0,0,0,TenSpcElt,,0,0,TenSpcElt,,TenSpcElt,Hmtp,-38,-38,-38,-38
