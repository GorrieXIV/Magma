174,1
S,ZeroChainMap,Create the chain map from C to D all of whose module maps are zero,0,2,0,0,0,0,0,0,0,183,,0,0,183,,182,-38,-38,-38,-38,-38
S,IsProperChainMap,Checks to see if we can take kernel and cokernel without truncating the complexes,0,1,0,0,0,0,0,0,0,182,,36,-38,-38,-38,-38,-38
S,IsChainMap,"True if the list of maps L from the terms of complex C to the terms of D is a chain complex of degree n, i. e. it has the right length and the diagram commutes",0,4,0,0,0,0,0,0,0,148,,0,0,183,,0,0,183,,0,0,168,,36,-38,-38,-38,-38,-38
S,IsChainMap,True if the chain map f really is a chain map,0,1,0,0,0,0,0,0,0,182,,36,-38,-38,-38,-38,-38
S,DefinedInDegrees,The first and last degree of the domain of f on which the chain map f is defined,0,1,0,0,0,0,0,0,0,182,,148,148,-38,-38,-38,-38
S,ModuleMaps,The module maps of f,0,1,0,0,0,0,0,0,0,182,,168,-38,-38,-38,-38,-38
S,Kernel,The kernel complex of f and the chain map of the inclusion. In the event that the chain map is not defined on a particular term of the Domain then the entire term is assumed to be in the kernel,0,1,0,0,0,0,0,0,0,182,,183,182,-38,-38,-38,-38
S,Cokernel,The cokernel complex of f and the chain map of the projection onto the quotient,0,1,0,0,0,0,0,0,0,182,,183,182,-38,-38,-38,-38
S,Image,The image complex I of f and the inclusion of I into the codomain and the projection of the domain onto I. If the chain map has no defined image into a particular term of the codomain then the image is assumed to be zero,0,1,0,0,0,0,0,0,0,182,,183,182,182,-38,-38,-38
S,+,The sum of the two chain maps f and g,0,2,0,0,0,0,0,0,0,182,,0,0,182,,182,-38,-38,-38,-38,-38
S,eq,Checks to see if two chain maps are equal,0,2,0,0,0,0,0,0,0,182,,0,0,182,,37,-38,-38,-38,-38,-38
S,*,The product of the scalar s and the chain map f,0,2,0,0,0,0,0,0,0,182,,0,0,148,,182,-38,-38,-38,-38,-38
S,*,The composition of the two chain maps f and g,0,2,0,0,0,0,0,0,0,182,,0,0,182,,182,-38,-38,-38,-38,-38
S,IsZero,True if and only if the chain map f is zero in every degree,0,1,0,0,0,0,0,0,0,182,,36,-38,-38,-38,-38,-38
S,IsInjective,True if and only if the chain map f is an injection in every degree,0,1,0,0,0,0,0,0,0,182,,36,-38,-38,-38,-38,-38
S,IsSurjective,True if and only if the chain map f is a surjection in every degree,0,1,0,0,0,0,0,0,0,182,,36,-38,-38,-38,-38,-38
S,IsIsomorphism,True if and only if the chain map f is an isomorphism in every degree,0,1,0,0,0,0,0,0,0,182,,36,-38,-38,-38,-38,-38
S,IsShortExactSequence,"True if the sequence of chain complexes, 0 -> Domain(f) -> Domain(g) -> Codomain(g) -> 0, where the internal maps are f and g, is exact",0,2,0,0,0,0,0,0,0,182,,0,0,182,,36,-38,-38,-38,-38,-38
S,InducedMapOnHomology,The homomorphism induced on homology by the chain map f in degree n,0,2,0,0,0,0,0,0,0,148,,0,0,182,,160,-38,-38,-38,-38,-38
S,ConnectingHomomorphism,The connecting homomorphism in degree n of the short exact sequence of chain complexes given by the chain maps f and g,0,3,0,0,0,0,0,0,0,148,,0,0,182,,0,0,182,,155,-38,-38,-38,-38,-38
S,LongExactSequenceOnHomology,The long exact sequence on homology for the exact sequence of complexes given by the chain maps f and g as a chain complex with the homolgy group in degree i for the Cokernel of C appearing in degree 3i,0,2,0,0,0,0,0,0,0,182,,0,0,182,,183,-38,-38,-38,-38,-38
