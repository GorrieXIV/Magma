174,1
V,ArtRep,3
A,FldNum,1,artinrepdata
T,ArtRep,-,0
A,ArtRep,3,K,character,conductor
S,IsCoercible,Coerce an Artin representation,0,2,0,0,0,0,0,0,0,-1,,0,0,ArtRep,,36,-1,-38,-38,-38,-38
S,in,"""in"" function for an Artin representation",0,2,0,0,0,0,0,0,0,-1,,0,0,ArtRep,,36,-38,-38,-38,-38,-38
S,&+,Sum a sequence of Artin representations (needed as zero does not exist),1,0,1,82,0,ArtRep,1,0,0,0,0,0,0,0,82,,ArtRep,-38,-38,-38,-38,-38
S,&*,Times a sequence of Artin representations (needed as one does not exist),1,0,1,82,0,ArtRep,1,0,0,0,0,0,0,0,82,,ArtRep,-38,-38,-38,-38,-38
S,ArtRepCreate,Create an Artin representation (internal function),0,0,0,0,0,0,0,ArtRep,-38,-38,-38,-38,-38
S,Print,Print an Artin representation,0,2,0,0,1,0,0,0,0,298,,0,0,ArtRep,,-38,-38,-38,-38,-38,-38
S,Conductor,Conductor of an Artin representation,0,1,0,0,0,0,0,0,0,ArtRep,,148,-38,-38,-38,-38,-38
S,DefiningPolynomial,The polynomial whose roots Group(A) permutes,0,1,0,0,0,0,0,0,0,ArtRep,,312,-38,-38,-38,-38,-38
S,FrobeniusElement,"Compute a Frobenius element at p in the Galois group of the Galois closure of K. This is a permutation on the roots of a polynomial defining K, which can be recovered as DefiningPolynomial(A) for any Artin representation of K; the Frobenius element is well-defined up to conjugacy and modulo inertia",0,2,0,0,0,0,0,0,0,148,,0,0,27,,222,-38,-38,-38,-38,-38
S,FrobeniusElement,"Compute a Frobenius element at p in the Galois group of the Galois closure of K. This is a permutation on the roots of a polynomial defining K, which can be recovered as DefiningPolynomial(A) for any Artin representation of K; the Frobenius element is well-defined up to conjugacy and modulo inertia",0,2,0,0,0,0,0,0,0,147,,0,0,27,,222,-38,-38,-38,-38,-38
S,Group,Returns the Galois group of the field K=Field(A) through which A factors,0,1,0,0,0,0,0,0,0,ArtRep,,224,-38,-38,-38,-38,-38
S,Character,Character of an Artin representation,0,1,0,0,0,0,0,0,0,ArtRep,,39,-38,-38,-38,-38,-38
S,Degree,Degree (=dimension) of an Artin representation,0,1,0,0,0,0,0,0,0,ArtRep,,148,-38,-38,-38,-38,-38
S,Dimension,Degree (=dimension) of an Artin representation,0,1,0,0,0,0,0,0,0,ArtRep,,148,-38,-38,-38,-38,-38
S,IsIrreducible,True if the Artin representation A is irreducible,0,1,0,0,0,0,0,0,0,ArtRep,,36,-38,-38,-38,-38,-38
S,Decomposition,"Decompose A into irreducible consituents. Returns a sequence [...<A_i,n_i>...] with A_i irreducible and n_i their exponents in A (possibly negative)",0,1,0,0,0,0,0,0,0,ArtRep,,82,-38,-38,-38,-38,-38
S,IsRamified,True if the Artin representation A is ramified at p,0,2,0,0,0,0,0,0,0,148,,0,0,ArtRep,,36,-38,-38,-38,-38,-38
S,IsWildlyRamified,True if the Artin representation A is wildly ramified at p,0,2,0,0,0,0,0,0,0,148,,0,0,ArtRep,,36,-38,-38,-38,-38,-38
S,Field,Number field K such that A factors through the Galois closure of K,0,1,0,0,0,0,0,0,0,ArtRep,,27,-38,-38,-38,-38,-38
S,IsZero,Whether an Artin representation is zero,0,1,0,0,0,0,0,0,0,ArtRep,,36,-38,-38,-38,-38,-38
S,!!,"Given an Artin representation A of some number field, recognize it if possible as an Artin representation of F and return F!!A,true. If not possible, return 0,false",0,2,0,0,0,0,0,0,0,ArtRep,,0,0,27,,ArtRep,36,-38,-38,-38,-38
S,ChangeField,"Given an Artin representation A of some number field, recognize it if possible as an Artin representation of F and return F!!A,true. If not possible, return 0,false",0,2,0,0,0,0,0,0,0,27,,0,0,ArtRep,,ArtRep,36,-38,-38,-38,-38
S,Minimize,"A restricted to the smallest number field K such that A factors through the its Galois closure. If Optimize=true (default), attempt to minimize the defining polynomial of K using OptimizedRepresentation",0,1,0,0,0,0,0,0,0,ArtRep,,ArtRep,-38,-38,-38,-38,-38
S,Kernel,The smallest Galois extension K/Q such that A factors through Gal(K/Q). Note that this field may be enormous and uncomputable,0,1,0,0,0,0,0,0,0,ArtRep,,27,-38,-38,-38,-38,-38
S,+,Direct sum of two Artin representations,0,2,0,0,0,0,0,0,0,ArtRep,,0,0,ArtRep,,ArtRep,-38,-38,-38,-38,-38
S,-,Direct difference of two Artin representations,0,2,0,0,0,0,0,0,0,ArtRep,,0,0,ArtRep,,ArtRep,-38,-38,-38,-38,-38
S,-,Negation of an Artin representation,0,1,0,0,0,0,0,0,0,ArtRep,,ArtRep,-38,-38,-38,-38,-38
S,*,Tensor product of two Artin representations,0,2,0,0,0,0,0,0,0,ArtRep,,0,0,ArtRep,,ArtRep,-38,-38,-38,-38,-38
S,eq,Test whether the two Artin representations are equal,0,2,0,0,0,0,0,0,0,ArtRep,,0,0,ArtRep,,36,-38,-38,-38,-38,-38
S,!!,The Artin representation of K with character ch,0,2,0,0,0,0,0,0,0,39,,0,0,27,,ArtRep,-38,-38,-38,-38,-38
S,!!,The Artin representation of K with character ch,0,2,0,0,0,0,0,0,0,82,,0,0,27,,ArtRep,-38,-38,-38,-38,-38
S,ArtinRepresentations,"Artin representations that factor through Q, i.e. just the principal character of Gal(Qbar/Q)",0,1,0,0,0,0,0,0,0,262,,82,-38,-38,-38,-38,-38
S,ArtinRepresentations,All irreducible Artin representations that factor through the normal closure of K,0,1,0,0,0,0,0,0,0,27,,82,-38,-38,-38,-38,-38
S,LSeries,L-series of an Artin representation,0,1,0,0,0,0,0,0,0,ArtRep,,LSer,-38,-38,-38,-38,-38
S,HodgeStructure,The Hodge structure of an Artin representation,0,1,0,0,0,0,0,0,0,ArtRep,,HodgeStruc,-38,-38,-38,-38,-38
S,PermutationCharacter,"For a number field K with Galois closure F, compute the character of C[Gal(Qbar/Q)/Gal(Qbar/K)] as an Artin representation. It is of degree [K:Q] and is the character of the permutation representation of the absolute Galois group on the embeddings of K in C",0,1,0,0,0,0,0,0,0,27,,ArtRep,-38,-38,-38,-38,-38
S,PermutationCharacter,The principal character of Gal(Qbar/Q) as an Artin representation,0,1,0,0,0,0,0,0,0,262,,ArtRep,-38,-38,-38,-38,-38
S,EulerFactor,The Euler factor of a Dirichlet character at a prime,0,2,0,0,0,0,0,0,0,148,,0,0,GrpDrchElt,,312,-38,-38,-38,-38,-38
S,ArtinRepresentation,"Convert a Dirichlet character chi to an Artin representation A. To avoid recomputation, the minimal field through which A factors may be specified by the field parameter",0,1,0,0,0,0,0,0,0,GrpDrchElt,,ArtRep,-38,-38,-38,-38,-38
S,ArtinRepresentation,"Convert a Dirichlet character chi to an Artin representation A. To avoid recomputation, the minimal field through which A factors may be specified by the field parameter",0,1,0,0,0,0,0,0,0,GrpDrchNFElt,,ArtRep,-38,-38,-38,-38,-38
S,EulerFactor,Euler factor of A at p. The coefficient field (cyclotomic field or some complex field) may be specified with the optional parameter R,0,2,0,0,0,0,0,0,0,148,,0,0,ArtRep,,312,-38,-38,-38,-38,-38
S,Determinant,"Given an Artin representation, return its determinant as an Artin rep",0,1,0,0,0,0,0,0,0,ArtRep,,ArtRep,-38,-38,-38,-38,-38
S,^,Tensor power of an Artin representation,0,2,0,0,0,0,0,0,0,148,,0,0,ArtRep,,ArtRep,-38,-38,-38,-38,-38
S,*,Direct sum of an Artin representation n times,0,2,0,0,0,0,0,0,0,ArtRep,,0,0,148,,ArtRep,-38,-38,-38,-38,-38
S,*,Direct sum of an Artin representation n times,0,2,0,0,0,0,0,0,0,148,,0,0,ArtRep,,ArtRep,-38,-38,-38,-38,-38
S,DirichletCharacter,Convert a linear Artin representation to a Dirichlet character (over Q),0,1,0,0,0,0,0,0,0,ArtRep,,GrpDrchElt,-38,-38,-38,-38,-38
S,HeckeCharacter,Convert a linear Artin representation to a Dirichlet character (over Q),0,1,0,0,0,0,0,0,0,ArtRep,,GrpHeckeElt,-38,-38,-38,-38,-38
S,Symmetrization,"Given an Artin representation A and a partition S, return the symmetrization of A corresponding to S",0,2,0,0,0,0,0,0,0,82,,0,0,ArtRep,,ArtRep,-38,-38,-38,-38,-38
S,Symmetrization,"Given a character chi and a partition P, return the symmetrization",0,2,0,0,0,0,0,0,0,82,,0,0,39,,39,-38,-38,-38,-38,-38
S,IsOrthogonalCharacter,"Given a character of a finite group, determine whether it is orthogonal",0,1,0,0,0,0,0,0,0,39,,36,-38,-38,-38,-38,-38
S,OrthogonalSymmetrization,"Given a (hereditarily) orthogonal character chi and a partition P, return the orthogonal symmetrization",0,2,0,0,0,0,0,0,0,82,,0,0,39,,39,-38,-38,-38,-38,-38
S,IsSymplecticCharacter,"Given a character of a finite group, determine whether it is symplectic",0,1,0,0,0,0,0,0,0,39,,36,-38,-38,-38,-38,-38
S,SymplecticSymmetrization,"Given a (hereditarily) symplectic character chi and a partition P, return the symplectic symmetrization",0,2,0,0,0,0,0,0,0,82,,0,0,39,,39,-38,-38,-38,-38,-38
