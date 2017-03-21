174,1
A,ModFrmHil,1,UseHardHeckeGenerator
A,FldNum,1,SplittingField
S,HeckeOperator,The Hecke operator T_p on the space M of Hilbert modular forms (where p is a prime ideal of the base field of M),0,2,0,0,0,0,0,0,0,-1,,0,0,ModFrmHil,,-34,-38,-38,-38,-38,-38
S,AtkinLehnerOperator,The Atkin-Lehner operator W_q on the space M of Hilbert modular forms (where q is an ideal of the base field of M),0,2,0,0,0,0,0,0,0,-1,,0,0,ModFrmHil,,-34,-38,-38,-38,-38,-38
S,HeckeCharacteristicPolynomial,"Optimized way to obtain CharacteristicPolynomial(HeckeOperator(M, p))",0,2,0,0,0,0,0,0,0,-1,,0,0,ModFrmHil,,312,-38,-38,-38,-38,-38
S,HeckeEigenvalueBound,Bound on |a_P| where a_P is the Hecke eigenvalue at the prime P of a cuspidal newform in M,0,2,0,0,0,0,0,0,0,-1,,0,0,ModFrmHil,,-45,-38,-38,-38,-38,-38
S,SetRationalBasis,"For a space M of Hilbert modular forms over a number field K, this resets the basis of the space to be such that the Hecke operators are matrices with entries in the smallest field possible. (In parallel weight, this is Rationals(). In general, it is a subfield of the splitting field of K.) The basis is then fixed, and all subsequent computations with M will be done relative to this basis",0,1,0,0,1,0,0,0,0,ModFrmHil,,-38,-38,-38,-38,-38,-38
S,NewformDecomposition,"Given a new space M of Hilbert modular forms, this decomposes M into subspaces that are irreducible as Hecke modules, and returns this list of new spaces",0,1,0,0,0,0,0,0,0,ModFrmHil,,168,-38,-38,-38,-38,-38
S,Eigenform,An eigenform in the space M of Hilbert modular forms (which must be an irreducible module under the Hecke action),0,1,0,0,0,0,0,0,0,ModFrmHil,,ModFrmHilElt,-38,-38,-38,-38,-38
S,Eigenforms,"A list of eigenforms in the space M of Hilbert modular forms, corresponding to the NewformDecomposition of M",0,1,0,0,0,0,0,0,0,ModFrmHil,,168,-38,-38,-38,-38,-38
S,IsEigenform,True iff the Hilbert modular form f was constructed as an eigenform,0,1,0,0,0,0,0,0,0,ModFrmHilElt,,36,-38,-38,-38,-38,-38
S,HeckeEigenvalueField,Same as BaseField(Eigenform(M)),0,1,0,0,0,0,0,0,0,ModFrmHil,,-24,-38,-38,-38,-38,-38
S,HeckeEigenvalue,"Given an eigenform f in a new space of Hilbert modular forms, this returns the eigenvalue for the Hecke operator at the prime P",0,2,0,0,0,0,0,0,0,-1,,0,0,ModFrmHilElt,,-45,-38,-38,-38,-38,-38
A,ModFrmHil,2,RawSpace,include_eis
A,FldNum,1,NumbersOfNewformsOfDegree1
A,ModFrmHil,1,NewformsOfDegree1
S,NewformsOfDegree1,Returns the newforms in M that have rational Fourier coefficients,0,1,0,0,0,0,0,0,0,ModFrmHil,,168,-38,-38,-38,-38,-38
S,DecompositionOldAndNew,"Decomposition of the Hecke module M as a direct sum of the 'oldspace' relative to M0 (the largest Hecke submodule of M whose irreducible submodules appear in M0), and the complementary submodule. These are returned as subspaces of the underlying vector space of M. Both M and M0 are assumed to be semisimple, and to satisfy the same properties regarding dimensions of old and new spaces that hold for modular forms. At least one of the optional arguments ('old_dimension' or 'primes' or 'bound') must be provided. The routine will terminate as soon as any of the following hold: (i) the dimension of the oldspace is <= the specified 'old_dimension', (ii) the Hecke action for all specified 'primes' has been used (or if 'primes' are not specified, all good primes with norm up to the specified 'bound')",0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,159,159,-38,-38,-38,-38
S,NewAndOldSubspacesUsingHeckeAction,"Given a Hecke module M of level N and a prime p, this returns the p-new subspace of M, and the p-old subspace, as subspaces of the underlying vector space of M. By definition, the p-old subspace is the space spanned by all images in M of the space Mp of level N/p. It is obtained by computing the dimensions of all oldspaces, and computing the Hecke action on M and Mp for sufficiently many primes. M is assumed to be semisimple, and to satisfy the same properties regarding dimensions of old and new spaces that hold for modular forms",0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,-1,-38,-38,-38,-38,-38