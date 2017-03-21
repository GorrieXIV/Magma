174,1
S,BaseRing,"The field over which Basis(M) is defined. This is either the rational numbers, a prime finite field, or a p-adic field Q_p",0,1,0,0,0,0,0,0,0,ModFrm,,-44,-38,-38,-38,-38,-38
S,Dimension,"The dimension of the space M of modular forms. (If M is defined over a ring R, then M is free and this is the rank of M.)",0,1,0,0,0,0,0,0,0,ModFrm,,148,-38,-38,-38,-38,-38
S,Level,The level of M,0,1,0,0,0,0,0,0,0,ModFrm,,148,-38,-38,-38,-38,-38
S,Level,The level of f,0,1,0,0,0,0,0,0,0,ModFrmElt,,148,-38,-38,-38,-38,-38
S,IsRingOfAllModularForms,True if and only if M is the ring of all modular forms over a given ring,0,1,0,0,0,0,0,0,0,ModFrm,,36,-38,-38,-38,-38,-38
S,Weight,The weight of M,0,1,0,0,0,0,0,0,0,ModFrm,,148,-38,-38,-38,-38,-38
S,Weight,"The weight of f, if it is defined",0,1,0,0,0,0,0,0,0,ModFrmElt,,148,-38,-38,-38,-38,-38
S,IsGamma1,True if and only if M is explicitly a space of modular forms for Gamma_1(N),0,1,0,0,0,0,0,0,0,ModFrm,,36,-38,-38,-38,-38,-38
S,IsGamma0,True if and only if M is a space of modular forms for Gamma_0(N),0,1,0,0,0,0,0,0,0,ModFrm,,36,-38,-38,-38,-38,-38
S,IsAmbientSpace,True if and only if M is an ambient space,0,1,0,0,0,0,0,0,0,ModFrm,,36,-38,-38,-38,-38,-38
S,IsCuspidal,True if M is contained in the cuspidal subspace of the ambient space of M,0,1,0,0,0,0,0,0,0,ModFrm,,36,-38,-38,-38,-38,-38
S,IsEisenstein,True if M is contained in the Eisenstein subspace of the ambient space of M,0,1,0,0,0,0,0,0,0,ModFrm,,36,-38,-38,-38,-38,-38
S,Degree,The number of Galois conjugates of f over the prime subfield,0,1,0,0,0,0,0,0,0,ModFrmElt,,148,-38,-38,-38,-38,-38
S,DirichletCharacters,The sequence containing Galois representatives of the Dirichlet characters associated with M,0,1,0,0,0,0,0,0,0,ModFrm,,82,-38,-38,-38,-38,-38
S,Parent,,0,1,0,0,0,0,0,0,0,ModFrmElt,,ModFrm,-38,-38,-38,-38,-38
S,eq,"True if M and N are mathematically the same space of modular forms, and their base rings are equal",0,2,0,0,0,0,0,0,0,ModFrm,,0,0,ModFrm,,36,-38,-38,-38,-38,-38
S,eq,True iff f and g are mathematically the same modular form (and their parent spaces are equal),0,2,0,0,0,0,0,0,0,ModFrmElt,,0,0,ModFrmElt,,36,-38,-38,-38,-38,-38
S,subset,"True iff M1 is a subspace of M2, where these are spaces of modular forms with equal ambient spaces",0,2,0,0,0,0,0,0,0,ModFrm,,0,0,ModFrm,,36,-38,-38,-38,-38,-38
S,in,,0,2,0,0,0,0,0,0,0,ModFrm,,0,0,ModFrmElt,,36,-38,-38,-38,-38,-38
S,IsNewform,True if f was created using Newform,0,1,0,0,0,0,0,0,0,ModFrmElt,,36,-38,-38,-38,-38,-38
S,IsEisensteinSeries,True if f was created using EisensteinSeries,0,1,0,0,0,0,0,0,0,ModFrmElt,,36,-38,-38,-38,-38,-38
S,EisensteinData,"The data <chi, psi, t, chi', psi'> that defines the Eisenstein series f",0,1,0,0,0,0,0,0,0,ModFrmElt,,303,-38,-38,-38,-38,-38
S,IsCuspidalNewform,True if f is cuspidal and was created using the Newform intrinsic,0,1,0,0,0,0,0,0,0,ModFrmElt,,36,-38,-38,-38,-38,-38
S,IsNew,True if M is contained in the new subspace of the ambient space of M,0,1,0,0,0,0,0,0,0,ModFrm,,36,-38,-38,-38,-38,-38
S,AmbientSpace,The ambient space that contains M,0,1,0,0,0,0,0,0,0,ModFrm,,ModFrm,-38,-38,-38,-38,-38
S,VectorSpace,Same as RSpace(M),0,1,0,0,0,0,0,0,0,ModFrm,,191,175,175,-38,-38,-38
S,RSpace,"The abstract free module isomorphic to the given space of modular forms M, over the same base ring, and a map to M (with inverse)",0,1,0,0,0,0,0,0,0,ModFrm,,191,175,175,-38,-38,-38
S,Precision,The default printing precision for elements of M,0,1,0,0,0,0,0,0,0,ModFrm,,148,-38,-38,-38,-38,-38
S,SetPrecision,Set the default printing precision for elements of M,0,2,0,0,1,0,0,0,0,148,,0,0,ModFrm,,-38,-38,-38,-38,-38,-38
S,RaisePrecision,Set the default printing precision for elements of M to the given value if this is higher than the current precision,0,2,0,0,1,0,0,0,0,148,,0,0,ModFrm,,-38,-38,-38,-38,-38,-38
S,Eltseq,"The sequence [a1, ..., an] such that f = a1*g_1 + ... + an*g_n, where g_1, ..., g_n is the basis of the parent of f",0,1,0,0,0,0,0,0,0,ModFrmElt,,82,-38,-38,-38,-38,-38
