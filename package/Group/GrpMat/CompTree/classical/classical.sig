174,1
V,ClassicalRecognition,10
A,GrpMat,1,ClassicalRecognitionData
A,GrpPerm,1,ClassicalRecognitionData
A,GrpMat,1,SU32Data
A,GrpPerm,1,SU32Data
S,ClassicalChangeOfBasis,G is a classical group in its natural representation; return change-of-basis matrix to conjugate ClassicalStandardGenerators () to those returned by ClassicalConstructiveRecognition (G),1,0,1,178,0,84,1,0,0,0,0,0,0,0,178,,180,-38,-38,-38,-38,-38
S,ClassicalConstructiveRecognition,"Determine if G is a quasisimple classical group in natural representation. If so, construct standard generators S for G; return true, S and SLPs for S in defining generators of G. Otherwise return false",1,0,1,178,0,84,1,0,0,0,0,0,0,0,178,,36,82,82,-38,-38,-38
S,ClassicalElementToWord,"G is a constructively recognised classical group. If g in an element of G, then express g as an SLP in the standard generators of G and return true and the SLP; otherwise return false",0,2,0,0,0,0,0,0,0,-28,,0,0,-27,,36,137,-38,-38,-38,-38
S,ClassicalConstructiveRecognition,"G is isomorphic to a central quotient of classical group of specified <type> in dimension d, with defining field GF (q); the string <type> is one of SL, Sp, SU, Omega, Omega+, Omega-. Construct standard generators for G; if successful, then return true, maps between G and its standard copy, rewriting maps, standard generators of G and their SLPs in the defining generators of G; otherwise return false. If Verify is true, then check that the supplied parameters for an input matrix representation are correct",0,4,0,0,0,1,0,0,0,148,,0,0,148,,0,0,298,,0,0,-27,,36,175,175,175,175,82
