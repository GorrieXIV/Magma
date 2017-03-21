174,1
T,PhiModElt,-,1,ModMatFldElt
A,PhiModElt,2,Parent,Vector
T,PhiMod,PhiModElt,1,ModMatFld
A,PhiMod,4,Space,Phi,r,Frobenius
S,Dimension,Return the dimension of the phi-module D,0,1,0,0,0,0,0,0,0,PhiMod,,148,-38,-38,-38,-38,-38
S,BaseRing,Return the coefficient ring of the phi-module D,0,1,0,0,0,0,0,0,0,PhiMod,,-44,-38,-38,-38,-38,-38
S,FrobeniusMatrix,Return the matrix of the Frobenius action on D,0,1,0,0,0,0,0,0,0,PhiMod,,155,-38,-38,-38,-38,-38
S,Print,Print an element of a phi-module,0,1,0,0,1,0,0,0,0,PhiModElt,,-38,-38,-38,-38,-38,-38
S,Print,Print a phi-module,0,1,0,0,1,0,0,0,0,PhiMod,,-38,-38,-38,-38,-38,-38
S,IsEtale,Say whether a phi-module is etale,0,1,0,0,0,0,0,0,0,PhiMod,,36,-38,-38,-38,-38,-38
S,PhiModule,"Create a phi-module out of its matrix G. The optional argument F describes the action of the Frobenius on the coefficients by a couple [s,b], the action on the residue field is given by a -> a^(p^s) and the action on the variable u is given by u-> u^b. The default value is such that the Frobenius is the classical x -> x^p map",0,1,0,0,0,0,0,0,0,177,,PhiMod,-38,-38,-38,-38,-38
S,PhiModuleElement,Create an element of a phi-module D out of a vector x. The vector should have dimension d x 1 (where dim D = d) and the same coefficient ring as D,0,2,0,0,0,0,0,0,0,PhiMod,,0,0,155,,PhiModElt,-38,-38,-38,-38,-38
S,ChangePrecision,Change the precision of a phi-module D to the precision pr,0,2,0,0,1,0,0,0,0,148,,1,1,PhiMod,,-38,-38,-38,-38,-38,-38
S,ElementaryPhiModule,"Create an elementary phi-module D(d,s) over the ring S. The optional argument F describes the action of the Frobenius on the coefficients",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,288,,PhiMod,-38,-38,-38,-38,-38
S,DirectSum,Return the phi-module obtained by direct sum of the phi-modules Phi1 and Phi2,0,2,0,0,0,0,0,0,0,PhiMod,,0,0,PhiMod,,PhiMod,-38,-38,-38,-38,-38
S,BaseChange,Change the basis in which the matrix of the Frobenius action on the phi-module D is written. The base change matrix is P,0,2,0,0,1,0,0,0,0,177,,1,1,PhiMod,,-38,-38,-38,-38,-38,-38
S,RandomBaseChange,Randomly change the basis in which the matrix of the Frobenius action on the phi-module D is written,0,1,0,0,1,0,0,1,1,PhiMod,,-38,-38,-38,-38,-38,-38
S,Phi,Apply the map phi on the phi-module D to an element x of D,0,2,0,0,0,0,0,0,0,PhiModElt,,0,0,PhiMod,,PhiModElt,-38,-38,-38,-38,-38
S,SemisimpleDecomposition,Return a Jordan-Holder decomposition of a phi-module D. The result is given as: - the matrix of the Frobenius in a basis corresponding to a Jordan-Holder sequence - the matrix of the new basis - the list of slopes of the phi-module - the list of dimensions of the Jordan-Holder blocks - the list of polynomials describing (together with the slopes) the composition factors,0,1,0,0,0,0,0,0,0,PhiMod,,177,177,82,82,-38,-38
S,Slopes,Return the slopes of a phi-module,0,1,0,0,0,0,0,0,0,PhiMod,,82,-38,-38,-38,-38,-38
