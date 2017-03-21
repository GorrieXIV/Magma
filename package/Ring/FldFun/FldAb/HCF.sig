174,1
V,Drinfeld,2
S,HilbertClassField,"The Hilbert class field of K, ie. the maximal unramified Abelian extension where I is totally split",0,2,0,0,0,0,0,0,0,230,,0,0,4,,FldFunAb,-38,-38,-38,-38,-38
A,RngFunOrd,1,BasisGenerators
S,MyMaximalOrder,Computes the maximal order of F componentwise,0,1,0,0,0,0,0,0,0,4,,8,-38,-38,-38,-38,-38
S,MyBasis,,0,2,0,0,0,0,0,0,0,-44,,0,0,10,,82,-38,-38,-38,-38,-38
S,MyBasis,"In the implemented case, this returns a R-basis for M",0,2,0,0,0,0,0,0,0,-44,,0,0,8,,82,-38,-38,-38,-38,-38
S,Sign,"The sign of x at I, ie. the 1st non-zero coefficient in the expansion",0,2,0,0,0,0,0,0,0,230,,0,0,5,,85,-38,-38,-38,-38,-38
S,ChangeModel,Change the representation of K so that P is the only infinite place,0,2,0,0,0,0,0,0,0,230,,0,0,4,,4,175,-38,-38,-38,-38
S,RationalReconstruction,Tries to apply rational reconstruction modulo f to all coefficients of e,0,2,0,0,0,0,0,0,0,312,,0,0,5,,36,5,-38,-38,-38,-38
S,MinimalPolynomial,The minimal polynomial of x,0,1,0,0,0,0,0,0,0,171,,312,-38,-38,-38,-38,-38
S,AnalyticDrinfeldModule,"For an infinite place P of degree 1 in K, compute the image of a non-constant under a sign-normalised Drinfeld module of rank 1",0,2,0,0,0,0,0,0,0,230,,0,0,4,,5,RngUPolTwstElt,-38,-38,-38,-38
S,AlgebraicToAnalytic,"Given the non-trivial image R_a under a Drinfel module, find approximations for the lattice used to define the module",0,2,0,0,0,0,0,0,0,230,,0,0,RngUPolTwstElt,,RngUPolTwstElt,-38,-38,-38,-38,-38
S,Extend,"Given a non-constant image ImA under a Drinfeld module and an arbitrary integral element b, copute the image of b. P has to be the infinite place used",0,3,0,0,0,0,0,0,0,230,,0,0,-45,,0,0,RngUPolTwstElt,,312,-38,-38,-38,-38,-38
S,InternalGetExpCoeffVal,,0,1,0,0,0,0,0,0,0,230,,82,-38,-38,-38,-38,-38
S,InternalGetExpCoeffValError,Computes estimates for the error in the coefficients of exp when only using elements on L(InfBound*P) for the approximation,0,1,0,0,0,0,0,0,0,230,,82,-38,-38,-38,-38,-38
S,InternalGetExpVal,Computes a lower bound of the valuation of Exp(x) where Exp is the exponetial associated to the MaximalOrderFinite and Expand,0,2,0,0,0,0,0,0,0,230,,0,0,-45,,148,148,-38,-38,-38,-38
S,InternalGetDrinfeldVal,Computes lower bounds for the valuation of the coefficients of the image of x under the Drinfeld module,0,2,0,0,0,0,0,0,0,230,,0,0,-45,,82,-38,-38,-38,-38,-38
S,InternalGetNormalisedDrinfeldVal,Computes lower bounds for the valuation of the coefficients of the image of x under the sign normalised Drinfeld module,0,2,0,0,0,0,0,0,0,230,,0,0,-45,,148,-38,-38,-38,-38,-38
S,AdditivePolynomialFromRoots,"Computes (essentially) the polynomial whose roots are L(InfBound*P + Class), evaluated at x",0,2,0,0,0,0,0,0,0,230,,0,0,-45,,-1,-38,-38,-38,-38,-38
S,Exp,"An approximation to the Exponential of L(n*P), n -> Infty",0,2,0,0,0,0,0,0,0,230,,0,0,-45,,RngUPolTwstElt,-38,-38,-38,-38,-38
S,InternalCosetModABasis,"AM mod M is a F_q vectorspce. This computes a basis for it. If Class is given, M is replaced by the ideal generating it",0,1,0,0,0,0,0,0,0,5,,82,-38,-38,-38,-38,-38
S,AnalyticModule,"Computes the image of x under ""the"" Drinfeld module. Ex, when given, must be a twisted polynomial approximating the Exponential fction for this lattice",0,2,0,0,0,0,0,0,0,230,,0,0,-45,,-1,-38,-38,-38,-38,-38
S,CanNormalize,"Scales the image T under the Drinfeld module to have smaller, positive valuations",0,1,0,0,0,0,0,0,0,RngUPolTwstElt,,36,RngUPolTwstElt,-45,-38,-38,-38
S,CanSignNormalize,"Given a twisted polynomial T (which should be the image under a Drinfeld module), attempt to normalize the leading term to be in the finite field",0,1,0,0,0,0,0,0,0,RngUPolTwstElt,,36,RngUPolTwstElt,-45,-38,-38,-38
S,InternalSolve,,0,4,0,0,0,0,0,0,0,148,,0,0,-48,,0,0,-48,,0,0,82,,-1,-38,-38,-38,-38,-38
