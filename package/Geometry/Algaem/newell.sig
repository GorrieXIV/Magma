174,1
S,IsIntegralModel,returns true if an elliptic curve over a number field has integral coefficients,1,0,1,334,0,-9,1,0,0,0,0,0,0,0,334,,36,-38,-38,-38,-38,-38
S,IsIntegralModel,returns true if the defining coefficients of E have non-negative valuation at the prime ideal p,1,0,1,334,0,-9,2,0,0,0,0,0,0,0,217,,0,0,334,,36,-38,-38,-38,-38,-38
S,IntegralModel,"A model with integral coefficients of the elliptic curve E, defined over a number field",1,0,1,334,0,-9,1,0,0,0,0,0,0,0,334,,334,376,376,-38,-38,-38
S,HyperellipticPolynomials,"Return x^3+a2*x^2+a4*x+a6, a1*x+a3",0,1,0,0,0,0,0,0,0,334,,312,312,-38,-38,-38,-38
A,MapSch,1,Isogeny_Dual
S,DualIsogeny,The dual isogeny of the given isogeny phi between two elliptic curves. This satisfies phi*dual = [m] where m is the degree of phi,0,1,0,0,0,0,0,0,0,376,,376,-38,-38,-38,-38,-38
S,TwoIsogeny,computes the 2-isogeny with the 2-torsion point P in the kernel,0,1,0,0,0,0,0,0,0,372,,175,-38,-38,-38,-38,-38
S,Reduction,"Returns the reduction of an elliptic curve at a prime ideal, provided the given model has good reduction at the prime. The map gives the reduction map on the Mordell-Weil group of the curve",0,2,0,0,0,0,0,0,0,217,,0,0,334,,334,175,-38,-38,-38,-38
S,Reduction,"Computes the map between Abelian groups induced by the reduction of an elliptic curve. The codomain of the returned map is isomorphic to the group of rational points on the curve in reduction. Presently, the elliptic curve must have good reduction at P. The second return value is an isomorphism from an abstract abelian group to the group of rational points on the reduction of the curve",0,2,0,0,0,0,0,0,0,217,,0,0,175,,175,175,175,-38,-38,-38
S,TorsionBound,"Returns a bound on the size of the torsion subgroup of E by considering at least n primes (with early exit in some cases, such as when the torsion is shown to be only two-torsion)",1,0,1,334,0,27,2,0,0,0,0,0,0,0,148,,0,0,334,,148,-38,-38,-38,-38,-38
S,pPowerTorsion,returns the pPower torsion on E. The optional parameter gives an upper bound on the size of the p-power torsion subgroup that is used in the computations,0,2,0,0,0,0,0,0,0,148,,0,0,334,,107,175,-38,-38,-38,-38
A,CrvEll,1,TorsionSubgroup
S,TorsionSubgroup,The torsion subgroup of E over its base field,1,0,1,334,0,27,1,0,0,0,0,0,0,0,334,,107,175,-38,-38,-38,-38
S,IsPSaturated,Tests if given MWmap is p-saturated,0,2,0,0,0,0,0,0,0,148,,0,0,175,,36,-38,-38,-38,-38,-38
