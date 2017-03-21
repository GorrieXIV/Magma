174,1
T,ModAbVarLSer,-,0
A,ModAbVarLSer,3,abelian_variety,critical_strip,name
S,LSeries,The L-series associated to A,0,1,0,0,0,0,0,0,0,ModAbVar,,ModAbVarLSer,-38,-38,-38,-38,-38
S,ModularAbelianVariety,Given an L-function L of a modular abelian variety return the abelian variety to which L was attached,0,1,0,0,0,0,0,0,0,ModAbVarLSer,,ModAbVar,-38,-38,-38,-38,-38
S,CriticalStrip,Given an L-function L of a modular abelian variety return integers x and y such that the critical strip for L is the set of complex numbers with real part strictly between x and y,0,1,0,0,0,0,0,0,0,ModAbVarLSer,,148,148,-38,-38,-38,-38
S,Print,,0,2,0,0,1,0,0,0,0,298,,0,0,ModAbVarLSer,,-38,-38,-38,-38,-38,-38
S,FrobeniusPolynomial,"Given an abelian variety A over a number field, return the characteristic polynomial of Frob_p acting on any ell-adic Tate module of A, where p and ell do not divide the level of A",0,2,0,0,0,0,0,0,0,148,,0,0,ModAbVar,,312,-38,-38,-38,-38,-38
S,FrobeniusPolynomial,"The characteristic polynomial of Frobenius at the nonzero prime ideal P on the modular abelian variety A, where P is assumed to be a prime of good reduction for A, and A is defined over a field that contains the prime P",0,2,0,0,0,0,0,0,0,217,,0,0,ModAbVar,,312,-38,-38,-38,-38,-38
S,FrobeniusPolynomial,The characteristic polynomial of Frobenius on A,0,1,0,0,0,0,0,0,0,ModAbVar,,312,-38,-38,-38,-38,-38
S,LRatio,"The ratio L(A,j)*(j-1)!/((2pi)^{j-1}*Omega_j), where j is a ""critical integer"", so 1<=j<=k-1, and Omega_j is the volume of the group of real points on A when j is odd, and the volume of the -1 eigenspace for conjugation when j is even",0,2,0,0,0,0,0,0,0,148,,0,0,ModAbVar,,267,-38,-38,-38,-38,-38
S,LRatio,"The ratio L(A,j)*(j-1)!/((2pi)^{j-1}*Omega_j), where j is a ""critical integer"", so 1<=j<=k-1, and Omega_j is the volume of the group of real points on A when j is odd, and the volume of the -1 eigenspace for conjugation when j is even",0,2,0,0,0,0,0,0,0,148,,0,0,ModAbVarLSer,,267,-38,-38,-38,-38,-38
S,IsZeroAt,Determines (rigorously) whether the L-function L is zero at s,0,2,0,0,0,0,0,0,0,148,,0,0,ModAbVarLSer,,36,-38,-38,-38,-38,-38
S,Evaluate,"The value of L at s, where s must be an integer that lies in the critical strip for L",0,2,0,0,0,0,0,0,0,148,,0,0,ModAbVarLSer,,402,-38,-38,-38,-38,-38
S,Evaluate,"The value of L at s, where s must be an integer that lies in the critical strip for L, computed using prec terms of power series",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,ModAbVarLSer,,402,-38,-38,-38,-38,-38
S,@,"The value of L at s, where s is an integer that lies in the critical strip",0,2,0,0,0,0,0,0,0,ModAbVarLSer,,0,0,148,,-45,-38,-38,-38,-38,-38
S,LeadingCoefficient,The leading coefficient of the Taylor expansion about the critical integer s and the order of vanishing of L at s,0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,ModAbVarLSer,,402,148,-38,-38,-38,-38
