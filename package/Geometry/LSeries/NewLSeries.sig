174,1
T,LSerMot,-,0
A,LSerMot,1,oldL
A,LSerMot,1,cffunc
A,LSerMot,1,sign
A,LSerMot,3,cond,hodge,wt
A,LSerMot,2,bprec,dprec
A,LSerMot,3,coeffvec,coeffbprec,exact_coeffs
A,LSerMot,4,parent,name,prod,is_zeta
A,LSerMot,6,Vp,GS,E,O,mE,mO
A,LSerMot,5,cE,cO,bp,gbpow,gbcf
S,LPhi_powser,,0,2,0,0,0,0,0,0,0,402,,0,0,LSerMot,,402,-38,-38,-38,-38,-38
A,LSerMot,3,Mn,MnCFc,MnCFv
S,LPhi_contfrac,,0,2,0,0,0,0,0,0,0,402,,0,0,LSerMot,,402,-38,-38,-38,-38,-38
A,LSerMot,3,cancelPhi,tsizePhi,tcrossPhi
A,LSerMot,3,mun,munCFc,munCFv
S,LGfunc_powser,,0,4,0,0,0,0,0,0,0,148,,0,0,148,,0,0,402,,0,0,LSerMot,,402,-38,-38,-38,-38,-38
S,LGfunc_contfrac,,0,4,0,0,0,0,0,0,0,148,,0,0,148,,0,0,402,,0,0,LSerMot,,402,-38,-38,-38,-38,-38
A,LSerMot,3,cancelDs,tsizeDs,tcrossDs
S,LSetPrecision,,0,2,0,0,1,0,0,0,0,148,,0,0,LSerMot,,-38,-38,-38,-38,-38,-38
S,MotivicLSeries,,0,3,0,0,0,0,0,0,0,-1,,0,0,148,,0,0,HodgeStruc,,LSerMot,-38,-38,-38,-38,-38
S,MotivicLSeries,Turn a Lser into an LSerMot,0,1,0,0,0,0,0,0,0,LSer,,LSerMot,-38,-38,-38,-38,-38
S,CheckFunctionalEquation,New version of CheckFunctionalEquation,0,1,0,0,0,0,0,0,0,LSerMot,,402,-38,-38,-38,-38,-38
S,IsOne,True when the degree of L is 0,0,1,0,0,0,0,0,0,0,LSerMot,,36,-38,-38,-38,-38,-38
S,Factorization,"If an L-series is known to be a product of other L-series, return them and their exponents [<L1,n1>,...]. Otherwise returns [<L,1>]",0,1,0,0,0,0,0,0,0,LSerMot,,82,-38,-38,-38,-38,-38
S,*,Product of two motivic L-series,0,2,0,0,0,0,0,0,0,LSerMot,,0,0,LSerMot,,LSerMot,-38,-38,-38,-38,-38
S,^,Take a power of a motivic L-series,0,2,0,0,0,0,0,0,0,148,,0,0,LSerMot,,LSerMot,-38,-38,-38,-38,-38
S,MotivicLProduct,Return the product of a sequence of L-series,1,0,1,82,0,LSerMot,1,0,0,0,0,0,0,0,82,,LSerMot,-38,-38,-38,-38,-38
S,MotivicLProduct,"Return the product of a sequence of L-series, given as <L,n> tuples",1,0,1,82,0,303,1,0,0,0,0,0,0,0,82,,LSerMot,-38,-38,-38,-38,-38
S,/,Quotient of two motivic L-series. It is not checked whether this is valid,0,2,0,0,0,0,0,0,0,LSerMot,,0,0,LSerMot,,LSerMot,-38,-38,-38,-38,-38
S,eq,"true iff L1 and L2 are L-series associated to the same object, except false for modular forms over number fields, and isogenous elliptic curves over Q are also checked",0,2,0,0,0,0,0,0,0,LSerMot,,0,0,LSerMot,,36,-38,-38,-38,-38,-38
S,ne,"true iff L1 and L2 are not associated to the same object, except always true for modular forms over number fields, and isogenous elliptic curves over Q are always checked",0,2,0,0,0,0,0,0,0,LSerMot,,0,0,LSerMot,,36,-38,-38,-38,-38,-38
S,Print,,0,2,0,0,1,0,0,0,0,298,,0,0,LSerMot,,-38,-38,-38,-38,-38,-38
S,IsCoercible,,0,2,0,0,0,0,0,0,0,-1,,0,0,LSerMot,,36,-1,-38,-38,-38,-38
S,in,,0,2,0,0,0,0,0,0,0,-1,,0,0,LSerMot,,36,-38,-38,-38,-38,-38
