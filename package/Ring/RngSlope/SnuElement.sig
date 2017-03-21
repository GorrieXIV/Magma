174,1
S,Normalize,"Given a power series ring element (over an inexact ring), remove the lower coefficients that are weakly zero",0,1,0,0,0,0,0,0,0,286,,286,-38,-38,-38,-38,-38
S,Normalize,"Given a Laurent series ring element (over an inexact ring), remove the lower coefficients that are weakly zero",0,1,0,0,0,0,0,0,0,285,,286,-38,-38,-38,-38,-38
T,SnuRng,SnuElement,0
A,SnuRng,3,R,nu,var_name
A,SnuElement,2,f,S
S,SnuRing,"Given a p-adic field/ring and a (rational) slope, return the S^nu slope ring",0,2,0,0,0,0,0,0,0,267,,0,0,400,,SnuRng,-38,-38,-38,-38,-38
S,SnuRing,"Given a p-adic field/ring and a (rational) slope, return the S^nu slope ring",0,2,0,0,0,0,0,0,0,267,,0,0,395,,SnuRng,-38,-38,-38,-38,-38
S,SnuRing,"Given a p-adic field/ring and a (rational) slope, return the S^nu slope ring",0,2,0,0,0,0,0,0,0,148,,0,0,395,,SnuRng,-38,-38,-38,-38,-38
S,SnuRing,"Given a p-adic field/ring and a (rational) slope, return the S^nu slope ring",0,2,0,0,0,0,0,0,0,148,,0,0,400,,SnuRng,-38,-38,-38,-38,-38
S,SnuRing,"Given a p-adic field/ring, return the S^nu slope ring where nu is a vararg",0,1,0,0,0,0,0,0,0,395,,SnuRng,-38,-38,-38,-38,-38
S,SnuRing,"Given a p-adic field/ring, return the S^nu slope ring where nu is a vararg",0,1,0,0,0,0,0,0,0,400,,SnuRng,-38,-38,-38,-38,-38
S,SnuRing,"Given a prime p, construct the S^nu slope ring over Q_p (nu is a vararg)",0,1,0,0,0,0,0,0,0,148,,SnuRng,-38,-38,-38,-38,-38
S,SnuRing,"Given a prime p and a precision e, construct the S^nu slope ring over Q_p with p-adic precision e (nu is a vararg)",0,2,0,0,0,0,0,0,0,148,,0,0,148,,SnuRng,-38,-38,-38,-38,-38
S,SnuRing,"Given a p-adic power series ring and a (rational) slope, construct the S^nu slope ring",0,2,0,0,0,0,0,0,0,267,,0,0,289,,SnuRng,-38,-38,-38,-38,-38
S,SnuRing,"Given a p-adic power series ring and a (rational) slope, construct the S^nu slope ring",0,2,0,0,0,0,0,0,0,148,,0,0,289,,SnuRng,-38,-38,-38,-38,-38
S,SnuRing,"Given a p-adic power series ring, return the S^nu slope ring (nu is a vararg)",0,1,0,0,0,0,0,0,0,289,,SnuRng,-38,-38,-38,-38,-38
S,SnuRing,"Given a S^nu_p ring, return the associated S^nu ring",0,1,0,0,0,0,0,0,0,SpRng,,SnuRng,-38,-38,-38,-38,-38
S,SnuRing,"Given a S^nu_u ring, return the associated S^nu ring",0,1,0,0,0,0,0,0,0,SuRng,,SnuRng,-38,-38,-38,-38,-38
S,eq,Whether inputs are equal,0,2,0,0,0,0,0,0,0,SnuRng,,0,0,SnuRng,,36,-38,-38,-38,-38,-38
S,ne,Whether inputs are unequal,0,2,0,0,0,0,0,0,0,SnuRng,,0,0,SnuRng,,36,-38,-38,-38,-38,-38
S,Slope,The slope of a S^nu slope ring,0,1,0,0,0,0,0,0,0,SnuRng,,267,-38,-38,-38,-38,-38
S,Precision,The u-precision of the power series ring associated to a S^nu slope ring,0,1,0,0,0,0,0,0,0,SnuRng,,148,-38,-38,-38,-38,-38
S,CoefficientRing,The p-adic coefficient ring associated to a S^nu slope ring,0,1,0,0,0,0,0,0,0,SnuRng,,148,-38,-38,-38,-38,-38
S,PrintNamed,Print SnuRing,0,3,0,0,1,0,0,0,0,298,,0,0,298,,0,0,SnuRng,,-38,-38,-38,-38,-38,-38
S,.,The i-th generator (i=1),0,2,0,0,0,0,0,0,0,148,,0,0,SnuRng,,SnuElement,-38,-38,-38,-38,-38
S,AssignNames,,1,1,1,82,0,298,2,0,0,1,0,0,0,0,82,,1,1,SnuRng,,-38,-38,-38,-38,-38,-38
S,Name,The i-th name (i is 1),0,2,0,0,0,0,0,0,0,148,,0,0,SnuRng,,SnuElement,-38,-38,-38,-38,-38
S,IsCoercible,,0,2,0,0,0,0,0,0,0,-1,,0,0,SnuRng,,36,SnuElement,-38,-38,-38,-38
S,Parent,The parent ring,0,1,0,0,0,0,0,0,0,SnuElement,,SnuRng,-38,-38,-38,-38,-38
S,+,Sum of inputs,0,2,0,0,0,0,0,0,0,SnuElement,,0,0,SnuElement,,SnuElement,-38,-38,-38,-38,-38
S,+,Generic add (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SnuElement,,SnuElement,-38,-38,-38,-38,-38
S,+,Generic add (tries coercion),0,2,0,0,0,0,0,0,0,SnuElement,,0,0,-1,,SnuElement,-38,-38,-38,-38,-38
S,-,Negation of input,0,1,0,0,0,0,0,0,0,SnuElement,,SnuElement,-38,-38,-38,-38,-38
S,-,Difference of inputs,0,2,0,0,0,0,0,0,0,SnuElement,,0,0,SnuElement,,SnuElement,-38,-38,-38,-38,-38
S,-,Generic sub (tries coercion,0,2,0,0,0,0,0,0,0,-1,,0,0,SnuElement,,SnuElement,-38,-38,-38,-38,-38
S,-,Generic sub (tries coercion,0,2,0,0,0,0,0,0,0,SnuElement,,0,0,-1,,SnuElement,-38,-38,-38,-38,-38
S,*,Product of inputs,0,2,0,0,0,0,0,0,0,SnuElement,,0,0,SnuElement,,SnuElement,-38,-38,-38,-38,-38
S,*,Generic mult (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SnuElement,,SnuElement,-38,-38,-38,-38,-38
S,*,Generic mult (tries coercion),0,2,0,0,0,0,0,0,0,SnuElement,,0,0,-1,,SnuElement,-38,-38,-38,-38,-38
S,/,Quotient of inputs,0,2,0,0,0,0,0,0,0,SnuElement,,0,0,SnuElement,,SnuElement,-38,-38,-38,-38,-38
S,/,Generic div (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SnuElement,,SnuElement,-38,-38,-38,-38,-38
S,/,Generic div (tries coercion),0,2,0,0,0,0,0,0,0,SnuElement,,0,0,-1,,SnuElement,-38,-38,-38,-38,-38
S,^,The n-th power of x,0,2,0,0,0,0,0,0,0,148,,0,0,SnuElement,,SnuElement,-38,-38,-38,-38,-38
S,eq,Equality of inputs,0,2,0,0,0,0,0,0,0,SnuElement,,0,0,SnuElement,,36,-38,-38,-38,-38,-38
S,eq,Generic equals (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SnuElement,,36,-38,-38,-38,-38,-38
S,eq,Generic equals (tries coercion),0,2,0,0,0,0,0,0,0,SnuElement,,0,0,-1,,36,-38,-38,-38,-38,-38
S,ne,Nonequality of inputs,0,2,0,0,0,0,0,0,0,SnuElement,,0,0,SnuElement,,36,-38,-38,-38,-38,-38
S,ne,Generic unequal (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SnuElement,,36,-38,-38,-38,-38,-38
S,ne,Generic unequal (tries coercion),0,2,0,0,0,0,0,0,0,SnuElement,,0,0,-1,,36,-38,-38,-38,-38,-38
S,NumericalPrecision,The effective power series precision of the input ring,0,1,0,0,0,0,0,0,0,SnuRng,,148,-38,-38,-38,-38,-38
S,PrintNamed,Print SnuElement,0,3,0,0,1,0,0,0,0,298,,0,0,298,,0,0,SnuElement,,-38,-38,-38,-38,-38,-38
S,LeadingTerm,The leading term in the power series expansion of a S^nu element,0,1,0,0,0,0,0,0,0,SnuElement,,286,-38,-38,-38,-38,-38
S,WeierstrassTerm,The term corresponding to the Weierstrass degree (it has smallest valuation),0,1,0,0,0,0,0,0,0,SnuElement,,286,-38,-38,-38,-38,-38
S,IsWeaklyZero,True if input is weakly zero,0,1,0,0,0,0,0,0,0,SnuElement,,36,-38,-38,-38,-38,-38
S,Coefficients,"The coefficients of the underlying power series, with valuation shift",0,1,0,0,0,0,0,0,0,SnuElement,,82,148,148,-38,-38,-38
S,O,Returns O(x),0,1,0,0,0,0,0,0,0,SnuElement,,36,-38,-38,-38,-38,-38
S,GaussValuation,Return the Gauss valuation of the element f in its parent S^nu Returns Precision(Parent(f))+1 for 0,0,1,0,0,0,0,0,0,0,SnuElement,,267,-38,-38,-38,-38,-38
S,WeierstrassDegree,Return the Weierstrass degree of the element f in S^nu,0,1,0,0,0,0,0,0,0,SnuElement,,267,-38,-38,-38,-38,-38
S,IsDistinguished,Test if f is distinguished and returns its Weierstrass degree,0,1,0,0,0,0,0,0,0,SnuElement,,36,148,-38,-38,-38,-38
S,Quotrem,"Given A and B with v(A) >= v(B) returns Q,R such that A = B*Q + R with R a polynomial with degree less than the Weierstrass degree of B. We suppose that A and B have infinite u-precision (i.e are polynomials) and ensure that Q and R are known up to padic-precision piprec",0,2,0,0,0,0,0,0,0,SnuElement,,0,0,SnuElement,,SnuElement,SnuElement,-38,-38,-38,-38
S,WeierstrassPreparation,Let f be a distinguished element of S_nu (i.e. whose Gauss valuation is 0) with Weierstrass degree d. Write f = UP where U is invertible in S^nu and P is a polynomial of degree d,0,1,0,0,0,0,0,0,0,SnuElement,,SnuElement,SnuElement,-38,-38,-38,-38
S,ExtendedGcd,"Given A and B with v(A)>=v(B) this returns G,H,w,x,y,z with Aw+Bx=G where v(G)=v(B) and Ay+Bz=H with v(H)>v(A) and wz-xy=1. The fact that H need not be 0 in all cases is due to the non-Euclidean nature of S^nu",0,2,0,0,0,0,0,0,0,SnuElement,,0,0,SnuElement,,SnuElement,SnuElement,SnuElement,SnuElement,SnuElement,SnuElement
