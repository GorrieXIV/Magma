174,1
T,SpRng,SpElement,0
A,SpRng,3,R,nu,var_name
A,SpRng,2,A,B
A,SpElement,2,f,S
S,SpRing,"Given a p-adic ring/field and a (rational) slope, return the S^nu_p ring",0,2,0,0,0,0,0,0,0,267,,0,0,400,,SpRng,-38,-38,-38,-38,-38
S,SpRing,"Given a p-adic ring/field and a (rational) slope, return the S^nu_p ring",0,2,0,0,0,0,0,0,0,267,,0,0,395,,SpRng,-38,-38,-38,-38,-38
S,SpRing,"Given a p-adic ring/field and a (rational) slope, return the S^nu_p ring",0,2,0,0,0,0,0,0,0,148,,0,0,395,,SpRng,-38,-38,-38,-38,-38
S,SpRing,"Given a p-adic ring/field and a (rational) slope, return the S^nu_p ring",0,2,0,0,0,0,0,0,0,148,,0,0,400,,SpRng,-38,-38,-38,-38,-38
S,SpRing,"Given a p-adic ring/field, return the S^nu_p slope ring (nu is a vararg)",0,1,0,0,0,0,0,0,0,395,,SpRng,-38,-38,-38,-38,-38
S,SpRing,"Given a p-adic ring/field, return the S^nu_p slope ring (nu is a vararg)",0,1,0,0,0,0,0,0,0,400,,SpRng,-38,-38,-38,-38,-38
S,SpRing,"Given a prime p, get the S^nu_p slope ring over Q_p (nu is a vararg)",0,1,0,0,0,0,0,0,0,148,,SpRng,-38,-38,-38,-38,-38
S,SpRing,"Given a prime p and a precision e, construct the S^nu_p slope ring over Q_p with p-adic precision e (nu is a vararg)",0,2,0,0,0,0,0,0,0,148,,0,0,148,,SpRng,-38,-38,-38,-38,-38
S,SpRing,"Given a p-adic power series ring and a (rational) slope, construct the associated S^nu_p slope ring",0,2,0,0,0,0,0,0,0,267,,0,0,289,,SpRng,-38,-38,-38,-38,-38
S,SpRing,"Given a p-adic power series ring and a (rational) slope, construct the associated S^nu_p slope ring",0,2,0,0,0,0,0,0,0,148,,0,0,289,,SpRng,-38,-38,-38,-38,-38
S,SpRing,"Given a p-adic power series ring, get the S^nu_p slope ring (nu is a vararg)",0,1,0,0,0,0,0,0,0,289,,SpRng,-38,-38,-38,-38,-38
S,SpRing,"Given a S^nu slope ring, construct the associated S^nu_p localization",0,1,0,0,0,0,0,0,0,SnuRng,,SpRng,-38,-38,-38,-38,-38
S,eq,Whether two Sp rings are equal,0,2,0,0,0,0,0,0,0,SpRng,,0,0,SpRng,,36,-38,-38,-38,-38,-38
S,ne,Whether 2 Sp rings are unequal,0,2,0,0,0,0,0,0,0,SpRng,,0,0,SpRng,,36,-38,-38,-38,-38,-38
S,Precision,The u-precision of the power series ring associated to a S^nu_p slope ring,0,1,0,0,0,0,0,0,0,SpRng,,148,-38,-38,-38,-38,-38
S,Slope,The slope of a S^nu_p slope ring,0,1,0,0,0,0,0,0,0,SpRng,,267,-38,-38,-38,-38,-38
S,CoefficientRing,The p-adic coefficient ring of a S^nu_p slope ring,0,1,0,0,0,0,0,0,0,SpRng,,148,-38,-38,-38,-38,-38
S,PrintNamed,Print SpRng,0,3,0,0,1,0,0,0,0,298,,0,0,298,,0,0,SpRng,,-38,-38,-38,-38,-38,-38
S,.,The i-th generator (i=1),0,2,0,0,0,0,0,0,0,148,,0,0,SpRng,,SpElement,-38,-38,-38,-38,-38
S,AssignNames,,1,1,1,82,0,298,2,0,0,1,0,0,0,0,82,,1,1,SpRng,,-38,-38,-38,-38,-38,-38
S,Name,The i-th name (i is 1),0,2,0,0,0,0,0,0,0,148,,0,0,SpRng,,SpElement,-38,-38,-38,-38,-38
S,IsCoercible,,0,2,0,0,0,0,0,0,0,-1,,0,0,SpRng,,36,SpElement,-38,-38,-38,-38
S,Parent,The parent Sp ring of an element,0,1,0,0,0,0,0,0,0,SpElement,,SpRng,-38,-38,-38,-38,-38
S,+,The sum of the inputs,0,2,0,0,0,0,0,0,0,SpElement,,0,0,SpElement,,SpElement,-38,-38,-38,-38,-38
S,+,Generic add (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SpElement,,SpElement,-38,-38,-38,-38,-38
S,+,Generic add (tries coercion),0,2,0,0,0,0,0,0,0,SpElement,,0,0,-1,,SpElement,-38,-38,-38,-38,-38
S,+,Generic add (tries coercion),0,2,0,0,0,0,0,0,0,SnuElement,,0,0,SpElement,,SpElement,-38,-38,-38,-38,-38
S,+,Generic add (tries coercion),0,2,0,0,0,0,0,0,0,SpElement,,0,0,SnuElement,,SpElement,-38,-38,-38,-38,-38
S,-,Negation of the input,0,1,0,0,0,0,0,0,0,SpElement,,SpElement,-38,-38,-38,-38,-38
S,-,Difference of inputs,0,2,0,0,0,0,0,0,0,SpElement,,0,0,SpElement,,SpElement,-38,-38,-38,-38,-38
S,-,Generic sub (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SpElement,,SpElement,-38,-38,-38,-38,-38
S,-,Generic sub (tries coercion),0,2,0,0,0,0,0,0,0,SpElement,,0,0,-1,,SpElement,-38,-38,-38,-38,-38
S,-,Generic sub (tries coercion),0,2,0,0,0,0,0,0,0,SnuElement,,0,0,SpElement,,SpElement,-38,-38,-38,-38,-38
S,-,Generic sub (tries coercion),0,2,0,0,0,0,0,0,0,SpElement,,0,0,SnuElement,,SpElement,-38,-38,-38,-38,-38
S,*,Product of inputs,0,2,0,0,0,0,0,0,0,SpElement,,0,0,SpElement,,SpElement,-38,-38,-38,-38,-38
S,*,Generic mult (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SpElement,,SpElement,-38,-38,-38,-38,-38
S,*,Generic mult (tries coercion),0,2,0,0,0,0,0,0,0,SpElement,,0,0,-1,,SpElement,-38,-38,-38,-38,-38
S,*,Generic mult (tries coercion),0,2,0,0,0,0,0,0,0,SnuElement,,0,0,SpElement,,SpElement,-38,-38,-38,-38,-38
S,*,Generic mult (tries coercion),0,2,0,0,0,0,0,0,0,SpElement,,0,0,SnuElement,,SpElement,-38,-38,-38,-38,-38
S,/,Quotient of inputs,0,2,0,0,0,0,0,0,0,SpElement,,0,0,SpElement,,SpElement,-38,-38,-38,-38,-38
S,/,Generic div (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SpElement,,SpElement,-38,-38,-38,-38,-38
S,/,Generic div (tries coercion),0,2,0,0,0,0,0,0,0,SpElement,,0,0,-1,,SpElement,-38,-38,-38,-38,-38
S,/,Generic div (tries coercion),0,2,0,0,0,0,0,0,0,SnuElement,,0,0,SpElement,,SpElement,-38,-38,-38,-38,-38
S,/,Generic div (tries coercion),0,2,0,0,0,0,0,0,0,SpElement,,0,0,SnuElement,,SpElement,-38,-38,-38,-38,-38
S,^,The n-th power of x,0,2,0,0,0,0,0,0,0,148,,0,0,SpElement,,SpElement,-38,-38,-38,-38,-38
S,eq,Whether inputs are equal,0,2,0,0,0,0,0,0,0,SpElement,,0,0,SpElement,,36,-38,-38,-38,-38,-38
S,eq,Generic equals (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SpElement,,36,-38,-38,-38,-38,-38
S,eq,Generic equals (tries coercion),0,2,0,0,0,0,0,0,0,SpElement,,0,0,-1,,36,-38,-38,-38,-38,-38
S,eq,Generic equals (tries coercion),0,2,0,0,0,0,0,0,0,SnuElement,,0,0,SpElement,,36,-38,-38,-38,-38,-38
S,eq,Generic equals (tries coercion),0,2,0,0,0,0,0,0,0,SpElement,,0,0,SnuElement,,36,-38,-38,-38,-38,-38
S,ne,Nonequality of inputs,0,2,0,0,0,0,0,0,0,SpElement,,0,0,SpElement,,36,-38,-38,-38,-38,-38
S,ne,Generic unequal (tries coercion),0,2,0,0,0,0,0,0,0,-1,,0,0,SpElement,,36,-38,-38,-38,-38,-38
S,ne,Generic unequal (tries coercion),0,2,0,0,0,0,0,0,0,SpElement,,0,0,-1,,36,-38,-38,-38,-38,-38
S,ne,Generic unequal (tries coercion),0,2,0,0,0,0,0,0,0,SnuElement,,0,0,SpElement,,36,-38,-38,-38,-38,-38
S,ne,Generic unequal (tries coercion),0,2,0,0,0,0,0,0,0,SpElement,,0,0,SnuElement,,36,-38,-38,-38,-38,-38
S,NumericalPrecision,The effective power series precision of the input ring,0,1,0,0,0,0,0,0,0,SpRng,,148,-38,-38,-38,-38,-38
S,PrintNamed,Print SpElement,0,3,0,0,1,0,0,0,0,298,,0,0,298,,0,0,SpElement,,-38,-38,-38,-38,-38,-38
S,LeadingTerm,The leading term of the power series expansion of an S^nu_p element,0,1,0,0,0,0,0,0,0,SpElement,,286,-38,-38,-38,-38,-38
S,WeierstrassTerm,The Weierstrass term of a S^nu_p element,0,1,0,0,0,0,0,0,0,SpElement,,286,-38,-38,-38,-38,-38
S,IsWeaklyZero,True if input is weakly zero,0,1,0,0,0,0,0,0,0,SpElement,,36,-38,-38,-38,-38,-38
S,O,Returns O(x),0,1,0,0,0,0,0,0,0,SpElement,,36,-38,-38,-38,-38,-38
S,Coefficients,"The coefficients of the underlying power series, with valuation shift",0,1,0,0,0,0,0,0,0,SpElement,,82,148,148,-38,-38,-38
S,GaussValuation,Return the Gauss valuation of the element f in its parent S^nu_p Returns Precision(Parent(f))+1 for 0,0,1,0,0,0,0,0,0,0,SpElement,,267,-38,-38,-38,-38,-38
S,WeierstrassDegree,Return the Weierstrass degree of the element f in S^nu_p,0,1,0,0,0,0,0,0,0,SpElement,,267,-38,-38,-38,-38,-38
S,Quotrem,"Given A and B returns Q,R such that A = B*Q + R with R a polynomial whose degree is less than the Weierstrass degree of B",0,2,0,0,0,0,0,0,0,SpElement,,0,0,SpElement,,SpElement,SpElement,-38,-38,-38,-38
S,ExtendedGcd,"Given A and B with v(A)>=v(B) this returns G,H,w,x,y,z with Aw+Bx=G where v(G)=v(B) and Ay+Bz=H and wz-xy=1. Here H will always be 0, since S_p^nu is Euclidean",0,2,0,0,0,0,0,0,0,SpElement,,0,0,SpElement,,SpElement,SpElement,SpElement,SpElement,SpElement,SpElement
