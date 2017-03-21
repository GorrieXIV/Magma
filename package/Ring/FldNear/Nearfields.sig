174,1
T,Nfd,-,0
A,Nfd,8,gf,prim,p,q,matgrp,sz,psi,phi
T,NfdElt,-,0
A,NfdElt,3,parent,elt,log
T,NfdDck,NfdElt,1,Nfd
A,NfdDck,4,h,v,twist,rho
T,NfdZss,NfdElt,1,Nfd
A,NfdZss,2,ndx,mu
S,DicksonPairs,"List the Dickson pairs (q, v) for prime p, where hlo and hhi are the lower and upper bounds on h and vlo, vhi are the lower and upper bounds on v",0,5,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,0,0,148,,0,0,148,,82,-38,-38,-38,-38,-38
S,DicksonPairs,"List the Dickson pairs (p^h, v) for prime p, where h1 and v1 are upper bounds on h and v",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,82,-38,-38,-38,-38,-38
S,DicksonTriples,"List the Dickson triples (p,h,v) for prime p, where hb and vb are bounds on h and v",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,82,-38,-38,-38,-38,-38
S,DicksonNearfield,"Create a Dickson nearfield from the Dickson pair (q,v)",0,2,0,0,0,0,0,0,0,148,,0,0,148,,NfdDck,-38,-38,-38,-38,-38
S,NumberOfVariants,"The number of non-isomorphic nearfields with Dickson pair (q,v)",0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,NumberOfVariants,The number of variants of the Dickson nearfield N,0,1,0,0,0,0,0,0,0,NfdDck,,148,-38,-38,-38,-38,-38
S,VariantRepresentatives,"Representatives for the variant parameter of nearfields with Dickson pair (q,v)",0,2,0,0,0,0,0,0,0,148,,0,0,148,,82,-38,-38,-38,-38,-38
S,ZassenhausNearfield,Create the irregular nearfield number n),0,1,0,0,0,0,0,0,0,148,,NfdZss,-38,-38,-38,-38,-38
S,+,x + y,0,2,0,0,0,0,0,0,0,NfdElt,,0,0,NfdElt,,NfdElt,-38,-38,-38,-38,-38
S,+:=,x +:= y,0,2,0,0,1,0,0,1,1,NfdElt,,1,1,NfdElt,,-38,-38,-38,-38,-38,-38
S,-,x - y,0,2,0,0,0,0,0,0,0,NfdElt,,0,0,NfdElt,,NfdElt,-38,-38,-38,-38,-38
S,-,-x,0,1,0,0,0,0,0,0,0,NfdElt,,NfdElt,-38,-38,-38,-38,-38
S,-:=,x +:= y,0,2,0,0,1,0,0,1,1,NfdElt,,1,1,NfdElt,,-38,-38,-38,-38,-38,-38
S,*,Left scalar multiple of a nearfield element y,0,2,0,0,0,0,0,0,0,NfdElt,,0,0,148,,NfdElt,-38,-38,-38,-38,-38
S,*,Right scalar multiple of a nearfield element x,0,2,0,0,0,0,0,0,0,148,,0,0,NfdElt,,NfdElt,-38,-38,-38,-38,-38
S,*:=,x *:= y,0,2,0,0,1,0,0,1,1,NfdElt,,1,1,NfdElt,,-38,-38,-38,-38,-38,-38
S,*,x * y,0,2,0,0,0,0,0,0,0,NfdElt,,0,0,NfdElt,,NfdElt,-38,-38,-38,-38,-38
S,Inverse,x^-1,0,1,0,0,0,0,0,0,0,NfdElt,,NfdElt,-38,-38,-38,-38,-38
S,/,The quotient x/y of nearfield elements x and y,0,2,0,0,0,0,0,0,0,NfdElt,,0,0,NfdElt,,NfdElt,-38,-38,-38,-38,-38
S,^,The n-th power of nearfield element x,0,2,0,0,0,0,0,0,0,148,,0,0,NfdElt,,NfdElt,-38,-38,-38,-38,-38
S,^,The conjugate of x by y,0,2,0,0,0,0,0,0,0,NfdElt,,0,0,NfdElt,,NfdElt,-38,-38,-38,-38,-38
S,PrintNamed,Print description of the nearfield N,0,3,0,0,1,0,0,0,0,298,,0,0,298,,0,0,NfdDck,,-38,-38,-38,-38,-38,-38
S,PrintNamed,Print description of the nearfield N,0,3,0,0,1,0,0,0,0,298,,0,0,298,,0,0,NfdZss,,-38,-38,-38,-38,-38,-38
S,#,Cardinality of the nearfield N,0,1,0,0,0,0,0,0,0,Nfd,,148,-38,-38,-38,-38,-38
S,Cardinality,Cardinality of the nearfield N,0,1,0,0,0,0,0,0,0,Nfd,,148,-38,-38,-38,-38,-38
S,Parent,Return the parent of the nearfield element x,0,1,0,0,0,0,0,0,0,NfdElt,,Nfd,-38,-38,-38,-38,-38
S,Print,Print a nearfield element x,0,1,0,0,1,0,0,0,0,NfdElt,,-38,-38,-38,-38,-38,-38
S,Hash,Return the hash value for a nearfield element x,0,1,0,0,0,0,0,0,0,NfdElt,,148,-38,-38,-38,-38,-38
S,!,Coerce a finite field element x into the nearfield N,0,2,0,0,0,0,0,0,0,85,,0,0,Nfd,,NfdElt,-38,-38,-38,-38,-38
S,Element,Create a nearfield element from a finite field element,0,2,0,0,0,0,0,0,0,85,,0,0,Nfd,,NfdElt,-38,-38,-38,-38,-38
S,IsCoercible,True iff the finite field element x is coercible into the nearfield N,0,2,0,0,0,0,0,0,0,-1,,0,0,Nfd,,36,-1,-38,-38,-38,-38
S,ElementToSequence,Create a sequence from an element x of a nearfield,0,1,0,0,0,0,0,0,0,NfdElt,,82,-38,-38,-38,-38,-38
S,in,True iff the element x is in the nearfield N,0,2,0,0,0,0,0,0,0,Nfd,,0,0,-1,,36,-38,-38,-38,-38,-38
S,Random,Create a random element of the nearfield N,0,1,0,0,0,0,0,0,0,Nfd,,NfdElt,-38,-38,-38,-38,-38
S,Identity,Create the multiplicative identity of the nearfield N,0,1,0,0,0,0,0,0,0,Nfd,,NfdElt,-38,-38,-38,-38,-38
S,Zero,Create the additive identity of the nearfield N,0,1,0,0,0,0,0,0,0,Nfd,,NfdElt,-38,-38,-38,-38,-38
S,IsZero,True if x is the additive identity of the nearfield N,0,1,0,0,0,0,0,0,0,NfdElt,,36,-38,-38,-38,-38,-38
S,IsIdentity,True if x is the multiplicative identity of the nearfield N,0,1,0,0,0,0,0,0,0,NfdElt,,36,-38,-38,-38,-38,-38
S,eq,x eq y,0,2,0,0,0,0,0,0,0,NfdElt,,0,0,NfdElt,,36,-38,-38,-38,-38,-38
S,ne,x ne y,0,2,0,0,0,0,0,0,0,NfdElt,,0,0,NfdElt,,36,-38,-38,-38,-38,-38
S,IsUnit,True if the nearfield element x is a unit,0,1,0,0,0,0,0,0,0,NfdElt,,36,-38,-38,-38,-38,-38
S,UnitGroup,The unit group of the nearfield N returned as a matrix group M and a map from M to N,0,1,0,0,0,0,0,0,0,Nfd,,178,175,-38,-38,-38,-38
S,UnitGroup,The unit group of the nearfield N returned as a permutation group,1,0,1,304,0,224,2,0,0,0,0,0,0,0,Nfd,,0,0,304,,224,-38,-38,-38,-38,-38
S,UnitGroup,The unit group of the nearfield N returned as a PC-group,1,0,1,304,0,129,2,0,0,0,0,0,0,0,NfdDck,,0,0,304,,129,-38,-38,-38,-38,-38
S,UnitGroup,The unit group of the nearfield N returned as a PC-group,1,0,1,304,0,129,2,0,0,0,0,0,0,0,NfdZss,,0,0,304,,129,-38,-38,-38,-38,-38
S,Order,Order of the unit x of a nearfield,0,1,0,0,0,0,0,0,0,NfdElt,,148,-38,-38,-38,-38,-38
S,AffineGroup,"The sharply two-transitive affine group associated with a nearfield, returned as a matrix group",0,1,0,0,0,0,0,0,0,Nfd,,178,-38,-38,-38,-38,-38
S,AffineGroup,"The sharply two-transitive affine group associated with a nearfield, returned as a permutation group",1,0,1,304,0,224,2,0,0,0,0,0,0,0,Nfd,,0,0,304,,224,-38,-38,-38,-38,-38
S,AffineGroup,"The sharply two-transitive affine group associated with a regular nearfield, returned as a PC-group",1,0,1,304,0,129,2,0,0,0,0,0,0,0,NfdDck,,0,0,304,,129,-38,-38,-38,-38,-38
S,AffineGroup,"The sharply two-transitive affine group associated with an irregular nearfield, returned as a PC-group",1,0,1,304,0,129,2,0,0,0,0,0,0,0,NfdZss,,0,0,304,,129,-38,-38,-38,-38,-38
S,PrimeField,Return the prime field of the nearfield N,0,1,0,0,0,0,0,0,0,Nfd,,84,-38,-38,-38,-38,-38
S,Kernel,Return the kernel of the nearfield N as a finite field,0,1,0,0,0,0,0,0,0,Nfd,,84,-38,-38,-38,-38,-38
S,ExtendedUnitGroup,The extended unit group of a Dickson nearfield,0,1,0,0,0,0,0,0,0,NfdDck,,178,-38,-38,-38,-38,-38
S,eq,N eq M,0,2,0,0,0,0,0,0,0,NfdDck,,0,0,NfdDck,,36,-38,-38,-38,-38,-38
S,eq,N eq M,0,2,0,0,0,0,0,0,0,NfdZss,,0,0,NfdZss,,36,-38,-38,-38,-38,-38
S,ne,N ne M,0,2,0,0,0,0,0,0,0,NfdDck,,0,0,NfdDck,,36,-38,-38,-38,-38,-38
S,ne,N ne M,0,2,0,0,0,0,0,0,0,NfdZss,,0,0,NfdZss,,36,-38,-38,-38,-38,-38
S,IsIsomorphic,"Test whether the regular nearfields N1 and N2 are isomorphic. If they are, return an isomorphism",0,2,0,0,0,0,0,0,0,NfdDck,,0,0,NfdDck,,36,175,-38,-38,-38,-38
S,AutomorphismGroup,The automorphism group A of the regular nearfield N and a map giving the action of A on N,0,1,0,0,0,0,0,0,0,NfdDck,,224,175,-38,-38,-38,-38
S,AutomorphismGroup,The automorphism group A of the irregular nearfield N and a map giving the action of A on N,0,1,0,0,0,0,0,0,0,NfdZss,,224,-38,-38,-38,-38,-38
S,SubConstr,The sub-nearfield of the Dickson nearfield N generated by E,0,2,0,0,0,0,0,0,0,82,,0,0,NfdDck,,NfdDck,175,-38,-38,-38,-38
S,SubConstr,The sub-nearfield of the Dickson nearfield N generated by x,0,2,0,0,0,0,0,0,0,-1,,0,0,NfdDck,,NfdDck,175,-38,-38,-38,-38
S,ProjectivePlane,The finite projective plane coordinatised by the nearfield N,0,1,0,0,0,0,0,0,0,Nfd,,259,236,234,-38,-38,-38
S,HughesPlane,The Hughes plane based on the nearfield N,0,1,0,0,0,0,0,0,0,Nfd,,259,236,234,-38,-38,-38
