174,1
S,NumberOfSmoothDivisors,"The number of effective divisors of degree less equal n who consist of places of degree less equal m only. P[i] contains the (generic) number of places of degree 1 <= i <= min(n, m)",1,2,1,82,0,-45,3,0,0,0,0,0,0,0,82,,0,0,148,,0,0,148,,-45,-38,-38,-38,-38,-38
V,ClassGroup,2
A,FldFunG,2,S,cld
A,RngFunOrd,4,S,UToF,FToId,IdToCl
A,SetEnum,6,S,fS,SReg,USToF,FToDivS,DivSToClS
A,Map,1,PreimageTest
S,ClassGroupAbelianInvariants,The Abelian invariants of the divisor class group of F,0,1,0,0,0,0,0,0,0,-3,,82,-38,-38,-38,-38,-38
S,ClassGroup,"The divisor class group of F as an Abelian group, a map of representatives from the class group to the divisor group and the homomorphism from the divisor group onto the divisor class group",0,1,0,0,0,0,0,0,0,-3,,107,175,175,-38,-38,-38
S,ClassNumber,The order of the group of divisor classes of degree zero of F,0,1,0,0,0,0,0,0,0,-3,,148,-38,-38,-38,-38,-38
S,GlobalUnitGroup,"The group of global units of F, i.e. the multiplicative group of the exact constant field, as an Abelian group together with the map into F",0,1,0,0,0,0,0,0,0,-3,,107,175,-38,-38,-38,-38
S,IsGlobalUnit,"Whether a is a global unit, i.e. a constant",0,1,0,0,0,0,0,0,0,5,,36,-38,-38,-38,-38,-38
S,IsGlobalUnitWithPreimage,"True and the preimage of a in the global unit group, false otherwise",0,1,0,0,0,0,0,0,0,5,,36,108,-38,-38,-38,-38
S,PrincipalDivisorMap,The map from the multiplicative group of the function field to the group of divisors,0,1,0,0,0,0,0,0,0,-3,,175,-38,-38,-38,-38,-38
S,ClassGroupExactSequence,"Returns the three maps in the center of the exact sequence 0 -> k -> F -> Div -> Cl -> 0 where k is the global unit group of the function field, F is the multiplicative group of the function field, Div is the divisor group and Cl is the divisor class group",0,1,0,0,0,0,0,0,0,-3,,175,175,175,-38,-38,-38
S,SUnitGroup,The group of S-units as an Abelian group and the map into the function field,1,0,1,83,0,230,1,0,0,0,0,0,0,0,83,,107,175,-38,-38,-38,-38
S,IsSUnit,"True if a is an S-unit, false otherwise",1,1,1,83,0,230,2,0,0,0,0,0,0,0,83,,0,0,5,,36,-38,-38,-38,-38,-38
S,IsSUnitWithPreimage,"True and the preimage of a in the S-unit group if a is an S-unit, false otherwise",1,1,1,83,0,230,2,0,0,0,0,0,0,0,83,,0,0,5,,36,108,-38,-38,-38,-38
S,SRegulator,The S-Regulator,1,0,1,83,0,230,1,0,0,0,0,0,0,0,83,,148,-38,-38,-38,-38,-38
S,SPrincipalDivisorMap,The map from the multiplicative group of the function field to the group of divisors (mod places in S),1,0,1,83,0,230,1,0,0,0,0,0,0,0,83,,175,-38,-38,-38,-38,-38
S,IsSPrincipal,"True and a generator if D is principal modulo places in S, false otherwise",1,1,1,83,0,230,2,0,0,0,0,0,0,0,83,,0,0,59,,36,5,-38,-38,-38,-38
S,SClassGroup,"The S-class group as an Abelian group, a map of representatives from the S-class group to the group of divisors (mod places in S) and the homomorphism from the group of divisors (mod places in S) onto the S-class group",1,0,1,83,0,230,1,0,0,0,0,0,0,0,83,,107,175,175,-38,-38,-38
S,SClassGroupExactSequence,"Returns the three maps in the center of the exact sequence 0 -> U -> F -> Div -> Cl -> 0 where U is the S-unit group, F is the multiplicative group of the function field, Div is the group of divisors (mod places in S) and Cl is the S-class group",1,0,1,83,0,230,1,0,0,0,0,0,0,0,83,,175,175,175,-38,-38,-38
S,SClassGroupAbelianInvariants,The Abelian invariants of the S-class group,1,0,1,83,0,230,1,0,0,0,0,0,0,0,83,,82,-38,-38,-38,-38,-38
S,SClassNumber,The order of the torsion part of the S-class group,1,0,1,83,0,230,1,0,0,0,0,0,0,0,83,,148,-38,-38,-38,-38,-38
S,UnitGroup,The unit group of a finite maximal order O as an Abelian group and the map from the unit group into O,0,1,0,0,0,0,0,0,0,8,,107,175,-38,-38,-38,-38
S,IsUnitWithPreimage,"True and the preimage of a in the unit group of O if a is a unit, false otherwise",0,1,0,0,0,0,0,0,0,9,,36,108,-38,-38,-38,-38
S,Regulator,The regulator of the unit group of the finite maximal order O,0,1,0,0,0,0,0,0,0,8,,148,-38,-38,-38,-38,-38
S,PrincipalIdealMap,The map from the multiplicative group of the field of fractions of O to the group of fractional ideals of O where O is a finite maximal order,0,1,0,0,0,0,0,0,0,8,,175,-38,-38,-38,-38,-38
S,IsPrincipal,"True and a generator if the fractional ideal I is principal, false otherwise",0,1,0,0,0,0,0,0,0,10,,36,5,-38,-38,-38,-38
S,ClassGroup,"The ideal class group of the finite maximal order O as an Abelian group, a map of representatives from the ideal class group to the group of fractional ideals and the homomorphism from the group of fractional ideals onto the ideal class group",0,1,0,0,0,0,0,0,0,8,,107,175,175,-38,-38,-38
S,ClassGroupExactSequence,"Returns the maps in the center of the exact sequence 0 -> U -> F -> Id -> Cl -> 0 where U is the unit group of O, F is the multiplicative group of the field of fractions of O, Id is the group of fractional ideals of O and Cl is the class group of O for a finite maximal order O",0,1,0,0,0,0,0,0,0,8,,175,175,175,-38,-38,-38
S,ClassGroupAbelianInvariants,The Abelian invariants of the ideal class group of the finite maximal order O,0,1,0,0,0,0,0,0,0,8,,82,-38,-38,-38,-38,-38
S,ClassNumber,The order of the ideal class group of the finite maximal order O,0,1,0,0,0,0,0,0,0,8,,148,-38,-38,-38,-38,-38
S,FundamentalUnits,A sequence of fundamental units of the finite maximal order O,0,1,0,0,0,0,0,0,0,8,,82,-38,-38,-38,-38,-38
S,IndependentUnits,A sequence of independent units of the finite maximal order O,0,1,0,0,0,0,0,0,0,8,,82,-38,-38,-38,-38,-38
S,DeleteAttributes,Remove all attributes from R,0,1,0,0,1,0,0,0,0,-44,,-38,-38,-38,-38,-38,-38
S,ClassGroupChecks,Do some checks of the class group functionality. If all is true check the functions for the finite maximal order as well,0,2,0,0,1,0,0,0,0,36,,0,0,-3,,-38,-38,-38,-38,-38,-38
