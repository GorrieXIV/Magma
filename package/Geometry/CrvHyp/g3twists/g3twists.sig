174,1
V,G3Twists,3
S,ShiodaInvariants,"Compute the Shioda invariants 'J2', 'J3', 'J4', 'J5', 'J6', 'J7', 'J8', 'J9' and 'J10' of a polynomial of degree at most 8, considered as a binary form of degre 8 (see 1967 Shioda's paper). Weights of these invariants are returned too",0,1,0,0,0,0,0,0,0,312,,82,82,-38,-38,-38,-38
S,ShiodaInvariants,"Compute the Shioda invariants 'J2', 'J3', 'J4', 'J5', 'J6', 'J7', 'J8', 'J9' and 'J10' of the hyperelliptic curve y^2 + h(x) * y = f(x) (see 1967 Shioda's paper). Weights of these invariants are returned too",0,1,0,0,0,0,0,0,0,82,,82,82,-38,-38,-38,-38
S,ShiodaInvariants,"Compute the Shioda invariants 'J2', 'J3', 'J4', 'J5', 'J6', 'J7', 'J8', 'J9' and 'J10' of a genus 3 hyperelliptic curve (see 1967 Shioda's paper). Weights of these invariants are returned too",0,1,0,0,0,0,0,0,0,338,,82,82,-38,-38,-38,-38
S,ShiodaInvariantsEqual,Check whether Shioda Invariants V1 en V2 of two genus 3 hyperelliptic curves or of two binary forms of degree 8 are equivalent,0,2,0,0,0,0,0,0,0,82,,0,0,82,,36,-38,-38,-38,-38,-38
S,ShiodaAlgebraicInvariants,"This function computes a degree 5 polynomial in J8 from the 6 free Shioda invariants J2, J3, J4, J5, J6 and J7. This function computes Shioda's relations too, that is 5 polynomials (of degree at most 2) whose roots are respectivaly J9 and J10 (as functions of J8). By default (ratsolve := true), this function computes solutions to Shioda's system and returns them as a list of 9-uplet (J2, J3, J4, J5, J6, J7, J8, J9, J10). Otherwise (ratsolve := false), the system is returned as is",0,1,0,0,0,0,0,0,0,82,,82,-38,-38,-38,-38,-38
S,MaedaInvariants,"Compute the Maeda field invariants 'I2', 'I3', 'I4', 'I4p', 'I8' and 'I9' of a polynomial of degree at most 8, considered as a binary form of degre 8 (see 1990 Maeda's paper)",0,1,0,0,0,0,0,0,0,312,,82,-38,-38,-38,-38,-38
S,MaedaInvariants,"Compute the Maeda field invariants 'I2', 'I3', 'I4', 'I4p', 'I8' and 'I9' of a genus 3 hyperelliptic curve C",0,1,0,0,0,0,0,0,0,338,,82,-38,-38,-38,-38,-38
S,DiscriminantFromShiodaInvariants,Compute the discriminant of a genus 3 hyperelliptic curve with the given Shioda Invariants,0,1,0,0,0,0,0,0,0,82,,-45,-38,-38,-38,-38,-38
S,HyperellipticCurveFromShiodaInvariants,"Compute a genus 3 hyperelliptic curve and its automorphism group from given Shioda invariants if they are non-singular, ""[], <>"" is returned otherwise. For singular Shioda invariants, see the function ""HyperellipticPolynomialFromShiodaInvariants""",0,1,0,0,0,0,0,0,0,82,,338,224,-38,-38,-38,-38
S,HyperellipticPolynomialFromShiodaInvariants,Compute from given Shioda invariants a univariate polynomial f(x) with f of degree 8. This function also returns the automorphism group of the curve y^2 = f(x),0,1,0,0,0,0,0,0,0,82,,312,224,-38,-38,-38,-38
S,HyperellipticPolynomialsFromShiodaInvariants,,1,0,1,82,0,85,1,0,0,0,0,0,0,0,82,,82,224,-38,-38,-38,-38
S,TwistedHyperellipticPolynomialsFromShiodaInvariants,Compute twisted hyperelliptic polynomials and their automorphism groups from Shioda invariants,1,0,1,82,0,85,1,0,0,0,0,0,0,0,82,,82,224,-38,-38,-38,-38
S,GeometricAutomorphismGroupFromShiodaInvariants,Compute the automorphism group from given Shioda invariants (i.e from invariants of genus 3 hyperelliptic curves),0,1,0,0,0,0,0,0,0,82,,224,-38,-38,-38,-38,-38
S,GeometricAutomorphismGroupGenus3Classification,"Give all possible automorphism groups of a genus 3 hyperelliptic curve, and the corresponding number of curves (up to isomorphism and twists) with this group, defined over the finite field given in input",0,1,0,0,0,0,0,0,0,84,,82,82,-38,-38,-38,-38