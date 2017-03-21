174,1
V,cbrank,3
S,TwoPowerIsogenyDescentRankBound,"Computes an upper bound for the rank of E(Q) where E/Q is an elliptic curve with rational 2-torsion point T. The program finishes early if the current rank bound is less than Cutoff (by default 2), or if the number of steps exceeds MaxSteps (by default 5). Let phi : E -> E' be the isogeny with kernel generated by T, and phihat : E' -> E the dual isogeny. Let phi_m and phihat_m be the isogenies of degree 2^m obtained by composing phi and phihat m times. Then the rank bound after m steps is that obtained by computing the images of the Selmer groups attached to phi_m and phihat_m in the Selmer groups attached to phi and phihat. The dimensions of these images are also returned. In cases where E or E' has full rational 2-torsion, a 6th step, corresponding to 8-descent, may also be possible",2,0,1,334,0,262,1,1,372,0,262,2,0,0,0,0,0,0,0,372,,0,0,334,,148,82,82,-38,-38,-38
S,TwoPowerIsogenyDescentRankBound,"Returns TwoPowerIsogenyDescentRankBound(E,T) where T is the unique 2-torsion point on E",1,0,1,334,0,262,1,0,0,0,0,0,0,0,334,,148,82,82,-38,-38,-38