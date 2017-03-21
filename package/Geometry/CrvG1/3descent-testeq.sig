174,1
A,CrvEll,2,ThreeTorsionType,ThreeTorsionPoints
S,ThreeTorsionType,"Identifies the action of Galois on E[3], where E is an elliptic curve over Q. The possible values returned are ""Generic"", ""2Sylow"", ""Dihedral"", ""Generic3Isogeny"", ""Z/3Z-nonsplit"", ""mu3-nonsplit"", ""Diagonal"" and ""mu3+Z/3Z""",1,0,1,334,0,262,1,0,0,0,0,0,0,0,334,,298,-38,-38,-38,-38,-38
S,ThreeTorsionPoints,Same as ThreeTorsionOrbits,1,0,1,334,0,262,1,0,0,0,0,0,0,0,334,,303,-38,-38,-38,-38,-38
S,ThreeTorsionOrbits,"Computes <T_1, ... , T_r> where the T_i are representatives for the Galois orbits on E[3] - O",1,0,1,334,0,262,1,0,0,0,0,0,0,0,334,,303,-38,-38,-38,-38,-38
S,ThreeSelmerElement,"Given a ternary cubic with the same invariants as E, returns an element in (the algebra associated to) the 3-Selmer group of E, corresponding to the cubic",1,0,1,334,0,262,2,0,0,0,0,0,0,0,371,,0,0,334,,303,-38,-38,-38,-38,-38
S,ThreeSelmerElement,"Given a ternary cubic C, returns the corresponding element in (the algebra associated to) the 3-Selmer group of E, where E is the Jacobian of C",0,1,0,0,0,0,0,0,0,-1,,303,-38,-38,-38,-38,-38
S,ThreeSelmerElement,"Given a ternary cubic with the same invariants as E, returns an element in (the algebra associated to) the 3-Selmer group of E, corresponding to the cubic",1,0,1,334,0,262,2,0,0,0,0,0,0,0,493,,0,0,334,,303,-38,-38,-38,-38,-38
S,ThreeSelmerElement,"Given a ternary cubic with the same invariants as E, returns an element in (the algebra associated to) the 3-Selmer group of E, corresponding to the cubic",1,0,1,334,0,262,2,0,0,0,0,0,0,0,63,,0,0,334,,303,-38,-38,-38,-38,-38
S,ThreeTorsionMatrices,"Given a ternary cubic with the same invariants as E, computes a matrix in GL_3(L) describing the action of E[3] on the cubic, where E[3] - {0} = Spec L. The determinant of this matrix is computed by ThreeSelmerElement",1,0,1,334,0,262,2,0,0,0,0,0,0,0,493,,0,0,334,,303,-38,-38,-38,-38,-38
S,ThreeTorsionMatrices,"Given a ternary cubic with the same invariants as E, computes a matrix in GL_3(L) describing the action of E[3] on the cubic, where E[3] - {0} = Spec L. The determinant of this matrix is computed by ThreeSelmerElement",1,0,1,334,0,262,2,0,0,0,0,0,0,0,63,,0,0,334,,303,-38,-38,-38,-38,-38
S,IsEquivalent,"Determines whether two ternary cubics over Q are equivalent as genus one models, and if so also returns the transformation relating them",0,2,0,0,0,0,0,0,0,63,,0,0,63,,36,303,-38,-38,-38,-38
S,Reduce,Replaces a ternary cubic by a GL_3(Z)-equivalent one with smaller coefficients,0,1,0,0,0,0,0,0,0,63,,63,303,-38,-38,-38,-38
