174,1
T,HodgeStruc,-,0
A,HodgeStruc,3,A,w,phv
S,Print,,0,2,0,0,1,0,0,0,0,298,,0,0,HodgeStruc,,-38,-38,-38,-38,-38,-38
S,HodgeStructure,"Create a Hodge structure from a suitable input (sequence, list, tuple)",0,1,0,0,0,0,0,0,0,-1,,HodgeStruc,-38,-38,-38,-38,-38
S,HodgeStructure,"Given a motivic weight and suitable gamma shifts, return the Hodge structure",0,2,0,0,0,0,0,0,0,82,,0,0,148,,HodgeStruc,-38,-38,-38,-38,-38
S,HasHodgeStructure,"Determine whether an L-series has a Hodge structure, and if so return it",0,1,0,0,0,0,0,0,0,LSer,,36,HodgeStruc,-38,-38,-38,-38
S,HodgeStructure,Return the Hodge structure of an L-series (assuming it has one),0,1,0,0,0,0,0,0,0,LSer,,HodgeStruc,-38,-38,-38,-38,-38
S,Eltseq,"Given a Hodge structure, return the underlying eltseq",0,1,0,0,0,0,0,0,0,HodgeStruc,,82,-38,-38,-38,-38,-38
S,+,,0,2,0,0,0,0,0,0,0,HodgeStruc,,0,0,HodgeStruc,,HodgeStruc,-38,-38,-38,-38,-38
S,-,,0,2,0,0,0,0,0,0,0,HodgeStruc,,0,0,HodgeStruc,,HodgeStruc,-38,-38,-38,-38,-38
S,*,Tensor product of Hodge structures,0,2,0,0,0,0,0,0,0,HodgeStruc,,0,0,HodgeStruc,,HodgeStruc,-38,-38,-38,-38,-38
S,TensorProduct,Tensor product of Hodge structures,0,2,0,0,0,0,0,0,0,HodgeStruc,,0,0,HodgeStruc,,HodgeStruc,-38,-38,-38,-38,-38
S,*,,0,2,0,0,0,0,0,0,0,HodgeStruc,,0,0,148,,HodgeStruc,-38,-38,-38,-38,-38
S,^,Iterated tensor product of a Hodge structure,0,2,0,0,0,0,0,0,0,148,,0,0,HodgeStruc,,HodgeStruc,-38,-38,-38,-38,-38
S,Dual,"Dual of a Hodge structure, ie negate all (p,q)",0,1,0,0,0,0,0,0,0,HodgeStruc,,HodgeStruc,-38,-38,-38,-38,-38
S,Determinant,The determinant of a Hodge structure,0,1,0,0,0,0,0,0,0,HodgeStruc,,HodgeStruc,-38,-38,-38,-38,-38
S,SymmetricPower,"Given a Hodge structure, compute its mth symmetric power",0,2,0,0,0,0,0,0,0,148,,0,0,HodgeStruc,,HodgeStruc,-38,-38,-38,-38,-38
S,AlternatingSquare,"Given a Hodge structure, compute its alternating square",0,1,0,0,0,0,0,0,0,HodgeStruc,,HodgeStruc,-38,-38,-38,-38,-38
S,TateTwist,"Given a Hodge structure, twist it by k (reduce weight by 2k)",0,2,0,0,0,0,0,0,0,148,,0,0,HodgeStruc,,HodgeStruc,-38,-38,-38,-38,-38
S,EffectiveHodgeStructure,"Given a Hodge structure, translate it so that all the H^(p,q) have p,q nonnegative, with at least one equal to zero",0,1,0,0,0,0,0,0,0,HodgeStruc,,HodgeStruc,148,-38,-38,-38,-38
S,HodgeVector,"Given a Hodge structure, compute its Hodge vector (and Tate shift)",0,1,0,0,0,0,0,0,0,HodgeStruc,,82,148,-38,-38,-38,-38
S,eq,,0,2,0,0,0,0,0,0,0,HodgeStruc,,0,0,HodgeStruc,,HodgeStruc,-38,-38,-38,-38,-38
S,IsEmpty,,0,1,0,0,0,0,0,0,0,HodgeStruc,,36,-38,-38,-38,-38,-38
S,GammaFactors,"Given a Hodge structure, return its Gamma factors (shifts)",0,1,0,0,0,0,0,0,0,HodgeStruc,,82,-38,-38,-38,-38,-38
S,GammaShifts,"Given a Hodge structure, return its Gamma shifts (factors)",0,1,0,0,0,0,0,0,0,HodgeStruc,,82,-38,-38,-38,-38,-38
S,Degree,"Given a Hodge structure, return its degree",0,1,0,0,0,0,0,0,0,HodgeStruc,,148,-38,-38,-38,-38,-38
S,Weight,"Given a Hodge structure, return its weight",0,1,0,0,0,0,0,0,0,HodgeStruc,,82,-38,-38,-38,-38,-38
S,RootNumber,"Given a Hodge structure, compute the root number at infinity",0,1,0,0,0,0,0,0,0,HodgeStruc,,52,-38,-38,-38,-38,-38
S,CriticalPoints,"Given an L-series with a Hodge structure, return the critical points",0,1,0,0,0,0,0,0,0,LSer,,82,-38,-38,-38,-38,-38
S,CriticalPoints,"Given a Hodge structure, return the critical points of an associated L-series",0,1,0,0,0,0,0,0,0,HodgeStruc,,82,-38,-38,-38,-38,-38
S,ImaginaryTwist,Twist a Hodge structure by the nontrivial weight 0 Hodge structure,0,1,0,0,0,0,0,0,0,HodgeStruc,,HodgeStruc,-38,-38,-38,-38,-38
