174,1
A,ModSym,4,inner_twists,cm_twists,degmap,endomorphism_algebra_centre
S,HasCM,Decides whether or not the modular abelian variety attached to the given modular symbols space has complex multiplication,0,1,0,0,0,0,0,0,0,ModSym,,36,148,-38,-38,-38,-38
S,IsCM,Decides whether or not the modular abelian variety attached to the given modular symbols space has complex multiplication,0,1,0,0,0,0,0,0,0,ModSym,,36,148,-38,-38,-38,-38
S,InnerTwists,"The inner twists characters of the non-CM newform corresponding to the modular symbols space M. For level larger than 100 uses by default a non-proved bound; this can be changed with the optional parameter Proof. WARNING: Even if Proof is True, the program does not prove that every twist returned is in fact an inner twist (though they are up to precision 0.00001)",0,1,0,0,0,0,0,0,0,ModSym,,82,-38,-38,-38,-38,-38
S,DegreeMap,"Data defining the map delta: G_Q -> F*/F*^2 associated to the given space of modular symbols, which must be new and irreducible over Q. Returns a sequence of tuples <t,f>, where t is in Q and f is in F",0,1,0,0,0,0,0,0,0,ModSym,,82,-38,-38,-38,-38,-38
S,BrauerClass,Gives the Brauer class of the endomorphism algebra of the abelian variety A_f attached to the newform f corresponding to the modular symbols space M (resp. the motive M_f for weight larger than 2). It is given as the (possibily empty) list of the places of the centre F that ramify in the quaternion algebra representing this Brauer class,0,1,0,0,0,0,0,0,0,ModSym,,82,-38,-38,-38,-38,-38
S,ObstructionDescentBuildingBlock,"For a modular symbols space M corresponding to a non-CM weight 2 newform f, this computes the obstruction to the existence of a building block over K_P isogenous to the building block B_f corresponding to the form f. This obstruction is given as a list of places of the polyquadratic field K_P",0,1,0,0,0,0,0,0,0,ModSym,,82,-38,-38,-38,-38,-38
S,BoundedFSubspace,Returns the newform subspaces of weight k and Nebentypus character eps corresponding to non-CM newforms for which the field F has degree over Q in the given range,1,2,1,82,0,148,3,0,0,0,0,0,0,0,82,,0,0,148,,0,0,GrpDrchElt,,82,-38,-38,-38,-38,-38