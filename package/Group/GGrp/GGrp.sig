174,1
A,GGrp,16,A,Gamma,action,F,f2gamma,Faction,AB,a2ab,ind_from,ind_mod,ind_proj,ind_rep,H1,CM,k,gamma2fld
S,HackobjPrintGGrp,Prints an object of type GGrp,0,2,0,0,1,0,0,0,0,298,,0,0,494,,-38,-38,-38,-38,-38,-38
S,Group,Returns the Grp object assosiated with A,0,1,0,0,0,0,0,0,0,494,,-27,-38,-38,-38,-38,-38
S,GammaAction,Returns the action assosiated with A,0,1,0,0,0,0,0,0,0,494,,175,-38,-38,-38,-38,-38
S,ActingGroup,Returns the group acting on A,0,1,0,0,0,0,0,0,0,494,,-27,175,-38,-38,-38,-38
S,IsInduced,"Returns true if the Gamma-Group was created as an induced Gamma group. If true, returns the GGrp it was induced from, the normal subgroup as GGrp, the projection and the representative maps as further return values",0,1,0,0,0,0,0,0,0,494,,36,494,494,175,175,-38
S,eq,"Test equality of two Gamma-groups A,B",0,2,0,0,0,0,0,0,0,494,,0,0,494,,36,-38,-38,-38,-38,-38
S,GammaGroup,Return the Gamma-group A as a GGrp object,1,2,2,175,0,-27,0,364,3,0,0,0,0,0,0,0,175,,0,0,-27,,0,0,-27,,494,-38,-38,-38,-38,-38
S,GammaGroup,The Gamma-group A as a GGrp object,1,2,2,175,0,-27,0,118,3,0,0,0,0,0,0,0,175,,0,0,-27,,0,0,-27,,494,-38,-38,-38,-38,-38
S,InducedGammaGroup,The Group A/B as a Gamma-group with the induced Gamma-action. The returned Gamma-group will have the information on the Gamma-group it was induced from,0,2,0,0,0,0,0,0,0,-27,,0,0,494,,494,-38,-38,-38,-38,-38
S,IsNormalised,Returns true if the group is normalised by the action,1,1,2,175,0,-27,0,364,2,0,0,0,0,0,0,0,175,,0,0,-27,,36,-38,-38,-38,-38,-38
