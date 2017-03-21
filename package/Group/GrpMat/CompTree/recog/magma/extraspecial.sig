174,1
A,GrpMat,1,ExtraSpecialData
V,C6,10
S,HasC6Decomposition,"Given G that normalises an extraspecial r-group or 2-group of symplectic type, tries to find a certain homomorphism into a permutation or a matrix group. Returns true if a homomorphism has been found. Returns false if G is known not to normalise an extraspecial r-group or a 2-group of symplectic type. Returns ""unknown"" if no homomorphism can be found. The algorithm is one-sided Monte Carlo. If it answers ""unknown"", with probability at most ErrorProb, a homomorphism of the required kind still exists. The algorithm is Brooksbank, Niemeyer and Seress: ""A reduction algorithm for matrix groups with an extraspecial normal subgroup"", Math Reviews number 2257997",0,1,0,0,0,0,0,0,0,178,,36,-38,-38,-38,-38,-38
S,C6Parameters,Return prime and exponent of the extraspecial or symplectic subgroup normalised by G,0,1,0,0,0,0,0,0,0,178,,82,-38,-38,-38,-38,-38
S,C6Basis,Return change-of-basis matrix for extraspecial subgroup normalised by G,0,1,0,0,0,0,0,0,0,178,,180,-38,-38,-38,-38,-38
S,C6Kernel,Kernel of homomorphism found by HasC6Decomposition,0,1,0,0,0,0,0,0,0,178,,178,136,-38,-38,-38,-38
S,C6Action,Action element of g on extraspecial or symplectic group normalised by G,0,2,0,0,0,0,0,0,0,180,,0,0,178,,-28,-38,-38,-38,-38,-38
S,C6Image,Image of homomorphism found by HasC6Decomposition,0,1,0,0,0,0,0,0,0,178,,-27,-38,-38,-38,-38,-38
