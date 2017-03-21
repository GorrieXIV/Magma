174,1
S,TannerGraph,"For an LDPC code C, return its Tanner graph. If there are n variables and m checks, then the graph has n+m nodes, the first n of which are the variable nodes",0,1,0,0,0,0,0,0,0,-39,,-26,-38,-38,-38,-38,-38
S,LDPCGirth,"For an LDPC code C, return the girth of its Tanner graph",0,1,0,0,0,0,0,0,0,-39,,148,-38,-38,-38,-38,-38
S,LDPCCode,"Given a sparse binary matrix H, return the LDPC code which has H as its parity check matrix",0,1,0,0,0,0,0,0,0,93,,-39,-38,-38,-38,-38,-38
S,GallagerCode,"Return a random (a,b)-regular LDPC code of length n, using Gallager's original method of construction",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,-39,-38,-38,-38,-38,-38
S,MargulisCode,"Return the (3,6)-regular binary LDPC code of length 2(p^3-p) using the group-based construction of Margulis",0,1,0,0,0,0,0,0,0,148,,-39,-38,-38,-38,-38,-38
S,RegularLDPCEnsemble,"Return a random code from the ensemble of (a,b)-regular binary LDPC codes",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,-39,-38,-38,-38,-38,-38
S,IrregularLDPCEnsemble,"Given (unnormalized) degree distributions for check and vertex weights, return an LDPC code from the corresponding ensemble of length n. Note that the distributions will not be matched perfectly unless everything is in complete balance",0,3,0,0,0,0,0,0,0,82,,0,0,82,,0,0,148,,-39,-38,-38,-38,-38,-38
S,IsRegularLDPC,"Returns true if C is an LDPC code and has regular column and row weights. If true, the row and column weights are also returned",0,1,0,0,0,0,0,0,0,-39,,36,148,148,-38,-38,-38
S,GoodLDPCEnsemble,Returns the published threshold and density distributions of good irregular LDPC code ensembles which have been published in the literature. They occur in no particular order,0,1,0,0,0,0,0,0,0,148,,402,82,82,-38,-38,-38
S,DensityEvolutionBinarySymmetric,"Evolve the ensemble of irregular LDPC codes on the binary symmetric channel using probability p0, determining if p0 lies below the threshold",2,0,1,82,0,402,1,1,82,0,402,3,0,0,0,0,0,0,0,402,,0,0,82,,0,0,82,,36,-38,-38,-38,-38,-38
S,LDPCBinarySymmetricThreshold,Determine the threshold over the binary symmetric channel of the irregular LDPC ensemble,2,0,1,82,0,402,1,1,82,0,402,2,0,0,0,0,0,0,0,82,,0,0,82,,402,-38,-38,-38,-38,-38
S,DensityEvolutionBinarySymmetric,"Evolve the ensemble of (v,c)-regular LDPC codes on the binary symmetric channel using probability p0, determining if p0 lies below the threshold",0,3,0,0,0,0,0,0,0,402,,0,0,148,,0,0,148,,36,-38,-38,-38,-38,-38
S,LDPCBinarySymmetricThreshold,"Determine the threshold over the binary symmetric channel of the (dv,dc)-regular LDPC ensemble",0,2,0,0,0,0,0,0,0,148,,0,0,148,,402,-38,-38,-38,-38,-38
S,LDPCEnsembleRate,"Return the rate of codes in an LDPC ensemble defined by the given density distributions. Note that this function just weights the input densities, so it may give results greater than 1",2,0,1,82,0,402,1,1,82,0,402,2,0,0,0,0,0,0,0,82,,0,0,82,,402,-38,-38,-38,-38,-38
S,LDPCEnsembleRate,"Return the rate of a (v,c)-regular LDPC code. Note that this function just weights the input densities, so it may give results greater than 1",0,2,0,0,0,0,0,0,0,148,,0,0,148,,402,-38,-38,-38,-38,-38
