174,1
T,TorFan,-,0
A,TorFan,18,lattice,cones,cones_all,rays,virtual_ray_indices,has_all_virtual_rays,cones_numbers_of_known_faces,cones_superfaces,cone_indices,cones_maximal,cones_intersections,cones_propagation_array,cones_propagation_seq,cones_propagation_int,is_complete,resolution,terminalisation,canonicalisation
S,PrintNamed,,0,3,0,0,1,0,0,0,0,298,,0,0,298,,0,0,TorFan,,-38,-38,-38,-38,-38,-38
S,DoesDefineFan,"True iff the sequence of cones S defines a fan. If true, then the intersection table for the cones is also given. If the optional parameter 'verbose' (default: false) is set to true then the first obstruction to defining a fan will be printed",1,0,1,82,0,TorCon,1,0,0,0,0,0,0,0,82,,36,82,-38,-38,-38,-38
S,CreateVirtualRays,"Given a sequence S of rays of a fan, computes the remaining virtual rays which form a basis of the lattice complementary to the linear span of S. Virtual rays are useful, for example, when calculating the coordinate ring of the toric variety associated to the fan when the variety is a product of a torus and a smaller toric variety",1,0,1,82,0,TorLatElt,1,0,0,0,0,0,0,0,82,,82,-38,-38,-38,-38,-38
S,VirtualRayIndices,The indices of virtual rays of the fan F calculated so far,0,1,0,0,0,0,0,0,0,TorFan,,82,-38,-38,-38,-38,-38
S,PureRayIndices,The indices of pure rays among all known rays of the fan F,0,1,0,0,0,0,0,0,0,TorFan,,82,-38,-38,-38,-38,-38
S,VirtualRays,All the virtual rays of the fan F,0,1,0,0,0,0,0,0,0,TorFan,,82,-38,-38,-38,-38,-38
S,Fan,,2,0,1,82,1,82,0,148,1,1,82,1,82,0,148,2,0,0,0,0,0,0,0,82,,0,0,82,,TorFan,-38,-38,-38,-38,-38
S,Fan,The fan with rays generated by the toric lattice points in R and cone indices specified by S. If optional parameter 'define_fan' (default: false) is set to true then the verification that the data defines a fan is skipped. If optional parameter 'min_rays' (default: false) is set to true then it is assumed that there are no virtual rays. If the optional parameter 'max_cones' (default: false) is set to true then it is assumed that the cones are maximal. If the optional parameter 'is_complete' (default: false) is set to true then it is assumed that the fan is complete,2,0,1,82,0,TorLatElt,1,1,82,1,82,0,148,2,0,0,0,0,0,0,0,82,,0,0,82,,TorFan,-38,-38,-38,-38,-38
S,Fan,The fan generated by the sequence of cones S. If the optional parameter 'define_fan' (default: false) is set to true then the verification that the data defines a fan is skipped. If the optional parameter 'max_cones' (default: false) is set to true then it is assumed that the cones are maximal. If the optional parameter 'is_complete' (default: false) is set to true then it is assumed that the fan is complete,1,0,1,82,0,TorCon,1,0,0,0,0,0,0,0,82,,TorFan,-38,-38,-38,-38,-38
S,Fan,The fan consisting of a single cone C,0,1,0,0,0,0,0,0,0,TorCon,,TorFan,-38,-38,-38,-38,-38
S,FanWithWeights,The fan generated by the weights W. The optional parameter 'ample' can be used to specify the ample divisor to use. If the optional parameter 'define_fan' (default: false) is set to true then the verification that the weights define a fan is skipped,1,0,1,82,1,82,0,148,1,0,0,0,0,0,0,0,82,,TorFan,-38,-38,-38,-38,-38
S,ZeroFan,The fan in a toric lattice of dimension n supported at 0,0,1,0,0,0,0,0,0,0,148,,TorFan,-38,-38,-38,-38,-38
S,ZeroFan,The fan in the toric lattice L supported at 0,0,1,0,0,0,0,0,0,0,TorLat,,TorFan,-38,-38,-38,-38,-38
S,FanOfAffineSpace,The fan of affine space of dimension d,0,1,0,0,0,0,0,0,0,148,,TorFan,-38,-38,-38,-38,-38
S,FanOfWPS,The fan of n-dimensional projective space,0,1,0,0,0,0,0,0,0,148,,TorFan,-38,-38,-38,-38,-38
S,FanOfWPS,The fan of weighted projective space with weights W,1,0,1,82,0,148,1,0,0,0,0,0,0,0,82,,TorFan,-38,-38,-38,-38,-38
S,FanOfFakeProjectiveSpace,The fan of fake weighted projective space (i.e the quotient of weighted projective space with weights W by a finite group action with weights Q),2,0,1,82,0,148,1,1,82,1,82,0,267,2,0,0,0,0,0,0,0,82,,0,0,82,,TorFan,-38,-38,-38,-38,-38
S,Fan,"The product of fans F1 and F2, together with the following lattice maps: the embedding of the ambient lattice of F1, the embedding of the ambient lattice of F2, the projection onto the ambient lattice of F1, and the projection onto the ambient lattice of F2",0,2,0,0,0,0,0,0,0,TorFan,,0,0,TorFan,,TorFan,175,175,175,175,-38
S,Fan,"The product of the fans in S, together with the following sequences of lattice maps: the embeddings of ambient lattices of the fans in S, and the projections onto the ambient lattices of the fans in S",1,0,1,82,0,TorFan,1,0,0,0,0,0,0,0,82,,TorFan,82,82,-38,-38,-38
S,*,The product of the fans F1 and F2,0,2,0,0,0,0,0,0,0,TorFan,,0,0,TorFan,,TorFan,-38,-38,-38,-38,-38
S,^,The product of n copies of the fan F,0,2,0,0,0,0,0,0,0,148,,0,0,TorFan,,TorFan,-38,-38,-38,-38,-38
S,Blowup,The fan given by subdividing the fan F at the ray R (represented by a toric lattice point),0,2,0,0,0,0,0,0,0,TorLatElt,,0,0,TorFan,,TorFan,-38,-38,-38,-38,-38
S,NormalFan,"The normal fan of the fan F in the quotient lattice, and the corresponding quotient map (does not check that the cone C is a face in F)",0,2,0,0,0,0,0,0,0,TorCon,,0,0,TorFan,,TorFan,175,-38,-38,-38,-38
S,Skeleton,The fan generated by the cones of dimension at most n in the fan F,0,2,0,0,0,0,0,0,0,148,,0,0,TorFan,,TorFan,-38,-38,-38,-38,-38
S,OneSkeleton,The fan generated by the rays of the fan F,0,1,0,0,0,0,0,0,0,TorFan,,TorFan,-38,-38,-38,-38,-38
S,Cones,The cones generating the fan F,0,1,0,0,0,0,0,0,0,TorFan,,82,-38,-38,-38,-38,-38
S,Cone,The i-th cone generating the fan F,0,2,0,0,0,0,0,0,0,148,,0,0,TorFan,,82,-38,-38,-38,-38,-38
S,Cone,"The cone C spanned by those rays in the fan F whose indices appear in S. By default C must be a cone in F. If the optional parameter 'extend' is set to true (default: false), then the smallest cone in F containing C will be found (if such a cone exists). If the parameter 'in_fan' is set to false (default: true) then the cone is created even if it failed previous tests",1,1,1,82,0,148,2,0,0,0,0,0,0,0,82,,0,0,TorFan,,TorCon,-38,-38,-38,-38,-38
S,Rays,The rays of the fan F,0,1,0,0,0,0,0,0,0,TorFan,,82,-38,-38,-38,-38,-38
S,Ray,The i-th ray of the fan F,0,2,0,0,0,0,0,0,0,148,,0,0,TorFan,,TorLatElt,-38,-38,-38,-38,-38
S,PureRays,The pure rays of F (i.e. those that are not virtual - a vector is pure iff it is a minimal R-generator of one of the cones in F),0,1,0,0,0,0,0,0,0,TorFan,,82,-38,-38,-38,-38,-38
S,AllRays,The rays of the fan F. This will include all virtual rays,0,1,0,0,0,0,0,0,0,TorFan,,82,-38,-38,-38,-38,-38
S,ConeIndices,The sequence S of integers such that the cone C is generated by rays with indexes S[i]. C must be a member of the fan F,0,2,0,0,0,0,0,0,0,TorCon,,0,0,TorFan,,82,-38,-38,-38,-38,-38
S,ConeIndices,The sequence S of sets of integers such that the i-th cone of the fan F is generated by the rays with indices S[i]. If the optional parameter 'rays' is given then the indices are relative to this sequence,0,1,0,0,0,0,0,0,0,TorFan,,82,-38,-38,-38,-38,-38
S,Ambient,The toric lattice containing the cones of the fan F,0,1,0,0,0,0,0,0,0,TorFan,,TorLat,-38,-38,-38,-38,-38
S,Face,The smallest cone containing the cone C in the fan F. If no such cone exists in F then an error is produced,0,2,0,0,0,0,0,0,0,TorCon,,0,0,TorFan,,TorCon,-38,-38,-38,-38,-38
S,MaxCones,The cones of maximal dimension in the fan F,0,1,0,0,0,0,0,0,0,TorFan,,82,-38,-38,-38,-38,-38
S,AllCones,The cones of the fan F,0,1,0,0,0,0,0,0,0,TorFan,,82,-38,-38,-38,-38,-38
S,Cones,The n-dimensional cones in the fan F,0,2,0,0,0,0,0,0,0,148,,0,0,TorFan,,82,-38,-38,-38,-38,-38
S,Representative,A representative cone in the fan F,0,1,0,0,0,0,0,0,0,TorFan,,TorCon,-38,-38,-38,-38,-38
S,Zero,The 0-dimensional cone of the fan F,0,1,0,0,0,0,0,0,0,TorFan,,TorCon,-38,-38,-38,-38,-38
S,ConesOfCodimension,The codimension n cones in the fan F,0,2,0,0,0,0,0,0,0,148,,0,0,TorFan,,82,-38,-38,-38,-38,-38
S,ConeIntersection,The intersection of two cones C1 and C2 in the fan F. This is usually more efficient than C1 meet C2,0,3,0,0,0,0,0,0,0,TorCon,,0,0,TorCon,,0,0,TorFan,,TorCon,-38,-38,-38,-38,-38
S,SimplicialSubdivision,A simplicial fan subdividing the fan F,0,1,0,0,0,0,0,0,0,TorFan,,TorFan,-38,-38,-38,-38,-38
S,Resolution,A resolution of singularities of the fan F. If the optional parameter 'deterministic' (default: true) is set to false then a non-deterministic algorithm will be used to calculate the resolution,0,1,0,0,0,0,0,0,0,TorFan,,TorFan,-38,-38,-38,-38,-38
S,Terminalisation,A Q-factorial terminal refinement of the fan F,0,1,0,0,0,0,0,0,0,TorFan,,TorFan,-38,-38,-38,-38,-38
S,Canonicalisation,A Q-factorial canonical refinement of the fan F,0,1,0,0,0,0,0,0,0,TorFan,,TorFan,-38,-38,-38,-38,-38
S,eq,True iff the fans F1 and F2 are equal,0,2,0,0,0,0,0,0,0,TorFan,,0,0,TorFan,,36,-38,-38,-38,-38,-38
S,IsComplete,True iff the fan F is complete,0,1,0,0,0,0,0,0,0,TorFan,,36,-38,-38,-38,-38,-38
S,IsProjective,True iff the fan F defines a projecive variety over the ring K (i.e. iff F is complete and the nef cone is of maximum dimension),0,2,0,0,0,0,0,0,0,TorFan,,0,0,-44,,36,-38,-38,-38,-38,-38
S,IsInSupport,"True iff the toric lattice point v is in support of the fan F. If true, then the index of the first cone in F found to contain v is also given",0,2,0,0,0,0,0,0,0,TorFan,,0,0,TorLatElt,,36,148,-38,-38,-38,-38
S,InnerNormals,"If all the cones of the fan F are Q-Gorenstein, gives a sequence of elements in the dual lattice where the i-th element is the inner normal of the i-th cone of F",0,1,0,0,0,0,0,0,0,TorFan,,82,-38,-38,-38,-38,-38
S,OuterNormals,"If all the cones of the fan F are Q-Gorenstein, gives a sequence of elements in the dual lattice where the i-th element is the outer normal of the i-th cone of F",0,1,0,0,0,0,0,0,0,TorFan,,82,-38,-38,-38,-38,-38
S,IsGorenstein,True iff all cones of the fan F are Gorenstein,0,1,0,0,0,0,0,0,0,TorFan,,36,-38,-38,-38,-38,-38
S,IsQGorenstein,True iff all cones of the fan F are Q-Gorenstein,0,1,0,0,0,0,0,0,0,TorFan,,36,-38,-38,-38,-38,-38
S,IsQFactorial,True iff all cones of the fan F are Q-factorial,0,1,0,0,0,0,0,0,0,TorFan,,36,-38,-38,-38,-38,-38
S,IsIsolated,True iff all cones of the fan F are isolated,0,1,0,0,0,0,0,0,0,TorFan,,36,-38,-38,-38,-38,-38
S,IsTerminal,True iff all cones of the fan F are terminal,0,1,0,0,0,0,0,0,0,TorFan,,36,-38,-38,-38,-38,-38
S,IsCanonical,True iff all cones of the fan F are canonical,0,1,0,0,0,0,0,0,0,TorFan,,36,-38,-38,-38,-38,-38
S,IsSingular,True iff there exists a singular cone in the fan of F,0,1,0,0,0,0,0,0,0,TorFan,,36,-38,-38,-38,-38,-38
S,IsNonSingular,True iff all cones of the fan F are nonsingular,0,1,0,0,0,0,0,0,0,TorFan,,36,-38,-38,-38,-38,-38
S,IsNonsingular,True iff all cones of the fan F are nonsingular,0,1,0,0,0,0,0,0,0,TorFan,,36,-38,-38,-38,-38,-38
S,SingularCones,The minimum sequence of singular cones of the fan F. Also gives the sequences of indices of the rays of F defining each singular cone,0,1,0,0,0,0,0,0,0,TorFan,,82,82,-38,-38,-38,-38
S,NonSimplicialCones,The minimum sequence of non-simplicial cones of the fan F. Also gives the sequences of indices of the rays of F defining each non-simplicial cone,0,1,0,0,0,0,0,0,0,TorFan,,82,82,-38,-38,-38,-38
S,Image,The image of the fan F under the toric lattice map phi,1,0,2,175,0,TorLat,0,TorLat,2,0,0,0,0,0,0,0,TorFan,,0,0,175,,TorFan,-38,-38,-38,-38,-38
S,@,The image of the fan F under the toric lattice map phi,1,1,2,175,0,TorLat,0,TorLat,2,0,0,0,0,0,0,0,175,,0,0,TorFan,,TorFan,-38,-38,-38,-38,-38
S,IsFanMap,True iff the toric lattice identity map determines a map of fans F1 -> F2 (i.e. iff each cone of F1 is a subcone of some cone of F2),0,2,0,0,0,0,0,0,0,TorFan,,0,0,TorFan,,36,-38,-38,-38,-38,-38
S,IsFanMap,"True iff the lattice map phi is a map of fans F1 -> F2, i.e. if phi applied to each cone of F1 is a subcone of some cone of F2",1,2,2,175,0,TorLat,0,TorLat,3,0,0,0,0,0,0,0,175,,0,0,TorFan,,0,0,TorFan,,36,-38,-38,-38,-38,-38
S,in,"True iff C a cone of F (not necessary maximal, could be a face of any other cone)",0,2,0,0,0,0,0,0,0,TorFan,,0,0,TorCon,,36,-38,-38,-38,-38,-38
S,ResolveFanMap,"Given two fans F1 and F2 in the same lattice, finds the fan F such that the lattice identity induces fan maps: F->F1 and F->F2. F1 and F2 are expected to have the same support, otherwise non-proper resolution (more precisely supported at the intersection of the supports of F1 and F2) will be returned",0,2,0,0,0,0,0,0,0,TorFan,,0,0,TorFan,,TorFan,-38,-38,-38,-38,-38
