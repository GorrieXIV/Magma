174,1
T,ShfCoh,-,0
A,ShfCoh,15,M,X,Mtype,Isupp,Iann,Mfull,M0,div_map,rr_space,Mprj,xmats,xmap,prj_is_full,loc_free_rk,is_arith_CM
T,ShfHom,-,0
A,ShfHom,6,dom,cod,r1,r2,hm,deg
S,Print,,0,2,0,0,1,0,0,0,0,298,,0,0,ShfCoh,,-38,-38,-38,-38,-38,-38
S,Print,,0,2,0,0,1,0,0,0,0,298,,0,0,ShfHom,,-38,-38,-38,-38,-38,-38
S,IsCoercible,,0,2,0,0,0,0,0,0,0,-1,,0,0,ShfCoh,,36,-1,-38,-38,-38,-38
S,IsCoercible,,0,2,0,0,0,0,0,0,0,-1,,0,0,ShfHom,,36,-1,-38,-38,-38,-38
S,in,,0,2,0,0,0,0,0,0,0,ShfCoh,,0,0,-1,,36,-38,-38,-38,-38,-38
S,in,,0,2,0,0,0,0,0,0,0,ShfHom,,0,0,-1,,36,-38,-38,-38,-38,-38
S,Sheaf,Create the coherent sheaf on X represented by graded module M,0,2,0,0,0,0,0,0,0,380,,0,0,67,,ShfCoh,-38,-38,-38,-38,-38
S,CanonicalSheaf,"Create the dth Serre twist of the canonical sheaf on (equidimensional, locally Cohen-Macaulay) scheme X",0,2,0,0,0,0,0,0,0,148,,0,0,380,,ShfCoh,-38,-38,-38,-38,-38
S,CanonicalSheaf,"Create the the canonical sheaf on (equidimensional, locally Cohen-Macaulay) scheme X",0,1,0,0,0,0,0,0,0,380,,ShfCoh,-38,-38,-38,-38,-38
S,StructureSheaf,Create the twisted structure sheaf O_X(n) on scheme X,0,2,0,0,0,0,0,0,0,148,,0,0,380,,ShfCoh,-38,-38,-38,-38,-38
S,StructureSheaf,Create the structure sheaf O_X on scheme X,0,1,0,0,0,0,0,0,0,380,,ShfCoh,-38,-38,-38,-38,-38
S,Twist,Create the Serre twist S(d) of sheaf S,0,2,0,0,0,0,0,0,0,148,,0,0,ShfCoh,,ShfCoh,-38,-38,-38,-38,-38
S,Restriction,Restriction of S to subscheme Y of the base scheme of S,0,2,0,0,0,0,0,0,0,380,,0,0,ShfCoh,,ShfCoh,-38,-38,-38,-38,-38
S,SheafOfDifferentials,Return the sheaf of differentials on ordinary projective scheme X,0,1,0,0,0,0,0,0,0,380,,ShfCoh,-38,-38,-38,-38,-38
S,TangentSheaf,Return the locally-free tangent sheaf on ordinary projective scheme X,0,1,0,0,0,0,0,0,0,380,,ShfCoh,-38,-38,-38,-38,-38
S,HorrocksMumfordBundle,P is ordinary projective 4-space over a field. Returns the sheaf giving the rank 2 locally free Horrocks-Mumford bundle on P,0,1,0,0,0,0,0,0,0,379,,ShfCoh,-38,-38,-38,-38,-38
S,Module,Returns the defining module of S,0,1,0,0,0,0,0,0,0,ShfCoh,,67,-38,-38,-38,-38,-38
S,Scheme,Returns the scheme on which sheaf S is supported,0,1,0,0,0,0,0,0,0,ShfCoh,,380,-38,-38,-38,-38,-38
S,FullModule,Returns the maximal (separated) module of S,0,1,0,0,0,0,0,0,0,ShfCoh,,67,-38,-38,-38,-38,-38
S,GlobalSectionSubmodule,Returns the submodule of the maximal module of S generated in degrees >= 0,0,1,0,0,0,0,0,0,0,ShfCoh,,67,-38,-38,-38,-38,-38
S,SaturateSheaf,Compute the maximal graded module representing S,0,1,0,0,1,0,0,1,1,ShfCoh,,-38,-38,-38,-38,-38,-38
S,Domain,Domain of sheaf homomorphism,0,1,0,0,0,0,0,0,0,ShfHom,,ShfCoh,-38,-38,-38,-38,-38
S,Codomain,Codomain of sheaf homomorphism,0,1,0,0,0,0,0,0,0,ShfHom,,ShfCoh,-38,-38,-38,-38,-38
S,Degree,Degree of sheaf homomorphism,0,1,0,0,0,0,0,0,0,ShfHom,,148,-38,-38,-38,-38,-38
S,ModuleHomomorphism,The underlying module homomorphism of sheaf homomorphism,0,1,0,0,0,0,0,0,0,ShfHom,,453,-38,-38,-38,-38,-38
S,SheafHomomorphism,"Returns the homomorphism from S to T given by h, which is a module homomorphism between underlying modules (defining, maximal or global sections)",0,3,0,0,0,0,0,0,0,453,,0,0,ShfCoh,,0,0,ShfCoh,,ShfHom,-38,-38,-38,-38,-38
S,Expand,Expands a sequence of coherent sheaf homomorphisms into a single sheaf homomorphism,1,0,1,82,0,ShfHom,1,0,0,0,0,0,0,0,82,,ShfHom,-38,-38,-38,-38,-38
S,Image,Image of a sheaf homomorphism with the restriction of the map to the image and the inclusion map of the image into the codomain,0,1,0,0,0,0,0,0,0,ShfHom,,ShfCoh,ShfHom,ShfHom,-38,-38,-38
S,Cokernel,Cokernel of a sheaf homomorphism with the projection map of the codomain onto it,0,1,0,0,0,0,0,0,0,ShfHom,,ShfCoh,ShfHom,-38,-38,-38,-38
S,Kernel,Kernel of a sheaf homomorphism with the inclusion map,0,1,0,0,0,0,0,0,0,ShfHom,,ShfCoh,ShfHom,-38,-38,-38,-38
S,DivisorMap,"Returns the (rational) divisor map associated to the invertible sheaf on X given by S and the image of this map. The map returned is usually a scheme graph map but may also be a traditional MapSch. If the graphmap parameter is set to true, a MapSchGrph is definitely returned",0,1,0,0,0,0,0,0,0,ShfCoh,,175,380,-38,-38,-38,-38
S,IntersectionPairing,S1 and S2 are invertible sheaves representing Cartier Divisors D1 and D2 on the same surface X. Returns the intersection number D1.D2,0,2,0,0,0,0,0,0,0,ShfCoh,,0,0,ShfCoh,,148,-38,-38,-38,-38,-38
S,TensorProduct,"Computes the tensor product of two sheaves on the same scheme. If Maximize (default false) is true, the maximal module of the result is used",0,2,0,0,0,0,0,0,0,ShfCoh,,0,0,ShfCoh,,ShfCoh,-38,-38,-38,-38,-38
S,TensorPower,"Computes the nth tensor power of S for n a positive or negaitive integer. If Maximize (default true) is true, the maximal module of the result is used",0,2,0,0,0,0,0,0,0,148,,0,0,ShfCoh,,ShfCoh,-38,-38,-38,-38,-38
S,DirectSum,The direct sum of sheaves S1 and S2,0,2,0,0,0,0,0,0,0,ShfCoh,,0,0,ShfCoh,,ShfCoh,-38,-38,-38,-38,-38
S,DivisorToSheaf,"Returns the invertible sheaf <-> the (locally principal) effective divisor on X defined by ideal I. If GetMax is true (the default), the module computed is the maximal separated one, the associated divisor map is computed and stored and a basis for the Riemann-Roch space is computed and stored at the same time in a slightly more efficient way than for the direct sheaf computation",0,2,0,0,0,0,0,0,0,64,,0,0,380,,ShfCoh,-38,-38,-38,-38,-38
S,RiemannRochBasis,"Returns a basis for the Riemann-Roch space of the (locally principal) effective divisor D on variety X defined by ideal I. Returned as a sequence [F1,..,Fn] of numerators and a denominator G such that rational functions Fi/G on X give a basis for L(D). An invertible sheaf representing the divisor class of D is also returned",0,2,0,0,0,0,0,0,0,64,,0,0,380,,82,63,ShfCoh,-38,-38,-38
S,IsLocallyFree,"Returns whether S is a locally free sheaf of constant rank on its scheme X and, if so, its rank. If parameter UseFitting is true (the default), uses Fitting ideals. Otherwise, uses the etale stratification method described in the handbook. Assumed that X is equidimensional, connected and (locally) Cohen-Macualay for the stratification method",0,1,0,0,0,0,0,0,0,ShfCoh,,36,148,-38,-38,-38,-38
S,IsArithmeticallyCohenMacaulay,Returns whether the maximal separated module representing S is a CohenMacaulay module of maximal dimension over the coordinate ring of its scheme X (which is assumed equidimensional),0,1,0,0,0,0,0,0,0,ShfCoh,,36,-38,-38,-38,-38,-38
S,CohomologyDimension,"The dimension of the cohomology group H^r(X,S(n)) over the base field, where S(n) is the nth Serre twist of coherent sheaf S",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,ShfCoh,,148,-38,-38,-38,-38,-38
S,DimensionOfGlobalSections,"The dimension of the space of global section of $S$, H^0(S), over the base field. (Usually faster) alternative to CohomologyDimension(S,0,0)",0,1,0,0,0,0,0,0,0,ShfCoh,,148,-38,-38,-38,-38,-38
S,Dual,"Returns the dual sheaf of S, Hom(S,O_X) where O_X is the structure sheaf of the scheme of S",0,1,0,0,0,0,0,0,0,ShfCoh,,ShfCoh,-38,-38,-38,-38,-38
S,SheafHoms,"Returns the sheaf Hom(S,T) and a map on the underlying module of Hom(S,T) that takes homogeneous elements to the actual homomorphism they represent",0,2,0,0,0,0,0,0,0,ShfCoh,,0,0,ShfCoh,,ShfCoh,175,-38,-38,-38,-38
S,IsIsomorphicWithTwist,"Returns whether sheaf S is isomorphic to a Serre twist T(d) of T, another sheaf on the same base scheme. If so, the twist d and an isomorphism of degree d are also returned",0,2,0,0,0,0,0,0,0,ShfCoh,,0,0,ShfCoh,,36,148,ShfHom,-38,-38,-38
S,IsIsomorphic,"Returns whether sheaves S and T on the same base scheme are isomorphic. If so, an isomorphism between them is also returned",0,2,0,0,0,0,0,0,0,ShfCoh,,0,0,ShfCoh,,36,ShfHom,-38,-38,-38,-38
S,ZeroSubscheme,"S should be a locally free sheaf (this is not checked) of scheme X and s a homogeneous element of the defining, full or global section module of S, representing a global section of a twist S1 of S. Returns the zero subscheme of s, i.e. the largest subscheme of X on which s pulls back to the zero section of the pullback of S1",0,2,0,0,0,0,0,0,0,69,,0,0,ShfCoh,,380,-38,-38,-38,-38,-38
