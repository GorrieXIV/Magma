174,1
V,CompositionTree,10
A,Grp,2,CTNodeData,CTCompSeries
S,CompositionTree,"Computes a composition tree, stores it as G`CTNodeData and return tree",1,0,1,178,0,84,1,0,0,0,0,0,0,0,178,,82,-38,-38,-38,-38,-38
S,CompositionTree,"Computes a composition tree, stores it as G`CTNodeData and return tree",0,1,0,0,0,0,0,0,0,224,,82,-38,-38,-38,-38,-38
S,HasCompositionTree,Does G have an attached composition tree?,0,1,0,0,0,0,0,0,0,-27,,36,-38,-38,-38,-38,-38
S,CleanCompositionTree,Remove all data related to composition tree from G,0,1,0,0,1,0,0,0,0,-27,,-38,-38,-38,-38,-38,-38
S,CompositionTreeFastVerification,"G must have a composition tree. Determines if the tree can be verified easily using presentations, ie if presentations on nice generators are known for all leaves",0,1,0,0,0,0,0,0,0,-27,,36,-38,-38,-38,-38,-38
S,CompositionTreeVerify,"G must have a composition tree. Verify the correctness of the composition tree by constructing a presentation for G. If G satisfies the presentation, then return true, and the relators of the presentation as SLPs; otherwise return false. The presentation is on the group returned by CompositionTreeNiceGroup",0,1,0,0,0,0,0,0,0,-27,,36,82,-38,-38,-38,-38
S,int_CompositionTreeFix,G must have a composition tree. Rebuild parts of a composition tree if a verification failed,0,1,0,0,1,0,0,0,0,-27,,-38,-38,-38,-38,-38,-38
S,CompositionTreeElementToWord,"G must have a composition tree. If g is an element of G, then return true and an SLP for g in the nice generators of G, otherwise return false",0,2,0,0,0,0,0,0,0,-28,,0,0,-27,,36,137,-38,-38,-38,-38
S,CompositionTreeNiceToUser,"G must have a composition tree. Returns the coercion map from SLPs in nice generators of G to SLPs in user generators of G, as well as the SLPs of the nice generators in the user generators",0,1,0,0,0,0,0,0,0,-27,,175,82,-38,-38,-38,-38
S,CompositionTreeSLPGroup,"G must have a composition tree. Returns the nice word group for the root node, and the map from the nice word group to the group",0,1,0,0,0,0,0,0,0,-27,,136,175,-38,-38,-38,-38
S,CompositionTreeSLPGroup,"G must have a composition tree. Returns the nice word group for the root node, and the map from the nice word group to the group",1,0,1,178,0,84,1,0,0,0,0,0,0,0,178,,136,175,-38,-38,-38,-38
S,CompositionTreeNiceGroup,G must have a composition tree. Returns the nice group for the root node,0,1,0,0,0,0,0,0,0,-27,,-27,-38,-38,-38,-38,-38
S,CompositionTreeFactorNumber,Identifies the minimal i such that g lies in G_i of the composition series for G,0,2,0,0,0,0,0,0,0,-28,,0,0,-27,,148,-38,-38,-38,-38,-38
S,CompositionTreeSeries,"Given a group G with a composition tree, returns: 1. Composition series, 1 = G_0 < G_1 < ... < G_k = G 2. Maps G_i -> S_i, where S_i is the standard copy of G_i / G_(i-1), i >= 1 The kernel of this map is G_(i-1). S_i may be the standard copy plus scalars Z, and the map is then a homomorphism modulo scalars, so that the kernel is (G_(i-1).Z)/Z 3. Maps S_i -> G_i 4. Maps S_i -> WordGroup(S_i) 5. Flag to indicate if the series is a true composition series. 6. A sequence of the leaf nodes in the composition tree corresponding to each composition factor. 7. Maps S_i -> WordGroup(CompositionTreeNiceGroup(G)) All maps are defined by rules, so Function can be applied on them to avoid built-in membership testing. In certain cases the series is not a true composition series, because certain leaves could not be refined completely, due to too large indices",0,1,0,0,0,1,0,0,0,-27,,82,168,168,168,36,82
S,DisplayCompTreeNodes,"Show information about the nodes in the composition tree. The tree is traversed in-order. If NonTrivial is true, then display only non-trivial nodes. If Leaves is true then display only leaves",0,1,0,0,1,0,0,0,0,-27,,-38,-38,-38,-38,-38,-38
S,SearchForDecomposition,Compute image and kernel of a decomposition of G. Also return the partial composition tree,0,1,0,0,0,0,0,0,0,178,,-27,-27,82,-38,-38,-38
S,SearchForDecomposition,Compute image and kernel of a decomposition of G. Also return the partial composition tree,0,1,0,0,0,0,0,0,0,224,,-27,-27,82,-38,-38,-38
S,CompositionTreeReductionInfo,"Return a string description of the reduction at node with number nodeNr in the composition tree for G, as well as the image and kernel of the reduction",0,2,0,0,0,0,0,0,0,148,,0,0,-27,,298,-27,-27,-38,-38,-38
S,CompositionTreeCBM,Return a change of basis matrix that exhibits the Aschbacher reductions of G given by the composition tree,0,1,0,0,0,0,0,0,0,178,,180,-38,-38,-38,-38,-38
S,CompositionTreeOrder,return order of group having composition tree,0,1,0,0,0,0,0,0,0,-27,,148,-38,-38,-38,-38,-38
S,CompositionTreeFactoredOrder,return factored order of group having composition tree,0,1,0,0,0,0,0,0,0,-27,,149,-38,-38,-38,-38,-38
S,CompositionTreeNonAbelianFactors,return a list naming the non-abelian composition factors of a group G having a composition tree,0,1,0,0,0,0,0,0,0,-27,,168,-38,-38,-38,-38,-38
