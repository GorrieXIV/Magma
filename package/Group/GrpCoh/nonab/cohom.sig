174,1
A,OneCoC,5,coc,A,imgs,class,interelts
S,OneCocycle,Return a 1-cocycle on A defined by the sequence imgs,0,2,0,0,0,0,0,0,0,82,,0,0,494,,495,-38,-38,-38,-38,-38
S,OneCocycle,Return a 1-cocycle on A defined by the map alpha,1,1,2,175,0,-27,0,-27,2,0,0,0,0,0,0,0,175,,0,0,494,,495,-38,-38,-38,-38,-38
S,OneCocycle,Return a 1-cocycle on A defined by the map alpha,0,2,0,0,0,0,0,0,0,141,,0,0,494,,495,-38,-38,-38,-38,-38
S,TrivialOneCocycle,Return the trivial one-cocycle on A,0,1,0,0,0,0,0,0,0,494,,495,-38,-38,-38,-38,-38
S,HackobjPrintOneCoC,Prints an object of type OneCoC,0,2,0,0,1,0,0,0,0,298,,0,0,495,,-38,-38,-38,-38,-38,-38
S,eq,"Test equality of two 1-cocycles alpha, beta",0,2,0,0,0,0,0,0,0,495,,0,0,495,,36,-38,-38,-38,-38,-38
S,@,The image of g under the cocycle alpha,0,2,0,0,0,0,0,0,0,495,,0,0,-28,,36,-38,-38,-38,-38,-38
S,GammaGroup,The Gamma-group on which alpha is defined,0,1,0,0,0,0,0,0,0,495,,494,-38,-38,-38,-38,-38
S,CocycleMap,The map defining alpha,0,1,0,0,0,0,0,0,0,495,,175,-38,-38,-38,-38,-38
S,IsOneCocycle,"Returns true iff imgs defines a 1-cocycle. If true, the 1-cocycle is also returned as the second argument",1,1,1,82,0,-28,2,0,0,0,0,0,0,0,82,,0,0,494,,36,495,-38,-38,-38,-38
S,IsOneCocycle,"Returns true iff alpha defines a 1-cocycle. If true, the 1-cocycle is also returned as the second argument",1,1,2,175,0,-27,0,-27,2,0,0,0,0,0,0,0,175,,0,0,494,,36,495,-38,-38,-38,-38
S,AreCohomologous,"True iff cocycles alpha, beta are cohomologous with respect to some a in A. If true, returns the element a as the second return value",0,2,0,0,0,0,0,0,0,495,,0,0,495,,36,-28,-38,-38,-38,-38
S,CohomologyClass,The cohomology class of alpha,0,1,0,0,0,0,0,0,0,495,,151,-38,-38,-38,-38,-38
S,InducedOneCocycle,Returns the cocycle induced by alpha on the induced Gamma-group A/B,0,3,0,0,0,0,0,0,0,495,,0,0,-27,,0,0,494,,495,-38,-38,-38,-38,-38
S,InducedOneCocycle,Returns the cocycle induced by alpha on the induced Gamma-group AmodB,0,2,0,0,0,0,0,0,0,495,,0,0,494,,495,-38,-38,-38,-38,-38
S,ExtendedOneCocycle,"Given a 1-cocycle alpha in Z^1(G,A/B), return a list of non-cohomologous 1-cocycles in Z^1(G,A), which induce to alpha. If the optional argument OnlyOne is set to true, only one extension is returned. This is much more efficient",0,1,0,0,0,0,0,0,0,495,,83,-38,-38,-38,-38,-38
S,ExtendedCohomologyClass,"Given a 1-cocycle alpha in Z^1(G,A/B), return a list of non-cohomologous 1-cocycles in Z^1(G,A), which induce to alpha or to a 1-cocycle cohomologous to alpha",0,1,0,0,0,0,0,0,0,495,,83,-38,-38,-38,-38,-38
S,Cohomology,"H^n(Gamma, A) as a set of representatives of the cohomology classes",0,2,0,0,0,0,0,0,0,148,,0,0,494,,83,-38,-38,-38,-38,-38
S,OneCohomology,"H^1(Gamma, A) as a set of representatives of the cohomology classes",0,1,0,0,0,0,0,0,0,494,,83,-38,-38,-38,-38,-38
S,OneCohomologyAb,"H^1(Gamma, A) as a set of representatives of the cohomology classes",0,1,0,0,0,0,0,0,0,494,,83,-38,-38,-38,-38,-38
S,OneCohomologyFP_,"H^1(Gamma, A) as a set of representatives of the cohomology classes",0,1,0,0,0,0,0,0,0,494,,83,-38,-38,-38,-38,-38
S,OneCohomologyFP,"H^1(Gamma, A) as a set of representatives of the cohomology classes",0,1,0,0,0,0,0,0,0,494,,83,-38,-38,-38,-38,-38
S,TwistedGroup,The Gamma-group obtained by twisting A by the cocycle alpha,0,2,0,0,0,0,0,0,0,495,,0,0,494,,494,-38,-38,-38,-38,-38
