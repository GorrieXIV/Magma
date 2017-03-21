174,1
T,AInfinity,-,0
A,AInfinity,8,A,k,i,R,S,P,m,f
S,ActionMatrix,"Given a vector x representing an element of A, returns a matrix corresponding to the right multiplication action of this vector on the algebra",0,2,0,0,0,0,0,0,0,-34,,0,0,34,,155,-38,-38,-38,-38,-38
S,CohomologyRingQuotient,Returns the quotient ring of cohomology for a CohomologyRing result,0,1,0,0,0,0,0,0,0,270,,-44,175,-38,-38,-38,-38
S,LiftToChainmap,"Takes a module map and returns the corresponding chain map, unique up to chain homotopy, lifting the map in question",0,3,0,0,0,0,0,0,0,148,,0,0,-34,,0,0,183,,182,-38,-38,-38,-38,-38
S,NullHomotopy,Returns a null homotopy of the map f. This should fail IsChainMap and similar tests,0,1,0,0,0,0,0,0,0,182,,182,-38,-38,-38,-38,-38
S,IsNullHomotopy,Verifies a given null homotopy,0,2,0,0,0,0,0,0,0,182,,0,0,182,,36,-38,-38,-38,-38,-38
S,ChainmapToCohomology,Takes a cocycle and returns an element of the cohomology quotient ring containing that cocycle,0,2,0,0,0,0,0,0,0,270,,0,0,182,,-45,-38,-38,-38,-38,-38
S,CohomologyToChainmap,Takes an element of the quotient cohomology ring and constructs a chain map within that coclass,0,3,0,0,0,0,0,0,0,183,,0,0,270,,0,0,-45,,182,-38,-38,-38,-38,-38
S,AInfinityRecord,Constructs the data structure storing data for Aoo calculations in group cohomology. Expects G to be a p-group. n controls how far resolutions are pushed and might be depreciated later,0,2,0,0,0,0,0,0,0,148,,0,0,-27,,270,-38,-38,-38,-38,-38
S,MasseyProduct,"Calculates a Massey product of the given cohomology elements, or if no Massey product exists, calculates an A-infinity higher product in its place",1,1,1,82,0,-45,2,0,0,0,0,0,0,0,82,,0,0,AInfinity,,-45,-38,-38,-38,-38,-38
S,HighProduct,Calculates the Aoo product of the elements in terms,1,1,1,82,0,-45,2,0,0,0,0,0,0,0,82,,0,0,AInfinity,,-45,-38,-38,-38,-38,-38
S,HighMap,Calculates the corresponding Aoo-quasiisomorphism evaluated at the elements in terms,1,1,1,82,0,-45,2,0,0,0,0,0,0,0,82,,0,0,AInfinity,,182,-38,-38,-38,-38,-38
