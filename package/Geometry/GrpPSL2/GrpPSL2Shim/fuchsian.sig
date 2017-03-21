174,1
A,GrpPSL2,10,ShimVolume,ShimEllipticInvariants,ShimLevel,ShimFDDisc,ShimFDGens,ShimGroup,ShimGroupMap,ShimFDSidepairs,IsShimuraGroup,ShimData
A,AlgAssVOrd,2,IsEichler,FuchsianGroup
A,AlgQuat,2,SplitRealPlace,MatrixRepresentation
S,SplitRealPlace,"Returns the unique real place at which A is split, if it exists",0,1,0,0,0,0,0,0,0,17,,332,-38,-38,-38,-38,-38
S,FuchsianMatrixRepresentation,Returns a map A -> M_2(R) when A has a unique split place,0,1,0,0,0,0,0,0,0,17,,175,-38,-38,-38,-38,-38
S,FuchsianGroup,"Returns the group of totally positive units of O modulo base units as a Fuchsian group, where O is an Eichler order of level N in a quaternion algebra of discriminant D over F. If ComputeAlgebra := false, then a representative algebra is not computed, so the object returned is just an empty hull, and only invariants can be computed",0,3,0,0,0,0,0,0,0,217,,0,0,217,,0,0,27,,GrpPSL2,-38,-38,-38,-38,-38
S,FuchsianGroup,"Returns the group O_1^* of units of norm 1 as a Fuchsian group where O is an Eichler order of level N in a quaternion algebra of discriminant D over F. If ComputeAlgebra := false, then a representative algebra is not computed, so the object returned is just an empty hull, and only invariants can be computed",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,262,,GrpPSL2,-38,-38,-38,-38,-38
S,IsEichler,Returns true if and only if the quaternion order O is an Eichler order in Omax,0,2,0,0,0,0,0,0,0,19,,0,0,19,,36,-38,-38,-38,-38,-38
S,IsEichler,Returns true if and only if the quaternion order O is an Eichler order in Omax,0,2,0,0,0,0,0,0,0,435,,0,0,435,,36,-38,-38,-38,-38,-38
S,FuchsianGroup,"Returns the group of units of reduced norm 1 as a Fuchsian group. Currently requires that O is an Eichler order. By default, this is verified; to skip, set VerifyEichler := false",0,1,0,0,0,0,0,0,0,19,,GrpPSL2,-38,-38,-38,-38,-38
S,FuchsianGroup,"Returns the group of totally positive units modulo base units as a Fuchsian group. Currently requires that O is an Eichler order. By default, this is verified; to skip, set VerifyEichler := false. For the group of units of reduced norm 1, set TotallyPositive := false",0,1,0,0,0,0,0,0,0,435,,GrpPSL2,-38,-38,-38,-38,-38
S,FuchsianGroup,"Returns the group of totally positive units modulo base units in a maximal order in A, as a Fuchsian group",0,1,0,0,0,0,0,0,0,17,,GrpPSL2,-38,-38,-38,-38,-38
S,Order,Returns an order of level N inside the maximal quaternion order O,0,2,0,0,0,0,0,0,0,217,,0,0,435,,435,-38,-38,-38,-38,-38
S,FuchsianGroup,"Returns FuchsianGroup(QuaternionOrder(A, N))",0,2,0,0,0,0,0,0,0,148,,0,0,17,,GrpPSL2,-38,-38,-38,-38,-38
S,FuchsianGroup,Returns the group of totally positive units modulo base units in an order of level N in A as a Fuchsian group,0,2,0,0,0,0,0,0,0,217,,0,0,17,,GrpPSL2,-38,-38,-38,-38,-38
S,Quaternion,Returns the quaternion corresponding to the Fuchsian group element g,0,1,0,0,0,0,0,0,0,GrpPSL2Elt,,18,-38,-38,-38,-38,-38
