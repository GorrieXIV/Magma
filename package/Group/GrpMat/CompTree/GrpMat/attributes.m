freeze;

declare attributes GrpMat: RandomElements, Seed, NormalSeed, 
SLPGroup, SLPGroupHom, UserGenerators, UserWords, 
ChangeOfBasis, CompositionFactors, 
InverseWordMap, Submodule, ParentModule, 
SL2Basis
;

declare attributes GrpPerm: RandomElements, Seed, NormalSeed, 
SLPGroup, SLPGroupHom, UserGenerators, UserWords, 
InverseWordMap, Basis, Submodule, ActionType; 

declare attributes GrpAb: RandomElements, Seed, NormalSeed, 
SLPGroup, SLPGroupHom, UserGenerators, Basis, // MatrixGenerator, 
UserWords, InverseWordMap, ActionType; 

declare attributes GrpPC: UserGenerators, SLPGroup, SLPGroupHom, 
RandomElements, InverseWordMap;
//, Submodule, ActionType; 

declare attributes GrpAb: UserGenerators, SLPGroup, SLPGroupHom, 
RandomElements;

// declare attributes GrpSLP: RandomProcess, Relations;

declare attributes Grp: 
SLPGroup, SLPGroupHom, UserGenerators, UserWords; 

declare attributes Grp:
                DefiningField,
                SL2OracleData,
                IsNaturalRep,
                IsGeneratedByTransvectionGroups,
                Sp4RecognitionData;

