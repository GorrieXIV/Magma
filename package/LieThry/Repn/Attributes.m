freeze;

declare attributes Map :
  HighestWeightSpaces, // Space of highest weights, possibly decomposed by weight
  HighestWeights,      // Highest weights wrt standard basis
  Weights,             
  WeightSpaces,
  ExtendedTorus,
    //Store result of a WeightBase call
  WeightBase_B,
  WeightBase_vectB, 
  WeightBase_Orbits, 
  WeightBase_vectOrbit, 
  WeightBase_J, 
  WeightBase_Ws, 
  WeightBase_Actions, 
  WeightBase_M, 
  WeightBase_WeylMxs,
    //Store result of a actionsOfWeylReflections call
  WeylRefl_hs,
  WeylRefl_wds,
  WeylRefl_reflmxs,
  WeylRefl_imWeightVect,
  WeylRefl_weightact;

declare attributes Map: UnderlyingFunction, 
  IsProjectiveRepresentation,
  ProjectiveKernelPower;  // the r st the map to GL/{a\in k^*|a^r=1} is a hom

declare attributes AlgLie :
  StandardRepresentation, AdjointRepresentation;

declare attributes GrpLie :
  LieAlgebra, StandardRepresentation, AdjointRepresentation;


