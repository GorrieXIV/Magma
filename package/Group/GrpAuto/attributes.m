freeze;

declare attributes GrpAuto :
    RepGroup,               /* Preferred representation for automorphim group */
    RepMap,                 /* Map for RepGroup (GrpAuto -> RepGroup) */
    MapToRepElt,            /* UserProgram which takes an arbitrary map and constructs elt of RepGroup */
    MatrixGroup,            /* Matrix group representation */
    RepEltToMap,            /* Take an elt of RepGroup and construct map (faster than RepMap^-1 for matrix rep) */
    MapToAutoElt,           /* Coerce the given Map into the automorphism group */
    PCGenerators;           /* SetIndx containing pc-generators for soluble automorphim group */
