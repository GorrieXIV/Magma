freeze;

declare attributes GrpAuto :
    PCRepData;              /* Record used to hold process_data when constructing PC reps */

/* Verbose flag for automorphism/isomorphism code for soluble groups */
declare verbose AutomorphismGroupSolubleGroup, 3;

/* Verbose flags for config */
/* Enable computation of AutK where AutS is soluble */
declare verbose AutomorphismGroupSolubleGroupComputeAutK, 1;
/* Disable computation of AutSKN (orbit-sabilizer) */
declare verbose AutomorphismGroupSolubleGroupDoNotComputeAutSKN, 1;
/* Overrides the orbit limit in the AutSKN computation */
declare verbose AutomorphismGroupSolubleGroupAutSKNIgnoreOrbitLimit, 1;

/* Config values */
AutomorphismGroupSolubleGroup_ComputeAutSKN_OrbitLimit := 2^9;
