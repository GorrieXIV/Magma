freeze;

/* sporadic group maximal subgroup record format */

SporadicRF := recformat <name : MonStgElt, parent : MonStgElt, 
  generators : SeqEnum, group : Grp, order : RngIntElt, index: RngIntElt>;

