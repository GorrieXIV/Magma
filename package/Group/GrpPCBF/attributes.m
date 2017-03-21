freeze;


declare attributes GrpPCBF:
    E, // master group, used for testing
    L, // normal subgroup, used for testing
    // Q, // quotient E/L
    rho, //: Map, // natural homomorphism from E to Q, used for testing
    // GR, //: Rec, // record of type PDF
    strgenpreimgs, //: SetIndx, // preimages of strong generators
    // N: GrpPC, // polycyclically presented group isomorphic to L
    phi, //: Map, // isomorphism from L onto N, used for testing
    pcgens, //: SetIndx, // generators of polycyclic normal subgroup
    // PCGC ,//: SeqEnum,
    // PCGCI, //: SeqEnum,
    // tailelts, //: SeqEnum,
    // taileltsinv, //: SeqEnum,
    e, //: Tup, // identity element of this PCBF-group
    strgenpreimgsnf, //: SeqEnum,
    strgenpreimgsnfinv, //: SeqEnum,
    pcgensnf, //: SeqEnum, // sequence of elements (in normal form) that generate normal subgroup
    grpgens, //: SeqEnum, // sequence of elements (in normal form) that generate the entire group
    ismaster, //: BoolElt, // true iff this record is created from a MAGMA-known group
    supergrp; //: Rec // parent group


// define record formats to store the relevant data

PDF := recformat<
        G: GrpPerm, // the permutation group itself
        natset: SetIndx, // the natural set on which G acts
        B: SeqEnum, // base of gp
        bo: SeqEnum, // basic orbits of gp
        S: SetIndx, // set of strong generators of gp
        Sinv: SetIndx, // set of inverses of strong generators of gp
        sgindexlist: SeqEnum, // sgindexlist[i] is list of indices of strong gens lying in the i-th basic stabiliser G[i]
	sgindexmap: SeqEnum, // sgindexmap[i,j] is Position(sgindexlist[i],j)
        sv: SeqEnum, // sv[i] is Schreier vector for basic orbit number i
        tail: SeqEnum,
        tailinv: SeqEnum,
        utail: SeqEnum,
        utailinv: SeqEnum >;
