freeze;

declare attributes GrpMat: LMGNode, AutInfo;
declare attributes GrpPerm: AutInfo;
declare attributes RngInt: LMGSchreierBound;
declare verbose LMG, 3;
//seems to be the only way of handling global constants in packages, so
//that they can be changed by the user.
ZZZ := Integers();
ZZZ`LMGSchreierBound := 40000;
LMGRF := recformat<
  RS: BoolElt,			   //true if RandomSchreier works
  verified: BoolElt,               //true if group order verifies
  T: SeqEnum,                      //CompositionTree
  series: SeqEnum,                 //terms in ascending composition series
  ims: List,                       //standard copies of comp factors
  tofacs: List,                    //maps from comp series terms to ims
  fromfacs: List,                  //maps from ims to series terms
  factoword: List,                 //word maps of ims
  Y: SeqEnum,                      //inverse images in G of gens of ims
  W: SeqEnum,                      //SLPs of Y
  factorsol: SeqEnum,              //Is comp factor solvable?
  factortype: SeqEnum,             //1,2,3,4 for position of factor in TF-series
  factorname: List,                //name of comp factor (SimpleGroupName)
  factorord: SeqEnum,              //order of comp factor
  sfclass: SeqEnum,    //sfclass[i] true if i-th socle factor nat rep classical
  socperm: GrpPerm,                //perm group induced on socle factors
  ngensu: RngIntElt,               //number of generators of unipotent radical.
  unirad: GrpMat,                  //unipotent radical
  uniradPC: GrpPC,                 //PC-group isomorphic to unipotnet radical
  uniradtoPC: Map,                 //map unipotnet radical to radPC
  isunirad: BoolElt,               //true if G is a unipotent radical
  uniradgp: GrpMat,                //group for which G is the unipotent radical
  rad: GrpMat,                     //solvable radical
  radPC: GrpPC,                    //PC-group isomorphic to solv radical
  radtoPC: Map,                    //map solv radical to radPC
  israd: BoolElt,                  //true if G is a solvable radical
  radgp: GrpMat,                   //group for which G is the solvable radical
  radmoduniPC: GrpPC,              //PC-group isomorphic to solv radical mod uni
  radmodunitoPC: Map,              //map radical mod unirad to radmoduniPC
  socstar: GrpMat,                 //Socle*
  pker: GrpMat,                    //PKernel
  pkerPC: GrpPC,                   //PC-group isomorphic to PKer/Soc*
  pkertoPC: Map,                   //map PKer to pkerPC
  Gtosocperm: Map,                 //map G to socperm
  GtoGmodsocstar: Map,             //Map G to G/socstar
  Gmodsocstar: GrpPerm,            //G/socstar
  Gtoradquot: Map,                 //Map G to G/rad
  radquot: GrpPerm,                //G/rad
  iwmrq: Map,                      //InverseWordMap of radquot
  cseries: SeqEnum,                //terms in ascending chief series
  cfactorname: SeqEnum,            //names of chief factors (MAGMA style)
  cseriesrad: SeqEnum,     //terms in ascending chief series of G within radpc
  radmods: List,           //radpc modules of layers in cseriesrad
  radmodactions:List,      //functions giving actions of G on radmods  
  genmodactions: List     //actions of group generators on modules
  //rqradmodactions:List     //same as radmodactions but faster using radquot
  //abandoned because it wasn't faster!
>;
