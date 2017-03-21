freeze;

import "extendaut.m":    FindDerivationsH;
import "extendaut.m":    FindModuleAutomorphismsH;
import "extendaut.m":    FindLiftingAutomorphismsH;
import "extendaut.m":    CalculateAutPresH;
import "oddfns.m":       CalculateOuterAutsH;
import "oddfns.m":       TidyUpH;
import "oddfns.m":       FinalTidyUpH;
import "oddfns.m":       AGAutGroupToMap;
import "radquot.m":      RadQuotAutsH;
import "refineseries.m": CharRefineSeriesH;
import "refineseries.m": DefineGroupGensH;
import "refineseries.m": DoesLayerSplitH;

/* This is a variant of autgp.m where G is known to be the semidirect
 * product of a soluble group N by a group H, N is chosen
 * to be at the bottom of the series, and the subgroup of Aut(G)
 * that fixes N is returned.
 * The main function is AutGpSD and it returns the full record GR.
 */
intrinsic AutGpSG(G :: GrpPerm, H :: GrpPerm, N :: GrpPerm
          :Print:=0,SmallModAut:=1000,
         SmallOuterAutGroup:=20000, SmallSubOutGp:=100000,
         VerySmallModAut:=1, PrintSearchCount:=1000, 
         SmallSimpleFactor:=5000)  -> GrpAuto
{The automorphism group of a semidirect product group G=NH fixing N}

/* G should be a finite permutation group.
 */
  local AutRF, GR, L, orq, level, aut, genims, emptylist;

  if Category(G) ne GrpPerm then
    error "Arguments for AutGpSG must be permutation groups";
  end if;
  if not H subset G then
    error "Second Argument for AutGpSG must be a subgroup";
  end if;
  if not IsNormal(G,N) or not IsSoluble(N) then
    error "Third Argument for AutGpSG must be a normal soluble subgroup";
  end if;
  if not #(N meet H) eq 1 or sub<G|N,H> ne G then
    error "Arguments do not describe a semidirect product.";
  end if;

  /* AutRF is the record format for the record in which we will store the
     data needed in the calculation.
   */
  AutRF := recformat< 
  permgroup: GrpPerm,   // The permutation group G
    fpgroup: GrpFP,     // Presentation of group/subseries[level], where level
                        // is how far the computation has got so far -
   fptoperm: Map,       // Isomorphism from fpgroup -> group mapping
                        // Fpgroup.i -> newgens[i]. In fact, when the
                        // computation is done down to level, it is a
                        // isomorphism onto group/subseries[level].
   autgroup: GrpFP,     // Presentation of automorphism group  of
                        // group/subseries[level] - the first few generators
                        // are the same as fpgroup and generate the
                        // inner automorphisms
                        // the generators map onto newgens
 outerautgroup: GrpFP,  // Presentation of outer automorphism group
                        // derived from autgroup by removing inner gens.
    fptoaut: Map,       // Homomorphism from fpgroup -> autgroup
 auttoouter: Map,	// Epimorphism from autgroup to outerautgroup
 orderautgroup: RngIntElt,
                        // order of automorphism group of group/subseries[level]
 orderouterautgroup: RngIntElt, // order of outer automorphism group
                        // group/subseries[level].
     centre: GrpFP,     // The centre of G/subseries[level] as a subgroup
                        // of fpgroup, where level is how far the
                        // computation has got so far.	
    newgens: SeqEnum,   // new generators of G
   newgroup: Grp,       // permgroup with newgens as generators
    radquot: GrpPerm,   // Radical quotient of G (RQ)
     radmap: Map,       // epimorphism group->radquot
  radinvars: Tup,       // triple <#socle(radquot),#radquot,invar>
   rqwordgp: GrpFP,     // the word-group of radquot
  rqgenlist: SeqEnum,   // generators of socle factors of RQ
 rqprojlist: SeqEnum,   // projections onto socle factors of RQ
   rqfplist: SeqEnum,   // word maps of socle factors of RQ
  rqsocquot: GrpPerm,   // Socle quotient of RQ
   rqsocmap: Map,       // epimorphism RQ -> GR`rqsocquot
 rqsqwordmap: Map,       // word map of GR`rqsocquot
  subseries: SeqEnum,   // descending sequence of char. subgroups of G,
                        // subseries[1] is soluble radical of G.
                        // Layers except G/subseries[1] are elementary abelian
                        // subseries[length+1] is trivial.
     length: RngIntElt, // length of subseries - 1.
   radindex: RngIntElt, // #radquot
      index: SeqEnum,   // i-th term is #subseries[i]/#subseries[i+1]
   layermod: SeqEnum,   // i-th term is the module subseries[i]/subseries[i+1] 
   layermap: List,   // maps of G onto layermod
   quotgens: SeqEnum,   // i-th term is number of generators of fpgroup that
                        // generate F modulo subseries[i]
      split: BoolElt,   // true if extension of subseries[level]/
                        // subseries[level+1] splits over G/subseries[level+1]
  outimages: SeqEnum,   // images in fpgroup of its generators under the
                        // outer automorphism generators
   outautos: List,      // the list of the automorphisms of G induced by
                        // the outimages, followed by the inverse autos.
     genims: SeqEnum,   // generator images of generating automorphisms
    soluble: BoolElt,   // true if automorphism group is soluble.
  /* the next few are for control parameters that can be reset as options */
 printlevel: RngIntElt, // = 0,1,2,3 - level of diagnostic printing
 smallmodaut: RngIntElt, // threshhold for using reg. rep. for modaut
 verysmallmodaut: RngIntElt, // threshhold for not computing induced mod aut.
 smallouterautgroup: RngIntElt, // threshhold for reg. rep. of outerautgroup
 smallsuboutgp: RngIntElt, // threshhold for reg. rep. of lifting sub of outgp
   printsct: RngIntElt, // diagnostic print control during big lifting search
 smallsimplefactor: RngIntElt, // order for regular rep. of socle factors,
  /* the final few fields are for technical data when lifting */
 oldfpgroup: GrpFP,     // previous fpgroup
 oldfptoperm: Map,      // previous fptoperm
 oldoutimages: SeqEnum, // previous outimages
    relvals: SeqEnum,   // values of relations of oldfptoperm in module
        cem: ModMatRngElt, // complement equations matrix of extension
   innerder: List,      // i-th element is a list of elements of G that induce
                        // inner derivation automorphisms of G/layermod[i+1] 
   derspace: List,      // i-th element is Space of all derivations (with
                        // supplied basis) of derivations of
                        // G/layermod[i+1] with innerder coming first.
innermodaut: SeqEnum,   // i-th element is list of elements of G that generate
                        // inner module automorphisms.
     modaut: GrpMat,    // The module automorphism group
     mapres: GrpFP,     // Presentation of modaut
  mapresmap: Map,       // homomorphism mapres->modaut
     rmamap: Map,       // Map of modaut onto its regular perm rep.
 liftoutaut: GrpFP,     // presentation of the subgroup of lifting autos in
                        // the old outautgroup
  orderliftoutaut: RngIntElt, //order of `liftoutaut
    /* The next few are for locating elements of the group from a
     * permutation representation used of the holomorph used in the search
     * for lifting outer automorphisms */
    holgens: SeqEnum,
     holmap: Map,
    holperm: SeqEnum,
    holword: SeqEnum,
    gpholpt: SeqEnum,
 newgpholpt: SeqEnum,
    imholpt: SeqEnum, // the final two are used in isomorphism testing.
 newimholpt: SeqEnum
    >;

/* Set fields of GR, and calculate series with elementary layers. */
  GR := rec<AutRF | permgroup:=G, printlevel:=Print, smallmodaut:=SmallModAut,
    smallouterautgroup:=SmallOuterAutGroup, smallsuboutgp:=SmallSubOutGp,
    verysmallmodaut:=VerySmallModAut, printsct:=PrintSearchCount,
    smallsimplefactor:=SmallSimpleFactor >;
  /* First calculate the elementary abelian series for H */ 
  L:=ElementaryAbelianSeriesCanonical(H);
  GR`length:=#L-1;
  GR`subseries:=L;
  /* It is generally better to have small factor groups in the series,
   * so we will attempt to refine it with characteristic subgroups.
   */
  if GR`printlevel gt 2 then
    print "    +Initial series of characteristic subgroups computed.";
  end if;
  CharRefineSeriesH(~GR,Centre(G));
  CharRefineSeriesH(~GR,DerivedGroup(GR`subseries[1]));

  /* Now lift the series to G, putting N at the bottom */
  L := [ sub<G | l,N> : l in GR`subseries ];
  L := Prune(L) cat ElementaryAbelianSeriesCanonical(N);
  GR`length:=#L-1;
  GR`subseries:=L;

  GR`radindex:= Index(G,GR`subseries[1]);
  GR`radquot, GR`radmap := RadicalQuotient(G);
  GR`index:=[]; GR`layermod:=[]; GR`layermap:=[**];
  for i in [1..GR`length] do
    GR`index[i]:= #GR`subseries[i]/#GR`subseries[i+1];
    GR`layermod[i], GR`layermap[i] :=
        GModule(G,GR`subseries[i],GR`subseries[i+1]);
  end for;
  if GR`length eq 0 then GR`subseries[1]:=sub<G|>; end if;
  if GR`printlevel gt 0 then
    print "Series of characteristic subgroups computed.";
    print "Top factor has order",GR`radindex;
    print "Orders of descending elementary abelian layers are: ", GR`index;
  end if;

  GR`soluble := true;
  if GR`radindex eq 1 then
    if GR`printlevel gt 0 then
      print "The group is soluble";
    end if;
    GR`newgens := [];
    GR`newgroup := sub<G|>;
    GR`quotgens := [0];
    GR`split := true;
  else
    emptylist:=[]; // place filler
    RadQuotAutsH(~GR,~GR,false,~emptylist);
    if GR`printlevel gt 0 then
      print "Automorphism group of top factor has order",GR`orderautgroup;
      print "Outer automorphism group of top factor has order",
             GR`orderouterautgroup;
    end if;
  end if;
  /* At this stage, we complete the definition of GR`newgens, by
     putting all of the layermod generators in GR`newgens.
   */
  if GR`printlevel gt 2 then
    print"    +Redefining group generators";
  end if;
  DefineGroupGensH(~GR,true);

  /* Next we decide which of the extensions defined by the layers are split.
   * For the nonsplit ones we may carry out a further refinement into
   * a split extension and a nonsplit Frattini extension by a semisimple
   * module.
   */
  level := 1;
  GR`innerder:=[* *]; GR`derspace:=[* *];
  GR`innermodaut:=[];
  while level le GR`length do
    if GR`printlevel gt 0 then
      print "";
      print "Lifting through level",level,"of order",GR`index[level];
    end if;
    DoesLayerSplitH(~GR,level,~refine);
      /* If this procedure results in a refinement of the series, then
       * 'refine' is set true
       */
    if GR`printlevel gt 0 and refine then
       print
  "The characteristic series is being refined to separate the splitting part.";
    end if;
    if not refine then
      FindDerivationsH(~GR,level,true);
      FindModuleAutomorphismsH(~GR,level,true);
      FindLiftingAutomorphismsH(~GR,level);
      CalculateOuterAutsH(~GR,level);
      CalculateAutPresH(~GR,level);
      if GR`printlevel gt 0 then
        print "Order of automorphism group at this level is",GR`orderautgroup;
        print "Order of outer automorphism group at this level is",
                  GR`orderouterautgroup;
      end if;

      level+:=1;
    end if;
    TidyUpH(~GR);
  end while;
  // The current value of GR`soluble applies to solubility of the outer
  // automorphism group. Correct this:
  if GR`radindex gt 1 then
    GR`soluble := false;
  end if;
  FinalTidyUpH(~GR);

  // Now compute the generator images of the generators of GR`autgroup.
  genims:=[];
  if #G eq 1 then
    GR`fpgroup := Group<x|x>;
    GR`autgroup := Group<x|x>;
    GR`outerautgroup := Group<x|x>;
    GR`orderautgroup := 1;
    GR`orderouterautgroup := 1;
    GR`centre := sub<GR`fpgroup|>;
  else
    for i in [1..Ngens(GR`autgroup)] do
      aut := AGAutGroupToMap(GR,(GR`autgroup).i);
      Append(~genims,[aut(G.i) : i in [1..Ngens(G)]]);
    end for;
  end if;
  GR`genims := genims;

  S := [G.i: i in [1 .. Ngens(G)]];
  A := AutomorphismGroup(G, S, genims);
  A`Group := G;
  A`Order := GR`orderautgroup;
  A`InnerGenerators := [A.i : i in [1..Ngens(GR`fpgroup)]];
  A`Soluble := GR`soluble;
  A`OuterOrder := GR`orderouterautgroup;
  A`CharacteristicSeries := G eq  GR`subseries[1] select GR`subseries
                                                  else [G] cat GR`subseries;
  A`FpGroup := <GR`autgroup, hom<GR`autgroup->A | [A.i : i in [1..Ngens(A)]]> >;
  A`OuterFpGroup := <GR`outerautgroup, GR`auttoouter>;
  return A, GR;

end intrinsic;
