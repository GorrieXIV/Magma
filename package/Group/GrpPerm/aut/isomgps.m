freeze;

import "extendaut.m":    FindDerivationsH;
import "extendaut.m":    FindModuleAutomorphismsH;
import "extendaut.m":    FindLiftingAutomorphismsH;
import "extendaut.m":    CalculateAutPresH;
import "extendaut.m":    DoesIsomorphismLiftH;
import "oddfns.m":       CalculateOuterAutsH;
import "oddfns.m":       TidyUpH;
import "oddfns.m":       FinalTidyUpH;
import "oddfns.m":       AGAutGroupToMap;
import "radquot.m":      RadQuotAutsH;
import "refineseries.m": CharRefineSeriesH;
import "refineseries.m": DefineGroupGensH;
import "refineseries.m": DoesLayerSplitH;
forward IsIsomorphicGen;

/* The main function IsIsomorphic is for deciding whether two
 * finite permutation or matrix groups H and G are isomorphic and, if so, to
 * define an isomorphism from H to G.
 * Various items of data are computed for this purpose, including a
 * series of characteristic subgroups of H,G with elementary layers (apart
 * from the top layer), a finite presentation of H,G, generators for the
 * centre of H,G, etc.
 * The automorphism group of G is computed as we go along, using the
 * same methods as in the function AutomorphismGroup.
 * If groups are not isomorphic, false alone is returned.
 * If they are then true, an isomorphism is returned.
 */

intrinsic IsIsomorphic (H :: GrpPerm, G :: GrpPerm :Print:=0,SmallModAut:=1000,
        SmallOuterAutGroup:=20000, SmallSubOutGp:=100000,
         VerySmallModAut:=1, PrintSearchCount:=1000, SmallSimpleFactor:=5000)
         -> BoolElt, Map
{True if groups H and G are isomorphic}
     return IsIsomorphicGen(H,G:Print:=Print,SmallModAut:=SmallModAut,
        SmallOuterAutGroup:=SmallOuterAutGroup,
        SmallSubOutGp:=SmallSubOutGp, VerySmallModAut:=VerySmallModAut,
        PrintSearchCount:=PrintSearchCount,
        SmallSimpleFactor:=SmallSimpleFactor);
end intrinsic;

intrinsic IsIsomorphic (H :: GrpPerm, G :: GrpMat :Print:=0,SmallModAut:=1000,
        SmallOuterAutGroup:=20000, SmallSubOutGp:=100000,
         VerySmallModAut:=1, PrintSearchCount:=1000, SmallSimpleFactor:=5000)
         -> BoolElt, Map
{True if groups H and G are isomorphic}
     return IsIsomorphicGen(H,G:Print:=Print,SmallModAut:=SmallModAut,
        SmallOuterAutGroup:=SmallOuterAutGroup,
        SmallSubOutGp:=SmallSubOutGp, VerySmallModAut:=VerySmallModAut,
        PrintSearchCount:=PrintSearchCount,
        SmallSimpleFactor:=SmallSimpleFactor);
end intrinsic;

intrinsic IsIsomorphic (H :: GrpPerm, G :: GrpPC :Print:=0,SmallModAut:=1000,
        SmallOuterAutGroup:=20000, SmallSubOutGp:=100000,
         VerySmallModAut:=1, PrintSearchCount:=1000, SmallSimpleFactor:=5000)
         -> BoolElt, Map
{True if groups H and G are isomorphic}
     return IsIsomorphicGen(H,G:Print:=Print,SmallModAut:=SmallModAut,
        SmallOuterAutGroup:=SmallOuterAutGroup,
        SmallSubOutGp:=SmallSubOutGp, VerySmallModAut:=VerySmallModAut,
        PrintSearchCount:=PrintSearchCount,
        SmallSimpleFactor:=SmallSimpleFactor);
end intrinsic;

intrinsic IsIsomorphic (H :: GrpMat, G :: GrpPerm :Print:=0,SmallModAut:=1000,
        SmallOuterAutGroup:=20000, SmallSubOutGp:=100000,
         VerySmallModAut:=1, PrintSearchCount:=1000, SmallSimpleFactor:=5000)
         -> BoolElt, Map
{True if groups H and G are isomorphic}
     return IsIsomorphicGen(H,G:Print:=Print,SmallModAut:=SmallModAut,
        SmallOuterAutGroup:=SmallOuterAutGroup,
        SmallSubOutGp:=SmallSubOutGp, VerySmallModAut:=VerySmallModAut,
        PrintSearchCount:=PrintSearchCount,
        SmallSimpleFactor:=SmallSimpleFactor);
end intrinsic;

intrinsic IsIsomorphic (H :: GrpMat, G :: GrpMat :Print:=0,SmallModAut:=1000,
        SmallOuterAutGroup:=20000, SmallSubOutGp:=100000,
         VerySmallModAut:=1, PrintSearchCount:=1000, SmallSimpleFactor:=5000)
         -> BoolElt, Map
{True if groups H and G are isomorphic}
     return IsIsomorphicGen(H,G:Print:=Print,SmallModAut:=SmallModAut,
        SmallOuterAutGroup:=SmallOuterAutGroup,
        SmallSubOutGp:=SmallSubOutGp, VerySmallModAut:=VerySmallModAut,
        PrintSearchCount:=PrintSearchCount,
        SmallSimpleFactor:=SmallSimpleFactor);
end intrinsic;

intrinsic IsIsomorphic (H :: GrpMat, G :: GrpPC :Print:=0,SmallModAut:=1000,
        SmallOuterAutGroup:=20000, SmallSubOutGp:=100000,
         VerySmallModAut:=1, PrintSearchCount:=1000, SmallSimpleFactor:=5000)
         -> BoolElt, Map
{True if groups H and G are isomorphic}
     return IsIsomorphicGen(H,G:Print:=Print,SmallModAut:=SmallModAut,
        SmallOuterAutGroup:=SmallOuterAutGroup,
        SmallSubOutGp:=SmallSubOutGp, VerySmallModAut:=VerySmallModAut,
        PrintSearchCount:=PrintSearchCount,
        SmallSimpleFactor:=SmallSimpleFactor);
end intrinsic;

intrinsic IsIsomorphic (H :: GrpPC, G :: GrpPerm :Print:=0,SmallModAut:=1000,
        SmallOuterAutGroup:=20000, SmallSubOutGp:=100000,
         VerySmallModAut:=1, PrintSearchCount:=1000, SmallSimpleFactor:=5000)
         -> BoolElt, Map
{True if groups H and G are isomorphic}
     return IsIsomorphicGen(H,G:Print:=Print,SmallModAut:=SmallModAut,
        SmallOuterAutGroup:=SmallOuterAutGroup,
        SmallSubOutGp:=SmallSubOutGp, VerySmallModAut:=VerySmallModAut,
        PrintSearchCount:=PrintSearchCount,
        SmallSimpleFactor:=SmallSimpleFactor);
end intrinsic;

intrinsic IsIsomorphic (H :: GrpPC, G :: GrpMat :Print:=0,SmallModAut:=1000,
        SmallOuterAutGroup:=20000, SmallSubOutGp:=100000,
         VerySmallModAut:=1, PrintSearchCount:=1000, SmallSimpleFactor:=5000)
         -> BoolElt, Map
{True if groups H and G are isomorphic}
     return IsIsomorphicGen(H,G:Print:=Print,SmallModAut:=SmallModAut,
        SmallOuterAutGroup:=SmallOuterAutGroup,
        SmallSubOutGp:=SmallSubOutGp, VerySmallModAut:=VerySmallModAut,
        PrintSearchCount:=PrintSearchCount,
        SmallSimpleFactor:=SmallSimpleFactor);
end intrinsic;

intrinsic IsIsomorphic (H :: GrpPC, G :: GrpPC :Print:=0,SmallModAut:=1000,
        SmallOuterAutGroup:=20000, SmallSubOutGp:=100000,
         VerySmallModAut:=1, PrintSearchCount:=1000, SmallSimpleFactor:=5000)
         -> BoolElt, Map
{True if groups H and G are isomorphic}
     return IsIsomorphicGen(H,G:Print:=Print,SmallModAut:=SmallModAut,
        SmallOuterAutGroup:=SmallOuterAutGroup,
        SmallSubOutGp:=SmallSubOutGp, VerySmallModAut:=VerySmallModAut,
        PrintSearchCount:=PrintSearchCount,
        SmallSimpleFactor:=SmallSimpleFactor);
end intrinsic;

IsIsomorphicGen := function(H,G:Print:=0,SmallModAut:=1000,
        SmallOuterAutGroup:=20000, SmallSubOutGp:=100000,
         VerySmallModAut:=1, PrintSearchCount:=1000, SmallSimpleFactor:=5000)
  local AutRF, GR, HR, L, LH, orq, level, aut, genims, isomims,
        refine, refineH, TG, TH;

  if #G ne #H then
    if Print gt 0 then
       print "The two groups have different orders.";
    end if;
    return false, _;
  end if;

  if G cmpeq H then
    if Print gt 0 then
       print "The two groups are equal.";
    end if;
	if Type(G) eq GrpPC then
		return true, iso< H->G | [ G | H.i : i in [1..NPCgens(H)] ] >;
	end if;
    return true, iso<H->G | [G| H.i: i in [1..Ngens(H)]]>;
  end if;

  TG := Type(G); TH := Type(H);
  if TG eq GrpPC and TH eq GrpPC then
     if #G ne #H then return false,_; end if;
     if  #Factorisation(#G) eq 1 then
       //G, H p-groups - use special purpose code
        return IsIsomorphicPGroups(H,G);
     end if;
  end if;
  if (TH eq GrpMat or TH eq GrpPerm) and (TG eq GrpPC) then
     if not IsSoluble(H) then return false, _; end if;
     P, phi := PCGroup(H);
     isit, iso := $$(P,G:Print:=Print,SmallModAut:=SmallModAut,
        SmallOuterAutGroup:=SmallOuterAutGroup,
        SmallSubOutGp:=SmallSubOutGp, VerySmallModAut:=VerySmallModAut,
        PrintSearchCount:=PrintSearchCount,
        SmallSimpleFactor:=SmallSimpleFactor);
     if isit then return true, phi*iso;
     else return false, _;
     end if;
   end if;
   if (TG eq GrpMat or TG eq GrpPerm) and (TH eq GrpPC) then
     if not IsSoluble(G) then return false, _; end if;
     P, phi := PCGroup(G);
     isit, iso := $$(H,P:Print:=Print,SmallModAut:=SmallModAut,
        SmallOuterAutGroup:=SmallOuterAutGroup,
        SmallSubOutGp:=SmallSubOutGp, VerySmallModAut:=VerySmallModAut,
        PrintSearchCount:=PrintSearchCount,
        SmallSimpleFactor:=SmallSimpleFactor);
     if isit then return true, iso*phi^-1;
     else return false, _;
     end if;
   end if;

  /* AutRF is the record format for the record in which we will store the
   * data needed in the calculation.
   */
  AutRF := recformat< 
  permgroup: Grp,       // The permutation group G
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
    newgens: SeqEnum,   // our new choice of generators of permgroup
   newgroup: Grp,       // permgroup with newgens as generators
    radquot: GrpPerm,   // Radical quotient of G
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
                        // Layers except G/subseries[1] are elementary abelian
                        // subseries[length+1] is trivial.
     length: RngIntElt, // length of subseries - 1.
   radindex: RngIntElt, // #radquot
      index: SeqEnum,   // i-th term is #subseries[i]/#subseries[i+1]
   layermod: SeqEnum,   // i-th term is the module subseries[i]/subseries[i+1] 
   layermap: SeqEnum,   // maps of G onto layermod
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
    /* The next three are for locating elements of the group from a
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

/* Set fields of GR,HR and calculate series with elementary layers. */
  GR := 
    rec<AutRF | permgroup:=G, printlevel:=Print, smallmodaut:=SmallModAut,
    smallouterautgroup:=SmallOuterAutGroup, smallsuboutgp:=SmallSubOutGp,
    verysmallmodaut:=VerySmallModAut, printsct:=PrintSearchCount,
    smallsimplefactor:=SmallSimpleFactor >;
  HR := 
    rec<AutRF | permgroup:=H, printlevel:=Print, smallmodaut:=SmallModAut,
    smallouterautgroup:=SmallOuterAutGroup, smallsuboutgp:=SmallSubOutGp,
    verysmallmodaut:=VerySmallModAut, printsct:=PrintSearchCount,
    smallsimplefactor:=SmallSimpleFactor >;
  L:=ElementaryAbelianSeriesCanonical(G);
  LH:=ElementaryAbelianSeriesCanonical(H);
  GR`length:=#L-1;
  GR`subseries:=L;
  HR`length:=#LH-1;
  HR`subseries:=LH;
  if #L ne #LH then
    if GR`printlevel gt 0 then
       print "Characteristic series of the two groups are different.";
    end if;
    return false,_;
  end if;
  for i in [1..#L] do if #L[i] ne #LH[i] then
    if GR`printlevel gt 0 then
       print "Characteristic series of the two groups are different.";
    end if;
    return false,_;
  end if; end for;
  if (not (TG eq GrpPC and TH eq GrpPC)) and #L[1] eq #G then
    /* G amd H are both soluble */
    PG, toPG := PCGroup(G);
    PH, toPH := PCGroup(H);
    isit, f := $$(PH,PG:Print:=Print,SmallModAut:=SmallModAut,
            SmallOuterAutGroup:= SmallOuterAutGroup,
	    SmallSubOutGp:=SmallSubOutGp,
	     VerySmallModAut:=VerySmallModAut,
	     PrintSearchCount:=PrintSearchCount,
	     SmallSimpleFactor:=SmallSimpleFactor);
    if isit then
	return true, toPH*f*toPG^-1;
    else
	return false, _;
    end if;
  end if;
  /* It is generally better to have small factor groups in the series,
   * so we will attempt to refine it with characteristic subgroups.
   */
  if GR`printlevel gt 2 then
    print "    +Initial series of characteristic subgroups computed.";
  end if;
  CharRefineSeriesH(~GR,Centre(G));
  CharRefineSeriesH(~HR,Centre(H));
  if #L ne #LH then
    if GR`printlevel gt 0 then
       print "Characteristic series of the two groups are different.";
    end if;
    return false,_;
  end if;
  for i in [1..#L] do if #L[i] ne #LH[i] then
    if GR`printlevel gt 0 then
       print "Characteristic series of the two groups are different.";
    end if;
    return false,_;
  end if; end for;

  GR`radindex:= Index(G,GR`subseries[1]);
  if GR`radindex gt 1 then
    GR`radquot, GR`radmap := RadicalQuotient(G);
  end if;
  GR`index:=[]; GR`layermod:=[]; GR`layermap:=[PowerStructure(Map)|];
  for i in [1..GR`length] do
    GR`index[i]:= #GR`subseries[i]/#GR`subseries[i+1];
    GR`layermod[i], GR`layermap[i] :=
        GModule(G,GR`subseries[i],GR`subseries[i+1]);
  end for;

  HR`radindex:= Index(H,HR`subseries[1]);
  if HR`radindex gt 1 then
    HR`radquot, HR`radmap := RadicalQuotient(H);
  end if;
  HR`index:=[]; HR`layermod:=[]; HR`layermap:=[PowerStructure(Map)|];
  for i in [1..HR`length] do
    HR`index[i]:= #HR`subseries[i]/#HR`subseries[i+1];
    HR`layermod[i], HR`layermap[i] :=
        GModule(H,HR`subseries[i],HR`subseries[i+1]);
  end for;
  if GR`length eq 0 then
     GR`subseries[1]:=sub<G|>;
     HR`subseries[1]:=sub<H|>;
  end if;
  if GR`printlevel gt 0 then
    print "Series of characteristic subgroups computed.";
    print "Top factor has order",GR`radindex;
    print "Orders of descending elementary abelian layers are: ", GR`index;
  end if;

  GR`soluble := true;
  HR`soluble := true;
  if GR`radindex eq 1 then
    if GR`printlevel gt 0 then
      print "The groups are soluble";
    end if;
    GR`newgens  := [];
    GR`newgroup := sub<G|>;
    GR`quotgens := [0];
    GR`split := true;
    HR`newgens  := [];
    HR`newgroup := sub<H|>;
    HR`quotgens := [0];
    HR`split := true;
    isomims:=[];
  else
    isomims:=[];
    RadQuotAutsH(~HR,~GR,true,~isomims);
    if #isomims eq 0 then
      if GR`printlevel gt 0 then
         print "The two groups have nonisomorphic radical quotients.";
      end if;
      return false,_;
    end if;

    // We shall maintain the isomorphism H/subseries[level]->G/subseries[level]
    // as a list isomims of the images of the generators of HR`fpgroup in
    // GR`fpgroup under that image. Since RadQuotAutsH finds corresponding
    // generators, this is straightforward at this stage.
    if GR`printlevel gt 0 then
      print "Isomorphism found between radical quotients of groups.";
      print "Automorphism group of radical quotient has order",GR`orderautgroup;
      print "Outer automorphism group of radical quotient has order",
             GR`orderouterautgroup;
    end if;
  end if;
  /* At this stage, we complete the definition of GR`newgens, by
     making all of the layermod generators generators
   */
  if GR`printlevel gt 2 then
    print"    +Redefining group generators";
  end if;
  DefineGroupGensH(~GR,true);
  DefineGroupGensH(~HR,false);

  /* Next we decide which of the extensions defined by the layers are split.
   * For the nonpslit ones we may carry out a further refinement into
   * a split extension and a nonsplit Frattini extension by a semisimple
   * module.
   */
  level := 1;
  GR`innerder:=[* *]; GR`derspace:=[* *]; GR`innermodaut:=[];
  HR`innerder:=[* *]; HR`derspace:=[* *]; HR`innermodaut:=[];
  while level le GR`length do
    if GR`printlevel gt 0 then
      print "";
      print "Lifting through level",level,"of order",GR`index[level];
    end if;
    DoesLayerSplitH(~GR,level,~refine);
    DoesLayerSplitH(~HR,level,~refineH);
    /* If this procedure results in a refinement of the series, then
     * 'refine' is set true
     */
    if refine ne refineH then
      if GR`printlevel gt 0 then
         print "One of the groups splits and the other does not at this level";
      end if;
      return false,_;
    end if;
    
    if GR`printlevel gt 0 and refine then
       print
  "The characteristic series is being refined to separate the splitting part.";
    end if;
    if not refine then
      if  GR`split ne  HR`split then
        if GR`printlevel gt 0 then
          print "One of the groups splits and the other does not at this level";
        end if;
        return false,_;
      end if;
      FindDerivationsH(~GR,level,true);
      FindDerivationsH(~HR,level,false);
      // Is it necessary or a good idea to do this for H?
      // It gives us a potential distinguishing feature anyway!
      if #GR`innerder[level] ne #HR`innerder[level] or
         Dimension(GR`derspace[level]) ne Dimension(HR`derspace[level]) then
        if GR`printlevel gt 0 then
           print
           "The two groups have different derivation structure at this level.";
        end if;
        return false,_;
      end if;

      FindModuleAutomorphismsH(~GR,level,true);
      FindModuleAutomorphismsH(~HR,level,false);
      if #GR`modaut ne #HR`modaut then
        if GR`printlevel gt 0 then
           print
  "The two groups have different module automorphism groups at this level.";
        end if;
        return false,_;
      end if;

      DoesIsomorphismLiftH(~HR,~GR,level,~isomims);
      if #isomims eq 0 then
        if GR`printlevel gt 0 then
           print
           "Isomorphism Grp1->Grp2 at level", level, "does not lift.";
        end if;
        return false,_;
      end if;

      CalculateOuterAutsH(~GR,level);
      CalculateAutPresH(~GR,level);
      if GR`printlevel gt 0 then
        print "Order of automorphism group at this level is",GR`orderautgroup;
        print "Order of outer automorphism group at this level is",
                  GR`orderouterautgroup;
      end if;

      level+:=1;
    end if;
    TidyUpH(~HR);
    TidyUpH(~GR);
  end while;
  // The current value of GR`soluble applies to solubility of the outer
  // automorphism group. Correct this:
  if GR`radindex gt 1 then
    GR`soluble := false;
  end if;
  FinalTidyUpH(~GR);
  FinalTidyUpH(~HR);

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
  GR`genims:=genims;
  // And finally compute the isomorphism itself!
  if GR`printlevel gt 0 then
    print "Groups are isomorphic - computing isomorphism.";
  end if;
  isom := hom<HR`newgroup->GR`newgroup |
       [HR`newgens[i] -> GR`fptoperm(isomims[i]) : i in [1..#HR`newgens]] >;
  // if Type(G) ne GrpPC then
    isom := hom< H->G | [isom(H.i) : i in [1..Ngens(H)]] >;
  // end if;

  return true, isom;
end function;
