freeze;
 
import "backtrack.m":  FindLiftingOutAutsH;
import "backtrack.m":  PermRepOutAutGpH;
import "backtrack.m":  FindLiftingIsomH;
import "backtrack.m":  EASectionCentraliser;
import "oddfns.m":     AutExtensionH;
import "oddfns.m":     InverseImageGRH;
import "oddfns.m":     IsIsomModH;
import "oddfns.m":     CalculateIsomH;
import "oddfns.m":     CalculateOuterAutsH;
import "oddfns.m":     IsIsomHtoGModH;
import "oddfns.m":     IsomExtensionHtoGH;

FindDerivationsH := procedure(~GR,level,outerauts)
/* Find the derivations of G/subseries[level+1].
 * The centre of G/subseries[level+1] is also computed as part of this
 * process.
 */
  local Z, F, G, m, dm, nfg, ocx, prime,
        newcentgens, minakgens, subak, V, VV, U, vecs,
        ns, innerder, idvecs, dvecs, odvecs, minimagens, subocx, newgens;

  if GR`printlevel gt 1 then
    print "  +Finding derivations";
  end if;
  Z := Integers();
  F := GR`fpgroup;
  G := GR`newgroup;
  newgens := GR`newgens;
  m := GR`layermod[level];
  dm := Dimension(m);
  prime := #BaseRing(m);
  nfg := GR`quotgens[level];
  V:=VectorSpace(GF(prime),dm*nfg);

  if  GR`quotgens[level] eq 0 then
    // only possible if level=1 - no derivations
    GR`centre := GR`fpgroup;
    GR`innerder[1] := [];
    GR`derspace[1] := RSpaceWithBasis([V|]);
    GR`innermodaut[1] := [G|];
    return;
  end if;

  /* We need to find the centre of G/subseries[level+1] and the
   * centraliser of layermod[level] (to find the inner automorphisms
   * that are derivations).
   */
  ocx := sub < G | GR`centre @ GR`oldfptoperm, GR`subseries[level] >;
  actkern :=
       EASectionCentraliser(ocx,GR`subseries[level],GR`subseries[level+1]);
  actkernc := sub<actkern|
           DerivedGroup(actkern), {x^prime:x in Generators(actkern)} >;
  /* actkernc certainly lies in the centre of G/subseries[level+1] -
   * but some other elements of actkern might also.
   */
  newcentgens := (#actkernc eq  1) select [] else 
      [InverseImageGRH(GR,x,level) : x in Generators(actkernc)];
  /* find a minimal generating set of actkern modulo actkernc */
  minakgens := [];
  subak := actkernc;
  for g in Generators(actkern) do
    if not g in subak then
      Append(~minakgens,g);
      subak := sub<actkern| subak,g >;
    end if;
  end for;
  /* Now calculate the derivations of G/subseries[level]->layermod[level]
   * defined by conjugating with the generators of actkern in minakgens.
   */
  vecs:=[]; // will be a list of elements of V - one for each minakgen.
  for g in minakgens do
    vec:=[];
    for i in [1..nfg] do
     /* calculate commutator of newgens[i] with g which lies in
        layermod[level] */
      v := (newgens[i]^-1*g^-1*newgens[i]*g) @ GR`layermap[level];
      for j in [1..dm] do
        vec[(i-1)*dm+j] := v[j];
      end for;
    end for;
    Append(~vecs,V!vec);
  end for;
  /* The elements of actkern corresponding to the nullspace of vecs also
   * lie in the centre of G/subseries[level+1]
   * We also append them to actkernc
   */
  VV:=VectorSpace(GF(prime),#minakgens);
  ns:=NullSpace(Hom(VV,V)!vecs);
  for b in Basis(ns) do
    g:=Id(G);
    for i in [1..#minakgens] do
      g := g * minakgens[i]^(Z!b[i]);
    end for;
    Append(~newcentgens,InverseImageGRH(GR,g,level));
    actkernc := sub <actkern | actkernc, g >;
  end for;
  delete GR`centre;
  GR`centre := (#newcentgens eq 0) select sub <F|>
                else sub<F|newcentgens>;

  /* Now find minimal generators of actkern/actkernc again. These correspond
   * to the inner derivations of G/subseries[level+1]
   */ 
  idvecs := [V|];
  innerder := [];
  subak := actkernc;
  for i in [1..#minakgens] do
    g := minakgens[i];
    if not g in subak then
      Append(~innerder,g);
      Append(~idvecs,vecs[i]);
      subak := sub<actkern| subak,g >;
    end if;
  end for;
  delete vecs;

  /* The full space of derivations of G/subseries[level+1] is given by
   * the nullspace of the complement equations matrix of layermod[level].
   */
  ns := NullSpace(GR`cem);
  /* do a little check! */
  for vec in idvecs do if not vec in ns then
     error "Inner derivation is not a derivation!";
  end if; end for;
  dvecs := Basis(ns);
  /* From these we want to find a basis of the outer derivations */
  odvecs := [];
  U := sub<V|idvecs>;
  for vec in dvecs do if not vec in U then
    Append(~odvecs,vec);
    U:=sub<V | U, vec >;
  end if; end for;
  GR`innerder[level] := innerder; 
  GR`derspace[level] := RSpaceWithBasis(idvecs cat odvecs);
  if GR`printlevel gt 2 then
    print "    +Found derivations";
  end if;

  /* Now record outimages of new outer derivations */
  if outerauts then
    GR`oldoutimages:=GR`outimages;
    GR`outimages:=[];
    for vec in odvecs do
      genims:=[];
      for i in [1..nfg] do
        w:=F.i;
        for j in [1..dm] do
          w := w * (F.(nfg+j))^(Z!vec[(i-1)*dm+j]);
        end for;
        Append(~genims,w);
      end for;
      for j in [1..dm] do
        Append(~genims,F.(nfg+j));
      end for;
      Append(~GR`outimages,genims);
    end for;
  end if;

  /* Finally, at this stage, we can find minimal generators of ocx modulo
   * actkern. These correspond to inner module automorphisms.
   * In the non-split case there should not be any - in the split case,
   * we can choose them in the complement.
   */
  if not GR`split then
    if ocx ne actkern then
      error "In non-split case there should be no inner module automorphisms.";
    end if;
    GR`innermodaut[level] := [G|];
    if GR`printlevel gt 1 then
      print "  +Groups of inner and outer derivations have orders",
               prime^#idvecs,"and ",prime^#odvecs;
    end if;
    return;
  end if;

  minimagens := [G|];
  subocx := actkern;
  for g in Generators(ocx) do
    if not g in subocx then
      Append(~minimagens,InverseImageGRH(GR,g,level-1)@GR`fptoperm);
       //  using level-1 puts them in the complement 
      subocx := sub<ocx| subocx,g >;
    end if;
  end for;
  GR`innermodaut[level] := minimagens;
  if GR`printlevel gt 2 then
    print "    +Found inner module automorphisms.";
  end if;
  if GR`printlevel gt 1 then
    print "  +Groups of inner and outer derivations have orders",
             prime^#idvecs,"and ",prime^#odvecs;
  end if;

end procedure;


FindModuleAutomorphismsH := procedure(~GR,level,outerauts)
/* Find the G-module automorphisms of subseries[level]/subseries[level+1].
 */
  local Z, F, m, dm, nfg, prime, genims, mag, modaut, nima, magens, subma, mat,
            rma, nmagens, ordima;

  if GR`printlevel gt 1 then
    print "  +Finding module automorphisms";
  end if;
  Z := Integers();
  F := GR`fpgroup;
  nfg := GR`quotgens[level];
  m := GR`layermod[level];
  dm := Dimension(m);
  prime := #BaseRing(m);

  if  GR`quotgens[level] eq 0 then // only possible if level=1
    modaut := GL(dm,prime);
    magens := [modaut.i : i in [1..Ngens(modaut)] ];
    GR`outimages:=[];
  else
    modaut := AutomorphismGroup(GR`layermod[level]);
  end if;
/* We want the elements that are inner automorphisms to come first and
 * then reduce list of remaining generators
 */
  nima := #GR`innermodaut[level];
  if nima gt 0 then
    magens:=[];
    for g in GR`innermodaut[level] do
      mat := (g) @ Representation(GR`layermod[level]);
      if not mat in modaut then
        error "Error - inner module automorphism not in whole group";
      end if;
      mat := modaut!mat;
      Append(~magens,mat);
    end for;
    subma := sub<modaut|magens>;
    ordima := #subma;
    for g in Generators(modaut) do
      if not g in subma then
        Append(~magens,g);
        subma:=sub<modaut|subma,g>;
      end if;
    end for;
    /* finally change generators to makeinners come first */
    modaut := sub<modaut|magens>;
  else ordima:=1;
    magens := [modaut.i : i in [1..Ngens(modaut)] ];
  end if;
  /* Next we need to find a presentation of modaut. If the order is not
   * small, then we take it on strong generators - if it is small we use
   * existing generators
   */
  if #modaut lt GR`smallmodaut then
    if GR`printlevel gt 2 then
      print "    +Small module automorphism group";
    end if;
    GR`rmamap, rma := CosetAction(modaut,sub<modaut|>);
    GR`mapres, GR`mapresmap := FPGroup(rma);
  else
    if GR`printlevel gt 2 then
      print "    +Large module automorphism group";
    end if;
    GR`rmamap := IdentityHomomorphism(modaut);
    // Change FPGroup to FPGroupStrong (JJC 22/5/02)
    GR`mapres, GR`mapresmap := FPGroupStrong(modaut);
    // GR`mapres, GR`mapresmap := FPGroup(modaut);
    /* I presume that the first generators of GR`mapres correspond to
     * those of modaut, but had better check!
     */
    nmagens := #magens;
    for i in [1..nmagens] do
      if (GR`mapres.i) @ GR`mapresmap ne magens[i] then
        error "FPGroup function is misbehaving";
      end if;
    end for;
    for i in [nmagens+1..Ngens(GR`mapres)] do
      Append(~magens,(GR`mapres.i) @ GR`mapresmap);
    end for;
    modaut := sub<modaut|magens>;
  end if;

  GR`modaut := modaut;
  mag := [modaut.i : i in [nima+1..Ngens(modaut)]];
  /* In the split case, these will be new outer automorphism generators, so
   * record their outimages. Of course, they centralise the complement.
   */
  if outerauts and GR`split then
    for i in [1..#mag] do
      genims := [ F.i : i in [1..nfg] ];
      for j in [1..dm] do
        w:=Id(F);
        for k in [1..dm] do
          w := w * (F.(nfg+k))^(Z!mag[i][j][k]);
        end for;
        Append(~genims,w);
      end for;
      Append(~GR`outimages,genims);
    end for;
    if not IsSoluble(modaut) then
      GR`soluble:=false;
    end if;
  end if;
  if GR`printlevel gt 1 then
    print "  +Module automorphism group has order ",#modaut;
    print "  +Inner module automorphism group has order ",ordima;
  end if;

end procedure;

FindLiftingAutomorphismsH := procedure(~GR,level)
/* Extend calculation of automorphism group from G/subseries[level] to
   G/subseries[level+1] (G = GR`permgroup).
 */
  local Z, F, G, GG, m, dm, nfg, iso, isiso, modaut, genims,
        allfix, oldoutgp, newgenims, newgens,
        oim, noim, lift, nliftgens, lifthom, subooggens;

  if  GR`quotgens[level] eq 0 then
    // only possible if level=1 - nothing to lift.
    GR`liftoutaut := Group<x|x>;
    GR`orderliftoutaut := 1;
    GR`soluble := IsSoluble(GR`modaut);
    return;
  end if;
  if GR`orderouterautgroup eq 1 then
    GR`liftoutaut := Group<x|x>;
    GR`orderliftoutaut := 1;
    return;
  end if;

  if GR`printlevel gt 1 then
    print "  +Finding which outer automorphisms from previous layer lift.";
  end if;
  Z := Integers();
  F := GR`fpgroup;
  G := GR`newgroup;
  newgens := GR`newgens;
  nfg := GR`quotgens[level];
  m := GR`layermod[level];
  dm := Dimension(m);
  prime := #BaseRing(m);
  modaut := GR`modaut;

  /* We need to find which of the old outer automorphisms fix the module
   * layermod[level]. In the split case, all such lift to automorphisms
   * of G/subseries[level+1], but in the nonsplit case we need to make
   * a further test.
   * First check to see if they all do.
   */
  allfix := true;
  oim := GR`oldoutimages;
  noim := #oim;
  lifthom := hom<GR`oldfpgroup->F | [F.i : i in [1..nfg]] >;
  nliftgens := 0;
  GG := GR`permgroup;
  for i in [1..noim] do
    ims := [(GG.j) @ GR`outautos[i] : j in [1..Ngens(GG)] ];
    isiso, iso := IsIsomModH(GR,ims,level);
    if isiso then
      if GR`split then
        genims := [oa @ lifthom : oa in oim[i] ];
      else
        lift:=false;
        if #modaut lt GR`smallmodaut then
         for g in GR`modaut do
          lift, newgenims := AutExtensionH(GR,oim[i],g*iso,level);
          if lift then
            genims:=newgenims;
            iso := g*iso;
            break;
          end if;
         end for;
        end if;
        if not lift then allfix:=false; break; end if;
      end if;
    else allfix:=false; break;
    end if;
    for j in [1..dm] do
      w:=Id(F);
      for k in [1..dm] do
        w := w * (F.(nfg+k))^(Z!iso[j][k]);
      end for;
      Append(~genims,w);
    end for;
    Append(~GR`outimages,genims);
    nliftgens +:= 1;
  end for;
  if allfix then
    GR`liftoutaut := GR`outerautgroup;
    GR`orderliftoutaut := GR`orderouterautgroup;
    if GR`printlevel gt 1 then
      print "  +All outer automorphisms fix the module and lift.";
    end if;
  else
    if GR`printlevel gt 1 and #modaut lt GR`smallmodaut then
      print "  +Not all outer automorphisms fix the module and lift.";
    end if;
  /* Now form an appropriate permutation representation of the
   * old outer automorphism group.
   */
    PermRepOutAutGpH(~GR,~GR,level,[]);
    oldoutgp := Image(GR`holmap);
    subooggens := [ (GR`holgens)[i] : i in [1..nliftgens] ];
    FindLiftingOutAutsH(~GR,level,oldoutgp,subooggens);
  end if;

end procedure;

DoesIsomorphismLiftH := procedure(~HR,~GR,level,~isomims)
/* Decide whether the isomorphism H/subseries[level]->G/subseries[level]
 * of which the generator imagesare defined by isomims lifts to the
 * next level. If so, extend isomims accordingly, and also
 * Extend calculation of automorphism group from G/subseries[level] to
 * G/subseries[level+1] (G = GR`permgroup).
 * If not, then replace isomims by the empty sequence.
 */
  local Z, F, G, GG,  H, HH, m, dm, nfg, iso, isiso, modaut, genims, newgens,
        Hnewgens, allfix, oldoutgp, newgenims, newisomims,
        oim, noim, lift, nliftgens, lifthom, subooggens,
        HtoG, imsHtoG, isisoHtoG, isoHtoG, liftHtoG, emptylist;

  if  GR`quotgens[level] eq 0 then
    // only possible if level=1 - nothing to lift.
    GR`liftoutaut := Group<x|x>;
    GR`orderliftoutaut := 1;
    GR`soluble := IsSoluble(GR`modaut);
    isomims := [(GR`fpgroup).i : i in [1..(GR`quotgens)[2]] ];
    return;
  end if;

  if GR`printlevel gt 1 then
    print "  +Finding whether isomorphism from previous layer lifts.";
  end if;
  Z := Integers();
  F := GR`fpgroup;
  GG := GR`permgroup;
  G := GR`newgroup;
  newgens := GR`newgens;
  nfg := GR`quotgens[level];
  m := GR`layermod[level];
  dm := Dimension(m);
  prime := #BaseRing(m);
  modaut := GR`modaut;
  HH := HR`permgroup;
  H := HR`newgroup;
  Hnewgens := HR`newgens;
  lifthom := hom<GR`oldfpgroup->F | [F.i : i in [1..nfg]] >;

  /* We will need the isomorphism on G`permgroup/subseries[level]
   * defined by isomims - of course isomims now lie in GR`oldfpgroup.
   * Define first on GR`permgroup.
   */
  HtoG := hom< H->G |
    [Hnewgens[i]->GR`oldfptoperm(isomims[i]) : i in [1.. #isomims]] cat
    [Hnewgens[i]->Id(G) : i in [nfg+1..#Hnewgens]] : Check:=false >; 
  imsHtoG := [HtoG(HH.j) : j in [1..Ngens(HH)] ];
  // Do we induce an isomorphism on the modules?
  isisoHtoG, isoHtoG := IsIsomHtoGModH(HR,GR,imsHtoG,level);
  if isisoHtoG then //yes
    if GR`split then
      liftHtoG:=true;
      isomims := [im @ lifthom : im in isomims ];
    else
      for g in HR`modaut do
        // try lifting with all possible module automorphisms
        liftHtoG, newisomims :=
                        IsomExtensionHtoGH(HR,GR,isomims,g*isoHtoG,level);
        if liftHtoG then
          isomims:=newisomims;
          isoHtoG := g*isoHtoG;
          break;
        end if;
      end for;
    end if;
    if liftHtoG then
      for j in [1..dm] do
        w:=Id(F);
        for k in [1..dm] do
          w := w * (F.(nfg+k))^(Z!isoHtoG[j][k]);
        end for;
        Append(~isomims,w);
      end for;
      if GR`printlevel gt 0 then
        print "Isomorphism lifts - found lifting before search.";
      end if;
    end if;
  else //no
    liftHtoG:=false;  
  end if;
  if GR`printlevel gt 1 and not liftHtoG then
      print
       "  +Isomorphism does not induce module automorphism or does not lift.";
  end if;

  if GR`orderouterautgroup eq 1 then
   // We can now settle this case.
    if not liftHtoG then
      isomims:=[];
      return;
    end if;
    GR`liftoutaut := Group<x|x>;
    GR`orderliftoutaut := 1;
    return;
  end if;

  /* We need to find which of the old outer automorphisms fix the module
   * layermod[level]. In the split case, all such lift to automorphisms
   * of G/subseries[level+1], but in the nonsplit case we need to make
   * a further test.
   * First check to see if they all do.
   */
  allfix := true;
  oim := GR`oldoutimages;
  noim := #oim;
  nliftgens := 0;
  for i in [1..noim] do
    ims := [(GG.j) @ GR`outautos[i] : j in [1..Ngens(GG)] ];
    isiso, iso := IsIsomModH(GR,ims,level);
    if isiso then
      if GR`split then
        genims := [oa @ lifthom : oa in oim[i] ];
      else
        lift:=false;
        if #modaut lt GR`smallmodaut then
         for g in GR`modaut do
          lift, newgenims := AutExtensionH(GR,oim[i],g*iso,level);
          if lift then
            genims:=newgenims;
            iso := g*iso;
            break;
          end if;
         end for;
        end if;
        if not lift then allfix:=false; break; end if;
      end if;
    else
      allfix:=false; break;
    end if;
    for j in [1..dm] do
      w:=Id(F);
      for k in [1..dm] do
        w := w * (F.(nfg+k))^(Z!iso[j][k]);
      end for;
      Append(~genims,w);
    end for;
    Append(~GR`outimages,genims);
    nliftgens +:= 1;
  end for;
  if allfix then
    if GR`printlevel gt 1 then
      print "  +All outer automorphisms fix the module and lift.";
    end if;
    if not liftHtoG then
      if GR`printlevel gt 0 then
        print "Isomorphism does not lift.";
      end if;
      isomims:=[];
      return;
    end if;
    GR`liftoutaut := GR`outerautgroup;
    GR`orderliftoutaut := GR`orderouterautgroup;
  else
    if GR`printlevel gt 1 and #modaut lt GR`smallmodaut then
      print "  +Not all outer automorphisms fix the module and lift.";
    end if;
  /* Now form an appropriate permutation representation of the
   * old outer automorphism group.
   */
    if liftHtoG then
      PermRepOutAutGpH(~HR,~GR,level,[]);
    else
      PermRepOutAutGpH(~HR,~GR,level,isomims);
    end if;
    oldoutgp := Image(GR`holmap);
    subooggens := [ (GR`holgens)[i] : i in [1..nliftgens] ];
    if liftHtoG then
      emptylist:=[];
      FindLiftingIsomH(~HR,~GR,level,oldoutgp,subooggens,~emptylist);
    else
      // still looking for a lifting isomorphism.
      FindLiftingIsomH(~HR,~GR,level,oldoutgp,subooggens,~isomims);
    end if;
  end if;

end procedure;

IdentifyDerivationH := function(GR,aut,level)
/* aut should be an automorphism of G (mod subseries[level+1]) that induces
 * the identity on G/subseries[level]. The vector of coefficients of the
 * derivation as an element of GR`derspace[level] (which should have been
 * calculated by now) is returned.
 */

 local G, m, dm, V, W, ng, vec, newgens; 

  if Dimension(GR`derspace[level]) eq 0 then
    return [];
  end if;
  G := GR`newgroup;
  newgens := GR`newgens;
  m := GR`layermod[level];
  prime := #BaseRing(m);
  dm := Dimension(m);
  ng := GR`quotgens[level];
  V := VectorSpace(GF(prime),ng*dm);
  vec:=[];
  for i in [1..ng] do
    v := newgens[i]^-1 * aut(newgens[i]);
    if not v in GR`subseries[level] then
      error "Error in IdentifyDerivationH - not a derivation";
    end if;
    vec := vec cat Eltseq(v @ GR`layermap[level]);
  end for;
  vec := V!vec;
  return Coordinates(GR`derspace[level],vec);
end function;

IdentifyInnerAutH := function(GR,aut,level)
/* aut should be an inner automorphism of G (mod subseries[level+1]).
 * An element of g inducing aut by conjugation is found.
 */
 local Z, G, caut, el, rq, rm, C, im, conj, g, vec, id, m, dm, lm, prime, gl,
       rep, cautmat, ngg, ivwm, w, model, grima, newgens;

  Z := Integers();
  caut:=aut;
  G:=GR`newgroup;
  newgens := GR`newgens;

  if GR`radindex eq 1 then
    el := Id(G);
  else
    /* identify aut in radical quotient */
    rq:=GR`radquot;
    rm:=GR`radmap;
    el:=Id(rq);
    C :=rq;
    for i in [1..Ngens(rq)] do
      im := (newgens[i] @ aut) @ rm; // of course newgens[i] @ rm = rq.i
      conj, g := IsConjugate(C,rq.i,el*im*el^-1);
      if not conj then
        error "Error in IdentifyInnerAutH - aut mod radquot not inner";
      end if;
      el := g*el;
      if i lt Ngens(rq) then
        C := Centraliser(rq,sub<rq | [rq.j : j in [1..i] ] >);
      end if;
    end for;
    el := el@@rm;
  end if;
 
  for lev in [1..level] do
    caut := hom<G->G |
           [newgens[j]->(el*newgens[j]*el^-1)@aut : j in [1..#newgens] ] :
                            Check := false >;
    if lev gt 1 then
       // we need to identify the inner module automorphism induced by caut.
      ngg := GR`quotgens[lev];
      m := GR`layermod[lev];
      lm := GR`layermap[lev];
      prime := #BaseRing(m);
      dm := Dimension(m);
      gl:=GL(dm,prime);
      cautmat:=[];
      for i in [1..dm] do
        cautmat := cautmat cat ElementToSequence((newgens[ngg+i]@caut) @ lm);
      end for;
      cautmat := gl!cautmat;
      if cautmat ne Id(gl) then
        rep:=Representation(m);
        grima := GR`innermodaut[lev];
        repim := sub< gl | [x@rep : x in grima] >;
        if not cautmat in repim then
          error "At level",lev,"automorphism is not inner";
        end if;
        if Ngens(repim) ne #grima then
          error "Wrong number of generators of matrix group.";
        end if;
        ivwm := InverseWordMap(repim);
        w := cautmat@ivwm;
        el *:= Evaluate(w, grima);
        caut := hom<G->G |
            [newgens[j]->(el*newgens[j]*el^-1)@aut : j in [1..#newgens] ] :
                            Check:=false >;
      end if;
    end if;
    vec := IdentifyDerivationH(GR,caut,lev);
    id := GR`innerder[lev];
    for j in [1..#vec] do
      if vec[j] ne 0 then
        if j gt #id then
            error "Error in IdentifyInnerAutH - aut at level",lev," not inner";
        end if;
        el := el * id[j]^(Z!vec[j]);
      end if;
    end for;
  end for;

  return el;
end function;

CalculateAutPresH := procedure(~GR,level)
/* Calculate presentation of automorphism group of G modulo subseries[level+1]
 */
local Z, G, ngg,  F, ng, goa, ngoa, FA, FOA, FtoFA, FArels, FOArels, newgens,
      noder, ider, nider, prime, m, dm, rm, lm, aut, newaut,  vec, el, rel,
      ngrma, matoFA, mat, mats,
      ma, nima, imawds, w, gl, nggl, gltoFA, gltoFOA, FAtoFOA, g, ig,
      modautterm;

  if GR`printlevel gt 1 then
    print "  +Computing presentation of automorphism group at level",level;
  end if;
  Z := Integers();
  G := GR`newgroup;
  newgens := GR`newgens;
  ngg := #newgens;
  F := GR`fpgroup;
  ng := Ngens(F);
  /* How many generators do we need for automorphism group? */
  goa := GR`outimages;
  ngoa := #goa;
  nga := ng + ngoa;
  FA := FreeGroup(nga);
  if ngoa eq 0 then
    FOA := Group<x|x>;
  else
    FOA := FreeGroup(ngoa);
  end if;
  FtoFA := hom<F->FA |  [FA.i : i in [1..ng] ]>;
  FArels := [ LHS(r)@FtoFA = RHS(r)@FtoFA : r in Relations(F) ];
  /* Adjoin any central generators from F */
  if #(GR`centre@GR`fptoperm) gt 1 then
    FArels := FArels cat [ x@FtoFA = Id(FA) : x in Generators(GR`centre) ];
  end if;

  /* First we want the action of outer automorphisms on G */
  if GR`printlevel gt 2 then
    print "    +Relations for outer automorphisms on group";
  end if;
  for i in [1..ngoa] do for j in [1..ng] do
    /* Action of i-th outer aut on j-th gen. of G */
    Append(~FArels,FA.(ng+i)^-1*FA.j*FA.(ng+i) = goa[i][j]@FtoFA);
  end for; end for;

  /* Next adjoin elementary abelian relations for derivations */
  m := GR`layermod[level];
  lm := GR`layermap[level];
  prime := #BaseRing(m);
  dm := Dimension(m);
  ider := GR`innerder[level];
  nider := #ider;
  noder := Dimension(GR`derspace[level]) - nider;
  if GR`printlevel gt 2 then
    print "    +Elementary abelian relations for derivations";
  end if;
  if noder gt 0 then
    FArels := FArels cat [ (FA.(ng+i))^prime = Id(FA) : i in [1..noder] ];
    FArels := FArels cat [  FA.(ng+i) * FA.(ng+j) =  FA.(ng+j) * FA.(ng+i) :
                            i in [1..noder], j in [1..noder] | i lt j ];
  
    GR`orderouterautgroup := prime^noder;
  /* Now the action of the other generators on these */
    if GR`printlevel gt 2 then
      print "    +Action of other automorphisms on derivations";
    end if;
    for i in [noder+1..ngoa] do for j in [1..noder] do
      /* Calculate action of i-th out-gen on j-th - set up as auto of G */
      aut := CalculateIsomH(GR,[-i,j,i]);
      vec := IdentifyDerivationH(GR,aut,level);
      el := Id(G);
      for k in [1..nider] do     
        el := el * ider[k]^(Z!vec[k]);
      end for; // el is the inner automorphism component
      w := InverseImageGRH(GR,el,level) @ FtoFA;
      for k in [1..noder] do
        w := w * FA.(ng+k)^(Z!vec[nider+k]);
      end for;
      Append(~FArels,FA.(ng+i)^-1 * FA.(ng+j) * FA.(ng+i) = w); 
    end for; end for;
  else GR`orderouterautgroup := 1;
  end if;
  
  /* In the split case, we adjoin presentation of module aut group */
  if GR`split and  #GR`modaut gt 1 then
    if GR`printlevel gt 2 then
      print "    +Relations of module automorphism group";
    end if;
    /* First identify the words in FA corresponding to inner mod auts */
    nima := #GR`innermodaut[level];
    ma := GR`modaut;
    imawds := [];
    for g in GR`innermodaut[level] do
      Append(~imawds,InverseImageGRH(GR,g,level)@FtoFA);
    end for;
    ngrma := Ngens(ma) - nima;
    matoFA := hom<GR`mapres->FA |
                          imawds cat [FA.(ng+noder+i) : i in [1..ngrma] ]>;
    FArels := FArels cat
                [ LHS(r)@matoFA = RHS(r)@matoFA : r in Relations(GR`mapres)];
    GR`orderouterautgroup *:= Index(ma,sub<ma|[ma.i:i in [1..nima] ]>);
    /* And we want the action of other generators on the module auts. */
    if GR`printlevel gt 2 then
      print "    +Action of other automorphisms on module automorphisms";
    end if;
    for i in [noder+ngrma+1..ngoa] do for j in [noder+1..noder+ngrma] do
      /* Calculate action of i-th out-gen on j-th - set up as auto of G */
      aut := CalculateIsomH(GR,[-i,j,i]); /* now we want the matrix action */
      mat := [];
      for k in [1..dm] do
        mat := mat cat Eltseq((m.k)@@lm @ aut @lm);
      end for;
      mat := ma!mat;
      w := mat @ GR`rmamap @@ GR`mapresmap;
      Append(~FArels,FA.(ng+i)^-1 * FA.(ng+j) * FA.(ng+i) = w@matoFA); 
    end for; end for;
  else
    nima:=0; ngrma:=0;
  end if;

  /* Finally we have to deal with the outer auts at the previous layer */
  if GR`printlevel gt 2 then
    print "    +Values of lifted outer automorphisms from previous layer";
  end if;
  gl := GR`liftoutaut;
  if GR`orderliftoutaut gt 1 then
    nggl := Ngens(gl);
    gltoFA := hom<gl->FA | [FA.(ng+noder+ngrma+i) : i in [1..nggl] ]>;
    gltoFOA := hom<gl->FOA | [FOA.(noder+ngrma+i) : i in [1..nggl] ]>;
    for r in Relations(gl) do
      rel := LHS(r)*RHS(r)^-1;
      aut := CalculateIsomH(GR,rel@gltoFOA);
      g:=IdentifyInnerAutH(GR,aut,level-1);
      ig := InverseImageGRH(GR,g,level);
      if GR`split and nima + ngrma gt 0 then
        /* relation g^-1 * aut could evaluate to a mod aut */
        mat := [];
        for k in [1..dm] do
          mat := mat cat Eltseq((g * (m.k)@@lm * g^-1) @ aut @ lm);
        end for;
        mat := ma!mat;
        w := mat @ GR`rmamap @@ GR`mapresmap;
        modautterm := w@matoFA;
      else
        modautterm := Id(FA);
      end if;
      
      /* relation g^-1 * aut could evaluate to a derivation */
      newaut := hom<G->G |
           [newgens[i]->(g * newgens[i] * g^-1)@aut : i in [1..ngg] ] :
                            Check := false >;
      vec := IdentifyDerivationH(GR,newaut,level);
      el := Id(G);
      for k in [1..nider] do
        el := el * ider[k]^(Z!vec[k]);
      end for; // el is the inner automorphism component
      w := InverseImageGRH(GR,el,level) @ FtoFA;
      for k in [1..noder] do
        w := w * FA.(ng+k)^(Z!vec[nider+k]);
      end for;
      Append(~FArels,rel@gltoFA = ig@FtoFA * modautterm * w);
    end for;
    GR`orderouterautgroup *:= GR`orderliftoutaut;
  end if;
  GR`orderautgroup := GR`orderouterautgroup *
                  Index(G,sub<G|GR`subseries[level+1],GR`centre@GR`fptoperm>);
  
  delete GR`autgroup;
  delete GR`outerautgroup;
  delete GR`auttoouter;
  GR`autgroup := quo<FA | FArels >;
  if ngoa ne 0 then
    FAtoFOA := hom<FA->FOA |
                   [Id(FOA) : i in [1..ng]] cat [FOA.i : i in [1..ngoa]] >;
    FOArels:=[LHS(r)@FAtoFOA = RHS(r)@FAtoFOA : r in FArels];
    GR`outerautgroup := quo<FOA | FOArels >;
    FOA := GR`outerautgroup;
    GR`auttoouter :=  hom<GR`autgroup->FOA |
                   [Id(FOA) : i in [1..ng]] cat [FOA.i : i in [1..ngoa]] >;
  else
    GR`outerautgroup := FOA;
    GR`auttoouter :=  hom<GR`autgroup->FOA | [Id(FOA) : i in [1..ng]] >;
  end if;
  GR`fptoaut := hom<F->GR`autgroup | [(GR`autgroup).i : i in [1..ng]] >;
end procedure;
