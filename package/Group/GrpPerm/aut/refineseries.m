freeze;


import "oddfns.m":  CalculateOuterAutsH;
import "oddfns.m":  ElementaryAbelianPresentation;

DefineGroupGensH := procedure(~GR,outerauts)
/* Put the layermod generators into GR`newgens.
 */
  local ng, newgens, level, m, nmg, G, i, gotinv, iso, isoi;

  ng := GR`quotgens[1];
  newgens:= GR`newgens;

  for level in [1..GR`length] do
    m := GR`layermod[level];
    nmg := Dimension(m);
    newgens := newgens cat [(m.i) @@ GR`layermap[level] : i in [1..nmg] ];
    Append(~GR`quotgens,#newgens);
  end for;
  GR`newgens := newgens;
  GR`newgroup := sub<GR`permgroup | newgens >;

  if ng ne 0 then
    G := GR`permgroup;
    GR`fptoperm := hom<GR`fpgroup -> GR`permgroup |
                                          [newgens[i] : i in [1..ng]] >;
  /* At this stage, we can initialise GR`autautos on the radical quotient */
    if outerauts then
      CalculateOuterAutsH(~GR,0);
    end if;
  end if;
end procedure;

FrattiniSubmoduleH := function(G,M,N,F,proj,printlevel)
/* M/N should be an elementary abelian section of a permutation group G,
 * such that the module M/N is semisimple.
 * The intersection of M/N with the Fitting subgroup of G/N is computed
 * and its inverse image in G returned.
 * F should be a finitely presented group, and proj a map F->G that
 * induces an isomorphism F -> G/M.
 */
  
  local m, phi, cm, l, L, rm, fm, dm, nfg, rv, rels, w, v, gl, gens, projgl,
        Z, nglg, split, comps,  comp, vec, mgens, newG, newM, newproj;

  Z := Integers();
  m, phi := GModule(G,M,N);
  if Socle(m) ne m then
    error "Error in FrattiniSubmoduleH: module is not semisimple";
  end if;
  /* Find a minimal submodule of m */
  cm := CompositionSeries(m);
  l := cm[1];
  L := l @@ phi;
  if printlevel gt 2 then
    print "      +Submodule of order",#L/#N,",in section of order",#M/#N;
  end if;

  nfg := Ngens(F);
  if M eq L then
    gl := F;
    projgl := proj;
  else
  /* Next set up G/L as an fp-group */
    m, phi := GModule(G,M,L);
    rm := Representation(m);
    dm := Dimension(m);
    fm := GModule(F,[F.i @ proj @ rm : i in [1..nfg] ]);
    /* calculate values of relations of F in fm */
    rv := [];
    rels := Relations(F);
    for rel in rels do
      w := LHS(rel)*RHS(rel)^-1;
      v := fm!Eltseq(w @ proj @ phi);
      Append(~rv,v);
    end for;
    gl := ModuleExtension(fm,rv); // fp-group for G/L
    /* define the map onto G defining isomorphism onto G/L */
    gens := [ F.i @ proj : i in [1..nfg] ] cat [ m.i @@ phi : i in [1..dm] ];
    projgl := hom< gl -> G | gens >;
  end if;

  /* Next set up L/N as gl module */
  m, phi := GModule(G,L,N);
  rm := Representation(m);
  dm := Dimension(m);
  nglg := Ngens(gl);
  fm := GModule(gl,[gl.i @ projgl @ rm : i in [1..nglg] ]);
  /* calculate values of relations of gl in fm */
  rv := [];
  rels := Relations(gl);
  for rel in rels do
    w := LHS(rel)*RHS(rel)^-1;
    v := fm!Eltseq(w @ projgl @ phi);
    Append(~rv,v);
  end for;
  split, comps := ComplementVectors(fm,rv);
  if split then
    if printlevel gt 1 then
      print "  +Split extension";
    end if;
    if M eq L then
      return N;
    end if;
    /* L is not in the Frattini subgroup - find a complement to L/N in
     * G/N and apply the procedure recursively to it.
     */
    gens := [gl.i @ projgl : i in [1..nglg] ];
    mgens := [m.i @@ phi : i in [1..dm] ];
    comp := comps[1];
    for gen in [1..nglg] do
     /* multiply this generator by the necessary tail in comp */
      vec := comp[gen];
      for i in [1..dm] do
        gens[gen] := gens[gen] * mgens[i]^(Z!vec[i]);
      end for;
    end for;
    newG := sub<G | gens, N >;
    newM := sub<G | [gens[i] : i in [nfg+1..nglg]], N >;
    newproj := hom<F->newG | [gens[i] : i in [1..nfg]] >;
    return $$(newG,newM,N,F,newproj,printlevel);
  else
    if printlevel gt 2 then
      print "      +Nonsplit extension";
    end if;
    /* L is in the Frattini subgroup */
    if M eq L then
      return M;
    end if;
    return $$(G,M,L,F,proj,printlevel);
  end if;

end function;

RefineSeriesH := procedure(~GR,level,subgp)
/* Insert subgp into the submormal series as GR`subseries[level+1]
 */
 local newgens, m, nmg;

/* first check that subgp has the necessary inclusion properties */
  if not IsNormal(GR`permgroup,subgp) or not subgp subset GR`subseries[level]
     or not GR`subseries[level+1] subset subgp or subgp eq GR`subseries[level]
     or subgp eq GR`subseries[level+1] then
    error "Third argument in RefineSeriesH is invalid";
  end if; 

  if GR`printlevel gt 1 then
      print "Refining series.";
  end if;

  for i in Reverse([level+1 .. GR`length+1]) do
    GR`subseries[i+1] := GR`subseries[i];
  end for;
  GR`subseries[level+1] := subgp;

  for i in Reverse([level+1 .. GR`length]) do
    GR`layermod[i+1] := GR`layermod[i];
  end for;
  for i in Reverse([level+1 .. GR`length]) do
    GR`layermap[i+1] := GR`layermap[i];
  end for;
  for i in [level..level+1] do
    GR`layermod[i], GR`layermap[i] :=
      GModule(GR`permgroup,GR`subseries[i],GR`subseries[i+1]);
  end for;

  for i in Reverse([level+1 .. GR`length]) do
    GR`index[i+1] := GR`index[i];
  end for;
  for i in [level..level+1] do
    GR`index[i]:= #GR`subseries[i]/#GR`subseries[i+1];
  end for;

  for i in Reverse([level+1 .. GR`length+1]) do
    GR`quotgens[i+1] := GR`quotgens[i];
  end for;
  GR`quotgens[level+1] -:= Dimension(GR`layermod[level+1]);

  newgens:= [ GR`newgens[i] : i in [1..GR`quotgens[level]] ];

  GR`length +:= 1;
  for i in [level..GR`length] do
    m := GR`layermod[i];
    nmg := Dimension(m);
    newgens := newgens cat [(m.j) @@ GR`layermap[i] : j in [1..nmg] ];
  end for;
  GR`newgens := newgens;
  GR`newgroup := sub<GR`permgroup | newgens >;
  GR`fptoperm := hom<GR`fpgroup->GR`permgroup |
                   [newgens[i] : i in [1..Ngens(GR`fpgroup)] ] >;
  if GR`printlevel gt 0 then
      print "Indices of descending elementary subgroup chain: ", GR`index;
  end if;

end procedure;

DoesLayerSplitH := procedure(~GR,level,~refine)
/* Decide whether the extension of subseries[level]/subseries[level+1] by
 * G/subseries[level] (G = GR`permgroup) splits.
 * If so, then change generators of G to include generators of a complement
 * mod subseries[level+1].
 * If not, then first refine to semisimple modules, and then to
 * Frattini extension.
 */
  local Z, F, G, m, dm, ngg, nfg, rels, rel, rv, w, v, allzero, split, comps,
        comp, gens, gen, vec, soc, fsm, newgens;

  Z:=Integers();
  G := GR`permgroup;
  newgens := GR`newgens;
  ngg := #newgens;
  m := GR`layermod[level];
  dm := Dimension(m);
  prime := #BaseRing(m);
  if  GR`quotgens[level] eq 0 then // only possible if level=1
    if GR`printlevel gt 1 then
      print "  +Top level splits (trivial radical quotient).";
    end if;
    GR`fpgroup := ElementaryAbelianPresentation(prime,dm);
    F := GR`fpgroup;
    GR`fptoperm := hom< F->G | [newgens[i] : i in [1..dm]] >;
    GR`split:=true;
    refine:=false;
    return;
  end if;

  /* Decide whether G = GR`permgroup splits over layermod[level].
   * If so, change generators GR`newgens to include complement generators.
   */
  F := GR`fpgroup;
  nfg := Ngens(F);
  /* First we must construct an F-module equivalent to m */
  rm := Representation(m);
  fm := GModule(F,[newgens[i] @ rm : i in [1..nfg] ]);

  /* Now calculate values of relations of F in fm */
  rv := [];
  rels := Relations(F);
  allzero := true;
  for rel in rels do
    w := LHS(rel)*RHS(rel)^-1;
    v := fm!Eltseq(w@GR`fptoperm@GR`layermap[level]);
    if v ne fm!0 then allzero:=false; end if;
    Append(~rv,v);
  end for;
  if allzero then
    if GR`printlevel gt 1 then
      print "  +Extension splits with no generator change at level",level;
    end if;
    split := true;
  else
    split, comps := ComplementVectors(fm,rv);
    if split then
      /* We want to replace generators of G by complement generators */
      if GR`printlevel gt 1 then
        print "  +Extension splits with change of generators at level",level;
      end if;
      gens := [newgens[i] : i in [1..ngg] ];
      comp := comps[1];
      for gen in [1..nfg] do
       /* multiply this generator by the necessary tail in comp */
        vec := comp[gen];
        for i in [1..dm] do
          gens[gen] := gens[gen] * gens[nfg+i]^(Z!vec[i]);
        end for;
      end for;
      for i in [1..#rv] do
        rv[i] := fm!0;
      end for;
      GR`newgens := gens;
      GR`newgroup := sub<GR`permgroup | gens >;
    else
      if GR`printlevel gt 1 then
        print "  +Extension does not split at level",level;
      end if;
      /* If module is not semisimple, then refine by introducing socle into
       * series. */
      soc:=Socle(m);
      if soc ne m then
        RefineSeriesH(~GR,level,soc @@ GR`layermap[level]);
        refine:=true;
        return;
      end if;
      /* Now if module is not in Frattini subgroup, introduce this subgroup
       * into series.
       */
      fsm := FrattiniSubmoduleH(GR`permgroup,GR`subseries[level],
                GR`subseries[level+1],GR`fpgroup,GR`fptoperm,GR`printlevel);
      if fsm ne GR`subseries[level] then
        RefineSeriesH(~GR,level,fsm);
        refine:=true;
        return;
      end if;
    end if;
  end if;

  GR`split:=split;
  refine:=false;
  GR`relvals:=rv;
  GR`cem:=ComplementEquationsMatrix(fm);
  GR`oldfpgroup := GR`fpgroup;
  GR`oldfptoperm := GR`fptoperm;
  GR`fpgroup := ModuleExtension(fm,rv);
  GR`fptoperm := hom< GR`fpgroup->G | [GR`newgens[i] : i in [1..nfg+dm]] >;

end procedure;

CharRefineSeriesH := procedure(~GR,subgp)
/* subgp should be a characteristic subgroup of GR`permgroup.
 * This function attempts to refine the series of subgroups
 * by using the images of subgp wherever possible.
 */
local  changed, G, H, series;
  G := GR`permgroup;
  series := GR`subseries;
  ind := GR`length;
  changed:=false;
  while ind gt 0 do
    H := sub< G | series[ind+1], subgp> meet series[ind];
    if series[ind+1] ne H and series[ind] ne H then
      changed := true;
      GR`length +:= 1;
      for i in Reverse([ind+1..GR`length]) do
        GR`subseries[i+1] := GR`subseries[i];
      end for;
      GR`subseries[ind+1] := H;
    end if;
    ind -:= 1;
  end while;
  if changed and GR`printlevel gt 2 then
    print "    +Refined Series using characteristic subgroup";
  end if;
end procedure;
