freeze;

TidyUpH := procedure(~GR)
  //Clear up redundant data at end of level
  delete GR`newgpholpt;
  delete GR`gpholpt;
  delete GR`holword;
  delete GR`holperm;
  delete GR`holmap;
  delete GR`holgens;
  delete GR`liftoutaut;
  delete GR`orderliftoutaut;
  delete GR`rmamap;
  delete GR`mapresmap;
  delete GR`mapres;
  delete GR`modaut;
  delete GR`cem;
  delete GR`relvals;
  delete GR`oldfpgroup;
  delete GR`oldfptoperm;
  delete GR`oldoutimages;
end procedure;

FinalTidyUpH := procedure(~GR)
  //Clear up redundant data at end of run.
  delete GR`oldfpgroup;
  delete GR`oldfptoperm;
  delete GR`oldoutimages;
  delete GR`innerder;
  delete GR`derspace;
  delete GR`innermodaut;
end procedure;

CalculateOuterAutsH := procedure(~GR,level)
/* Calculate outer automorphisms as automorphisms of G (modulo
 * subseries[level+1]). The list is twice as long as #GR`outimages,
 * and the corresponding outer automorphisms are followed by the list
 * of their inverses.
 */
  local G, ng, ngg, gotinv, iso, isoi, order, ims, GI, newgens;

  if GR`printlevel gt 1 then
    print "  +Computing automorphism actions on current quotient.";
  end if;
  G:=GR`newgroup;
  newgens := GR`newgens;
  ngg := #newgens;
  ng := GR`quotgens[level+1];
  GR`outautos := [**];
  if #GR`outimages ne 0 then
    for oi in GR`outimages do
      iso := hom< G->G |
             [newgens[i]->oi[i]@GR`fptoperm : i in [1..#oi]] cat
             [newgens[i]->newgens[i] : i in [ng+1..ngg]]: Check:=false >;
      Append(~GR`outautos,iso);
    end for;
    /* and append their inverses */
    for oi in GR`outimages do
      ims := [im@GR`fptoperm : im in oi] cat [newgens[i] : i in [ng+1..ngg]];
      iso := hom< G->G |
               [newgens[i]->ims[i] : i in [1..#ims]] : Check:=false >;
      if GR`printlevel gt 2 then
         print "    +Computed action of an outer automorphism.";
      end if;
      isoi := iso;
/*
      order:=2;
      while not gotinv do
        gotinv:=true;
        for g in Generators(G) do
          if not g^-1 * (g @ isoi @ iso) in GR`subseries[level+1] then
            gotinv:=false; isoi := isoi*iso;
            order+:=1;
            break;
          end if;
        end for;
      end while;
That can be slow - try something different.
*/
      GI := sub< G | ims >; 
      isoi := hom< GI->G |
                  [ims[i]->newgens[i] : i in [1..#newgens]] : Check:=false >;
      isoi := hom< G->G |
                  [newgens[i]->newgens[i] @ isoi : i in [1..#newgens]] :
                                                            Check:=false >;
      if GR`printlevel gt 2 then
        //print "    +Computed action of its inverse. Order = ",order;
        print "    +Computed action of its inverse.";
      end if;
      Append(~GR`outautos,isoi);
    end for;
  end if;
end procedure;

CalculateOldIsomH:=function(GR,w)
  /* w should be a nontrivial word in the (old) outer automorphism generators.
   * Calculate and return the corresponding isomorphism of
   * GR`permgroup (modulo subseries[level] of course).
   */
  local sw, auts, aut, noi;
  if #w eq 0 then
    return IdentityHomomorphism(GR`permgroup);
  end if;
  auts := GR`outautos;
  noi := #GR`oldoutimages;
  sw := ElementToSequence(w);
  /* Inverses in auts come at the end, so change numbering in sw */
  for i in [1..#sw] do
    if sw[i] lt 0 then
      sw[i] := noi-sw[i];
    end if;
  end for;
  aut := auts[sw[1]];
  for i in [2..#sw] do
    aut := aut*auts[sw[i]];
  end for;
  return aut;
end function;

IsIsomModH := function(GR,ims,level)
  /* ims should be the images of the generators of GR`permgroup
   * under an isomorphism iso of G=GR`permgroup modulo subseries[level].
   * Decide whether the G-module layermod[level] is isomorphic to the
   * induced module layermod[level]^(iso^-1), and if so return an isomorphism.
   */
  local  G, ng, m1, mats, rm1, m2, isiso, iso;
  G := GR`permgroup;
  ng := Ngens(G);
  m1 := GR`layermod[level];
  rm1 := Representation(m1);
  mats := [ ims[i] @ rm1 : i in [1..ng] ];
  m2 := GModule(G,mats);
  /* m2 is actually m1^(iso^-1). */
  isiso, iso := IsIsomorphic(m1,m2);
  if isiso then
    return isiso, iso;
  end if;
  return isiso, 0;

end function;

IsIsomHtoGModH := function(HR,GR,ims,level)
  /* ims should be the images of the generators of GR`permgroup
   * under an isomorphism iso of G=GR`permgroup modulo subseries[level].
   * Decide whether the G-module layermod[level] is isomorphic to the
   * induced module layermod[level]^(iso^-1), and if so return an isomorphism.
   */
  local  G, H, ngH, mG1, mH1, mats, rmG1, mH2, isiso, iso;
  G := GR`permgroup;
  H := HR`permgroup;
  ngH := Ngens(H);
  mG1 := GR`layermod[level];
  rmG1 := Representation(mG1);
  mH1 := HR`layermod[level];
  mats := [ ims[i] @ rmG1 : i in [1..ngH] ];
  mH2 := GModule(H,mats);
  /* mH2 is actually mH1^(iso^-1). */
  isiso, iso := IsIsomorphic(mH1,mH2);
  if isiso then
    return isiso, iso;
  end if;
  return isiso, 0;

end function;

RadQuotWord := function(GR,x)
/* x is an element in G=GR`permgroup.
 * A word in GR`rqwordgp for the image of x in the radical quotient of G 
 * is returned.
 * Much of code is similar to PresentationSubgroupTF.
 */
  local genlist, projlist, fplist, r, subgpptr, dn, RQ, F, word, y, w,
        di;

  genlist:=GR`rqgenlist;
  projlist:=GR`rqprojlist;
  fplist:=GR`rqfplist;
  r := #genlist-1;
  subgpptr:=[];
  subgpptr[1]:=0;
  for i in [2..r+1] do
    subgpptr[i] := subgpptr[i-1] + #genlist[i-1];
  end for;
  dn:=subgpptr[r+1];

  RQ := GR`radquot;
  F := GR`rqwordgp;
  word := Id(F);
  x := x @ GR`radmap;
  y := x @ GR`rqsocmap;
  if y ne Id(Parent(y)) then
    w := ElementToSequence(y @@ GR`rqsqwordmap);
    for j in w do
      if j gt 0 then
        word := word * F.(dn+j);
        x := (RQ.(dn+j))^-1 * x;
      else
        word := word * (F.(dn-j)^-1);
        x := RQ.(dn-j) * x;
      end if;
    end for;
  end if;

  for i in [1..r] do
    di := subgpptr[i];
    w := ElementToSequence(x @ projlist[i] @@ fplist[i]);
    for j in w do
      if j gt 0 then
        word := word * F.(di+j);
      else
        word := word * (F.(di-j))^-1;
      end if;
    end for;
  end for;

  return word;
end function;

InverseImageGRH := function(GR,x,level)
/* GR should be an AutRF record to which ExtendAuts has been applied (or
 * is being applied) to level at least level.
 * x should be an element in GR`permgroup, and the invese image
 * in GR`fpgroup (down to level level) is returned.
 */

  local  F, word, suffix, wgtoF, i, j, v, d, ngp;

  if not x in GR`permgroup then
    error "Second argument to InverseImageGRH should be in GR'permgroup";
  end if;

  Z := Integers();
  F := GR`fpgroup;
  word := Id(F);
  oldx := x;
  if not x in GR`subseries[1] then
    wgtoF := hom< GR`rqwordgp->F | [F.i : i in [1..GR`quotgens[1] ]] >;
    word := word * wgtoF(RadQuotWord(GR,x));
    x := (word@GR`fptoperm)^-1 * x;
  end if;
  for i in [1..level] do
    if not x in GR`subseries[i+1] then
      suffix:=Id(F);
      v := x @ GR`layermap[i];
      d := Dimension(GR`layermod[i]);
      ngp := GR`quotgens[i];
      for j in [1..d] do
        suffix := suffix*F.(ngp+j)^(Z!v[j]);
      end for;
      x := (suffix@GR`fptoperm)^-1 * x;
      word := word*suffix;
    end if;
  end for;

  return word;
end function;

AutExtensionH := function(GR,autims,modmap,level)
/* Decide whether the automorphism of GR`oldfpgroup of which the generator
 * images are given by autims together with the map of the layermod[level]
 * specified by the matrix modmap lift to an automorphism of GR`fpgroup.
 * Return true or false accordingly and, if true, return the generator
 * images of the extension.
 */
local F, Fisom, m, dm, V, W, ng, nr, w, rels, rel, relim, x, rv, cons,
      newF, lifthom, liftautims, Z, word;

  F:=GR`oldfpgroup;
  Fisom := hom<F->F|autims>;
  ng := Ngens(F);
  nr := #Relations(F);
  m := GR`layermod[level];
  prime := #BaseRing(m);
  dm := Dimension(m);
  V := VectorSpace(GF(prime),nr*dm);
  /* We try and find vectors v_i of m such that the map F.iv_i -> autims[i]
   * is the required lift of Fisom.
   * This reduces to solving a system of equations of form
   * x*cem = w, where cem is the complement equations matrix of the
   * extension (which we already know), x (the unknown) is the row of
   * v_i's and w is a nr*dm vector to be computed.
   */
  w:=V!0;
  rels := Relations(F);
  rv := GR`relvals;
  for i in [1..nr] do
    /* We need to work out what value rel@Fisom takes in the module
     * when evaluated modulo subseries[level+1].
     */
      // image in GR`permgroup - should be in subseries[level]
    rel := LHS(rels[i])*RHS(rels[i])^-1;
    relim:= rel @ Fisom @ GR`oldfptoperm @ GR`layermap[level];
    /* To get the correct entries in w, we apply inverse of modmap to w,
     * and subtract the relvals for this relation.
     */
    relim := relim * modmap^-1;
    for j in [1..dm] do
      w[(i-1)*dm+j] := relim[j] - rv[i][j];
    end for;
  end for;
  /* Now see if there is a solution */
  cons, x := IsConsistent(GR`cem,w);
  if not cons then
    return false, [];
  end if;
  /* There is a solution. It is F.i -> autims[i].(-v_i)*modmap,
   * so we need to replace the v_i by (-v_i)*modmap.
   */
  liftautims:=[];
  newF := GR`fpgroup;
  lifthom := hom<F->newF | [newF.i : i in [1..ng]] >;
  V:=VectorSpace(GF(prime),dm);
  Z:=Integers();
  for i in [1..ng] do
    word := autims[i]@lifthom;
    w := V![x[j]: j in [(i-1)*dm+1..i*dm] ];
    w := -w*modmap;
    for j in [1..dm] do
      word := word * (newF.(ng+j))^(Z!w[j]);
    end for;
    Append(~liftautims,word);
  end for;
  return true, liftautims;

end function;

IsomExtensionHtoGH := function(HR,GR,isomims,modmap,level)
/* Decide whether the isomorphism HR`oldfpgroup -> GR`oldfpgroup of which the
 * generator images are given by isomims together with the map of the
 * layermod[level] specified by the matrix modmap lift to an isomorphism 
 * HR`fpgroup -> GR`fpgroup.
 * Return true or false accordingly and, if true, return the generator
 * images of the extension.
 */
local FG, FH, Fisom, m, dm, V, W, ng, nr, w, rels, rel, relim, x, rvH,
      cons, newFG, lifthom, liftisomims, Z, word;

  FG:=GR`oldfpgroup;
  FH:=HR`oldfpgroup;
  Fisom := hom<FH->FG|isomims>;
  ng := Ngens(FH);
  nr := #Relations(FH);
  m := GR`layermod[level];
  prime := #BaseRing(m);
  dm := Dimension(m);
  V := VectorSpace(GF(prime),nr*dm);
  /* We try and find vectors v_i of m such that the map FH.iv_i -> isomims[i]
   * is the required lift of Fisom.
   * This reduces to solving a system of equations of form
   * x*cem = w, where cem is the complement equations matrix of the
   * extension (which we already know), x (the unknown) is the row of
   * v_i's and w is a nr*dm vector to be computed.
   */
  w:=V!0;
  rels := Relations(FH);
  rvH := HR`relvals;
  for i in [1..nr] do
    /* We need to work out what value rel@Fisom takes in the module
     * when evaluated modulo subseries[level+1].
     */
      // image in GR`permgroup - should be in subseries[level]
    rel := LHS(rels[i])*RHS(rels[i])^-1;
    relim:= rel @ Fisom @ GR`oldfptoperm @ GR`layermap[level];
    /* To get the correct entries in w, we apply inverse of modmap to w,
     * and subtract the relvals for this relation.
     */
    relim := relim * modmap^-1;
    for j in [1..dm] do
      w[(i-1)*dm+j] := relim[j] - rvH[i][j];
    end for;
  end for;
  /* Now see if there is a solution */
  cons, x := IsConsistent(HR`cem,w);
  if not cons then
    return false, [];
  end if;
  /* There is a solution. It is FH.i -> isomims[i].(-v_i)*modmap,
   * so we need to replace the v_i by (-v_i)*modmap.
   */
  liftisomims:=[];
  newFG := GR`fpgroup;
  lifthom := hom<FG->newFG | [newFG.i : i in [1..ng]] >;
  V:=VectorSpace(GF(prime),dm);
  Z:=Integers();
  for i in [1..ng] do
    w := V![x[j]: j in [(i-1)*dm+1..i*dm] ];
    w := -w*modmap;
    word := isomims[i]@lifthom;
    for j in [1..dm] do
      word := word * (newFG.(ng+j))^(Z!w[j]);
    end for;
    Append(~liftisomims,word);
  end for;
  return true, liftisomims;

end function;

CalculateIsomH:=function(GR,w)
  /* w should be a nontrivial word in the outer automorphism generators,
   * or a corresponding list of integers.
   * Calculate and return the corresponding isomorphism of
   * GR`permgroup (modulo subseries[level+1] of course).
   */
  local sw, auts, aut, noi;
  auts := GR`outautos;
  noi := #GR`outimages;
  sw := ElementToSequence(w);
  /* Inverses in auts come at the end, so change numbering in sw */
  for i in [1..#sw] do
    if sw[i] lt 0 then
      sw[i] := noi-sw[i];
    end if;
  end for;
  aut := auts[sw[1]];
  for i in [2..#sw] do
    aut := aut*auts[sw[i]];
  end for;
  return aut;
end function;

AGAutGroupToMap := function(GR,w)
/* GR should be an AutRF record output by AutGroup.
 * w should be an element in GR`autgroup.
 * The corresponding automorphism of GR`permgroup is returned.
 */

  local  fields, G, F, FtoG, ni, no, inners, outers, sw, swi, aswi, g,
         aut, caut;

  if Category(GR) ne Rec then
    error "Argument of AGAutGroupToMap must be an automorphism group record";
  end if;
  fields := Names(GR);
  if not "permgroup" in fields or not "autgroup" in fields then
    error "Argument of AGAutGroupToMap must be an automorphism group record";
  end if;

  if not w in GR`autgroup then
    error "Second argument to AGAutGroupToMap should be in GR`autgroup";
  end if;

  inners := []; // inner automorphisms to be calculated as needed.
  outers := GR`outautos;
  F := GR`fpgroup;
  ni := Ngens(F);
  FtoG := GR`fptoperm;
  G := GR`permgroup;
  no := #outers div 2;
  sw := ElementToSequence(w);

  if #sw eq 0 then
    return hom< G->G | x :-> x >;
  end if;

  for i in [1..#sw] do
    swi := sw[i];
    aswi := Abs(swi);
    if aswi le ni and not IsDefined(inners,aswi) then
      g := FtoG(F.aswi);
      inners[aswi] := hom< G->G | x :-> g^-1*x*g >;
      inners[aswi+ni] := hom< G->G | x :-> g*x*g^-1 >;
    end if;
    if aswi le ni then
      aut := swi gt 0 select inners[aswi] else inners[aswi+ni];
    else
      aut := swi gt 0 select outers[aswi-ni] else outers[aswi-ni+no];
    end if;
    caut := i eq 1 select aut else caut*aut;
  end for;

  return caut;
end function;

ElementaryAbelianPresentation := function(p,d)
/* This function simply returns the natural presentation of an elementary
 * abelian group of order p^d.
 */
 local i,j, F, RE;

  F := FreeGroup(d);
  RE := [];
  for i in [1..d] do
    Append(~RE,F.i^p=1);
  end for;
  for i in [1..d-1] do
    for j in [i+1..d] do
      Append(~RE,(F.i,F.j)=1);
    end for;
  end for;

  return quo <F|RE>;
end function;

