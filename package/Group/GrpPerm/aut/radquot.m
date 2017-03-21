freeze;

import "../max/identify.m":	IdentifyAlmostSimpleGroupH;
import "oddfns.m":		RadQuotWord;
import "../max/oddfns.m":	PresentationSubgroupTF;
import "../max/oddfns.m":	PermutationRepresentationSumH;

/* This file contains the procedures for identifying the radical
 * quotient of the group G (=GR`permgroup) and finding a map from the
 * in the database to the radical quotient of G.
 *
 * Each perfect group RG  in the almost simpel groups database  is defined by
*  two generators,  x  and  y  with orders ox and oy, say.
 * (x and y  are actually defined as generators of a free group of rank 2.)
 * x is always chosen so that there is a unique Aut(RG)-class of elements
 * of order ox in RG.
 *
 * The list returned for G is a record with the following fields:
 * name - a string, describing the group G.
 * resname - a string, describing the soluble residual RG of the group.
 * ox - the order of x,
 * oy - the order of y,
 * geninfo - a list of length two, the elements are 3-tuples
 *           giving order of element (i.e. ox or oy), length of
 *        class of element a,y. Ignore third component.
 * conjelts - in cases where G is not normal in Aut(RG), we may have to
 *        replace the original generators x,y of RG by conjugates under
 *        autmorphisms of RG that do not normalise G.
 *        conjelts is a list of the (nontrivial) conjugating automorphisms -
 *        that is, coset reps. of Normaliser(G) in Aut(RG) as words in
 *        the generating automorphisms t,  u, v....
 * rels - a list of words in  x  and  y which, taken together with
 *        x^ox and y^oy constitute a set of defining relators for RG.
 * repsg - generators of a subgroup of index about 1000 suitable
 *             for use with inverse word group
 * outimages - the images (as words in gens of RG) of the generators of RG
 *        under the outer automorphism group of RG.
 * subgens - words in the outer automorphisms generators of RG that
 *           together with RG generate G.
 * normgens - words in the outer automorphisms generators of RG that
 *           generate the outer automorphism group of G.
 * subpres - presentation of G/RG on subgens.
 * normpres - presentation of Aut(G)/G on normgens.
 */

RadQuotAutsH := procedure(~HR,~GR,isom,~isomims)
/* Identify the radical quotient of G=GR`permgroup and see if it is stored in
 * the database. If not exit with error.
 * If so, then find a homomorphism from the database group to GR`radquot,
 * and set up fields of GR appropriately.
 * If outerauts is true then we also read off the automorphisms of GR`radquot
 * from the database and compute the presentation of GR`radquot.
 * If isom is false then we are just computing Aut(G) and HR, isomims are
 * ignored.
 * If isom is true, then we are also looking for an isomorphism from
 * H = HR`permgroup -> G. If this is found, then the generator images
 * of the FP-group for H under such an isomorphism (mod. radquot) are
 * returned in isomims - otherwise isomims is returned empty.
 */
local GQ, SA, SP, pSQ,  SF, nSF,  socreps, fac, gens1, gens2, cfac,
      SC, projlist, genlist, preslist, fplist, wpembeddings,
      sri, Print, pl, fe, feim, feims, f,
      N, psi, A, pres, msilist, theta, P, dP, T, t, F, phi, W, eG, eP,
      ims, im, rho, GQgens, donerep, wpfusedembeddings, fusednos, I, IGQ,
      eGF, ng, nggq, outim, relval, rel, FA, FArels, FtoFA, ngfa,
      HQ, SAH, pSQH, SFH, socrepsH, eH, x, projlistH, wpembeddingsH, HQgens,
      fusednosH, donerepH, wpfusedembeddingsH, phiH, IHQ, NHG, IGQC, C, pIGQ,
      preslistH, E, tau, eGHF, SQ, conj, Fhom;

  GQ := GR`radquot;
  Print:=GR`printlevel;

  SA,SP,_ := SocleAction(GQ);
  _, pSQ, _ := SocleQuotient(GQ);
  SF:=SocleFactors(GQ);
  nSF := #SF;
  socreps := [ Representative(o) : o in Orbits(SP) ];
 
  if isom then
    HQ := HR`radquot;
    SAH,SP,_ := SocleAction(HQ);
    _, pSQH, _ := SocleQuotient(HQ);
    SFH:=SocleFactors(HQ);
    socrepsH := [ Representative(o) : o in Orbits(SP) ];
    if #SFH ne nSF or #socrepsH ne #socreps then
      if Print gt 1 then
        print "  +Numbers of orbits on socle factors not the same.";
      end if;
      return;
    end if;
  end if;


  projlist:=[];
  for k in [1..nSF] do
    fac := SF[k];
    gens1 := [fac.i : i in [1..Ngens(fac)]];
    cfac := Centraliser(GQ,fac);
    gens2 :=  [cfac.i : i in [1..Ngens(cfac)]];
    SC := sub< GQ | gens1 cat gens2 >;
    projlist[k] := hom< SC->fac | gens1 cat [Id(fac) : x in [1..#gens2]] >;
  end for;
 
  GR`rqprojlist := projlist;
  genlist:=[];
  preslist:=[];
  fplist:=[PowerStructure(Map)|];
  wpembeddings:=[];

  if isom then
    projlistH:=[];
    for k in [1..nSF] do
      fac := SFH[k];
      gens1 := [fac.i : i in [1..Ngens(fac)]];
      cfac := Centraliser(HQ,fac);
      gens2 :=  [cfac.i : i in [1..Ngens(cfac)]];
      SC := sub< HQ | gens1 cat gens2 >;
      projlistH[k] := hom< SC->fac | gens1 cat [Id(fac) : x in [1..#gens2]] >;
    end for;
   
    HR`rqprojlist := projlistH;
  end if;

  for srino in [1..#socreps] do
    sri:=socreps[srino];
    pl := projlist[sri];
    S := SF[sri];
    if Print gt 1 then
      print "  +Considering socle factor number ",sri;
    end if;
    if Print gt 2 then
      print S;
    end if;
    N := Stabilizer(Image(SA), sri) @@ SA;
    //N:=Normaliser(GQ,S);
    psi, A, _, E, Fhom := IdentifyAlmostSimpleGroupH(S,N,Print:max:=false);
 
    theta,P := CosetAction(GQ,N);
    dP := Degree(P);
    T:=[GQ|Id(GQ)]; // transversal of N in GQ.
    for i in [2..dP] do
      _,t := IsConjugate(P,1,i);
      T[i] := t@@theta;
    end for;
 
    genlist[sri]:=[GQ|];
    for i in [1..Ngens(A)] do if A.i in Socle(A) then
      Append(~genlist[sri],A.i @@ psi @ pl);
    end if; end for;

    for t in T do if t ne Id(GQ) then
      srit:=sri^SA(t);
      genlist[srit]:=[GQ| g^t : g in genlist[sri] ];
    end if; end for;
    for t in T do
      srit:=sri^SA(t);
      compsub:=sub<GQ|genlist[srit]>;
      if #compsub le GR`smallsimplefactor then
        E,tau := FPGroup(compsub);
        preslist[srit]:=E;
        fplist[srit] := tau;
/* Surely Ngens(F) = Ngens(compsub) in this case ? */
        for i in [Ngens(compsub)+1..Ngens(E)] do
          error "This cannot be!";
          Append(~genlist[srit],tau(E.i));
        end for;
      else
        if assigned Fhom then
          tau := hom < E->compsub | x :-> (x @ Fhom @@ psi @ pl)^t,
                                    x :-> (x^(t^-1)) @@ pl @ psi @@ Fhom >;
        else
          E,tau := FPGroupStrong(compsub);
        end if;
        preslist[srit]:=E;
        fplist[srit] := tau;
        for i in [Ngens(compsub)+1..Ngens(E)] do
          Append(~genlist[srit],tau(E.i));
        end for;
      end if;
    end for;
 
    /* Next we define the natural map rho: GQ -> A Wr P (with image
     * contained in N/C Wr P) induced by the insertion N -> GQ.
     */
    W, eG, eP := WreathProduct(A,Sym(dP));
    ims:=[W|];
    for g in [GQ.i : i in [1..Ngens(GQ)] ] do
      im := g @ theta @ eP;
      for i in [1..dP] do
        t := T[i];
        tcomp := (T[1^theta(t*g^-1)] * g * t^-1) @ psi @ eG[i];
        im := im * tcomp;
      end for;
      Append(~ims,im);
    end for;
    rho := hom<GQ->W| ims >;
    // rho is an embedding taking S to the first factor.
    if Print gt 1 then
      print "  +Constructed embedding into wreath product";
    end if;
    wpembeddings[srino] := rho;
  end for;
  GR`rqfplist := fplist;

  if isom then
    wpembeddingsH:=[];
    for srino in [1..#socrepsH] do
      sri:=socrepsH[srino];
      pl := projlistH[sri];
      S := SFH[sri];
      if Print gt 1 then
        print "  +Considering H socle factor number ",sri;
      end if;
      if Print gt 2 then
        print S;
      end if;
      N:=Normaliser(HQ,S);
      psi, A, _, _, _ := IdentifyAlmostSimpleGroupH(S,N,Print:max:=false);
   
      theta,P := CosetAction(HQ,N);
      dP := Degree(P);
      T:=[HQ|Id(HQ)]; // transversal of N in GQ.
      for i in [2..dP] do
        _,t := IsConjugate(P,1,i);
        T[i] := t@@theta;
      end for;
   
      /* Next we define the natural map rho: HQ -> A Wr P (with image
       * contained in N/C Wr P) induced by the insertion N -> GQ.
       */
      W, eH, eP := WreathProduct(A,Sym(dP));
      ims:=[W|];
      for g in [HQ.i : i in [1..Ngens(HQ)] ] do
        im := g @ theta @ eP;
        for i in [1..dP] do
          t := T[i];
          tcomp := (T[1^theta(t*g^-1)] * g * t^-1) @ psi @ eH[i];
          im := im * tcomp;
        end for;
        Append(~ims,im);
      end for;
      rho := hom<HQ->W| ims >;
      // rho is an embedding taking S to the first factor.
      if Print gt 1 then
        print "  +Constructed embedding into wreath product";
      end if;
      wpembeddingsH[srino] := rho;
    end for;
  end if;

   
  SQ, GR`rqsocmap := SocleQuotient(GQ);
  ReduceDefiningGenerators(~(SQ));
  if #SQ le GR`smallsimplefactor then
    F,phi := FPGroup(SQ);
  else
    F,phi := FPGroupStrong(SQ);
  end if;
  preslist[nSF+1] := F;
  genlist[nSF+1] := [ SQ.i @@ GR`rqsocmap : i in [1..Ngens(SQ)] ];

  if #SQ gt 1 then
    for i in [Ngens(SQ)+1..Ngens(F)] do
      Append(~genlist[nSF+1],F.i @ phi @@ GR`rqsocmap);
    end for;
  end if;

  GR`rqsocquot := SQ;
  GR`rqsqwordmap := phi;

  GR`rqgenlist := genlist;
  GQ, GR`rqwordgp := PresentationSubgroupTF(genlist,preslist,projlist,fplist);

  GQgens:= &cat(genlist);
  GR`radquot := GQ;
 
  F := GR`rqwordgp;

  GR`fpgroup := F;
  GR`centre := sub<F|>;
  GR`newgens := [g@@GR`radmap : g in GQgens];
  GR`newgroup := sub<GR`permgroup | GR`newgens >;
  nggq := Ngens(GR`newgroup);
  assert Ngens(F) eq nggq;
  GR`quotgens := [ nggq ];
  GR`fptoperm := hom<F -> GR`newgroup | [GR`newgens[i] : i in [1..nggq]] >;

/* We will compute the automorphism group as the normaliser in a suitable
 * overgroup of the full wreath product embedding space. For this we need
 * to work out which wreath product embeddings could have the same image,
 * because they could conceivably be fused under Aut(GQ).
 * The next bit of code is more complicated in the isom case, so we will
 * do that separately.
 */
  if not isom then
    donerep := [false : i in [1..#socreps]];
    wpfusedembeddings:=[];
    for srino in [1..#socreps] do if not donerep[srino] then
      rho := wpembeddings[srino];
      fusednos := [srino];
      I := Codomain(rho);
      for j in [srino+1..#socreps] do if not donerep[j] then
        if Codomain(wpembeddings[j]) cmpeq I then
          Append(~fusednos,j);
          donerep[j]:=true;
        end if;
      end if; end for;
      if #fusednos eq 1 then
        Append(~wpfusedembeddings,rho);
      else
        W, eGF := WreathProduct(I,Sym(#fusednos));
        feims := [];
        for g in GQgens do
          feim:=Id(W);
          for i in [1..#fusednos] do
            f := fusednos[i];
            feim := feim * (g @ wpembeddings[f] @ eGF[i]);
          end for;
          Append(~feims,feim);
        end for;
        fe := hom< GQ->W | feims >;
        Append(~wpfusedembeddings, fe);
      end if;
    end if; end for;
    phi := PermutationRepresentationSumH(GQ,wpfusedembeddings);
    I := Codomain(phi);
    IGQ := Image(phi);
    IGQC := IGQ;
    pIGQ := IdentityHomomorphism(IGQ);
    N := Normaliser(I,IGQ);
  else
    donerep := [false : i in [1..#socreps]];
    donerepH := [false : i in [1..#socrepsH]];
    wpfusedembeddings:=[];
    wpfusedembeddingsH:=[];
    for srino in [1..#socreps] do if not donerep[srino] then
      rho := wpembeddings[srino];
      fusednos := [srino];
      I := Codomain(rho);
      for j in [srino+1..#socreps] do if not donerep[j] then
        if Codomain(wpembeddings[j]) cmpeq I then
          Append(~fusednos,j);
          donerep[j]:=true;
        end if;
      end if; end for;
      fusednosH:=[];
      for j in [1..#socrepsH] do if not donerepH[j] then
        if Codomain(wpembeddingsH[j]) cmpeq I then
          Append(~fusednosH,j);
          donerepH[j]:=true;
        end if;
      end if; end for;
      if #fusednos ne #fusednosH then
        if Print gt 1 then
          print "  +Socle factors are not isomorphic on counting";
        end if;
        return;
      end if;
      W, eGF := WreathProduct(I,Sym(#fusednos));
      W, eGHF := WreathProduct(W,Sym(2));
      feims := [];
      for g in GQgens do
        feim:=Id(W);
        for i in [1..#fusednos] do
          f := fusednos[i];
          feim := feim * (g @ wpembeddings[f] @ eGF[i] @ eGHF[1]);
        end for;
        Append(~feims,feim);
      end for;
      fe := hom< GQ->W | feims >;
      Append(~wpfusedembeddings, fe);
      feims := [];
      for g in [HQ.i : i in [1..Ngens(HQ)] ] do
        feim:=Id(W);
        for i in [1..#fusednosH] do
          f := fusednosH[i];
          feim := feim * (g @ wpembeddingsH[f] @ eGF[i] @ eGHF[2]);
        end for;
        Append(~feims,feim);
      end for;
      fe := hom< HQ->W | feims >;
      Append(~wpfusedembeddingsH, fe);
    end if; end for;
    phi := PermutationRepresentationSumH(GQ,wpfusedembeddings);
    phiH := PermutationRepresentationSumH(HQ,wpfusedembeddingsH);
    I := Codomain(phi);
    IGQ := Image(phi);
    IHQ := Image(phiH);
    C := Centraliser(I,IGQ);
    if not IHQ subset C or #(IGQ meet C) ne 1  then
      error "Centralising error in isomorphism set-up";
    end if;
    gens1 := [IGQ.i : i in [1..Ngens(IGQ)]];
    gens2 := [C.i : i in [1..Ngens(C)]];
    IGQC := sub< I | gens1 cat gens2 >;
    pIGQ := hom< IGQC->IGQ | gens1 cat [Id(IGQ): i in [1..Ngens(C)]]>;
    NHG := Normaliser(I,sub<I|IGQ,IHQ>);
    N := Normaliser(NHG,IGQ);
    IGQC := N meet IGQC;
    conj, x := IsConjugate(NHG,IGQ,IHQ);
    if not conj then
      if Print gt 1 then
        print "  +Socle factors are not isomorphic on normaliser computation";
      end if;
      return;
    end if;
    // We will use x to set up the isomorphism H->G.
    isomims := [ F.i : i in [1..Ngens(F)] ];
    HR`rqgenlist:=[];
    preslistH:=[];
    HR`rqfplist:=[PowerStructure(HomGrp)|];
    for k in [1..nSF] do
      // get HR`rqgenlist, etc. by conjugating genlist by x
      HR`rqgenlist[k] := [ ((g @ phi)^x) @@ phiH : g in genlist[k] ];
      preslistH[k]:=preslist[k];
      compsub:=sub<HQ|HR`rqgenlist[k]>;
      // the order of the socle factors of H may have changed, so we
      // need to redefine HR`rqprojlist.
      l := Representative({ l : l in [1..nSF] | compsub eq SFH[l] });
      HR`rqprojlist[k] := projlistH[l];
      HR`rqfplist[k]:= iso< preslistH[k]->compsub | HR`rqgenlist[k]>;
    end for;
    HR`rqgenlist[nSF+1] := [ ((g @ phi)^x) @@ phiH : g in genlist[nSF+1] ];
    SQ, HR`rqsocmap := SocleQuotient(HQ);
    // must use corresponding generators to G
    SQ := sub< SQ | [ g @ (HR`rqsocmap) : g in HR`rqgenlist[nSF+1]] >;
    preslistH[nSF+1] := preslist[nSF+1];
    if Ngens(SQ) eq 0 then
      HR`rqsqwordmap := hom< preslistH[nSF+1] -> SQ |
                             [ Id(SQ)] >;
    else
      HR`rqsqwordmap := hom< preslistH[nSF+1] -> SQ |
                             [ SQ.i : i in [1..Ngens(SQ)] ] >;
    end if;

    HR`rqsocquot := SQ;

    HQ, HR`rqwordgp := PresentationSubgroupTF(
                      HR`rqgenlist,preslistH,HR`rqprojlist,HR`rqfplist);
   
   
    HQgens:= &cat(HR`rqgenlist);
    HR`radquot := HQ;
   
    F := HR`rqwordgp;
    HR`fpgroup := F;
    HR`centre := sub<F|>;
    HR`newgens := [g@@HR`radmap : g in HQgens];
    HR`newgroup := sub<HR`permgroup | HR`newgens >;
    nggq := Ngens(HR`newgroup);
    HR`quotgens := [ nggq ];
    if HR`quotgens ne GR`quotgens then
      error "Number of socle quotient generators wrong.";
    end if;
    HR`fptoperm := hom<F -> HR`newgroup | [HR`newgens[i] : i in [1..nggq]] >;
  end if;

  F := GR`fpgroup;
  if N eq IGQC then
    GR`outimages := [];
    GR`autgroup := F;
    GR`outerautgroup := Group<x|x>;
    GR`orderautgroup := #GQ;
    GR`orderouterautgroup := 1;
    if GR`printlevel gt 1 then
      print "  +Top factor has no outer automorphisms.";
    end if;
    GR`fptoaut :=
         hom<F->F | [F.i : i in [1..Ngens(F)]] >;
    GR`auttoouter := hom<F->GR`outerautgroup |
                   [Id(GR`outerautgroup) : i in [1..Ngens(F)]] >;
    return;
  end if;

  // get a minimal set of normalising generators
  ng := [];
  while sub<N|IGQC,ng> ne N do
    x:=Random(N);
    while  x in sub<N|IGQC,ng> do x:=Random(N); end while;
    Append(~ng,x);
  end while;

  /* Now deal with automorphism group data */
  ngfa := nggq + #ng;
  FA := FreeGroup(ngfa);
  FtoFA := hom <F->FA | [FA.i : i in [1..nggq] ] >;
  FArels := [rel@FtoFA : rel in Relations(F)];
  GR`outimages := [];

 /* get action of outer auts on generators of GQ */
  
  for k in [1..#ng] do
    w := ng[k];
    outim := [RadQuotWord(GR, (w^-1*phi(GQgens[i])*w) @@ phi @@ GR`radmap) :
              i in [1..Ngens(F)]];

    FArels := FArels cat
      [FA.(nggq+k)^-1*FA.i*FA.(nggq+k) = FtoFA(outim[i]) : i in [1..Ngens(F)]];
    Append(~GR`outimages,outim);
  end for;

  // Finally relators of outer auts 
  // get a presentation of N/IGQC
  Q, pQ := quo<N|IGQC>;
  Q := sub< Q | [pQ(g) : g in ng] >;
  presQ := FPGroup(Q);

  // define an inverse 'hom' for evaluating relators in IGQC.
  liftQ := hom< presQ -> N | ng >;
  for rQ in Relations(presQ) do
    w:=LHS(rQ)*RHS(rQ)^-1;
    relval := liftQ(w) @ pIGQ @@ phi;
    w:=ElementToSequence(w);
    rel:=Id(FA);
    for i in w do
      if i gt 0 then
        rel := rel*FA.(nggq+i);
      else
        rel := rel*(FA.(nggq-i))^-1;
      end if;
    end for;
    Append(~FArels,rel = FtoFA(RadQuotWord(GR, relval @@ GR`radmap)));
  end for;

  if GR`printlevel gt 2 then
    print "    +Found presentation of automorphism group of top factor.";
  end if;

  GR`autgroup := quo< FA | FArels >;
  GR`outerautgroup := presQ;
  GR`orderouterautgroup := #GR`outerautgroup;
  GR`orderautgroup := GR`orderouterautgroup * #GQ;

  GR`fptoaut :=
       hom<F->GR`autgroup | [(GR`autgroup).i : i in [1..Ngens(F)]] >;
  GR`auttoouter := hom<GR`autgroup->presQ |
             [Id(presQ) : i in [1..Ngens(F)]] cat [presQ.i : i in [1..#ng]] >;

end procedure;
