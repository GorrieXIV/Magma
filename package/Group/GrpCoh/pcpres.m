freeze;

import "pcpresgen.m": PCElToSeq;
//import "strongpres.m": FirstCohomologyGroupG;

ModulePCP := function(P,M)
/* M is a module for permutation or matrix  group P, where P is a p-group,
 * over field of order p.
 * Return PP, phi, MM where PP, phi := pQuotient(P,p,127)
 * and MM the corresponding module for PP.
 */
  local PP, prime, phi, MM, R;
  if P ne Group(M) then
    error "Incompatible arguments for ModulePCP!";
  end if;
  prime := Factorisation(#P)[1][1];
  if #BaseRing(M) ne prime then
     error "Module has wrong characteristic";
  end if;
  PP, phi := pQuotient(P,prime,127);
  R := Representation(M);
  MM := GModule(PP,[ R(PP.i @@ phi) : i in [1..NPCgens(PP)] ]);
  return PP, phi, MM;
end function;


MakeModuleRecordPCP := function(P,M)
/* This is called prior to calling any of the cohomological functions,
 * and returns a cohomology module with fields for the various objects
 * that may get computed.
 * P is a GrpPC for a finite p-group
 * M should be a module for P over the field of order p.
 * The cohomological functions take this record as argument.
 */
  local R, PG, p, ng, relpos, mats, imats, r, F, rels, PtoF, FQ, ct, MF;

  p := Factorisation(#P)[1][1];
  R := Representation(M);
  PG := PCGenerators(P);
  ng := #PG;
  mats := [ R(PG[i]) : i in [1..ng] ];
  imats := [ m^-1 : m in mats ];
  r := EmptyCohomologyModule();
  r`modtype := ModGrp;
  r`gptype := GrpPC;
  r`gpc:=P;
  r`mats := mats; r`imats := imats;
  r`dim := Dimension(M);
  r`ring := BaseRing(M);

  /* We need a well-defined ordering for the PC relations of P, and
   * a corresponding GrpFP to use for the ComplementEquationsMatrix.
   * We use the ordering P.1^p, ... P.n^p, (P.2,P.1), (P.3,P.1), (P.3,P.2),...
   * The array relpos gives the number of the corresponding relation.
   * relpos[i][i] for P.i^p  and relpos[j][i] for (P.j,P.i).
   *
   * The format for relations of an extension of M by P will be
   * P.i^p = word * m  or  (P.j,P.i) = word * m, for m in M, where j>i.
   */
  relpos := [ [] : i in [1..ng] ];
  F := FreeGroup(ng);
  PtoF := function(w) //map word in P to corresponding word in F
   local s; s:=ElementToSequence(w); return &*[F.i^s[i]:i in [1..ng]];
  end function;
  //PtoF := hom < P->F | [F.i : i in [1..ng]] >; unsafe
  rels := [];
  
  ct := 0;
  for i in [1..ng] do 
    ct +:= 1;
    relpos[i][i] := ct;
    Append(~rels,PtoF(P.i^p)^-1 * PtoF(P.i)^p ); 
  end for;
  
  for j in [2..ng] do for i in [1..j-1] do
    ct +:= 1;
    relpos[j][i] := ct;
    Append(~rels,PtoF(P.j*P.i)^-1 * PtoF(P.j) * PtoF(P.i)); 
  end for; end for;

  r`relpos := relpos;

  r`gf := quo<F|rels>;
  //Will need complement equations matrix - get is as follows:
  //FirstCohomologyGroupG(r);
  MF := GModule(r`gf,[ R(P.i) : i in [1..ng] ]);
  r`cem := ComplementEquationsMatrix(MF);

  // Work out the 1-cohomology components using existing functions
/*
  r`cem := ComplementEquationsMatrix(MF);
  r`Z1 := Nullspace(r`cem);
  r`B1 := ConjugateComplementSubspace(MF);
  r`H1, r`Z1toH1 := quo< r`Z1 | r`B1 >;
*/

  return r;
end function;

CollectGeneralWordPCP := procedure(P,w,add,d,~X,colno,relpos,mats,imats)
/* P is a PC-group and w a sequence of integers in the range [1..NPCgens(P)],
 * representing a word in P. The word is collected, using P.
 * As we do this, we fill in entries of X in columns [colno+1..colno+d]
 * for tails arising.
 * If add is true, add entries to X, otherwise subtract.
 */
  local wmap, actmat, p, collecting, pos, gen, nextgen, genct, rowno;

  // We want the matrix for the whole word.
  // The acting matrix will be that of the suffix of the word from the
  // current point in the word.
  if #w le 1 then return; end if;
  wmat :=  mats[w[1]];
  for i in [2..#w] do wmat := wmat*mats[w[i]]; end for;

  p := Factorisation(#P)[1][1];

  collecting := true;
  changed := true;
  while collecting do
    if changed then
       if #w le 1 then return; end if;
       pos := 1;
       gen := w[pos];
       genct := 1;
       actmat := imats[gen]*wmat;
    end if;
    pos := pos+1;
    nextgen := w[pos];
    actmat := imats[nextgen]*actmat;
    genct :=  nextgen eq gen select genct+1 else 1;
    if nextgen lt gen then
      Insert(~w,pos-1,pos,PCElToSeq(P.gen*P.nextgen));
      rowno := d*(relpos[gen][nextgen]-1);
      //  Alter X in positions [rowno+1..rowno+d, colno+1..colno+d]
      if add then
        InsertBlock(~X,ExtractBlock(X,rowno+1,colno+1,d,d)+actmat,
                                                          rowno+1,colno+1);
        //for k in [1..d] do for l in [1..d] do
        //   X[rowno+k][colno+l] +:= actmat[k][l];
        //end for; end for;
      else
        InsertBlock(~X,ExtractBlock(X,rowno+1,colno+1,d,d)-actmat,
                                                          rowno+1,colno+1);
        //for k in [1..d] do for l in [1..d] do
        //   X[rowno+k][colno+l] -:= actmat[k][l];
        //end for; end for;
      end if;
      changed := true;
    elif genct eq p then
      Insert(~w,pos-p+1,pos,PCElToSeq(P.gen^p));
      rowno := d*(relpos[gen][gen]-1);
      //  Alter X in positions [rowno+1..rowno+d, colno+1..colno+d]
      if add then
        InsertBlock(~X,ExtractBlock(X,rowno+1,colno+1,d,d)+actmat,
                                                          rowno+1,colno+1);
        //for k in [1..d] do for l in [1..d] do
        //   X[rowno+k][colno+l] +:= actmat[k][l];
        //end for; end for;
      else
        InsertBlock(~X,ExtractBlock(X,rowno+1,colno+1,d,d)-actmat,
                                                          rowno+1,colno+1);
        //for k in [1..d] do for l in [1..d] do
        //   X[rowno+k][colno+l] -:= actmat[k][l];
        //end for; end for;
      end if;
      changed := true;
    else
      gen := nextgen;
      changed := false;
    end if;
    if not changed and pos eq #w then
      collecting := false;
    end if;
  end while;
end procedure;

SecondCohomologyGroupPCP := procedure(CM)
/* 
 * SecondCohomologyGroupSG computes a matrix and stores its nullspace, which
 *  is isomorphic to Z^2(G,M), then computes B2, H2.
 */

  local  P, mats, imats, p, K, d, ng, nr, ncols, X, colno, rowno, relpos, w;

  mats:=CM`mats; imats:=CM`imats; relpos:=CM`relpos;
  K:=CM`ring;
  p:=#K;
  d :=CM`dim;
  P:=CM`gpc;

  ng := NPCGenerators(P);
  nr := ng * (ng+1) div 2; // number of PC-relations

  /* Set up the matrix  X  where we will store the equations */
  ncols := d * (ng*(ng-1)*(ng-2) div 6 + ng*(ng-1) + ng); 
     // d * number of associativity conditions to be checked.
  vprint ModCoho: "Setting up",ncols,"equations in",nr*d,"unknowns";
  X:=Hom(RSpace(K,nr*d),RSpace(K,ncols))!0;
  
  colno:=0;

  // 1. the (P.i^p)*P.i = P.i*(P.i^p) conditions.
  for i in [1..ng] do
    w := [i : n in [1..p+1]];
    CollectGeneralWordPCP(P,w,true,d,~X,colno,relpos,mats,imats);
    w := [i] cat PCElToSeq(P.i^p); 
    rowno := d*(relpos[i][i]-1);
    for k in [1..d] do
      X[rowno+k][colno+k] -:= 1;
    end for;
    CollectGeneralWordPCP(P,w,false,d,~X,colno,relpos,mats,imats);
    colno +:= d;
  end for;

  // 2. the P.j*P.i*P.i^p-1 = P.j*(P.i^p) (j>i) conditions.
  for j in [2..ng] do for i in [1..j-1] do
    w := [j] cat [i : n in [1..p]];
    CollectGeneralWordPCP(P,w,true,d,~X,colno,relpos,mats,imats);
    w := [j] cat PCElToSeq(P.i^p); 
    rowno := d*(relpos[i][i]-1);
    for k in [1..d] do
      X[rowno+k][colno+k] -:= 1;
    end for;
    CollectGeneralWordPCP(P,w,false,d,~X,colno,relpos,mats,imats);
    colno +:= d;
  end for; end for;

  // 3. the P.j^p*P.i = P.j^p-1*P.j*P.i^p (j>i) conditions.
  for j in [2..ng] do for i in [1..j-1] do
    w := [j : n in [1..p]] cat [i];
    CollectGeneralWordPCP(P,w,true,d,~X,colno,relpos,mats,imats);
    w := [j : n in [1..p-1]] cat PCElToSeq(P.j*P.i); 
    rowno := d*(relpos[j][i]-1);
    for k in [1..d] do
      X[rowno+k][colno+k] -:= 1;
    end for;
    CollectGeneralWordPCP(P,w,false,d,~X,colno,relpos,mats,imats);
    colno +:= d;
  end for; end for;

  // 4. the (P.k*P.j)*P,i = P.k*(P.j*P.i) (k>j>i) conditions.
  for k in [3..ng] do for j in [2..k-1] do for i in [1..j-1] do
    w := [k,j,i];
    CollectGeneralWordPCP(P,w,true,d,~X,colno,relpos,mats,imats);
    w := [k] cat PCElToSeq(P.j*P.i); 
    rowno := d*(relpos[j][i]-1);
    for k in [1..d] do
      X[rowno+k][colno+k] -:= 1;
    end for;
    CollectGeneralWordPCP(P,w,false,d,~X,colno,relpos,mats,imats);
    colno +:= d;
  end for; end for; end for;

  //We won't store X itself, since it is very large - we only
  // need its nullspace.
  CM`Z2 := Nullspace(X);
  vprint ModCoho,2: "Calculated Z2";
  CM`B2 := Image(CM`cem);
  CM`H2, CM`Z2toH2 := quo< CM`Z2 | CM`B2 >;
  vprint ModCoho,2: "Calculated H2";

end procedure;

MakeModuleRecordRes := function(G,M)
/* Make a record for computation of H^2(G,M) by SecondCohomologyDimensionRes */
  local K, p, PP, MP, P, phi, CMF, CM, fac;
  CMF := recformat<
                    gp: Grp,
                module: ModGrp,
                   rep: Map,
                 prime: RngIntElt,
                 sylgp: Grp,
              syltopcp: Map,
               modcoho: ModCoho,
              subchain: SeqEnum>;

  K := BaseRing(M);
  p := #K;
  PP := Sylow(G,p);
  fac := FactoredOrder(PP);
  vprint ModCoho,1: "Computing H^2(P,M): |P| =",fac[1][1],"^",fac[1][2];
  if #PP eq 1 then
       return rec <CMF| gp:=G, module:=M, prime:=p,sylgp:=PP >;
  end if;

  MP := Restriction(M,PP);
  P, phi, MP := ModulePCP(PP,MP);
  CM:=MakeModuleRecordPCP(P,MP);
  SecondCohomologyGroupPCP(CM);
  return rec < CMF | gp:=G, module:=M, rep:=Representation(M), prime:=p,
                     sylgp:=PP, syltopcp:=phi, modcoho:=CM >;
end function;
    
ExtensionOfModulePCP := function(CM,seq)
/* CM`H2 should have been computed already with SecondCohomologyGroup.
 * seq should be an integer sequence representing an element of  CM`H2.
 * A presentation of a corresponding extension of the module by the
 * group is returned
 */
 local Z, P, p, mats, imats, ng, z2v, w, rels, rel, phi, H2, e, E;

  Z := Integers();
  P:=CM`gpc; mats:=CM`mats;
  p:= #CM`ring; d := CM`dim;
  ng := NPCGenerators(P);

  H2 := CM`H2;
  e := H2!0;
  if #seq ne Ngens(H2) then
    error "Second argument has wrong length";
  end if;
  e := H2!seq;
  z2v := e @@ CM`Z2toH2;

  //Now we can censtruct the extension.
  F := FreeGroup(ng+d);
  rels := [];
  for i in [1..d] do
    Append(~rels,(F.(ng+i))^p = Id(F));
  end for;
  for i in [1..d] do for j in [i+1..d] do
    Append(~rels,F.(ng+i)*F.(ng+j) = F.(ng+j)*F.(ng+i));
  end for; end for;
  for i in [1..ng] do for j in [1..d] do
    w:=Id(F);
    for k in [1..d] do
      w := w * (F.(ng+k))^Z!mats[i][j][k];
    end for;
    Append(~rels,F.i^-1*F.(ng+j)*F.i = w);
  end for; end for;

  PtoF := function(w) //map word in P to corresponding word in F
   local s; s:=ElementToSequence(w); return &*[F.i^s[i]:i in [1..ng]];
  end function;
  //phi := hom<P->F | [F.i : i in [1..ng]] >; unsafe
  colno := 0;
  for i in [1..ng] do
    w := Id(F);
    for k in [1..d] do w := w * F.(ng+k)^Z!z2v[colno+k];  end for;
    Append(~rels,F.i^p = PtoF(P.i^p)*w);
    colno +:= d;
  end for;

  for j in [2..ng] do for i in [1..j-1] do
    w := Id(F);
    for k in [1..d] do w := w * F.(ng+k)^Z!z2v[colno+k];  end for;
    Append(~rels,F.j*F.i = PtoF(P.j*P.i)*w);
    colno +:= d;
  end for; end for;
  E := quo<F|rels>;
  return E;
end function;

StabilityTest2 := function(MR,g)
/* MR should be a record returned by MakeModuleRecordRes and g an element
 * of MR`gp. Let P = MR`sylgp, and H2 = MR`modcoho`H2.
 * Let Q = P meet g^-1Pg.
 * Two maps from H2 to H^2(Q,M) are computed, the first being the
 * restriction, and the second the restriction to P meet gPg^-1
 * followed by conjugation by g.
 * The kernel of the difference of the maps is returned, which is
 * precisely the set of elements of H2 that are stable wrt g.
 */

  local K, p, d, G, M, P, PP, Q, QQ, ng, ngq, Ptopcp, Qtopcp, MQ, CMQ,
        mats, imats, H2, Z2toH2, h2ims, seq, imcocyc, colno,
        gmat, gi, w1, w2, w2s, wm, E, PtoE, PE, EtoPE, PtoPE, PEM, cmat;

  vprint ModCoho,2: "StabilityTest",g;
  G := MR`gp;
  if not g in G then
    error "Second argument of StabilityTest is not in the group";
  end if;
  p := MR`prime;
  K := GF(p);
  PP := MR`sylgp;
  Ptopcp := MR`syltopcp;
  H2 := MR`modcoho`H2;
  Z2toH2 := MR`modcoho`Z2toH2;
  M := MR`module;
  d := Dimension(M);

  QQ := PP meet PP^g;
  MQ := Restriction(M,QQ);
  Q, Qtopcp, MQ := ModulePCP(QQ,MQ);
  ngq := NPCGenerators(Q);
  vprint ModCoho,2: "Exponent of intersection",ngq;
  CMQ := MakeModuleRecordPCP(Q,MQ);
  SecondCohomologyGroupPCP(CMQ);
  P := MR`modcoho`gpc;
  ng := NPCGenerators(P);
  mats := MR`modcoho`mats;
  imats := MR`modcoho`imats;
  gi := g^-1;
  gmat := (MR`rep)(g);

  h2ims := [];
  for h2genno in [1..Ngens(H2)] do
    seq := [0 : i in [1..Ngens(H2)]]; seq[h2genno]:=1;
    E :=  ExtensionOfModulePCP(MR`modcoho,seq);
    PtoE := hom<P->E | [E.i : i in [1..ng]]>; 
    PE, EtoPE := pQuotient(E,p,127);
    PEM := sub < PE | [EtoPE(E.(ng+i)) : i in [1..d]]>;
    PtoPE := Ptopcp*PtoE * EtoPE;
    // We need a matrix to convert an element of PEM from the
    // Magma representation to an element in the generators of our M.
    // To do this we multiply the magma word by cmat
    cmat := Matrix(K,d,d,
                 [ElementToSequence(PEM!EtoPE(E.(ng+i))) : i in [1..d]])^-1;
 
    imcocyc := RSpace(K,d*ngq*(ngq+1) div 2)!0;
    colno := 0;
    for i in [1..ngq] do
      // imtail for Q.i^p
      w1 := (Q.i @@ Qtopcp @ PtoPE)^p;
      w2s := PCElToSeq(Q.i^p);
      w2 := Id(PE);
      for n in w2s do
        w2 := w2 * (Q.n @@ Qtopcp @ PtoPE);
      end for;
      wm := Vector(K,d,ElementToSequence(PEM!(w2^-1*w1)))*cmat;
      for k in [1..d] do imcocyc[colno+k] +:= wm[k]; end for;

      w1 := (((Q.i @@ Qtopcp)^gi) @ PtoPE)^p;
      w2 := Id(PE);
      w2s := PCElToSeq(Q.i^p);
      for n in w2s do
        w2 := w2 * (((Q.n @@ Qtopcp)^gi) @ PtoPE);
      end for;
      wm := Vector(K,d,ElementToSequence(PEM!(w2^-1*w1)))*cmat*gmat;
      for k in [1..d] do imcocyc[colno+k] -:= wm[k]; end for;

      colno +:= d;
    end for;
    for j in [2..ngq] do for i in [1..j-1] do
      // imtail for Q.j * Q.i
      w1 :=  (Q.j @@ Qtopcp @ PtoPE) * (Q.i @@ Qtopcp @ PtoPE);
      w2 := Id(PE);
      w2s := PCElToSeq(Q.j*Q.i);
      for n in w2s do
        w2 := w2 * (Q.n @@ Qtopcp @ PtoPE);
      end for;
      wm := Vector(K,d,ElementToSequence(PEM!(w2^-1*w1)))*cmat;
      for k in [1..d] do imcocyc[colno+k] +:= wm[k]; end for;

      w1 := (((Q.j @@ Qtopcp)^gi) @ PtoPE) * (((Q.i @@ Qtopcp)^gi) @ PtoPE);
      w2 := Id(PE);
      w2s := PCElToSeq(Q.j*Q.i);
      for n in w2s do
        w2 := w2 * (((Q.n @@ Qtopcp)^gi) @ PtoPE);
      end for;
      wm := Vector(K,d,ElementToSequence(PEM!(w2^-1*w1)))*cmat*gmat;
      for k in [1..d] do imcocyc[colno+k] -:= wm[k]; end for;

      colno +:= d;
    end for; end for;
    Append(~h2ims,CMQ`Z2toH2(imcocyc));
  end for;
  return Kernel(hom < H2->CMQ`H2 | h2ims >);
end function;

FindSubgroupChain := function(G,P: n:=20 )
  /* P should be a Sylow p-subgroup of permutation group G.
   * Find and return a list of subgroups [G=P,...,Gn=G] with
   * Gi < G{i+1} with index as small as possible.
   * But stop trying to refine if index is less than n
   */
  local p, seq, sylind, orb, norbs, orbdone, Z, OZG, OZ, centels, a, b, c,
        H, N, foundsub, bestind, ind, bestsub, orbsize, orbno, orbstab,
        el, elno, cent, badind;

  p := Factorisation(#P)[1][1];
  // We find the sequence from the top down.
  seq := [G];
  sylind := Index(G,P);
  if sylind eq 1 then return seq; end if;

  //We will be trying to find subgroups of P as stabilizers of orbits of P,
  //so we first calculate the orbits.
  if sylind ge n then
     orb := Orbits(P);
     norbs := #orb;
     orbdone := [];
     for i in [1..norbs] do
        orbdone[i] := false; //this means orbit number i is not yet processed.
     end for;
  end if;

   //We also might try centralizers of central elements, so let's find
   //the centre of P, and then find a small random set of elements
   //of order p.
   Z := Centre(P);
   OZG := [];
   for el in Generators(Z) do
     Append(~OZG,el^(Order(el) div p));
   end for;
   OZ := sub<Z|OZG>;
   if IsCyclic(OZ) then
      centels := [OZG[1]];
   elif #OZG eq 2 then
     a := OZG[1]; b := OZG[2];
     if p eq 2 then centels:=[a,b,a*b];
       elif p eq 3 then centels:=[a,b,a*b,a*b^2];
       elif p eq 5 then centels:=[a,b,a*b,a*b^2,a*b^3,a*b^4];
       else centels:=[a,b,a*b,a*b^2,a*b^3,a*b^4,a*b^5,a*b^6];
     end if;
   else
     a := OZG[1]; b := OZG[2]; c := OZG[3];
     centels := [a,b,c,a*b,a*c,b*c,a*b*c];
   end if;

   //Now we start looking for subgroups.
   H := G;
   foundsub := true;
   while sylind ge n and foundsub do
      foundsub := false;
      bestind := sylind; //The smallest index we have so far.

      //First try the normalizer of P
      N := Normalizer(H,P);
      if H ne N and P ne N then
        ind :=  Index(H,N);
        if ind lt n then
           //Found a suitable subgroup!!
           H := N;
           Append(~seq,H);
           foundsub := true;
           sylind := sylind div ind;
        else
           bestind := ind;  bestsub := N;
        end if;
      end if;

      //We next look for a suitable subgroup as a stabilizer of an orbit
      //of P - we consider the orbits in order of increasing size - we
      //go only up to size 16, since it takes too long to calculate set
      //stabilizers for large sets.
      orbsize := 1;
      while not foundsub and orbsize le 16 do
         orbno := 1;
         while not foundsub and orbno le norbs and orbno le 20 do
            if not orbdone[orbno] and #orb[orbno] eq orbsize then
               if orb[orbno] eq Orbit(H,Representative(orb[orbno])) then
                  orbstab := H;
               else
                  orbstab := Stabilizer(H,orb[orbno]);
               end if;
               if orbstab eq H or orbstab eq P then
                  orbdone[orbno] := true;
               else
                  ind := Index(H,orbstab);
                  if ind lt n then
                     //Found a suitable subgroup!!
                     H := orbstab;
                     Append(~seq,H);
                     foundsub := true;
                     sylind := sylind div ind;
                     orbdone[orbno] := true;
                  else  
                     //We could try the normalizer!
                     N := Normalizer(H,orbstab);
                     if N ne H and N ne orbstab then
                        ind := Index(H,N);
                        orbstab := N;
                        if ind lt n then
                           //Found a suitable subgroup!!
                           H := N;
                           Append(~seq,H);
                           foundsub := true;
                           sylind := sylind div ind;
                        end if;
                     end if;
                     if ind lt bestind then
                       //Not ideal, but the best we have so far, so remember it!
                       bestind := ind;  bestsub := orbstab;
                     end if;
                  end if;
               end if;
            end if;
            orbno := orbno + 1;
         end while;
         orbsize := orbsize+1;
      end while;

      if not foundsub then
         //Orbit stabilizers wasn't satisfactory, so we'll try
         //centralizers of central elements of P -
         //We have already collected a few such elements of order p.
         elno := 1;
         while  not foundsub and elno le #centels do
            el := centels[elno];
            cent := Centralizer(H,el);
            if cent ne H and cent ne P then
              ind := Index(H,cent);
              if ind lt n then
                 //Found a suitable subgroup!!
                 H := cent;
                 Append(~seq,H);
                 foundsub := true;
                 sylind := sylind div ind;
              else  
                  //We could try the normalizer!
                  N := Normalizer(H,cent);
                  if N ne H and N ne cent then
                     ind := Index(H,N);
                     cent := N;
                     if ind lt n then
                        //Found a suitable subgroup!!
                        H := N;
                        Append(~seq,H);
                        foundsub := true;
                        sylind := sylind div ind;
                     end if;
                  end if;
                  if ind lt bestind then
                 //Not ideal, but the best we have so far, so remember it!
                     bestind := ind;  bestsub := cent;
                  end if;
              end if;
            end if;
            elno := elno+1;
         end while;
      end if;

      if not foundsub and bestind lt sylind then
         //We make do with the best one we found!
         H := bestsub;
         Append(~seq,H);
         foundsub := true;
         sylind := sylind div ind;
      end if;
   end while;

   N := Normalizer(H,P);
   if H ne N and P ne N then
     Append(~seq,N);
   end if;
   Append(~seq,P);

   badind := false;
   for i in [1..#seq-1] do
     ind := Index(seq[i],seq[i+1]);
     if ind gt 50000 then badind := true; itis := ind; end if;
   end for;

   if badind then
     print
  "#WARNING: An index in the subgroup chain found is larger than 50000:",itis;
   end if;

   return Reverse(seq);
end function;

FindSubgroupChainGrpMat:= function(G,P: n:=20 )
//version of FindSubgroupChainMat for matrix groups by using perm. rep.
  local phi, X, S;
  phi, X := PermutationRepresentation(G:ModScalars:=true);
  S := FindSubgroupChain(X,phi(P):n:=n);
  S := [s @@ phi : s in S];
  if P ne S[1] then
    Reverse(~S); Append(~S,P); Reverse(~S);
  end if;
  return S;
end function;

DCosReps := function(G,H,K)
/* H,K subgroups of permutation group G.
 * Return a list of double cosets representatives of H,K in G
 */
  local phi, P, T, cr, g;
  phi, P := CosetAction(G,H);
  if Category(G) eq GrpPerm then
    cr := [ i @@ phi : i in [Representative(o): o in Orbits(phi(K))] ];
  else
    T := Transversal(G,H);
    cr := [ T[i] : i in [Representative(o): o in Orbits(phi(K))] ];
  end if;
  return cr;
end function;

SecondCohomologyDimensionRes2 := function(G,M)
/* M should be a module over a prime field for the GrpPerm G.
 * The dimension of H^2(G,M) over GF(p) is computed by computing
 * the subgroup of stable elements of H^2(P,M) for P in Syl_p(G)
 * and returned.
 * The module record is also returned to help with diagnostics.
 */
  local CM, P, p, S, cK, H1, Hi, H2, cr, cosreps, dcosreps, ng;

  CM := MakeModuleRecordRes(G,M);
  P := CM`sylgp;
  p := CM`prime;
  if #P eq 1 then vprint ModCoho: "Trivial Sylow-subgroup"; return 0; end if;

  cK := CM`modcoho`H2;
  vprint ModCoho,1: "Dimension of H^2(P,M) =",Dimension(cK);

  vprint ModCoho,1: "Finding subgroup chain";
  if Category(G) eq GrpMat then S := FindSubgroupChainGrpMat(G,P);
  else S := FindSubgroupChain(G,P);
  end if;
  CM`subchain := S;
  vprint ModCoho,1:
       "Indices (from bottom up):", [Index(S[i+1],S[i]): i in [1..#S-1]];
  cosreps := [];
  for l in [1..#S-1] do
    H1 := S[l+1]; H2 := S[l]; //H2 < H1
    vprint ModCoho,1: "\nNext subgroup - index",Index(H1,H2);
    if l eq 1 and IsNormal(H1,H2) then 
      //Don't really need coset reps, and generators mod P will do instead of
      //double coset reps 
      cosreps[l] := {* Id(G) *};
      dcosreps := [];
      Hi := H2;
      while Hi ne H1 do
        x:=Random(H1);
        if x in Hi then continue; end if;
        Append(~dcosreps,x);
        Hi := sub<H1 | Hi,x>;
      end while;
    else
      if l lt #S-1 then
        cr := RightTransversal(H1,H2);
        cosreps[l] := {* G!x : x in cr *};
      end if;
      dcosreps := [ g^-1: g in DCosReps(H1,H2,P) ];
    end if;
    for g in dcosreps do
      if g in H2 then continue; end if; // don't need trivial rep.!
      vprint ModCoho,2: "Next double coset rep";
      ng := g;
      R := H2 meet P^ng;
      if #R mod p ne 0 then
         vprint ModCoho,2: "Trivial Sylow intersection";
         continue;
      end if;
      // We need to adjust g to get R into P.
      for m in Reverse([1..l-1]) do
        for h in cosreps[m] do
          if R^(h^-1) subset S[m] then
            R := R^(h^-1);
            ng := ng*h^-1;
            break;
          end if;
        end for;
        if not R subset S[m] then
          error "Sylow intersection error!";
        end if;
      end for;
      cK := cK meet StabilityTest2(CM,ng);
      if Dimension(cK) eq 0 then
         vprint ModCoho,1: "Dimension of H^2(H,M) = 0";
         return 0;
      end if;
    end for;
    vprint ModCoho,1: "Dimension of H^2(H,M) =",Dimension(cK);
  end for;
  return Dimension(cK);
end function;
