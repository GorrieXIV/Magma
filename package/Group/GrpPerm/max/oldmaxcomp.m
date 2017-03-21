freeze;

/*
    Part of maximal subgroups package.
    Written by Derek Holt.
*/

forward PMaxSubsH;
import "maxcomp.m": MaxSubsTF;
import "identify.m":IdentifyAlmostSimpleGroupH;
import "oddfns.m":IsHomomorphismH, PermRepAlmostSimpleGroupH,
   DirectProductWithEmbeddingsAndProjectionsH,
   IsConjugateSequencesH,PresentationSubgroupTF,SubgroupTF,
   PermutationRepresentationSumH, WreathComplementTail,
   MinimalOvergroupsH, ConjugatingElement;
//import "normconj.m": PartitionIsConjugate;

PType1Maximals := procedure(~GR,srino)
/* Find the maximal subgroups of Type 1 coming from socle factor
 * SF[socreps[srino]]. That is, those coming from maximal subgroups
 * of the corresponding almost simple group.
 */
  local G, sri, socreps, SF, Print, SA, nSF, genlist, projlist, pSQ,
        S, T, psi, N, A, msilist, newgenlist, newpreslist, newfplist,
        srit, msigens, msi, compsub, F, phi, rec, I, H, x, y, con, q,
        SQ, pSQH;
 
  G:=GR`group;
  socreps:=GR`socreps;
  SF:=GR`SF;
  SA:=GR`SA;
  genlist:=GR`genlist;
  projlist:=GR`projlist;
  Print:=GR`printlevel;
  nSF:=#SF;
  pSQ:=GR`pSQ;
  SQ := Codomain(pSQ);

  sri:=socreps[srino];
  S := SF[sri];
  if Print gt 0 then
    print "Finding Type 1 maximal subgroups for socle factor number ",sri;
  end if;
  T:=GR`transversals[srino];
  psi := GR`asembeddings[srino];
  N := Domain(psi);
  A := Codomain(psi);
  Impsi := Image(psi);
  SocImpsi := Socle(Impsi);
  Orbitsri := Orbit(Image(SA),sri);
  msilist:=GR`msints[srino];
  for subgp in msilist do
    newgenlist:=genlist;
    newpreslist:=GR`preslist;
    newfplist:=GR`fplist;
    msigens := [ g @@ psi @ projlist[sri] : g in subgp`generators ];
    if GR`presentation then
     // compute presentations of the subgroups in msilist
      msi := sub< G | msigens >;
// BEWARE - Verify needed
      msi`Order := subgp`order; // BEWARE - this is billu's addition
      if #msi le GR`smallsimplefactor then
        F,phi := FPGroup(msi);
      else
        F,phi := FPGroupStrong(msi);
	msigens := [F.i@phi : i in [1..Ngens(F)]];
      end if;
    end if;

    compsub:=[];
    for t in T do
      srit := sri^SA(t);
      newgenlist[srit]:= [ (g^t) @ projlist[srit] : g in msigens ];
        //NOTE Evaluation of projlist SLOW!
      compsub[srit]:=sub<G|newgenlist[srit]>; 
      compsub[srit]`Order := subgp`order; // BEWARE - this is billu's addition
      if GR`presentation then
// print "Type 1 pres";
        newpreslist[srit] := F;
        // DFH's code was: newfplist[srit] := hom< F->compsub[srit] | newgenlist[srit] >;
	// billu's replacement to get shorter words from @@newfplist[srit] (2 lines):
	aux := hom< F->compsub[srit] | newgenlist[srit] >;
	newfplist[srit] := hom< F->compsub[srit] | x :-> x@aux, y :-> (y^(t^-1))@@phi>;
      end if;
    end for;
    // I := sub< G | &cat(newgenlist) >;  only needed for sanity check
    // intersection of the subgroup we are computing with Soc(G)

/* DONT NEED THIS ANY MORE !
     * In the case G=Sym(n) for n>=9, a generator of the normaliser of each
     * subgroup outside of Alt(n) should have been returned with the subgroup.
     * If there is only one socle factor in this orbit, then we can use
     * this information.
     *
    if #T eq 1 and "normgen" in Names(Format(subgp)) and
                    assigned subgp`normgen then
      newgenlist[nSF+1] := [(subgp`normgen) @@ psi];
      // CORRECTION!  We also need generators outside socle that
      // centralize S.
      H := pSQ(sub<G|GR`socle,(subgp`normgen) @@ psi>);
      if H ne SQ then
        C:=Centraliser(G,S);
        while H ne SQ do
          x:=Random(C);
          if not pSQ(x) in H then
            Append(~newgenlist[nSF+1],x);
            H:=sub<SQ|H,pSQ(x)>;
          end if;
        end while;
      end if;
      if GR`presentation then
       //we have to re-calculate presentation of G/socle in this case!
        H := sub< G | newgenlist[nSF+1] >;
        pSQH := hom< H->SQ | [pSQ(g) : g in newgenlist[nSF+1]] >;
        SQH := sub< SQ | [pSQ(g) : g in newgenlist[nSF+1]] >;
        if #SQH le GR`smallsimplefactor then
           F,phi := FPGroup(SQH);
        else
           F,phi := FPGroupStrong(SQH);
        end if;
        newpreslist[nSF+1] := F;
        for i in [Ngens(SQH)+1..Ngens(F)] do
          Append(~newgenlist[nSF+1],F.i @ phi @@ pSQH);
        end for;
      end if;
    else
*/
    
    // Now we build generators of the normaliser of I in G
    // (modulo the subgroup)
    // We do this, because calling 'Normaliser' can be very slow!
      newgenlist[nSF+1] := [];
      for elt in GR`modsocgens do
          x := elt;
          //multiply x by suitable elements of socle factors until it
          //normalises I.
          symnorm := false;
          for p in Orbitsri do
            q := p^SA(x);
            if "normgen" in Names(Format(subgp)) and
                    assigned subgp`normgen then
              symnorm := true;

	      dummy := exists(tp){t: t in T | sri^SA(t) eq p}; assert dummy;
	      dummy := exists(tq){t: t in T | sri^SA(t) eq q}; assert dummy;
              yy := tq*x^-1*tp^-1;
              if not psi(yy) in SocImpsi then
                yy *:= subgp`normgen @@ psi;
              end if;
              y := (yy ^ tq) @ projlist[q];
            else
              con, y := IsConjugate(SF[q],compsub[p]^x,compsub[q]);
              if not con then
	        // SF[q], compsub[p]^x, compsub[q]:Magma;
                error "Conjugation error while calculating normaliser",
                                                              #compsub[q];
              end if;
            end if;
            x := x*y;
          end for;
	  /* BEWARE - Bill U removed this check
          if symnorm and not I^x eq I then
            error "Computed element does not normalise subgroup";
          end if;
	  */
          Append(~newgenlist[nSF+1],x);
      end for;
/*  end if; */

    rec:=rec<GR`RFG|>;
    if GR`presentation then
       rec`subgroup, rec`presentation := PresentationSubgroupTF
                            (newgenlist,newpreslist,GR`projlist,newfplist);
    else rec`subgroup := SubgroupTF(newgenlist);
    end if;
    rec`length := (#S div subgp`order)^#T;
    rec`order := #G div rec`length;
    AssertAttribute(rec`subgroup, "Order", rec`order);
    // assert not IsNormal(G,rec`subgroup);
    Append(~GR`maxsubs,rec);
    if Print gt 0 then
      print "  +Maximal subgroup of order",rec`order,
                                   "induced from almost simple group.";
      if Print gt 2 then print rec`subgroup; end if;
    end if;
  end for;
  return;
end procedure;

PType2Maximals := procedure(~GR,srino)
/* Find the maximal subgroups of Type 2 coming from socle factor
 * S = SF[socreps[srino]]. That is, those of diagonal type. They
 * correspond to homomorphisms from H/M to A/S that extend the map N/M->A/S
 * induced by psi, for all minimal overgroups H of N=N(S), where A if the
 * almost simple group associated with N. The overgroups correspond to
 * minimal block systems of P (= CosetImage(G,N)).
 */
  local G, M, sri, socreps, SF, nSF, Print, SA, projlist, rec, pSQ,
        S, T, psi, N, A, newgenlist,
        N0, A0, pA0, gensN0, imgensN0, psi0, impsi0, overgps,
        x, x0, H0, THN, indHN, TGH, TGHrep, indGH, liftpsi0, THNlift, w,
        srit, sriu, sriv, sritv, t, u, v,
        y, I, conngl1, conngl1c, connglt;
 
  G:=GR`group;
  socreps:=GR`socreps;
  SF:=GR`SF;
  SA:=GR`SA;
  pSQ:=GR`pSQ;
  projlist:=GR`projlist;
  Print:=GR`printlevel;
  nSF:=#SF;
 
  sri:=socreps[srino];
  S := SF[sri];
  if Print gt 0 then
    print
  "Finding Type 2 (diagonal) maximal subgroups for socle factor number ",sri;
  end if;
  T:=GR`transversals[srino];
  psi := GR`asembeddings[srino];
  N := Domain(psi);
  A := Codomain(psi);

  if N eq G then
    return;
  end if;
  N0 := N @ pSQ; // N/M
  A0, pA0 := quo<A|Socle(A)>;
  gensN0 := [ N0.i : i in [1..Ngens(N0)]];
  imgensN0 := [ gensN0[i] @@ pSQ @ psi @ pA0 : i in [1..#gensN0] ];
  psi0 := hom< N0->A0 | imgensN0 >;
  impsi0 := Image(psi0);
  overgps := MinimalOvergroupsH(G,N);
  if Print gt 1 then
    print "    +",#overgps, "minimal overgroups found for this socle factor.";
  end if;
  for H in overgps do
    if Print gt 1 then print
      "    +Overgroup of order",#H;
      if Print gt 2 then print H; end if;
    end if;
    x:=Id(H);
    while x in N do x:=Random(H); end while;
/* BEWARE - Bill U removed this check
"Check";
    if sub<G|N,x> ne H  then
      error "Minimal overgroup error.";
    end if;
"End check"; */
    H0 := H @ pSQ; // H/M
    x0 := x @ pSQ;
    H0 := sub <H0 | gensN0, x0>;
    if Print gt 1 then
       print "    +Extra generator:",x0;
    end if;
    // for each lifting, if any, we will need some transversal data
    THN := [t: t in T | t in H];
    indHN := #THN;
    TGH, TGHrep := RightTransversal(G,H);
    indGH := #TGH;
    // Now look for all homomorphism extensions of psi0 for this overgroup.
    for a in A0 do
      liftpsi0 := hom<H0->A0 | imgensN0 cat [a]>;
      if IsHomomorphismH(liftpsi0,imgensN0 cat [a]) then
        if Print gt 1 then
          print "    +Found a lifting. Extra generator -> ",a;
        end if;
        // Now construct the corresponding diagonal-type subgroup.
        // Again, we first find the intersection with M and then
        // compute the normaliser.
        newgenlist:=GR`genlist;
        // fplist and preslist can stay as they are for diagonals.
        THNlift := [ THN[i] @ pSQ @ liftpsi0 @@ pA0 : i in [1..indHN] ];
        for t in T do
          newgenlist[sri^SA(t)]:=[];
        end for;
        newgenlist[sri]:=[];
        for z in GR`genlist[sri] do
          w:=Id(G);
          for i in [1..#THN] do
            g:=THN[i];
            srit := sri^SA(g);
            w := w *
       (((THNlift[i] * psi(z) * THNlift[i]^-1) @@ psi)^g) @ projlist[srit];
          end for;
          Append(~newgenlist[sri],w);
          for t in TGH do if not t in H then
            Append(~newgenlist[sri^SA(t)],w^t);
          end if; end for;
        end for;

        // I := sub< G | &cat(newgenlist) >; only needed for sanity check
        // Now we build generators of the normaliser of I in G
        // (modulo the subgroup)
        // We do this, because calling 'Normaliser' can be very slow!
        newgenlist[nSF+1] := [];
        for elt in GR`modsocgens do
            x := elt;
            //multiply x by suitable elements of socle factors until it
            //normalises I.
            for i in [1..#TGH] do
              u := TGH[i];
              v := TGHrep(u*x);
              sriu := sri^SA(u);
              sriv := sri^SA(v);
              conngl1 := [ ((z^x) @ projlist[sriv])^(v^-1) :
                                                    z in newgenlist[sriu] ];
              for j in [1..#THN] do
                t:=THN[j];
                if not t in N then
                  srit := sri^SA(t);
                  sritv := sri^SA(t*v);
                  conngl1c := [ (z^x) @ projlist[sritv] :
                                                    z in newgenlist[sriu] ];
                  connglt := [
 ((((THNlift[j] * psi(z) * THNlift[j]^-1) @@ psi)^(t*v)) @ projlist[sritv]) :
                               z in conngl1 ]; 
      //print SF[srit], Universe(connglt), Universe(conngl1c);
                  con, y := IsConjugateSequencesH(SF[sritv],conngl1c,connglt);
                  if not con then
                     error "Normaliser error in Type2Maximals";
                  end if;
                  x := x * y;
                end if;
              end for;
            end for;
/* BEWARE - Bill U removed this check
"Check normalizer";
            if not I^x eq I then
              error "Computed element does not normalise subgroup";
            end if;
"Check normalizer ended";
*/
            Append(~newgenlist[nSF+1],x);
        end for;


        rec:=rec<GR`RFG|>;
        if GR`presentation then
// print "Type 2 pres";
          rec`subgroup, rec`presentation := PresentationSubgroupTF
                            (newgenlist,GR`preslist,GR`projlist,GR`fplist);
        else rec`subgroup := SubgroupTF(newgenlist);
        end if;
	rec`length := #S^(#T-#TGH);
        rec`order := #G div rec`length;
        AssertAttribute(rec`subgroup,"Order",rec`order);
	// assert not IsNormal(G,rec`subgroup);
        Append(~GR`maxsubs,rec);
        if Print gt 0 then
          print "  +Maximal subgroup of order",rec`order,
                                   "of diagonal type.";
          if Print gt 2 then print rec`subgroup; end if;
        end if;
      end if;
    end for;
  end for;
  return;
end procedure;

PType3Maximals := procedure(~GR,srino,srjno)
/* Find the maximal subgroups of Type 3 coming from socle factors
 * SF[socreps[srino]] and SF[socreps[srjno]]. That is, those that are
 * diagonals across two equivalent orbits of the socle factors.
 */
  local G, sri, socreps, SF, nSF, Print, SA, projlist, rec,
        rhoi, Wi, srj, rhoj, Wj, S, T, TR, psi, N, A, P, newgenlist,
        Imi, Qi, pQi, Mi, QImi, Imj, QImj, ei, ej, pi, pj, rhoP,
        ImP, QImigens, Qisoims, Qiso, conj, conjel, ce, zi, h, g,
        srit, srjt, x, v, sriv, srjv, conngl1, conngl1c, connglt, I;
 
  G:=GR`group;
  socreps:=GR`socreps;
  SF:=GR`SF;
  SA:=GR`SA;
  projlist:=GR`projlist;
  Print:=GR`printlevel;
  nSF:=#SF;
  sri:=socreps[srino];
  srj:=socreps[srjno];

  if Print gt 0 then
    print
   "Finding Type 3 (2-orbit diagonal) maximal subgroups for socle factors",
     sri,"and",srj;
  end if;

  S := SF[sri];
  rhoi := GR`wpembeddings[srino][1];
  Wi := Codomain(rhoi);
  Imi := Image(rhoi);
  Qi, pQi, Mi := SocleQuotient(Wi);
  QImi := pQi(Imi);
  psi := GR`asembeddings[srino];
  A := Codomain(psi);
  T, TR := Transversal(G,Domain(psi));
  rhoj := GR`wpembeddings[srjno][1];
  Wj := Codomain(rhoj);
  if Wi cmpne Wj then
    return; // socle orbits are inequivalent.
  end if;
  Imj := Image(rhoj);
  if #Imi ne #Imj then
    return; // socle orbits are inequivalent.
  end if;
  QImj := pQi(Imj);
  if Print gt 1 then
    print "    +Orbits of Socle factors ",sri,"and",srj, "could be equivalent.";
  end if;
  // Construct the diagonal of the two embeddings.
  P, ei, ej, pi, pj := DirectProductWithEmbeddingsAndProjectionsH(Wi,Wj);
  rhoP := hom< G->P | [ ei(rhoi(G.k))*ej(rhoj(G.k)) : k in [1..Ngens(G)]]>;
  ImP := Image(rhoP);
  if #ImP div #Socle(ImP) ne #QImi then
    if Print gt 1 then
      print "    +Embedding is not diagonal - orbits are inequivalent.";
    end if;
    return;
  end if;
  // Construct the induced isomorphism from Qi to Qj
  QImigens := [Qi| QImi.k : k in [1..Ngens(QImi)] ];
  Qisoims :=  [Qi| q @@ pQi @@ rhoi @ rhoP @ pj @ pQi : q in QImigens ];
  Qiso := hom< QImi->QImj | Qisoims >;
  if not IsHomomorphismH(Qiso,Qisoims) or Image(Qiso) ne QImj then
    error "Induced isomorphism QImi->QImj incorrect.";
  end if;
  conj, conjel := IsConjugateSequencesH(Qi,QImigens,Qisoims);
  if not conj then
    if Print gt 1 then
      print
  "    +Diagonal embedding induce no isomorphism - orbits are inequivalent.";
    end if;
    return;
  end if;
  for c in Centraliser(Qi,QImj) do
    ce := (conjel * c) @@ pQi;
    newgenlist:=GR`genlist;
    // as usual we construct the generators of the intersection of
    // the maximal with Socle(G) - first find the images of these
    // generators in P.
    h := Representative({t: t in T | rhoi(S)^(ce^-1) eq rhoi(S^t)});
    //Now socle factor sri corresponds to srj^SA(h^-1) in the isomorphism
    //between orbit of sri and orbit of srj.
    for t in T do
      srit := sri^SA(t);
      srjt := srj^SA(h^-1*t);
      newgenlist[srit]:=[]; 
      newgenlist[srjt]:=[]; 
      for z in GR`genlist[srit] do
        zi := z @ rhoi;
        //g := (ei(zi) @@ rhoP @ projlist[srit]) *
        //    (ej(zi^ce) @@ rhoP @ projlist[srjt]);
        g := (z @ projlist[srit]) * ((zi^ce) @@ rhoj @ projlist[srjt]);
        Append(~newgenlist[srit],g);
      end for;
    end for;
    // I := sub< G | &cat(newgenlist) >; only needed for sanity check
    // Now we build generators of the normaliser of I in G
    // (modulo the subgroup)
    // We do this, because calling 'Normaliser' can be very slow!
    newgenlist[nSF+1] := [];
    for elt in GR`modsocgens do
        x := elt;
        //multiply x by suitable elements of socle factors until it
        //normalises I.
        for t in T do
          srit := sri^SA(t);
          srjt := srj^SA(h^-1*t);
          v := TR(t*x);
          sriv := sri^SA(v);
          srjv := srj^SA(h^-1*v);
          conngl1  := [ (z^x) @ projlist[sriv] : z in newgenlist[srit] ];
          conngl1c := [ (z^x) @ projlist[srjv] : z in newgenlist[srit] ];
          //connglt  := [ ej((z @ rhoi)^ce) @@ rhoP @ projlist[srjv] :
           //                                               z in conngl1 ];
          connglt  := [ ((z @ rhoi)^ce) @@ rhoj @ projlist[srjv] :
                                                         z in conngl1 ];
          con, y := IsConjugateSequencesH(SF[srjv],conngl1c,connglt);
          if not con then
             error "Normaliser error in Type3Maximals";
          end if;
          x := x * y;
        end for;
	/* BEWARE - Bill U removed this check
        if not I^x eq I then
          error "Computed element does not normalise subgroup";
        end if;
	*/
        Append(~newgenlist[nSF+1],x);
    end for;

    rec:=rec<GR`RFG|>;
    if GR`presentation then
// print "Type 3 pres";
       rec`subgroup, rec`presentation := PresentationSubgroupTF
                         (newgenlist,GR`preslist,GR`projlist,GR`fplist);
    else rec`subgroup := SubgroupTF(newgenlist);
    end if;
    rec`length := #S^#T;
    rec`order := #G div rec`length;
    AssertAttribute(rec`subgroup,"Order",rec`order);
    // assert not IsNormal(G,rec`subgroup);
    Append(~GR`maxsubs,rec);
    if Print gt 0 then
      print "  +Maximal subgroup of order",rec`order, "2-orbit diagonal.";
      if Print gt 2 then print rec`subgroup; end if;
    end if;
  end for;
  return;
end procedure;

PType4Maximals := procedure(~GR,srino)
/* Find the maximal subgroups of Type 4 coming from socle factor
 * S = SF[socreps[srino]]. That is, those of twisted wreath product type.
 * They are certain types of complements of the base group in the
 * wreath product, so the computation will be carried out in the image
 * of the wreath product embedding.
 */
  local rho, W, G, eG, A, B, BG, M, SA, SB, SBG, NWA, CWA, NA, CA, pSA, SQ, pSQ,
        pNQ, NQ, T, pT, Comps, C, Ggens, Cgens, Qgens, Cgen, t, u, tail, rec,
        E, D, DT, ims, overgps, gensA, gensCWA, gensD, x, extends, NWAn,
        newgenlist, nSF, sri, ct, CSA;

 
  Print:=GR`printlevel;
  if Print gt 0 then
    print
   "Finding Type 4 (twisted wreath-type) maximal subgroups for socle factor",
     GR`socreps[srino];
  end if;
 
  rho := GR`wpembeddings[srino][1];

  if GR`presentation then
// print "Type 4 pres";
    nSF:= #GR`SF;
    newgenlist:=GR`genlist;
    sri:=(GR`socreps)[srino];
    T:=GR`transversals[srino];
    for t in T do
       newgenlist[sri^(GR`SA)(t)]:=[];
    end for;
  end if;

  W := Codomain(rho);
  G := Image(rho);
  eG := GR`wpembeddings[srino][2];
  A := Image(eG[1]); // term of base group.
  B := sub < W | [Image(eG[i]) : i in [2..#eG]] >; //Base group = A x B.
  AssertAttribute(B,"Order",#A^(#eG-1));
  RandomSchreier(B);
  BG := sub < W | A,B >;
  AssertAttribute(BG,"Order",#A^#eG);
  RandomSchreier(BG);
  SBG := BG meet G;
  if SBG ne Socle(BG) then
    if Print gt 1 then
      print "  +This is not a twisted wreath product of a simple group.";
    end if;
    return;
  end if;
  
  // SA := A meet G; Bill U change 
  SA := A meet SBG;
  
  // SB := B meet G; Bill U change 
  SB := B meet SBG;

  // NWA := Normaliser(W,A); Bill U change - many extra lines 
  // to avoid the call to Normaliser
  // Compute Normaliser(W,A) as stabilizer of point in conjugation action
  // First set up the conj action
  factors := [Image(eG[i]) : i in [1..#eG]];
  fac_reps := [Generic(W)|];
  for i := 1 to #factors do
    fl := exists(x){x:x in Generators(factors[i]) | not IsIdentity(x)};
    assert fl;
    Append(~fac_reps, x);
  end for;
  S := Sym(#factors);
  ims := [S|];
  for i := 1 to Ngens(W) do
    im := [];
    for j := 1 to #factors do
	x := fac_reps[j]^W.i;
	fl := exists(k){k: k in [1..#factors] | x in factors[k]};
	assert fl;
	im[j] := k;
    end for;
    Append(~ims, im);
  end for;
  Wact := hom<W->S| ims>; // action of W, by conjugation, on factors
  // and now get the normaliser
  NWA := Stabilizer(Image(Wact), 1) @@ Wact;
  // end Bill U change
  
  // CWA := Centraliser(W,A); Bill U change 
  CWA := Centraliser(NWA, A);

  // NA := NWA meet G; Bill U change
  // Another normaliser by stabiliser of point.
  // NA is Normaliser(G,A)
  Gact := hom<G->S | [G.i @ Wact : i in [1..Ngens(G)]]>;
  NA := Stabilizer(Image(Gact), 1) @@ Gact;
  // end Bill U change

  // CA := CWA meet G; Bill U change
  CA := CWA meet NA;
 
  // NWA = CWA X A, so we will use this fact to get a perm. rep. of NA/(SB)
  gensA := [A.i : i in [1..Ngens(A)]];
  gensCWA := [CWA.i : i in [1..Ngens(CWA)]];
  NWAn := sub < W | gensA cat gensCWA >;
 
  // Once we are happy that all is well with NWA, A, and CWA, we should
  // replace the following if statement by
  // NWAn`Order := #NWA;
  if NWA ne NWAn then
    error "Normaliser generation error in Type4Maximals";
  end if;
  NWA := NWAn;
  pSA1 := hom < NWA->A | gensA cat [Id(A): i in [1..Ngens(CWA)]] >;
                                              //projection of NWA onto A.
  pSA := hom < NA->A | a:->pSA1(a) >; //restriction to NA.
  SQ, pSQ := SocleQuotient(NA);
  pNQ, NQ := PermutationRepresentationSumH(NA,[pSA,pSQ]);
  if #NQ ne Index(NA,SB) then
    error "Normaliser perm. rep. error in Type4Maximals";
  end if; 

  T,pT:=Transversal(G,NA);
  /* We only want the maximal complements, so the following is inefficient:
   * Comps := Complements(NQ,pNQ(SA));
   * Go via maximal subgroups instead!
   */

  Comps := MaximalSubgroups(NQ);
  Comps := [m`subgroup : m in Comps | m`order eq Index(NQ,pNQ(SA)) and
                         #(m`subgroup meet pNQ(SA)) eq 1];
  // get some generators of G mod SBG.
  Qgens := [ rho(elt) : elt in GR`modsocgens | rho(elt) ne Id(G) ];
  for comp in Comps do
    C := comp @@ pNQ;
    // extend this complement to a complement of SBG in G.
    // This might be maximal.

    // Next lines Bill U change to get rid of WreathComplementTail call,
    // which makes far too many RandomSchreier calls.
    pCdom := sub < G | [C.i : i in [1..Ngens(C)]] cat
					[SA.i : i in [1..Ngens(SA)]]>;
    pCdom`Order := #C * #SA;
    pC := hom < pCdom -> C | [C.i : i in [1..Ngens(C)]] cat
                                        [Id(C) : i in [1..Ngens(SA) ]]>;
    // end Bill U change
    Cgens:=[];
    for g in Qgens do
      Cgen := g;
      for t in T do
        u := pT(t*g);
        // tail := WreathComplementTail(G,SA,SB,C,t*g*u^-1); Bill U change
	tail := pSA1(pC(x)^-1 * x) where x := t*g*u^-1;
        Cgen := Cgen * (tail^-1)^u;
      end for;
      Append(~Cgens,Cgen);
    end for;
    E := sub< G | Cgens >;
    if #E ne Index(G,SBG) then
      error "Bad complement construction in Type4Maximals";
    end if;
    if Print gt 1 then
      print "  +Have a complement in wreath product";
    end if;

    D := E meet NA;
    // now set up the conjugation map D->Aut(A)=A 
    ims :=[];
    gensD := [ D.i : i in [1..Ngens(D)] ];
    for d in gensD do
      Append(~ims,ConjugatingElement(A,d));
        // element of A inducing same action on A as d
    end for;
    if not SA subset sub<A|ims> then
      //image subset does not contain Inn(SA) so E is not maximal.
      if Print gt 1 then
        print "  +Image does not contain Inn(A) - complement not maximal.";
      end if;
      continue;
    end if;
    // We now have to check whether the homomorphism D->A defined above
    // extends to a homomorphism DE -> A for any DE with D < DE <= E.
    // If so then E is not maximal.
    // We use a brute force check for this, except that we check that
    // SA is at least a composition factor of the overgroup.
    CSA := CompositionFactors(SA);
    if not #CSA eq 1 then error "SA not simple"; end if;
    overgps:=MinimalOvergroupsH(E,D);
    for H in overgps do
      if Position(CompositionFactors(H),CSA[1]) eq 0 then
        extends := false;
        continue;
      end if;
      t:=Random(H);
      while t in D do t:=Random(H); end while;
      DE := sub< E|gensD cat [t]>;
      extends := false;
      for a in A do
        if IsHomomorphismH( hom< DE->A | ims cat [a] >, ims cat [a] ) then
          if Print gt 1 then
            print
     "  +Homomorphism to Aut(SA) extends - complement not maximal.";
          end if;
          extends:=true;
          break;
        end if;
      end for;
      if extends then
        break;
      end if;
    end for;
    if extends then
      continue;
    end if;
    rec:=rec<GR`RFG|>;
    if GR`presentation then
       ct:=0;
       newgenlist[nSF+1] := [];
       for g in GR`modsocgens do
         if rho(g) eq Id(G) then
           Append(~newgenlist[nSF+1],g);
         else
           ct +:= 1;
           Append(~newgenlist[nSF+1],(E.ct)@@rho);
         end if;
       end for;
       rec`subgroup, rec`presentation := PresentationSubgroupTF
                         (newgenlist,GR`preslist,GR`projlist,GR`fplist);
    else rec`subgroup := E @@ rho;
    end if;
    rec`order:=#rec`subgroup; 
    // assert not IsNormal(GR`group, rec`subgroup);
    rec`length:= Index(GR`group,rec`subgroup);
    Append(~GR`maxsubs,rec);
    if Print gt 0 then
      print "  +Maximal subgroup of order",rec`order, "twisted wreath type.";
      if Print gt 2 then print rec`subgroup; end if;
    end if;
  end for;
  return;
end procedure;

PType5Maximals:=procedure(~GR)
/* Find maximal subgroups containing the socle, including the whole group. */
  local G, SF, nSF, pSQ, SQ, S, ms, newgenlist, rec, Print;

  G:=GR`group;
  SF:=GR`SF;
  pSQ:=GR`pSQ;
  SQ:=Image(pSQ);
  pSQ:=GR`pSQ;
  nSF:=#SF;
  newgenlist:=GR`genlist;
  newpreslist:=GR`preslist;
  Print:=GR`printlevel;

  if Print gt 0 then
    print "Finding Type 5 maximal subgroups - those containing the socle.";
  end if;
  if #SQ ne 1 then
    S := MaximalSubgroupsH(SQ,sub<SQ|>:
                            Presentation:=GR`presentation,Print:=Print);
    for m in S do
      rec:=rec<GR`RFG|>;
      ms := m`subgroup;
      if GR`presentation then
// print "Type 5 pres";
        newpreslist[nSF+1] := m`presentation;
        newgenlist[nSF+1] :=
                    [g@@pSQ : g in [ms.i : i in [1..Ngens(ms)]]];
        rec`subgroup, rec`presentation := PresentationSubgroupTF
                            (newgenlist,newpreslist,GR`projlist,GR`fplist);
      else rec`subgroup := ms@@pSQ;
      end if;
      rec`order := #G div Index(SQ,m`subgroup);
      AssertAttribute(rec`subgroup,"Order",rec`order);
      rec`length:=m`length;
      Append(~GR`maxsubs,rec);
      if Print gt 0 then
        print "  +Maximal subgroup of order",rec`order, "containing socle.";
        if Print gt 2 then print rec`subgroup; end if;
      end if;
    end for;
  end if;

// finally do G.
  if not GR`trivrad then
    newgenlist[nSF+1] := GR`modsocgens;
    rec:=rec<GR`RFG|>;
    rec`subgroup, rec`presentation := PresentationSubgroupTF
                            (newgenlist,GR`preslist,GR`projlist,GR`fplist);
    rec`order:=#G; 
    rec`length:=1;
    Append(~GR`maxsubs,rec);
    if Print gt 0 then
      print "  +Full group of order",rec`order;
      if Print gt 2 then print rec`subgroup; end if;
    end if;
  end if;
  return;
end procedure;

PMaxSubsH :=
    function(G,N:Print:=0,SSF:=5000,maxind:=0,radprimes:={},Presentation:=false)
/* Find maximal subgroups of G modulo the soluble normal subgroup N.
 * Use MaximalSubgroupsTF on the radical quotient where necessary.
 * If maxind ne 0 then return only subgroups of index at most maxind
 */
  local L, Q, pQ, M, MM, mm, s, ss, Res;

  if #G eq 1 then return []; end if;

  L:=ElementaryAbelianSeries(G,N);

  Q, pQ := RadicalQuotient(G);

  M := MaxSubsTF(Q,sub<Q|>:Print:=Print,SSF:=SSF,TrivRad:= (#Q eq #G),
            maxind:=maxind,radprimes:=radprimes,Presentation:=Presentation);
  if Print gt 1 then
    print #M,"subgroups of radical quotient found";
  end if;

  if Presentation then
    MM := [];
    for m in M do
      s := m`subgroup;
      mm := m;
      mm`subgroup := sub<G | [s.i @@ pQ : i in [1..Ngens(s)]] >;
      Append(~MM,mm);
    end for;
  else
    MM := [];
    Res := [];
    for m in M do
      mm := m;
      s := m`subgroup;
      if s eq Q then
  	mm`subgroup := sub<G | [s.i @@ pQ : i in [1..Ngens(s)]] >;
  	Append(~MM,mm);
      else
        ss := s @@ pQ;
        ReduceGenerators(~ss);
  	mm`subgroup := ss;
  	mm`order *:= #Radical(G);
  	Append(~Res,mm);
      end if;
    end for;
  end if;

  for i in [1..#L-1] do
    if Presentation then
      M := SubgroupsLift(G,L[i],L[i+1],MM:Al:="Maximal",Presentation:=true);
      MM := M;
    else
      assert #MM eq 1;
      M := SubgroupsLift(G,L[i],L[i+1],MM:Al:="Maximal",Presentation:=false);
      if Print gt 1 then
        print #M,"subgroups after lifting through layer", i;
      end if;
      MM := [];
      for m in M do
  	mm := m;
  	if m`order * #L[i+1]  eq #G then
  	    Append(~MM, mm);
  	else
          s := sub<G|m`subgroup,L[i+1]>;
          if maxind eq 0 or Index(G,s) le maxind then
            ReduceGenerators(~s);
            mm`subgroup := s;
            mm`order *:= #L[i+1];
            if assigned mm`presentation then delete mm`presentation; end if;
            Append(~Res, mm);
          end if;
  	end if;
      end for;
    end if;
  end for;

  if Presentation then
    if maxind ne 0 then
      return [m : m in MM | Index(G,m`subgroup) le maxind];
    end if;
    return MM;
  else
    return Res;
  end if;

end function;
