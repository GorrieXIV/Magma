freeze;

import "oddfns.m":  AutExtensionH;
import "oddfns.m":  CalculateOldIsomH;
import "oddfns.m":  InverseImageGRH;
import "oddfns.m":  IsIsomModH;
import "oddfns.m":  IsIsomHtoGModH;
import "oddfns.m":  IsomExtensionHtoGH;

EASectionCentraliser := function(G, H, K)
  local M, d, F, phi;
   if Type(G) eq GrpPC then
     M, phi := quo< G | K >;
     return Centraliser(M, phi(H)) @@ phi;
   end if;
   M := GModule(G,H,K);
   d := Dimension(M); F := BaseRing(M);
   phi := Representation(M);
   phi := hom< G-> GL(d,F) | [ phi(G.i) : i in [1..Ngens(G)]] >;
   return Kernel(phi);
end function;

PermRepOutAutGpH := procedure(~HR,~GR,level,isomims)
/* Find a suitable permutation representation of the
 * old outer automorphism group.
 * HR and isomims are only used when isomorphism testing.
 */
  local quotorder, F, A, nfg, nag, ims, FH, Hrels, H, FHtoH, FtoFH, AtoFH,
        X, FtoX, HtoP, P, Q, N, R, QtoR, Rgens, O,
        w, pt, G, newgens, Hnewgens, dm, drophom, ON, Rperms, HtoG, HH, ctproc;
  /* first work out order of GR`permgroup/subseries[level */
  quotorder := GR`radindex;
  for i in [1..level-1] do
    quotorder *:= GR`index[i];
  end for;
  if GR`printlevel gt 1 then
    print "    +Choosing a perm. rep. for previous outer automorphism group";
    print "    +Order of previous quotient group is",quotorder;
  end if;
  if GR`orderouterautgroup lt GR`smallouterautgroup or
     GR`orderouterautgroup lt quotorder then
   // use regular perm. rep.
//"diag",GR`orderouterautgroup,GR`smallouterautgroup,quotorder;
    if GR`printlevel gt 1 then
      print "    +Using regular action for the search";
    end if;
    ctproc := CosetEnumerationProcess(GR`outerautgroup, sub<GR`outerautgroup|> :
                       CosetLimit := Max(1000000,2*GR`orderouterautgroup) );
    StartEnumeration(~ctproc);
    if not HasValidIndex(ctproc) then
      error "Index too large for coset enumeration - giving up.";
    end if;
//  GR`holmap := CosetAction(GR`outerautgroup, sub<GR`outerautgroup|>);
    GR`holmap := CosetAction(ctproc);
    GR`holgens := [ (GR`outerautgroup).i @ GR`holmap :
                           i in [1..Ngens(GR`outerautgroup)] ];
    return;
  else
   // Form a perm. action using the holomorph at previous level.
    F:=GR`oldfpgroup;
    A:=GR`autgroup;
    ims:=GR`oldoutimages;
    nfg:=Ngens(F);
    nag:=Ngens(A);
    FH:=FreeGroup(nfg+nag);
    FtoFH:=hom<F->FH | [FH.i : i in [1..nfg] ]>;
    AtoFH:=hom<A->FH | [FH.(nfg+i) : i in [1..nag] ]>;
    Hrels := [r@FtoFH : r in Relations(F)] cat [r@AtoFH : r in Relations(A)];
    /* We also want relations for action of A on F */
    for i in [1..nfg] do for j in [1..nfg] do
      Append(~Hrels, FH.j^FH.(i+nfg) = FH.j^FH.i);
    end for; end for;
    for i in [1..nag-nfg] do for j in [1..nfg] do
      Append(~Hrels, FH.j^FH.(i+nfg+nfg) = ims[i][j]@FtoFH );
    end for; end for;

    H,FHtoH := quo<FH|Hrels>;
    ctproc := CosetEnumerationProcess(H, sub<H|[H.i : i in [nfg+1..nfg+nag] ]> :
                       CosetLimit := 2000000 );
    StartEnumeration(~ctproc);
    if not HasValidIndex(ctproc) then
      error "Index too large for coset enumeration - giving up.";
    end if;
    //HtoP := CosetAction(H,sub<H | [H.i : i in [nfg+1..nfg+nag] ]>);
    HtoP := CosetAction(ctproc);
    P := Image (HtoP);
    Q := sub<P | [(H.i)@HtoP : i in [nfg+1..nfg+nag] ]>;
    N := sub<P | [(H.i)@HtoP : i in [nfg+1..2*nfg] ]>;
    /* Now Q is isomorphic to the old aut.gp. and N the inner aut. gp.
     * Form the outer aut.gp. by taking action of Q on orbits of N and
     * hope that it is faithful!
     */
    O := Orbits(N);
    O := [ Set(o) : o in O ];
    Rgens := [];
    for i in [1..Ngens(Q)] do
      Rgens[i] := [ Position(O,O[j]^Q.i) : j in [1..#O] ];
    end for;
    R := sub< Sym(#O) | Rgens >;
    QtoR := hom< Q-> R | Rgens >;
    if #R eq GR`orderouterautgroup then
      if GR`printlevel gt 1 then
        print "    +Using holomorph action for search.",
              "Degree is",Degree(R);
      end if;
      /* Now we define some fields to enable us to identify the elements in
       * GR`permgroup and GR`oldfpgroup that correspond to the points being
       * permuted by the holomorph H.
       */
      GR`holmap:=QtoR;
      GR`holgens:= [ (H.i)@HtoP@QtoR : i in [2*nfg+1..nfg+nag] ];
      GR`holperm:=[]; GR`holword:=[];
      GR`gpholpt:=[]; GR`newgpholpt:=[];
      FtoX := CosetAction(F,sub<F|>);
      X := Image(FtoX);
      for el in X do
        w:= el@@FtoX;
        pt :=  1 ^ (w @ FtoFH @ FHtoH @ HtoP);
        GR`holword[pt] := w;
        GR`holperm[pt] := w @ GR`oldfptoperm;
      end for;
      dm := Dimension(GR`layermod[level]);
      drophom := hom< GR`fpgroup->F | [F.i : i in [1..nfg]] cat
                                      [Id(F) : i in [1..dm] ] >;
      G := GR`permgroup;
      for i in [1..Ngens(G)] do
        w := InverseImageGRH(GR,G.i,level-1)@drophom;
        GR`gpholpt[i] := 1 ^ (w @ FtoFH @ FHtoH @ HtoP);
      end for;
      G := GR`newgroup;
      newgens := GR`newgens;
      for i in [1..nfg] do
        w := InverseImageGRH(GR,newgens[i],level-1)@drophom;
        GR`newgpholpt[i] := 1 ^ (w @ FtoFH @ FHtoH @ HtoP);
      end for;
      if #isomims ne 0 then
       // for isomorphism testing we need corresponding data from isomims
        GR`imholpt:=[]; GR`newimholpt:=[];
        H:=HR`newgroup;
        Hnewgens := HR`newgens;
        G:=GR`newgroup;
        newgens := GR`newgens;
        HtoG := hom< H->G |
            [Hnewgens[i]->GR`oldfptoperm(isomims[i]) : i in [1..#isomims]] cat
            [Hnewgens[i]->Id(G) : i in [nfg+1..#Hnewgens]] : Check:=false >;
        HH:=HR`permgroup;
        for i in [1..Ngens(HH)] do
          w := InverseImageGRH(GR,HtoG(HH.i),level-1)@drophom;
          GR`imholpt[i] := 1 ^ (w @ FtoFH @ FHtoH @ HtoP);
        end for;
        for i in [1..nfg] do
          w := isomims[i];
          GR`newimholpt[i] := 1 ^ (w @ FtoFH @ FHtoH @ HtoP);
        end for;
      end if;
      return;
    else
      // use regular perm. rep.
       if GR`printlevel gt 1 then
         print "    +Using regular action for search";
       end if;
       ctproc :=
            CosetEnumerationProcess(GR`outerautgroup, sub<GR`outerautgroup|> :
                       CosetLimit := Max(1000000,2*GR`orderouterautgroup) );
       StartEnumeration(~ctproc);
       if not HasValidIndex(ctproc) then
         error "Index too large for coset enumeration - giving up.";
       end if;
//     GR`holmap := CosetAction(GR`outerautgroup, sub<GR`outerautgroup|>);
       GR`holmap := CosetAction(ctproc);
       GR`holgens := [ (GR`outerautgroup).i @ GR`holmap :
                           i in [1..Ngens(GR`outerautgroup)] ];
       return;
    end if;
  end if;

end procedure;

SeqToMatH := function(m)
/* m should be a sequence of length d in of elements in a d-dimensional
 * module forming a basis of that module.
 * The corresponding invertible matrix is computed.
 */
  local d, F, s;
  d:=Dimension(Parent(m[1]));
  F:=BaseRing(Parent(m[1]));
  s:=ElementToSequence(m[1]);
  for i in [2..d] do
    s := s cat ElementToSequence(m[i]);
  end for;
  return MatrixAlgebra(F,d)!s;
end function;
  
FindLiftingOutAutsH := procedure(~GR,level,outgp,subgens)
/* outgp should be a permutation group isomorphic to the outer
 * automorphism group at the previous level. We search through this
 * group generating its subgroup of automorphisms that lift to outer
 * automorphisms modulo the next level. This involves a backtrack
 * search in the permutation group. subgens generate a subgroup
 * already known to lift.
 */
local Z, F, oldF, G, newgens, m, V, dm, K, bigger, suboutgp, oivwm, ogivwm,
      cands, havecands, conj, el, giso, isiso, iso,
      genims, newgenims, nfg, drophom, lifthom, w,
      nb, stabchain, borbit, index, btlevel, cp, cpind, substab,
      fm, im, bopt, OGBase, ImOGBase, sct,
      deg, reject, haverejects, rejectim, stabtrans,
      XSet, XSeq, holmap, holperm, holword, gpholpt, newgpholpt, ims, iel,
      FPmap,
      calcmodaut, cent, seccent, seccentgen, genct, nogood,
      generatingrelnos, modrelgens, modrelgensmatinv, rv, rvi,
      oldFaut, rels, rel, relim, imrelgens, imrelgensmat;

  Z := Integers();
  F := GR`fpgroup;
  oldF := GR`oldfpgroup;
  G := GR`newgroup;
  newgens := GR`newgens;
  nfg := GR`quotgens[level];
  m := GR`layermod[level];
  dm := Dimension(m);
  K := BaseRing(m);
  suboutgp := sub<outgp|subgens>;
  drophom := hom< F->oldF | [oldF.i : i in [1..nfg]]
                                cat [Id(oldF) : i in [1..dm] ] >;
  lifthom := hom< oldF->F | [F.i : i in [1..nfg]] >;
  deg:=Degree(outgp);
/* If GR`subseries[level] is central in G modulo GR`subseries[level+1],
 * the extension is nonsplit, and #GR`modaut>1, then we can calculate
 * the module automorphism induced by the outer automorphism being tested
 * for lifting, rather than trying all possibilities.
 */
  cent := sub < G | GR`centre @ GR`fptoperm, GR`subseries[level+1] >;
  seccent := EASectionCentraliser(G,GR`subseries[level],GR`subseries[level+1]);
  seccentgen := [ newgens[i] in seccent : i in [1..nfg] ]; 
  calcmodaut :=  #GR`modaut gt GR`verysmallmodaut and not GR`split;
  if calcmodaut and GR`printlevel gt 1 then
    print "  +Will try to compute induced module automorphisms.";
  end if;
  if calcmodaut then
    /* We first find a subset of GR`relvals that generates m.
     * The corresponding relators of GR`oldfpgroup will be used to
     * calculate the induced module automorphism.
     */
    rels := Relations(oldF);
    generatingrelnos:=[];
    modrelgens:=[];
    rv:=GR`relvals;
    V:=VectorSpace(m);
    for i in [1..#rv] do
      rel := ElementToSequence(LHS(rels[i])*RHS(rels[i])^-1);
      genct := [ K!0 : i in [1..nfg] ];
      nogood:=false;
      for i in rel do
        if not seccentgen[Abs(i)] then
          nogood:=true;
          break;
        end if;
        if i gt 0 then genct[i]+:=1;
          else genct[-i]-:=1; 
        end if;
      end for;
      nogood := nogood or genct ne [ K!0 : i in [1..nfg] ];
      if nogood then
        continue;
      end if;
      rvi := V!(Eltseq(rv[i]));
      if not rvi in sub<V|modrelgens> then
        Append(~modrelgens,rvi);
        Append(~generatingrelnos,i);
        if sub<V|modrelgens> eq V then
          break;
        end if;
      end if;
    end for;
    if #modrelgens eq dm then
      modrelgensmatinv := SeqToMatH(modrelgens)^-1;
    else
      if GR`printlevel gt 1 then
        print "  +Cannot compute induced module automorphisms.";
      end if;
      calcmodaut:=false;
    end if;
    if GR`printlevel gt 1 then
      print "  +Generating reln. numbers are: ",generatingrelnos;
    end if;
  end if;

/* The code for the case where outgp acts regularly is much simpler, so we
 * handle it separately.
 */
  if IsRegular(outgp) then
    if GR`printlevel gt 1 then
      print "    +Starting search for lifting automorphisms";
      print "    +Lifting subgroup has order",#suboutgp;
    end if;
    cands := [ Minimum(o) : o in Orbits(suboutgp) ];
    reject:=[];
    haverejects:=false;
    sct:=0; //for diagnostic use only
    for i in [2..deg] do
      if not i in cands  then
        continue;
      end if;
      _,el := IsConjugate(outgp,1,i);
      sct+:=1;
      if GR`printlevel gt 2 and sct mod GR`printsct eq 0 then
         print "      +search count =",sct;
      end if;
      if haverejects then
        rejectim:=false;
        for j in Orbit(sub<outgp|el>,1) do
          if Minimum(Orbit(suboutgp,j)) in reject then
             rejectim:=true;
             break;
          end if;
        end for;
        if rejectim then
          Append(~reject,i);
          continue;
        end if;
      end if;
      giso := CalculateOldIsomH(GR,el@@GR`holmap);
      ims := [((GR`permgroup).j) @ giso : j in [1..Ngens(GR`permgroup)] ];
      isiso, iso := IsIsomModH(GR,ims,level);
      bigger:=false;
      if isiso then
        if GR`split then
           genims:=[ InverseImageGRH(GR,newgens[i]@giso,level-1):
                                                       i in [1..nfg]];
           bigger:=true;
        else
          genims:=[ InverseImageGRH(GR,newgens[i]@giso,level-1)@drophom :
                                                       i in [1..nfg]];
          if calcmodaut then
            oldFaut := hom<oldF->oldF | genims>;
            imrelgens:=[];
            for i in generatingrelnos do
              rel := LHS(rels[i])*RHS(rels[i])^-1;
              relim:= rel @ oldFaut @ GR`oldfptoperm @ GR`layermap[level]; 
              Append(~imrelgens,relim);
            end for;
            imrelgensmat := SeqToMatH(imrelgens);
            if IsUnit(imrelgensmat) then
              iso := modrelgensmatinv*imrelgensmat;
              bigger, newgenims := AutExtensionH(GR,genims,iso,level);
              if bigger then
                genims:=newgenims;
              end if;
            else
              bigger:=false;
            end if;
          else
            for g in GR`modaut do
              bigger, newgenims := AutExtensionH(GR,genims,g*iso,level);
              if bigger then
                genims:=newgenims;
                iso := g*iso;
                break;
              end if;
            end for;
          end if;
        end if;
      end if;
      if bigger then
        for j in [1..dm] do
          w:=Id(F);
          for k in [1..dm] do
            w := w * (F.(nfg+k))^(Z!iso[j][k]);
          end for;
          Append(~genims,w);
        end for;
        Append(~GR`outimages,genims);
        Append(~subgens,el);
        suboutgp:=sub<outgp|subgens>;
        if GR`printlevel gt 1 then
          print "    +Lifting subgroup now has order",#suboutgp;
        end if;
        cands := [ Minimum(o) : o in Orbits(suboutgp) ];
      else
        haverejects:=true;
        Append(~reject,i);
      end if;
    end for;

    GR`liftoutaut := FPGroup(suboutgp);
    GR`orderliftoutaut := #suboutgp;
    if IsSoluble(suboutgp) then
      if GR`split then
        GR`soluble:=IsSoluble(GR`modaut);
      else
        GR`soluble:=true;
      end if;
    else
      GR`soluble:=false;
    end if;
    if GR`printlevel gt 1 then
      print "  +Subgroup of lifting outer automorphisms has order",#suboutgp;
    end if;
    return;
  end if;

/* First work out indices and transversals for the stabiliser chain */
  if GR`printlevel gt 1 then
    print "    +Calculating indices, basic orbits and transversals.";
  end if;
  OGBase:=Base(outgp);
  nb:=#OGBase;
  stabchain := []; borbit:=[]; index:=[];
  stabtrans:=[];
  for i in [1..nb] do
    stabchain[i] := Stabiliser(outgp,[OGBase[j]:j in [1..i-1]]);
    borbit[i] := [k: k in Orbit(stabchain[i],OGBase[i])];
    /* We want the base point to come first though! */
    p:=Position(borbit[i],OGBase[i]);
    if p ne 1 then
      borbit[i][p]:=borbit[i][1]; borbit[i][1]:=OGBase[i];
    end if;
    stabtrans[i]:=[];
    for j in [1..#borbit[i]] do
      bopt:=borbit[i][j];
      _,el:=IsConjugate(stabchain[i],OGBase[i],bopt);
      stabtrans[i][j]:=el;
    end for;
  end for;
  stabchain[nb+1] := sub<outgp|>;
  for i in [1..nb] do
    index[i] := Index(stabchain[i],stabchain[i+1]);
  end for;

  XSet:=GSet(outgp);
  XSeq:=SetToSequence(XSet);
  cands:=[];
  havecands:=[ false : i in [1..nb] ];
  ImOGBase:=OGBase;
  if #suboutgp gt 1 then
    for j in [1..nb] do
      substab := Stabilizer(suboutgp,[OGBase[i]:i in [1..j-1]]);
      if #substab gt 1 then
        havecands[j]:=true;
        //It is important that the base point is one of the candidates
        cands[j] := [Position(XSeq,OGBase[j])];
        for orb in Orbits(substab) do
          if  not OGBase[j] in orb then
            Append(~cands[j],Minimum([Position(XSeq,o):o in orb]));
          end if;
        end for;
      else break;
      end if;
    end for;
  end if;

  holperm := GR`holperm;
  holword := GR`holword;
  holmap := GR`holmap;
  gpholpt := GR`gpholpt;
  newgpholpt := GR`newgpholpt;

/* At any time in the search, there will be a current permutation, which
 * is the element being sought.
 * It should be thought of as specifying the base images of the first
 * "btlevel" base points of outgp, where "btlevel" is the current level of the
 * search.
 * Permutations cp[1], ..., cp[btlevel-1] will be stored, which have the
 * correct base images up to Base[1],...,Base[btlevel-1] respectively.
 * In fact cp[btlevel] = x*cp[btlevel-1], where x is a permutation in a right
 * transversal of stabchain[i+1] in stabchain[i].
 * (The searching procedure can sometimes be speeded up by storing these
 * transversals explicitly, particularly for larger values of i, where they
 * are accessed more frequently, but this will depend on whether there is
 * sufficient space available.)
 * At the bottom level, when cp[nb] has been calculated, it is tested
 * for the lifting property and if it satisfies this, it is adjoined
 * to subgens, and subgp extended.
 */   

  cp := [];
  cpind:=[];
  for i in [1..nb+1] do
    cpind[i] := 0;
  end for;
  /* The integer cpind[i] is for running through the transversal of
   * stabchain[i+1] in stabchain[i]. When cpind[i]=j, we are considering
   * that term in the transversal that maps OGBase[i] to the j-th point
   * in the i-th basic orbit.
   */
  btlevel := 1;
  fm := nb+1; /* The first moved base point */
 
/* Now the search can begin! */
  if GR`printlevel gt 1 then
    print "    +Starting search for lifting automorphisms";
    print "    +Lifting subgroup has order",#suboutgp;
  end if;
  sct:=0; //for diagnostic use only
  while btlevel gt 0 do
    cpind[btlevel] +:=1;
    if cpind[btlevel] gt index[btlevel] then
      /* backtrack */
      cpind[btlevel] := 0;
      btlevel -:= 1;
      if btlevel eq fm and cpind[btlevel] gt 1 then
        /* we have ruled out a particular image of this base point, so
         everything in its suboutgp-orbit can be ruled out */
        bopt := borbit[btlevel][cpind[btlevel]];
        substab := Stabilizer(suboutgp,[OGBase[i]:i in [1..btlevel-1]]);
        for i in Orbit(substab,bopt) do
          reject[Position(XSeq,i)]:=true;
        end for;
        haverejects:=true;
      end if;
    else
      if cpind[btlevel] eq 2 and btlevel lt fm then
         fm := btlevel; /* We are moving the base point OGBase[btlevel] for the
                           first time.  */
         if GR`printlevel gt 1 then
           print "      +First moved base point in search =",fm;
         end if;
         reject:=[false : i in [1..deg]];
         haverejects:=false;
      end if;
     /* Now we work out the full current permutation at this level */
      cp[btlevel]:=stabtrans[btlevel][cpind[btlevel]];
      if btlevel gt fm then
        cp[btlevel] := cp[btlevel]*cp[btlevel-1];
      end if;
      if btlevel eq fm or (btlevel gt fm and btlevel lt nb) then
        ImOGBase[btlevel] := OGBase[btlevel]^cp[btlevel];
        if havecands[btlevel] then
          if not Position(XSeq,ImOGBase[btlevel]) in cands[btlevel] then
            continue;
          end if;
          if btlevel lt nb-1 then
            substab := Stabiliser(suboutgp,[ImOGBase[i] : i in [1..btlevel]]);
            if #substab gt 1 then
              havecands[btlevel+1]:=true;
              cands[btlevel+1] := [Minimum([Position(XSeq,o):o in orb]):
                                                  orb in Orbits(substab)];
            else
              havecands[btlevel+1]:=false;
            end if;
          end if;
        else 
          havecands[btlevel+1]:=false;// could have been left 'true' earlier
        end if;
      end if;
        
      bopt := borbit[btlevel][cpind[btlevel]];
      if btlevel eq nb then
         el := cp[btlevel];
         sct +:=1;
         if GR`printlevel gt 2 and sct mod GR`printsct eq 0 then
           print "      +search count =",sct;
         end if;
         if el in suboutgp then
           continue;
         end if;
         if haverejects then
          rejectim:=false;
          for i in Orbit(sub<outgp|el>,OGBase[fm]) do
           if reject[Position(XSeq,i)] then
             rejectim:=true;
             break;
           end if;
          end for;
          if rejectim then
            continue;
          end if;
         end if;
         iel := el@@holmap;
         ims := [ holperm[g^iel] : g in gpholpt ];
         isiso, iso := IsIsomModH(GR,ims,level);
	 bigger:=false;
         if isiso then
           if GR`split then
              genims:=[ holword[g^iel]@lifthom : g in newgpholpt ];
              bigger:=true;
           else
             genims:=[ holword[g^iel] : g in newgpholpt ];
             if calcmodaut then
               oldFaut := hom<oldF->oldF | genims>;
               imrelgens:=[];
               for i in generatingrelnos do
                 rel := LHS(rels[i])*RHS(rels[i])^-1;
                 relim:= rel @ oldFaut @ GR`oldfptoperm @ GR`layermap[level];
                 Append(~imrelgens,relim);
               end for;
               imrelgensmat := SeqToMatH(imrelgens);
               if IsUnit(imrelgensmat) then
                 iso := modrelgensmatinv*imrelgensmat;
                 bigger, newgenims := AutExtensionH(GR,genims,iso,level);
                 if bigger then
                   genims:=newgenims;
                 end if;
               else
                 bigger:=false;
               end if;
             else
               for g in GR`modaut do
                 bigger, newgenims := AutExtensionH(GR,genims,g*iso,level);
                 if bigger then
                   genims:=newgenims;
                   iso := g*iso;
                   break;
                 end if;
               end for;
             end if;
           end if;
         end if;
         if bigger then
           for j in [1..dm] do
             w:=Id(F);
             for k in [1..dm] do
               w := w * (F.(nfg+k))^(Z!iso[j][k]);
             end for;
             Append(~genims,w);
           end for;
           Append(~GR`outimages,genims);
           Append(~subgens,el);
           suboutgp:=sub<outgp|subgens>;
           if GR`printlevel gt 1 then
             print "    +Lifting subgroup now has order",#suboutgp;
           end if;
           for j in [1..fm] do
             substab := Stabilizer(suboutgp,[OGBase[i]:i in [1..j-1]]);
             if #substab gt 1 then
               havecands[j]:=true;
               //It is important that the base point is one of the candidates
               cands[j] := [Position(XSeq,OGBase[j])];
               for orb in Orbits(substab) do
                 if  not OGBase[j] in orb then
                   Append(~cands[j],Minimum([Position(XSeq,o):o in orb]));
                 end if;
               end for;
             else break;
             end if;
           end for;
           for i in [fm+1..btlevel] do
             cpind[i]:=0;
           end for;
           btlevel:=fm;
         end if;
      else
        btlevel +:= 1;
      end if;
    end if;
  end while;
  if GR`printlevel gt 1 then
    print "    +Search is complete.";
  end if;

  if #suboutgp lt GR`smallsuboutgp then
    GR`liftoutaut := FPGroup(suboutgp);
    GR`orderliftoutaut := #suboutgp;
  else
    /* We need to introduce new generators to get a presentation
     * of suboutgp.
     */
    GR`liftoutaut, FPmap := FPGroupStrong(suboutgp);
    GR`orderliftoutaut := #suboutgp;
    /* I presume that the first generators of GR`lifoutaut correspond to
     * those of suboutgp, but had better check!
     */
    for i in [1..Ngens(suboutgp)] do
      if (GR`liftoutaut.i) @ FPmap ne suboutgp.i then
        error "FPGroupStrong function is misbehaving";
      end if;
    end for;
    for i in [Ngens(suboutgp)+1..Ngens(GR`liftoutaut)] do
    /* Work out generator images of new generator */
      el := (GR`liftoutaut.i) @ FPmap;
      iel := el@@holmap;
      ims := [ holperm[g^iel] : g in gpholpt ];
      isiso, iso := IsIsomModH(GR,ims,level);
      if  not isiso then
         error "New strong generator not does not induce module isomorphism!";
      end if;
      genims:=[ holword[g^iel] : g in newgpholpt ];
      if GR`split then
        genims:=[ holword[g^iel]@lifthom : g in newgpholpt ];
        bigger:=true;
      else
        genims:=[ holword[g^iel] : g in newgpholpt ];
        for g in GR`modaut do
          bigger, newgenims := AutExtensionH(GR,genims,g*iso,level);
          if bigger then
            genims:=newgenims;
            iso := g*iso;
             break;
          end if;
        end for;
      end if;
      if bigger then
        for j in [1..dm] do
          w:=Id(F);
          for k in [1..dm] do
            w := w * (F.(nfg+k))^(Z!iso[j][k]);
          end for;
          Append(~genims,w);
        end for;
        Append(~GR`outimages,genims);
      else
        error "New strong generator not does not lift to isomorphism!";
      end if;
    end for;
  end if; //if #suboutgp lt GR`smallsuboutgp
  if IsSoluble(suboutgp) then
    if GR`split then
      GR`soluble:=IsSoluble(GR`modaut);
    else
      GR`soluble:=true;
    end if;
  else
    GR`soluble:=false;
  end if;
  if GR`printlevel gt 1 then
    print "  +Subgroup of lifting outer automorphisms has order",#suboutgp;
  end if;
  return;
end procedure;
  
FindLiftingIsomH := procedure(~HR,~GR,level,outgp,subgens,~isomims)
/* outgp should be a permutation group isomorphic to the outer
 * automorphism group at the previous level. We search through this
 * group generating its subgroup of automorphisms that lift to outer
 * automorphisms modulo the next level. This involves a backtrack
 * search in the permutation group. subgens generate a subgroup
 * already known to lift.
 * If isomims is nonempty, then we are searching for a lifting of the
 * isomorphism H/subseries[level]->G/subseries[level] to the next level.
 */
local Z, F, oldF, G, GG, newgens, H, HH, Hnewgens, m, V, dm, K, bigger,
      suboutgp, oivwm, ogivwm, cands, havecands, conj, el, giso, isiso, iso,
      genims, newgenims, nfg, drophom, lifthom, w,
      nb, stabchain, borbit, index, btlevel, cp, cpind, substab,
      fm, im, bopt, OGBase, ImOGBase, sct,
      deg, reject, haverejects, rejectim, stabtrans,
      XSet, XSeq, holmap, holperm, holword, gpholpt, newgpholpt, ims, iel,
      FPmap,
      calcmodaut, cent, seccent, seccentgen, genct, nogood,
      generatingrelnos, modrelgens, modrelgensmatinv, rv, rvi,
      oldFaut, rels, rel, relim, imrelgens, imrelgensmat,
      haveisom, imsHtoG, isisoHtoG, isoHtoG, liftHtoG, newisomims, tryisomims,
      imholpt, newimholpt;
  
  haveisom := #isomims eq 0;
    
  Z := Integers();
  F := GR`fpgroup;
  oldF := GR`oldfpgroup;
  G := GR`newgroup;
  newgens := GR`newgens;
  H := HR`newgroup;
  Hnewgens := HR`newgens;
  GG := GR`permgroup;
  HH := HR`permgroup;
  nfg := GR`quotgens[level];
  m := GR`layermod[level];
  dm := Dimension(m);
  K := BaseRing(m);
  suboutgp := sub<outgp|subgens>;
  drophom := hom< F->oldF | [oldF.i : i in [1..nfg]]
                                cat [Id(oldF) : i in [1..dm] ] >;
  lifthom := hom< oldF->F | [F.i : i in [1..nfg]] >;
  deg:=Degree(outgp);
/* If GR`subseries[level] is central in G modulo GR`subseries[level+1],
 * the extension is nonsplit, and #GR`modaut>1, then we can calculate
 * the module automorphism induced by the outer automorphism being tested
 * for lifting, rather than trying all possibilities.
 */
  cent := sub < G | GR`centre @ GR`fptoperm, GR`subseries[level+1] >;
  seccent := EASectionCentraliser(G,GR`subseries[level],GR`subseries[level+1]);
  seccentgen := [ newgens[i] in seccent : i in [1..nfg] ]; 
  calcmodaut :=  #GR`modaut gt GR`verysmallmodaut and not GR`split;
  if calcmodaut and GR`printlevel gt 1 then
    print "  +Will try to compute induced module automorphisms.";
  end if;
  if calcmodaut then
    /* We first find a subset of GR`relvals that generates m.
     * The corresponding relators of GR`oldfpgroup will be used to
     * calculate the induced module automorphism.
     */
    rels := Relations(oldF);
    generatingrelnos:=[];
    modrelgens:=[];
    rv:=GR`relvals;
    V:=VectorSpace(m);
    for i in [1..#rv] do
      rel := ElementToSequence(LHS(rels[i])*RHS(rels[i])^-1);
      genct := [ K!0 : i in [1..nfg] ];
      nogood:=false;
      for i in rel do
        if not seccentgen[Abs(i)] then
          nogood:=true;
          break;
        end if;
        if i gt 0 then genct[i]+:=1;
          else genct[-i]-:=1; 
        end if;
      end for;
      nogood := nogood or genct ne [ K!0 : i in [1..nfg] ];
      if nogood then
        continue;
      end if;
      rvi := V!(Eltseq(rv[i]));
      if not rvi in sub<V|modrelgens> then
        Append(~modrelgens,rvi);
        Append(~generatingrelnos,i);
        if sub<V|modrelgens> eq V then
          break;
        end if;
      end if;
    end for;
    if #modrelgens eq dm then
      modrelgensmatinv := SeqToMatH(modrelgens)^-1;
    else
      if GR`printlevel gt 1 then
        print "  +Cannot compute induced module automorphisms.";
      end if;
      calcmodaut:=false;
    end if;
    if GR`printlevel gt 1 then
      print "  +Generating reln. numbers are: ",generatingrelnos;
    end if;
  end if;

/* The code for the case where outgp acts regularly is much simpler, so we
 * handle it separately.
 */
  if IsRegular(outgp) then
    if GR`printlevel gt 1 then
      print "    +Starting search for lifting automorphisms";
      print "    +Lifting subgroup has order",#suboutgp;
    end if;
    cands := [ Minimum(o) : o in Orbits(suboutgp) ];
    reject:=[];
    haverejects:=false;
    sct:=0; //for diagnostic use only
    for i in [2..deg] do
      if not i in cands  then
        continue;
      end if;
      _,el := IsConjugate(outgp,1,i);
      sct+:=1;
      if GR`printlevel gt 2 and sct mod GR`printsct eq 0 then
         print "      +search count =",sct;
      end if;
      if haverejects then
        rejectim:=false;
        for j in Orbit(sub<outgp|el>,1) do
          if Minimum(Orbit(suboutgp,j)) in reject then
             rejectim:=true;
             break;
          end if;
        end for;
        if haveisom and rejectim then
          Append(~reject,i);
          continue;
        end if;
      end if;
      giso := CalculateOldIsomH(GR,el@@GR`holmap);
      if not haveisom then
        // try this for a possible isomorphism inducing map
        HtoG := hom< H->G |
   [Hnewgens[i]->GR`oldfptoperm(isomims[i]) @ giso : i in [1..#isomims]] cat
          [Hnewgens[i]->Id(G) : i in [nfg+1..#Hnewgens]] : Check:=false  >;
        imsHtoG := [HtoG(HH.j) : j in [1..Ngens(HH)] ];
        // first test if it induces a module isomorphism
        isisoHtoG, isoHtoG := IsIsomHtoGModH(HR,GR,imsHtoG,level);
        if isisoHtoG then
          if GR`printlevel gt 2 then
             print
         "    +Found a lifting of isomorphism inducing a module isomorphism.";
          end if;
          if GR`split then
            haveisom:=true;
            isomims :=
               [ InverseImageGRH(GR,GR`oldfptoperm(x)@giso,level-1) :
                                                              x in isomims];
          else
            tryisomims :=
              [ InverseImageGRH(GR,GR`oldfptoperm(x)@giso,level-1)@drophom :
                                                              x in isomims];
            for g in HR`modaut do
 // we might later use the calcmodaut mechanism here intead of trying them all
              liftHtoG, newisomims :=
                          IsomExtensionHtoGH(HR,GR,tryisomims,g*isoHtoG,level);
              if liftHtoG then
                haveisom:=true;
                isomims:=newisomims;
                isoHtoG := g*isoHtoG;
                break;
              end if;
            end for;
          end if;
          if haveisom then
            for j in [1..dm] do
              w:=Id(F);
              for k in [1..dm] do
                w := w * (F.(nfg+k))^(Z!isoHtoG[j][k]);
              end for;
              Append(~isomims,w);
            end for;
            if GR`printlevel gt 0 then
              print "Isomorphism lifts - found lifting during search.";
            end if;
          end if;
        end if;
        if haverejects and rejectim then
          Append(~reject,i);
          continue;
        end if;
      end if;

      ims := [(GG.j) @ giso : j in [1..Ngens(GG)] ];
      isiso, iso := IsIsomModH(GR,ims,level);
      bigger:=false;
      if isiso then
        if GR`split then
           genims:=[ InverseImageGRH(GR,newgens[i]@giso,level-1):
                                                       i in [1..nfg]];
           bigger:=true;
        else
          genims:=[ InverseImageGRH(GR,newgens[i]@giso,level-1)@drophom :
                                                       i in [1..nfg]];
          if calcmodaut then
            oldFaut := hom<oldF->oldF | genims>;
            imrelgens:=[];
            for i in generatingrelnos do
              rel := LHS(rels[i])*RHS(rels[i])^-1;
              relim:= rel @ oldFaut @ GR`oldfptoperm @ GR`layermap[level]; 
              Append(~imrelgens,relim);
            end for;
            imrelgensmat := SeqToMatH(imrelgens);
            if IsUnit(imrelgensmat) then
              iso := modrelgensmatinv*imrelgensmat;
              bigger, newgenims := AutExtensionH(GR,genims,iso,level);
              if bigger then
                genims:=newgenims;
              end if;
            else
              bigger:=false;
            end if;
          else
            for g in GR`modaut do
              bigger, newgenims := AutExtensionH(GR,genims,g*iso,level);
              if bigger then
                genims:=newgenims;
                iso := g*iso;
                break;
              end if;
            end for;
          end if;
        end if;
      end if;
      if bigger then
        for j in [1..dm] do
          w:=Id(F);
          for k in [1..dm] do
            w := w * (F.(nfg+k))^(Z!iso[j][k]);
          end for;
          Append(~genims,w);
        end for;
        Append(~GR`outimages,genims);
        Append(~subgens,el);
        suboutgp:=sub<outgp|subgens>;
        if GR`printlevel gt 1 then
          print "    +Lifting subgroup now has order",#suboutgp;
        end if;
        cands := [ Minimum(o) : o in Orbits(suboutgp) ];
      else
        haverejects:=true;
        Append(~reject,i);
      end if;
    end for;

    GR`liftoutaut := FPGroup(suboutgp);
    GR`orderliftoutaut := #suboutgp;
    if IsSoluble(suboutgp) then
      if GR`split then
        GR`soluble:=IsSoluble(GR`modaut);
      else
        GR`soluble:=true;
      end if;
    else
      GR`soluble:=false;
    end if;
    if GR`printlevel gt 1 then
      print "  +Subgroup of lifting outer automorphisms has order",#suboutgp;
    end if;
    if not haveisom then
      if GR`printlevel gt 1 then
        print "  +Isomorphism has not lifted after search.";
      end if;
      isomims:=[];
    end if;
    return;
  end if;

/* First work out indices and transversals for the stabiliser chain */
  if GR`printlevel gt 1 then
    print "    +Calculating indices, basic orbits and transversals.";
  end if;
  OGBase:=Base(outgp);
  nb:=#OGBase;
  stabchain := []; borbit:=[]; index:=[];
  stabtrans:=[];
  for i in [1..nb] do
    stabchain[i] := Stabiliser(outgp,[OGBase[j]:j in [1..i-1]]);
    borbit[i] := [k: k in Orbit(stabchain[i],OGBase[i])];
    /* We want the base point to come first though! */
    p:=Position(borbit[i],OGBase[i]);
    if p ne 1 then
      borbit[i][p]:=borbit[i][1]; borbit[i][1]:=OGBase[i];
    end if;
    stabtrans[i]:=[];
    for j in [1..#borbit[i]] do
      bopt:=borbit[i][j];
      _,el:=IsConjugate(stabchain[i],OGBase[i],bopt);
      stabtrans[i][j]:=el;
    end for;
  end for;
  stabchain[nb+1] := sub<outgp|>;
  for i in [1..nb] do
    index[i] := Index(stabchain[i],stabchain[i+1]);
  end for;

  XSet:=GSet(outgp);
  XSeq:=SetToSequence(XSet);
  cands:=[];
  havecands:=[ false : i in [1..nb] ];
  ImOGBase:=OGBase;
  if #suboutgp gt 1 then
    for j in [1..nb] do
      substab := Stabilizer(suboutgp,[OGBase[i]:i in [1..j-1]]);
      if #substab gt 1 then
        havecands[j]:=true;
        //It is important that the base point is one of the candidates
        cands[j] := [Position(XSeq,OGBase[j])];
        for orb in Orbits(substab) do
          if  not OGBase[j] in orb then
            Append(~cands[j],Minimum([Position(XSeq,o):o in orb]));
          end if;
        end for;
      else break;
      end if;
    end for;
  end if;

  holperm := GR`holperm;
  holword := GR`holword;
  holmap := GR`holmap;
  gpholpt := GR`gpholpt;
  newgpholpt := GR`newgpholpt;
  if not haveisom then
    imholpt := GR`imholpt;
    newimholpt := GR`newimholpt;
  end if;

/* At any time in the search, there will be a current permutation, which
 * is the element being sought.
 * It should be thought of as specifying the base images of the first
 * "btlevel" base points of outgp, where "btlevel" is the current level of the
 * search.
 * Permutations cp[1], ..., cp[btlevel-1] will be stored, which have the
 * correct base images up to Base[1],...,Base[btlevel-1] respectively.
 * In fact cp[btlevel] = x*cp[btlevel-1], where x is a permutation in a right
 * transversal of stabchain[i+1] in stabchain[i].
 * (The searching procedure can sometimes be speeded up by storing these
 * transversals explicitly, particularly for larger values of i, where they
 * are accessed more frequently, but this will depend on whether there is
 * sufficient space available.)
 * At the bottom level, when cp[nb] has been calculated, it is tested
 * for the lifting property and if it satisfies this, it is adjoined
 * to subgens, and subgp extended.
 */   

  cp := [];
  cpind:=[];
  for i in [1..nb+1] do
    cpind[i] := 0;
  end for;
  /* The integer cpind[i] is for running through the transversal of
   * stabchain[i+1] in stabchain[i]. When cpind[i]=j, we are considering
   * that term in the transversal that maps OGBase[i] to the j-th point
   * in the i-th basic orbit.
   */
  btlevel := 1;
  fm := nb+1; /* The first moved base point */

/* Now the search can begin! */
  if GR`printlevel gt 1 then
    print "    +Starting search for lifting automorphisms";
    print "    +Lifting subgroup has order",#suboutgp;
  end if;
  sct:=0; //for diagnostic use only
  while btlevel gt 0 do
    cpind[btlevel] +:=1;
    if cpind[btlevel] gt index[btlevel] then
      /* backtrack */
      cpind[btlevel] := 0;
      btlevel -:= 1;
      if btlevel eq fm and cpind[btlevel] gt 1 then
        /* we have ruled out a particular image of this base point, so
         everything in its suboutgp-orbit can be ruled out */
        bopt := borbit[btlevel][cpind[btlevel]];
        substab := Stabilizer(suboutgp,[OGBase[i]:i in [1..btlevel-1]]);
        for i in Orbit(substab,bopt) do
          reject[Position(XSeq,i)]:=true;
        end for;
        haverejects:=true;
      end if;
    else
      if cpind[btlevel] eq 2 and btlevel lt fm then
         fm := btlevel; /* We are moving the base point OGBase[btlevel] for the
                           first time.  */
         if GR`printlevel gt 1 then
           print "      +First moved base point in search =",fm;
         end if;
         reject:=[false : i in [1..deg]];
         haverejects:=false;
      end if;
     /* Now we work out the full current permutation at this level */
      cp[btlevel]:=stabtrans[btlevel][cpind[btlevel]];
      if btlevel gt fm then
        cp[btlevel] := cp[btlevel]*cp[btlevel-1];
      end if;
      if btlevel eq fm or (btlevel gt fm and btlevel lt nb) then
        ImOGBase[btlevel] := OGBase[btlevel]^cp[btlevel];
        if havecands[btlevel] then
          if not Position(XSeq,ImOGBase[btlevel]) in cands[btlevel] then
            continue;
          end if;
          if btlevel lt nb-1 then
            substab := Stabiliser(suboutgp,[ImOGBase[i] : i in [1..btlevel]]);
            if #substab gt 1 then
              havecands[btlevel+1]:=true;
              cands[btlevel+1] := [Minimum([Position(XSeq,o):o in orb]):
                                                  orb in Orbits(substab)];
            else
              havecands[btlevel+1]:=false;
            end if;
          end if;
        else 
          havecands[btlevel+1]:=false;// could have been left 'true' earlier
        end if;
      end if;
        
      bopt := borbit[btlevel][cpind[btlevel]];
      if btlevel eq nb then
         el := cp[btlevel];
         sct +:=1;
        if GR`printlevel gt 2 and sct mod GR`printsct eq 0 then
           print "      +search count =",sct;
        end if;
         if el in suboutgp then
           continue;
         end if;
         if haverejects then
          i := OGBase[fm]^el;
	  rejectim := reject[Position(XSeq,i)];
          if rejectim then
            continue;
          end if;
         end if;
         iel := el@@holmap;
         if not haveisom then
           // try this for a possible isomorphism inducing map
           imsHtoG := [holperm[g^iel] : g in imholpt ];
           isisoHtoG, isoHtoG := IsIsomHtoGModH(HR,GR,imsHtoG,level);
           if isisoHtoG then
             if GR`printlevel gt 2 then
                print
         "    +Found a lifting of isomorphism inducing a module automorphism.";
             end if;
             if GR`split then
               haveisom:=true;
               isomims := [ holword[g^iel]@lifthom : g in newimholpt ];
             else
               tryisomims := [ holword[g^iel] : g in newimholpt ];
               for g in HR`modaut do
  // we might later use the calcmodaut mechanism here intead of trying them all
                 liftHtoG, newisomims :=
                       IsomExtensionHtoGH(HR,GR,tryisomims,g*isoHtoG,level);
                 if liftHtoG then
                   haveisom:=true;
                   isomims:=newisomims;
                   isoHtoG := g*isoHtoG;
                   break;
                 end if;
               end for;
             end if;
             if haveisom then
               for j in [1..dm] do
                 w:=Id(F);
                 for k in [1..dm] do
                   w := w * (F.(nfg+k))^(Z!isoHtoG[j][k]);
                 end for;
                 Append(~isomims,w);
               end for;
               if GR`printlevel gt 0 then
                 print "Isomorphism lifts - found lifting during search.";
               end if;
             end if;
           end if;
         end if;

         ims := [ holperm[g^iel] : g in gpholpt ];
         isiso, iso := IsIsomModH(GR,ims,level);
	 bigger:=false;
         if isiso then
           if GR`split then
              genims:=[ holword[g^iel]@lifthom : g in newgpholpt ];
              bigger:=true;
           else
             genims:=[ holword[g^iel] : g in newgpholpt ];
             if calcmodaut then
               oldFaut := hom<oldF->oldF | genims>;
               imrelgens:=[];
               for i in generatingrelnos do
                 rel := LHS(rels[i])*RHS(rels[i])^-1;
                 relim:= rel @ oldFaut @ GR`oldfptoperm @ GR`layermap[level];
                 Append(~imrelgens,relim);
               end for;
               imrelgensmat := SeqToMatH(imrelgens);
               if IsUnit(imrelgensmat) then
                 iso := modrelgensmatinv*imrelgensmat;
                 bigger, newgenims := AutExtensionH(GR,genims,iso,level);
                 if bigger then
                   genims:=newgenims;
                 end if;
               else
                 bigger:=false;
               end if;
             else
               for g in GR`modaut do
                 bigger, newgenims := AutExtensionH(GR,genims,g*iso,level);
                 if bigger then
                   genims:=newgenims;
                   iso := g*iso;
                   break;
                 end if;
               end for;
             end if;
           end if;
         end if;
         if bigger then
           for j in [1..dm] do
             w:=Id(F);
             for k in [1..dm] do
               w := w * (F.(nfg+k))^(Z!iso[j][k]);
             end for;
             Append(~genims,w);
           end for;
           Append(~GR`outimages,genims);
           Append(~subgens,el);
           suboutgp:=sub<outgp|subgens>;
           if GR`printlevel gt 1 then
             print "    +Lifting subgroup now has order",#suboutgp;
           end if;
           for j in [1..fm] do
             substab := Stabilizer(suboutgp,[OGBase[i]:i in [1..j-1]]);
             if #substab gt 1 then
               havecands[j]:=true;
               //It is important that the base point is one of the candidates
               cands[j] := [Position(XSeq,OGBase[j])];
               for orb in Orbits(substab) do
                 if  not OGBase[j] in orb then
                   Append(~cands[j],Minimum([Position(XSeq,o):o in orb]));
                 end if;
               end for;
             else break;
             end if;
           end for;
           for i in [fm+1..btlevel] do
             cpind[i]:=0;
           end for;
           btlevel:=fm;
         end if;
      else
        btlevel +:= 1;
      end if;
    end if;
  end while;
  if GR`printlevel gt 1 then
    print "    +Search is complete.";
  end if;

  if #suboutgp lt GR`smallsuboutgp then
    GR`liftoutaut := FPGroup(suboutgp);
    GR`orderliftoutaut := #suboutgp;
  else
    /* We need to introduce new generators to get a presentation
     * of suboutgp.
     */
    GR`liftoutaut, FPmap := FPGroupStrong(suboutgp);
    GR`orderliftoutaut := #suboutgp;
    /* I presume that the first generators of GR`lifoutaut correspond to
     * those of suboutgp, but had better check!
     */
    for i in [1..Ngens(suboutgp)] do
      if (GR`liftoutaut.i) @ FPmap ne suboutgp.i then
        error "FPGroupStrong function is misbehaving";
      end if;
    end for;
    for i in [Ngens(suboutgp)+1..Ngens(GR`liftoutaut)] do
    /* Work out gneerator images of new generator */
      el := (GR`liftoutaut.i) @ FPmap;
      iel := el@@holmap;
      ims := [ holperm[g^iel] : g in gpholpt ];
      isiso, iso := IsIsomModH(GR,ims,level);
      if  not isiso then
         error "New strong generator not does not induce module isomorphism!";
      end if;
      genims:=[ holword[g^iel] : g in newgpholpt ];
      if GR`split then
        genims:=[ holword[g^iel]@lifthom : g in newgpholpt ];
        bigger:=true;
      else
        genims:=[ holword[g^iel] : g in newgpholpt ];
        for g in GR`modaut do
          bigger, newgenims := AutExtensionH(GR,genims,g*iso,level);
          if bigger then
            genims:=newgenims;
            iso := g*iso;
             break;
          end if;
        end for;
      end if;
      if bigger then
        for j in [1..dm] do
          w:=Id(F);
          for k in [1..dm] do
            w := w * (F.(nfg+k))^(Z!iso[j][k]);
          end for;
          Append(~genims,w);
        end for;
        Append(~GR`outimages,genims);
      else
        error "New strong generator not does not lift to isomorphism!";
      end if;
    end for;
  end if; //if #suboutgp lt GR`smallsuboutgp
  if IsSoluble(suboutgp) then
    if GR`split then
      GR`soluble:=IsSoluble(GR`modaut);
    else
      GR`soluble:=true;
    end if;
  else
    GR`soluble:=false;
  end if;
  if GR`printlevel gt 1 then
    print "  +Subgroup of lifting outer automorphisms has order",#suboutgp;
  end if;
  if not haveisom then
    if GR`printlevel gt 1 then
      print "  +Isomorphism has not lifted after search.";
    end if;
    isomims:=[];
  end if;
  return;
end procedure;
