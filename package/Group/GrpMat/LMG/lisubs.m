freeze;

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

ExtendOneSubgroupH := function(G,k,subrec,maxind,calcpres:Print:=0)
/* k is the layer A/B of the chief series of G that we are lifting through
 * where A := cs[k+1]; B := cs[k];
 * subrec is a record defining a subgroup H/A of G/A, and a
 * corresponding list of records defining subgroups of G/B of index
 * at most maxind that map onto H/A is returned.
 * (The subgroups involved are not really subgroups of the quotients
 * G/A and G/B, but subgroups of G that map onto the theoretical
 * subgroups.)
 * If calcpres is true, then presentations for each subgroup in the list
 * returned are calculated.
 */
 local r,rpc,rad,rtopc,rq,Gtorq,rm,m,ptom,gmacts,mats,cs,mgensG,src,
       RF, Z, ExtendSubsH, ES, ESR, dim, p, mindim, RM, L,
       SL, GonSLgens, gen, perm, im, Rep, repgen, S, SA, ngs,
       Spres, Spresmap, nlifts, rels, nrs, rel, w, normS, ngns,
       normSonSL, nS2nSonSL, normSonSLgens, FixS, OFixS, RV, RVQ, RVS,
       orb, prep, grep, orbreps, intmorph, normsubS, sns, normsubSonSL, subdim,
       quodim, SM, subSM, quoSM, projSM, SpresM, subSpresM, repquoSM,
       repsubSM, split, Comps, Compreps, Comporblens, Compact, comp, nc,
       CCS, imcomp, normgens, wordgp, quoSA, quoSAg, projSA,
       wgtoG, wgtoqSp, word, tail, wm,
       ngp, ngactgp, ngorbs, classlenA, classlen,
       quoSMtoG, subSMtoG,
       liftgens, liftpres, liftsub, liftsubB, intsub, vec,
       longtail, longvec, mat, i, j, c, d, conjsub, quolimit,
       translimit, repsub;

  r := G`LMGNode;
  rpc := r`radPC;
  rad := r`rad;
  rtopc := r`radtoPC;
  rq := r`radquot;
  Gtorq := r`Gtoradquot;
  rm := r`radmods;
  //gmacts := r`rqradmodactions;
  gmacts := r`radmodactions;
  cs := r`cseries;
  m := rm[k][1];
  ptom := rm[k][2];
  prep := rm[k][3];
  grep := gmacts[k];
  p := #BaseRing(m);
  dim := Dimension(m);
  A := cs[k+1]; B := cs[k];

 quolimit := 2000;
 translimit := 32;
 RF := Format(subrec);
 Z := Integers();
 ExtendSubsH := []; /* This will be the lifted subgroup-list to be returned. */

 S:=subrec`subgroup;
 ngs:=Ngens(S);
 if subrec`index eq 1 then
   SA := G;
 else
   SA := sub< Generic(G) | A,S>;
   AssertAttribute(SA, "Order", #G div subrec`index);
 end if;
 mindim := Minimum(
        [ d : d in [0..dim] | subrec`index * p^(dim-d) le maxind ] );

 if mindim eq dim then
   src := subrec;
   
   liftgens := src`order eq 1 select [m.i @@ ptom @@ rtopc : i in [1..dim]]
      else [S.i : i in [1..ngs]] cat [m.i @@ ptom @@ rtopc : i in [1..dim]];
   src`subgroup := sub< Generic(G) | liftgens >;
   src`order *:= p^dim; 
   if src`order eq p^dim then
     src`presentation := ElementaryAbelianPresentation(#BaseRing(m),dim);
   else 
     Spres := src`presentation;
     subSpresM := GModule(Spres,[grep(S.i) : i in [1..ngs] ]);
     quoSsubmap := hom< Spres->G | [ liftgens[i] : i in [1..ngs] ] >;
             // Once again, this is not a genuine homomorphism! 
     RVS:=[];
     rels:=Relations(Spres);
     for rel in rels do
          w := LHS(rel)*RHS(rel)^-1;
          Append(~RVS,subSpresM!Eltseq(m!Eltseq(w@quoSsubmap@rtopc@ptom)));
     end for;
     src`presentation := ModuleExtension(subSpresM,RVS);
   end if;
   return [src];
 end if;

 RM := GModule(S,[MatrixAlgebra(GF(p),dim) | grep(S.i): i in [1..Ngens(S)]]);
 SL := Submodules(RM : CodimensionLimit:=dim-mindim);
 SLI := {@ Eltseq( EchelonForm(Morphism(U, RM)) ) : U in SL @};
 if subrec `index le 2 then
   normS := G; indnormS := 1;
 else
   normS := LMGNormaliser(G,SA);
   indnormS := LMGIndex(G,normS);
 end if;
 /* We want representatives of the orbits of normS in its conjugation
  * action on SL. So set up that action.
  */
 if Print gt 1 or (Print eq 1 and #SL gt 512) then
   print "  +Setting up action of group on",#SL,"subgroups of layer.";
 end if;
 ngns := Ngens(normS);
 normSonSLgens := [];
 for i in [1..ngns] do
   perm := [];
   repgen := grep(normS.i);
   for j in [1..#SL] do
     perm[j] :=
        Position(SLI, Eltseq( EchelonForm( Morphism(SL[j],RM)*repgen ) ) );
   end for;
   Append(~normSonSLgens,Sym(#SL)!perm);
 end for;
 normSonSL := sub<Sym(#SL) | normSonSLgens >;
 nS2nSonSL := hom< normS->normSonSL | normSonSLgens >;
 OFixS := Orbits(normSonSL);
 orbreps := [ Representative(orb) : orb in OFixS ];
 if Print gt 1 then
   print "    ",#orbreps,"possible intersections of subgroup with module.";
   print "  -Done.";
 end if;

 /* Now we find all liftings to G/B of the specified subgroup of G/A */
 Spres:=subrec`presentation;
 if ngs eq 0 then
   Spresmap := hom< Spres->Generic(S) | [ Id(S) ] >;
 else
   Spresmap := hom< Spres->Generic(S) | [ S.i : i in [1..ngs] ] >;
 end if;
 /* This is not a genuine homomorphism - the whole point is that we want to
  * work out the images of the relators of Spres in A/B
  */
 rels:=Relations(Spres);
 nrs:=#rels;
 RV:=[];
 for rel in rels do
   w := LHS(rel)*RHS(rel)^-1;
   Append(~RV,w@Spresmap@rtopc@ptom);
 end for;
 nlifts:=0;
 for rep in orbreps do
   quolimit := 1000;
   intmorph:=Morphism(SL[rep],RM);
   normsubSonSL := Stabiliser(normSonSL,rep);
   indnormsubS := indnormS * #Orbit(normSonSL,rep);
   normsubS := sub<  Generic(G)  | normsubSonSL@@nS2nSonSL >;
   
   /* We are now going to find those subgroups of G/B which intersect
    * A/B in the inverse image in G of intmorph.
    * We need to regard this subgroup as a module for normsubS
    */
   subdim := Dimension(Image(intmorph));
   quodim := dim-subdim;
   SM := GModule(normsubS, [grep(normsubS.i): i in [1..Ngens(normsubS)]]);
   subSM := sub< SM | [ SM!Eltseq(intmorph[i]) : i in [1..subdim] ] >;
   if Print gt 2 then
     print "      +Trying intersection of size",#subSM;
   end if;
   quoSM, projSM := quo<SM|subSM>;
   /* We need to look find conjugacy classes of complements of quoSM=SM/subSM
    * in S/subSM, to find those subgroups of G/B which map onto S/B and
    * intersect A/B in subSM/B.
    * To do the cohomology calculation, we need to work with the module
    * MQ regarded as being over the finitely presented group Spres.
    */
   if quodim ne 0 then
     repquoSM := Representation(quoSM);
     SpresM := ngs eq 0 select
               GModule(Spres,[Id(S)@repquoSM]) else
               GModule(Spres,[(S.i)@repquoSM : i in [1..ngs] ]); 
     /*  We need to coerce the values of RV into this module 
      */
     RVQ := [ SpresM!Eltseq((SM!Eltseq(RV[i]))@projSM) : i in [1..nrs] ];
     /* Now we can do the cohomology calculation at last! */
     split, Comps := ComplementVectors(SpresM,RVQ);
     CCS := ConjugateComplementSubspace(SpresM);
     /* This is the coboundary space, of which Comps forms the set of
      * complements. We may need this if we have a normaliser acting
      * on the set Comps, to identify the equivalence class of an
      * unknown complement.
      * NOTE - this is a little inefficient, since it was called anyway
      * by ComplementVecs - maybe ComplementVecs should return it too?
      */
	classlenA := p^Dimension(CCS);
      /* This is the index of the normaliser in A of the subgroup in A
       * To get the actual classlen it will later be multiplied by the index
       * of the normaliser modulo A
       */
   else
     split := true;
     Comps := [ [ quoSM!0 : i in [1..ngs] ] ];
     classlenA := 1;
   end if;
   if not split then
     if Print gt 2 then
       print "       No complements for this intersection."; 
     end if;
   else
     nc := #Comps;
     if Print gt 2 then
       print "      ",nc,"complements for this intersection."; 
     end if;
     if nc ge 2^10 then quolimit := 50000; end if;
     if nc ge 2^14 then quolimit := 500000; end if;
     if  nc gt 1 and normsubS ne SA and subrec`order lt quolimit then
       /* We have to find the action of normsubS on the set of complements,
        * and only take one representative from each orbit of this action.
        * Since this involves forming the quotient SA/A, if this quotient
        * is very large, then we use a more direct method, with IsConjugate,
        * which we do later.
        * First locate the generators of normsubS that we need to use.
        */
        if Print gt 2 then
          print "       +Calculating normaliser action on complements (1).";
        end if;

	/* We're going to want Position's in Comps, so make an 
	 * indexed set of it for efficiency's sake - billu 7/1/04
	 */
	Comps := {@ c : c in Comps @};
	assert #Comps eq nc;

       normgens := [];
       sns := SA;
       for gen in Generators(normsubS) do
         if not LMGIsIn(sns,gen) then
           Append(~normgens,gen);
           sns := sub< Generic(G) |sns,gen>;
         end if;
       end for;
       if Print gt 2 then
         print "        ",#normgens,"normalising generators for this subgroup.";
       end if;
       /* Next we must work out the action of each such generator on S.
        * We need the results as  word in the generators of Spres
        * (which correspond to those of S).
        * We store them as word[i][j], for the action of the i-th normgen
        * on the j-th generator of S (mod A).
        * We also store corresponding elements tail[i][j] of quoSM.
        * These are defined as follows Let lword[i][j] be the word word[i][j]
        * lifted to G. Then, modulo subSM, we have
        * normgen[i]*lword[i][j]*normgen[i]^-1 = S.j*tail[i][j].
        * In fact, tail[i][j] needs to be co-erced into SpresM for
        * later use.
        */
/* Unfortunately need to use quotient here */
       quoSA, projSA := quo<SA|A>;
       if Print ge 3 then
         "Formed quotient of degree", Degree(quoSA);
       end if;
       quoSAg := sub< Generic(quoSA) | [(S.i)@projSA : i in [1..ngs] ] >;
       AssertAttribute(quoSAg, "Order", subrec`order);
       /* quoSAg has the generating set that we need */
       wordgp, wm := FPGroup(quoSAg: StrongGenerators:=false );
       wgtoG := ngs eq 0 select
            hom<wordgp->Generic(G) | [Id(S)] > else
            hom<wordgp->Generic(G) | [S.i : i in [1..ngs] ] >;
       wgtoqSp := ngs eq 0 select
            hom<wordgp->Spres | [Id(Spres)] > else
            hom<wordgp->Spres | [Spres.i : i in [1..ngs] ] >;
       word:=[]; tail:=[];
       for i in [1..#normgens] do
         word[i]:=[]; tail[i]:=[];
         gen := normgens[i];
         for j in [1..ngs] do
           w := (gen^-1*S.j*gen)@projSA@@wm;
           word[i][j]:=w@wgtoqSp;
           vec :=
             (SM!Eltseq((S.j^-1*gen*(w@wgtoG)*gen^-1)@rtopc@ptom))@projSM;
           tail[i][j] := SpresM!(Eltseq(vec));
         end for;
       end for;
       /* Now we are ready to work out the action of normsubS on the set
        * of complements. We won't set this up as a formal G-action on the
        * set, but simply build the corresponding permutations ngp[i] of the
        * set {1,2,..,nc} induced by the generator normgens[i], where
        * the image ngp[i][j] of j under ngp[i] corresponds to conjugation
        * of Comps[j] by normgens[i]^-1.
        */
       ngp := [];
       for i in [1..#normgens] do
         ngp[i] := [];
         gen := normgens[i];
         mat := repquoSM(gen)^-1;
         for c in [1..nc] do
           comp:=Comps[c];
           /* We need to concatenate all the ngs vectors for the cocycle for
            * the conjugated complement together to get a vector of length
            * ngs*quodim
            */
           longvec := [];
           for j in [1..ngs] do
             /* Calculate tail for generator j in the conjugated complement */
             vec := tail[i][j] + TailVector(SpresM,comp,word[i][j])*mat;
             longvec := longvec cat Eltseq(vec);
           end for;
           longvec := VectorSpace(GF(p),ngs*quodim)!longvec;
           vec, longvec := DecomposeVector(CCS,longvec);
           /* longvec lies in the complement of CCS, and can be split up
            * to give the image complement - we also must add in the tail.
            */
           imcomp := [];
           vec := SpresM!0;
           for j in [1..ngs] do
             for l in [1..quodim] do
               vec[l] := longvec[(j-1)*quodim+l];
             end for;
             Append(~imcomp,vec);
           end for;
           pos := Position(Comps,imcomp);
           if pos eq 0 then
             //print CCS, Comps, imcomp;
             error "Image of complement under conjugation is not in list!";
           end if;
           ngp[i][c] := pos;
         end for;
       end for;
       ngactgp := sub<Sym(nc)|ngp>;
       ngorbs := Orbits(ngactgp);
       Compreps := [ Comps[Representative(ngorbs[l])] : l in [1..#ngorbs] ];
	 Comporblens := [#(ngorbs[l]) : l in  [1..#ngorbs] ];
       if Print gt 2 then
         print "       -",#Compreps,"orbits on complements.";
       end if;
     else
       Compreps := Comps;
       Comporblens := [];
     end if;
     /* We need to pull back the generators of quoSM and of subSM to G and QB
      * let's see if we can get this right!
      */
     quoSMtoG :=
         [ (m!Eltseq((quoSM.i)@@projSM))@@ptom@@rtopc : i in [1..quodim] ];
     subSMtoG := [ (m!Eltseq(intmorph[i]))@@ptom@@rtopc : i in [1..subdim] ];
     intsub := sub< Generic(G) | B,subSMtoG>;
     /* Now, for each complement, we can work out the generators of the
      * corresponding lifting subgroup, and then work out a presentation
      * of the subgroup on those generators.
      */
     ES := []; /* we store the lifted subgroups in ES and add it on to
                * ExtendSubsH later.
                */
     for compno in [1..#Compreps] do
       comp := Compreps[compno];
       classlen := classlenA * indnormsubS;
       if Comporblens ne [] then classlen *:= Comporblens[compno]; end if;
       liftgens := [];
       for i in [1..ngs] do
           gen := S.i;
           vec := comp[i];
           for j in [1..quodim] do
               gen := gen * quoSMtoG[j]^(Z!vec[j]);
           end for;
           Append(~liftgens,gen);
       end for;
       //liftgens := liftgens cat subSMtoG;
       liftgens := ngs eq 0 select subSMtoG else liftgens cat subSMtoG;
       liftsub := sub< Generic(G) | liftgens >;
       //liftsubB := sub< Generic(G) | B, liftgens >;
       /* To get the presentation, we need to work out the relation values
        * as elements of subSM
        */
       if (calcpres) then
         if subdim ne 0 then
           if SA eq A then
             liftpres := ElementaryAbelianPresentation(p,subdim);
           else
             repsubSM := Representation(subSM);
             subSpresM := ngs eq 0 select
                GModule(Spres,[Id(S)@repsubSM]) else
                GModule(Spres,[(S.i)@repsubSM : i in [1..ngs] ]);
             quoSsubmap :=
                 hom< Spres->G | [ liftgens[i] : i in [1..ngs] ] >;
             /* Once again, this is not a genuine homomorphism! */
             RVS:=[];
             for rel in rels do
               w := LHS(rel)*RHS(rel)^-1;
               Append(~RVS,
             subSpresM!Eltseq(subSM!SM!Eltseq(w@quoSsubmap@rtopc@ptom)));
             end for;
             liftpres := ModuleExtension(subSpresM,RVS);
           end if;
         else
           liftpres := Spres;
         end if;
         Append(~ES,rec<RF | subgroup:=liftsub, presentation:=liftpres,
			//	order:=#liftsubB div #B, length:=classlen,
			order:=subrec`order * p^subdim, length:=classlen,
                                index := subrec`index * p^quodim >);
       else
         Append(~ES,rec<RF | subgroup:=liftsub,
			//	order:=#liftsubB div #B, length:=classlen,
			order:=subrec`order * p^subdim, length:=classlen,
                                index := subrec`index * p^quodim >);
       end if;
       nlifts +:= 1;
     end for;
     if  nc gt 1 and normsubS ne SA and subrec`order ge quolimit then
       /* We have to find the action of normsubS on the set of complements,
        * and only take one representative from each orbit of this action.
        */
       if Print gt 2 then
         print "       +Calculating normaliser action on complements (2).";
       end if;
       normgens := [];
       sns := SA;
       for gen in Generators(normsubS) do
         if not gen in sns then
           Append(~normgens,gen);
           sns := sub<Generic(G)|sns,gen>;
         end if;
       end for;
       //normgens := [ gen : gen in Generators(normsubS) | not gen in SA ];
       if Print gt 2 then
         print "        ",#normgens,"normalising generators for this subgroup.";
       end if;
       ngp := [];
       sublist := {@ sub<Generic(G)|B,e`subgroup> :  e in ES @};
       smallind := Index(SA,sublist[1]) le translimit;
       if smallind then
         trans := [ Transversal(SA, Normaliser(SA,s) ) : s in sublist];
       end if;
       for i in [1..#normgens] do
         ngp[i] := [];
         gen := normgens[i];
         for c in [1..nc] do
           if smallind then
             for t in trans[c] do
               d := Position(sublist, sublist[c]^(t*gen));
               if d gt 0 then
                 ngp[i][c] := d;
                 break;
               end if;
             end for;
           else
             conjsub:=sublist[c]^gen;
             for d in [1..nc] do
               if IsConjugate(SA,conjsub,sublist[d]) then
                 ngp[i][c] := d;
                 break;
               end if;
             end for;
           end if;
         end for;
       end for;
       ngorbs := Orbits( sub<Sym(nc)|ngp> );
       ESR := [];
       for  l in [1..#ngorbs] do
         repsub := ES[Representative(ngorbs[l])];
         repsub`length *:= #ngorbs[l];
         Append(~ESR,repsub);
       end for;
       //print "       -",#ESR,"orbits on complements.";
     else
       ESR := ES;
     end if;
     ExtendSubsH := ExtendSubsH cat ESR;

   end if;
 end for;
 //print "    -Total of",nlifts,"liftings of this subgroup found.";
 //print "  +Total of",#ExtendSubsH,"subgroups found at next level.";

 return ExtendSubsH;
end function;

LMGLI := function(G,n : Print:=0);
//alternative version of LMGLowIndexNormalSubgroups using repeated maxsubs
//start inthe same way
  if Print ge 1 then
    "Finding low index subgroups of radical quotient";
  end if;
  r := G`LMGNode;
  rq := r`radquot;
  rad := r`rad;
  Gtorq := r`Gtoradquot;
  lisubs, pres :=
         LowIndexSubgroups(rq, n : Presentation:=false, Print:=Print);
  if Print ge 1 then
     #lisubs, "low index subgroups of radical quotient";
  end if;
  subs1 := [];
  for i in [1..#lisubs] do
    S := lisubs[i];
    H := sub< Generic(G) | [(S.i) @@ Gtorq : i in [1..Ngens(S)] ], rad >;
    H`Order := LMGOrder(G) div Index(rq,S);
    Append(~subs1, H);
  end for;
  ns1 := #subs1;
  subs2 := [];
  trans := [];
  ct := 1;
  while ct le ns1 + #subs2 do
    H := ct le ns1 select subs1[ct] else subs2[ct-ns1];
    if LMGIndex(G,H) le n div 2 then
      if Print ge 1 then 
        "Calling LMGMaximalSubgroups on subgroup of index",LMGIndex(G,H);
      end if;
      max := LMGIndex(G,H) eq 1 select
        [m`subgroup : m in LMGMaximalSubgroups(G) ] else
        [m`subgroup : m in LMGMaximalSubgroups(H) ];
      if Print ge 1 then 
        #max, "maximal subgroups";
      end if;
      for M in max do if LMGIndex(G,M) le n then
        if ct le ns1 and LMGIsSubgroup(M,rad) then
          continue;
        end if;
        if Print ge 2 then "    next: index",LMGIndex(G,M); end if;
        oM := LMGOrder(M);
        new := true;
        for i in [1..#subs2] do
          //for small indices we just try conjugating by transversal elements
          N := subs2[i];
          if oM ne LMGOrder(N) then continue; end if;
          if not IsDefined(trans,i) then
            if Print ge 2 then "    computing a transversal"; end if;
            trans[i] := [u^-1 : u in LMGRightTransversal(G,N)];
            if Print ge 2 then "    done"; end if;
          end if;
          for u in trans[i] do
            if LMGIsSubgroup(N,M^u) then new:=false; break i; end if;
          end for;
        end for;
        if Print ge 2 then "    new:",new; end if;
        if new then
          Append(~subs2,M);
        end if;
      end if; end for;
    end if;
    ct +:= 1;
  end while;
  subs := subs1 cat subs2;
  Sort(~subs,func<x,y|LMGOrder(y)-LMGOrder(x)>);
  return subs;
end function;
  
LISubs := function(G,n : Presentation:=false, Print:=0, Max:=true)
/* use standard LowIndexSubgroupson solvable radical and then lift through
 * layers of chief series.
 */
local RF,r,cs,rpc,rad,rtopc,rq,rm,Gtorq,subord,LL,L,mm,s,k,Res,
      ss,calcpres,pres,lisubs,lisubsl,lisubsfinal;
  RF := recformat<order: RngIntElt,
                 length: RngIntElt,
               subgroup: GrpMat,
           presentation: GrpFP,
                  index: RngIntElt>;
  if Max and not Presentation then 
    return LMGLI(G,n : Print:=Print);
  end if;
  r := G`LMGNode;
  cs := r`cseries;
  rpc := r`radPC;
  rad := r`rad;
  rtopc := r`radtoPC;
  rq := r`radquot;
  rm := r`radmods;
  Gtorq := r`Gtoradquot;
  subord := #rad;

  if Print ge 1 then
     print "Elementary abelian series of length:",#cs-1;
     print "Layer sizes:", [#rm[i][1] : i in [#rm .. 1 by -1]];
  end if;

/* the LowIndexSubgroupsfunction for PC-groups is not very good!
  if #rq eq 1 then //group soluble
    LL := [];
    if Print ge 2 then
       print "Applying LowIndexSubgroups to PC group";
    end if;
    L := LowIndexSubgroups(rpc, n);
    for s in L do
      ss := sub< Generic(G) | [s.i @@ rtopc : i in [1..Ngens(s)]] >;
      Append(~LL,ss);
    end for;
    //LowIndexSubgroups for PC-groups has no presentation option!
    if Presentation then
      return [ rec< RF | subgroup:=l, presentation:=FPGroup(l)> : l in LL]; 
    else return [ rec< RF | subgroup:=l > : l in LL];
    end if;
  end if;
*/

  calcpres := #cs eq 1 select Presentation else true;

  if Print ge 1 then
    "Finding low index subgroups of radical quotient";
  end if;
  lisubs, pres :=
         LowIndexSubgroups(rq, n : Presentation:=calcpres, Print:=Print);
  if Print ge 1 then
     #lisubs, "low index subgroups of radical quotient";
  end if;
  lisubsl := [];
  for i in [1..#lisubs] do
    S := lisubs[i];
    newrec := rec< RF | >;
    newrec`order := #S;
    newrec`index := Index(rq,S);
    newrec`length := Index(rq, Normaliser(rq,S));
    if calcpres then
      newrec`presentation := pres[i];
    end if;
    newrec`subgroup :=
          sub< Generic(G) | [(S.i) @@ Gtorq : i in [1..Ngens(S)] ] >;
    Append(~lisubsl, newrec);
  end for;
  lisubs := lisubsl;

  lisubsfinal := [];
  for i in [#rm .. 1 by -1] do
    calcpres := i eq 1 select Presentation else true;
    lisubsl := [];
    if Print ge 1 then
      print "Extending through layer size ",#rm[i][1];
      print #lisubs,"subgroups";
      print "orders:", [subrec`order : subrec in lisubs];
    end if;
    ct:=0;
    for subrec in lisubs do
      ct +:= 1;
      if Print gt 1 then
        print " Lifting subgroup number",ct,"of",#lisubs,"of order",
                subrec`order;
      end if;
      lisubse :=
        ExtendOneSubgroupH(G,i,subrec,n,calcpres:Print:=Print);
      for subrece in lisubse do
        cps := subrece;
        if cps`index gt n div 2 then
          cps`subgroup := sub< Generic(G) | subrece`subgroup, cs[i] >;
          cps`order := #G div cps`index;
          Append(~lisubsfinal, cps);
        else
          Append(~lisubsl, subrece);
        end if;
      end for;
    end for;
    lisubs := lisubsl;
  end for;

  lisubs := lisubsfinal cat lisubsl;
  Sort(~lisubs,func<x,y|y`order-x`order>);
  for i in [1..#lisubs] do
    AssertAttribute(lisubs[i]`subgroup,"Order",lisubs[i]`order);
  end for;

  return lisubs;
end function;
