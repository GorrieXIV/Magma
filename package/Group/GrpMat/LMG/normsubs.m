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

ExtendOneSubgroupH := function(G,k,subrec,calcpres:Print:=0)
/* k is the layer A/B of the chief series of G that we are lifting through
 * where A := cs[k+1]; B := cs[k];
 * subrec is a record defining a normal subgroup H/A of G/A, and a
 * corresponding list of records defining normal subgroups of G/B
 * that map onto H/A is returned.
 * (The subgroups involved are not really subgroups of the quotients
 * G/A and G/B, but subgroups of G that map onto the theoretical
 * subgroups.)
 * If calcpres is true, then presentations for each subgroup in the list
 * returned are calculated.
 */
 local r,rpc,rad,rtopc,rq,Gtorq,rm,gmacts,m,ptom,mats,cs,
       mgensG,src,
       RF, Z, ExtendSubsH, ES, ESR, dim, p, RM, L,
       SL, gen, perm, im, Rep, repgen, S, SA, ngs,
       Spres, Spresmap, nlifts, rels, nrs, rel, w, RV, RVQ, RVS,
       orb, prep, grep, orbreps, intmorph, sns, subdim,
       quodim, SM, subSM, quoSM, projSM, SpresM, subSpresM, repquoSM,
       split, Comps, Compreps, Comporblens, Compact, comp, nc,
       imcomp, normgens, wordgp, quoSA, quoSAg, projSA,
       wgtoG, wgtoqSp, word, tail, wm,
       ngp, ngactgp, ngorbs, classlenA, classlen,
       quoSMtoG, subSMtoG, QQ, rr, rrC,
       liftgens, liftpres, liftsub, liftsubB, intsub, vec, s, x, dim2,
       longtail, longvec, mat, i, j, c, d, conjsub, quolimit, translimit,
       repsub, SAPC, APC, NPC, QPC, rho, QAPC, A, MQPC, MQAPC, MComps, sgens,MA;

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
 SA := sub< Generic(G) | A,S>;
 ngs:=Ngens(S);

 RM := GModule(S,[MatrixAlgebra(GF(p),dim) | grep(S.i): i in [1..Ngens(S)]]);
 //there are only two possible intersections, zero and RM
 SL := [ sub< RM | >, RM ];

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
 for rep in [1,2] do
   quolimit := 1000;
   intmorph:=Morphism(SL[rep],RM);
   
   /* We are now going to find those subgroups of G/B which intersect
    * A/B in the inverse image in G of intmorph.
    * We need to regard this subgroup as a module for G
    */
   subdim := Dimension(Image(intmorph));
   quodim := dim-subdim;
   SM := GModule(G, [grep(G.i): i in [1..Ngens(G)]]);
   subSM := sub< SM | [ SM!Eltseq(intmorph[i]) : i in [1..subdim] ] >;
   if Print gt 2 then
     print "      +Trying intersection of size",#subSM;
   end if;
   quoSM, projSM := quo<SM|subSM>;
   if Dimension(SL[rep]) eq 0 then
   /* We need to look find conjugacy classes of complements of SM in SA.
    * To do the cohomology calculation, we need to work with the module
    * MQ regarded as being over the finitely presented group Spres.
    */
     if forall{g : g in Generators(S) | LMGIsIn(rad,g) } then
 //we often get lots of complements in this case, so use a different method
       if Print gt 2 then
         print "      +subgroup of radical";
       end if;
       //get PC image of SA and A
       SAPC := sub< rpc | [ SA.i @ rtopc : i in [1..Ngens(SA)] ] >;
       APC := sub< rpc | [ A.i @ rtopc : i in [1..Ngens(A)] ] >;
       //want largest elementary abelian quotient of SAPC/B
       NPC := sub< SAPC | DerivedGroup(SAPC), [ g^p : g in Generators(SAPC)],
                          [ B.i @ rtopc : i in [1..Ngens(B)] ] >; 
       QPC, rho := quo< SAPC | NPC >;
       rhoA := hom< APC -> QPC | [rho(APC.i) : i in [1..NPCGenerators(APC)]] >;
       QAPC := rho(APC);
       if #QAPC ne p^dim then
         if Print gt 2 then
           print "       No complements for this intersection."; 
         end if;
       continue;
       end if;
       //have to make QPC into a G-module
       dim2 := fac[1][2] where fac := FactoredOrder(QPC);
       MA := MatrixAlgebra(GF(p),dim2);
       mats := [ 
     MA!Matrix( 
       [ Eltseq(((QPC.j @@ rho @@ rtopc)^G.i) @ rtopc @ rho) : j in [1..dim2] ]
             ) : i in [1..Ngens(G)]
               ];
       MQPC := GModule(G,mats);
       MQAPC := sub< MQPC | [ MQPC| Eltseq(QPC!g) : g in Generators(QAPC) ] >;
       MComps := Complements(MQPC,MQAPC);
       if Print gt 2 then
         print "      ",#MComps,"complements for this intersection."; 
       end if;
       for c in MComps do
         //we will need to project elements of SA/B onto comp
         QQ, rr := quo< MQPC | c >;
         rrA := hom< MQAPC->QQ | [rr(MQAPC.i) : i in [1..Ngens(MQAPC)]] >;
         sgens := [Generic(G)|];
         for i in [1..Ngens(S)] do
           //multiply S.i by element of A to bring it into complement
           x := (MQPC!Eltseq(S.i @ rtopc @ rho)) @ rr @@ rrA; //in A
           s := Eltseq(Morphism(MQAPC,MQPC)(-x));
           ChangeUniverse(~s,Integers());
           Append(~sgens, S.i * ((QPC!s) @@ rhoA @@ rtopc));
         end for;
         if calcpres then
           Append(~ExtendSubsH, rec<RF | subgroup:=
                 sub< Generic(G) | sgens >,
                      order:=subrec`order * p^subdim,
                      presentation:=Spres, length:=1 > );
          else
           Append(~ExtendSubsH, rec<RF | subgroup:=
                 sub< Generic(G) | sgens >,
                      order:=subrec`order * p^subdim, length:=1 > );
         end if;
       end for;
       continue;
     end if;

     //complements can only give normal subgroups when action of S trivial
     mats := ngs eq 0 select [grep(Id(S))] else [grep(S.i) : i in [1..ngs] ];
     if mats ne [ grep(Id(S)) : i in [1..Ngens(Spres)] ] then
       if Print gt 2 then
         print "       No complements for this intersection."; 
       end if;
       continue;
     end if;
     SpresM := GModule(Spres, mats);
     /*  We need to coerce the values of RV into this module */
     RVQ := [ SpresM!Eltseq(SM!Eltseq(RV[i])) : i in [1..nrs] ];
     /* Now we can do the cohomology calculation at last! */
     split, Comps := ComplementVectors(SpresM,RVQ);
     classlenA := 1;
   else
     split := true;
     Comps := [ [ quoSM!0 : i in [1..ngs] ] ];
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
     if nc ge 2^14 then quolimit := 500000; end if;
     if  nc gt 32 and subrec`order lt quolimit then
       /* We have to find the action of G on the set of complements,
        * and we only want those that are fixed by G.
        * Since this involves forming the quotient SA/A, if this quotient
        * is very large, or if there are very few complements, then
        * we use a more direct method which we do later.
        * First locate the generators of G that we need to use.
        */
       if Print gt 2 then
          print "       +Calculating normaliser action on complements (1).";
       end if;

	/* We're going to want Position's in Comps, so make an 
	 * indexed set of it for efficiency's sake - billu 7/1/04
	 */
       //want to avoid that in big matrix groups
       //Comps := {@ c : c in Comps @};
       //assert #Comps eq nc;

       normgens := [];
       sns := SA;
       for gen in Generators(G) do
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
       /* Now we are ready to work out the action of G on the set
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
         mat := Matrix(grep(gen)^-1);
         for c in [1..nc] do
           comp:=Comps[c];
           /* We need to concatenate all the ngs vectors for the cocycle for
            * the conjugated complement together to get a vector of length
            * ngs*quodim
            */
           longvec := [];
           imcomp := [ SpresM |
                        tail[i][j] + TailVector(SpresM,comp,word[i][j])*mat :
                                        j in [1..ngs] ];
           pos := Position(Comps,imcomp);
           if pos eq 0 then
             error "Image of complement under conjugation is not in list!";
           end if;
           ngp[i][c] := pos;
         end for;
       end for;
       ngactgp := sub<Sym(nc)|ngp>;
       ngorbs := Orbits(ngactgp);
       //only want orbits of length 1
       Compreps := [ Comps[Representative(ngorbs[l])] : l in [1..#ngorbs] |
                                                          #ngorbs[l]  eq 1 ];
       if Print gt 2 then
         print "       -",#Compreps,"orbits of length 1 on complements.";
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
       liftgens := [];
       for i in [1..ngs] do
           gen := S.i;
           vec := comp[i];
           for j in [1..quodim] do
               gen := gen * quoSMtoG[j]^(Z!vec[j]);
           end for;
           Append(~liftgens,gen);
       end for;
       liftgens := ngs eq 0 select subSMtoG else liftgens cat subSMtoG;
       liftsub := sub< Generic(G) | liftgens >;
       /* To get the presentation, we need to work out the relation values
        * as elements of subSM
        */
       if (calcpres) then
         if subdim ne 0 then
           if subrec`order eq 1 then
             liftpres := ElementaryAbelianPresentation(p,subdim);
           else
             subSpresM := ngs eq 0 select
                GModule(Spres,[grep(Id(S))] ) else
                GModule(Spres,[grep(S.i) : i in [1..ngs] ]);
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
			order:=subrec`order * p^subdim, length:=1 >);
       else
         Append(~ES,rec<RF | subgroup:=liftsub,
			order:=subrec`order * p^subdim, length:=1 >);
       end if;
       nlifts +:= 1;
     end for;
     if  nc gt 1 and (nc le 32 or subrec`order ge quolimit) then
       /* We have to calculate directly which complements are normal in G
        */
       if Print gt 2 then
         print "       +Finding normal complements (2).";
       end if;
       sublist := [ sub<Generic(G)|B,e`subgroup> :  e in ES ];
       norminds :=
           [i : i in [1..#sublist] | LMGEqual(sublist[i],sublist[i]^G) ];
       ESR := [ ES[i] : i in norminds ];
     else
       ESR := ES;
     end if;
     ExtendSubsH := ExtendSubsH cat ESR;
   end if;
 end for; //for rep in [1,2] do
 //print "    -Total of",nlifts,"liftings of this subgroup found.";
 //print "  +Total of",#ExtendSubsH,"subgroups found at next level.";

 return ExtendSubsH;
end function;

NormSubs := function(G : Presentation:=false, Print:=0)
/* Use standard NormalSubgroups on solvable radical and then lift through
 * layers of chief series.
 */
local RF,r,cs,rpc,rad,rtopc,rq,rm,Gtorq,subord,LL,L,mm,s,k,Res,
      ss,calcpres,pres,normsubs,normsubsl,normsubsfinal;
  RF := recformat<order: RngIntElt,
                 length: RngIntElt,
               subgroup: GrpMat,
           presentation: GrpFP,
                  index: RngIntElt>;
  r := G`LMGNode;
  cs := r`cseries;
  rpc := r`radPC;
  rad := r`rad;
  rtopc := r`radtoPC;
  rq := r`radquot;
  rm := r`radmods;
  Gtorq := r`Gtoradquot; subord := #rad;

  if Print ge 1 then
     print "Elementary abelian series of length:",#cs-1;
     print "Layer sizes:", [#rm[i][1] : i in [#rm .. 1 by -1]];
  end if;

  calcpres := #cs eq 1 select Presentation else true;

  normsubs := NormalSubgroups(rq : Presentation:=calcpres);
  if Print ge 1 then
     print #normsubs,"normal subgroups of radical quotient";
  end if;

  normsubsl := [];
  for i in [1..#normsubs] do
    newrec := normsubs[i];
    newrec`subgroup :=
          sub< Generic(G) | [(S.i) @@ Gtorq : i in [1..Ngens(S)] ] >
               where S := newrec`subgroup;
    Append(~normsubsl, newrec);
  end for;
  normsubs := normsubsl;

  for i in [#rm .. 1 by -1] do
    calcpres := i eq 1 select Presentation else true;
    normsubsl := [];
    if Print ge 1 then
      print "Extending through layer size ",#rm[i][1];
      print #normsubs,"subgroups to lift";
      print "orders:", [subrec`order : subrec in normsubs];
    end if;
    ct:=0;
    for subrec in normsubs do
      ct +:= 1;
      if Print gt 1 then
        print "    Lifting subgroup number",ct,"of",#normsubs,"of order",
                   subrec`order;
      end if;
      normsubse :=
        ExtendOneSubgroupH(G,i,subrec,calcpres:Print:=Print);
      for subrece in normsubse do
//Type(subrece):Magma;
        Append(~normsubsl, subrece);
      end for;
    end for;
    normsubs := normsubsl;
  end for;

  Sort(~normsubs,func<x,y|x`order-y`order>);
  for subrec in normsubs do
    AssertAttribute(subrec`subgroup,"Order",subrec`order);
  end for;
  return normsubs;
end function;
