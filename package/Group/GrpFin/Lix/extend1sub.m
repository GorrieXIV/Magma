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

LowIndexSubmodulesH := function(M,codim)
//No longer needed -  use Submodules(M, CodimensionLimit:=codim)
/* M is a KG-module for G finite group, K finite field.
 * Return all submodules of codimension up to codim
 * by repeatedly calling 'MaximalSubmodules'
 */
  local dM, S, lcdsub, ct, L;
  dM := Dimension(M);
  S := MaximalSubmodules(M);
  lcdsubs := [m : m in S | dM-Dimension(m) le codim] cat [M];
  Sort(~lcdsubs,func<x,y|Dimension(y)-Dimension(x)>);
  ct := 2;
  while ct le #lcdsubs do
    L := lcdsubs[ct];
    if dM-Dimension(L) eq codim then
      break;
    end if;
    S := MaximalSubmodules(L);
    for m in S do
      if dM-Dimension(m) le codim and not m in lcdsubs then
        Append(~lcdsubs,m);
      end if;
    end for;
    Sort(~lcdsubs,func<x,y|Dimension(y)-Dimension(x)>);
    ct := ct+1;
  end while;
  return lcdsubs;
end function;

ExtendOneSubgroupH := function(G,A,B,subrec,maxind,calcpres:Print:=0)
/* A and B are normal subgroups of the permutation group G with
 * B < A and A/B elementary abelian.
 * subrec is a record defining a subgroup H/A of G/A, and a
 * corresponding list of records defining subgroups of G/B of index
 * at most maxind that map onto H/A is returned.
 * (The subgroups involved are not really subgroups of the quotients
 * G/A and G/B, but subgroups of G that map onto the theoretical
 * subgroups.)
 * If calcpres is true, then presentations for each subgroup in the list
 * returned are calculated.
 */
 local RF, Z, ExtendSubsH, ES, ESR, M, K, dim, p, mindim, phi, RM, L,
       SL, GonSLgens, gen, perm, im, Rep, repgen, S, SA, ngs,
       Spres, Spresmap, nlifts, rels, nrs, rel, w, normS, ngns,
       normSonSL, nS2nSonSL, normSonSLgens, FixS, OFixS, RV, RVQ, RVS,
       orb, rep, orbreps, intmorph, normsubS, sns, normsubSonSL, subdim,
       quodim, SM, subSM, quoSM, projSM, SpresM, subSpresM, repquoSM,
       repsubSM, split, Comps, Compreps, Comporblens, Compact, comp, nc,
       CCS, imcomp, normgens, wordgp, quoSA, quoSAg, projSA,
       wgtoG, wgtoqSp, word, tail, wm,
       ngp, ngactgp, ngorbs, classlenA, classlen,
       quoSMtoG, subSMtoG,
       liftgens, liftpres, liftsub, liftsubB, intsub, vec,
       longtail, longvec, mat, i, j, k, c, d, conjsub, quolimit,
       translimit, repsub;

 quolimit := 2000;
 translimit := 32;
 RF := Format(subrec);
 Z := Integers();
 ExtendSubsH := []; /* This will be the lifted subgroup-list to be returned. */

 M, phi := GModule(G,A,B);
 K := BaseRing(M);
 p := Characteristic(K);
 dim := Dimension(M);
 S:=subrec`subgroup;
 SA := sub< Generic(G) |A,S>;
 ngs:=Ngens(S);
 AssertAttribute(SA, "Order", #G div subrec`index);
 mindim := Minimum(
        [ d : d in [0..dim] | subrec`index * p^(dim-d) le maxind ] );

 if mindim eq dim then
   src := subrec;
   
   liftgens := SA eq A select [M.i @@ phi : i in [1..dim]]
               else [S.i : i in [1..ngs]] cat [M.i @@ phi : i in [1..dim]];
   src`subgroup := sub< G | liftgens >;
   src`order *:= p^dim; 
   if SA eq A then
     src`presentation := ElementaryAbelianPresentation(#BaseRing(M),dim);
   else 
     Spres := src`presentation;
     repsubSM := Representation(M);
     subSpresM := GModule(Spres,[(S.i)@repsubSM : i in [1..ngs] ]);
     quoSsubmap := hom< Spres->G | [ liftgens[i] : i in [1..ngs] ] >;
             // Once again, this is not a genuine homomorphism! 
     RVS:=[];
     rels:=Relations(Spres);
     for rel in rels do
          w := LHS(rel)*RHS(rel)^-1;
          Append(~RVS,subSpresM!Eltseq(M!(w@quoSsubmap@phi)));
     end for;
     src`presentation := ModuleExtension(subSpresM,RVS);
   end if;
   return [src];
 end if;

 RM := Restriction(M,S);
 SL := Submodules(RM : CodimensionLimit:=dim-mindim);
 SLI := {@ Eltseq( EchelonForm(Morphism(U, RM)) ) : U in SL @};
 normS := Normaliser(G,SA);
 indnormS := Index(G,normS);
 /* We want representatives of the orbits of normS in its conjugation
  * action on SL. So set up that action.
  */
 if Print gt 1 or (Print eq 1 and #SL gt 512) then
   print "  +Setting up action of group on",#SL,"subgroups of layer.";
 end if;
 Rep := Representation(M);
 ngns := Ngens(normS);
 normSonSLgens := [];
 for i in [1..ngns] do
   perm := [];
   repgen := Rep(normS.i);
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
   Spresmap := hom< Spres->S | [ Id(S) ] >;
 else
   Spresmap := hom< Spres->S | [ S.i : i in [1..ngs] ] >;
 end if;
 /* This is not a genuine homomorphism - the whole point is that we want to
  * work out the images of the relators of Spres in A/B
  */
 rels:=Relations(Spres);
 nrs:=#rels;
 RV:=[];
 for rel in rels do
   w := LHS(rel)*RHS(rel)^-1;
   Append(~RV,w@Spresmap@phi);
 end for;
 nlifts:=0;
 for rep in orbreps do
   quolimit := 1000;
   intmorph:=Morphism(SL[rep],RM);
   normsubSonSL := Stabiliser(normSonSL,rep);
   indnormsubS := indnormS * #Orbit(normSonSL,rep);
   normsubS := sub<  Generic(G)  | normsubSonSL@@nS2nSonSL >;
   
   /* We are now going to find those subgroups of G/B which intersect
    * A/B in the subgroup phi^-1(intmorph).
    * We need to regard this subgroup as a module for normsubS
    */
   subdim := Dimension(Image(intmorph));
   quodim := dim-subdim;
   SM := Restriction(M,normsubS);
   subSM := sub< SM | [ SM!(intmorph[i]) : i in [1..subdim] ] >;
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
   if quodim ne 0  and A ne G then
     repquoSM := Representation(quoSM);
     SpresM := ngs eq 0 select
               GModule(Spres,[Id(S)@repquoSM]) else
               GModule(Spres,[(S.i)@repquoSM : i in [1..ngs] ]); 
     //if not CheckRels(SpresM) then
     //  error "Error in quotient-module matrices.";
     //end if;
     /*  We need to coerce the values of RV into this module 
      */
     RVQ := [ SpresM!Eltseq((SM!RV[i])@projSM) : i in [1..nrs] ];
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
	classlenA := (#K)^Dimension(CCS);
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
     //if  nc gt 1 and normsubS ne SA and Index(SA,A) lt quolimit then
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
         if not gen in sns then
           Append(~normgens,gen);
           sns := sub< Generic(G) |sns,gen>;
         end if;
       end for;
       //normgens := [ gen : gen in Generators(normsubS) | not gen in SA ];
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
            hom<wordgp->G | [Id(S)] > else
            hom<wordgp->G | [S.i : i in [1..ngs] ] >;
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
             (SM!((S.j^-1*gen*(w@wgtoG)*gen^-1)@phi))@projSM;
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
           longvec := VectorSpace(K,ngs*quodim)!longvec;
           vec, longvec := DecomposeVector(CCS,longvec);
           /* longvec lies in the complement of CCS, and can be split up
            * to give the image complement - we also must add in the tail.
            */
           imcomp := [];
           vec := SpresM!0;
           for j in [1..ngs] do
             for k in [1..quodim] do
               vec[k] := longvec[(j-1)*quodim+k];
             end for;
             Append(~imcomp,vec);
           end for;
           k := Position(Comps,imcomp);
           if k eq 0 then
             //print CCS, Comps, imcomp;
             error "Image of complement under conjugation is not in list!";
           end if;
           ngp[i][c] := k;
         end for;
       end for;
       ngactgp := sub<Sym(nc)|ngp>;
       ngorbs := Orbits(ngactgp);
       Compreps := [ Comps[Representative(ngorbs[k])] : k in [1..#ngorbs] ];
	 Comporblens := [#(ngorbs[k]) : k in  [1..#ngorbs] ];
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
     quoSMtoG := [ (M!((quoSM.i)@@projSM))@@phi : i in [1..quodim] ];
     subSMtoG := [ (M!intmorph[i])@@phi : i in [1..subdim] ];
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
       if A ne G or subdim eq 0 then 
         for i in [1..ngs] do
           gen := S.i;
           if not gen in A then //gen only in A when S trivial
             vec := comp[i];
             for j in [1..quodim] do
               gen := gen * quoSMtoG[j]^(Z!vec[j]);
             end for;
             Append(~liftgens,gen);
           end if;
         end for;
       end if;
       //liftgens := liftgens cat subSMtoG;
       liftgens := SA eq A select subSMtoG else liftgens cat subSMtoG;
       liftsub := sub< Generic(G) | liftgens >;
       liftsubB := sub< Generic(G) | B, liftgens >;
       /* To get the presentation, we need to work out the relation values
        * as elements of subSM
        */
       if (calcpres) then
         if subdim ne 0 then
           if SA eq A then
             liftpres := ElementaryAbelianPresentation(#BaseRing(M),subdim);
           else
             repsubSM := Representation(subSM);
             subSpresM := ngs eq 0 select
                GModule(Spres,[Id(S)@repsubSM]) else
                GModule(Spres,[(S.i)@repsubSM : i in [1..ngs] ]);
             //if not CheckRels(subSpresM) then
             //  error "Error in submodule matrices.";
             //end if;
             quoSsubmap :=
                 hom< Spres->G | [ liftgens[i] : i in [1..ngs] ] >;
             /* Once again, this is not a genuine homomorphism! */
             RVS:=[];
             for rel in rels do
               w := LHS(rel)*RHS(rel)^-1;
               Append(~RVS,subSpresM!Eltseq(subSM!SM!(w@quoSsubmap@phi)));
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
     //if  nc gt 1 and normsubS ne SA and Index(SA,A) ge quolimit then
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
       for  k in [1..#ngorbs] do
         repsub := ES[Representative(ngorbs[k])];
         repsub`length *:= #ngorbs[k];
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
