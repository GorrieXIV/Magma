freeze;

/*
Package written by Derek Holt - last update Dec 2002 -
to compute maximal subgroups of a permutation group.
*/

forward MaxSubsTF;
import "identify.m":IdentifyAlmostSimpleGroupH;
import "oddfns.m":IsHomomorphismH, PermRepAlmostSimpleGroupH,
   DirectProductWithEmbeddingsAndProjectionsH,
   IsConjugateSequencesH,PresentationSubgroupTF,SubgroupTF,
   PermutationRepresentationSumH, WreathComplementTail,
   MinimalOvergroupsH, ConjugatingElement;
import "oldmaxcomp.m":PType1Maximals,PType2Maximals,PType3Maximals,
                      PType4Maximals,PType5Maximals,PMaxSubsH;
import "maxsubsmodn.m": MaxSubsModN;
import "../../GrpFin/Lix/lifns.m" : MustCover;

intrinsic
 MaximalSubgroupsTF(G::GrpPerm :Print:=0,SmallSimpleFactor:=5000,
                                 Presentation:=false) -> SeqEnum
{  G should be a permutation group with trivial soluble radical (i.e. a
  TF-group). The maximal subgroups of G are computed, including G.
  A list subgroup records is returned.
}
  if Category(G) ne GrpPerm then
    error "Argument for MaximalSubgroupsTF must be a permutation group";
  end if;
  if #SolubleRadical(G) ne 1 then
    error "Soluble radical of group must be trivial in MaximalSubgroupsTF";
  end if;

  return MaxSubsTF(G, sub<G|> :Print:=Print,SSF:=SmallSimpleFactor,
                                                  Presentation:=Presentation);
end intrinsic;

intrinsic
 MaxSubsTF2(G::GrpPerm, Print::RngIntElt: Presentation:=false) -> SeqEnum
{For internal use};
  if Category(G) ne GrpPerm then
    error "Argument for MaximalSubgroupsTF must be a permutation group";
  end if;
  if #SolubleRadical(G) ne 1 then
    error "Soluble radical of group must be trivial in MaximalSubgroupsTF";
  end if;

  return MaxSubsTF(G, sub<G|> :Print:=Print,SSF:=5000,
                                             Presentation:=Presentation);
end intrinsic;

intrinsic
 MaxSubsTF4(G::GrpPerm, Print::RngIntElt, TrivRad::BoolElt, Pres::BoolElt) -> SeqEnum
{For internal use};
  if Category(G) ne GrpPerm then
    error "Argument for MaximalSubgroupsTF must be a permutation group";
  end if;
  if #SolubleRadical(G) ne 1 then
    error "Soluble radical of group must be trivial in MaximalSubgroupsTF";
  end if;

  return MaxSubsTF(G, sub<G|> :Print:=Print,SSF:=5000, TrivRad:=TrivRad,
                                               Presentation:=Pres);
end intrinsic;

intrinsic
 MaximalSubgroupsH(G::GrpPerm, N::GrpPerm :Print:=0,SmallSimpleFactor:=5000,
                        maxind:=0,radprimes:={},Presentation:=false) -> SeqEnum
{ Find maximal subgroups of G modulo the soluble normal subgroup N.
  Use MaximalSubgroupsTF on the radical quotient where necessary.
  A list subgroup records is returned.
}
  if Category(G) ne GrpPerm  or Category(N) ne GrpPerm then
    error "Arguments for MaximalSubgroupsH must be permutation groups";
  end if;
  if not N subset G or not IsNormal(G,N) then
    error "Arg. 2 of MaximalSubgroupsH must be normal in Arg. 1";
  end if;

  return PMaxSubsH(G,N:Print:=Print,SSF:=SmallSimpleFactor,
          maxind:=maxind,radprimes:=radprimes, Presentation:=Presentation);
end intrinsic;
 
intrinsic
 MaximalSubgroupsH(G::GrpPerm :Print:=0,SmallSimpleFactor:=5000,
                    maxind:=0,radprimes:={},Presentation:=false) -> SeqEnum
{ Find maximal subgroups of G.
  Use MaximalSubgroupsTF on the radical quotient where necessary.
  A list of subgroup records is returned.
  if maxind > 0 then return only subgps of index at most maxind
}
  if Category(G) ne GrpPerm  then
    error "Argument for MaximalSubgroupsH must be permutation group";
  end if;

  return PMaxSubsH(G,sub<G|>:Print:=Print,SSF:=SmallSimpleFactor,
         maxind:=maxind,radprimes:=radprimes,Presentation:=Presentation);
end intrinsic;
 

forward Type4Maximals, Type5Maximals, WreathProductEmbeddings;
MaxSubsTF := function(G,S:Print:=0,SSF:=5000,TrivRad:=false,
                                 maxind:=0,radprimes:={},Presentation:=false)
/* G should be a permutation group with trivial soluble radical (i.e. a
 * TF-group). The maximal subgroups of G are computed, including G.
 * Normally this function will be applied to TF-groups in which the socle
 * is not simple, and the socle factors are fairly small groups.
 * The second group S is usually sub<G|> and ignored, but on recursive
 * calls to MaxSubsTF it may be one of the socle factors of G, for which
 * we are specifically seeking Type 3 (2-orbit diagonal) maximals.
 * if maxind > 0 then return only subgps of index at most maxind
 */
  local RFG, RFMSTF, GR, SA, SP, SAK, SQ, pSQ, M, SF, nSF, O, SC, socreps,
        projlist, fac, cfac, gens1, gens2, pQ, Q, X, SPX, rho, RM, m, OI,
        k, calc;

  RFG := recformat<order:RngIntElt, length:RngIntElt,
                      subgroup:GrpPerm, presentation:GrpFP>;

  RFMSTF := recformat<
          group: GrpPerm,   // The group G
             SF: SeqEnum,   // list of socle factors of G
             SA: Map,       // perm. action of G on socle factors
            pSQ: Map,       // projection of G onto its socle quotient
          socle: GrpPerm,   // the socle of G
        socreps: SeqEnum,   // list of orbit rep. numbers of SA on SF
        genlist: SeqEnum,   // genlist[i]=generators of i-th socle factor
       projlist: SeqEnum,   // projlist[i]=projection of <S,C_G(S)> onto
			    // S, where S=SF[i].
       preslist: SeqEnum,   // preslist[i]=presentation of SF[i].
         fplist: SeqEnum,   // fplist[i]=isomorphism from preslist[i] SF[i].
   asembeddings: List,      // asembeddings[i]=embedding of normaliser of
			    // SF[socreps[i]] mod centraliser in almost simple
			    // group.
   wpembeddings: SeqEnum,   // wpembeddings[i]=wreath product embedding of
                            // SF[socreps[i]].
   transversals: SeqEnum,   // transversals[i]=transversal of normaliser of
                            // SF[socreps[i]] in G.
         msints: SeqEnum,   // msints[i]=maximal subgroups intersections of
			    // almost simple group of SF[socreps[i]].
        maxsubs: SeqEnum,   // list of records for amximal subgroups
     modsocgens: SeqEnum,   // a list of generators of G mod Socle(G)
     printlevel: RngIntElt, // = 0,1,2,3 - level of diagnostic printing
 smallsimplefactor: RngIntElt, // - order for use of regular rep. of socle
	trivrad:  BoolElt,  // true if called on group with trivial radical
            RFG: RecFrmt,   // standard recformat for subgroups.
   presentation: BoolElt    //true if presentations of maximals required
  >;
         
  GR := rec< RFMSTF | group:=G, RFG:=RFG, maxsubs:=[], printlevel:=Print,
                      smallsimplefactor:=SSF, trivrad := TrivRad,
                      presentation:=Presentation >;

  if IsTrivial(G) then
    n := Max(Ngens(G), 1);
    pres := quo<FreeGroup(n)|[$.i: i in [1..n]]>;
    return [ rec<RFG| order := 1, subgroup := G, length := 1,
          presentation := pres >];
  end if;

  if not Presentation and Degree(G) ge 10 and IsAltsym(G) then
    res := MaximalSubgroupsAltSym(G);
    rec:=rec<GR`RFG|>;
    F, phi := FPGroupStrong(G);
    G := sub< G | [phi(F.i) : i in [1..Ngens(F)]] >;
    rec`subgroup := G;
    rec`presentation := F;
    rec`length := 1;
    rec`order := #G;
    Append(~res, rec);
    return res;
  end if;

  SA,SP,SAK := SocleAction(G);
  SQ, pSQ, M := SocleQuotient(G);
  SF:=SocleFactors(G);
  nSF := #SF;
  O := Orbits(SP);
  socreps := [ Representative(o) : o in Orbits(SP) ];

  GR`SF:=SF; 
  GR`SA := SA;
  GR`pSQ := pSQ;
  GR`socle := M;
  GR`socreps := socreps;

  projlist:=[];
  for k in [1..nSF] do
    fac := SF[k];
    gens1 := [fac.i : i in [1..Ngens(fac)]];
    // cfac := Centraliser(G,fac); Bill U change - next 2 lines
    nfac := Stabiliser(SP, k) @@ SA;
    cfac := Centraliser(nfac, fac);
    gens2 :=  [cfac.i : i in [1..Ngens(cfac)]];
    SC := sub< G | gens1 cat gens2 >;
    AssertAttribute(SC,"Order",#fac * #cfac);
    RandomSchreier(SC);
    projlist[k] := hom< SC->fac | gens1 cat [Id(fac) : x in [1..#gens2]] >;
  end for;

  GR`projlist := projlist;

  /* The following lists are computed on the first loop through the
   * representative socle factors - this is before we start finding
   * maximal subgroups.
   */
  GR`wpembeddings:=[];
  GR`transversals:=[];
  GR`asembeddings:=[**];
  GR`msints := [];
  GR`genlist:=[];
  GR`preslist:=[];
  GR`fplist:=[PowerStructure(Map)|];

  WreathProductEmbeddings(~GR : maxind:=maxind,radprimes:=radprimes);
  // Find generators of G mod Socle(G).
  H := sub<SQ|>;
  while H ne SQ do
    x := Random(SQ);
    if not x in H then
      H := sub<SQ|H,x>;
    end if;
  end while;
  GR`modsocgens := [x @@ pSQ : x in Generators(H)];
  // assert sub<G|GR`modsocgens, GR`socle> eq G;

  // Now we can start finding the maximal subgroups.
  if #S eq 1 then
    for srino in [1..#socreps] do
      if maxind gt 0 then //may be able to ignore this factor
        calc := not MustCover(SF[socreps[srino]],maxind,radprimes);
      else calc := true;
      end if;
      if calc then PType1Maximals(~GR,srino); end if;
      if maxind eq 0 or maxind ge #SF[socreps[srino]] then
        PType2Maximals(~GR,srino);
      end if;
  
      /* if the action of SP on the orbits other than srino is not soluble
       * then we could conceivably get some Type 3 maximals recursively,
       * by first factoring out the socle factors in the other orbits.
       * We have to investigate that possibility!
       * First get action of SP on other orbits
       */
      if maxind eq 0 or maxind ge #SF[socreps[srino]] then
        X:={};
        for i in [1..#O] do if i ne srino then
          X := X join O[i];
        end if; end for;
        SPX := X eq {} select sub<SP|> else OrbitImage(SP,X);
        rho := GR`wpembeddings[srino][1];
        if not IsSoluble(SPX) and #SPX ge #Image(rho) then 
          // Must try this out! We form a perm. rep. of the required quotient
          // by summing the representations given by rho and pSQ
          pQ1, Q1 := 
            PermutationRepresentationSumH(G,[PowerStructure(Map)|rho,pSQ]);
  	Q, pRQ := RadicalQuotient(Q1);
  	pQ := pQ1 * pRQ;
          if Print gt 0 then 
            print
            "RECURSIVE CALL of MaximalSubgroupsTF to quotient of order",#Q;
          end if;
          RM := MaxSubsTF(Q,pQ(SF[socreps[srino]]) : Print:=Print,SSF:=SSF,
  		 Presentation:=Presentation );
          if Print gt 0 then 
            print "END OF RECURSIVE CALL";
          end if;
          for i in [1..#RM] do
            m := RM[i];
            if GR`presentation then
               sri := socreps[srino];
               newgenlist:=GR`genlist;
               newpreslist:=GR`preslist;
               for t in GR`transversals[srino] do
                 newgenlist[sri^(GR`SA)(t)]:=[];
               end for;
               H := m`subgroup;
               newgenlist[nSF+1] := [ (H.i)@@pQ : i in [1..Ngens(H)] ];
               if #Kernel(pRQ) gt 1 then
                  newgenlist[nSF+1]  := newgenlist[nSF+1] cat
                              [g@@pQ1 : g in Generators(Kernel(pRQ))];
               end if;
               //we have to re-calculate presentation of G/socle in this case!
               H := sub< G | newgenlist[nSF+1] >;
               pSQH := hom< H->SQ | [pSQ(g) : g in newgenlist[nSF+1]] >;
               SQH := sub< SQ | [pSQ(g) : g in newgenlist[nSF+1]] >;
               if #SQH le GR`smallsimplefactor then
                  F,phi := FPGroup(SQH:StrongGenerators:=false);
               else
                  F,phi := FPGroup(SQH:StrongGenerators:=true);
               end if;
               newpreslist[nSF+1] := F;
               for i in [Ngens(SQH)+1..Ngens(F)] do
                 Append(~newgenlist[nSF+1],F.i @ phi @@ pSQH);
               end for;
  
               m`subgroup, m`presentation := PresentationSubgroupTF
                           (newgenlist,newpreslist,GR`projlist,GR`fplist);
            else m`subgroup := (m`subgroup) @@ pQ;
            end if;
            m`order := #m`subgroup;
            Append(~GR`maxsubs,m);
          end for; //for i in [1..#RM] do
        end if; //if not IsSoluble(SPX) and #SPX ge #Image(rho) then
      end if; //if maxind eq 0 or maxind ge #SF[socreps[srino]] then
    end for; //for srino in [1..#socreps] do
  end if; //if #S eq 1 then

  /* Now the Type 3 maximals - those that are diagonals across two equivalent
   * orbits of the socle factors
   */
  for srino in [1..#socreps] do
    if maxind eq 0 or maxind ge #SF[socreps[srino]] then
      if #S gt 1 and not IsConjugate(G,S,SF[socreps[srino]]) then
        continue;
      end if;
      for srjno in [1..#socreps] do
        if srjno eq srino then
          if #S eq 1 then break;
          else continue;
          end if;
        end if;
        PType3Maximals(~GR,srino,srjno);
      end for;
    end if;
  end for;

  if #S gt 1 then
    return GR`maxsubs;
  end if;
  for srino in [1..#socreps] do
    if maxind eq 0 or maxind ge #SF[socreps[srino]]^6 then
      OI := OrbitImage(SP,Orbit(SP,socreps[srino]));
      if #OI ge 6 and not IsSoluble(Stabiliser(OI,1)) then
    // there could be Type 4 maximals (twisted wreathproduct types)
        PType4Maximals(~GR,srino);
      end if;
    end if;
  end for;

  PType5Maximals(~GR);

  if maxind ne 0 then
    return [m : m in GR`maxsubs | Index(G,m`subgroup) le maxind];
  end if;
  return GR`maxsubs;
end function;

WreathProductEmbeddings := procedure(~GR : maxind:=0,radprimes:={})
/* Calculate the wreath product embeddings associated with the orbits of
 * the socle action on the socle factors of G.
 */
  local G, sri, socreps, SF, Print, SA, genlist, pl, 
        N, psi, A, msilist, theta, P, dP, T, t, F, Fhom, phi, W, eG, eP,
        ims, im, rho, calc;

  G:=GR`group;
  socreps:=GR`socreps;
  SF:=GR`SF;
  SA:=GR`SA;
  genlist:=GR`genlist;
  Print:=GR`printlevel;

  for srino in [1..#socreps] do
    sri:=socreps[srino];
    pl := (GR`projlist)[sri];
    S := SF[sri];
    calc := maxind gt 0 select not MustCover(S,maxind,radprimes) else true;
    if Print gt 0 then
      print "Considering socle factor number ",sri;
      if not calc then
        "All maximals of sufficiently low index must cover this factor";
      end if;
    end if;
    if Print gt 1 then
      print S;
    end if;
    N := Stabilizer(Image(SA), sri) @@ SA;
    // assert N eq Normaliser(G,S);
    if calc then 
      psi, A, msilist, F, Fhom := IdentifyAlmostSimpleGroupH(S,N,Print);
    else
      A := S;
      for g in Generators(N) do if not g in A then
        A := sub< G | A,g >;
      end if; end for;
      psi := hom< A -> A | [A.i : i in [1..Ngens(A)]] >;
      msilist := [PowerStructure(Rec)|];
    end if;

    //msilist can contain trivial subgroup generators, which can cause
    //problems later, so eliminate
    for i in [1.. #msilist] do
      if Id(A) in msilist[i]`generators then
        badrec := msilist[i];
        repeat Exclude(~badrec`generators,Id(A));
        until not Id(A) in badrec`generators;
        msilist[i] := badrec;
      end if;
    end for;

    theta,P := CosetAction(G,N);
    dP := Degree(P);
    T:=[G|Id(G)]; // transversal of N in G.
    for i in [2..dP] do
      _,t := IsConjugate(P,1,i);
      T[i] := t@@theta;
    end for;

    genlist[sri]:=[G|];
    for i in [1..Ngens(A)] do if A.i in Socle(A) then
      g := A.i @@ psi @ pl;
      if not g eq Id(G) and not g in genlist[sri] and
                                       not g^-1 in genlist[sri] then
        Append(~genlist[sri],g);
      end if;
    end if; end for;

    for t in T do if t ne Id(G) then
      srit:=sri^SA(t);
      genlist[srit]:=[G| g^t : g in genlist[sri] ];
    end if; end for;
    for t in T do
      srit:=sri^SA(t);
      compsub:=sub<G|genlist[srit]>;
      compsub`Order := #S; // BEWARE - Bill U's addition
      if #compsub le GR`smallsimplefactor then
        F,phi := FPGroup(compsub);
        GR`preslist[srit]:=F;
        GR`fplist[srit] := phi;
/* Surely Ngens(F) = Ngens(compsub) in this case ? */
        for i in [Ngens(compsub)+1..Ngens(F)] do
          error "This cannot be!";
          Append(~genlist[srit],phi(F.i));
        end for;
      else
        if assigned Fhom then
          phi := hom < F->compsub | x :-> (x @ Fhom @@ psi @ pl)^t,
                                     x :-> (x^(t^-1)) @@ pl @ psi @@ Fhom >;
        else
          F,phi := FPGroupStrong(compsub);
        end if;
        GR`preslist[srit]:=F;
        GR`fplist[srit] := phi;
        for i in [Ngens(compsub)+1..Ngens(F)] do
          Append(~genlist[srit],phi(F.i));
        end for;
      end if;
    end for;

    /* Next we define the natural map rho: G -> A Wr P (with image
     * contained in N/C Wr P) induced by the insertion N -> G.
     */
    W, eG, eP := WreathProduct(A, Sym(dP));
    // We use Sym(dP) rather than P as the second factor, because we may need
    // the embedding into Sym(dP) for Type 3 maximals below.
    ims:=[W|];
    for g in [G.i : i in [1..Ngens(G)] ] do
      im := g @ theta @ eP;
      for i in [1..dP] do
        t := T[i];
        tcomp := (T[1^theta(t*g^-1)] * g * t^-1) @ psi @ eG[i];
        im := im * tcomp;
      end for;
      Append(~ims,im);
    end for;
    rho := hom<G->W| ims >;
    // rho is an embedding taking S to the first factor.
    if Print gt 1 then
      print "  +Constructed embedding into wreath product";
    end if;
    GR`wpembeddings[srino] := <rho,eG>;
    GR`transversals[srino] := T;
    GR`asembeddings[srino] := psi;
    GR`msints[srino] := msilist;
    GR`genlist := genlist;
  end for;
  return;
end procedure;

Type4Maximals := procedure(~GR,srino)
/* Find the maximal subgroups of Type 4 coming from socle factor
 * S = SF[socreps[srino]]. That is, those of twisted wreath product type.
 * They are certain types of complements of the base group in the
 * wreath product, so the computation will be carried out in the image
 * of the wreath product embedding.
 */
  local rho, W, G, eG, A, B, BG, M, SA, SB, SBG, NWA, CWA, NA, 
	CA, pSA, SQ, pSQ,
        pNQ, NQ, T, pT, Comps, C, Ggens, Cgens, Qgens, Cgen, t, u, tail, rec,
        E, D, DT, ims, overgps, gensA, gensCWA, gensD, x, extends, NWAn, CSA;
 
  Print:=GR`printlevel;
  if Print gt 0 then
    print
   "Finding Type 4 (twisted wreath-type) maximal subgroups for socle factor",
     GR`socreps[srino];
  end if;
 
  rho := GR`wpembeddings[srino][1];
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
  SBG := BG  meet G;
  if SBG ne Socle(BG) then
    if Print gt 1 then
      print "  +This is not a twisted wreath product of a simple group.";
    end if;
    return;
  end if;
  SA := A meet SBG;
  SB := B meet SBG;
  NWA := Normaliser(W,A);
  CWA := Centraliser(NWA,A);
  NA := NWA meet G;
  CA := CWA meet NA;
  // NWA = CWA X A, so we will use this fact to get a perm. rep. of NA/(SB)
  gensA := [A.i : i in [1..Ngens(A)]];
  gensCWA := [CWA.i : i in [1..Ngens(CWA)]];
  NWAn := sub < W | gensA cat gensCWA >;
  if NWA ne NWAn then
    error "Normaliser generation error in Type4Maximals";
  end if;
  NWA := NWAn;
  pSA := hom < NWA->A | gensA cat [Id(A): i in [1..Ngens(CWA)]] >;
                                              //projection of NWA onto A.
  pSA := hom < NA->A | a:->pSA(a) >; //restriction to NA.
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
    // This might be maximal
    Cgens:=[];
    for g in Qgens do
      Cgen := g;
      for t in T do
        u := pT(t*g);
        tail := WreathComplementTail(G,SA,SB,C,t*g*u^-1);
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
    // If there are fewer than 42 socle factors, then we can skip the
    // next check.
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
    rec`subgroup := E @@ rho;
    rec`order:=#rec`subgroup; 
    rec`length:=
	IsNormal(GR`group,rec`subgroup) select 1 
	    else Index(GR`group,rec`subgroup);
    Append(~GR`maxsubs,rec);
    if Print gt 0 then
      print "  +Maximal subgroup of order",rec`order, "twisted wreath type.";
      if Print gt 2 then print rec`subgroup; end if;
    end if;
  end for;
  return;
end procedure;

Type5Maximals:=procedure(~GR)
/* Find maximal subgroups containing the socle, including the whole group. */
  local G, SF, nSF, pSQ, SQ, S, newgenlist, rec, Print;

  G:=GR`group;
  SF:=GR`SF;
  pSQ:=GR`pSQ;
  SQ:=Image(pSQ);
  pSQ:=GR`pSQ;
  nSF:=#SF;
  Print:=GR`printlevel;

  if Print gt 0 then
    print "Finding Type 5 maximal subgroups - those containing the socle.";
  end if;
  if #SQ ne 1 then
    S := MaximalSubgroups(SQ);
    for m in S do
      rec:=rec<GR`RFG|>;
      rec`subgroup := (m`subgroup)@@pSQ;
      rec`order := #G div Index(SQ,m`subgroup);
      AssertAttribute(rec`subgroup,"Order",rec`order);
      rec`order:=#rec`subgroup; 
      rec`length:=m`length;
      Append(~GR`maxsubs,rec);
      if Print gt 0 then
        print "  +Maximal subgroup of order",rec`order, "containing socle.";
        if Print gt 2 then print rec`subgroup; end if;
      end if;
    end for;
  end if;

// finally do G.
      newgenlist:=GR`genlist;
      newgenlist[nSF+1] := GR`modsocgens;
      rec:=rec<GR`RFG|>;
      if GR`trivrad then
	rec`subgroup := G;
      else
        rec`subgroup, rec`presentation := 
	PresentationSubgroupTF(newgenlist,GR`preslist,GR`projlist,GR`fplist);
      end if;
      rec`order:=#G; 
      rec`length:=1;
      Append(~GR`maxsubs,rec);
      if Print gt 0 then
	print "  +Full group of order",rec`order;
	if Print gt 2 then print rec`subgroup; end if;
      end if;

end procedure;

intrinsic MaximalSubgroupsN(G::GrpPerm, N::GrpPerm : Print:=0) -> SeqEnum
{Maximal subgroups of permutation group G that contain the normal subgroup
 N of G}
  return MaxSubsModN(G,N : Print:=Print);
end intrinsic;

intrinsic MaximalSubgroupsN(G::GrpMat, N::GrpMat : Print:=0) -> SeqEnum
{Maximal subgroups of matrix group G that contain the normal subgroup
 N of G}
  return MaxSubsModN(G,N : Print:=Print);
end intrinsic;
