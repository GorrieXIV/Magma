freeze;

// NOTE - these functions currently call the functions in ~/maxcomp
forward LiftComplementsElAb, refine_section, section_complements,
        section_supplements, LiftComplementsSection, LiftedPresentation;

// Extension to allow non-abelian normal subgroup. 21/11/99
// Written by Derek Holt.

//========================================================================================
intrinsic Complements(G::GrpPerm, M::GrpPerm : Presentation := 0) -> SeqEnum
{Given a finite permutation group G, with normal subgroup M,
if M has a complement in G return a list of representatives of the conjugacy
classes of complements in G. If M does not have a complement in G, 
the empty sequence is returned}

  if not ISA(Category(G), GrpPerm) then
    error "First argument for Complements must be a perm-group";
  end if;
  if not (ISA(Category(M), GrpPerm) and IsNormal(G,M)) then
    error "Second argument for Complements must be a normal subgroup of first";
  end if;
  require Presentation cmpeq 0 or Type(Presentation) eq GrpFP: "Presentation must be an FP-group";
  if not (Presentation cmpeq 0) and Ngens(G) ne Ngens(Presentation) then
    error "Presentation and G must have corresponding generators";
  end if;
  
  fl, Comps := section_complements(G, M, sub< G | >: comps:=2, presentation := Presentation );
  return Comps;
 
end intrinsic;

//========================================================================================
intrinsic HasComplement(G::GrpPerm, M::GrpPerm : Presentation := 0) -> BoolElt, GrpPerm
{Given a finite permutation group G, with normal subgroup M,
if M has a complement in G return true, otherwise false. A single
complement is also returned.}

  if Category(G) ne GrpPerm then
    error "First argument for HasComplement must be a perm-group";
  end if;
  if Category(M) ne GrpPerm or not IsNormal(G,M) then
    error "Second argument for HasComplement must be a normal subgroup of G";
  end if;
  require Presentation cmpeq 0 or Type(Presentation) eq GrpFP: "Presentation must be an FP-group";
  if not (Presentation cmpeq 0) and Ngens(G) ne Ngens(Presentation) then
    error "Presentation and G must have corresponding generators";
  end if;
  
  fl, C := section_complements(G, M, sub< G | >: comps:=1, presentation:=Presentation );
  if fl then
     return fl, C[1];
  else
     return fl, _;
  end if;
 
end intrinsic;


//========================================================================================
intrinsic RefineSection(G::GrpPerm, M::GrpPerm, N::GrpPerm) -> SeqEnum
{Given a finite permutation group G, with normal subgroups N and M,
such that N <= M, this returns a list L of subgroups of G,
all satisfying N < L[i] < M, such that L[1]/N and L[i+1]/L[i] are
elementary abelian or direct products of nonabelian simple groups
for all i, and L[#L] = M}

  if  not IsNormal(G,M) then
    error
       "Second argument for Complement must be a normal subgroup of G";
  end if;
  if not IsNormal(G,N) then
    error
       "Third argument for Complement must be a normal subgroup of G";
  end if;
  if not N subset M or N eq M then
    error
     "Second argument for Complement must be a proper subgroup of third";
  end if;

  L := refine_section(G, M, N);
  return L;
 
end intrinsic;

intrinsic Complements(G::GrpPerm, M::GrpPerm, N::GrpPerm: Presentation:=0) -> SeqEnum
{Given a finite permutation group G, with normal subgroups N and M,
such that N < M,
if M/N has a complement in G/N return a list of representatives 
of the conjugacy classes of complements in G/N. If M/N does not have a 
complement in G/N, the empty sequence is returned}

  if Category(G) ne GrpPerm then
    error "First argument for Complement must be a perm-group";
  end if;
  if Category(M) ne GrpPerm  or not IsNormal(G,M) then
    error
       "Second argument for Complement must be a normal subgroup of G";
  end if;
  if Category(N) ne GrpPerm  or not IsNormal(G,N) then
    error
       "Third argument for Complement must be a normal subgroup of G";
  end if;
  if not N subset M  or N eq M then
    error
     "Second argument for Complement must be a proper subgroup of third";
  end if;
  require Presentation cmpeq 0 or Type(Presentation) eq GrpFP: "Presentation must be an FP-group";
  if not (Presentation cmpeq 0) and Ngens(G) ne Ngens(Presentation) then
    error "Presentation and G must have corresponding generators";
  end if;
  
  fl, Comp := section_complements(G, M, N: comps:=2, presentation := Presentation );
  return Comp;
 
end intrinsic;

intrinsic Complement(G::GrpPerm, M::GrpPerm, N::GrpPerm: Presentation := 0) -> SeqEnum
{Given a finite permutation group G, with normal subgroups N and M,
such that N < M,
if M/N has a complement in G/N return a list of representatives 
of the conjugacy classes of complements in G/N. If M/N does not have a 
complement in G/N, the empty sequence is returned}

  if Category(G) ne GrpPerm then
    error "First argument for Complement must be a perm-group";
  end if;
  if Category(M) ne GrpPerm  or not IsNormal(G,M) then
    error
       "Second argument for Complement must be a normal subgroup of G";
  end if;
  if Category(N) ne GrpPerm  or not IsNormal(G,N) then
    error
       "Third argument for Complement must be a normal subgroup of G";
  end if;
  if not N subset M  or N eq M then
    error
     "Second argument for Complement must be a proper subgroup of third";
  end if;
  require Presentation cmpeq 0 or Type(Presentation) eq GrpFP: "Presentation must be an FP-group";
  if not (Presentation cmpeq 0) and Ngens(G) ne Ngens(Presentation) then
    error "Presentation and G must have corresponding generators";
  end if;
  
  fl, Comp := section_complements(G, M, N: comps:=2, presentation := Presentation );
  return Comp;
 
end intrinsic;

intrinsic Supplements(G::GrpPerm, M::GrpPerm) -> SeqEnum
{Given a finite permutation group G, with soluble normal subgroup M,
if M has a supplement in G return a list of representatives of the conjugacy
classes of supplements in G. If M does not have a supplement in G, the empty sequence
is returned}

  if Category(G) ne GrpPerm then
    error "First argument for Supplements must be a perm-group";
  end if;
  if Category(M) ne GrpPerm or not IsNormal(G,M) then
    error "Second argument for Supplements must be a normal subgroup of G";
  end if;
  
  fl, Supps := section_supplements(G, M, sub< G | >: supps:=2 );
  return Supps;
 
end intrinsic;

//========================================================================================
intrinsic HasSupplement(G::GrpPerm, M::GrpPerm) -> BoolElt, GrpPerm
{Given a finite permutation group G, with soluble normal subgroup M,
if M has a supplement in G return true, otherwise false. A single
supplement is also returned.}

  if Category(G) ne GrpPerm then
    error "First argument for HasSupplement must be a perm-group";
  end if;
  if Category(M) ne GrpPerm or not IsNormal(G,M) then
    error "Second argument for HasSupplement must be a normal subgroup of G";
  end if;
  
  fl, C := section_supplements(G, M, sub< G | >: supps:=1 );
  if fl then
     return fl, C[1];
  else
     return fl, _;
  end if;
 
end intrinsic;


//========================================================================================
intrinsic Supplements(G::GrpPerm, M::GrpPerm, N::GrpPerm) -> SeqEnum
{Given a finite permutation group G, with normal subgroups N and M,
such that N < M and M/N is soluble,
if M/N has a supplement in G/N return a list of representatives 
of the conjugacy classes of M/N in G/N. If M/N does not have a supplement
in G/N, the empty sequence is returned}

  if Category(G) ne GrpPerm then
    error "First argument for Supplement must be a perm-group";
  end if;
  if Category(M) ne GrpPerm  or not IsNormal(G,M) then
    error
       "Second argument for Supplement must be a normal subgroup of G";
  end if;
  if Category(N) ne GrpPerm  or not IsNormal(G,N) then
    error
       "Third argument for Supplement must be a normal subgroup of G";
  end if;
  if not N subset M  or N eq M then
    error
     "Third argument for Supplement must be a proper subgroup of Second";
  end if;
  
  fl, Supp := section_supplements(G, M, N: supps:=2 );
  return Supp;
 
end intrinsic;

intrinsic Supplement(G::GrpPerm, M::GrpPerm, N::GrpPerm) -> SeqEnum
{Given a finite permutation group G, with normal subgroups N and M,
such that N < M and M/N is soluble,
if M/N has a supplement in G/N return a list of representatives 
of the conjugacy classes of M/N in G/N. If M/N does not have a supplement
in G/N, the empty sequence is returned}

  if Category(G) ne GrpPerm then
    error "First argument for Supplement must be a perm-group";
  end if;
  if Category(M) ne GrpPerm  or not IsNormal(G,M) then
    error
       "Second argument for Supplement must be a normal subgroup of G";
  end if;
  if Category(N) ne GrpPerm  or not IsNormal(G,N) then
    error
       "Third argument for Supplement must be a normal subgroup of G";
  end if;
  if not N subset M  or N eq M then
    error
     "Third argument for Supplement must be a proper subgroup of Second";
  end if;
  
  fl, Supp := section_supplements(G, M, N: supps:=2 );
  return Supp;
 
end intrinsic;

//========================================================================================

section_complements := function(G, M, N: comps:=2, presentation := 0 )

/* G should be a finite permutation group, with normal subgroups N and M,
 * where N < M.
 * SectionComplement decides whether M/N has a complement in G/N, and
 * returns true or false accordingly.
 * If the optional parameter comps=0, that is all it returns.
 * If comps=1 and there are complements, then it returns one complement.
 * If comps=2 (default) and there are complements, then it returns
 * a list of representatives of the conjugacy classes of complements of
 * M/N in G/N.
 */

  local Comps, F, FG, f, rels, split, comp;

  if G eq M then
    if comps eq 0 then
      return true, [];
    end if;
    return true, [N];
  end if;
  if M eq N then
    if comps eq 0 then
      return true, [];
    end if;
    return true, [G];
  end if;

  if presentation cmpeq 0 then
  /* We need to construct a presentation of G/M (and hence of any
   * complements that there are). We do it on the strong generators of
   * G, using the function FPGroup. The generators of M will be added
   * as extra relators, to get the required presentation of G/M.
   */
  FG, f := FPGroupStrong(G);
  rels := [];
  for g in Generators(M) do
    Append(~rels,g@@f);
  end for;
  F := quo<FG | rels>;

  /* The individual complements will be stored as lists of generators,
   * which correspond to those of F and FG.
   * (We store them as lists rather than as subgroups, since some of the
   *  elements in the list might be trivial, and we don't want them to get
   * deleted, or we would ruin the correspondence with F.
   * Initially, there is a single complement (of A/A in G/A).
   */
  Comps := [ [(FG.i)@f : i in [1..Ngens(FG)] ] ];
  else
    F := presentation;
    Comps := [[G.i: i in [1..Ngens(G)]]];
  end if;
  split, Comps := LiftComplementsSection(G,M,N,F,Comps,comps);

  if not split then
    return false, [];
  end if;
  /* Change the complements from lists of generators to genuine subgroups
   * containing N.
   */
  if comps eq 0 then
    Comps := [];
  elif comps eq 1 then
    Comps := [ sub<G|((Generators(N) join SequenceToSet(Comps[1])) diff {Id(G)})>];
  else
    Comps := [ sub<G|((Generators(N) join SequenceToSet(comp)) diff {Id(G)})> : 
		comp in Comps ];
  end if;
  for x in Comps do AssertAttribute(x, "Order", #G div (#M div #N)); end for;
  return true, Comps;

end function;

section_supplements := function(G, M, N: supps:=2 )

/* G should be a finite permutation group, with normal subgroups N and M,
 * where N < M and M/N must be soluble.
 * SectionSupplement decides whether M/N has proper supplements in G/N, and
 * returns true or false accordingly.
 * If the optional parameter comps=0, that is all it returns.
 * If supps=1 and there are supplements, then it returns one supplement.
 * If supps=2 (default) and there are supplements, then it returns
 * a list of representatives of the conjugacy classes of minimal
 * supplements of M/N in G/N.
 */

  local RF, F, FG, f, rels, split, supp, suppsexist,
        L, sol, A, B, len, Supps, MinSupps, m, phi, pres, liftpres,
        ls, lm, lphi, CS, cs, H, suppct, S, Se, lifts, new, T;

  RF:=recformat<supp:SeqEnum, pres: GrpFP, int: ModGrp, modmap: Map>;

  if M eq N then
    return false, [];
  end if;
  if G eq M then
    if supps eq 0 then
      return true, [];
    end if;
    return true, [N];
  end if;

  /* We need to construct a presentation of G/M .
   * We do it on the strong generators of
   * G, using the function FPGroup. The generators of M will be added
   * as extra relators, to get the required presentation of G/M.
   */
  FG, f := FPGroupStrong(G);
  rels := [];
  for g in Generators(M) do
    Append(~rels,g@@f);
  end for;
  F := quo<FG | rels>;

  // Now find an elementary series from N to M to lift through.
  L,sol:=refine_section(G,M,N); len:=#L;
  if not sol then
    error "Error in Supplements routine. The section M/N must be soluble";
  end if;
  index:=[#L[1] div #N];
  for i in [2..len] do Append(~index,Index(L[i],L[i-1])); end for;
  //print "Indices of ascending subgroup chain: ", Reverse(index);

  /* We lift the supplements through the layers A/B of the series, where
   * at each stage we lift only the minimal supplements from the previous
   * stage.
   * During the lifting process, each supplement is stored as a RF record,
   * where the components are
   * supp: list of generators of the supplement mod A
   * pres: presentation of the supplement mod A generators corresponding
   *       to those in the list 'supp'.
   * int : a module representing the current intersection of the supplement
   *       with A/B.
   * modmap: the map from <supp,int> to the module int.
   * Initially, there is a single supplement <G,M>.
   * A supplement S becomes a minimal supplement in an elementary
   * section A/B when it does not split over any maximal normal
   * subgroups of (S meet A)/B.
   */
  suppsexist:=false;
  Supps := [rec<RF| supp:=[f(FG.i) : i in [1..Ngens(FG)] ], pres:=F >];
  A := M;
  for layer in Reverse([1..len]) do
    //print "layer = ",layer;
    MinSupps:=[];
    B := (layer eq 1) select N else L[layer-1];
    // initially all supplements have intersection the whole of A/B.
    CS := [];;
    for s in Supps do
      H := sub<G|s`supp,A>;
      m,phi := GModule(H,A,B);
      cs := s;
      cs`int := m;
      cs`modmap := phi;
      Append(~CS,cs);
    end for;
    Supps := CS;
    /* Now we go through all of the supplements to see if they split 
     * over a maximal submodule of their current intersection with m.
     * A supplement thatdoesn't split becomes a minimal supplement at
     * this layer.
     */
    suppct:=1;
    while suppct le #Supps do
      S := Supps[suppct]`supp;
      m := Supps[suppct]`int;
      phi := Supps[suppct]`modmap;
      pres := Supps[suppct]`pres;
      H := Group(m);
      /* Run through maximal submodules of m */
      lifts:=false;
      if Dimension(m) gt 0 then
        for ms in MaximalSubmodules(m) do
          lifts, LiftSupps := LiftComplementsElAb(G,m@@phi,ms@@phi,pres,[S],2);
          if lifts then
            suppsexist:=true;
            for ES in LiftSupps do
              ls := sub<H | ES, B>;
              if ls meet A eq B then
                Append(~Supps,rec<RF|supp:=ES,pres:=pres,int:=ms,modmap:=phi>);
                //GModule won't work, but Dim(ms)=0, so that's OK.
              else
               lm ,lphi := GModule(ls,ls meet A,B);
                Append(~Supps,
                          rec<RF|supp:=ES,pres:=pres,int:=lm,modmap:=lphi>);
              end if;
            end for;
            break;
          end if;
        end for;
      end if;
   
      if lifts then
        new:=false;
      else
        // this is a minimal suupplement, but we must check it for
        // conjugacy with existing ones.
        new:=true;
        T:=sub<G|S,B>;
        for s in MinSupps do
          if IsConjugate(G,T,sub<G|s`supp,B>) then
            new:=false;
            break;
          end if;
        end for;
      end if;
      if new and (layer gt 1 or sub<G|S,B> ne G) and
           (layer gt 1 or supps eq 2 or (supps eq 1 and #MinSupps eq 0)) then 
        if layer eq 1 then
          Append(~MinSupps, rec<RF|supp:=S>);
        else
          if Dimension(m) eq 0 then
            Se:=S; liftpres:=pres;
          else
            Se, liftpres := LiftedPresentation(S,pres,m,phi);
          end if;
          Append(~MinSupps, rec<RF|supp:=Se, pres:=liftpres>);
        end if;
      end if;
      suppct +:= 1;
    end while;

    Supps:=MinSupps; 
    A:=B;
  end for;

  if not suppsexist then
    return false, [];
  end if;
  /* Change the supplements from lists of generators to genuine subgroups
   * containing N.
   */
  if supps eq 0 then
    Supps := [];
  elif supps eq 1 then
    Supps := [ sub<G|N,Supps[1]`supp> ];
  else
    Supps := [ sub<G|N,s`supp> : s in Supps ];
  end if;
  return true, Supps;

end function;

LiftComplementsSection := function(G,M,N,F,Comps,comps)
  local LiftComps, L, len, index, split, ecomps, MSL, Q, pQ, Supps,
        Suppsubs, newcomp, onesplit, usesylp, p, got, S;

  usesylp:=true;

  L:=refine_section(G,M,N); len:=#L;
  index:=[#L[1] div #N];
  for i in [2..len] do Append(~index,Index(L[i],L[i-1])); end for;
  //print "Indices of ascending subgroup chain: ", Reverse(index);
/* Now comes the lifting phase through the layers. */
  A := M;
  for i in Reverse([1..len]) do
  //print "i = ",i;
    B := (i eq 1) select N else L[i-1];
    ecomps := (i eq 1) select comps else 2;
    /* At the intermediate steps we need to return conjugacy class reps.
     * of complements, in order to see if they extend further.
     * At the final step, we only return them if the caller wants them.
     */
    if IsPrimePower(#A div #B) then
      //elementary abelian section
      split, LiftComps := LiftComplementsElAb(G,A,B,F,Comps,ecomps);
      // mix-up with returned type!
      if ecomps eq 1 and split then LiftComps := [LiftComps]; end if;
    else 
      //nonabelian section
      split := false;
      LiftComps:=[];
  //print "#Comps =",#Comps;
      for comp in Comps do
  //print "Next comp";
        H := sub < G | comp, A >;
        if usesylp and IsPrimePower(#H div #A) then
          p := Factorisation(#H div #A)[1][1];
          Suppsubs := [sub<H | Sylow(H,p), B >];
        else
          if IsSoluble(B) then
  //print "Getting maximals soluble case";
            MSL := MaximalSubgroups(H,B);
            MSL := [sub<H|m`subgroup,B> : m in MSL];
  //print #MSL, "maximals";
          else
  //print "Getting maximals insoluble case";
            if #B eq 1 then
              MSL := MaximalSubgroups(H,sub<H|>);
              MSL := [m`subgroup : m in MSL];
            else
              Q,pQ:=quo<H|B>;
              MSL := MaximalSubgroups(Q,sub<Q|>);
              MSL := [m`subgroup @@ pQ : m in MSL];
            end if;
          end if;
  //print "Got maximals";
          Suppsubs := [m : m in MSL | sub<H|m,A> eq H and not A subset m];
        end if;
        // For each such subgroup we need to find elements mapping
        // onto the same elements of G/A as those in comp.
        // and then find complements of it recursively.
  //print "#Suppsubs=",#Suppsubs;
        for supp in Suppsubs do
  //print "supp of order",#supp;
          newcomp:=[H|];
          for g in comp do
            X:=sub<H|A,g> meet supp;
            T := RightTransversal(X,X meet A);
            for t in T do if t^-1*g in A then
              Append(~newcomp,t);
              break;
            end if; end for;
          end for;
          if supp meet A eq B then
            onesplit:=true;
            Supps:=[newcomp];
          else
            onesplit, Supps :=
               LiftComplementsSection(supp,(supp meet A),B,F,[newcomp],ecomps);
  //print "end of recursive call";
          end if;
          if onesplit then
            split:=true;
  // only add new supplements ifthey are not conjugate to existing ones.
            for supp in Supps do
               S := sub<G|supp,B>;
               got:=false;
               for comp in LiftComps do if IsConjugate(G,S, sub<G|comp,B>) then
                   got:=true;
                   break;
               end if; end for;
               if not got then LiftComps cat:= [supp]; end if;
            end for;      
          end if;
        end for;
      end for;
    end if;

    if not split then
      return false, [ ];
    end if;
    Comps := LiftComps;
    A:=B;
  end for;
 
  return true, Comps;
end function;


//==========================================================================================
refine_section := function(G, M, N)
/* (This is essentially the same as ElAbSeries, but with M as upper limit
 * of series).
 * G should be a finite permutation group, with normal subgroups N and M,
 * where N < M.
 * This function calculates and returns a list L of subgroups of G,
 * all satisfying N < L[i] < M, such that L[1]/N and L[i+1]/L[i] are
 * elementary abelian or direct products of nonabelian simple groups
 * for all i, and L[#L] = M.
 * It does it by looking for normal p-subgroups and refining,
 * and then factoring them out when there are no more to find, and
 * working in the factor group.
 * It also returns true or false, according to whether M/N is soluble or not.
 */
  local L, len, NN, Q, phi, fac, fact, p, P, quoP, projP, primes, syls, CS, i,
        R, pR, sol;

/* First compute all the relevant Sylow-subgroups of G */
  sol := true;
  fac := Factorisation(#M div #N);
  primes := [];
  syls := [];
  for fact in fac do
    p:=fact[1];
    Append(~primes,p);
    Append(~syls,Sylow(G,p));
  end for;

  L:=[]; len:=0; /* len = length of L */
  NN:=N;
  /* NN will be a normal subgroup of G */
  while true do
    fac := Factorisation(#M div #NN);
    for  fact in fac do
      p := fact[1];
      Q := syls[Position(primes,p)]; /* a Sylow p-subgroup of G */
      if #Q eq #G then P := M;
      else
        P := Core(G,sub<G|NN,Q>) meet M;
      end if;
      if #P ne #NN then
        /* Split P/NN up into elementary layers and append to L */
        quoP, projP := quo < P|NN>;
        CS := pCentralSeries(quoP,p);
        for i in Reverse([1..#CS-1]) do
          len +:= 1;
          if len eq 1 then
            L[len] := sub<G | CS[i]@@projP>;
          else
            L[len] := sub<G | L[len-1], CS[i]@@projP>;
          end if;
        end for;
      end if;
    end for;
    if len eq 0 or L[len] eq NN then
      /* L[len]/N = soluble radical of M/N, so M/N is not soluble, and we
       * take the nonabelian soluble residual as next layer
       */
      sol:=false;
      if IsSoluble(N) then
        // NN is the soluble radical of M.
        R, pR := RadicalQuotient(M);
      else
        R, pR := quo<M|NN>;
      end if;
      len +:= 1;
      L[len]:=SolubleResidual(R)@@pR;
    end if;
    NN:=L[len];
    if NN eq M then
      break;
    end if;
  end while;

  return L, sol;
end function;

//==========================================================================================
LiftComplementsElAb := function(G,A,B,F,Comps,ecomps)
/* This function is called by section_complements and section_supplements.
 * A and B are normal subgroups of a subgroup H of the permutation group G with
 * B < A and A/B elementary abelian.
 * Comps is a list of generators of subgroups of H, that form complements
 * of some section M/A in H/A, when taken modulo A.
 * F is a finitely presented group isomorphic to these complements, with
 * corresponding generators to those in the lists.
 * LiftComplementsElAb attempts to lift these complements to complements
 * of M/B in H/B.
 * It returns true or false, according to whether some complement lifts.
 * If ecomps=0 it returns just this.
 * If ecomps=1 it returns one such complement (if there are any).
 * If ecomps=2 it returns a list containing representatives of the
 * conjugacy classes of these lifted complements in H.
 * (The complements are defined as lists of their generators in H.)
 */
 local NG, Z, LiftComps, M, K, dim, phi, ng, nr, rels, FM, comp, FtoG, RV, FRV,
       CCS, w, rel, i, j, split, NewComps, nnc, NCS, newcomp, liftgens, gen, EC,
       vec, SA, normSA, ECR, sns, normgens, ngp, c, d, conjcomp, ngorbs;

 LiftComps := []; /* This will be the lifted complement-list to be returned.*/

 NG := Normaliser(G,A) meet Normaliser(G,B);
                        //usually G, but not always when called from
                        //section_supplements on a proper subgroup.
 Z := Integers();
 M, phi := GModule(NG,A,B);
 dim := Dimension(M);
 K := BaseRing(M);
 Rep := Representation(M);
 ng := Ngens(F);
 rels:=Relations(F); nr:=#rels;

 /* Now we find all liftings to H/B of each complement in the list */
 // print "  +Lifting",#Comps,"complements through next layer, of size",#M;
 for comp in Comps do
  //print "    +Lifting next complement.";
   FtoG := hom < F->NG | comp >;
   /* This is not a genuine homomorphism - the whole point is that we want to
    * work out the images of the relators of F in A/B
    */
   FM := GModule(F,[comp[i]@Rep : i in [1..ng] ]); 
   /* FM is essentially the same module as M=A/B but regarded as an F-module */
   RV:=[];
   for rel in rels do
     w := LHS(rel)*RHS(rel)^-1;
     Append(~RV,w@FtoG@phi);
   end for;
  /*  We need to coerce the values of RV into this FM */
   FRV := [ FM!Eltseq(RV[i]) : i in [1..nr] ];
   /* Now we can do the cohomology calculation! */
   split, NewComps := ComplementVectors(FM,FRV);

   if split and ecomps eq 0 then
    //print "Extension splits.";
     return true,0;
   end if;
   if not split then
  //print "       No lifts for this complement."; 
   else
     nnc := #NewComps;
  //print "      ",nnc,"lifts for this complement."; 
     /* Now, for each complement, we can work out the generators of the
      * corresponding lifted complement.
      */

     EC := [];
     for newcomp in NewComps do
       liftgens := [];
       for i in [1..ng] do
         gen := comp[i];
         vec := newcomp[i];
         for j in [1..dim] do
           gen := gen * (M.j)@@phi^(Z!vec[j]);
         end for;
         Append(~liftgens,gen);
       end for;
   /* A check follows that can be omitted when program is reliable! */
  //print "AAAAA";
       S := sub<G|liftgens>;
       if S meet A ne S meet B then
         error "Subgroup",S,"is not a complement!";
       end if;
  //print "BBBBB";
       if ecomps eq 1 then
         return true, liftgens;
       end if;
       Append(~EC,liftgens);
     end for;

     SA := sub <G|A,comp>;
  //print Index(G,SA);
     normSA := Normaliser(G,SA) meet Normaliser(G,B);
  //print "Got normaliser";
     if nnc gt 1 and normSA ne SA then
     /* We have to work out the action of the normaliser of the complement
      * being lifted on the lifts.
      * We will do this using IsConjugate Subgroup, to avoid the
      * complications of doing it using the cohomology.
      */
  //print "       +Calculating normaliser action on complements.";
       normgens := [];
       sns := SA;
       for gen in Generators(normSA) do
         if not gen in sns then
            Append(~normgens,gen);
            sns := sub<G|sns,gen>;
         end if;
       end for;
  //print "        ",#normgens,"normalising generators for this subgroup.";
       /* Now we are ready to work out the action of normsub on the set
        * of complements. We won't set this up as a formal G-action on the
        * set, but simply build the corresponding permutations ngp[i] of the
        * set {1,2,..,nnc} induced by the generator normgens[i], where
        * the image ngp[i][j] of j under ngp[i] corresponds to conjugation
        * of NewComps[j] by normgens[i].
        * First we must form the subgroups generated by the complements.
        */
       NCS := [ sub<G|B,newcomp> : newcomp in EC ];
       ngp := [];
       for i in [1..#normgens] do
         ngp[i] := [];
         gen := normgens[i];
         for c in [1..nnc] do
           conjcomp:=NCS[c]^gen;
           for d in [1..nnc] do
             if IsConjugate(SA,conjcomp,NCS[d]) then
               ngp[i][c] := d;
               break;
             end if;
           end for;
         end for;
       end for;
       ngorbs := Orbits( sub<Sym(nnc)|ngp> );
       ECR := [ EC[Representative(ngorbs[k])] : k in [1..#ngorbs] ];
       // print "       -",#ECR,"orbits on complements.";
     else
       ECR := EC;
     end if;
     LiftComps := LiftComps cat ECR;
   end if;
 end for;
  //print "  +Total of",#LiftComps,"complements found at next level.";
 if #LiftComps eq 0 then
   return false, 0;
 end if;

 return true, LiftComps;
end function;

LiftedPresentation := function(supp,F,m,phi)
/* supp should be a list of permutations generating a subgroup S of
 * a group H with normal subgroups B<A, such that SB=A.
 * F should be a presentation of S/A with generators corresponding
 * to those of S.
 * m should be the section A/B as an H-module with natural map phi:A->m.
 * An extended list of generators suppe of S is returned  containing
 * a basis of S meet A mod B, together with a presentation of S/B on
 * this generating set.
 */

  local ng, d, suppe, H, FtoH, Rep, Fm, RV, FRV, rels, w;

  ng:= Ngens(F);
  d := Dimension(m);
  suppe :=  supp cat [m.i @@ phi : i in [1..d]]; //extended supp generators

  H := Group(m);
  FtoH := hom< F->H | [supp[i] : i in [1..ng]] >;
  rels := Relations(F);
  Rep := Representation(m);
  Fm := GModule(F,[supp[i]@Rep : i in [1..ng] ]);
  //Fm is essentially the same module as m=A/B but regarded as an F-module

  // calculate values of relations of F in m - we need these for the
  // presentation
  RV:=[];
  for rel in rels do
    w := LHS(rel)*RHS(rel)^-1;
    Append(~RV,w @ FtoH @ phi);
  end for;
  /*  We need to coerce the values of RV into this Fm */
  FRV := [ Fm!Eltseq(r) : r in RV ];

  return suppe, ModuleExtension(Fm,FRV);
end function;
