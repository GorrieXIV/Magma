freeze;

/* try storing images as integer sequences - works faster */
declare verbose IsoSearch, 2;

intrinsic SearchForIsomorphism (G:: GrpFP, H:: GrpFP, m:: RngIntElt:
     All := false, IsomsOnly := true, MaxRels := 0, CycConjTest := true) ->
       BoolElt, HomGrp, HomGrp
{Search for an isomorphism from G to H, in which the sum of the lengths
  of the images of the generators of G is at most m}
/*
 * G, H should be FP-groups.
 * Search for an isomorphism from G to H, in which the sum of the lengths
 * of the images of the generators of G is at most m
 * If All is true, then all such isomorphisms are returned, otherwise
 * only the first one found
 * If IsomsOnly is false, then all homomorhisms are returned.
 * MaxRels is value of the MaxRelations parameter used in calls of RWSGroup.
 * Default is 250*m, but sometimes a higher value may be needed, or
 * a lower value results in a much faster run.
 * CycConjTest (true by default) means that images of the first generator
 * which have a cyclic conjugate that comes earlier in the lexicographical
 * order are rejected, because there would be a conjugate isomorphism in which
 * the image was the cyclic conjugate. This nearly always results in faster
 * run-times, but occasionally it can happen that the conjugate isomorphism
 * has a larger sum of lengths of generator images, which is clearly bad.
 * So the user has the option of not rejecting such images.
 */
  if IsomsOnly then
    Gab, GtoGab := AbelianQuotient(G);
    Hab, HtoHab := AbelianQuotient(H);
    if Invariants(Gab) ne Invariants(Hab) then
      print "Groups have different abelianizations";
      return false, _, _;
    end if;
    DoAQTest := Invariants(Gab) ne [] and assigned GtoGab and assigned HtoHab;
    //DoAQTest means check during the search that abelian invariants
    //of subgroups of G and their current images in H are equal.
  else DoAQTest := false;
  end if;

  if not IsomsOnly then
    tHtoG := hom< H-> G | [Id(G): i in [1..Ngens(H)]] >;
    // just a place filler for non-existent inverse map.
  end if;

  if All then CycConjTest:=false; end if;

  mil := m;
  ng:=Ngens(G); nh:=Ngens(H);
  if All then isoms := []; end if;

  vprint IsoSearch: "Running Knuth-Bendix on first group";
  //Difficult to get RWSGroup parameters good for all examples
  
  if MaxRels eq 0 then MaxRels := 250*mil; end if;
  msl := #Relations(G) eq 0 select 0
   else Max({#LHS(r):r in Relations(G)} join {#RHS(r):r in Relations(G)})+1;
  if msl lt 2*mil then msl := 2*mil; end if;
  RG:=RWSGroup(G :
         MaxRelations:=MaxRels,MaxStoredLen:=<msl,msl>,MaxOpLen:=mil,
	 Warning := false);
  Grels := Relations(RG);
  vprint IsoSearch: #Grels, "relations";
  //check if any generators are trivial. If so, exit with error.
  for i in [1..ng] do if RG.i eq Id(RG) then
    print "Generator number",i,"in the first group is trivial.";
    error "Try simplifying the presentation and re-running.";
  end if; end for;

  vprint IsoSearch: "Running Knuth-Bendix on second group";
  msl := #Relations(H) eq 0 select 0
   else Max({#LHS(r):r in Relations(H)} join {#RHS(r):r in Relations(H)})+1;
  if msl lt 2*mil then msl := 2*mil; end if;
  RH:=RWSGroup(H : 
         MaxRelations:=MaxRels,MaxStoredLen:=<msl,msl>,MaxOpLen:=mil,
	 Warning := false);
  Hrels := Relations(RH);
  vprint IsoSearch: #Hrels, "relations";

  if IsomsOnly then WH := Seq(RH,1,mil-ng+1 : Search:="BFS");
  else WH := Seq(RH,0,mil : Search:="BFS");
  end if;
  WH := {@ x: x in WH @}; //for locating positions of inverses
  if IsomsOnly then
    vprint IsoSearch: #WH,"words of length at most",mil-ng+1;
  else
    vprint IsoSearch: #WH,"words of length at most",mil;
  end if;

  //Mark indices in WH for lengths of words
  lenstart := [];
  len := 1;
  for i in [1..#WH] do if #WH[i] eq len then
    lenstart[len] := i;
    len +:= 1;
  end if; end for;
  for i in [len..mil+1] do lenstart[i] := #WH+1; end for;
  vprint IsoSearch:
      "Starting positions of words of lengths 1,2,3,... in second group:";
  vprint IsoSearch: lenstart;

  WHlen := [ #w : w in WH ];
  WHlen[#WHlen+1] := mil+1; //so that we know we are past the end of the list.

  if CycConjTest then
    WHmincyc := [ ];
    /* if the first generator in a word in WH is not the minimal generator
     * in that word, then some cyclic conjugate of that word precedes it
     * in the lexicographical ordering. So we do not need to consider it
     * as an image of the highest numbered generator.
     */
    gno := func< x | x gt 0 select 2*x-1 else -2*x >;
    for w in WH do
      esw:=[gno(x): x in Eltseq(w)];
      Append(~WHmincyc,(w eq RH!1) or (esw[1] eq Min(esw)));
    end for;
    vprint IsoSearch: #[x: x in WHmincyc | x ],
        "words in second group are minimal cyclic conjugates";
  end if;

  //calculate indices of inverses of elements of WH
  WHinv := [];
  for i in [1..#WH] do WHinv[i] := Position(WH,WH[i]^-1); end for;
  WHS := [Eltseq(w) : w in WH];
  delete WH;
  WHSH := [H!w : w in WHS];

  rels := [ ElementToSequence(LHS(r)*RHS(r)^-1) : r in Relations(G) ];

  /* If there is more than one generators, then we try to order them such that
   * relators involving not all of the generators can be applied high up
   * the search tree.
   * (The generator with largest value of genpos is at the top
   * of the search tree.)
   * genpos[i] will mark the height of generator i in the search tree
   * and  sortrels[pos] will contain those relators which involve
   * the generator at height pos but no lower generators.
   * Relators are sorted by length to improve efficiency of search.
   */
  if ng eq 1 then
    genpos:=[1..ng]; sortrels:=[Sort(rels,func<x,y|#x - #y>)];
  else
    relinvolve := [ { Abs(i) : i in r } : r in rels ];
    //Are there any not involving all generators?
    genpos:=[]; sortrels:=[];
    unplaced := ng;
    while unplaced gt 0 do
      if {#ri : ri in relinvolve | ri ne {} } eq {} then
        min := unplaced;
      else min := Min( {#ri : ri in relinvolve | ri ne {} } );
      end if;
      if min eq unplaced then
        ct := 0;
        for i in [1..ng] do
          if not IsDefined(genpos,i) then
            ct+:=1; genpos[i] := ct;
          end if;
        end for;
        srels := [ rels[i] : i in [1..#rels] | relinvolve[i] ne {} ];
        sortrels[1]:=Sort(srels,func<x,y|#x - #y>);
        for i in [2..unplaced] do sortrels[i] := []; end for;
      else
      //Find set of size min occurring most often
        nocc:=0;
        for ri in relinvolve do if #ri eq min then
          if #[ rj : rj in relinvolve | rj eq ri ] gt nocc then
            nocc := #[ rj : rj in relinvolve | rj eq ri ];
            nos := ri;
          end if;
        end if; end for;
        srels := [ rels[i] : i in [1..#rels] | relinvolve[i] eq nos ];
        sortrels[unplaced-min+1]:=Sort(srels,func<x,y|#x - #y>);
        for i in [unplaced-min+2..unplaced] do sortrels[i] := []; end for;
        ct := unplaced-min;
        for no in nos do
          ct +:= 1;
          genpos[no] := ct;
        end for;
        // Remove nos from relinvolve
        relinvolve := [ ri diff nos : ri in relinvolve ];
      end if;
      unplaced := unplaced-min;
    end while;
  end if;

  // Now we renumber the relations according to their new positions
  for i in [1..#sortrels] do for j in [1..#sortrels[i]] do
                                            for k in [1..#sortrels[i][j]] do
    x := sortrels[i][j][k];
    sortrels[i][j][k] := x gt 0 select genpos[x] else -genpos[-x];
  end for; end for; end for;

  vprint IsoSearch: "generator positions:",genpos;
  vprint IsoSearch:  "sorted relations:",sortrels;

  if DoAQTest then
    /* we will record some information about the images of the subgroups of
     * G in Gab. We can check that this agrees with the corresponding subgroups
     * of H in Hab during the search
     */
    invgenpos := [];
    for i in [1..ng] do invgenpos[genpos[i]] := i; end for;
    CumGeninvars := [
            Invariants(GtoGab(sub<G|[G.(invgenpos[j]) : j in [i..ng]]>)) :
                                                                i in [1..ng] ];
  end if;

  TestRels := function(sortrels,lev,WHS,WHinv,genpos,impos)
    //checks that relations are satisfied at this level
    id := RH!1;
    for w in sortrels[lev] do
      im := [];
      for g in w do
        if g gt 0 then im cat:= WHS[impos[g]];
        else im cat:= WHS[WHinv[impos[-g]]];
        end if;
      end for;
      if RH!im ne id then
        return false;
      end if;
    end for;
    return true;
  end function;

  AQTest := function(lev,ng,WHSH,impos,HtoHab,CumGeninvars)
    //checks that abelian invariants correspond
    return
      CumGeninvars[lev] eq
        Invariants(HtoHab(sub<H|[WHSH[impos[j]] : j in [lev..ng]]>));
  end function;

  //Now we are ready to start the search
  for imlensum in [0..mil] do
    vprint IsoSearch:
      "Searching for maps with sum of lengths of generator images =",imlensum;
    impos := [ 0 : i in [1..ng] ]; //position of image of G.i in the list WHS
    impos[ng] := ng eq 1 and imlensum gt 0 select lenstart[imlensum] else 1;
    lev := ng;
    //locate the first valid position for a homomorphism G->H in the backtrack
    while lev gt 0 do
      uplevel:=true;
      while uplevel and lev le ng do
        uplevel := false;
        while &+[WHlen[impos[i]] : i in [lev..ng]] le imlensum do
          if lev ne ng or not CycConjTest or WHmincyc[impos[lev]] then
            //It seems to waste time to do AQTest at level 1.
            if (not DoAQTest or lev eq 1 or
                 AQTest(lev,ng,WHSH,impos,HtoHab,CumGeninvars)) and
              (sortrels[lev] eq [] or
                     TestRels(sortrels,lev,WHS,WHinv,genpos,impos)) then
              break;
            end if;
          end if;
          impos[lev] +:= 1;
        end while;
        if &+[WHlen[impos[i]] : i in [lev..ng]] gt imlensum then
  vprint IsoSearch, 2:  "backtracking at level",lev;
           uplevel := true;
           lev +:=1;
           if lev le ng then impos[lev] +:= 1; end if;
        end if;
      end while;

      if lev gt ng then // we have come to the end of the search
        lev := 0; //to drop out of while loop
      elif lev gt 1 then
        lev -:= 1;
        if lev eq 1 then
          restsum := &+[WHlen[impos[i]] : i in [2..ng]];
          impos[lev] := imlensum-restsum eq 0 select 1
                                              else lenstart[imlensum-restsum];
        else impos[lev] := 1;
        end if;
      else //found a homomorphism!
        vprint IsoSearch: "Found a homomorphism";
        imGgens := [WHSH[impos[genpos[i]]]  : i in [1..ng]];
        Gimage := sub< H | imGgens >;
        GtoH := hom< G->H | imGgens >;
        vprint IsoSearch: imGgens;
        //check if epimorphism using coset enumeration
        ind := Index(H,Gimage:CosetLimit:=1000);
        if ind eq 1 then //epimorphism
          vprint IsoSearch: "It's an epimorphism";
          //find inverse images
          Rewrite(H,~Gimage:Strategy:="Felsch");
          imHgens := [G!Eltseq(Gimage!(H.i)) : i in [1..nh]];
          RGimHgens := [RG!Eltseq(imHgens[i]) : i in [1..nh]];
          //shorten words in imHgens.
          imHgens := [G!Eltseq(w) : w in RGimHgens];
          //Check if inverse map is an isomorphism
          phi := hom< H->RG | RGimHgens >;
          isisom := true;
          for w in Relations(H) do
            if phi(LHS(w)) ne phi(RHS(w)) then
              isisom:=false; break;
            end if;
          end for;
          if isisom then
            vprint IsoSearch: "Reverse map is a homomorphism";
            vprint IsoSearch: imHgens;
            //construct corresponding isomorphisms G->H, H->G
            HtoG := hom< H->G | imHgens >;
            if forall(g){g : g in Generators(G) |
                RG!Eltseq(g@GtoH@HtoG) eq RG!Eltseq(g)} then
              vprint IsoSearch: "It's an isomorphism!";
              if not All then
                 return true, GtoH, HtoG;
              end if;
              Append(~isoms, <GtoH, HtoG> );
            else
              vprint IsoSearch: "Reverse map does not appear to be inverse";
              if not IsomsOnly then
                 if All then Append(~isoms,<GtoH,tHtoG>);
                 //don't want to return the identity map
                 elif imGgens ne [Id(H):i in [1..ng]] then return true, GtoH, _;
                 end if;
              end if;
            end if;
          else
         vprint IsoSearch: "Reverse map does not appear to be a homomorphism";
            if not IsomsOnly then
               if All then Append(~isoms,<GtoH,tHtoG>);
               //don't want to return the identity map
               elif imGgens ne [Id(H):i in [1..ng]] then return true, GtoH, _;
               end if;
            end if;
          end if;
        else vprint IsoSearch: "Might not be an epimorphism!";
          if not IsomsOnly then
             if All then Append(~isoms,<GtoH,tHtoG>);
             //don't want to return the identity map
             elif imGgens ne [Id(H):i in [1..ng]] then return true, GtoH, _;
             end if;
          end if;
        end if;

        //carry on with search
        impos[lev]+:=1;
      end if;
    end while;
  end for;

  if All and #isoms ne 0 then
    return true, isoms, _;
  end if;

  return false,_,_;

end intrinsic;
