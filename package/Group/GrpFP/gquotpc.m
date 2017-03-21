freeze;

PowerSeq := function(w)
//express sequence w as v^n with n>0 maximal, return <v,n>.
  local l;
  l := #w;
  for d in Divisors(l) do
    if w eq &cat[ w[1..d] : i in [1..(l div d)] ] then
      return < w[1..d], l div d >;
    end if;
  end for;
end function;
  
IsIdProd := function(G, perms, word, exp)
  return IsIdentity( (&*[perms[i]:i in word])^exp );
end function;

AQCompatible := function(F,G)
  //uses AQInvariants as a quick test for G might be an epimorphic image of F
  fi := Reverse(AQInvariants(F));
  gi := Reverse(AQInvariants(G));
  return #fi ge #gi and forall(s){ s: s in [1..#gi] | fi[s] mod gi[s] eq 0 };
end function;

HomomorphismsPC := function(F,G:A:=G, Surjective:=true,Limit:=0,Print:=0,
                                      ExactOrders:=false)
/* G and A must be finite groups with G <= A.
 * F must be an Fp-group.
 * Find homomorphisms (or epimorphisms if Surjective is true)
 * of F to G up to conjugation in A, and return as a list.
 * If Limit > 0 stop after Limit homomorphisms found.
 */
  local len, rels, powgen, rel, g, cl, exord, FQ, clali,
    genpos, sortrels, relinvolve, min, unplaced, nocc, nos, ct, srels,
   result, classims, ind, perms, bfree, cenis, dcr, dcrinv, dcrpos, cen,
   lev, dcreps, uplevel, imgs, gpi, dcip, dcp, rpos, permword1, ans,
   TestRels, TestRelsFirst, TestRelsLater, TR, foundhom;
  if Category(F) ne GrpFP then
    error "First argument for HomomorphismsH should be an fp-group";
  end if;
  if not IsNormal(A,G) then
    error
 "Second and third arguments G,A for HomomorphismsH must be groups with G<=A";
  end if;
/*
  if Category(G) ne GrpPerm  or Category(A) ne GrpPerm or not G subset A
                                                     or not IsNormal(A,G) then
    error
 "Second and third arguments G,A for HomomorphismsH must be GrpPerm with G<=A";
  end if;
*/
  if Surjective and not AQCompatible(F,G) then
    if Print gt 0 then
      print "G cannot be image of F by AQInvariants test";
    end if;
    return [];
  end if;

  len := Ngens(F);
  //Fquots will be used for FQcompatability tests during backtrack search
  Fquots := [ AddRelation(F, F.1) ];
  for i in [2..len-1] do
    Fquots[i] := AddRelation(Fquots[i-1], F.i);
  end for;
  rels := [ ElementToSequence(LHS(r)*RHS(r)^-1) : r in Relations(F) ];
  powgen := [ 0 : i in [1..len] ];
  //locate relations which are powers of generators
  for rel in rels do
    if rel eq [ rel[1] : i in [1..#rel] ] then
      g := Abs(rel[1]);
      powgen[g] := Gcd(powgen[g],#rel);
    // We don't need this relation, because we will only look at images
    // for g in the appropriate conjugacy classes.
      Exclude(~rels,rel);
    end if;
  end for;

  if Print gt 0 then
    print "Orders of generators of F from presentation:",powgen;
  end if;

  rels := [ PowerSeq(r) : r in rels ];

  cl := Classes(A);
  cl := [ c : c in cl | c[3] in G ];
                              //Conjugacy classes of A that lie in G

  //Let's deal with the case when Ngens(F) = 1
  if len eq 1 then
    if Surjective then
      if ExactOrders then
        return [ hom< F->G | c[3] > : c in cl |
                         powgen[1] eq c[1] and c[1] eq #G ];
      end if;
      return [ hom< F->G | c[3] > : c in cl |
                         powgen[1] mod c[1] eq 0 and c[1] eq #G ];
    end if;
    if ExactOrders then
      return [ hom< F->G | c[3] > : c in cl | powgen[1] eq c[1] ];
    end if;
    return [ hom< F->G | c[3] > : c in cl | powgen[1] mod c[1] eq 0 ];
  end if;

  ords := Reverse(Sort(SetToSequence({ c[1] : c in cl })));

  /* We now do AQInvariants tests to see if some orders can be
   * eliminated as possible targets of generators of F
   * We also construct clali - clali[i] is the list of possible class
   * representatives of images of F.i.
   */
  clali := [];
  for i in [1..len] do
    exords := {};
    for o in ords do
     if not o in exords and powgen[i] mod o eq 0 and powgen[i] ne o then
        //Add relator F.i^o to F and find order
        FQ := AddRelation(F,F.i^o);
        if Surjective and not AQCompatible(FQ,G) then
          exords := exords join { x : x in ords | o mod x eq 0 };
        end if;
      end if;
    end for;
    if Print gt 0 then
      print "Excluded orders for images of generator",i,":",exords;
    end if;
    clali[i] := ExactOrders select
   [ c[3] : c in cl | powgen[i] eq c[1] and not c[1] in exords ]
     else
   [ c[3] : c in cl | powgen[i] mod c[1] eq 0 and not c[1] in exords ];
    if clali[i] eq [] then
      if Print gt 0 then
        print "No possible images for generator",i;
      end if;
      return [];
    end if;
  end for;
  if Print gt 0 then
        print "Numbers of possible class images:",[#x: x in clali];
  end if;

  /* If there are more than two generators, then we try to order them such that
   * relators involving not all of the generators can be applied high up
   * the search tree.
   * genpos[i] will mark the height of generator i in the search tree
   * and for pos<len sortrels[pos] will contain those relators which involve
   * the generator at height pos but no lower generators. 
   * Relators are sorted by length to improve efficiency of search.
   */
  if len eq 2 then
    genpos:=[1..len]; sortrels:=[Sort(rels,func<x,y|#x[1] - #y[1]>)];
  else
    relinvolve := [ { Abs(i) : i in r[1] } : r in rels ];
    //Are there any not involving all generators?
    genpos:=[]; sortrels:=[];
    unplaced := len;
    while unplaced gt 0 do
      min := Min( {#ri : ri in relinvolve | ri ne {} } );
      if min eq unplaced then
        ct := 0;
        for i in [1..len] do
          if not IsDefined(genpos,i) then
            ct+:=1; genpos[i] := ct;
          end if;
        end for;
        srels := [ rels[i] : i in [1..#rels] | relinvolve[i] ne {} ];
        sortrels[1]:=Sort(srels,func<x,y|#x[1] - #y[1]>);
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
        sortrels[unplaced-min+1]:=Sort(srels,func<x,y|#x[1] - #y[1]>);
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

  if Print gt 0 then
    print "generator positions:",genpos;
    print "sorted relations:",sortrels;
  end if;

  /* In this version, we make a note of those positions in permword,
   * for i in [1..#sortrels[1]] that will change at the bottom level (lev=1)
   * of the search - these are positions where double coset reps and their
   * inverses are inserted.
   */
  ct := 0;
  dcip:=[]; dcp:=[];
  for rel in sortrels[1] do
    ct +:= 1;
    dcip[ct]:=[]; dcp[ct]:=[];
    rpos := 0;
    for g in rel[1] do
      if genpos[Abs(g)] eq 1 then
        Append(~dcip[ct],rpos+1); Append(~dcp[ct],rpos+3);
        rpos +:= 3;
      else rpos +:= 1;
      end if;
    end for;
  end for;
  permword1 := [];

  TestRels := procedure(lev,perms,dcr,dcrinv,dcrpos,~ans)
  /* see if the current images satisfy the relations at level lev */
     local permword, ag, ipt;
     for rel in sortrels[lev] do
       // First build the list of permutation numbers that defines the
       // word which is the image of rel in G
       permword := [];
       for g in rel[1] do
         ag := genpos[Abs(g)];
         if ag eq len then
           if g gt 0 then Append(~permword,ag);
           else Append(~permword,len+ag);
           end if;
         elif ag eq 1 then
           Append(~permword,dcrinv[ag][dcrpos[ag]]);
           if g gt 0 then Append(~permword,ag);
           else Append(~permword,len+ag);
           end if;
           Append(~permword,dcr[ag][dcrpos[ag]]);
         else
           if g gt 0 then Append(~permword,2*len+ag);
           else Append(~permword,3*len+ag);
           end if;
         end if;
       end for;
       // Now see if the permutation defined by the word is the identity.
       if not IsIdProd(G, perms, permword, rel[2]) then
         ans := false; return;
       end if;
     end for;
     ans := true; return;
  end procedure;

  TestRelsFirst := procedure(perms,dcr,dcrinv,dcrpos,~permword1,~ans)
  // Version to be applied on first call of a run through lowest level 1.
     local  ag, ipt, ct;
     ct := 0;
     for rel in sortrels[1] do
       // First build the list of permutation numbers that defines the
       // word which is the image of rel in G
       ct +:= 1;
       permword1[ct] := [];
       for g in rel[1] do
         ag := genpos[Abs(g)];
         if ag eq len then
           if g gt 0 then Append(~permword1[ct],ag);
           else Append(~permword1[ct],len+ag);
           end if;
         elif ag eq 1 then
           Append(~permword1[ct],dcrinv[ag][dcrpos[ag]]);
           if g gt 0 then Append(~permword1[ct],ag);
           else Append(~permword1[ct],len+ag);
           end if;
           Append(~permword1[ct],dcr[ag][dcrpos[ag]]);
         else
           if g gt 0 then Append(~permword1[ct],2*len+ag);
           else Append(~permword1[ct],3*len+ag);
           end if;
         end if;
       end for;
     end for; //we have done this for all relations on the first run through

     ct := 0;
     for rel in sortrels[1] do
       // Now see if the permutation defined by the word is the identity.
       ct +:= 1;
       if not IsIdProd(G, perms, permword1[ct], rel[2]) then
         ans := false; return;
       end if;
     end for;
     ans := true; return;
  end procedure;

  TestRelsLater := procedure(perms,dcr,dcrinv,dcrpos,~permword1,~ans)
  // Version to be applied on  calls of a run through lowest level 1
  // other than the first. Fewer entries in permword1 need changing.
     local  ag, ipt, ct, dcig, dcg;
     ct := 0;
     dcg := dcr[1][dcrpos[1]]; dcig := dcrinv[1][dcrpos[1]];
     for rel in sortrels[1] do
       // First build the list of permutation numbers that defines the
       // word which is the image of rel in G
       ct +:= 1;
       for i in dcip[ct] do permword1[ct][i] := dcig; end for;
       for i in  dcp[ct] do permword1[ct][i] :=  dcg; end for;
       // Now see if the permutation defined by the word is the identity.
       if not IsIdProd(G, perms, permword1[ct], rel[2]) then
         ans := false; return;
       end if;
     end for;
     ans := true; return;
  end procedure;
   
  /* Now we are ready to start the search.
   * The outer backtrack is over the possible classes that can occur
   * as images of the generators of F
   */
  D := DerivedGroup(G);
  classims := [1 : i in [1..len]];
  result := [];
  ind:=len;
  while ind gt 0 do
    if Print gt 1 then
      print "Outer backtrack increment - index =",ind, classims;
    end if;
    ind:=len;
    //first check image in abelian quotient for being epimorphism
    possepi:=true;
    if Surjective then
      possepi := sub< G | D, [clali[i][classims[i]] : i in [1..len]] > eq G;
    end if;
    if Print gt 1 and not possepi then
      print "These class images cannot be epimorphic";
    elif  Print gt 1  then
      print "These are feasible class images";
    end if;
    if possepi then
      /* test class combination indicated by classims.
       * perms will be a long list of various permutations needed in the
       * calculation of images.
       * perms[1..len] will be the representatives of the class
       * combination indicated by classims, but with perms[h] the one
       * corresponding to the generator at height h.
       * perms[len+1..2*len] will be their inverses.
       * nfree is the smallest unused index in perms.
       */
      perms := [];
      for i in [1..len] do
        perms[genpos[i]] := clali[i][classims[i]];
        perms[genpos[i]+len] := clali[i][classims[i]]^-1;
      end for;
      // perms[2*len+1..3*len] and [3*len+1..4*len] will be used for current
      // conjugates of the above class images, and their inverses
      for i in [2*len+1..4*len] do perms[i] := Id(G); end for;
      nfree := 4*len+1;
  
      cenis :=  [ Centraliser(A,perms[i]) : i in [1..len] ];
  
      /* The inner backtrack runs through representatives of the classes
       * dcr[i] is a list of indices of permutations in the list perms that
       * we need to conjugate the class representative perms[i] by in the search.
       * dcrinv[i][j] is the index in perms of the inverse of dcr[i][j].
       * dcrpos[i] is the current position in dcr[i].
       * cen[i] is the intersection of the centralisers in A of the current
       * images of the generators of height >= i.
       */
  
      dcr:=[]; dcrinv:=[]; dcrpos:=[];
      cen:=[];
      cen[len]:=cenis[len];
  
      lev:=len-1;
  
      /* The next loop locates the first valid position for a homomorphism
       * F->G in the backtrack
       */
      foundhom := false;
      while lev gt 0 do
        if not foundhom then
          dcreps := IndexedSetToSequence(Transversal(A,cenis[lev],cen[lev+1]));
          if Print gt 2 then print #dcreps,"double coset reps, level",lev; end if;
          dcr[lev] := [nfree..nfree+#dcreps-1];
          dcrinv[lev] := [nfree+#dcreps..nfree+2* #dcreps-1];
          perms := [perms[i]:i in [1..nfree-1]]
                                        cat dcreps cat [ g^-1 : g in dcreps];
          nfree +:= 2* #dcreps;
          dcrpos[lev] := 1;
          if lev gt 1 then //calculate relevant conjugate and inverse explicitly
            perms[2*len+lev] := perms[dcrinv[lev][dcrpos[lev]]] * perms[lev] *
                                perms[dcr[lev][dcrpos[lev]]];
            perms[3*len+lev] := perms[dcrinv[lev][dcrpos[lev]]] * perms[len+lev] *
                                perms[dcr[lev][dcrpos[lev]]];
          end if;
        end if;
  
        foundhom:=false;
        uplevel:=true;
        while uplevel and lev lt len do
  	uplevel:=false;
          TR := TestRelsFirst;
  	while dcrpos[lev] le #dcr[lev] and sortrels[lev] ne [] do
            if lev eq 1 then TR(perms,dcr,dcrinv,dcrpos,~permword1,~ans);
            else TestRels(lev,perms,dcr,dcrinv,dcrpos,~ans);
            end if;
            if ans then break; end if;
            if lev eq 1 then TR := TestRelsLater; end if;
  	  dcrpos[lev] +:= 1; //increment because of relations
            if lev gt 1 and dcrpos[lev] le #dcr[lev] then
               perms[2*len+lev] := perms[dcrinv[lev][dcrpos[lev]]] *
                                    perms[lev] * perms[dcr[lev][dcrpos[lev]]];
               perms[3*len+lev] := perms[dcrinv[lev][dcrpos[lev]]] *
                                   perms[len+lev] * perms[dcr[lev][dcrpos[lev]]];
            end if;
            if Print gt 2 then print "Early increment at level",lev; end if;
  	end while;
  	if dcrpos[lev] gt #dcr[lev] then
            if Print gt 2 then print "Early break at level",lev; end if;
  	  uplevel := true;
            nfree := dcr[lev][1];
  	  lev +:= 1;
  	  if lev lt len then
  	    dcrpos[lev] +:= 1;
              if lev gt 1  and dcrpos[lev] le #dcr[lev] then
                 perms[2*len+lev] := perms[dcrinv[lev][dcrpos[lev]]] *
                                    perms[lev] * perms[dcr[lev][dcrpos[lev]]];
                 perms[3*len+lev] := perms[dcrinv[lev][dcrpos[lev]]] *
                                   perms[len+lev] * perms[dcr[lev][dcrpos[lev]]];
              end if;
  	  end if;
  	end if;
        end while;
  
        if lev ge len then // we have come to the end of the search
          lev := 0; //to drop out of while loop
        elif lev gt 1 then
  	cen[lev] := #cen[lev+1] eq 1 select cen[lev+1] else
             Centralizer(cen[lev+1],perms[lev]^perms[dcr[lev][dcrpos[lev]]]);
          lev -:= 1;
        else //found a homomorphism!
          imgs := [];
          for i in [1..len] do
            gpi := genpos[i];
            imgs[i] := gpi eq len select perms[gpi] else
                                         perms[gpi]^perms[dcr[gpi][dcrpos[gpi]]];
          end for;
          if not Surjective or sub<G|imgs> eq G then
            Append(~result,hom<F->G|imgs>);
            if Print gt 1 then
              print "Found a homomorphism";
            end if;
            if Limit ne 0 and #result eq Limit then
              return result;
            end if;
          end if;
          foundhom := true;
    
          //Carry on with the backtrack search
          dcrpos[lev] +:= 1;
        end if;
      end while;
    end if; //if possepi

    //increment classims in outer backtrack
    classims[ind]:=classims[ind]+1;
    while ind gt 0 and classims[ind] gt #clali[ind] do
      classims[ind] := 1;
      ind:=ind-1;
      advance := true;
      if ind gt 0 then
        while advance do
          advance := false;
	  classims[ind] := classims[ind]+1;
          if Surjective and ind lt len and classims[ind] le #clali[ind] then
            //incremental abelian compatability test
            Q := sub< G | D, [clali[i][classims[i]] : i in [1..ind]] >;
            if not AQCompatible(Fquots[ind],G/Q) then
              advance := true;
              if Print gt 1 then
                print "Incremental AQInvariants test fails for these images",
                       ind, classims;
              end if;
            end if;
          end if;
        end while;
      end if;
    end while;

  end while; //while ind ge 0

  return result;
end function;


intrinsic Homomorphisms(F::GrpFP, G::GrpPC:Surjective:=true,Limit:=0,Print:=0, ExactOrders:=false) -> SeqEnum
 {Find homomorphisms (or epimorphisms if Surjective is true)
  of F to G up to conjugation in G, and return as a list.}
  return HomomorphismsPC(F,G:Surjective:=Surjective, Limit:=Limit, Print := Print, ExactOrders:=ExactOrders);
end intrinsic;

intrinsic Homomorphisms(F::GrpFP, G::GrpPC, A::GrpPC:Surjective:=true,Limit:=0,Print:=0, ExactOrders:=false) -> SeqEnum
 {Find homomorphisms (or epimorphisms if Surjective is true)
  of F to G up to conjugation in A, and return as a list.}
  return HomomorphismsPC(F,G:A:=A,Surjective:=Surjective, Limit:=Limit, Print := Print, ExactOrders:=ExactOrders);
end intrinsic;
