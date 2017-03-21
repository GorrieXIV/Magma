freeze;

/*
This is a version of Homomorphisms that is slower than Homomorphisms
itself, and may return the same map multiple times, but it uses very
little memory.
*/


/* Here we do not worry about repetitions in the list of maps found, and just
 * avoid using excessive memory.
*/

intrinsic HomomorphismsLM(
    F::GrpFP,G::GrpPerm: A:=G,  Surjective:=true,One:=false,Print:=0
) -> SeqEnum
{A sequence containing homomorphisms from the fp-group F to the permutation
group G up to automorphisms induced by A where G is a subgroup of A.  If
Surjective is true the maps will be epimorphisms.  This is an alternative
to the intrinsic Homomorphisms which uses much less memory at the cost of
being much slower. Unlike Homomorphisms it does not remove duplicate
homomorphisms.}

/* G and A must be permutation groups with G <= A.
 * F must be an Fp-group.
 * Find homomorphisms (or epimorphisms if Surjective is true)
 * If One is true stop after the first homomorphism.
 */
  local base, len, rels, powgen, rel, g, cl, exord, FQ, clali,
    genpos, sortrels, relinvolve, min, unplaced, nocc, nos, ct, srels,
   result, classims, ind, perms, bfree, cenis, crep, crepinv, transproc, tpdone,
   lev, uplevel, imgs, gpi, rpos, permword1, ans,
   TestRelsFirst, TestRels, TR, foundhom;

/*
  if Category(F) ne GrpFP then
    error "First argument for HomomorphismsH should be an fp-group";
  end if;
  if Category(G) ne GrpPerm  or Category(A) ne GrpPerm or not G subset A
                                                     or not IsNormal(A,G) then
    error
 "Second and third arguments G,A for HomomorphismsH must be GrpPerm with G<=A";
  end if;
*/

  require G subset A and IsNormal(A, G):
      "Second and third arguments G, A must be GrpPerm with G normal in A";

  base := Base(G);
  len := Ngens(F);
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

  cl := Classes(A);
  cl := [ c : c in cl | c[3] in G ];
                              //Conjugacy classes of A that lie in G

  //Let's deal with the case when Ngens(F) = 1
  if len eq 1 then
    if Surjective then
      return [ hom< F->G | c[3] > : c in cl |
                         powgen[1] mod c[1] eq 0 and c[1] eq #G ];
    end if;
    return [ hom< F->G | c[3] > : c in cl | powgen[1] mod c[1] eq 0 ];
  end if;

  ords := Reverse(Sort(SetToSequence({ c[1] : c in cl })));

  /* We now do short coset enumerations to see if some orders can be
   * eliminated as possible targets of generators of F
   * (Idea filched from GAP code.)
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
        FQo := Index(FQ,sub<FQ|> : CosetLimit:= Min(#G*25*len,50000*len) );
        if Surjective then
          if FQo ne 0 and FQo lt #G then
            exords := exords join { x : x in ords | o mod x eq 0 };
          end if;
        elif FQo lt o then
          xords := exords join {o};
        end if;
      end if;
    end for;
    if Print gt 0 then
      print "Excluded orders for images of generator",i,":",exords;
    end if;
    clali[i] :=
   [ c[3] : c in cl | powgen[i] mod c[1] eq 0 and not c[1] in exords ];
    if clali[i] eq [] then
      if Print gt 0 then
        print "No possible images for generator",i;
      end if;
      return [];
    end if;
  end for;

  /* If there are more than two generators, then we try to order them such that
   * relators involving not all of the generators can be applied high up
   * the search tree.
   * genpos[i] will mark the height of generator i in the search tree
   * and for pos<len sortrels[pos] will contain those relators which involve
   * the generator at height pos but no lower generators. 
   * Relators are sorted by length to improve efficiency of search.
   */
  if len eq 2 then
    genpos:=[1..len]; sortrels:=[Sort(rels,func<x,y|#x - #y>)];
  else
    relinvolve := [ { Abs(i) : i in r } : r in rels ];
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

  if Print gt 0 then
    print "generator positions:",genpos;
    print "sorted relations:",sortrels;
  end if;

  permword1 := [];

  TestRels := procedure(lev,perms,crep,crepinv,~ans)
  /* see if the current images satisfy the relations at level lev */
     local permword, ag, ipt;
     for rel in sortrels[lev] do
       // First build the list of permutation numbers that defines the
       // word which is the image of rel in G
       permword := [];
       for g in rel do
         ag := genpos[Abs(g)];
         if ag eq len then
           if g gt 0 then Append(~permword,ag);
           else Append(~permword,len+ag);
           end if;
         elif ag eq 1 then
           Append(~permword,crepinv[ag]);
           if g gt 0 then Append(~permword,ag);
           else Append(~permword,len+ag);
           end if;
           Append(~permword,crep[ag]);
         else
           if g gt 0 then Append(~permword,2*len+ag);
           else Append(~permword,3*len+ag);
           end if;
         end if;
       end for;
       // Now see if the permutation defined by the word is the identity.
       if not IsIdentityProduct(G, perms, permword) then
         ans := false; return;
       end if;
     end for;
     ans := true; return;
  end procedure;

  TestRelsFirst := procedure(perms,crep,crepinv,~permword1,~ans)
  // Version to be applied on first call of a run through lowest level 1.
     local  ag, ipt, ct;
     ct := 0;
     for rel in sortrels[1] do
       // First build the list of permutation numbers that defines the
       // word which is the image of rel in G
       ct +:= 1;
       permword1[ct] := [];
       for g in rel do
         ag := genpos[Abs(g)];
         if ag eq len then
           if g gt 0 then Append(~permword1[ct],ag);
           else Append(~permword1[ct],len+ag);
           end if;
         elif ag eq 1 then
           Append(~permword1[ct],crepinv[ag]);
           if g gt 0 then Append(~permword1[ct],ag);
           else Append(~permword1[ct],len+ag);
           end if;
           Append(~permword1[ct],crep[ag]);
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
       if not IsIdentityProduct(G, perms, permword1[ct]) then
         ans := false; return;
       end if;
     end for;
     ans := true; return;
  end procedure;

  /* Now we are ready to start the search.
   * The outer backtrack is over the possible classes that can occur
   * as images of the generators of F
   */
  transproc := [* 0 : i in [1..len] *]; //for coset reps of centralizers
  tpdone := [false : i in [1..len]]; //means we have done all coset reps
  crep := [ 4*len+1 .. 5*len ]; //position in perms of coset reps
  crepinv := [ 5*len+1 .. 6*len ]; //position in perms of coset rep invs
  classims := [1 : i in [1..len]];
  result := [];
  ind:=len;
  while ind gt 0 do
    if Print gt 0 then
      print "Outer backtrack increment - index =",ind, classims;
    end if;
    ind:=len;
    /* test class combination indicated by classims.
     * perms will be a long list of various permutations needed in the
     * calculation of images.
     * perms[1..len] will be the representatives of the class
     * combination indicated by classims, but with perms[h] the one
     * corresponding to the generator at height h.
     * perms[len+1..2*len] will be their inverses.
     */
    perms := [];
    for i in [1..len] do
      perms[genpos[i]] := clali[i][classims[i]];
      perms[genpos[i]+len] := clali[i][classims[i]]^-1;
    end for;
    // perms[2*len+1..3*len] and [3*len+1..4*len] will be used for current
    // conjugates of the above class images, and their inverses
    for i in [2*len+1..4*len] do perms[i] := Id(G); end for;

    cenis :=  [ Centraliser(A,perms[i]) : i in [1..len] ];

    /* The inner backtrack runs through representatives of the classes
     * In this space-saving version, we use coset representatives of the
     * centralizers of the class reps, and do not store double coset reps,
     * even thoguh we will get the same images more than once.
     */

    lev:=len-1;

    /* The next loop locates the first valid position for a homomorphism
     * F->G in the backtrack
     */
    foundhom := false;
    
    while lev gt 0 do
      if not foundhom then
        transproc[lev] := TransversalProcess(A,cenis[lev]);
        perms[crep[lev]] := TransversalProcessNext(transproc[lev]);
        perms[crepinv[lev]] := perms[crep[lev]]^-1;
        tpdone[lev] := false;
        if lev gt 1 then //calculate relevant conjugate and inverse explicitly
          perms[2*len+lev] := perms[crepinv[lev]] * perms[lev] *
                              perms[crep[lev]];
          perms[3*len+lev] := perms[crepinv[lev]] * perms[len+lev] *
                              perms[crep[lev]];
        end if;
      end if;

      foundhom:=false;
      uplevel:=true;
      while uplevel and lev lt len do
	uplevel:=false;
        TR := TestRelsFirst;
	while not tpdone[lev] and sortrels[lev] ne [] do
          if lev eq 1 then TR(perms,crep,crepinv,~permword1,~ans);
          else TestRels(lev,perms,crep,crepinv,~ans);
          end if;
          if ans then break; end if;
          if TransversalProcessRemaining(transproc[lev]) eq 0 then
            tpdone[lev] := true;
          else
            perms[crep[lev]] := TransversalProcessNext(transproc[lev]);
            perms[crepinv[lev]] := perms[crep[lev]]^-1;
          end if;
          if lev gt 1 and not tpdone[lev] then
             perms[2*len+lev] := perms[crepinv[lev]] *
                                  perms[lev] * perms[crep[lev]];
             perms[3*len+lev] := perms[crepinv[lev]] *
                                 perms[len+lev] * perms[crep[lev]];
          end if;
          if Print gt 2 then print "Early increment at level",lev; end if;
	end while;
	if tpdone[lev] then
          if Print gt 1 then print "Early break at level",lev; end if;
	  uplevel := true;
	  lev +:= 1;
	  if lev lt len then
            if TransversalProcessRemaining(transproc[lev]) eq 0 then
              tpdone[lev] := true;
            else
              perms[crep[lev]] := TransversalProcessNext(transproc[lev]);
              perms[crepinv[lev]] := perms[crep[lev]]^-1;
            end if;
            if lev gt 1  and not tpdone[lev] then
               perms[2*len+lev] := perms[crepinv[lev]] *
                                  perms[lev] * perms[crep[lev]];
               perms[3*len+lev] := perms[crepinv[lev]] *
                                 perms[len+lev] * perms[crep[lev]];
            end if;
	  end if;
	end if;
      end while;

      if lev ge len then // we have come to the end of the search
        lev := 0; //to drop out of while loop
      elif lev gt 1 then
        lev -:= 1;
      else //found a homomorphism!
        imgs := [];
        for i in [1..len] do
          gpi := genpos[i];
          imgs[i] := gpi eq len select perms[gpi] else
                                       perms[gpi]^perms[crep[gpi]];
        end for;
        if not Surjective or sub<G|imgs> eq G then
          Append(~result,hom<F->G|imgs>);
          if Print gt 0 then
            print "Found a homomorphism";
          end if;
          if One then return result; end if;
        end if;
        foundhom := true;
  
        //Carry on with the backtrack search
        if TransversalProcessRemaining(transproc[lev]) eq 0 then
          tpdone[lev] := true;
        else
          perms[crep[lev]] := TransversalProcessNext(transproc[lev]);
          perms[crepinv[lev]] := perms[crep[lev]]^-1;
        end if;
      end if;
    end while;

    //increment classims in outer backtrack
    classims[ind]:=classims[ind]+1;
    while ind gt 0 and classims[ind] gt #clali[ind] do
      classims[ind] := 1;
      ind:=ind-1;
      if ind gt 0 then
	classims[ind] := classims[ind]+1;
      end if;
    end while;
  end while;

  return result;
end intrinsic;



