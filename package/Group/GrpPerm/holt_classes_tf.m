freeze;

PermRepAlmostSimpleGroupH := function(G,K)
/* Attempt to find a reasonable degree perm. rep. of the almost simple
 * group G/K.
 */
  local p, P, N, S, R, ind, minind, fact, m, pg, mp, mb, mpb;

  ind := #G div #K;
  minind := ind;
  S := K;
  R := SolubleResidual(G);
  for fact in Factorisation(ind) do
    p:=fact[1];
    P := sub<G | K, Sylow(R,p)>;
    N:=Normaliser(G,P);
    if #G div #N lt minind then
      S:=N; minind := #G div #N;
    end if;
  end for;

  m,pg := CosetAction(G,S);
  if IsPrimitive(pg) then
    return m,pg;
  end if;

  mp := MaximalPartition(pg);
  mb, mpb := BlocksAction(pg,mp);

  return m*mb, mpb;
end function;

ClassesAH := function(A,SQA)
// The classes of the almost simple group A modulo conjugation by soc(A).
// SQA should be the socle action of A.
  L, R, C := ClassesAHInternal(A, SQA);
  return [ <Order(R[i]), L[i], R[i], C[i]>: i in [1..#L]];
end function;

ClassesTFH := function(G:check:=false,centralisers:=true,powermaps:=false)
  local SA, SP, SAK, SQ, pSQ, M, SF, nSF, socreps, nsr, toAs, As, SQAs, NF, CF,
        fac, toP, toPs, P, Ps, degP, degPs, T, Ts, A, I, SQA, oA, toA, C, Cs,
        degAs, g, W, gensW, degW, WP, gensWP, gensWPinW, degWP, Wfacpts,
        Bfacpts, WPfac, Woffset, WPoffset, WtoWP, WPtoW, BtoW, r, t,
        genims, genim, im, tcomp, GtoW, IGtoW, goods, tosct, tailoffset,
        CSQ, crep, ctail, creps, ctails, crepi, crepinvi, Ocrepi, orep,
        i, j, allj, dom, crepres, crepinvires, found, cpermslist, Cg,
        ccent, ccentord, cent, centord, cconjelts, cconjelt, f, centim,
        centimord, ct, sv, rep, repim, centimgens, gotnew, elt, ielt,
        cperms, cperm, crepcent, crcgens, con, f1, f2, x, y, z, blockcoords,
        blocks, borepslist, blockreps, norbs, X, XGS, boreps, class, classes,
        creplist, ctaillist, OXGSlist, Ocreilist, classno, classnos,
        idclno, sqcl, orb, gres, cc, cc4, classespm, PermOffset, Permrestrict;

 PermOffset := function(p,offset,m,n)
 //Let permutation p of [1..m] act on [offset+1..offset+m] and cast into Sym(n)
 // e.g. PermOffset((1,2,5),6,5,12) = (7,8,11).
   return
    Sym(n)!([1..offset] cat [i^p + offset: i in [1..m]] cat [m+offset+1..n]);
 end function;

/*
 PermRestrict := function(p,dom,n)
 // p is in Sym(n).
 // dom should be a subset of {1..n} left fixed by p.
 // return restriction of p to dom as element of Sym(n)
 // e.g. PermRestrict( (1,2,6)(3,5), {3,4,5}, 6 ) = (3,5).
   local q;
   q := [1..n];
   for i in dom do q[i] := i^p; end for;
   return Sym(n)!q;
 end function; 
 */

  Print := GetVerbose("Classes");
  inittime := Cputime();
  assert #SolubleRadical(G) eq 1;

  SA, SP, SAK := SocleAction(G);
  SQ, pSQ, M := SocleQuotient(G);
  SF:=SocleFactors(G);
  nSF := #SF;
  if nSF eq 1 then
    return ClassesAlmostSimpleInternal(G:Centralizers:=centralisers, PowerMap:=powermaps);
  end if;
  socreps := [ Representative(o) : o in Orbits(SP) ];
  nsr := #socreps;

  // first locate socle factors and their induced automorphism
  // groups, and get their classes modulo conjugation in socle fatcors.
  Ts := []; toAs := [**]; As := [**]; SQAs := [**]; Cs := [**];
  toPs := [**]; Ps := []; degAs := []; degPs := [];
  for i in [1..nsr] do
    fac := socreps[i];
    NF := Stabiliser(SP,fac) @@ SA;
    CF := CentralizerOfNormalSubgroup(NF,SF[fac]:Check:=false);
    toP, P := CosetAction(G,NF);
    ReduceGenerators(~P);
    degP := Degree(P);
    T:=[G|Id(G)]; // transversal of NF in G.
    for i in [2..degP] do
      _,t := IsConjugate(P,1,i);
      T[i] := t@@toP;
    end for;
    Append(~degPs,degP); Append(~toPs,toP); Append(~Ps,P); Append(~Ts,T);

    oA := Index(NF,CF);
    if #CF eq 1 then
      A := NF;
      toA := IdentityHomomorphism(NF);
    else
      OCF := [ {t:t in o} : o in Orbits(CF) ];
      lengths := {* #o : o in OCF *};
      OCF := {@ o: o in OCF | Multiplicity(lengths, #o) gt 1 @};
      if #OCF gt 0 then
	  Agens := [Sym(#OCF)|];
	  for i in [1..Ngens(NF)] do
	    g := [];
	    for o in OCF do
	      Append(~g,Position(OCF,o^(NF.i)));
	    end for;
	    Append(~Agens,g);
	  end for;
	  A := sub<Sym(#OCF)|Agens>;
	  toA := hom<NF->A|Agens>;
      else
	 toA, A := PermRepAlmostSimpleGroupH(NF,CF);
      end if;
    end if;
    if #A ne oA then //not faithful
      toA, A := PermRepAlmostSimpleGroupH(NF,CF);
    end if;
    if Print ge 1 then
      "Degree of almost simple factor:",Degree(A);
    end if;
    ReduceGenerators(~A);
    Append(~toAs,toA);
    _, SQA := SocleQuotient(A);
    Append(~As,A); Append(~SQAs,SQA);
    Append(~degAs,Degree(A));
    Append(~Cs,ClassesAH(A,SQA));
  end for;

  //Now set up the direct product of wreath products W, into which we will
  //embed G. W maps onto permutation group WP permuting socel factors of W.
  degW := &+[ degAs[i] * degPs[i] : i in [1..nsr] ];
  degWP := &+[ degPs[i] : i in [1..nsr] ];
  gensW := [Sym(degW)|]; gensWP := [Sym(degWP)|]; 
  gensB := []; //gensB[i][j] = generators of j-th factor of base
               //group of i-th direct factor of W corresponding to As[i].
  gensP := [Sym(degWP)|];
  gensWPinW := [Sym(degW)|];
  Wfacpts := []; //Wfacpts[i] = points permuted by i-th direct factor of W. 
  Bfacpts := []; //Bfacpts[i][j] = points permuted by j-th factor of base
                 //group of i-th direct factor of W.
  WPfac := []; //For point k permuted by WP, WPfac[k] = <i,j>
              //where k corresponds to j-th factor of base
              //group of i-th direct factor of W. 
  Woffset := 0; WPoffset := 0;
  for i in [1..nsr] do
    Wfacpts[i] := <Woffset, Woffset + degAs[i]*degPs[i]>;
    Bfacpts[i] :=  [ <Woffset + (j-1)*degAs[i] + 1, Woffset + j*degAs[i]> :
                                         j in [1..degPs[i]] ];
    for j in [1..degPs[i]] do WPfac[j+WPoffset] := <i,j>; end for;

    gensB[i] := [PowerSequence(Sym(degW))|];
    for j in [1..degPs[i]] do
      gensB[i][j] := [ PermOffset(
                           As[i].k, Woffset+(j-1)*degAs[i], degAs[i], degW ) :
                                                     k in [1..Ngens(As[i])] ];  
    end for;
    gensW := gensW cat gensB[i][1];
    gensWP := gensWP cat [Id(Sym(degWP)) : j in [1..Ngens(As[i])] ];
    gensWPinW := gensWPinW cat [Id(Sym(degW)) : j in [1..Ngens(As[i])] ];

    //now produce generators of acting group
    for j in [1..Ngens(Ps[i])] do
      g := Ps[i].j;
      h := [];
      for l in [1..degPs[i]] do for k in [1..degAs[i]] do
        h[(l-1)*degAs[i] + k] := (l^g-1)*degAs[i] + k;
      end for; end for;
      h := Sym(degAs[i]*degPs[i])!h;
      Append(~gensW, PermOffset(h, Woffset, degAs[i]*degPs[i], degW));
      Append(~gensWPinW, PermOffset(h, Woffset, degAs[i]*degPs[i], degW));
      Append(~gensWP,PermOffset(g,WPoffset,degPs[i],degWP));
    end for;

    Woffset +:= degAs[i]*degPs[i]; 
    WPoffset +:= degPs[i]; 
  end for;

  W := sub< Sym(degW) | gensW >;
  WP := sub< Sym(degWP) | gensWP >;
  WtoWP := hom< W->WP | gensWP >;
  WPtoW := hom< WP->W | gensWPinW >;
  BtoW := [ [ hom< As[i]->W | gensB[i][j] > : j in [1..degPs[i]] ] :
                                                            i in [1..nsr] ];

  // Now we construct the embedding of G into W - this is done in the same way
  // as in WreathProductEmbeddings in the maximal subgroups code.

  genims := [];
  for g in [G.i : i in [1..Ngens(G)]] do
    Woffset := 0; WPoffset := 0;
    genim := Id(W);
    for i := 1 to nsr do
      //construct image of g in i-th direct factor of W 
      toP := toPs[i]; degP := degPs[i]; T := Ts[i];  toA := toAs[i];
      genim :=
          genim * PermOffset(toP(g),WPoffset,degPs[i],degWP) @ WPtoW;
      for j := 1 to degP do
        t := T[j];
        tcomp := (T[1^toP(t*g^-1)] * g * t^-1) @ toA @ BtoW[i][j];
        genim := genim * tcomp;
      end for;
      WPoffset +:= degPs[i]; 
      Woffset +:= degAs[i]*degPs[i]; 
    end for;
    Append(~genims,genim);
  end for;

  // assert IsHomomorphism(G,W,genims);
  GtoW := hom< G->W | genims >;
  IGtoW := Image(GtoW);

  //Now we are ready to start computing conjugacy classes.
  //We sort them according to their image modulo Soc(G) Soc(G
  CSQ := Classes(SQ);
  if powermaps then
    creplist :=[]; ctaillist :=[]; XGSlist:=[]; OXGSlist:=[]; Ocrepilist:=[];
    classno:=[];
  end if;

  //cpermslist := []; borepslist := [];

  classes := [];

  for c in CSQ do
    crep := c[3] @@ pSQ @ GtoW;
    ctail := [];
    ccent := [];
    ccentord := [];
    class := [];
    crepi := crep @ WtoWP; crepinvi := crepi @ WPtoW;
    Ocrepi := Orbits(sub<WP|crepi>);
    if powermaps then
      Append(~creplist,crep);
      Append(~Ocrepilist,Ocrepi);
      classnos := [];
    end if;
    norbs := #Ocrepi;
  /* crep is the representatives of the element of CSQ in W.
   * Representatives of classes under conjugation by Soc(G),
   * will be of form crep * ctail[1][j1] * ... * ctail[r][jr]
   * with r = #ctail = norbs, for arbitrary choices of j1,...,jr.
   * ccent[i][jk] will be the centralizer of crep * ctail[i][jk]
   * in the socle factors of W that lie in Ocrepi[i].
   * and ccentord[i][jk] its order.
   */

    tosct := 0;
    tailoffset := [];
    blocks := [];
    blockcoords := [];
    for x := 1 to norbs do
      o := Ocrepi[x];
      Append(~tailoffset,tosct);
      orep := Representative(o);
      i := WPfac[orep][1];
     //  assert forall(z){ oo: oo in o | WPfac[oo][1] eq i };
      j := WPfac[orep][2];
      allj := [ WPfac[oo][2] : oo in o ];
      dom := &join [ {Bfacpts[i][k][1]..Bfacpts[i][k][2]} : k in allj ]; 
      crepres := PermRestrict(crep,dom,degW);
      crepinvires := PermRestrict(crepinvi,dom,degW);
      //con := sub < W | [Socle(Image(BtoW[i][k])) : k in allj] >;
      // According to theory of conjugacy classes of wreath products,
      // crepres should be conjugate in W to crepinvires * (t @ BtoW[i][j])
      // for some class t in Cs[i] - find out which.
      isc := false;
      BtoWij := BtoW[i][j];
      for t in Cs[i] do
        isc, g := IsConjugate(W,crepinvires*(t[3]@BtoWij),crepres);
        if isc then
          goods := [r : r in Cs[i] | f(r[3]) eq f(t[3])] where f := SQAs[i];
          Append(~ctail,[((t[3]^-1 * s[3])@BtoWij)^g : s in goods] ) ;
          Append(~ccent,
           [ sub< W |
             [ &*[(t@BtoW[i][k])^g : k in allj] : t in Generators(s[4]) ] >
                                                               : s in goods ] );
          Append(~ccentord,[#(ccent[#ccent][i]) : i in [1..#goods] ]);
          Append(~blocks,[tosct+1..tosct+ #goods]);
          for y in [1.. #goods] do blockcoords[tosct+y] := <x,y>; end for; 
          tosct +:= #goods;
          break;
        end if;
      end for;
      assert isc;
    end for;  //for o in Ocrepi do
    if powermaps then Append(~ctaillist,ctail); end if;

if Print ge 2 then
    "Computing an action on", &*[#x:x in blocks], "classes";
end if;

    crepcent := Centraliser(SQ,c[3]) @@ pSQ @ GtoW;
    // Now we calculate fusion of these classes under crepcent
    // first try to minimize generators
    crcgens := [ crep ];
    H := sub< crepcent | crep, Socle(W) >;
    RandomSchreier(H);
    while H ne crepcent do
      repeat
	  g := Random(crepcent);
      until g notin H;
      Append(~crcgens,g); 
      H := sub< crepcent | H, g >;
      RandomSchreier(H);
    end while;

    cperms := [Sym(tosct)|]; cconjelts := [];
    for g in crcgens do
      cperm := []; cconjelt := [W|];
      h := g @ WtoWP;
      for x := 1 to norbs do
        o := Ocrepi[x];
        orep := Representative(o);
	oreph := orep^h;
	dummy := exists(z){z:z in [1..#Ocrepi]| oreph in Ocrepi[z]};
	assert dummy;
	i := WPfac[oreph][1];
	allj := [ WPfac[oo][2] : oo in Ocrepi[z] ];
	dom := &join [ {Bfacpts[i][k][1]..Bfacpts[i][k][2]} : k in allj ];
	con := sub < W | [Socle(Image(BtoW[i][k])) : k in allj] >;
	y := z;

        for i := 1 to #ctail[x] do
          t := ctail[x][i];
          f1 := PermRestrict(crep,dom,degW);
          f2 := PermRestrict((crep*t)^g,dom,degW);
          //f2 should be conjugate under con to f1*u for one u in ctail[y];
          for j := 1 to #ctail[y] do
            u := ctail[y][j];
            isc, f := IsConjugate(con,f2,f1*u);
            if isc then
              cperm[tailoffset[x]+i] := tailoffset[y]+j;
              cconjelt[tailoffset[x]+i] := f;
              break;
            end if;
          end for;
        end for;
      end for; //for x in [1..#Ocrepi] do
      Append(~cperms,cperm);
      Append(~cconjelts,cconjelt);
    end for; //for g in crcgens do
    X := sub< Sym(tosct) | cperms >;

    // We want the induced action of X on blockreps
    // where blockreps is the set of all sets containing one thing from 
    // each block

    broreps, brolens, XGSorbs := ClassesTFOrbitReps(blocks, X, powermaps); 
    if powermaps then Append(~OXGSlist, XGSorbs); end if;
    if Print ge 2 then
	"   found", #broreps," orbit representatives";
    end if;

    // now get the class reps
    for repct in [1..#broreps] do
      r := broreps[repct];
      g := crep;
      if centralisers then centgens := [G|]; end if;
      centord := 1;
      for s in r do
         centord *:= ccentord[blockcoords[s][1]][blockcoords[s][2]];
         g := g * ctail[blockcoords[s][1]][blockcoords[s][2]];
         if centralisers then
           cent := ccent[blockcoords[s][1]][blockcoords[s][2]];
           centgens := centgens cat [x @@ GtoW : x in Generators(cent) ];
         end if;
      end for;
      centimord := (#SQ div c[2]) div brolens[repct];
      centord *:= centimord;//order of Centraliser(IGtoW,g)
      h := g @@ GtoW; 
      if centralisers then
        centimgens := [ SQ | h@pSQ ];
        centim := sub< SQ | centimgens >;
        Append(~centgens,h);
	if false then/*####*/
        Cg := Centralizer(G,h:Subgroup:=sub< G | centgens >);
        Append(~class,<Order(h), #IGtoW div centord, h, Cg >);
	else/*####*/
        if centimord gt #centim then
          //Cg is not the full centralizer
          //we need to construct a Schreier vector for the orbit XGSorbs[repct]
          orb := {@ r @}; ct := 1; sv := [0];
          while ct le #orb do
            rep := orb[ct];
            for i in [1 .. #cperms] do
              repim := rep^cperms[i];
              if not repim in orb then
                Include(~orb,repim); Append(~sv,i);
              end if;
            end for;
            ct := ct+1;
          end while;
          //now adjoin new elements of centraliser
          while centimord gt #centim do
            gotnew:=false;
            while gotnew eq false do
              i:=Random([1..#orb]);
              k:=Random([1..#cperms]);
              j:=Position(orb,orb[i]^cperms[k]);
              if sv[j] eq k then continue; end if;
              elt := Id(W);
              ii := i; rep:=orb[ii];
              while sv[ii] ne 0 do
                s := sv[ii];
                ii := Position(orb,rep^(cperms[sv[ii]]^-1));
                rep:=orb[ii];
                for r in rep do elt := cconjelts[s][r] * elt; end for;
                elt := crcgens[s] * elt;
              end while;
              elt := elt * crcgens[k];
              rep := orb[i];
              for r in rep do elt := elt * cconjelts[k][r]; end for;
              ii := j; rep:=orb[ii];
              while sv[ii] ne 0 do
                s := sv[ii];
                ii := Position(orb,rep^(cperms[sv[ii]]^-1));
                rep:=orb[ii];
                for r in rep do elt := elt * cconjelts[s][r]^-1; end for;
                elt := elt * crcgens[s]^-1;
              end while;

              assert g*elt eq elt*g;
              ielt := elt @@ GtoW;
              if not ielt @ pSQ in centim then
                gotnew := true;
                Append(~centgens,ielt);
                Append(~centimgens,ielt @ pSQ);
                centim := sub< SQ | centimgens >;
              end if;
            end while;
          end while;
	end if;
        Cg := sub< G | centgens >;
        Append(~class,<Order(h), #IGtoW div centord, h, Cg >);
        end if; /*####*/
      else Append(~class,<Order(h), #IGtoW div centord, h >);
      end if;
      if powermaps then Append(~classnos,#classes+#class); end if;
    end for; //for repct in [1..#broreps] do
    if powermaps then Append(~classno,classnos); end if;
    assert &+[c[2] : c in class] eq #G div #Centraliser(SQ,c[3]); 
    
    //Append(~borepslist,broreps);
    //Append(~cpermslist,cperms);
    classes := classes cat class;
  end for; //for c in CSQ do

  assert &+[c[2] : c in classes] eq #G;
    if Print ge 1 then
	"Found", #classes, "classes. Time:",Cputime() - inittime;
    end if;
//if centralisers then
//assert [c[4] eq Centraliser(G,c[3]):c in classes] eq [true:c in classes];
//end if;

  if not powermaps then
    return classes;
  end if;

  // now for the power maps!
  // idclno := Representative({i:i in [1..#classes]|classes[i][3] eq Id(G)});
  dummy := exists(idclno){i:i in [1..#classes]|classes[i][3] eq Id(G)};
  assert dummy;
  if centralisers then
    classespm:=[ car<IntegerRing(), IntegerRing(), G, PowerStructure(GrpPerm),
               PowerSequence(car<IntegerRing(), IntegerRing()>) > | ];
  else classespm:=[ car<IntegerRing(), IntegerRing(), G,
               PowerSequence(car<IntegerRing(), IntegerRing()>) > | ];
  end if;
  for c in classes do
    cc := c;
    cc4 := [];
    for f in Factorisation(cc[1]) do
      g := cc[3]^f[1];
      if g eq Id(G) then
        Append(~cc4,<f[1],idclno>);
        continue;
      end if;
      //We have to locate the class number of g.
      //first replace by representative in socle quotient
      ginSQ := g@pSQ;
      oginSQ := Order(ginSQ);
      isc := false;
      for k := 1 to #CSQ do
	 if oginSQ eq CSQ[k,1] then
	     isc, h := IsConjugate(SQ, ginSQ, CSQ[k,3]);
	 end if;
         if isc then
             sqcl:=k; g:=g^(h @@ pSQ); g := g@GtoW;
             break;
         end if;
      end for;
      assert isc;

      crep := creplist[sqcl]; ctail :=  ctaillist[sqcl];
      OXGS := OXGSlist[sqcl];
      Ocrepi :=  Ocrepilist[sqcl];

      orb := {};
      tosct := 0;
      norbs := #Ocrepi;
      for x := 1 to norbs do
        o := Ocrepi[x];
        Append(~tailoffset,tosct);
        orep := Representative(o);
        i := WPfac[orep][1];
        j := WPfac[orep][2];
        allj := [ WPfac[oo][2] : oo in o ];
        dom := &join [ {Bfacpts[i][k][1]..Bfacpts[i][k][2]} : k in allj ];
        con := sub < W | [Socle(Image(BtoW[i][k])) : k in allj] >;
        gres := PermRestrict(g,dom,degW);
        crepres := PermRestrict(crep,dom,degW);
        //gres should be conjugate under con to crepres*t for a unique
        //t in ctail[x]. Find t.
        isc := false;
	ctailx := ctail[x];
        if gres eq crepres then
          for k := 1 to #ctailx do
            if ctailx[k] eq Id(W) then
              isc := true;
              Include(~orb,k+tosct); break;
            end if;
          end for;
        end if;
        if not isc then
          //first check which elements agree in order
          ordok := [ k: k in [1..#ctailx] |
                       CSgres eq CycleStructure(crepres*ctailx[k]) ]
			    where CSgres := CycleStructure(gres);
          if #ordok eq 1 then
            isc := true;
            Include(~orb,ordok[1]+tosct);
          else
	    for kk := 1 to #ordok-1 do
	      k := ordok[kk];
              isc := IsConjugate(con,gres,crepres*ctailx[k]); 
              if isc then
                 break;
              end if;
            end for;
	    if not isc then k := ordok[#ordok]; end if;
	    Include(~orb,k+tosct);
          end if;
        end if;
        tosct +:= #ctailx;
      end for; //for x in [1..norbs] do

      //find orbit representative of orb under centralizer action
      // j := Representative({ i: i in [1..#OXGS] | orb in OXGS[i] }); 
      dummy := exists(j){ i: i in [1..#OXGS] | orb in OXGS[i] };
      assert dummy;
      k := classno[sqcl][j];
      Append(~cc4,<f[1],k>);
      if check then assert IsConjugate(G,cc[3]^f[1],classes[k][3]); end if;
    end for; //for f in Factorisation(cc[1]) do

    Append(~cc,cc4);
    Append(~classespm,cc);
  end for; //for c in classes do
    if Print ge 1 then
	"Got power maps: Time:",Cputime() - inittime;
    end if;

  return classespm;

end function;

intrinsic ClassesTF(G::GrpPerm, C::BoolElt, P::BoolElt) -> SeqEnum[Tup]
{Derek Holt's algorithm for conjugacy classes of a permutation group with
trivial Fitting subgroup}

    require IsTrivial(Radical(G)): "Group must have trivial soluble radical";
    st, to_st := StandardGroup(G);
    if G cmpeq st then
	return ClassesTFH(G:centralisers := C, powermaps := P);
    else
	cl := ClassesTFH(st:centralisers := C, powermaps := P);
	len := #Rep(cl);
	if len eq 3 then
	    return [<t[1],t[2], t[3]@@to_st>:t in cl];
	elif len eq 4  then
	    return [<t[1],t[2],t[3]@@to_st,t[4]@@to_st>:t in cl];
	else assert len eq 5;
	    return [<t[1],t[2],t[3]@@to_st,t[4]@@to_st,t[5]>:t in cl];
	end if;
    end if;

end intrinsic;
