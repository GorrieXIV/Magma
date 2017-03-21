freeze;

RadMeet := function(G,H)
//intersection of subgp H of G with radical of G using presentation of radquot
  local r,rad,rq,Gtorq,nkg,imgens,Hgnos,gen,im,pos,hg,imh,wg,iwm,F, phi,h;
  r := G`LMGNode;
  rad := r`rad;
  rq := r`radquot;
  Gtorq := r`Gtoradquot;
  nkg := []; //normal generators of the kernel
  imgens := [];
  Hgnos := [];
  for i in [1..Ngens(H)] do
    gen := H.i;
    im := Gtorq(gen);
    if im eq Id(rq) then Append(~nkg,gen);
    else
      pos := Position(imgens, im);
      if pos ne 0 then Append(~nkg, gen^-1 * H.Hgnos[pos]);
      else
        pos := Position(imgens, im^-1);
          if pos ne 0 then Append(~nkg, gen * H.Hgnos[pos]);
            else Append(~imgens, im);
                 Hgnos[#imgens] := i; 
          end if;
      end if;
    end if;
  end for;
  if imgens eq [] then
    return H;
  end if;
  hg := [ H.Hgnos[k] : k in [1..#imgens] ];
  imh := sub< rq | imgens >;
  wg := WordGroup(imh);
  iwmimh := InverseWordMap(imh);
  F, phi := FPGroupStrong(imh);
  h := hom< F->wg | [F.i @ phi @ iwmimh : i in [1..Ngens(F)] ] >;
  for r in Relations(F) do
    Append(~nkg, Evaluate((LHS(r)*RHS(r)^-1) @ h, hg) );
  end for;
  return LMGNormalClosure(H, sub< Generic(G) | nkg> );
end function;

SubNorm := function(G,H:so:=256)
//normaliser of subgroup H of G
  local r,rpc,rad,rtopc,rq,Gtorq,rm,gmacts,imh,imn,nrqgens,x,inrqgens,cs,m,
    ptom,npcgens,inpcgens,rep,p,d,qpc,pctoqpc,qpc1,pctoqpc1,nqpc,npcmats,rado,
    radst,radonos,inrqgenmats,lo,fullgp,subgp,oa,oi,suborbs,ba,bi,rqact,rqst,
    fullo,deg,pt,perms,ssp,imssp,pos,gorbim,stg,istg,ords,iwmimn,slp,smat,pow,
    y,imhpres,hpres,phi,hptoh,rels,RV,w,imhpcg,hmeetm,hpm,shpm,qhpm,hpmtoqhpm,
    hmrpcg,hmrpctohmr,hmm,newnrqgens,newinrqgens,modconjmat,dqhpm,word,tail,
    perm,g,imhptohp,vec,longvec,imhpc,imhpctohp,ngmat,ngmatq,V,VQ,comps,
    imcomp,npermgp,npcpermgp,stab,substab,newstab,stabgens,newnpcgens,fqhpm,
    imnpc,imnpctonpcpermgp,npcstab,npcstabg,orighg,iwmimh,iwmnpg,imna,
    newimn,wd,gperm,ig,img,isc,qpcmm,fggens,iminrqgm,imngens;

  r := G`LMGNode;
  rpc := r`radPC;
  rad := r`rad;
  rtopc := r`radtoPC;
  rq := r`radquot;
  Gtorq := r`Gtoradquot;
  rm := r`radmods;
  //gmacts := r`rqradmodactions;
  gmacts := r`radmodactions;

  //find generators of H mod rad
  imhg := [];
  hg := [Generic(G)|];
  for i in [1..Ngens(H)] do
    gen := H.i;
    im := Gtorq(gen);
    if im ne Id(rq) and Position(imhg, im) eq 0 and
                                   Position(imhg, im^-1) eq 0 then
       Append(~imhg, im); Append(~hg, H.i);
    end if;
  end for;

  imh := sub< rq | imhg >;
  hmr := RadMeet(G,H);
  hmrpcg := [ hmr.i @ rtopc : i in [1..Ngens(hmr)] ];
  hmrpc := sub< rpc | hmrpcg >;
  hmrpctohmr := hom< hmrpc->rad | [ <hmrpcg[i],hmr.i> : i in [1..#hmrpcg] ] >;

//need to move to strong generators with presentation
  iwmimh := InverseWordMap(imh);
  imhpres, phi := FPGroupStrong(imh);
  imhg := [ rq | imhpres.i @ phi : i in [1..Ngens(imhpres)] ];
  hg := [ Generic(G) | Evaluate( iwmimh(imhg[i]), hg) : i in [1..#imhg] ];
  orighg := hg;  //hg itself will get bigger as we lift
  imh := sub< rq | imhg >;
  hpres := imhpres;
  hptoh := hom< hpres->Generic(G) | hg >;
  imhptohp := hom< imhpres->hpres | [hpres.i : i in [1..Ngens(imhpres)]] >;
  imhpcg := []; //generators of H in rad (as we lift)
  
  vprint LMG,1: "Calculating normaliser of image in radical quotient";
  imn := Normaliser( rq, imh );
  vprint LMG,1: "Normaliser of image in radical quotient has order", #imn;
  //try to minimise generators
  nrqgens := imhg;
  while sub< imn | nrqgens > ne imn do
    repeat x:=Random(imn); until not x in sub< imn | nrqgens >;
    Append(~nrqgens,x);
  end while;
  imn := sub< imn | nrqgens >;
  //normaliser will be stored as intersection of normaliser in rpc
  //with extra gens outside of radquot
  npcgens := [];
  inpcgens := []; //normaliser in rpc
  inrqgens := hg cat [nrqgens[i] @@ Gtorq : i in [#hg+1..#nrqgens]];
  cs := r`cseriesrad;
  qpc1, pctoqpc1 := quo< rpc | cs[#cs] >;
  imhpctohp := 0; imhpc:=0; //nonsense, but they need to be defined or Magma
                            //erroneously thinks there is an error!

  for lev in [#cs-1..1 by -1] do
    m := rm[lev][1];
    ptom := rm[lev][2];
    rep := rm[lev][3];
    p := #BaseRing(m);
    d := Dimension(m);
    vprint LMG,1: "Lifting through layer",lev,"of size",p,"^",d;
    //get action of generators of normaliser on layer
    //start with action of rpc
    qpc, pctoqpc := quo< rpc | cs[lev] >;
    //need the restriction of this map to H
    pctoqpch := hom< hmrpc -> qpc |
                              [pctoqpc(hmrpc.i) : i in [1..NPCgens(hmrpc)]] >;

    hmm:= hmrpc meet cs[lev+1];
    hmeetm := sub< V | [ V!(hmm.i @ ptom) : i in [1..Ngens(hmm)]] >
              where V := VectorSpace(m);
    vprint LMG,1: "Intersection of layer with H has size",p,
                                                    "^",Dimension(hmeetm);

    if Dimension(hmeetm) lt Dimension(m) then
      //first want stabiliser of hmeetm 
      //start with stabiliser in rad
      vprint LMG,1:
             "Calculating stabiliser of subgroup intersection with layer";
      nqpc := sub< qpc1 | [ npcgens[i] @ pctoqpc1  : i in [1..#npcgens]] >;
      npcmats := [ rep(nqpc.i @@ pctoqpc1) : i in [1..NPCgens(nqpc)] ];
      rado,radst,radonos := OrbitStabilizer(nqpc,npcmats,hmeetm);
      vprint LMG,2: "  #rado:",#rado,"#radst",#radst;
  
      //imhmats := [ gmacts[lev](orighg[i]:im:=imhg[i]) : i in [1..#imhg] ]; 
      imhmats := [ gmacts[lev](orighg[i]) : i in [1..#imhg] ]; 
      inrqgenmats := imhmats cat
   //[gmacts[lev](inrqgens[i]:im:=nrqgens[i]) : i in [1+#orighg..#inrqgens] ];
   [gmacts[lev](inrqgens[i]) : i in [1+#orighg..#inrqgens] ];
      //now stabiliser in G/rad - two strategies depending on #rado
      lo := #rado;
      if lo le so then
        vprint LMG,2: "  small orbit calculation";
        fullgp := sub< GL(d,p) | npcmats cat inrqgenmats >;
        oi := OrbitImage(fullgp,hmeetm);
        fggens := [ GL(d,p)| fullgp.i : i in [1..Ngens(fullgp)] ];
        suborbs :=
            Orbits( sub< oi | [oi.(Position(fggens,x)) : x in npcmats] > );
        ba, bi := BlocksAction(oi,suborbs[1]);
        iminrqgm := [ oi.(Position(fggens,x)) : x in inrqgenmats ];
        rqact := hom< imn->bi |
                            [iminrqgm[i] @ ba : i in [1..#inrqgens]] >;
        rqst := Stabiliser(bi,1) @@ rqact;
        vprint LMG,2: "  degree oi:",Degree(oi),"#rqst",#rqst;
      else
        vprint LMG,2: "  non-small orbit calculation";
        fullo := rado; deg := 1;
        perms := [ [] : i in [1..#inrqgenmats] ];
        pt := 1;
        while pt le deg do
          ssp := fullo[(pt-1)*lo+1];
          for i in [1..#inrqgenmats] do
            imssp := ssp ^ inrqgenmats[i];
            pos := Position(fullo,imssp);
            if pos eq 0 then //new orbit
              fullo join:=  OrbitStabilizer(nqpc,npcmats,imssp);
              deg +:= 1;
              perms[i][pt] := deg;
            else perms[i][pt] := (pos-1) div lo + 1;
            end if;
          end for;
          pt +:= 1;
        end while;
        ChangeUniverse(~perms, Sym(deg));
        gorbim := sub< Sym(deg) | perms >;
        rqact := hom< imn->gorbim | perms >;
        rqst := Stabiliser(gorbim,1) @@ rqact;
        vprint LMG,2: "  #fullo:",#fullo,"#rqst",#rqst;
      end if;
      //try to minimise generators
      newnrqgens := imhg;
      while sub< rqst | newnrqgens > ne rqst do
        repeat x:=Random(rqst); until not x in sub< rqst | newnrqgens >;
        Append(~newnrqgens,x);
      end while;
      iwmimn := InverseWordMap(imn);
      newinrqgens := orighg;
      for l in [#imhg+1..#newnrqgens] do
        slp := iwmimn(newnrqgens[l]);
        smat := Evaluate(slp, inrqgenmats);
        sst := hmeetm ^ smat;
        isc,x := IsConjugate(nqpc,npcmats,rado,radonos,sst); assert isc;
        newinrqgens[l] := Evaluate(slp,inrqgens) * ((x^-1) @@ pctoqpc1@@ rtopc);
      end for;
      nrqgens := newnrqgens;
      imn := sub< rqst | nrqgens >;
      iwmimn := InverseWordMap(imn);
      inrqgens := newinrqgens;
  
      npcgens := [radst.i @@ pctoqpc1 : i in [1..NPCgens(radst)] ];
      inpcgens := [ x @@ rtopc : x in npcgens ];
      imnpc := pctoqpc1( sub< rpc | npcgens > ); 
  
      //set up m, hmeetm and m/hmeetm as module for hpres
      vprint LMG,1: "Calculating normaliser of complement";
      hpm := GModule(hpres,imhmats cat [rep(imhpcg[i]): i in [1..#imhpcg]]);
      shpm := sub< hpm | [Eltseq(m!hmeetm.i) : i in [1..Ngens(hmeetm)]]>;
      qhpm, hpmtoqhpm := quo< hpm | shpm >; 
      dqhpm := Dimension(qhpm);

      //need complements in split extension of qhpm by hpres
      RV := [ qhpm!0 : i in [1..#Relations(hpres)] ]; 
      _, comps := ComplementVectors(qhpm, RV);
      CCS := ConjugateComplementSubspace(qhpm);
      assert comps[1] eq [ qhpm!0 : i in [1..Ngens(hpres)] ];
      vprint LMG,2 : "  ",#comps,"classes of complements";

      //now the messy bit! Action of normaliser on complements
      //we will seperate the code for calculating words and tails (which
      //was also used in Subgroups code) as a function
      GetWordsAndTails := function(ngen : imngen:="" )
        //ngen should be in normaliser as computed so far
        local word,tail,ct,ihg,g,wd;
        word := []; tail := [];
        ct := 0;
        ihg := imhg cat [Id(rq) : i in [#imhg+1..#hg]];
        for hgen in hg do
          g := ngen*hgen*ngen^-1;
          if imngen cmpne "" then
             //avoid costly application of Gtorq
             ct +:= 1;
             wd := (imngen * ihg[ct] * imngen^-1) @@ phi; 
          else
             wd := g @ Gtorq @@ phi;
          end if;
          hpwd := wd @ imhptohp;
          g := (hpwd @ hptoh)^-1 * g; 
          if lev lt #cs -1 then
            //also have some generators in H meet rad
            //hpwd := hpwd * (imhpc!(g @ rtopc @ pctoqpc1)) @ imhpctohp;
            hpwd := hpwd * g @ rtopc @ pctoqpc1 @ imhpctohp;
          end if;
          //now conjugate image of hpwd back to compute tail
          g := hgen^-1 * ngen^-1 * hptoh(hpwd) * ngen;
          Append(~word, hpwd);
          Append( ~tail, (hpm!Eltseq(g @ rtopc @ ptom)) @ hpmtoqhpm ); 
        end for; 
        return word, tail;
      end function;

      if #comps eq 1 then
        perms := [ [1] : ngen in inpcgens cat inrqgens ];
      else
        perms := [];
        imngens := [ Id(rq) : i in [1..#inpcgens]] cat nrqgens;
        ct := 0;
        for ngen in inpcgens cat inrqgens do
          //first work out word for ngen*hgen*ngen^-1 for hgen in hg and
          //tail when we conjugate back
          ct +:= 1;
          word, tail := GetWordsAndTails(ngen : imngen := imngens[ct]);
  
          //to work out the action on complements, we also need the matrix
          //of ngen in its action on qhpm
          ngmat := ngen @ gmacts[lev];
          ngmatq := [];
          V := VectorSpace(GF(p), d);
          VQ := VectorSpace(GF(p), dqhpm);
          for i in [1..dqhpm] do
            Append(~ngmatq,
              VQ!((hpm!(V!((qhpm.i) @@ hpmtoqhpm) * ngmat)) @ hpmtoqhpm) );
          end for;
          ngmatq := Matrix(ngmatq);
  
          perm := [];
          for comp in comps do
            longvec := [];
            for i in [1..#tail] do
              vec := tail[i] + TailVector(qhpm,comp,word[i])*ngmatq;
              longvec cat:= Eltseq(vec);
            end for;
            longvec := Vector(longvec);
            vec, longvec := DecomposeVector(CCS,longvec);
            //reconstruct image of complement from longvec
            imcomp := [];
            vec := qhpm!0;
            for j in [1..#tail] do
               for k in [1..dqhpm] do
                 vec[k] := longvec[(j-1)*dqhpm+k];
               end for;
               Append(~imcomp,vec);
            end for;
            pos := Position(comps,imcomp);
            if pos eq 0 then
               error "Image of complement under conjugation is not in list!";
            end if;
            Append(~perm, pos);
          end for; //for comp in comps do
          Append(~perms,perm);
        end for;  //for ngen in inpcgens cat inrqgens do
      end if; //if #comps eq 1 then

      //We want the stabiliser of the first comp - should be H itself
      npermgp := sub< Sym(#comps) | perms >;
      npcpermgp := sub< npermgp | [ npermgp.i : i in [1..#npcgens] ] >;
      stab := Stabiliser(npermgp,1);
      substab := Stabiliser(npcpermgp,1);
      vprint LMG,2: "  #npermgp:", #npermgp, "#npcpermgp:", #npcpermgp,
            "#stab:", #stab, "#substab:", #substab;
      stabgens := [ substab.i : i in [1..Ngens(substab)] ];
      //the generators of H should be in stab.
      stabgens cat:= [ npermgp.i : i in [#inpcgens+1 .. #inpcgens+#orighg] ];
      assert forall{x : x in stabgens | 1^x eq 1};
      
      //minimise generators of stab, starting with substab, followed by
      //generators in H
      newstab := sub< stab | stabgens >;
      while newstab ne stab do
        repeat g := Random(stab); until not g in newstab;
        Append(~stabgens, g);
        newstab := sub< stab | substab, stabgens >;
      end while;
      stab := newstab;
      iwmnpg := InverseWordMap(npermgp);
  
      //now we can put together the new generators of N at this level
      //start with pc generators in H - getting them into H is contorted!
      newnpcgens := [ (m!Eltseq(hpm!shpm.i)) @@ ptom @ pctoqpc @@ pctoqpch
                                           : i in [1..Dimension(hmeetm)] ];

      //now other generators from the module
      fqhpm := Fix(qhpm);
      newnpcgens cat:= [ (m!(Eltseq(fqhpm.i @@ hpmtoqhpm))) @@ ptom :
                             i in [1..Dimension(fqhpm)] ];

      //to recognise conjugating elements from qhpm, we'll need matrix
      //of actions of basis vector
      modconjmat := HorizontalJoin([idm - am : am in ActionGenerators(qhpm)])
                    where idm := IdentityMatrix(GF(p), dqhpm);
      ModConjElt := function(tail)
        //this calculates said conjugating element from qhpm
        local longvec, sol;
        longvec := Vector( &cat[ Eltseq(t) : t in tail ] );
        sol := Solution(modconjmat, longvec);
        return (m!Eltseq((qhpm!sol) @@ hpmtoqhpm)) @@ ptom;
      end function;

      //remaining generators from rad
      if lev lt #cs-1 then
        imnpctonpcpermgp := hom< imnpc -> npcpermgp |
                 [ <npcgens[i]@pctoqpc1, npermgp.i> : i in [1..#npcgens] ] >;
        npcstab := substab @@ imnpctonpcpermgp @@ pctoqpc1;  
        //now adjust by elements from modulepc
        npcstabg := [ npcstab.i : i in [1..NPCgens(npcstab)] ];
        for i in [1..NPCgens(npcstab)] do 
          _,tail := GetWordsAndTails(npcstab.i @@ rtopc : imngen:=Id(rq) );
          npcstabg[i] *:= ModConjElt(tail)^-1;
        end for;
        newnpcgens cat:= npcstabg;
      end if;

      //finally the generators from outside of rad and H
      newinrqgens :=  orighg;
      nrqgens := imhg;
      newimn := sub< rq | nrqgens >;
      //we need generators of kernel of imn onto the perm group on comps
      //need to get induced action of imn on orbits of npcpermgp
      oa := OrbitAction(npermgp,1);
      bi := BlocksImage( Image(oa), { oa(x) : x in Orbit(npcpermgp,1) } );
      imna := hom< imn -> bi | [ bi.(#inpcgens+i) : i in [1..Ngens(imn)]] >;
      for g in Generators(Kernel(imna)) do if not g in newimn then
        Append(~nrqgens, g);
        newimn := sub< rq | nrqgens >;
        wd := iwmimn(g);
        ig := Evaluate(wd, inrqgens);
        if lev lt #cs-1 then
          gperm :=
                Evaluate(wd, [npermgp.(#inpcgens+i) : i in [1..Ngens(imn)]] ); 
          isc, x := IsConjugate(npcpermgp, 1^gperm, 1); assert isc;
          ig *:= (x  @@ imnpctonpcpermgp @@ pctoqpc1 @@ rtopc);
        end if;
        _,tail := GetWordsAndTails(ig : imngen := g );
        ig *:= (ModConjElt(tail)^-1) @@ rtopc;
        Append(~newinrqgens, ig);
      end if; end for; 

      //and also inverse images of generators of stabiliser in perm gp
      for i in [Ngens(substab)+#orighg+1 .. #stabgens] do
	g := Evaluate(iwmnpg(stabgens[i]), inpcgens cat inrqgens);
        img := g@Gtorq;
        if not img in newimn then
          Append(~nrqgens, img); 
          _,tail := GetWordsAndTails(g : imngen:=img );
          g *:= (ModConjElt(tail)^-1) @@ rtopc;
          Append(~newinrqgens, g);
        end if;
      end for;

//reset things
      npcgens := newnpcgens;
      inpcgens := [ Generic(G) | x @@ rtopc : x in npcgens ];
      imnpc := pctoqpc( sub< rpc | npcgens > ); 

      inrqgens := newinrqgens;
      imn := sub< rq | nrqgens >;
      vprint LMG,1: "Order of image of normaliser in radical quotient is now",
                    #imn;
      vprint LMG,1: "Order of normaliser at this layer in radical is",
                    #imnpc;
    else  //i.e. if Dimension(hmeetm) eq Dimension(m) then
      //set up m, hmeetm and m/hmeetm as module for hpres
      //imhmats := [ gmacts[lev](hg[i]:im:=imhg[i]) : i in [1..#imhg] ]; 
      imhmats := [ gmacts[lev](hg[i]) : i in [1..#imhg] ]; 
      hpm := GModule(hpres,imhmats cat [rep(imhpcg[i]): i in [1..#imhpcg]]);
      shpm := sub< hpm | [Eltseq(m!hmeetm.i) : i in [1..Ngens(hmeetm)]]>;
      qhpm, hpmtoqhpm := quo< hpm | shpm >; 
      qpcmm := pctoqpch(hmm);
      npcgens := [ qpcmm.i @@ pctoqpc : i in [1..Ngens(qpcmm)] ] cat npcgens;
      inpcgens := [ npcgens[i] @@ rtopc : i in [1..Ngens(qpcmm)] ] cat inpcgens;
      imnpc := pctoqpc( sub< rpc | npcgens > ); 
    end if;

    //deal with extending H and hpres through layer -
    //only really need do this for lev gt 1
    if lev gt 1 then
      rels := Relations(hpres);
      RV := [];
      for rel in rels do
        w := LHS(rel)*RHS(rel)^-1;
        Append(~RV, shpm!hpm!Eltseq(m!(w @ hptoh @ rtopc @ ptom)));
      end for;
      hpres := ModuleExtension(shpm, RV);
      //need to get inverse images of hmeetm in H, which seems cumbersome!
      newhpcg := [ (m!Eltseq(hpm!shpm.i)) @@ ptom @ pctoqpc @@ pctoqpch
                                             : i in [1..Ngens(shpm)] ];
      imhpcg cat:= newhpcg;
      //also need various homomorphisms to the new hpres
      imhpc := pctoqpc( sub< rpc | imhpcg > ); 
      hg cat:= [ h @ hmrpctohmr : h in newhpcg ];
      imhpctohp := hom< imhpc->hpres |
          [ < imhpcg[i]@pctoqpc, hpres.(i+ #imhg) > : i in [1..#imhpcg]] >;
      hptoh := hom< hpres->Generic(G) | hg >;
      imhptohp := hom< imhpres->hpres | [hpres.i : i in [1..Ngens(imhpres)]] >;
  
      qpc1 := qpc;
      pctoqpc1 := pctoqpc;
    end if;
  end for; //for lev in [#cs-1..1 by -1] do
  return sub< Generic(G) | inpcgens cat inrqgens >;
end function;

SubIsConj := function(G,K,H:so:=256)
//test subgroups K and H of G for conjugacy
  local r,rpc,rad,rtopc,rq,Gtorq,rm,gmacts,imh,imn,nrqgens,x,inrqgens,cs,m,
    ptom,npcgens,inpcgens,rep,p,d,qpc,pctoqpc,qpc1,pctoqpc1,nqpc,npcmats,rado,
    radst,radonos,inrqgenmats,lo,fullgp,subgp,oa,oi,suborbs,ba,bi,rqact,rqst,
    fullo,deg,pt,perms,ssp,imssp,pos,gorbim,stg,istg,ords,iwmimn,slp,smat,pow,
    y,imhpres,hpres,phi,hptoh,rels,RV,w,imhpcg,hmeetm,hpm,shpm,qhpm,hpmtoqhpm,
    hmrpcg,hmrpctohmr,hmm,newnrqgens,newinrqgens,modconjmat,dqhpm,word,
    perm,g,imhptohp,vec,longvec,imhpc,imhpctohp,ngmat,ngmatq,V,VQ,comps,
    imcomp,npermgp,npcpermgp,stab,substab,newstab,stabgens,newnpcgens,fqhpm,
    imnpc,imnpctonpcpermgp,npcstab,npcstabg,orighg,iwmimh,iwmnpg,imna,
    newimn,wd,gperm,ig,img,isc,qpcmm,fggens,iminrqgm,imngens,
    ans,KK,imk,iwmimg,kg,kmr,kmrpc,kmm,kmeetm,kmeetmpos,pctoqpck1,kmrpctokmr,
    kmrpcg,x1,x1pc,x2,x2pc,tails,imkpcg,posK;


  r := G`LMGNode;
  rpc := r`radPC;
  rad := r`rad;
  rtopc := r`radtoPC;
  rq := r`radquot;
  Gtorq := r`Gtoradquot;
  rm := r`radmods;
  //gmacts := r`rqradmodactions;
  gmacts := r`radmodactions;

  //find generators of H mod rad
  imhg := [];
  hg := [Generic(G)|];
  for i in [1..Ngens(H)] do
    gen := H.i;
    im := Gtorq(gen);
    if im ne Id(rq) and Position(imhg, im) eq 0 and
                                   Position(imhg, im^-1) eq 0 then
       Append(~imhg, im); Append(~hg, H.i);
    end if;
  end for;

  imh := sub< rq | imhg >;
  imk := sub< rq | [K.i @ Gtorq : i in [1..Ngens(K)]] >;
  isc, x := IsConjugate( rq, imk, imh);
  if not isc then return false, _; end if;
  vprint LMG,2: "  Initialising conjugating element";
  ans := x @@ Gtorq;  KK := K^ans;
  
  hmr := RadMeet(G,H);
  hmrpcg := [ hmr.i @ rtopc : i in [1..Ngens(hmr)] ];
  hmrpc := sub< rpc | hmrpcg >;
  hmrpctohmr := hom< hmrpc->rad | [ <hmrpcg[i],hmr.i> : i in [1..#hmrpcg] ] >;

  kmr := RadMeet(G,K)^ans;
  K := KK;
  kmrpcg := [ kmr.i @ rtopc : i in [1..Ngens(kmr)] ];
  kmrpc := sub< rpc | kmrpcg >;
  kmrpctokmr := hom< kmrpc->rad | [ <kmrpcg[i],kmr.i> : i in [1..#kmrpcg] ] >;

  if #hmrpc ne #kmrpc then return false, _; end if;

//need to move to strong generators with presentation
  iwmimh := InverseWordMap(imh);
  imhpres, phi := FPGroupStrong(imh);
  imhg := [ rq | imhpres.i @ phi : i in [1..Ngens(imhpres)] ];
  hg := [ Generic(G) | Evaluate( iwmimh(imhg[i]), hg) : i in [1..#imhg] ];
  orighg := hg;  //hg itself will get bigger as we lift
  imh := sub< rq | imhg >;
  hpres := imhpres;
  hptoh := hom< hpres->Generic(G) | hg >;
  imhptohp := hom< imhpres->hpres | [hpres.i : i in [1..Ngens(imhpres)]] >;
  imhpcg := []; //generators of H in rad (as we lift)
  
  vprint LMG,1: "Calculating normaliser of image in radical quotient";
  imn := Normaliser( rq, imh );
  vprint LMG,1: "Normaliser of image in radical quotient has order", #imn;
  //try to minimise generators
  nrqgens := imhg;
  while sub< imn | nrqgens > ne imn do
    repeat x:=Random(imn); until not x in sub< imn | nrqgens >;
    Append(~nrqgens,x);
  end while;
  imn := sub< imn | nrqgens >;
  //normaliser will be stored as intersection of normaliser in rpc
  //with extra gens outside of radquot
  npcgens := [];
  inpcgens := []; //normaliser in rpc
  inrqgens := hg cat [nrqgens[i] @@ Gtorq : i in [#hg+1..#nrqgens]];
  cs := r`cseriesrad;
  qpc1, pctoqpc1 := quo< rpc | cs[#cs] >;
  imhpctohp := 0; imhpc:=0; //nonsense, but they need to be defined or Magma
                            //erroneously thinks there is an error!

  for lev in [#cs-1..1 by -1] do
    m := rm[lev][1];
    ptom := rm[lev][2];
    rep := rm[lev][3];
    p := #BaseRing(m);
    d := Dimension(m);
    vprint LMG,1: "Lifting through layer",lev,"of size",p,"^",d;
    //get action of generators of normaliser on layer
    //start with action of rpc
    qpc, pctoqpc := quo< rpc | cs[lev] >;
    //need the restriction of this map to H
    pctoqpch := hom< hmrpc -> qpc |
                              [pctoqpc(hmrpc.i) : i in [1..NPCgens(hmrpc)]] >;

    hmm:= hmrpc meet cs[lev+1];
    V := VectorSpace(m);
    hmeetm := sub< V | [ V!(hmm.i @ ptom) : i in [1..Ngens(hmm)]] >;
    vprint LMG,1: "Intersection of layer with H has size",p,
                                                    "^",Dimension(hmeetm);

    kmm:= kmrpc meet cs[lev+1];
    kmeetm := sub< V | [ V!(kmm.i @ ptom) : i in [1..Ngens(kmm)]] >;
    if Dimension(kmeetm) ne Dimension(hmeetm) then return false,_; end if;

    if Dimension(hmeetm) lt Dimension(m) then
      //first want stabiliser of hmeetm 
      //start with stabiliser in rad
      vprint LMG,1:
             "Calculating stabiliser of subgroup intersection with layer";
      nqpc := sub< qpc1 | [ npcgens[i] @ pctoqpc1  : i in [1..#npcgens]] >;
      npcmats := [ rep(nqpc.i @@ pctoqpc1) : i in [1..NPCgens(nqpc)] ];
      rado,radst,radonos := OrbitStabilizer(nqpc,npcmats,hmeetm);
      vprint LMG,2: "  #rado:",#rado,"#radst",#radst;
  
      //imhmats := [ gmacts[lev](orighg[i]:im:=imhg[i]) : i in [1..#imhg] ]; 
      imhmats := [ gmacts[lev](orighg[i]) : i in [1..#imhg] ]; 
      inrqgenmats := imhmats cat
   //[gmacts[lev](inrqgens[i]:im:=nrqgens[i]) : i in [1+#orighg..#inrqgens] ];
   [gmacts[lev](inrqgens[i]) : i in [1+#orighg..#inrqgens] ];
      //now stabiliser in G/rad - two strategies depending on #rado
      lo := #rado;
      if lo le so then
        vprint LMG,2: "  small orbit calculation";
        fullgp := sub< GL(d,p) | npcmats cat inrqgenmats >;
        if not kmeetm in Orbit(fullgp, hmeetm) then return false,_; end if;
        oi, orb := OrbitImage(fullgp,hmeetm);
        p1 := Position(orb,hmeetm); p2 := Position(orb,kmeetm);
        assert p1 gt 0 and p2 gt 0;
        isc, x1 := IsConjugate(oi, p1, p2);  assert isc;
        fggens := [ GL(d,p)| fullgp.i : i in [1..Ngens(fullgp)] ];
        suborbs :=
            Orbits( sub< oi | [oi.(Position(fggens,x)) : x in npcmats] > );
        ba, bi := BlocksAction(oi,suborbs[1]);
        iminrqgm := [ oi.(Position(fggens,x)) : x in inrqgenmats ];
        rqact := hom< imn->bi |
        //                  [inrqgenmats[i] @ oa @ ba : i in [1..#inrqgens]] >;
                            [iminrqgm[i] @ ba : i in [1..#inrqgens]] >;
        ba, bi := BlocksAction(oi,suborbs[1]);
        x1 := x1 @ ba @@ rqact @@ Gtorq;
        vprint LMG,2: "  Adjusting conjugating element 1";
        ans *:= x1^-1; K := K^(x1^-1);
        kmr := kmr^(x1^-1);
        kmrpcg := [ kmr.i @ rtopc : i in [1..Ngens(kmr)] ];
        kmrpc := sub< rpc | kmrpcg >;
        kmrpctokmr :=
             hom< kmrpc->rad | [ <kmrpcg[i],kmr.i> : i in [1..#kmrpcg] ] >;
        kmm:= kmrpc meet cs[lev+1];
        kmeetm := sub< V | [ V!(kmm.i @ ptom) : i in [1..Ngens(kmm)]] >;
        rqst := Stabiliser(bi,1) @@ rqact;
        vprint LMG,2: "  degree oi:",Degree(oi),"#rqst",#rqst;
      else
        vprint LMG,2: "  non-small orbit calculation";
        fullo := rado; deg := 1;
        perms := [ [] : i in [1..#inrqgenmats] ];
        pt := 1;
        while pt le deg do
          ssp := fullo[(pt-1)*lo+1];
          for i in [1..#inrqgenmats] do
            imssp := ssp ^ inrqgenmats[i];
            pos := Position(fullo,imssp);
            if pos eq 0 then //new orbit
              fullo join:=  OrbitStabilizer(nqpc,npcmats,imssp);
              deg +:= 1;
              perms[i][pt] := deg;
            else perms[i][pt] := (pos-1) div lo + 1;
            end if;
          end for;
          pt +:= 1;
        end while;
        kmeetmpos := Position(fullo,kmeetm);
        if kmeetmpos eq 0 then return false,_; end if;
        kmeetmpos := (kmeetmpos-1) div lo + 1;
        ChangeUniverse(~perms, Sym(deg));
        gorbim := sub< Sym(deg) | perms >;
        rqact := hom< imn->gorbim | perms >;
        isc, x1 := IsConjugate(gorbim, 1, kmeetmpos); assert isc;
        x1 := x1 @ ba @@ rqact @@ Gtorq;
        vprint LMG,2: "  Adjusting conjugating element 1";
        ans *:= x1^-1; K := K^(x1^-1);
        kmr := kmr^(x1^-1);
        kmrpcg := [ kmr.i @ rtopc : i in [1..Ngens(kmr)] ];
        kmrpc := sub< rpc | kmrpcg >;
        kmrpctokmr :=
             hom< kmrpc->rad | [ <kmrpcg[i],kmr.i> : i in [1..#kmrpcg] ] >;
        kmm:= kmrpc meet cs[lev+1];
        kmeetm := sub< V | [ V!(kmm.i @ ptom) : i in [1..Ngens(kmm)]] >;
        rqst := Stabiliser(gorbim,1) @@ rqact;
        vprint LMG,2: "  #fullo:",#fullo,"#rqst",#rqst;
      end if;

      if lev lt #cs -1 then
        isc,x2 := IsConjugate(nqpc,npcmats,rado,radonos,kmeetm);
        if not isc then return false,_; end if;
        vprint LMG,2: "  Adjusting conjugating element 2";
        x2pc := x2 @@ pctoqpc1;
        x2 := x2pc @@ rtopc;
        ans *:= x2^-1; K := K^(x2^-1);
        kmr := kmr^(x2^-1);
        kmrpcg := [ kmrpcg[i] ^ (x2pc^-1) : i in [1..Ngens(kmr)] ];
        kmrpc := sub< rpc | kmrpcg >;
        kmrpctokmr :=
             hom< kmrpc->rad | [ <kmrpcg[i],kmr.i> : i in [1..#kmrpcg] ] >;
      else assert kmeetm eq hmeetm;
      end if;

      //try to minimise generators
      newnrqgens := imhg;
      while sub< rqst | newnrqgens > ne rqst do
        repeat x:=Random(rqst); until not x in sub< rqst | newnrqgens >;
        Append(~newnrqgens,x);
      end while;
      iwmimn := InverseWordMap(imn);
      newinrqgens := orighg;
      for l in [#imhg+1..#newnrqgens] do
        slp := iwmimn(newnrqgens[l]);
        smat := Evaluate(slp, inrqgenmats);
        sst := hmeetm ^ smat;
        isc,x := IsConjugate(nqpc,npcmats,rado,radonos,sst); assert isc;
        newinrqgens[l] := Evaluate(slp,inrqgens) * ((x^-1) @@ pctoqpc1@@ rtopc);
      end for;
      nrqgens := newnrqgens;
      imn := sub< rqst | nrqgens >;
      iwmimn := InverseWordMap(imn);
      inrqgens := newinrqgens;
  
      npcgens := [radst.i @@ pctoqpc1 : i in [1..NPCgens(radst)] ];
      inpcgens := [ x @@ rtopc : x in npcgens ];
      imnpc := pctoqpc1( sub< rpc | npcgens > ); 
  
      //set up m, hmeetm and m/hmeetm as module for hpres
      vprint LMG,1: "Calculating normaliser of complement";
      hpm := GModule(hpres,imhmats cat [rep(imhpcg[i]): i in [1..#imhpcg]]);
      shpm := sub< hpm | [Eltseq(m!hmeetm.i) : i in [1..Ngens(hmeetm)]]>;
      qhpm, hpmtoqhpm := quo< hpm | shpm >; 
      dqhpm := Dimension(qhpm);
//"pp",Dimension(hmeetm),Dimension(shpm),Dimension(hpm), dqhpm;
//[Eltseq(m!hmeetm.i) : i in [1..Dimension(hmeetm)]];

      //need complements in split extension of qhpm by hpres
      RV := [ qhpm!0 : i in [1..#Relations(hpres)] ]; 
      _, comps := ComplementVectors(qhpm, RV);
      CCS := ConjugateComplementSubspace(qhpm);
      assert comps[1] eq [ qhpm!0 : i in [1..Ngens(hpres)] ];
      vprint LMG,2 : "  ",#comps,"classes of complements";

      //to identify the complement defined by K, we need to make generators
      //of K correspond to those of H
      kg := [ K.i : i in [1..Ngens(K)] ];
      imk := sub< rq | [k @ Gtorq : k in kg] >;
      iwmimk := InverseWordMap(imk);
      kg := [ Generic(G) | Evaluate( iwmimk(imhg[i]), kg) : i in [1..#imhg] ];
//"oo",#imhg,#imhpcg;
      tails := [ (hg[i]^-1 * kg[i]) @ rtopc : i in [1..#imhg] ];
      if lev lt #cs-1 then
        //adjust by elements in PC-group
        pctoqpck1 := hom< kmrpc -> qpc1 |
                              [pctoqpc1(kmrpc.i) : i in [1..NPCgens(kmrpc)]] >;
        tails := [ t * ((t^-1) @ pctoqpc1 @@ pctoqpck1) : t in tails ];
        tails cat:= 
                    [ (t^-1) * (t @ pctoqpc1 @@ pctoqpck1) : t in imhpcg ];
      end if;
      tails := [ (hpm!Eltseq(t @ ptom)) @ hpmtoqhpm : t in tails ];
//"tails:",tails;
      //now we can set up the vector representing the complement K
      longvec := Vector( &cat[ Eltseq(t) : t in tails ] ); 
      vec, longvec := DecomposeVector(CCS,longvec);
//"a",vec,longvec;
      //reconstruct image of complement from longvec
      imcomp := [];
      vec := qhpm!0;
      for j in [1..#tails] do
         for k in [1..dqhpm] do
            vec[k] := longvec[(j-1)*dqhpm+k];
         end for;
         Append(~imcomp,vec);
      end for;
//"b",CCS,comps,imcomp;
      posK := Position(comps,imcomp);
      if posK eq 0 then
         error "Complement defined by K is not in list!";
      end if;

      //now the messy bit! Action of normaliser on complements
      //we will seperate the code for calculating words and tails (which
      //was also used in Subgroups code) as a function
      GetWordsAndTails := function(ngen : imngen:="" )
        //ngen should be in normaliser as computed so far
        local word, tail, ct, ihg, g, wd, hpwd;
        word := []; tail := [];
        ct := 0;
        ihg := imhg cat [Id(rq) : i in [#imhg+1..#hg]];
        for hgen in hg do
          g := ngen*hgen*ngen^-1;
          if imngen cmpne "" then
             //avoid costly application of Gtorq
             ct +:= 1;
             wd := (imngen * ihg[ct] * imngen^-1) @@ phi;
          else
             wd := g @ Gtorq @@ phi;
          end if;
          hpwd := wd @ imhptohp;
          g := (hpwd @ hptoh)^-1 * g; 
          if lev lt #cs -1 then
            //also have some generators in H meet rad
            //hpwd := hpwd * (imhpc!(g @ rtopc @ pctoqpc1)) @ imhpctohp;
            hpwd := hpwd * g @ rtopc @ pctoqpc1 @ imhpctohp;
          end if;
          //now conjugate image of hpwd back to compute tails
          g := hgen^-1 * ngen^-1 * hptoh(hpwd) * ngen;
          Append(~word, hpwd);
          Append( ~tail, (hpm!Eltseq(g @ rtopc @ ptom)) @ hpmtoqhpm ); 
        end for; 
        return word, tail;
      end function;

      if #comps eq 1 then
        perms := [ [1] : ngen in inpcgens cat inrqgens ];
      else
        perms := [];
        imngens := [ Id(rq) : i in [1..#inpcgens]] cat nrqgens;
        ct := 0;
        for ngen in inpcgens cat inrqgens do
          //first work out word for ngen*hgen*ngen^-1 for hgen in hg and
          //tail when we conjugate back
          ct +:= 1;
          word, tails := GetWordsAndTails(ngen : imngen := imngens[ct]);
  
          //to work out the action on complements, we also need the matrix
          //of ngen in its action on qhpm
          ngmat := ngen @ gmacts[lev];
          ngmatq := [];
          V := VectorSpace(GF(p), d);
          VQ := VectorSpace(GF(p), dqhpm);
          for i in [1..dqhpm] do
            Append(~ngmatq,
              VQ!((hpm!(V!((qhpm.i) @@ hpmtoqhpm) * ngmat)) @ hpmtoqhpm) );
          end for;
          ngmatq := Matrix(ngmatq);
  
          perm := [];
          for comp in comps do
            longvec := [];
            for i in [1..#tails] do
              vec := tails[i] + TailVector(qhpm,comp,word[i])*ngmatq;
              longvec cat:= Eltseq(vec);
            end for;
            longvec := Vector(longvec);
            vec, longvec := DecomposeVector(CCS,longvec);
            //reconstruct image of complement from longvec
            imcomp := [];
            vec := qhpm!0;
            for j in [1..#tails] do
               for k in [1..dqhpm] do
                 vec[k] := longvec[(j-1)*dqhpm+k];
               end for;
               Append(~imcomp,vec);
            end for;
            pos := Position(comps,imcomp);
            if pos eq 0 then
               error "Image of complement under conjugation is not in list!";
            end if;
            Append(~perm, pos);
          end for; //for comp in comps do
          Append(~perms,perm);
        end for;  //for ngen in inpcgens cat inrqgens do
      end if; //if #comps eq 1 then

      //We want the stabiliser of the first comp - should be H itself
      npermgp := sub< Sym(#comps) | perms >;
      npcpermgp := sub< npermgp | [ npermgp.i : i in [1..#npcgens] ] >;
      if not posK in Orbit(npermgp,1) then
        return false,_;
      end if;
      stab := Stabiliser(npermgp,1);
      substab := Stabiliser(npcpermgp,1);
      vprint LMG,2: "  #npermgp:", #npermgp, "#npcpermgp:", #npcpermgp,
            "#stab:", #stab, "#substab:", #substab;
      stabgens := [ substab.i : i in [1..Ngens(substab)] ];
      //the generators of H should be in stab.
      stabgens cat:= [ npermgp.i : i in [#inpcgens+1 .. #inpcgens+#orighg] ];
      assert forall{x : x in stabgens | 1^x eq 1};
      
      //minimise generators of stab, starting with substab, followed by
      //generators in H
      newstab := sub< stab | stabgens >;
      while newstab ne stab do
        repeat g := Random(stab); until not g in newstab;
        Append(~stabgens, g);
        newstab := sub< stab | substab, stabgens >;
      end while;
      stab := newstab;
      iwmnpg := InverseWordMap(npermgp);
  
      //now we can put together the new generators of N at this level
      //start with pc generators in H - getting them into H is contorted!
      newnpcgens := [ (m!Eltseq(hpm!shpm.i)) @@ ptom @ pctoqpc @@ pctoqpch
                                           : i in [1..Dimension(hmeetm)] ];

      //now other generators from the module
      fqhpm := Fix(qhpm);
      newnpcgens cat:= [ (m!(Eltseq(fqhpm.i @@ hpmtoqhpm))) @@ ptom :
                             i in [1..Dimension(fqhpm)] ];

      //to recognise conjugating elements from qhpm, we'll need matrix
      //of actions of basis vector
      modconjmat := HorizontalJoin([idm - am : am in ActionGenerators(qhpm)])
                    where idm := IdentityMatrix(GF(p), dqhpm);
      ModConjElt := function(tails)
        //this calculates said conjugating element from qhpm
        local longvec, sol;
        longvec := Vector( &cat[ Eltseq(t) : t in tails ] );
        sol := Solution(modconjmat, longvec);
        return (m!Eltseq((qhpm!sol) @@ hpmtoqhpm)) @@ ptom;
      end function;

      //remaining generators from rad
      if lev lt #cs-1 then
        imnpctonpcpermgp := hom< imnpc -> npcpermgp |
                 [ <npcgens[i]@pctoqpc1, npermgp.i> : i in [1..#npcgens] ] >;
        npcstab := substab @@ imnpctonpcpermgp @@ pctoqpc1;  
        //now adjust by elements from modulepc
        npcstabg := [ npcstab.i : i in [1..NPCgens(npcstab)] ];
        for i in [1..NPCgens(npcstab)] do 
          _,tails := GetWordsAndTails(npcstab.i @@ rtopc : imngen:=Id(rq) );
          npcstabg[i] *:= ModConjElt(tails)^-1;
        end for;
        newnpcgens cat:= npcstabg;
      end if;

      //finally the generators from outside of rad and H
      newinrqgens :=  orighg;
      nrqgens := imhg;
      newimn := sub< rq | nrqgens >;
      //we need generators of kernel of imn onto the perm group on comps
      //need to get induced action of imn on orbits of npcpermgp
      oa := OrbitAction(npermgp,1);
      bi := BlocksImage( Image(oa), { oa(x) : x in Orbit(npcpermgp,1) } );
      imna := hom< imn -> bi | [ bi.(#inpcgens+i) : i in [1..Ngens(imn)]] >;
      for g in Generators(Kernel(imna)) do if not g in newimn then
        Append(~nrqgens, g);
        newimn := sub< rq | nrqgens >;
        wd := iwmimn(g);
        ig := Evaluate(wd, inrqgens);
        if lev lt #cs-1 then
          gperm :=
                Evaluate(wd, [npermgp.(#inpcgens+i) : i in [1..Ngens(imn)]] ); 
          isc, x := IsConjugate(npcpermgp, 1^gperm, 1); assert isc;
          ig *:= (x  @@ imnpctonpcpermgp @@ pctoqpc1 @@ rtopc);
        end if;
        _,tails := GetWordsAndTails(ig : imngen:=g );
        ig *:= (ModConjElt(tails)^-1) @@ rtopc;
        Append(~newinrqgens, ig);
      end if; end for; 

      //and also inverse images of generators of stabiliser in perm gp
      for i in [Ngens(substab)+#orighg+1 .. #stabgens] do
	g := Evaluate(iwmnpg(stabgens[i]), inpcgens cat inrqgens);
        img := g@Gtorq;
        if not img in newimn then
          Append(~nrqgens, img); 
          _,tails := GetWordsAndTails(g : imngen:=img );
          g *:= (ModConjElt(tails)^-1) @@ rtopc;
          Append(~newinrqgens, g);
        end if;
      end for;

      //conjugate K
      isc, x := IsConjugate( npermgp, 1, posK ); assert isc;
      x := Evaluate(iwmnpg(x), inpcgens cat inrqgens);
      vprint LMG,2: "  Adjusting conjugating element 3";
      ans *:= x^-1; K := K^(x^-1);
      kmr := kmr^(x^-1);
      kmrpcg := [ kmr.i @ rtopc : i in [1..Ngens(kmr)] ];
      kmrpc := sub< rpc | kmrpcg >;
      kmrpctokmr :=
             hom< kmrpc->rad | [ <kmrpcg[i],kmr.i> : i in [1..#kmrpcg] ] >;

      //have to identify complement yet again!
      kg := [ K.i : i in [1..Ngens(K)] ];
      imk := sub< rq | [k @ Gtorq : k in kg] >;
      iwmimk := InverseWordMap(imk);
      kg := [ Generic(G) | Evaluate( iwmimk(imhg[i]), kg) : i in [1..#imhg] ];
      tails := [ (hg[i]^-1 * kg[i]) @ rtopc : i in [1..#imhg] ];
      if lev lt #cs-1 then
        //adjust by elements in PC-group
        pctoqpck1 := hom< kmrpc -> qpc1 |
                              [pctoqpc1(kmrpc.i) : i in [1..NPCgens(kmrpc)]] >;
        tails := [ t * ((t^-1) @ pctoqpc1 @@ pctoqpck1) : t in tails ];
        tails cat:= 
                    [ (t^-1) * (t @ pctoqpc1 @@ pctoqpck1) : t in imhpcg ];
      end if;
      tails := [ (hpm!Eltseq(t @ ptom)) @ hpmtoqhpm : t in tails ];
      xpc := ModConjElt(tails);
      x := xpc @@ rtopc;
      vprint LMG,2: "  Adjusting conjugating element 4";
      ans *:= x^-1; K := K^(x^-1);
      kmr := kmr^(x^-1);
      kmrpcg := [ kmrpcg[i] ^ (xpc^-1) : i in [1..#kmrpcg] ];
      kmrpc := sub< rpc | kmrpcg >;
      kmrpctokmr := hom< kmrpc->rad |
                             [ <kmrpcg[i],kmr.i> : i in [1..#kmrpcg] ] >;
//reset things
      npcgens := newnpcgens;
      inpcgens := [ Generic(G) | x @@ rtopc : x in npcgens ];
      imnpc := pctoqpc( sub< rpc | npcgens > ); 

      inrqgens := newinrqgens;
      imn := sub< rq | nrqgens >;
      vprint LMG,1: "Order of image of normaliser in radical quotient is now",
                    #imn;
      vprint LMG,1: "Order of normaliser at this layer in radical is",
                    #imnpc;
    else  //i.e. if Dimension(hmeetm) eq Dimension(m) then
      //set up m, hmeetm and m/hmeetm as module for hpres
      //imhmats := [ gmacts[lev](hg[i]:im:=imhg[i]) : i in [1..#imhg] ]; 
      imhmats := [ gmacts[lev](hg[i]) : i in [1..#imhg] ]; 
      hpm := GModule(hpres,imhmats cat [rep(imhpcg[i]): i in [1..#imhpcg]]);
      shpm := sub< hpm | [Eltseq(m!hmeetm.i) : i in [1..Ngens(hmeetm)]]>;
      qhpm, hpmtoqhpm := quo< hpm | shpm >; 
      qpcmm := pctoqpch(hmm);
      npcgens := [ qpcmm.i @@ pctoqpc : i in [1..Ngens(qpcmm)] ] cat npcgens;
      inpcgens := [ npcgens[i] @@ rtopc : i in [1..Ngens(qpcmm)] ] cat inpcgens;
      imnpc := pctoqpc( sub< rpc | npcgens > ); 
    end if;

    //deal with extending H and hpres through layer -
    //only really need do this for lev gt 1
    if lev gt 1 then
      rels := Relations(hpres);
      RV := [];
      for rel in rels do
        w := LHS(rel)*RHS(rel)^-1;
        Append(~RV, shpm!hpm!Eltseq(m!(w @ hptoh @ rtopc @ ptom)));
      end for;
      hpres := ModuleExtension(shpm, RV);
      //need to get inverse images of hmeetm in H, which seems cumbersome!
      newhpcg := [ (m!Eltseq(hpm!shpm.i)) @@ ptom @ pctoqpc @@ pctoqpch
                                             : i in [1..Ngens(shpm)] ];
      imhpcg cat:= newhpcg;
      //also need various homomorphisms to the new hpres
      imhpc := pctoqpc( sub< rpc | imhpcg > ); 
      hg cat:= [ h @ hmrpctohmr : h in newhpcg ];
      imhpctohp := hom< imhpc->hpres |
          [ < imhpcg[i]@pctoqpc, hpres.(i+ #imhg) > : i in [1..#imhpcg]] >;
      hptoh := hom< hpres->Generic(G) | hg >;
      imhptohp := hom< imhpres->hpres | [hpres.i : i in [1..Ngens(imhpres)]] >;
  
      qpc1 := qpc;
      pctoqpc1 := pctoqpc;
    end if;
  end for; //for lev in [#cs-1..1 by -1] do

  return true, ans;
end function;
