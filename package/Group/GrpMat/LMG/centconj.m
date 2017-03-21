freeze;

FindConjugatingElement := function(matgp,ss1,ss2)
   //find g in matrix group matgp that maps ss1 to ss2
   //hopefully temporary fix - there is no Magma function to do this
   local orb, sv, ono, ng, ss, im, elt, next;
   if ss1 eq ss2 then return Id(matgp); end if;
   orb := {@ ss1 @};
   sv := [-1];
   ono := 1;
   ng := Ngens(matgp);
   while ono le #orb do
     ss := orb[ono];
     for i in [1..ng] do
       im := ss^(matgp.i);
       if im eq ss2 then
         elt := (matgp.i)^-1;
         next := sv[ono];
         while next ne -1 do
           elt *:= (matgp.next)^-1;
           ss := ss^((matgp.next)^-1);
           next := sv[Position(orb,ss)];
         end while;
         assert ss2^elt eq ss1;
         return elt^-1;
       elif not im in orb then
         Include(~orb,im);
         Append(~sv,i);
       end if;
     end for;
     ono +:= 1;
   end while;
   error "ss2 is not in the orbit of ss1";
end function;

ReduceGenerators := procedure(~G)
  //this deliberately does not change the first generator
  if Ngens(G) gt 1 then
    gens := [G.1]; subG := sub< G | gens >;
    while subG ne G do
      max := #subG;
      for i in [1..50] do //try and generate with one extra element
        x := Random(G);
        nsubG := sub< G | gens cat [x] >;
        if nsubG eq G then
          G := sub< G | gens cat [x] >; return;
        end if;
        if #nsubG gt max then max := #nsubG; bestx := x; end if;
      end for;
      //didn't work so just use any new element
      if max gt #subG then
        Append(~gens,bestx); subG := sub< G | gens >; 
      else
        repeat x := Random(G); until not x in subG;
        Append(~gens,x); subG := sub< G | gens >; 
      end if;
    end while;
  else return;
  end if;
  G := subG;
end procedure;

PCOSG := function(G, f, pt)
/* Polycyclic orbit-stabiliser calcualtion.
 * f is a group-action function S x G -> S, with G of type GrpPC, and pt in S.
 * Return orbit of pt, stabiliser of pt as subgroup of G, and
 * generator numbers in G that were used to build up orbit.
 */
  local ng,ords,orb,stabgens,orbnos,im,posmg,lo,pow,g,h;
  ng := NPCgens(G);
  ords := PCPrimes(G);
  orb := {@ pt @};
  stabgens := [G|];
  orbnos := [];
  for i in [ng .. 1 by -1] do
    im := f(<pt , G.i>);
    pos := Position(orb,im);
    if pos eq 0 then
      orb join:= {@ f(<o, G.i^k>) : o in orb, k in [1..ords[i]-1] @};
      Append(~orbnos,i);
    else
      g := G.i;
      lo := #orb;
      for t in Reverse(orbnos) do
        if pos eq 1 then break; end if;
        lo := lo div ords[t];
        pow := (pos-1) div lo;
        h := G.t^-pow;
        g *:= h;
        im := f(< im, h >);
        pos := Position(orb,im);
      end for;
      assert f(<pt,g>) eq pt;
      Append(~stabgens, g);
    end if;
  end for;
  return orb, sub< G | stabgens>, orbnos;
end function;

PCActGIsCon := function(G,f,orb,orbnos,impt) 
//orb, orbnos should be as returned by PCOSG on (G,f,pt)
//Determine if impt is in orb, and if so return conjugating element in G
local ng, g, lo, pos, pow, h;
      pos := Position(orb,impt);
      if pos eq 0 then return false,_; end if;
      ng := NPCgens(G);
      g := Id(G);
      lo := #orb;
      ords := PCPrimes(G);
      for t in Reverse(orbnos) do
        if pos eq 1 then break; end if;
        lo := lo div ords[t];
        pow := (pos-1) div lo;
        h := G.t^-pow;
        g *:= h;
        impt := f(<impt, h>);
        pos := Position(orb,impt);
      end for;
      assert pos eq 1;
      return true, g^-1;
end function;

EltCent := function(G,g:so:=256,N:=0,layers:={})
//N should be a normal subgroup of the radical quotient of G such that the
//inverse image of N in G acts decomposably on the modules of the soluble
//radical in the layer numbers (counting from bottom upwards) in layers 
  local r,rpc,rad,rtopc,rq,Gtorq,rm,gmacts,img,imc,cgens,x,cpc,icgens,cs,m,
     ptom,rep,p,d,qpc,pctoqpc,cqpc,cmats,col,pg,ig,mat,V,fact,rado,radst,
     radonos,igenmats,lo,fullgp,subgp,oa,oi,suborbs,ba,bi,rqact,rqst,fullo,
     deg,pt,perms,vec,imvec,pos,gorbim,stg,istg,ords,iwmimc,slp,smat,pow,y,
        ngn,nigensm,nactgens,Nact,Nmod,ISNmod,dns,nisNMod,cbmat,newlist,
        imcN,icgensN,igenmatsN,igenmatsG,Pact,DigenmatsN,orbrep,
        Dcmats,DNact,DPact,cqpctoDPact,iNactgens,radNag,listN,orbslists,olist,
        uct,prev,vecs,act,scol,Realact,f,actgp,Pactgp,nvec,nNorbs,Gorbs,Gact,
        rqtoGact,mvec,newg,irepV,irep,DNstab,DPstab,newNgens,iwmN,imcgens,
        stab,ggen,ggenact,ix, ovec,ovecc1, ovecc2;
  r := G`LMGNode;
  rpc := r`radPC;
  rad := r`rad;
  rtopc := r`radtoPC;
  rq := r`radquot;
  Gtorq := r`Gtoradquot;
  rm := r`radmods;
  //gmacts := r`rqradmodactions;
  gmacts := r`radmodactions;

  img := Gtorq(g);
  imc := Centraliser( rq, img );
  //try to minimise generators
  cgens := [img];
  while sub< imc | cgens > ne imc do
    repeat x:=Random(imc); until not x in sub< imc | cgens >;
    Append(~cgens,x);
  end while;
  imc := sub< imc | cgens >;
  //centraliser will be stored as intersection of centraliser in rpc
  //with extra gens outside of radical
  cpc := sub< rpc | >;
  icgens := [g] cat [cgens[i] @@ Gtorq : i in [2..#cgens]];
  cs := r`cseriesrad;

  for k in [#cs-1..1 by -1] do
    m := rm[k][1];
    ptom := rm[k][2];
    rep := rm[k][3];
    p := #BaseRing(m); d := Dimension(m);
    vprint LMG,1: "Lifting through layer",k,"of size",p,"^",d;

    if k in layers then
//set up some matrices for action of inverse image of N on this layer module
//find the summands of the module uner N, and corresponding basis change matrix
      ngn := Ngens(N);
      ingens := [ N.i @@ Gtorq : i in [1..ngn] ];
      //nactgens := [ gmacts[k](ingens[i] : im:=N.i) : i in [1..ngn] ];
      nactgens := [ gmacts[k](ingens[i] ) : i in [1..ngn] ];
      Nact := sub< GL(d,p) |
             [rep(g) : g in Generators(rpc)] cat nactgens >;
      Nmod := GModule(Nact);
      ISNmod := IndecomposableSummands(Nmod);
      dns := Dimension(ISNmod[1]);
      nISNmod := #ISNmod;
      assert forall{s : s in ISNmod | Dimension(s) eq dns};
      cbmat := Matrix( &cat[ [Morphism(s,Nmod)(s.i) : i in [1..Dimension(s)]] :
                              s in ISNmod ] );
      if nISNmod eq 1 then //no point in using N-action
        vprint LMG,1: "  ","removing",k,"from N-action layers";
        Exclude(~layers,k);
      end if;
    end if; //if k in layers

    //get action of generators of imc on layer
    //start with action of rpc
    qpc, pctoqpc := quo< rpc | cs[k] >;
    cqpc := sub< qpc | pctoqpc(cs[k+1]), pctoqpc(cpc) >;
    if k in layers then
        vprint LMG,1: "  ",
            "Calculating affine action of inverse image of N on layer";
        imcN := imc meet N;
        //minimise generators
        ReduceGenerators(~imcN);

        icgensN := [];
        iwmimc := InverseWordMap(imc);
        for l in [1..Ngens(imcN)] do
          slp := iwmimc(imcN.l);
          smat := Evaluate(slp, icgens);
          Append(~icgensN,smat);
        end for;
        //set up matrices for action in new basis
        col := Matrix(GF(p),d+1,1,[0: i in [1..d]] cat [1]);
        cmats := [];
        for i in [1..NPCgens(cqpc)] do
           pg := cqpc.i @@ pctoqpc; ig := pg @@ rtopc;
           mat := HorizontalJoin(
               VerticalJoin( cbmat*rep(pg)*cbmat^-1,
                             Matrix((g,ig) @ rtopc @ ptom)*cbmat^-1 ),
                             col );
           Append(~cmats,  mat);
        end for;
        igenmatsN := [ GL(d+1,p) | HorizontalJoin(
              //VerticalJoin( cbmat*gmacts[k](icgensN[i]:im:=imcN.i)*cbmat^-1,
              VerticalJoin( cbmat*gmacts[k](icgensN[i])*cbmat^-1,
                            Matrix((g,icgensN[i]) @ rtopc @ ptom)*cbmat^-1 ),
                            col ):
                          i in [1..#icgensN] ];
        igenmatsG := [ GL(d+1,p) | HorizontalJoin(
              //VerticalJoin( cbmat*gmacts[k](icgens[i]:im:=imc.i)*cbmat^-1,
              VerticalJoin( cbmat*gmacts[k](icgens[i])*cbmat^-1,
                            Matrix((g,icgens[i]) @ rtopc @ ptom)*cbmat^-1 ),
                            col ):
                          i in [1..#icgens] ];
        Nact := sub< GL(d+1,p) | cmats cat igenmatsN >;
        Pact := sub< GL(d+1,p) | cmats >;
//BSGS calculations are much easier in the dual of Nact, because shorter bases
//typically exist. So we complicate matters by computing this dual and using
//it for all BSGS calcualtions.
        DigenmatsN := [ Transpose(x)^-1 : x in igenmatsN ]; 
        Dcmats := [ Transpose(x)^-1 : x in cmats ]; 
        DNact := sub< GL(d+1,p) | Dcmats cat DigenmatsN >;
        DPact := sub< GL(d+1,p) | Dcmats >;
        cqpctoDPact := hom< cqpc-> DPact | Dcmats >;
        //we need to find generators of G mapping onto the generators of DNact.
        iNactgens := [Generic(G)|];
        for gen in [DNact.i : i in [1..Ngens(DNact)]] do
          pos := Position(Dcmats,gen);
          if pos ne 0 then
            Append(~iNactgens, cqpc.pos @@ pctoqpc @@ rtopc);
          else pos := Position(DigenmatsN,gen);
            Append(~iNactgens, icgensN[pos] );
          end if;
        end for;

        radNag := [ x @ Gtorq : x in iNactgens ]; 
        
        /* Find DNact-orbits DNact- and DPact-stabilisers, working down
         * through the summands.
         * For summand number i, each element of listN[i] is a triple u.
         * u[1] is the list of orbit reps down to level i, represented
         * as a list of i vectors of length dNS. u[2] and u[3] are the
         * stabilisers of this orbit rep in DNact and in DPact, respectively.
         *
         * orbslists[i] contain one triple t for each representative vec in 
         * listN[i-1]. t[1] is the action homomorphism from the stabiliser
         * in DNact of vec to the action on the current N-summand
         * t[2] is the list of (relevant) orbits of that action,
         * and t[3] just marks the position in listN[i] where 
         * these orbit reps and stabilisers start. 
         */
        listN := [];
        orbslists := [];
        V := VectorSpace(GF(p),d+1);
        ovec := VectorSpace(GF(p),d)!0;
        ovecc1 := [ VectorSpace(GF(p),dns)!0 : sno in [1..nISNmod] ];
        //we want to choose ovec as the representative of its orbit, so
        //extract its components. 
        V := VectorSpace(GF(p),dns+1);
        ovecc2 := p eq 2 select
                 [ V.(dns+1) : sno in [1..nISNmod] ]
            else [ sub< V | V.(dns+1) > : sno in [1..nISNmod] ];
        
        iwmN := InverseWordMap(DNact);
        for sno in [1..nISNmod] do
          vprint LMG,2: "  ","N summand no",sno;
          olist := [];
          uct := 0;
          prev := sno eq 1 select [< [], DNact, DPact > ] else listN[sno-1];
          lN := []; //stabilisers
          for u in prev do
            uct+:=1; vprint LMG,2:"  Rep number",uct;
            //get action of generators of current subgroup of DNact on layer
            vecs := u[1]; act := u[2]; Pact := u[3];
            scol := Matrix(GF(p),dns+1,1,[0: i in [1..dns]] cat [1]);
            Realact := [ Transpose(act.i)^-1 : i in [1..Ngens(act)] ];
            f := hom< act -> GL(dns+1,p) |
                  [ HorizontalJoin(
              VerticalJoin(
                 ExtractBlock(Realact[i],(sno-1)*dns+1,(sno-1)*dns+1,dns,dns),
                           ExtractBlock(Realact[i],d+1,(sno-1)*dns+1,1,dns) ),
                    scol) : i in [1..#Realact] ] >;
            actgp := Image(f);
            Pactgp := f(Pact);
            if p eq 2 then
              orbs := Orbits(actgp);
                   //only want those with nontrivial dns+1 entry
              orbs := [ o: o in orbs | Rep(o)[dns+1] ne 0 ];
            else
              orbs := LineOrbits(actgp);
                   //only want those with nontrivial dns+1 entry
              orbs := [ o: o in orbs | (Rep(o).1)[dns+1] ne 0 ];
            end if;
            Append(~olist,< f, orbs, #lN >); //#lN to mark position in lN
            for orb in orbs do
              orbrep := ovecc2[sno] in orb select ovecc2[sno]
                        else orb[1];
              vec := p eq 2 select orbrep
                     else (vec/vec[dns+1] where vec := orbrep.1);
              vec := Vector(Prune(Eltseq(vec)));
              nvec := Append(vecs,vec);
              Append(~lN, <nvec,Stabiliser(actgp,orbrep) @@ f,
                               Stabiliser(Pactgp,orbrep) @@ f>);
            end for;
          end for;
          Append(~listN,lN);
          Append(~orbslists,olist);
          vprint LMG,2: #lN,"N orbreps";
        end for; //for sno in [1..#ISNmod] do

        //Now work out action of G on orbit containing ovec.
        pos :=
         Position([listN[nISNmod][i][1] : i in [1..#listN[nISNmod]]], ovecc1);
        nNorbs := #listN[nISNmod];
        perms := [ [] : j in [1..#igenmatsG] ];
        orb := {@ pos @}; i:=1;
        while i le #orb do
          vec := HorizontalJoin(
              HorizontalJoin(listN[nISNmod][orb[i]][1]), Vector(GF(p),[1]) );
          for j in [1..#igenmatsG] do
            gen := igenmatsG[j];
            //get action of generator of G on orb[i];
            im := vec * gen;
            //need to locate orbit of im by working through orbits of N
            pos := 1;
            for sno in [1..nISNmod] do
              scol := Matrix(GF(p),dns+1,1,[0: i in [1..dns]] cat [1]);
              f := orbslists[sno][pos][1];
              act := Domain(f);
              actim := Image(f);
              V := VectorSpace(actim);
              imsno := V!HorizontalJoin(ExtractBlock(im,1,(sno-1)*dns+1,1,dns),
                         Vector(GF(p),[1]) );
              if p gt 2 then
                imsno := sub< V | imsno >;
              end if;
              orbs := orbslists[sno][pos][2];
              orbno := 0;
              for j in [1..#orbs] do
                if imsno in orbs[j] then
                  orbno:=j;
                  x := FindConjugatingElement(actim, imsno, orbs[j][1]);
                  im := im * Transpose(x @@ f)^-1;
                  break;
                end if;
              end for;
              assert orbno gt 0;
              pos := orbslists[sno][pos][3] + orbno;
            end for;
            if not pos in orb then Include(~orb, pos); end if;
            perms[j][i] := Position(orb,pos);
          end for; //for j in [1..#igenmatsG] do
          i +:= 1;
        end while; //while i le #orb

        Gact := sub< Sym(#orb) | perms >;
        rqtoGact := hom< imc -> Gact | perms >;
        //Need stabiliser of orb[1];
          orbrep := orb[1];
          //find group element
          vec := HorizontalJoin(listN[nISNmod][orbrep][1]);

          //first get stabiliser in DNact, DPact which is stored, and compute
          //inverse images in G
          irepV := VectorSpace(Nact)!HorizontalJoin( vec, Vector(GF(p),[1]) );
          irep := p eq 2 select irepV else sub< Parent(irepV) | irepV >; 
          DNstab := listN[nISNmod][orbrep][2];
          DPstab := listN[nISNmod][orbrep][3];
          ncpc := DPstab @@ cqpctoDPact @@ pctoqpc;
          
          //now add as few generators of Nstab as possible
          newNgens := [];
          while sub< DNstab | DPstab, newNgens > ne DNstab do
            repeat
              x:=Random(DNstab);
            until not x in sub< DNstab | DPstab, newNgens >;
            Append(~newNgens,x);
          end while;
          imcgens := [g@Gtorq]; istg := [Generic(G)|g];
          for gen in newNgens do
            slp := iwmN(gen);
            Append(~istg, Evaluate(slp, iNactgens) );
            Append(~imcgens, Evaluate(slp, radNag) );
          end for;

          //finally get stabiliser in G
          stab := Stabiliser(Gact,orbrep) @@ rqtoGact;
          ReduceGenerators(~stab);
          for gen in Generators(stab) do
            slp := iwmimc(gen);
            ggen := Evaluate(slp, icgens);
            ggenact :=  HorizontalJoin(
              VerticalJoin( cbmat*gmacts[k](ggen)*cbmat^-1,
                            Matrix((g,ggen) @ rtopc @ ptom)*cbmat^-1 ),
                            col );
            im := Vector(irepV * ggenact);
            //must find element in inverse image of N to bring im back to irep
            pos := 1;
            vec := [];
            for sno in [1..nISNmod] do
              scol := Matrix(GF(p),dns+1,1,[0: i in [1..dns]] cat [1]);
              f := orbslists[sno][pos][1];
              act := Domain(f);
              actim := Image(f);
              V := VectorSpace(actim);
              imsno := V!HorizontalJoin(ExtractBlock(im,1,(sno-1)*dns+1,1,dns),
                         Vector(GF(p),[1]) );
              if p gt 2 then imsno := sub< V | imsno >; end if;
              orbs := orbslists[sno][pos][2];
              orbno := 0;
              for j in [1..#orbs] do
                if imsno in orbs[j] then
                  orbno:=j;
                  x := FindConjugatingElement(actim, imsno, orbs[j][1]);
                  ix := x @@ f;
                  im := im * Transpose(ix)^-1;
                  slp := iwmN(ix);
                  ggen *:= Evaluate(slp, iNactgens);
                  break;
                end if;
              end for;
              assert orbno gt 0;
              pos := orbslists[sno][pos][3] + orbno;
            end for;
            Append(~istg, ggen);
            Append(~imcgens, ggen@Gtorq);
          end for; //for gen in Generators(stab) do
          cpc := ncpc;
          imc := sub<rq|imcgens>;
          icgens := istg;
    else //k in layers
      cmats := [];
      col := Matrix(GF(p),d+1,1,[0: i in [1..d]] cat [1]);
      for i in [1..NPCgens(cqpc)] do
        pg := cqpc.i @@ pctoqpc; ig := pg @@ rtopc;
        mat := HorizontalJoin(
           VerticalJoin( rep(pg), Matrix((g,ig) @ rtopc @ ptom)), col );
        Append(~cmats,  mat);
      end for;
      cqpcact := hom< cqpc->GL(d+1,p) | cmats >;
      V := VectorSpace(GF(p),d+1);
      fact := func<  t | t[1] * cqpcact(t[2]) >;
      rado,radst,radonos := PCOSG(cqpc,fact,V.(d+1));
      vprint LMG,2: "  #rado:",#rado,"#radst",#radst;
  
      //now action of imc on orbits
      igenmats := [ GL(d+1,p) | HorizontalJoin(
           //VerticalJoin( gmacts[k](icgens[i]:im:=imc.i),
           VerticalJoin( gmacts[k](icgens[i]),
                           Matrix((g,icgens[i]) @ rtopc @ ptom)), col ):
                               i in [1..#icgens] ];
      //need two strategies for action of rq
      lo := #rado;
      if lo le so then
        vprint LMG,2: "  small orbit calculation";
        fullgp := sub< GL(d+1,p) | cmats cat igenmats >;
        subgp := sub< GL(d+1,p) | cmats >;
	dummy := LMGOrder(fullgp);
        oa, oi := OrbitAction(fullgp,V.(d+1));
        suborbs := Orbits(oa(subgp));
        ba, bi := BlocksAction(oi,suborbs[1]);
        rqact := hom< imc->bi | [igenmats[i] @ oa @ ba : i in [1..#icgens]] >;
        rqst := Stabiliser(bi,1) @@ rqact;
        vprint LMG,2: "  degree oi:",Degree(oi),"#rqst",#rqst;
      else
        vprint LMG,2: "  non-small orbit calculation";
        fullo := rado; deg := 1;
        perms := [ [] : i in [1..#igenmats] ];
        pt := 1;
        while pt le deg do
          vec := fullo[(pt-1)*lo+1];
          for i in [1..#igenmats] do
            imvec := vec*igenmats[i];
            pos := Position(fullo,imvec);
            if pos eq 0 then //new orbit
              fullo join:=  PCOSG(cqpc,fact,imvec);
              deg +:= 1;
              perms[i][pt] := deg;
            else perms[i][pt] := (pos-1) div lo + 1;
            end if;
          end for;
          pt +:= 1;
        end while;
        ChangeUniverse(~perms, Sym(deg));
        gorbim := sub< Sym(deg) | perms >;
        rqact := hom< imc->gorbim | perms >;
        rqst := Stabiliser(gorbim,1) @@ rqact;
        vprint LMG,2: "  #fullo:",#fullo,"#rqst",#rqst;
      end if;
      assert  imc.1 in rqst;
      //try to minimise generators
      stg := [imc.1];
      while sub< rqst | stg > ne rqst do
        repeat x:=Random(rqst); until not x in sub< rqst | stg >;
        Append(~stg,x);
      end while;
      rqst := sub< rqst | stg >;
      istg := [Generic(G)|g];
      iwmimc := InverseWordMap(imc);
      for l in [2..#stg] do
        slp := iwmimc(stg[l]);
        smat := Evaluate(slp, igenmats);
        vec := V.(d+1) * smat;
        isc,x := PCActGIsCon(cqpc,fact,rado,radonos,vec); assert isc;
        istg[l] := Evaluate(slp,icgens) * ((x^-1) @@ pctoqpc @@ rtopc);
      end for;
      cpc := sub< rpc | [ radst.i @@ pctoqpc : i in [1..NPCgens(radst)] ] >;
      icgens := istg;
      imc := rqst;
    end if; //if k in layers
  end for; //for k in [#cs-1..1 by -1] 
  return sub<Generic(G) | [cpc.i @@ rtopc : i in [1..Ngens(cpc)]] cat icgens >;
end function;

IsConj := function(G,g,h:so:=256,N:=0,layers:={})
//N should be a normal subgroup of the radical quotient of G such that the
//inverse image of N in G acts decomposably on the modules of the soluble
//radical in the layer numbers (counting from bottom upwards) in layers 
  local r,rpc,rad,rtopc,rq,Gtorq,rm,gmacts,img,imc,cgens,x,cpc,icgens,cs,m,
     ptom,rep,p,d,qpc,pctoqpc,cqpc,cmats,col,pg,ig,mat,V,fact,rado,radst,
     radonos,igenmats,lo,fullgp,subgp,oa,oi,suborbs,ba,bi,rqact,rqst,fullo,
     deg,pt,perms,vec,imvec,pos,gorbim,stg,istg,ords,iwmimc,slp,smat,pow,y,
     ans,imh,orb,convec,convecpos,isc,
        ngn,nigensm,nactgens,Nact,Nmod,ISNmod,dns,nisNMod,cbmat,newlist,
        imcN,icgensN,igenmatsN,igenmatsG,Pact,DigenmatsN,orbrep,
        Dcmats,DNact,DPact,cqpctoDPact,iNactgens,radNag,listN,orbslists,olist,
        uct,prev,vecs,act,scol,Realact,f,actgp,Pactgp,nvec,nNorbs,Gorbs,Gact,
        rqtoGact,mvec,newg,irepV,irep,DNstab,DPstab,newNgens,iwmN,imcgens,
        stab,ggen,ggenact,ix, ovec,ovecc1, ovecc2, iwmGact,origg;
  origg := g; //just to check answer returned is correct
  r := G`LMGNode;
  rpc := r`radPC;
  rad := r`rad;
  rtopc := r`radtoPC;
  rq := r`radquot;
  Gtorq := r`Gtoradquot;
  img := Gtorq(g); imh := Gtorq(h);
  isc, x := IsConjugate( rq, img, imh);
  if not isc then return false, _; end if;
  vprint LMG,2: "  Initialising conjugating element";
  ans := x @@ Gtorq;  g := g^ans;

  rm := r`radmods;
  //gmacts := r`rqradmodactions;
  gmacts := r`radmodactions;

  imc := Centraliser( rq, imh );
  //try to minimise generators
  cgens := [imh];
  while sub< imc | cgens > ne imc do
    repeat x:=Random(imc); until not x in sub< imc | cgens >;
    Append(~cgens,x);
  end while;
  imc := sub< imc | cgens >;
  //centraliser will be stored as intersection of centraliser in rpc
  //with extra gens outside of radical
  cpc := sub< rpc | >;
  icgens := [g] cat [cgens[i] @@ Gtorq : i in [2..#cgens]];
  cs := r`cseriesrad;

  for k in [#cs-1..1 by -1] do
    m := rm[k][1];
    ptom := rm[k][2];
    rep := rm[k][3];
    p := #BaseRing(m); d := Dimension(m);
    vprint LMG,1: "Lifting through layer",k,"of size",p,"^",d;

    if k in layers then
//set up some matrices for action of inverse image of N on this layer module
//find the summands of the module uner N, and corresponding basis change matrix
      ngn := Ngens(N);
      ingens := [ N.i @@ Gtorq : i in [1..ngn] ];
      //nactgens := [ gmacts[k](ingens[i] : im:=N.i) : i in [1..ngn] ];
      nactgens := [ gmacts[k](ingens[i]) : i in [1..ngn] ];
      Nact := sub< GL(d,p) |
             [rep(g) : g in Generators(rpc)] cat nactgens >;
      Nmod := GModule(Nact);
      ISNmod := IndecomposableSummands(Nmod);
      dns := Dimension(ISNmod[1]);
      nISNmod := #ISNmod;
      assert forall{s : s in ISNmod | Dimension(s) eq dns};
      cbmat := Matrix( &cat[ [Morphism(s,Nmod)(s.i) : i in [1..Dimension(s)]] :
                              s in ISNmod ] );
      if nISNmod eq 1 then //no point in using N-action
        vprint LMG,1: "  ","removing",k,"from N-action layers";
        Exclude(~layers,k);
      end if;
    end if; //if k in layers

    //get action of generators of imc on layer
    qpc, pctoqpc := quo< rpc | cs[k] >;
    cqpc := sub< qpc | pctoqpc(cs[k+1]), pctoqpc(cpc) >;
    //this must be in the orbit if g,h are conjugate 
  
    if k in layers then
        vprint LMG,1: "  ",
            "Calculating affine action of inverse image of N on layer";
        imcN := imc meet N;
        //minimise generators
        ReduceGenerators(~imcN);

        icgensN := [];
        iwmimc := InverseWordMap(imc);
        for l in [1..Ngens(imcN)] do
          slp := iwmimc(imcN.l);
          smat := Evaluate(slp, icgens);
          Append(~icgensN,smat);
        end for;
        //set up matrices for action in new basis
        col := Matrix(GF(p),d+1,1,[0: i in [1..d]] cat [1]);
        cmats := [];
        for i in [1..NPCgens(cqpc)] do
           pg := cqpc.i @@ pctoqpc; ig := pg @@ rtopc;
           mat := HorizontalJoin(
               VerticalJoin( cbmat*rep(pg)*cbmat^-1,
                             Matrix((h,ig) @ rtopc @ ptom)*cbmat^-1 ),
                             col );
           Append(~cmats,  mat);
        end for;
        igenmatsN := [ GL(d+1,p) | HorizontalJoin(
              //VerticalJoin( cbmat*gmacts[k](icgensN[i]:im:=imcN.i)*cbmat^-1,
              VerticalJoin( cbmat*gmacts[k](icgensN[i])*cbmat^-1,
                            Matrix((h,icgensN[i]) @ rtopc @ ptom)*cbmat^-1 ),
                            col ):
                          i in [1..#icgensN] ];
        igenmatsG := [ GL(d+1,p) | HorizontalJoin(
              //VerticalJoin( cbmat*gmacts[k](icgens[i]:im:=imc.i)*cbmat^-1,
              VerticalJoin( cbmat*gmacts[k](icgens[i])*cbmat^-1,
                            Matrix((h,icgens[i]) @ rtopc @ ptom)*cbmat^-1 ),
                            col ):
                          i in [1..#icgens] ];
        Nact := sub< GL(d+1,p) | cmats cat igenmatsN >;
        Pact := sub< GL(d+1,p) | cmats >;
//BSGS calculations are much easier in the dual of Nact, because shorter bases
//typically exist. So we complicate matters by computing this dual and using
//it for all BSGS calcualtions.
        DigenmatsN := [ Transpose(x)^-1 : x in igenmatsN ]; 
        Dcmats := [ Transpose(x)^-1 : x in cmats ]; 
        DNact := sub< GL(d+1,p) | Dcmats cat DigenmatsN >;
        DPact := sub< GL(d+1,p) | Dcmats >;
        cqpctoDPact := hom< cqpc-> DPact | Dcmats >;
        //we need to find generators of G mapping onto the generators of DNact.
        iNactgens := [Generic(G)|];
        for gen in [DNact.i : i in [1..Ngens(DNact)]] do
          pos := Position(Dcmats,gen);
          if pos ne 0 then
            Append(~iNactgens, cqpc.pos @@ pctoqpc @@ rtopc);
          else pos := Position(DigenmatsN,gen);
            Append(~iNactgens, icgensN[pos] );
          end if;
        end for;

        radNag := [ x @ Gtorq : x in iNactgens ]; 
        
        /* Find DNact-orbits DNact- and DPact-stabilisers, working down
         * through the summands.
         * For summand number i, each element of listN[i] is a triple u.
         * u[1] is the list of orbit reps down to level i, represented
         * as a list of i vectors of length dNS. u[2] and u[3] are the
         * stabilisers of this orbit rep in DNact and in DPact, respectively.
         *
         * orbslists[i] contain one triple t for each representative vec in 
         * listN[i-1]. t[1] is the action homomorphism from the stabiliser
         * in DNact of vec to the action on the current N-summand
         * t[2] is the list of (relevant) orbits of that action,
         * and t[3] just marks the position in listN[i] where 
         * these orbit reps and stabilisers start. 
         */
        listN := [];
        orbslists := [];
        V := VectorSpace(GF(p),d+1);
        ovec := VectorSpace(GF(p),d)!0;
        ovecc1 := [ VectorSpace(GF(p),dns)!0 : sno in [1..nISNmod] ];
        //we want to choose ovec as the representative of its orbit, so
        //extract its components. 
        V := VectorSpace(GF(p),dns+1);
        ovecc2 := p eq 2 select
                 [ V.(dns+1) : sno in [1..nISNmod] ]
            else [ sub< V | V.(dns+1) > : sno in [1..nISNmod] ];
        
        iwmN := InverseWordMap(DNact);
        for sno in [1..nISNmod] do
          vprint LMG,2: "  ","N summand no",sno;
          olist := [];
          uct := 0;
          prev := sno eq 1 select [< [], DNact, DPact > ] else listN[sno-1];
          lN := []; //stabilisers
          for u in prev do
            uct+:=1; vprint LMG,2:"  Rep number",uct;
            //get action of generators of current subgroup of DNact on layer
            vecs := u[1]; act := u[2]; Pact := u[3];
            scol := Matrix(GF(p),dns+1,1,[0: i in [1..dns]] cat [1]);
            Realact := [ Transpose(act.i)^-1 : i in [1..Ngens(act)] ];
            f := hom< act -> GL(dns+1,p) |
                  [ HorizontalJoin(
                VerticalJoin(
                   ExtractBlock(Realact[i],(sno-1)*dns+1,(sno-1)*dns+1,dns,dns),
                             ExtractBlock(Realact[i],d+1,(sno-1)*dns+1,1,dns) ),
                    scol) : i in [1..#Realact] ] >;
            actgp := Image(f);
            Pactgp := f(Pact);
            if p eq 2 then
              orbs := Orbits(actgp);
                   //only want those with nontrivial dns+1 entry
              orbs := [ o: o in orbs | Rep(o)[dns+1] ne 0 ];
            else
              orbs := LineOrbits(actgp);
                   //only want those with nontrivial dns+1 entry
              orbs := [ o: o in orbs | (Rep(o).1)[dns+1] ne 0 ];
            end if;
            Append(~olist,< f, orbs, #lN >); //#lN to mark position in lN
            for orb in orbs do
              orbrep := ovecc2[sno] in orb select ovecc2[sno]
                        else orb[1];
              vec := p eq 2 select orbrep
                     else (vec/vec[dns+1] where vec := orbrep.1);
              vec := Vector(Prune(Eltseq(vec)));
              nvec := Append(vecs,vec);
              Append(~lN, <nvec,Stabiliser(actgp,orbrep) @@ f,
                               Stabiliser(Pactgp,orbrep) @@ f>);
            end for;
          end for;
          Append(~listN,lN);
          Append(~orbslists,olist);
          vprint LMG,2: #lN,"N orbreps";
        end for; //for sno in [1..#ISNmod] do

        //Now work out action of G on orbit containing ovec.
        pos :=
         Position([listN[nISNmod][i][1] : i in [1..#listN[nISNmod]]], ovecc1);
        nNorbs := #listN[nISNmod];
        perms := [ [] : j in [1..#igenmatsG] ];
        orb := {@ pos @}; i:=1;
        while i le #orb do
          vec := HorizontalJoin(
              HorizontalJoin(listN[nISNmod][orb[i]][1]), Vector(GF(p),[1]) );
          for j in [1..#igenmatsG] do
            gen := igenmatsG[j];
            //get action of generator of G on orb[i];
            im := vec * gen;
            //need to locate orbit of im by working through orbits of N
            pos := 1;
            for sno in [1..nISNmod] do
              scol := Matrix(GF(p),dns+1,1,[0: i in [1..dns]] cat [1]);
              f := orbslists[sno][pos][1];
              act := Domain(f);
              actim := Image(f);
              V := VectorSpace(actim);
              imsno := V!HorizontalJoin(ExtractBlock(im,1,(sno-1)*dns+1,1,dns),
                         Vector(GF(p),[1]) );
              if p gt 2 then
                imsno := sub< V | imsno >;
              end if;
              orbs := orbslists[sno][pos][2];
              orbno := 0;
              for j in [1..#orbs] do
                if imsno in orbs[j] then
                  orbno:=j;
                  x := FindConjugatingElement(actim, imsno, orbs[j][1]);
                  im := im * Transpose(x @@ f)^-1;
                  break;
                end if;
              end for;
              assert orbno gt 0;
              pos := orbslists[sno][pos][3] + orbno;
            end for;
            if not pos in orb then Include(~orb, pos); end if;
            perms[j][i] := Position(orb,pos);
          end for; //for j in [1..#igenmatsG] do
          i +:= 1;
        end while; //while i le #orb

        //now we can test whether convec is in the orbit and find conjugating
        //element if so.
        //first put convec into new basis
        //now locate number of N-orbit containing convec.
        pos := 1;
        convec := ((h^-1*g) @ rtopc @ ptom) * cbmat^-1;
        convec := VectorSpace(GF(p),d+1)!(Eltseq(convec)  cat [1]);
        im := convec;
        for sno in [1..nISNmod] do
          scol := Matrix(GF(p),dns+1,1,[0: i in [1..dns]] cat [1]);
          f := orbslists[sno][pos][1];
          act := Domain(f);
          actim := Image(f);
          V := VectorSpace(actim);
          imsno := V!HorizontalJoin(ExtractBlock(im,1,(sno-1)*dns+1,1,dns),
                         Vector(GF(p),[1]) );
          if p gt 2 then
                imsno := sub< V | imsno >;
          end if;
          orbs := orbslists[sno][pos][2];
          orbno := 0;
          for j in [1..#orbs] do
            if imsno in orbs[j] then
              orbno:=j;
              x := FindConjugatingElement(actim, imsno, orbs[j][1]);
              im := im * Transpose(x @@ f)^-1;
              break;
            end if;
          end for;
          assert orbno gt 0;
          pos := orbslists[sno][pos][3] + orbno;
        end for;

        pos := Position(orb,pos);
        if pos eq 0 then return false, _; end if;
        Gact := sub< Sym(#orb) | perms >;
        isc,x := IsConjugate(Gact,pos,orb[1]); assert isc;
        iwmGact := InverseWordMap(Gact);
        slp := x@iwmGact;
        y := Evaluate(slp, icgens);
        g := g^y;
        ans *:= y;
        convec := ((h^-1*g) @ rtopc @ ptom) * cbmat^-1;
        convec := VectorSpace(GF(p),d+1)!(Eltseq(convec)  cat [1]);
        //This should be in orb[1] - conjugate it back to rep
        pos := 1;
        im := convec;
        y := Id(G);
        for sno in [1..nISNmod] do
          scol := Matrix(GF(p),dns+1,1,[0: i in [1..dns]] cat [1]);
          f := orbslists[sno][pos][1];
          act := Domain(f);
          actim := Image(f);
          V := VectorSpace(actim);
          imsno := V!HorizontalJoin(ExtractBlock(im,1,(sno-1)*dns+1,1,dns),
                         Vector(GF(p),[1]) );
          if p gt 2 then
                imsno := sub< V | imsno >;
          end if;
          orbs := orbslists[sno][pos][2];
          orbno := 0;
          for j in [1..#orbs] do
            if imsno in orbs[j] then
              orbno:=j;
              x := FindConjugatingElement(actim, imsno, orbs[j][1]);
              im := im * Transpose(x @@ f)^-1;
              slp := x @@ f @ iwmN;
              y *:= Evaluate(slp, iNactgens);
              break;
            end if;
          end for;
          assert orbno gt 0;
          pos := orbslists[sno][pos][3] + orbno;
        end for;
        assert pos eq orb[1];
        g := g^y;
        ans *:= y;

        rqtoGact := hom< imc -> Gact | perms >;
        //Need stabiliser of orb[1];
          orbrep := orb[1];
          //find group element
          vec := HorizontalJoin(listN[nISNmod][orbrep][1]);

          //first get stabiliser in DNact, DPact which is stored, and compute
          //inverse images in G
          irepV := VectorSpace(Nact)!HorizontalJoin( vec, Vector(GF(p),[1]) );
          irep := p eq 2 select irepV else sub< Parent(irepV) | irepV >; 
          DNstab := listN[nISNmod][orbrep][2];
          DPstab := listN[nISNmod][orbrep][3];
          ncpc := DPstab @@ cqpctoDPact @@ pctoqpc;
          
          //now add as few generators of Nstab as possible
          newNgens := [];
          while sub< DNstab | DPstab, newNgens > ne DNstab do
            repeat
              x:=Random(DNstab);
            until not x in sub< DNstab | DPstab, newNgens >;
            Append(~newNgens,x);
          end while;
          imcgens := [g@Gtorq]; istg := [Generic(G)|g];
          for gen in newNgens do
            slp := iwmN(gen);
            Append(~istg, Evaluate(slp, iNactgens) );
            Append(~imcgens, Evaluate(slp, radNag) );
          end for;

          //finally get stabiliser in G
          stab := Stabiliser(Gact,orbrep) @@ rqtoGact;
          ReduceGenerators(~stab);
          for gen in Generators(stab) do
            slp := iwmimc(gen);
            ggen := Evaluate(slp, icgens);
            ggenact :=  HorizontalJoin(
              VerticalJoin( cbmat*gmacts[k](ggen)*cbmat^-1,
                            Matrix((g,ggen) @ rtopc @ ptom)*cbmat^-1 ),
                            col );
            im := Vector(irepV * ggenact);
            //must find element in inverse image of N to bring im back to irep
            pos := 1;
            vec := [];
            for sno in [1..nISNmod] do
              scol := Matrix(GF(p),dns+1,1,[0: i in [1..dns]] cat [1]);
              f := orbslists[sno][pos][1];
              act := Domain(f);
              actim := Image(f);
              V := VectorSpace(actim);
              imsno := V!HorizontalJoin(ExtractBlock(im,1,(sno-1)*dns+1,1,dns),
                         Vector(GF(p),[1]) );
              if p gt 2 then imsno := sub< V | imsno >; end if;
              orbs := orbslists[sno][pos][2];
              orbno := 0;
              for j in [1..#orbs] do
                if imsno in orbs[j] then
                  orbno:=j;
                  x := FindConjugatingElement(actim, imsno, orbs[j][1]);
                  ix := x @@ f;
                  im := im * Transpose(ix)^-1;
                  slp := iwmN(ix);
                  ggen *:= Evaluate(slp, iNactgens);
                  break;
                end if;
              end for;
              assert orbno gt 0;
              pos := orbslists[sno][pos][3] + orbno;
            end for;
            Append(~istg, ggen);
            Append(~imcgens, ggen@Gtorq);
          end for; //for gen in Generators(stab) do
          cpc := ncpc;
          imc := sub<rq|imcgens>;
          icgens := istg;
    else //if k in layers
      V := VectorSpace(GF(p),d+1);
      convec := V![ Eltseq( (h^-1*g) @ rtopc @ ptom ) cat [1] ];
      //start with action of rpc
      cmats := [];
      col := Matrix(GF(p),d+1,1,[0: i in [1..d]] cat [1]);
      for i in [1..NPCgens(cqpc)] do
        pg := cqpc.i @@ pctoqpc; ig := pg @@ rtopc;
        mat := HorizontalJoin(
           VerticalJoin( rep(pg), Matrix((h,ig) @ rtopc @ ptom)), col );
        Append(~cmats,  mat);
      end for;
      cqpcact := hom< cqpc->GL(d+1,p) | cmats >;
      fact := func<  t | t[1] * cqpcact(t[2]) >;
      rado,radst,radonos := PCOSG(cqpc,fact,V.(d+1));
      vprint LMG,2: "  #rado:",#rado,"#radst",#radst;
  
      //now action of imc on orbits
      igenmats := [ GL(d+1,p) | HorizontalJoin(
           //VerticalJoin( gmacts[k](icgens[i]:im:=imc.i),
           VerticalJoin( gmacts[k](icgens[i]),
                           Matrix((h,icgens[i]) @ rtopc @ ptom)), col ):
                               i in [1..#icgens] ];
      //need two strategies for action of rq
      lo := #rado;
      iwmimc := InverseWordMap(imc);
      if lo le so then
        vprint LMG,2: "  small orbit calculation";
        fullgp := sub< GL(d+1,p) | cmats cat igenmats >;
        subgp := sub< GL(d+1,p) | cmats >;
        if not convec in Orbit(fullgp,V.(d+1)) then return false,_; end if;
	dummy := LMGOrder(fullgp);
        oa, oi := OrbitAction(fullgp,V.(d+1));
        isc, x := IsConjugate(oi, oa(V.(d+1)), oa(convec)); assert isc;
        suborbs := Orbits(oa(subgp));
        ba, bi := BlocksAction(oi,suborbs[1]);
        rqact := hom< imc->bi | [igenmats[i] @ oa @ ba : i in [1..#icgens]] >;
        x := x @ ba @@ rqact;
        slp := iwmimc(x);
        x := Evaluate(slp,icgens);
        vprint LMG,2: "  Adjusting conjugating element";
        ans *:= x^-1; g := g^(x^-1);
        rqst := Stabiliser(bi,1) @@ rqact;
        vprint LMG,2: "  degree oi:",Degree(oi),"#rqst",#rqst;
      else
        vprint LMG,2: "  non-small orbit calculation";
        fullo := rado; deg := 1;
        perms := [ [] : i in [1..#igenmats] ];
        pt := 1;
        while pt le deg do
          vec := fullo[(pt-1)*lo+1];
          for i in [1..#igenmats] do
            imvec := vec*igenmats[i];
            pos := Position(fullo,imvec);
            if pos eq 0 then //new orbit
              fullo join:=  PCOSG(cqpc,fact,imvec);
              deg +:= 1;
              perms[i][pt] := deg;
            else perms[i][pt] := (pos-1) div lo + 1;
            end if;
          end for;
          pt +:= 1;
        end while;
        convecpos := Position(fullo,convec); 
        if convecpos eq 0 then return false,_; end if;
        convecpos := (convecpos-1) div lo + 1;
        ChangeUniverse(~perms, Sym(deg));
        gorbim := sub< Sym(deg) | perms >;
        rqact := hom< imc->gorbim | perms >;
        isc, x := IsConjugate(gorbim, 1, convecpos); assert isc;
        x := x @@ rqact;
        slp := iwmimc(x);
        x := Evaluate(slp,icgens);
        vprint LMG,2: "  Adjusting conjugating element";
        ans *:= x^-1; g := g^(x^-1);
        rqst := Stabiliser(gorbim,1) @@ rqact;
        vprint LMG,2: "  #fullo:",#fullo,"#rqst",#rqst;
      end if;
      assert  imc.1 in rqst;
      //we still need to conjugate  g to h in cqpc
      convec := V![ Eltseq( (h^-1*g) @ rtopc @ ptom ) cat [1] ];
      isc,x := PCActGIsCon(cqpc,fact,rado,radonos,convec); assert isc;
      vprint LMG,2: "  Adjusting conjugating element in radical";
      x := x @@ pctoqpc @@ rtopc;
      ans *:= x^-1; g := g^(x^-1);
  
      //try to minimise generators
      stg := [imc.1];
      while sub< rqst | stg > ne rqst do
        repeat x:=Random(rqst); until not x in sub< rqst | stg >;
        Append(~stg,x);
      end while;
      rqst := sub< rqst | stg >;
      istg := [Generic(G)|g];
      ords := [ #quo<cs[i]|cs[i+1]> where cs:=CompositionSeries(cqpc) :
                   i in [1..NPCgens(cqpc)] ]; //should be a standard function!
      for l in [2..#stg] do
        slp := iwmimc(stg[l]);
        smat := Evaluate(slp, igenmats);
        vec := V.(d+1) * smat;
        isc,x := PCActGIsCon(cqpc,fact,rado,radonos,vec); assert isc;
        istg[l] := Evaluate(slp,icgens) * ((x^-1) @@ pctoqpc @@ rtopc);
      end for;
      cpc := sub< rpc | [ radst.i @@ pctoqpc : i in [1..NPCgens(radst)] ] >;
      icgens := istg;
      imc := rqst;
    end if; //if k in layers
  end for; //for k in [#cs-1..1 by -1] 

  assert origg^ans eq h;
  return true, ans;
end function;

ConjClasses := function(G:so:=256,N:=0,layers:={})
//N should be a normal subgroup of the radical quotient of G such that the
//inverse image of N in G acts decomposably on the modules of the soluble
//radical in the layer numbers (counting from bottom upwards) in layers 
  local r,rpc,rad,rtopc,rq,Gtorq,rm,gmacts,img,imc,cgens,x,cpc,icgens,cs,m,
    ptom,rep,p,d,qpc,pctoqpc,cqpc,cmats,col,pg,ig,mat,V,fact,rado,radst,
    radonos,igenmats,lo,fullgp,subgp,oa,oi,suborbs,ba,bi,rqact,rqst,fullo,
    deg,pt, perms,vec,imvec,pos,gorbim,stg,istg,ords,iwmimc,slp,smat,pow,y,
    rqcl,list,orbs,v,w,ans,g,h,ncpc,orbrep,
        ngn,nigensm,nactgens,Nact,Nmod,ISNmod,dns,nisNMod,cbmat,newlist,
        imcN,icgensN,igenmatsN,igenmatsG,Pact,DigenmatsN,
        Dcmats,DNact,DPact,cqpctoDPact,iNactgens,radNag,listN,orbslists,olist,
        uct,prev,vecs,act,scol,Realact,f,actgp,Pactgp,nvec,nNorbs,Gorbs,Gact,
        rqtoGact,mvec,newg,irepV,irep,DNstab,DPstab,newNgens,iwmN,imcgens,
        stab,ggen,ggenact,ix;
  r := G`LMGNode;
  rpc := r`radPC;
  rad := r`rad;
  rtopc := r`radtoPC;
  rq := r`radquot;
  Gtorq := r`Gtoradquot;
  rm := r`radmods;
  gmacts := r`radmodactions;
  //gmacts := r`rqradmodactions;
  cs := r`cseriesrad;

  rqcl := Classes(rq);
  vprint LMG, 1: #rqcl, "classes in radical quotient";
  //ans will contain returned answer,
  //list will contain elements and their centralisers to be lifted
  list := [car<Generic(G),PowerStructure(GrpPC),PowerStructure(GrpPerm),
                                     PowerSequence(Generic(G))>| ];
  tct:=0;
  for rqc in rqcl do
    tct+:=1; vprint LMG,2:"  Radical quotient class",tct;
    img := rqc[3]; g := img @@ Gtorq;
    imc := Centraliser(rq, img);
    cgens := [img];
    while sub< imc | cgens > ne imc do
      repeat x:=Random(imc); until not x in sub< imc | cgens >;
      Append(~cgens,x);
    end while;
    imc := sub< imc | cgens >;
    cpc := sub< rpc | >;
    icgens := [g] cat [cgens[i] @@ Gtorq : i in [2..#cgens]];
    Append(~list, <g, cpc, imc, icgens > );
  end for;

  for k in [#cs-1..1 by -1] do
    m := rm[k][1];
    ptom := rm[k][2];
    rep := rm[k][3];
    p := #BaseRing(m); d := Dimension(m);
    //lift through layer cs[len]/cs[len-1]
    vprint LMG,1: "Lifting through layer",k,"of size",p,"^",d;

    if k in layers then
//set up some matrices for action of inverse image of N on this layer module
//find the summands of the module uner N, and corresponding basis change matrix
      vprint LMG,1: "Setting up action of normal subgroup on layer";;
      ngn := Ngens(N);
      ingens := [ N.i @@ Gtorq : i in [1..ngn] ];
      //nactgens := [ gmacts[k](ingens[i] : im:=N.i) : i in [1..ngn] ];
      nactgens := [ gmacts[k](ingens[i]) : i in [1..ngn] ];
      Nact := sub< GL(d,p) |
             [rep(g) : g in Generators(rpc)] cat nactgens >;
      Nmod := GModule(Nact);
      ISNmod := IndecomposableSummands(Nmod);
      dns := Dimension(ISNmod[1]);
      nISNmod := #ISNmod;
      assert forall{s : s in ISNmod | Dimension(s) eq dns}; 
      cbmat := Matrix( &cat[ [Morphism(s,Nmod)(s.i) : i in [1..Dimension(s)]] :
                              s in ISNmod ] );
      if nISNmod eq 1 then //no point in using N-action
        vprint LMG,1: "  ","removing",k,"from N-action layers";
        Exclude(~layers,k);
      end if;
    end if; //if k in layers
    newlist := [car<Generic(G),PowerStructure(GrpPC),PowerStructure(GrpPerm),
                                     PowerSequence(Generic(G))>| ];
    qpc, pctoqpc := quo< rpc | cs[k] >;

    tct:=0;
    for t in list do
      //get action of generators of C on layer
      tct+:=1; vprint LMG,2:"  Class number",tct;
      g := t[1]; cpc := t[2]; imc := t[3]; icgens := t[4];
      cqpc := sub< qpc | pctoqpc(cs[k+1]), pctoqpc(cpc) >;
      if k in layers then
        vprint LMG,3: "  ",
            "Calculating affine action of inverse image of N on layer";
        imcN := imc meet N;
        //minimise generators
        ReduceGenerators(~imcN);

        icgensN := [];
        iwmimc := InverseWordMap(imc);
        for l in [1..Ngens(imcN)] do
          slp := iwmimc(imcN.l);
          smat := Evaluate(slp, icgens);
          Append(~icgensN,smat);
        end for;
        //set up matrices for action in new basis
        col := Matrix(GF(p),d+1,1,[0: i in [1..d]] cat [1]);
        cmats := [];
        for i in [1..NPCgens(cqpc)] do
           pg := cqpc.i @@ pctoqpc; ig := pg @@ rtopc;
           mat := HorizontalJoin(
               VerticalJoin( cbmat*rep(pg)*cbmat^-1,
                             Matrix((g,ig) @ rtopc @ ptom)*cbmat^-1 ),
                             col );
           Append(~cmats,  mat);
        end for;
        igenmatsN := [ GL(d+1,p) | HorizontalJoin(
              //VerticalJoin( cbmat*gmacts[k](icgensN[i]:im:=imcN.i)*cbmat^-1,
              VerticalJoin( cbmat*gmacts[k](icgensN[i])*cbmat^-1,
                            Matrix((g,icgensN[i]) @ rtopc @ ptom)*cbmat^-1 ),
                            col ):
                          i in [1..#icgensN] ];
        igenmatsG := [ GL(d+1,p) | HorizontalJoin(
              //VerticalJoin( cbmat*gmacts[k](icgens[i]:im:=imc.i)*cbmat^-1,
              VerticalJoin( cbmat*gmacts[k](icgens[i])*cbmat^-1,
                            Matrix((g,icgens[i]) @ rtopc @ ptom)*cbmat^-1 ),
                            col ):
                          i in [1..#icgens] ];
        Nact := sub< GL(d+1,p) | cmats cat igenmatsN >;
        Pact := sub< GL(d+1,p) | cmats >;
//BSGS calculations are much easier in the dual of Nact, because shorter bases
//typically exist. So we complicate matters by computing this dual and using
//it for all BSGS calcualtions.
        DigenmatsN := [ Transpose(x)^-1 : x in igenmatsN ]; 
        Dcmats := [ Transpose(x)^-1 : x in cmats ]; 
        DNact := sub< GL(d+1,p) | Dcmats cat DigenmatsN >;
        DPact := sub< GL(d+1,p) | Dcmats >;
        cqpctoDPact := hom< cqpc-> DPact | Dcmats >;
        //we need to find generators of G mapping onto the generators of DNact.
        iNactgens := [Generic(G)|];
        for gen in [DNact.i : i in [1..Ngens(DNact)]] do
          pos := Position(Dcmats,gen);
          if pos ne 0 then
            Append(~iNactgens, cqpc.pos @@ pctoqpc @@ rtopc);
          else pos := Position(DigenmatsN,gen);
            Append(~iNactgens, icgensN[pos] );
          end if;
        end for;

        radNag := [ x @ Gtorq : x in iNactgens ]; 
        
        /* Find DNact-orbits DNact- and DPact-stabilisers, working down
         * through the summands.
         * For summand number i, each element of listN[i] is a triple u.
         * u[1] is the list of orbit reps down to level i, represented
         * as a list of i vectors of length dNS. u[2] and u[3] are the
         * stabilisers of this orbit rep in DNact and in DPact, respectively.
         *
         * orbslists[i] contain one triple t for each representative vec in 
         * listN[i-1]. t[1] is the action homomorphism from the stabiliser
         * in DNact of vec to the action on the current N-summand
         * t[2] is the list of (relevant) orbits of that action,
         * and t[3] just marks the position in listN[i] where 
         * these orbit reps and stabilisers start. 
         */
        listN := [];
        orbslists := [];
        
        for sno in [1..nISNmod] do
          vprint LMG,3: "  ","N summand no",sno;
          olist := [];
          uct := 0;
          prev := sno eq 1 select [< [], DNact, DPact > ] else listN[sno-1];
          lN := [];
          for u in prev do
            uct+:=1; vprint LMG,3:"  Rep number",uct;
            //get action of generators of current subgroup of DNact on layer
            vecs := u[1]; act := u[2]; Pact := u[3];
            scol := Matrix(GF(p),dns+1,1,[0: i in [1..dns]] cat [1]);
            Realact := [ Transpose(act.i)^-1 : i in [1..Ngens(act)] ];
            f := hom< act -> GL(dns+1,p) |
                  [ HorizontalJoin(
               VerticalJoin(
                 ExtractBlock(Realact[i],(sno-1)*dns+1,(sno-1)*dns+1,dns,dns),
                          ExtractBlock(Realact[i],d+1,(sno-1)*dns+1,1,dns) ),
                    scol) : i in [1..#Realact] ] >;
            actgp := Image(f);
            Pactgp := f(Pact);
            if p eq 2 then
              orbs := Orbits(actgp);
                   //only want those with nontrivial dns+1 entry
              orbs := [ o: o in orbs | Rep(o)[dns+1] ne 0 ];
            else
              orbs := LineOrbits(actgp);
                   //only want those with nontrivial dns+1 entry
              orbs := [ o: o in orbs | (Rep(o).1)[dns+1] ne 0 ];
            end if;
            Append(~olist,< f, orbs, #lN >); //#lN to mark position in lN
            for orb in orbs do
              orbrep := orb[1];
              vec := p eq 2 select orbrep
                     else (vec/vec[dns+1] where vec := orbrep.1);
              vec := Vector(Prune(Eltseq(vec)));
              nvec := Append(vecs,vec);
              Append(~lN, <nvec,Stabiliser(actgp,orbrep) @@ f,
                               Stabiliser(Pactgp,orbrep) @@ f>);
            end for;
          end for;
          Append(~listN,lN);
          Append(~orbslists,olist);
          vprint LMG,3: #lN,"N orbreps";
        end for; //for sno in [1..#ISNmod] do

        //Now the N orbits are represented by listN[nISNmod] and we are ready
        //to calculate the induced G-action.
        nNorbs := #listN[nISNmod];
        perms := [ ];
        iwmN := InverseWordMap(DNact);
        for gen in igenmatsG do
          //get action of generator of G on orbit
          perm := [];
          for i in [1..nNorbs] do
            im := HorizontalJoin(
              HorizontalJoin(listN[nISNmod][i][1]), Vector(GF(p),[1]) ) * gen;
            //need to locate orbit of im by working through orbits of N
            pos := 1;
            vec := [];
            for sno in [1..nISNmod] do
              scol := Matrix(GF(p),dns+1,1,[0: i in [1..dns]] cat [1]);
              f := orbslists[sno][pos][1];
              act := Domain(f);
              actim := Image(f);
              V := VectorSpace(actim);
              imsno := V!HorizontalJoin(ExtractBlock(im,1,(sno-1)*dns+1,1,dns),
                         Vector(GF(p),[1]) );
              if p gt 2 then
                imsno := sub< V | imsno >;
              end if;
              orbs := orbslists[sno][pos][2];
              orbno := 0;
              for j in [1..#orbs] do
                if imsno in orbs[j] then
                  orbno:=j;
                  x := FindConjugatingElement(actim, imsno, orbs[j][1]);
                  im := im * Transpose(x @@ f)^-1;
                  break;
                end if;
              end for;
              assert orbno gt 0;
              pos := orbslists[sno][pos][3] + orbno;
            end for;
            Append(~perm,pos);
          end for;
          Append(~perms, Sym(nNorbs)!perm);
        end for;

        Gact := sub< Sym(nNorbs) | perms >;
        rqtoGact := hom< imc -> Gact | perms >;
        Gorbs := Orbits(Gact);
        vprint LMG,3: #Gorbs,"G orbreps";
        //The orbit reps correspond to the conjugacy classes at this
        //level. Now to find their stabilizers.
        for orb in Gorbs do
          orbrep := Representative(orb);
          //find group element
          vec := HorizontalJoin(listN[nISNmod][orbrep][1]);
          mvec := m!Eltseq(vec * cbmat);
          newg := g * (mvec @@ ptom @@ rtopc);

          //first get stabiliser in DNact, DPact which is stored, and compute
          //inverse images in G
          irepV := VectorSpace(Nact)!HorizontalJoin( vec, Vector(GF(p),[1]) );
          irep := p eq 2 select irepV else sub< Parent(irepV) | irepV >; 
          DNstab := listN[nISNmod][orbrep][2];
          DPstab := listN[nISNmod][orbrep][3];
          ncpc := DPstab @@ cqpctoDPact @@ pctoqpc;
          
          //now add as few generators of Nstab as possible
          newNgens := [];
          while sub< DNstab | DPstab, newNgens > ne DNstab do
            repeat
              x:=Random(DNstab);
            until not x in sub< DNstab | DPstab, newNgens >;
            Append(~newNgens,x);
          end while;
          //we must always have g (now replaced by newg) as first generator
          //of stabiliser
          imcgens := [newg@Gtorq]; istg := [Generic(G)|newg];
          for gen in newNgens do
            slp := iwmN(gen);
            Append(~istg, Evaluate(slp, iNactgens) );
            Append(~imcgens, Evaluate(slp, radNag) );
          end for;

          //finally get stabiliser in G
          stab := Stabiliser(Gact,orbrep) @@ rqtoGact;
          ReduceGenerators(~stab);
          for gen in Generators(stab) do
            slp := iwmimc(gen);
            ggen := Evaluate(slp, icgens);
            ggenact :=  HorizontalJoin(
              VerticalJoin( cbmat*gmacts[k](ggen)*cbmat^-1,
                            Matrix((g,ggen) @ rtopc @ ptom)*cbmat^-1 ),
                            col );
            im := Vector(irepV * ggenact);
            //must find element in inverse image of N to bring im back to irep
            pos := 1;
            vec := [];
            for sno in [1..nISNmod] do
              scol := Matrix(GF(p),dns+1,1,[0: i in [1..dns]] cat [1]);
              f := orbslists[sno][pos][1];
              act := Domain(f);
              actim := Image(f);
              V := VectorSpace(actim);
              imsno := V!HorizontalJoin(ExtractBlock(im,1,(sno-1)*dns+1,1,dns),
                         Vector(GF(p),[1]) );
              if p gt 2 then imsno := sub< V | imsno >; end if;
              orbs := orbslists[sno][pos][2];
              orbno := 0;
              for j in [1..#orbs] do
                if imsno in orbs[j] then
                  orbno:=j;
                  x := FindConjugatingElement(actim, imsno, orbs[j][1]);
                  ix := x @@ f;
                  im := im * Transpose(ix)^-1;
                  slp := iwmN(ix);
                  ggen *:= Evaluate(slp, iNactgens);
                  break;
                end if;
              end for;
              assert orbno gt 0;
              pos := orbslists[sno][pos][3] + orbno;
            end for;
            Append(~istg, ggen);
            Append(~imcgens, ggen@Gtorq);
          end for; //for gen in Generators(stab) do
          Append(~newlist, < newg, ncpc, sub<rq|imcgens>, istg >);
        end for; //for orb in Gorbs do

      else //layer ne k
        cmats := [];
        col := Matrix(GF(p),d+1,1,[0: i in [1..d]] cat [1]);
        for i in [1..NPCgens(cqpc)] do
          pg := cqpc.i @@ pctoqpc; ig := pg @@ rtopc;
          mat := HorizontalJoin(
             VerticalJoin( rep(pg), Matrix((g,ig) @ rtopc @ ptom)), col );
          Append(~cmats,  mat);
        end for;
        cqpcact := hom< cqpc->GL(d+1,p) | cmats >;
        V := VectorSpace(GF(p),d+1);
        igenmats := [ GL(d+1,p) | HorizontalJoin(
           //VerticalJoin( gmacts[k](icgens[i]:im:=imc.i),
           VerticalJoin( gmacts[k](icgens[i]),
                         Matrix((g,icgens[i]) @ rtopc @ ptom)), col ):
                               i in [1..#icgens] ];
        fullgp := sub< GL(d+1,p) | cmats cat igenmats >;
        subgp := sub< GL(d+1,p) | cmats >;
        if p eq 2 then
          orbs := Orbits(fullgp); //only want those with nontrivial d+1 entry
          orbs := [ o: o in orbs | Rep(o)[d+1] ne 0 ];
        else
          orbs :=LineOrbits(fullgp);
                               //only want those with nontrivial d+1 entry
          orbs := [ o: o in orbs | (Rep(o).1)[d+1] ne 0 ];
        end if;
        vprint LMG,3: "  ",#orbs,"orbits";
        for orb in orbs do
          orbrep := orb[1];
          vprint LMG,3: "    Doing next orbit computation";
          vvec :=p eq 2 select orbrep else (vec/vec[d+1] where vec := orbrep.1);
          h := g * (m!Prune(Eltseq(vvec))) @@ ptom @@ rtopc;
          fact := func<  t | t[1] ^ cqpcact(t[2]) >;
          rado, radst, radonos := PCOSG(cqpc, fact, orbrep);
          vprint LMG,3: "    #rado:",#rado,"#radst",#radst;
          //two strategies for action of rq
          lo := #rado;
          if forall{m : m in cmats cat igenmats |orbrep ^ (GL(d+1,p)!m) in rado}
           then
           //easiest case: rado fixed by all gens
             vprint LMG,3:"    rado fixed by rq generators";
             rqst := imc;
             stg := [ imc.i : i in [1..Ngens(imc)] ];
          elif lo le so then
            vprint LMG,3: "    small orbit calculation";
	    dummy := LMGOrder(fullgp);
            oa, oi := OrbitAction(fullgp, orbrep);
            suborbs := Orbits(oa(subgp));
            ba, bi := BlocksAction(oi,suborbs[1]);
            rqact:=hom< imc->bi | [igenmats[i] @ oa @ ba : i in [1..#icgens]] >;
            rqst := Stabiliser(bi,1) @@ rqact;
            vprint LMG,3: "    degree oi:",Degree(oi),"#rqst",#rqst;
            stg := [imc.1];
            //minimise generators
            while sub< rqst | stg > ne rqst do
              repeat x:=Random(rqst); until not x in sub< rqst | stg >;
              Append(~stg,x);
            end while;
            rqst := sub< rqst | stg >;
          else
            vprint LMG,3: "    non-small orbit calculation";
            fullo := rado; deg := 1;
            perms := [ [] : i in [1..#igenmats] ];
            pt := 1;
            while pt le deg do
              vec := fullo[(pt-1)*lo+1];
              for i in [1..#igenmats] do
                imvec := vec ^ GL(d+1,p)!igenmats[i];
                pos := Position(fullo,imvec);
                if pos eq 0 then //new orbit
                  fullo join:=  PCOSG(cqpc,fact,imvec);
                  deg +:= 1;
                  perms[i][pt] := deg;
                else perms[i][pt] := (pos-1) div lo + 1;
                end if;
              end for;
              pt +:= 1;
            end while;
            ChangeUniverse(~perms, Sym(deg));
            gorbim := sub< Sym(deg) | perms >;
            rqact := hom< imc->gorbim | perms >;
            rqst := Stabiliser(gorbim,1) @@ rqact;
            vprint LMG,3: "    #fullo:",#fullo,"#rqst",#rqst;
            //minimise generators
            rqst := sub< rqst | imc.1, rqst >;
            ReduceGenerators(~rqst);
          end if;
          stg := [rqst.i : i in [1..Ngens(rqst)]];
          istg := [Generic(G)|h];
          iwmimc := InverseWordMap(imc);
          for l in [2..#stg] do
            slp := iwmimc(stg[l]);
            smat := Evaluate(slp, igenmats);
            w := orbrep ^ smat;
            isc,x := PCActGIsCon(cqpc,fact,rado,radonos,w); assert isc;
            istg[l] := Evaluate(slp,icgens) * ((x^-1) @@ pctoqpc @@ rtopc);
          end for;
         ncpc :=sub< rpc | [ radst.i @@ pctoqpc : i in [1..NPCgens(radst)] ] >;
          Append(~newlist, <h,ncpc,rqst,istg> );
        end for; //for orb in orbs do
      end if; //if k in layers
    end for; // for t in list do

    list := newlist;
    vprint LMG,1: #list,"classes in this quotient";
  end for; // for k in [#cs-1..1 by -1] do

  ans := [car<IntegerRing(), IntegerRing(), Generic(G)> | ];
  ansc := [PowerStructure(GrpMat)| ];  //centraliser of conj class rep
  for t in list do
    g := t[1]; cpc := t[2]; imc := t[3];
    Append(~ans, <Order(g), LMGOrder(G) div (#cpc * #imc), g> );
    Append(~ansc, sub< Generic(G) |
        [ t[2].i @@ rtopc : i in [1..Ngens(t[2])]] cat t[4] > );
  end for;
  return ans, ansc;
end function;
