freeze;

import "centconj.m" : PCOSG, PCActGIsCon;

MeetRad := function(G, H)
//H is a subgroup of G - compute H meet Radical(G) using FPGroupStrong
  local r,rad,rq,Gtorq,imHgens,imH,F,rho,imFgens,invimFgens,meetgens,iwmimH,
        FtoH,rels,K,hgens;
  r := G`LMGNode;
  rad := r`rad;
  rq := r`radquot;
  Gtorq := r`Gtoradquot;
  meetgens := [];
  hgens := [ Generic(H) | H.i : i in [1..Ngens(H)] ];
  imHgens := [ h @ Gtorq : h in hgens ];
  //FPGroupStrong eliminates trivial and repeated generators, so put in
  //corresponding generators of intersection.
  for i in [1..#imHgens] do
    if imHgens[i] eq Id(rq) then
      Append(~meetgens,H.i);
    else
      for j in [1..i-1] do
        if imHgens[i] eq imHgens[j] then
          Append(~meetgens,H.i*H.j^-1);
          continue i;
        end if;
      end for;
    end if;
  end for;
    
  imH := sub< rq | imHgens >;
  F, rho := FPGroupStrong(imH);
  imFgens := [ F.i @ rho : i in [1..Ngens(F)] ];
  //need to get these as elements of H
  iwmimH := InverseWordMap(imH);
  invimFgens := [ Evaluate( imFgens[i] @ iwmimH, hgens) : i in [1..Ngens(F)] ];
  FtoH := hom< F-> Generic(H) | invimFgens >;
  rels := [ LHS(r) * RHS(r)^-1 : r in Relations(F) ];
  meetgens cat:= [ r @ FtoH : r in rels ];
  K := sub<Generic(H)|meetgens>;
  LMGInitialise(K);
  return LMGNormalClosure(H, K);
end function;

MeetSubs := function(G,H,K : so:=256)
//H and K should be subgroups of G - find thier intersection -
//need radical quotient
local r,rpc,rad,rtopc,rq,Gtorq,rm,imh,imk,iwmimh,iwmimk,imm,slp,kmeetgens,
      kmeetr,hmeetr,kmeetm,hmeetm, mpc,mgens,m,ptom,rep,p,d,qpc,pctoqpc,
      hqpc,khom,kqpc,cbmat,khomb,hhomb,pctoqpcb,QMat,QVec,pg,pcmats,kim,ihim,
      mat,vec,amat,igenmats,kqpcact,V,fact,rado,radst,radonos,fullgp,subgp,
      oa,oi,ba,bi,rqact,rqst,stg,fullo,perms,pt,imvec,pos,deg,gorbim;

  r := G`LMGNode;
  rpc := r`radPC;
  rad := r`rad;
  rtopc := r`radtoPC;
  rq := r`radquot;
  Gtorq := r`Gtoradquot;
  rm := r`radmods;
  //gmacts := r`rqradmodactions;
  gmacts := r`radmodactions;
  
  imh := sub< rq | [ H.i @ Gtorq : i in [1..Ngens(H)]] >;
  imk := sub< rq | [ K.i @ Gtorq : i in [1..Ngens(K)]] >;
  iwmimh := InverseWordMap(imh);
  iwmimk := InverseWordMap(imk);
  imm := imh meet imk;
  //try to minimise generators
  mgens := [];
  while sub< imm | mgens > ne imm do
    repeat x:=Random(imm); until not x in sub< imm | mgens >;
    Append(~mgens,x);
  end while;
  imm := sub< imm | mgens >;

  hmeetr := MeetRad(G,H);
  kmeetr := MeetRad(G,K);
  //want these as PC-groups
  hmeetr := sub< rpc | [ g @ rtopc : g in Generators(hmeetr) ] >;
  kmeetr := sub< rpc | [ g @ rtopc : g in Generators(kmeetr) ] >;

  //intersection (as subgroup of K, mod current term in csrad) will be stored
  //as intersection mpc with rpc with extra gens outside of radical
  mpc := kmeetr;
  slp := [ imm.i @ iwmimk : i in [1..Ngens(imm)]];
  kmeetgens := [ Evaluate(s, [ K.i : i in [1..Ngens(K)]]) : s in slp ];
  cs := r`cseriesrad;
  vprint LMG,1: "Order of image of intersection in radical quotient:", #imm;

  for k in [#cs-1..1 by -1] do
    m := rm[k][1];
    ptom := rm[k][2];
    rep := rm[k][3];
    p := #BaseRing(m); d := Dimension(m);
    vprint LMG,1: "Lifting through layer",k,"of size",p,"^",d;
    qpc, pctoqpc := quo< rpc | cs[k] >;
    khom := hom< mpc -> qpc | [ mpc.i @ pctoqpc : i in [1..NPCgens(mpc)] ] >;
    kqpc := Image(khom);
    hmeetm := sub< rpc | cs[k], cs[k+1] meet hmeetr > @ ptom;

    //we will also need maps onto smaller quotient
    qpcb, pctoqpcb := quo< rpc | cs[k+1] >;
    khomb := hom< kmeetr -> qpcb |
                       [ kmeetr.i @ pctoqpcb : i in [1..NPCgens(kmeetr)] ] >;
    hhomb := hom< hmeetr -> qpcb |
                       [ hmeetr.i @ pctoqpcb : i in [1..NPCgens(hmeetr)] ] >;

    //we will be working in the quotient of m by hmeetm - set up bases
    //so that we can calculate action matrices
    ds := Dimension(hmeetm); dq := d-ds;
    bas := [ VectorSpace(m) | hmeetm.i @ Morphism(hmeetm,m) : i in [1..ds] ]; 
    bas := ExtendBasis(bas, VectorSpace(m));
    cbmat := Matrix(bas);
    //a couple of functions for extracting the quotient components of
    //matrices and vectors 
    QMat := func< mat | ExtractBlock(cbmat*mat*cbmat^-1,ds+1,ds+1,dq,dq) >; 
    QVec := func< vec | ExtractBlock(vec*cbmat^-1,1,ds+1,1,dq) >; 
    //Now set up actions first for kmeetr then for other gens
    col := Matrix(GF(p),dq+1,1,[0: i in [1..dq]] cat [1]);
    pcmats := [];
    for i in [1..NPCgens(kqpc)] do
      pg := kqpc.i @@ khom;
      //we have to write this as an element of H times element of module
      kim := pg @ pctoqpcb;
      assert kim in Image(hhomb);
      ihim := kim @@ hhomb;
      vec := (ihim^-1 * pg) @ ptom;
      mat := HorizontalJoin( VerticalJoin(QMat(rep(pg)), QVec(vec)), col );
      Append(~pcmats,  mat);
    end for;
    //find orbits
    kqpcact := hom< kqpc->GL(dq+1,p) | pcmats >;
    V := VectorSpace(GF(p),dq+1);
    fact := func<  t | t[1] * kqpcact(t[2]) >;
    rado,radst,radonos := PCOSG(kqpc,fact,V.(dq+1));
    vprint LMG,2: "  #rado:",#rado,"#radst",#radst;
    vprint LMG,1:
      "Current order of image of intersection in quotient of radical:", #radst;

    //now action of imm on orbits
    igenmats := [ GL(dq+1,p) | ];
    for i in [1..#kmeetgens] do
      //amat := gmacts[k](kmeetgens[i]:im:=imm.i);
      amat := gmacts[k](kmeetgens[i]);
      //we have to write kmeetgens[i] as an element of H times element of module
      slp := iwmimh(imm.i);
      h := Evaluate(slp,[H.i: i in [1..Ngens(H)]]);
      pg := (h^-1 * kmeetgens[i]) @ rtopc;
      kim := pg @ pctoqpcb;
      assert kim in Image(hhomb);
      ihim := kim @@ hhomb;
      vec := (ihim^-1 * pg) @ ptom;
      mat := HorizontalJoin( VerticalJoin(QMat(amat), QVec(vec)), col );
      Append(~igenmats,  mat);
    end for;
    //as in centconj, use two strategies
    lo := #rado;
    if lo le so then
        vprint LMG,2: "  small orbit calculation";
        fullgp := sub< GL(dq+1,p) | pcmats cat igenmats >;
        subgp := sub< GL(dq+1,p) | pcmats >;
	dummy := LMGOrder(fullgp);
        oa, oi := OrbitAction(fullgp,V.(dq+1));
        suborbs := Orbits(oa(subgp));
        ba, bi := BlocksAction(oi,suborbs[1]);
        rqact := hom< imm->bi | [igenmats[i] @ oa @ ba : i in [1..#igenmats]] >;
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
              fullo join:=  PCOSG(kqpc,fact,imvec);
              deg +:= 1;
              perms[i][pt] := deg;
            else perms[i][pt] := (pos-1) div lo + 1;
            end if;
          end for;
          pt +:= 1;
        end while;
        ChangeUniverse(~perms, Sym(deg));
        gorbim := sub< Sym(deg) | perms >;
        rqact := hom< imm->gorbim | perms >;
        rqst := Stabiliser(gorbim,1) @@ rqact;
        vprint LMG,2: "  #fullo:",#fullo,"#rqst",#rqst;
    end if; //if lo le so
    //try to minimise generators
    stg := [];
    while sub< rqst | stg > ne rqst do
      repeat x:=Random(rqst); until not x in sub< rqst | stg >;
      Append(~stg,x);
    end while;
    rqst := sub< rqst | stg >;
    istg := [Generic(G)|];
    iwmimm := InverseWordMap(imm);
    for l in [1..#stg] do
      slp := iwmimm(stg[l]);
      smat := Evaluate(slp, igenmats);
      vec := V.(dq+1) * smat;
      isc,x := PCActGIsCon(kqpc,fact,rado,radonos,vec); assert isc;
      istg[l] := Evaluate(slp,kmeetgens) * ((x^-1) @@ pctoqpc @@ rtopc);
    end for;
    mpc := sub< rpc |
       kmeetr meet cs[k], [ radst.i @@ khom : i in [1..NPCgens(radst)] ] >;
    kmeetgens := istg;
    imm := rqst;
    vprint LMG,1:
       "Current order of image of intersection in radical quotient:", #imm;
  end for; //for k in [#cs-1..1 by -1]
  return sub< Generic(G) | [ g @@ rtopc : g in Generators(mpc) ] cat istg >;
end function;
