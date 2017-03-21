freeze;

import "compab.m":  ReduceAbAutMat, ReduceAbAutVec, CheckRelationsA,
       IsAutAndInverse, MatrixOfGroupElement,  ComplementEquationsMatrixA,
       FirstCohomologyGroupA, SplitExtensionPermRepA;
import "strongpres.m": MakeGroupRecordSG, SWInv, SVWordH, SGWordH,
                       SVPermutationH;

MakeModuleRecordSGA := function(G,invar,mats)
/* This is called prior to calling any of the cohomological functions,
 * and returns a cohomology module with fields for the various objects
 * that may get computed.
 * G is a permutation group.
 * M should be a module for G.
 * The cohomological functions take this record as argument.
 */

  local GR, R, sg, r, ng, imats, omats, oimats;

  ng := Ngens(G);
  if ng ne #mats then
    error "Wrong number of matrices in MakeModuleRecordSGA";
  end if;
  GR := MakeGroupRecordSG(G : sgwords:=true);

  omats := [ ReduceAbAutMat(invar,m) : m in mats];
  oimats:=[];
  for i in [1..ng] do
    isit, oimats[i] := IsAutAndInverse(invar,omats[i]);
    if not isit then
      error "A matrix in MakeModuleRecordSGA does not define an automorphism";
    end if;
  end for;

  //But we want the matrices of the strong generators!
  mats := [ MatrixOfGroupElement(g,invar,omats,oimats) : g in GR`sgw ];
  imats :=[ MatrixOfGroupElement(g^-1,invar,omats,oimats) : g in GR`sgw ];

  if not CheckRelationsA(GR`gf,invar,mats:imats:=imats) then
    error "Matrices do not satisfy relations on strong generators";
  end if;

  r := EmptyCohomologyModule();
  r`modtype := GrpAb;
  r`gptype := GrpPerm;
  r`gr := GR;
  r`mats := mats; r`imats := imats;
  r`invar:=invar;
  r`dim := #invar;
  if #invar eq 0 then
    r`ring := Integers(1);
  else
    r`ring := invar[#invar] eq 0 select Integers() else Integers(invar[#invar]);
  end if;  
  r`gf := GR`gf;
  r`gftoG := GR`f2p;

  return r;
end function;

OneCocycleSGA := function(CM,s)
//returns a function G-> module
  local nselt, OC, d, ng, K, Z, GR, invar, mats, imats, V, genims;
  nselt := ElementToSequence(((CM`H1)!s) @@ CM`Z1toH1);
  ng := Ngens(CM`gf);
  GR := CM`gr;
  d := CM`dim;
  K := CM`ring;
  Z := Integers();
  invar := CM`invar;
  mats := CM`mats; imats:=CM`imats;
  V := RSpace(Z,d);
  //find images of one-cocyle on generators
  genims := [ V!(nselt[(i-1)*d+1 .. i*d]) : i in [1..ng] ];
  OC := function(gtp)
    local w, cmat, ans, g;
    g := gtp[1];
    w := ElementToSequence(SGWordH(GR,g));
    cmat := IdentityMatrix(Z,d);
    ans := V!0;
    //scan from right hand end
    for g in Reverse(w) do
      if g lt 0 then
        cmat := imats[-g]*cmat;
        ans -:= genims[-g]*cmat;
      else
        ans +:= genims[g]*cmat;
        cmat := mats[g]*cmat;
      end if;
    end for;
    return ReduceAbAutVec(invar,ans);
  end function;

  return OC;
end function;

IdentifyOneCocycleSGA := function(CM,OC)
  //identify from action on strong generators
  local sg, s;
  sg := CM`gr`sg;
  s := &cat [ ElementToSequence(OC(<sg[i]>)) : i in [1..#sg] ];
  s := RSpace(Integers(),#s)!s;
  if not s in CM`Z1 then
    error "Input to IdentifyOneCocycle is not a cocycle";
  end if;
  return s @ CM`Z1toH1;
end function;

IsOneCoboundarySGA := function(CM,OC)
  //if so then return 0-cochain z such that OC(<g>) = z(<>)^(1-g) for g in G
  local ng, d, K, Z, isc, sg, v, w;

  d := CM`dim;
  K := CM`ring;
  Z := Integers();

  sg := CM`gr`sg;
  w := &cat [ ElementToSequence(OC(<sg[i]>)) : i in [1..#sg] ];
  w := Vector(K, w);
  isc, v := IsConsistent(CM`csm, w);
  if not isc then return false, _; end if;
  /* Need lop off the unwanted end of v and write over Z. */
  V := RSpace(Z,d);
  v := V![-v[j] : j in [1..d]];
  return true, func< tp | v >;
end function;

TraceWordSGA :=
   procedure(w,K,invar,mats,imats,sg,sgi,bo,bono,tail,utail,colno,~X,~ntw)
//at present we always call with K=integers
   local d, pt, ipt, sgno, ptno, cmati, utno;
        d := #invar;
        ntw := [];
        pt:=bo[bono];
        ipt:=pt;
        ptno:=bono;
        cmati := IdentityMatrix(K,#invar);
        for g in w do
          if g ge 0 then
            sgno := Position(sgi,g);
            ntw := ntw cat tail[ptno][sgno];
            utno := utail[ptno][sgno];
            if utno gt 0 then
              InsertBlock(~X,
         ReduceAbAutMat(invar,ExtractBlock(X,d*(utno-1)+1,colno+1,d,d)+cmati),
                                                          d*(utno-1)+1,colno+1);
            end if;
            for i in tail[ptno][sgno] do
               if i gt 0 then cmati := ReduceAbAutMat(invar,imats[i]*cmati);
               else cmati := ReduceAbAutMat(invar,mats[-i]*cmati);
               end if;
            end for;
            ipt := ipt ^ sg[g];
            ptno := Position(bo,ipt);
          else
            sgno := Position(sgi,-g);
            ipt := ipt ^ (sg[-g]^-1);
            ptno := Position(bo,ipt);
            ntw := ntw cat SWInv(tail[ptno][sgno]);
            for i in SWInv(tail[ptno][sgno]) do
               if i gt 0 then cmati := ReduceAbAutMat(invar,imats[i]*cmati);
               else cmati := ReduceAbAutMat(invar,mats[-i]*cmati);
               end if;
            end for;
            utno := utail[ptno][sgno];
            if utno gt 0 then
              InsertBlock(~X,
       ReduceAbAutMat(invar,ExtractBlock(X,d*(utno-1)+1,colno+1,d,d)-cmati),
                                                          d*(utno-1)+1,colno+1);
            end if;
          end if;
        end for;
        if ipt ne pt then
          print w, bo, bono;
          error "Tracing error!";
        end if;
end procedure;

SecondCohomologyGroupSGA := procedure(CM)
/* 
 * SecondCohomologyGroupSG computes a matrix and stores its nullspace, which
 * is isomorphic to Z^2(G,M), then computes B2, H2.
 */

  local  invar, G, GR, mats, imats, K, d, ng, nr, nb, RG, ncols, X, colno, sgw,
    sgwmat, tail, utail, sg, reli, tw, ntw, bo, pt, w, h, gens, hgens,  nsgens,
    V1, V2, V3, deg, Y, stg, I, Z, VZ, YZ;

  if assigned CM`H2 then return; end if;
  if not assigned CM`cem then
    ComplementEquationsMatrixA(CM);
  end if;

  invar:=CM`invar; G:=CM`gf; mats:=CM`mats; imats:=CM`imats;
  Z := Integers();
  K := CM`ring;
  d := #invar;
  GR:=CM`gr;
  sg:=GR`sg;
  nb:=#GR`b;

  RG := Relations(GR`gf);
  nr := #RG;

  /* Set up the matrix  X  where we will store the equations */
  ncols := &+ [ #GR`bo[i] * #GR`reli[i] * d : i in [1.. #GR`b] ];
  vprint ModCoho: "Setting up",ncols,"equations in",GR`modvars*d,"unknowns";
  //XK:=Hom(RSpace(K,GR`modvars*d),RSpace(K,ncols))!0;
  X:=Hom(RSpace(Z,GR`modvars*d),RSpace(Z,ncols))!0;
  
  colno:=0;
  for bno in [nb..1 by -1] do
    sgw:=GR`sgword[bno];
    tail:=GR`tail[bno];
    utail:=GR`utail[bno];
    bo:=GR`bo[bno];
    reli:=GR`reli[bno];
    for bono in [1..#bo] do
      //Calculate inverse of action matrix
      sgwmat := IdentityMatrix(Z,d);
      for i in SWInv(sgw[bono]) do
        if i gt 0 then sgwmat := ReduceAbAutMat(invar,sgwmat*mats[i]);
        else sgwmat := ReduceAbAutMat(invar,sgwmat*imats[-i]);
        end if;
      end for;
  
      for rno in reli do
        //Scan relation no. rno under relevant group element
        //The equations generated are numbers colno+1 .. colno+d.
        r := RG[rno]; w := ElementToSequence(LHS(r)*RHS(r)^-1);
        TraceWordSGA(w,Z,invar,mats,imats,sg,GR`sgi[bno],
                                  bo,bono,tail,utail,colno,~X,~ntw);
        for j in [bno+1..nb] do
          tw:=ntw;
          TraceWordSGA(tw,Z,invar,mats,imats,sg,GR`sgi[j],
                           GR`bo[j],1,GR`tail[j],GR`utail[j],colno,~X,~ntw);
        end for;

        /* The equations specify that the word in the Schreier generators
         * coming from the scanned relator is equal to the conjugate of
         * of the Schreier generator for that relator under the inverse of
         * group element number elt - sgwmat is the matrix for this inverse.
         */
        //rpos := relpos[rno];
        for j in [1..d] do for k in [1..d] do
          X[d*(rno-1)+j][colno+k] -:= sgwmat[j][k];
          if invar[k] ne invar[d] then
            X[d*(rno-1)+j][colno+k] :=
                    (Integers()!X[d*(rno-1)+j][colno+k]) mod invar[k];
          end if;
        end for; end for;
        colno +:= d;
      end for;
    end for;
  end for;
  X := Hom(RSpace(K,GR`modvars*d),RSpace(K,ncols))!X;
  vprint ModCoho: "Done";

  //We won't store X itself, since it is very large - we only
  //need its nullspace.
  k := #[i : i in [1..d] | invar[i] ne invar[d] ];
  if k ne 0 then
    Y := Matrix(K,k,d,[0: i in [1..k*d]]);
    for i in [1..k] do Y[i][i] := invar[i]; end for;
    X := VerticalJoin(X, DirectSum([Y :i in [1..Ncols(X) div d]]));
  end if;
  vprint ModCoho: "Getting nullspace of ",Nrows(X),"by",Ncols(X),
                          "matrix over", CoefficientRing(X);
  vtime ModCoho: ns := Nullspace(X);

  vprint ModCoho: "Got Nullspace, dimension =", Dimension(ns);
  //First lop off the unwanted ends of the rows of N and store result.
  deg := GR`modvars*d;
  V1 := RSpace(K,deg);
  nsgens := [ V1![(ns.i)[j] : j in [1..deg]] : i in [1..Dimension(ns)]];
  CM`nsgens := nsgens;

//"making hom", d*nr, deg;
//  h := hom<V1->V2 |
//              [V2.i : i in [1..d*nr]] cat [V2!0 : i in [d*nr+1..deg]] >;
//"made";
  //need to adjoin generators for invariants of abelian group.

  V2 := RSpace(K,d*nr);
  k := #[i : i in [1..d] | invar[i] ne invar[d] ];
  Y:=[];
  for g in [1..nr] do
    stg := (g-1)*d;
    for j in [1..k] do
      v := V2!0;
      v[stg+j] := invar[j];
      Append(~Y,v);
    end for;
  end for;

  //To compute Z^2, we only need the first nr*d components of the
  //vectors in nsgens.
  V2 := RSpace(K,d*nr);
  hgens := [ V2![n[i]: i in [1..d*nr]] : n in nsgens ];
  //gens := [h(nsgens[i]) : i in [1..#nsgens] | h(nsgens[i]) ne 0] cat Y;
  CM`nsgens := [ V1 | nsgens[i] : i in [1..#nsgens] | not IsZero(hgens[i])];
  gens := [ h : h in hgens | not IsZero(h)] cat Y;
  
  //for now, we lift the result back up the integers, since quotients of
  //spaces over finite integer rings are not well behave.
  if (invar[d] ne 0) then
    VZ := RSpace(Integers(),nr*d);
    YZ := [ VZ!y : y in gens ];
    for g in [1..nr] do
      sg := (g-1)*d;
      for j in [k+1..d] do
        v := VZ!0;
        v[sg+j] := invar[j];
        Append(~YZ,v);
      end for;
    end for;
    CM`Z2 := sub < VZ | YZ >;
  else CM`Z2 := sub < V2 | gens >;
  end if;
  // make gens into a matrix
  V3 := RSpace(K,#gens);
  CM`Z2gens := Hom(V3,V2)!(gens);
  vprint ModCoho: "Calculated Z2";
  I := Image(CM`cem);
  
  //for now, we lift the result back up the integers, since quotients of
  //spaces over finite integer rings are not well behave.
  if (invar[d] ne 0) then
    YZ := [ VZ!y : y in Y ];
    for g in [1..nr] do
      sg := (g-1)*d;
      for j in [k+1..d] do
        v := VZ!0;
        v[sg+j] := invar[j];
        Append(~YZ,v);
      end for;
    end for;
    CM`B2 := sub< VZ | [VZ!(I.i) :i in [1..Ngens(I)]] cat YZ >;
  else CM`B2 := sub< V2 | [V2!(I.i) :i in [1..Ngens(I)]] cat Y >;
  end if;
  vprint ModCoho: "Calculated B2";

  CM`H2, CM`Z2toH2 := quo< CM`Z2 | CM`B2 >;
  vprint ModCoho: "Calculated H2";

end procedure;

MatrixOfExtensionSGA := function(CM,seq)
/* CM`H2 should have been computed already with SecondCohomologyGroup.
 * seq should be an integer sequence representing an element of  CM`H2.
 * A matrix enabling computation to be carried out in the corresponding
 * extension of the module by the group is returned. For the extension
 * itself, call ExtensionOfModuleSGA
 */
 local K, d, invar, nr, z2v, gens, w, nsg, lv, k;

  K := Integers();
  d := CM`dim;
  invar:=CM`invar;
  nr := #Relations(CM`gf);

  z2v := RSpace(CM`ring,d*nr)!(((CM`H2)!seq) @@ CM`Z2toH2);
  gens := CM`Z2gens;
  isit, w := IsConsistent(gens,z2v);
  if not isit then
    error "Inconsistent data";
  end if;

  nsg := CM`nsgens;
  k := #[i : i in [1..d] | invar[i] ne invar[d] ];
  // The last nr*k coefficients in w are junk
  lv := Universe(nsg)!0;
  for i in [1..Ncols(w)-k*nr] do
    lv := lv + nsg[i]*w[i];
  end for;
  lv:=ReduceAbAutVec(invar,ElementToSequence(lv));

  return Matrix(K,#lv div d,d,lv);
end function;


EvaluateCocycleSGA := function(CM,emat,w)
/* emat should be a matrix defining an extension, as returned by
 * ExtensionOfModuleSGA. w should be a word in the generators of G.
 * v and ow are returned, where the word evaluates to v*ow where v
 * is in the module, and ow is a canonical word for a group element.
 */
  local GR, sg, sgi, sv, im, mats, imats, cmati, bo, tail, utail, nw,
        pt, ipt, ptno, d, v, ow, K, invar;
  GR := CM`gr;
  mats:=CM`mats; imats:=CM`imats;
  invar := CM`invar;
  K := Integers();
  d := #invar;
  sg := GR`sg;
  v := RSpace(K,d)!0; 
  n := 1;
  w := ElementToSequence(w);
  ow := [];
  for bno in [1..#GR`b] do
    bo := GR`bo[bno]; tail := GR`tail[bno]; utail := GR`utail[bno];
    sgi := GR`sgi[bno]; sv := GR`sv[bno];
    nw := [];
    pt:=bo[1];
    ipt:=pt;
    ptno:=1;
    cmati := IdentityMatrix(K,d);

    for g in w do
      if g gt 0 then
        sgno := Position(sgi,g);
        nw := nw cat tail[ptno][sgno];
        utno := utail[ptno][sgno];
        if utno gt 0 then
          v +:= emat[utno]*cmati;
        end if;
        for i in tail[ptno][sgno] do
           if i gt 0 then cmati := imats[i]*cmati;
           else cmati := mats[-i]*cmati;
           end if;
           cmati := ReduceAbAutMat(invar,cmati);
        end for;
        ipt := ipt ^ sg[g];
        ptno := Position(bo,ipt);
      else
        sgno := Position(sgi,-g);
        ipt := ipt ^ (sg[-g]^-1);
        ptno := Position(bo,ipt);
        nw := nw cat SWInv(tail[ptno][sgno]);
        for i in SWInv(tail[ptno][sgno]) do
           if i gt 0 then cmati := imats[i]*cmati;
           else cmati := mats[-i]*cmati;
           end if;
           cmati := ReduceAbAutMat(invar,cmati);
        end for;
        utno := utail[ptno][sgno];
        if utno gt 0 then
          v -:= emat[utno]*cmati;
        end if;
      end if;
    end for;
    w := nw;
    ow := SVWordH(sg,sv,bo,ipt) cat ow;
  end for;

  v := ReduceAbAutVec(invar,v);

  return v, ow;
end function;

TwoCocycleSGA := function(CM,s)
  /* returns a two-cocycle G x G -> M corresponding to extensions
   * defined by sequence s.
   */
  local GR,TC,emat;
  emat := MatrixOfExtensionSGA(CM, s);
  GR := CM`gr;

  TC := function(gtp)
  /* g1,g2 should be elements of G = CM`gr`gp.
   * First canonical words w1, w2, w3 in the strong generators for
   * g1, g2 and g1*g2 are computed using SGWordH.
   * The value m of the 2-cocycle - i.e. that m in M such that
   * w1*w2 = w3*m is returned.
   */
   local GR, w1, w2, w3, m, s, g1, g2;
   GR := CM`gr;
   g1 := gtp[1];
   g2 := gtp[2];
   w1 := SGWordH(GR,g1);
   w2 := SGWordH(GR,g2);
   w3 := SGWordH(GR,g1*g2);
   m,s := EvaluateCocycleSGA(CM,emat,SWInv(w3) cat w1 cat w2);
   assert s eq [];
   return m;
  end function;
  return TC;
end function;

IdentifyTwoCocycleSGA := function(CM,TC)
/* Here TC must be a function of 2-variables defining a two-cycle
 * The corresponding element of CM`H2 is returned.
 * For each relator w of G, we usr the two-cocycle to evaluate  w in M,
 * then cat all the values together to give a vector which identifies.
 * the required element of H2.
 */
  local K, Z, V, catrv, w, rv, suff, g, F, FtoG, invwds, mats, cmat, invar, dim,
        G, TC1;

  mats := CM`mats; imats := CM`imats; invar:=CM`invar; dim := #invar;
  Z := Integers();
  K := CM`ring;
  V := RSpace(Z,dim);

  //We first have to sort out terms for inverses of generators
  F := CM`gr`gf;
  FtoG := CM`gr`f2p;
  G := CM`gr`gp;
  invwds := [];
  for i in [1..Ngens(F)] do
    g := FtoG(F.i);
    invwds[i] := -(V!TC(<g,g^-1>));
  end for;
  TC1 := V!TC(<Id(G),Id(G)>);

  catrv := [];
  suff := Id(F) @ FtoG;
  cmat := mats[1]^0;
  for r in Relations(F) do
    w := ElementToSequence(LHS(r)*RHS(r)^-1);
    rv := V!0;
    for j in Reverse(w) do
      if j gt 0 then
        g := F.j @ FtoG;
        rv +:= V!TC(<g, suff>);
        suff := g*suff;
        cmat := mats[j]*cmat;
      else
        rv +:= (invwds[-j] -TC1)*cmat;
        g := F.j @ FtoG;
        rv +:= V!TC(<g, suff>);
        suff := g*suff;
        cmat := imats[-j]*cmat;
      end if;
    end for;
    rv := ReduceAbAutVec(invar,rv);
    catrv := catrv cat ElementToSequence(rv);
  end for;
  catrv := RSpace(Integers(),#catrv)!catrv;
  if not catrv in CM`Z2 then
    error "Input to IdentifyTwoCocycle is not a cocycle";
  end if;

  return catrv @ CM`Z2toH2;
end function;

IsTwoCoboundarySGA := function(CM,TC)
/* Here TC must be a function of 2-variables defining a two-cycle
 * If it is a two coboundary, then a 1-cocycle OC is returned
 * such that TC(<g1,g2>) = OC(<g1>)^g2 + OC(<g2>) - OC(g1g2>). 
 * For each relator w of G, we usr the two-cocycle to evaluate  w in M,
 * then cat all the values together to give a vector which identifies.
 * the element of H2.
 */
  local K, Z, V, catrv, w, rv, suff, g, F, FtoG, invwds, mats, cmat, invar, dim,
        d, G, ng, genims, OC, sg, TC1;

  mats := CM`mats; imats := CM`imats; invar:=CM`invar; dim := #invar;
  Z := Integers();
  K := CM`ring;
  V := RSpace(Z,dim);

  //We first have to sort out terms for inverses of generators
  F := CM`gr`gf;
  FtoG := CM`gr`f2p;
  G := CM`gr`gp;
  invwds := [];
  for i in [1..Ngens(F)] do
    g := FtoG(F.i);
    invwds[i] := -(V!TC(<g,g^-1>));
  end for;
  TC1 := V!TC(<Id(G),Id(G)>);

  catrv := [];
  suff := Id(F) @ FtoG;
  cmat := mats[1]^0;
  for r in Relations(F) do
    w := ElementToSequence(LHS(r)*RHS(r)^-1);
    rv := V!0;
    for j in Reverse(w) do
      if j gt 0 then
        g := F.j @ FtoG;
        rv +:= V!TC(<g, suff>);
        suff := g*suff;
        cmat := mats[j]*cmat;
      else
        rv +:= (invwds[-j] - TC1)*cmat;
        g := F.j @ FtoG;
        rv +:= V!TC(<g, suff>);
        suff := g*suff;
        cmat := imats[-j]*cmat;
      end if;
    end for;
    rv := ReduceAbAutVec(invar,rv);
    catrv := catrv cat ElementToSequence(rv);
  end for;
  catrv := Vector(K, catrv);
  isc, v := IsConsistent(CM`cem, catrv);
  if not isc then return false, _; end if;

  /* Need to lop off the unwanted end of v and spliut up into vectors over Z. */
  d := CM`dim;
  V := RSpace(Z,d);

  //now define associated 1-cochain
  ng := Ngens(CM`gf);
  v := Eltseq(v);
  genims := [ V!(v[(i-1)*d+1 .. i*d]) : i in [1..ng] ];
  sg := CM`gr`sg;

  OC := function(gtp)
    local w, cmat, ans, g;
    g := gtp[1];
    if g eq Id(G) then return TC1; end if;
    w := ElementToSequence(SGWordH(CM`gr,g));
    cmat := IdentityMatrix(Z,d);
    ans := V!0;
    g := Id(G);
    //scan from right hand end
    first := true;
    for k in Reverse(w) do
      if k lt 0 then
        ans := ans + (TC1 + V!TC( <sg[-k],sg[-k]^-1>) )*cmat;
        cmat := imats[-k]*cmat;
        ans := first  select ans - genims[-k]*cmat
                   else ans - genims[-k]*cmat - V!TC(<sg[-k]^-1,g>);
        g := sg[-k]^-1*g;
      else
        ans := first  select ans + genims[k]*cmat
                   else ans + genims[k]*cmat - V!TC(<sg[k],g>);
        g := sg[k]*g;
        cmat := mats[k]*cmat;
      end if;
      first := false;
    end for;
    return ReduceAbAutVec(invar,ans);
  end function;

  return true, OC;
end function;

ExtensionOfModuleSGA := function(CM,seq)
/* CM`H2 should have been computed already with SecondCohomologyGroup.
 * seq should be as in MatrixOfExtensionSG.
 * A presentation of a corresponding extension of the module by the
 * group is returned.
 */
 local invar, G, mats, imats, Z, gens, w, lv, ng, RG, nr, d, emat,
       F, rels, rel, phi, E, A;

  emat := MatrixOfExtensionSGA(CM, seq);
  G:=CM`gf;
  invar:=CM`invar;
  mats:=CM`mats; imats:=CM`imats;
  Z := Integers();
  ng := Ngens(G);
  RG := Relations(G);
  nr := #RG;
  d := #invar;

  //Now we can construct the extension.
  F := FreeGroup(ng+d);
  rels := [];
  for i in [1..d] do
    Append(~rels,(F.(ng+i))^invar[i]);
  end for;
  for i in [1..d] do for j in [i+1..d] do
    Append(~rels,(F.(ng+i),F.(ng+j)));
  end for; end for;
  for i in [1..ng] do for j in [1..d] do
    w:=Id(F);
    for k in [1..d] do
      w := w * (F.(ng+k))^mats[i][j][k];
    end for;
    Append(~rels,F.i^-1*F.(ng+j)*F.i*w^-1);
  end for; end for;
  phi := hom<G->F | [F.i : i in [1..ng]] >;
  for k in [1..nr] do
    rel := phi(LHS(RG[k])*RHS(RG[k])^-1);
    for i in [1..d] do
      rel := rel*F.(ng+i)^-emat[k][i];
    end for;
    Append(~rels,rel);
  end for;

  E := quo<F|rels>;
  //Now we provide a normal form function for E using EvaluateCocycleSGA.
  E`NormalForm := function(w) //put word w in E into normal form
    local ww, V, v, mat;
    //first move acting generators to left to give ww.
    w := ElementToSequence(w);
    V := RSpace(Z,d);
    v := V!0;
    mat := mats[1]^0;
    ww := [];
    for g in w do
      if Abs(g) le ng then
        Append(~ww,g);
        v := g gt 0 select v*mats[g] else v*imats[-g];
        mat := g gt 0 select mat*mats[g] else mat*imats[-g];
      else
        v := g gt 0 select v+V.(g-ng) else v-V.(-g-ng);
      end if;
    end for;
    v1, ww := EvaluateCocycleSGA(CM,emat,ww);
    // unfortunately EvaluateCocycleSGA collects v1 to left!
    v1 := v1 * ReduceAbAutMat(invar,mat);
    v := ReduceAbAutVec(invar,v + v1);
    w := Id(E);
    for g in ww do w := w * E.g; end for;
    for i in [1..d] do w := w * E.(ng+i)^(Z!v[i]); end for;
    return w;
  end function;

  A := AbelianGroup(CM`invar);
  E`Projection :=
   hom< E -> CM`gr`gp | [g: g in CM`gr`sg] cat [Id(CM`gr`gp) : i in [1..d]] >;
  E`Injection := hom< A-> E |  [E.(ng+i): i in [1..d]] >;
  return E, E`Projection, E`Injection;
end function;

SplitExtensionSGA := procedure(CM)
/* Sets CM`SplitExtension to be  finite presentation of a split extension
 * of module by G. Strong generators of G come first.
 */
  local G, invar, mats, imats, Z, p, d, ng, F, rels, phi, E;

  if assigned CM`SplitExtension then return; end if;
  G:=CM`gf;
  mats:=CM`mats; imats:=CM`imats; invar := CM`invar;
  Z:=Integers();
  d := CM`dim;
  ng := Ngens(G);
  F := FreeGroup(ng+d);
  rels := [];
  for i in [1..d] do if invar[i] ne 0 then
    Append(~rels,(F.(ng+i))^invar[i]);
  end if; end for;
  for i in [1..d] do for j in [i+1..d] do
    Append(~rels,(F.(ng+i),F.(ng+j)));
  end for; end for;
  for i in [1..ng] do for j in [1..d] do
    w:=Id(F);
    for k in [1..d] do
      w := w * (F.(ng+k))^(Z!mats[i][j][k]);
    end for;
    Append(~rels,F.i^-1*F.(ng+j)*F.i*w^-1);
  end for; end for;
  phi := hom<G->F | [F.i : i in [1..ng]] >;
  for r in Relations(G) do
    Append(~rels,phi(LHS(r)*RHS(r)^-1));
  end for;
  E := quo<F | rels>;
  //Now we provide a normal form function for Es using EvaluateCocycleSG.
  E`NormalForm := function(w) //put word w in E into normal form
    local ww, V, v, p, sg;
    //first move acting generators to left to give ww.
    w := ElementToSequence(w);
    V := RSpace(Z,d);
    v := V!0;
    ww := [];
    for g in w do
      if Abs(g) le ng then
        Append(~ww,g);
        v := g gt 0 select v*mats[g] else v*imats[-g];
      else
        v := g gt 0 select v+V.(g-ng) else v-V.(-g-ng);
      end if;
    end for;
    v := ReduceAbAutVec(invar,v);
    // need permutation for ww
    sg := CM`gr`sg;
    p := Id(CM`gr`gp);
    for g in ww do p := g gt 0 select p*sg[g] else p*sg[-g]^-1; end for;
    ww := SGWordH(CM`gr,p);
    w := Id(E);
    for g in ww do w := w * E.g; end for;
    for i in [1..d] do w := w * E.(ng+i)^(Z!v[i]); end for;
    return w;
  end function;

  A := AbelianGroup(CM`invar);
  E`Projection :=
   hom< E -> CM`gr`gp | [g: g in CM`gr`sg] cat [Id(CM`gr`gp) : i in [1..d]] >;
  E`Injection := hom< A-> E |  [E.(ng+i): i in [1..d]] >;
  CM`SplitExtension := E;
end procedure;

SplitExtensionPermRepSGA := procedure(CM)
/* Find faithful perm. rep. of CM`SplitExtension.
 * The semidirect product of M by G is returned as a permutation group
 * with two orbits of lengths |M|, deg(G), where the action on the first
 * orbit has M as a regular normal subgroup, and the action on the
 * second is the same as G.  The images of G, M in this
 * permutation group are also returned.
 */
  local E, G, sg, M, V, ME, H, d, invar, Z, mats, gens, gen, deg;

  if assigned CM`SplitExtensionPermRep then return; end if;
  vprint ModCoho: "Finding permutation representation of split extension";
  if not assigned CM`SplitExtension then
    SplitExtensionSGA(CM);
  end if;
  E := CM`SplitExtension;
  invar := CM`invar;
  d := CM`dim;
  Z:=Integers();
  V := RSpace(Z,d);
  M := quo < V | [ invar[i]*V.i : i in [1..d]] >;
  ME := [ v : v in M ];
  G:=CM`gr`gp; sg := CM`gr`sg;
  if Category(G) eq GrpMat then // have to find faithful perm. rep.
    phi,G := PermutationRepresentation(G);
    sg := [phi(g) : g in sg];
  end if;
  mats:=CM`mats;

  /* first generators of G in action on M */
  gens := [];
  for i in [1..#sg] do
    gen :=
      [ Position(ME,M!ReduceAbAutVec(invar,ME[j]*mats[i])) : j in [1..#ME] ]
            cat [ #ME + j^sg[i] : j in [1..Degree(G)] ];
    Append(~gens, gen );
  end for;
  /* next generators of M */
  for i in [1..d] do
    gen :=
      [ Position(ME,M!ReduceAbAutVec(invar,ME[j]+M.i)) : j in [1..#ME] ] cat
                                       [ #ME + j : j in [1..Degree(G)] ];
    Append(~gens, gen );
  end for;

  deg := #ME + Degree(G);
  CM`SplitExtensionPermRep := sub< Sym(deg) | gens >;
  vprint ModCoho: "Found representation of degree",deg;

end procedure;


AutGroupOnH2SGA := function(CM)
/* Compute action of the automorphism group of the pair (G,Module) (obtained
 * from automorphism group of split extension of module by group) on
 * H^2. Return result as sequence of matrices.
 */
  local invar, G, mats, imats, Z, ng, RG, nr, d, E, P, Q, M, EtoP, EtoG, A,
        H2, H2invar, dH2, H2mats, H2mat, Gtriv, Mims, Mactmat, w, Gims, Gaut,
        Relims, seq, emat, lv, Relimvals, MtoE, K, Z2deg, V1, V2;

  if not assigned CM`H2 then 
     SecondCohomologyGroupSGA(CM);
  end if;
  if not assigned CM`SplitExtensionPermRep then
     if #CM`gr`gp lt 100 then
       SplitExtensionPermRepA(CM);
     else
       SplitExtensionPermRepSGA(CM);
     end if;
  end if;
  invar:=CM`invar; G:=CM`gf;
  mats:=CM`mats; imats:=CM`imats;
  H2 := CM`H2;
  H2invar := Moduli(H2);
  ChangeUniverse(~H2invar,Integers());
  d := CM`dim;
  dH2 := #H2invar;
  res := invar[d];
  if res ne 0 then
    for i in [1..#H2invar] do
      if H2invar[i] eq 0 then H2invar[i] := res; end if;
    end for;
  end if;
  Z := Integers();
  ng := Ngens(G);
  RG := Relations(G);
  nr := #RG;
  K := CM`ring;

  E := CM`SplitExtension;
  EtoG := hom < E->G | [G.i : i in [1..ng]] cat [Id(G) : i in [1..d]] >;
  P := CM`SplitExtensionPermRep;
  EtoP := hom < E->P | [P.i : i in [1..Ngens(E)]] >;
  Q := sub<P|[P.i : i in [1..ng]]>;
  M := sub<P|[P.i : i in [ng+1..ng+d]]>;
  MtoE := hom< M->E | [E.(ng+i) : i in [1..d]] >;
  vprint ModCoho: "Computing automorphism group of split extension";
  A := AutGpSG(P,Q,M);
  vprint ModCoho: "Done - order =",#A;

  H2mats := []; // list of matrices of degree H2invar giving action
  Z2deg := Degree(CM`Z2);
  V1 := RSpace(K,Z2deg);
  V2 := RSpace(Z,dH2);

  for agno in [1 .. Ngens(A)] do
    if IsInner(A.agno) then continue; end if;
    //If actions on P/M and M are trivial then we can skip it 
    Gtriv := true;
    for gno in [1..ng] do
      if not P.gno^-1 * (P.gno @ A.agno) in M then
         Gtriv := false;
         break;
      end if;
    end for;
    if Gtriv then
      if [M.i : i in [1..d]] eq [M.i @ A.agno : i in [1..d]] then
        //action on M is also trivial
          continue agno;
       end if;
    end if;
    // need action of A.agno on M
    Mims := [P.i @ A.agno @ MtoE : i in [ng+1..ng+d]];
    Mactmat := Matrix(Z,d,d,[0:i in [1..d^2]]);
    for r in [1..d] do
      w := Mims[r];
      for j in [1..#w] do
        g := GeneratorNumber(Subword(w,j,1));
        if g gt 0 then Mactmat[r][g-ng] +:=1;
        else Mactmat[r][-g-ng] -:=1;
        end if;
      end for;
    end for;
    Mactmat := ReduceAbAutMat(invar,Mactmat);
    //If action on P/M is nontrivial need action of A.agno^-1 on group relators.
    if not Gtriv then
      Gims := [P.i @ (A.agno^-1) @@ EtoP @ EtoG : i in [1..ng]];
      Gaut := hom<G->G | Gims >;
      Relims := [ (LHS(r)*RHS(r)^-1) @ Gaut : r in RG ];
    end if;

    H2mat := Matrix(Z,dH2,dH2,[0: i in [1..dH2^2]]);
   // the matrix specifying the action of A.agno on H2, which we now compute
    for H2gno in [1..dH2] do
      seq := [0: i in [1..dH2]]; seq[H2gno]:=1;
      emat := MatrixOfExtensionSGA(CM,seq);
     if Gtriv then
        lv := &cat [ElementToSequence(emat[i]*Mactmat) : i in [1..nr]];
     else
        Relimvals := [EvaluateCocycleSGA(CM,emat,w) : w in Relims];
        lv := &cat [ElementToSequence(Relimvals[i]*Mactmat) : i in [1..nr]];
     end if; 
     //H2mat[H2gno] := V2!((V1!lv) @ CM`Z2toH2);
     H2mat[H2gno] := lv @ CM`Z2toH2;
    end for;

    if H2mat ne IdentityMatrix(Z,dH2) then
      Append(~H2mats,H2mat);
    end if;
  end for;

  return H2mats;
end function;

DistinctExtensionsSGA := function(CM)
/* Compute orbit representatives of this action, and return
 * a list of presentations of the corresponding extensions.
 */
  local  H2mats,  Z, H2invar, invar, cd, V, H2elts, celt, lev, had,
         orbreps, orb, ct, rep, imrep, d, dH2, res;

  if not assigned CM`H2 then
     SecondCohomologyGroupSGA(CM);
  end if;
  if #(CM`H2) eq 0 then
    SplitExtensionSGA(CM); return [CM`SplitExtension];
  end if;
  H2mats := AutGroupOnH2SGA(CM);
  H2invar := Moduli(CM`H2);
  ChangeUniverse(~H2invar,Integers());
  d := CM`dim;
  invar := CM`invar;
  cd := #H2invar;
  res := invar[d];
  if res ne 0 then
    for i in [1..cd] do
      if H2invar[i] eq 0 then H2invar[i] := res; end if;
    end for;
  end if;
  Z := Integers();
  V := RSpace(Z,cd);
  /* First we have to make a list of all elements of the abelian group
   * define by H2invar.
   */
  celt := [0: i in [1..cd]];
  H2elts := {@ V!celt @};
  lev := cd;
  while lev gt 0 do
    celt[lev] +:= 1;
    if celt[lev] eq H2invar[lev] then
      celt[lev] := 0;
      lev -:=1;
      continue;
    end if;
    Include(~H2elts,V!celt);
    lev := cd;
  end while;

  //now work out orbits of action.
  had := [ false : i in [1..#H2elts] ];
  had[1] := true;
  orbreps := [1];
  for H2eltno in [2..#H2elts] do
    if had[H2eltno] then
      continue;
    end if;
    Append(~orbreps,H2eltno);
    orb := [H2eltno];
    ct := 1;
    while ct le #orb do
      rep := orb[ct];
      had[rep] := true;
      for mat in H2mats do
        imrep := Position(H2elts,ReduceAbAutVec(H2invar,H2elts[rep]*mat));
        if not had[imrep] then
          had[imrep] := true;
          Append(~orb,imrep);
        end if;
      end for;
      ct +:= 1;
    end while;
  end for;

  return
    [ ExtensionOfModuleSGA(CM,ElementToSequence(H2elts[x])) : x in orbreps ];

end function;

