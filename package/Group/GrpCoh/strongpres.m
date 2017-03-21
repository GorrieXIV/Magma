freeze;

import "fp.m": CheckRelations;

forward SVWordH, SGWordH, SVPermutationH;
MakeGroupRecordSG := function(G : sgwords:=false)
  local SGF, GR, nb, sg, nsg, sgi, sv, bo, pt, ipt, tail, utail, sgword,
        gct, w, reli, rel, rels, nr, g, pos, newpos;
  SGF := recformat<
             gp: GrpPerm,
             gf: GrpFP,
            f2p: Map,
             sg: SetIndx,
            sgw: SeqEnum,
             sv: SeqEnum,
              b: SeqEnum,
             bo: SeqEnum,
            sgi: SeqEnum, //sgi[i] is list of nos. of strong gens lying in G(i)
           reli: SeqEnum, //reli[i] is list of relation nos. of rels. in G(i)
         sgword: SeqEnum,
           tail: SeqEnum,
          utail: SeqEnum,
        modvars: RngIntElt >;
  GR := rec<SGF | gp:=G >;
  GR`gf, GR`f2p := FPGroupStrong(G);
  // The case of no strong generators or base points needs special treatment!
  if Base(G) eq [] then ChangeBase(~G,[Labelling(G)[1]]); end if;
  GR`b := Base(G);
  nb := #GR`b;
  GR`sg := {@ GR`f2p(GR`gf.i) : i in [1..Ngens(GR`gf)] @};
/*
  if #GR`sg eq 0 and Ngens(GR`gf) eq 1 then
    GR`sg := {@ Id(G) @};
  end if;
  if  GR`sg ne {@ GR`f2p(GR`gf.i) : i in [1..Ngens(GR`gf)] @} then
     error "FPGroupStrong is misbehaving";
  end if;
  GR`sg := StrongGenerators(G);
*/
  sg := GR`sg;
  nsg := #GR`sg;
  if sgwords then
      /* We need the strong generators as words in the original generators
       * in order to compute their matrices later. Could be inefficient!
       */
      F,phi := FPGroup(G);
      GR`sgw := [ s@@phi : s in sg];
  end if;
  GR`bo := BasicOrbits(G);
  GR`sv := SchreierVectors(G);
  rels := Relations(GR`gf);
  nr := #rels;
  GR`sgi:=[[1..nsg]];
  for bno in [2..nb] do
    GR`sgi[bno] := [k : k in [1..nsg] | GR`sg[k] in BasicStabilizer(G,bno)];
  end for;
  tail:=[]; utail:=[]; sgword:=[];
  gct := nr;
  for bno in [nb..1 by -1] do
    tail[bno]:=[]; utail[bno]:=[]; sgword[bno]:=[];
    bo := GR`bo[bno];
    sv := GR`sv[bno];
    sgi := GR`sgi[bno];
    for bono in [1..#bo] do
      tail[bno][bono]:=[]; utail[bno][bono]:=[];
      pt := bo[bono];
      sgword[bno][bono] := SVWordH(sg,sv,bo,pt);
      for sgno in [1..#sgi] do
        ipt := pt^sg[sgi[sgno]];
        iptno := Position(bo,ipt);
        if sv[iptno] eq sgi[sgno] or sv[bono] eq -sgi[sgno] then
          //This image is a definition
          tail[bno][bono][sgno] := [Integers()|];
          utail[bno][bono][sgno] := 0;
        else
          tail[bno][bono][sgno] := SGWordH(GR,
  SVPermutationH(sg,sv,bo,pt)*sg[sgi[sgno]]*SVPermutationH(sg,sv,bo,ipt)^-1);
          if bono eq 1 and bno lt nb and
                       Position(GR`sgi[bno+1],sgi[sgno]) gt 0 then
            utail[bno][bono][sgno] :=
                      utail[bno+1][bono][Position(GR`sgi[bno+1],sgi[sgno])];
          else
            gct+:=1;
            utail[bno][bono][sgno] := gct;
          end if;
        end if;
      end for;
    end for;
  end for;
  GR`tail:=tail; GR`utail:=utail; GR`sgword:=sgword;
  GR`modvars := gct;
  reli := [[1..nr]];
  for i in [2..nb] do reli[i]:=[]; end for;
  for i in [1..nr] do
    rel := LHS(rels[i])*RHS(rels[i])^-1;
    // see where rel sits in the stabilizer chain
    pos := nb;
    for j in [1.. #rel] do
      g := Abs(GeneratorNumber(Subword(rel,j,1)));
      newpos := Max([i: i in [1..nb] | g in GR`sgi[i] ]);
      if newpos lt pos then pos := newpos; end if; 
    end for;
    for j in [2..pos] do Append(~reli[j],i); end for;
  end for;
  GR`reli := reli;
  return GR;
end function;

SWInv := func < x | [ -y : y in Reverse(x) ] >;
              
SVWordH := function(sg,sv,bo,pt)
/* returns inverse of what SVWord should return, as an integer sequence
 * i.e. a word in strong generators taking base point of basic orbit bo to pt.
 * sv is Schreier vector, bo basic orbit at relevant level
 * sg list of strong generators of group
 */
   local ppt, s, ans;
   ppt := Position(bo,pt);
   s := sv[ppt];
   ans := [];
   while s ne 0 do
     Append(~ans,-s);
     pt := s gt 0 select pt^(sg[s]^-1) else pt^(sg[-s]);
     ppt := Position(bo,pt);
     s := sv[ppt];
   end while;
   return SWInv(ans);
end function;
   
SVPermutationH := function(sg,sv,bo,pt)
/* returns inverse of what SVPermutation should return.  i.e.
 * a permutation (or matrix) at level of basic orbit bo taking base point to pt.
 * sv is Schreier vector, bo basic orbit at relevant level
 * sg list of strong generators of group
 */
   local ppt, s, ans;
   ppt := Position(bo,pt);
   s := sv[ppt];
   ans := sg[1]^0;
   while s ne 0 do
     ans := s gt 0 select ans*sg[s]^-1 else ans*sg[-s];;
     pt := s gt 0 select pt^(sg[s]^-1) else pt^(sg[-s]);
     ppt := Position(bo,pt);
     s := sv[ppt];
   end while;
   return ans^-1;
end function;
   
SGWordH := function(GR,elt)
// The word in the strong generators for group element elt of GR`G
// returned as integer sequence
  local ans, ipt, nb;
  ans := [];
  nb := #GR`b;
  for bno in [1..nb] do
    ipt := GR`b[bno]^elt;
    ans :=  SVWordH(GR`sg,GR`sv[bno],GR`bo[bno],ipt) cat ans;
    elt := elt * SVPermutationH(GR`sg,GR`sv[bno],GR`bo[bno],ipt)^-1;
  end for;
  return ans;
end function;

MakeModuleRecordSG := function(G,M)
/* This is called prior to calling any of the cohomological functions,
 * and returns a cohomology module with fields for the various objects
 * that may get computed.
 * G is a permutation group.
 * M should be a module for G.
 * The cohomological functions take this record as argument.
 */
  local GR, R, sg, r, mats, imats;

  R := Representation(M);
  GR := MakeGroupRecordSG(G);
  sg := GR`sg;
  mats := [ R(sg[i]) : i in [1..#sg] ];
  imats := [ m^-1 : m in mats ];
  r := EmptyCohomologyModule();
  r`modtype := ModGrp;
  r`gptype := GrpPerm;
  r`gr := GR;
  r`module := M;
  r`mats := mats; r`imats := imats;
  r`dim := Dimension(M);
  r`ring := BaseRing(M);
  r`gf := GR`gf;
  r`gftoG := GR`f2p;

  if not CheckRelations(r`gf,mats : imats:=imats) then
    error "Matrices do not satisfy relations on strong generators";
  end if;

  return r;
end function;

ZeroCohomologyGroupG := procedure(CM)
  local K, d, mats, X;
  if assigned CM`H0 then return; end if;
  K := CM`ring;
  d := CM`dim;
  mats := CM`mats;

  X := HorizontalJoin([x - 1: x in mats]);
  CM`csm := X;
  CM`Z0 := Nullspace(X);
  CM`H0, CM`Z0toH0 := quo< CM`Z0 | sub<CM`Z0|> > ;

end procedure;

ZeroCocycleG := function(CM,s)
  local d, K;
  d := CM`dim;
  K := CM`modtype eq GrpAb select IntegerRing() else CM`ring;
  return func < tp | RSpace(K,d)!(((CM`H0)!s) @@ CM`Z0toH0) >;
end function;

IdentifyZeroCocycleG := function(CM,s)
  s := s(<>);
  if not s in CM`Z0 then
    error "Input to IdentifyZeroCocycle is not a cocycle";
  end if;
  return s @ CM`Z0toH0;
end function;

FirstCohomologyGroupG := procedure(CM)
  ZeroCohomologyGroupG(CM);
  if assigned CM`H1 then return; end if;
  MF := GModule(CM`gf,CM`mats);
  CM`cem := ComplementEquationsMatrix(MF);
  CM`Z1 := Nullspace(CM`cem);
  CM`B1 := Image(CM`csm);
  CM`H1, CM`Z1toH1 := quo< CM`Z1 | CM`B1 >;
end procedure;

OneCocycleSG := function(CM,s)
//returns a function G-> module
  local nselt, OC, d, ng, K, GR, mats, imats, V, genims;
  nselt := ElementToSequence(((CM`H1)!s) @@ CM`Z1toH1);
  ng := Ngens(CM`gf);
  GR := CM`gr;
  d := CM`dim;
  K := CM`ring;
  mats := CM`mats; imats:=CM`imats;
  V := RSpace(K,d);
  //find images of one-cocyle on generators
  genims := [ V!(nselt[(i-1)*d+1 .. i*d]) : i in [1..ng] ];
  OC := function(gtp) //gtp = <g>
    local w, cmat, ans, g;
    g := gtp[1];
    w := ElementToSequence(SGWordH(GR,g));
    cmat := IdentityMatrix(K,d);
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
    return ans;
  end function;

  return OC;
end function;

IdentifyOneCocycleSG := function(CM,OC)
  //identify from action on strong generators
  local sg, s;
  sg := CM`gr`sg;
  s := &cat [ ElementToSequence(OC(<sg[i]>)) : i in [1..#sg] ];
  s := RSpace(CM`ring,#s)!s;
  if not s in CM`Z1 then
    error "Input to IdentifyOneCocycle is not a cocycle";
  end if;
  return s @ CM`Z1toH1;
end function;

IsOneCoboundarySG := function(CM,OC)
//if so then return 0-cochain z such that OC(<g>) = z(<>)^(1-g) for g in G
  local ng, d, K, isc, sg, v, w;

  d := CM`dim;
  K := CM`ring;

  sg := CM`gr`sg;
  w := &cat [ ElementToSequence(OC(<sg[i]>)) : i in [1..#sg] ];
  w := Vector(K, w);
  isc, v := IsConsistent(CM`csm, w);
  if not isc then return false, _; end if;
  return true, func< tp | -v >;
end function;

TraceWord := procedure(w,K,d,mats,imats,sg,sgi,bo,bono,tail,utail,colno,~X,~ntw)
   local pt, ipt, sgno, ptno, cmati, utno;
        ntw := [];
        pt:=bo[bono];
        ipt:=pt;
        ptno:=bono;
        cmati := IdentityMatrix(K,d);
        for g in w do
          if g ge 0 then
            sgno := Position(sgi,g);
            ntw cat:= tail[ptno][sgno];
            utno := utail[ptno][sgno];
            if utno gt 0 then
              InsertBlock(~X,ExtractBlock(X,d*(utno-1)+1,colno+1,d,d)+cmati,
                                                          d*(utno-1)+1,colno+1);
              //for k in [1..d] do for l in [1..d] do
                //X[d*(utno-1)+k][colno+l] +:= cmati[k][l];
              //end for; end for;
            end if;
            for i in tail[ptno][sgno] do
               if i gt 0 then cmati := imats[i]*cmati;
               else cmati := mats[-i]*cmati;
               end if;
            end for;
            ipt := ipt ^ sg[g];
            ptno := Position(bo,ipt);
          else
            sgno := Position(sgi,-g);
            ipt := ipt ^ (sg[-g]^-1);
            ptno := Position(bo,ipt);
            ntw cat:= SWInv(tail[ptno][sgno]);
            for i in SWInv(tail[ptno][sgno]) do
               if i gt 0 then cmati := imats[i]*cmati;
               else cmati := mats[-i]*cmati;
               end if;
            end for;
            utno := utail[ptno][sgno];
            if utno gt 0 then
              InsertBlock(~X,ExtractBlock(X,d*(utno-1)+1,colno+1,d,d)-cmati,
                                                          d*(utno-1)+1,colno+1);
              //for k in [1..d] do for l in [1..d] do
               // X[d*(utno-1)+k][colno+l] -:= cmati[k][l];
              //end for; end for;
            end if;
          end if;
        end for;
        if ipt ne pt then
          print w, bo, bono;
          error "Tracing error!";
        end if;
end procedure;

SecondCohomologyGroupSG := procedure(CM : QmodZ := false)
/* 
 * SecondCohomologyGroupSG computes a matrix and stores its nullspace, which
 * is isomorphic to Z^2(G,M), then computes B2, H2.
 */

  local  GR, mats, imats, K, d, ng, nr, nb, RG, ncols, X, colno, sgw,
    sgwmat, tail, utail, sg, reli, tw, ntw, bo, pt, w, h, gens, nsgens,
    V1, V2, V3;

  if QmodZ and assigned CM`QmodZH2 then return; end if;
  if assigned CM`H2 then return; end if;
  FirstCohomologyGroupG(CM);
  mats:=CM`mats; imats:=CM`imats;
  K := BaseRing(mats[1]);
  d := CM`dim;
  GR:=CM`gr;
  sg:=GR`sg;
  nb:=#GR`b;

  RG := Relations(GR`gf);
  nr := #RG;

  /* Set up the matrix  X  where we will store the equations */
  ncols := &+ [ #GR`bo[i] * #GR`reli[i] * d : i in [1.. #GR`b] ];
  vprint ModCoho: "Setting up",ncols,"equations in",GR`modvars*d,"unknowns";
  X:=Hom(RSpace(K,GR`modvars*d),RSpace(K,ncols))!0;
  
  colno:=0;
  for bno in [nb..1 by -1] do
    sgw:=GR`sgword[bno];
    tail:=GR`tail[bno];
    utail:=GR`utail[bno];
    bo:=GR`bo[bno];
    reli:=GR`reli[bno];
    for bono in [1..#bo] do
      //Calculate inverse of action matrix
      sgwmat := IdentityMatrix(K,d);
      for i in SWInv(sgw[bono]) do
        if i gt 0 then sgwmat := sgwmat*mats[i];
        else sgwmat := sgwmat*imats[-i];
        end if;
      end for;
  
      for rno in reli do
        //Scan relation no. rno under relevant group element
        //The equations generated are numbers colno+1 .. colno+d.
        r := RG[rno]; w := ElementToSequence(LHS(r)*RHS(r)^-1);
        TraceWord(w,K,d,mats,imats,sg,GR`sgi[bno],
                                  bo,bono,tail,utail,colno,~X,~ntw);
        for j in [bno+1..nb] do
          tw:=ntw;
          TraceWord(tw,K,d,mats,imats,sg,GR`sgi[j],
                           GR`bo[j],1,GR`tail[j],GR`utail[j],colno,~X,~ntw);
        end for;

        /* The equations specify that the word in the Schreier generators
         * coming from the scanned relator is equal to the conjugate of
         * of the Schreier generator for that relator under the inverse of
         * group element number elt - sgwmat is the matrix for this inverse.
         */
        //rpos := relpos[rno];
        InsertBlock(~X,ExtractBlock(X,d*(rno-1)+1,colno+1,d,d)-sgwmat,
                                                          d*(rno-1)+1,colno+1);
        //for j in [1..d] do for k in [1..d] do
         // X[d*(rno-1)+j][colno+k] -:= sgwmat[j][k];
        //end for; end for;
        colno +:= d;
      end for;
    end for;
  end for;
  vprint ModCoho: "Done";

  if QmodZ then//computing H^2(G,M_QmodZ)
    F := SmithForm(X);
    rf := Rank(F);
    invar := [ F[i][i] : i in [1..rf] ];
    V := RSpace(Integers(), rf);
    CM`QmodZH2 := quo< V | [ invar[i]*V.i : i in [1..rf]] >;
    return;
  end if;

  //We won't store X itself, since it is very large - we only
  // need its nullspace.
  ns := Nullspace(X);
  vprint ModCoho: "Got Nullspace";
  V1 := RSpace(K,Nrows(X));
  nsgens := [ V1 | V1!(ns.i) : i in [1..Dimension(ns)]];
  CM`nsgens := nsgens;

  //To compute Z^2, we only need the first nr*d components of the
  //vectors in N.
  V2 := RSpace(K,d*nr);
  h := hom<V1->V2 |
              [V2.i : i in [1..d*nr]] cat [V2!0 : i in [d*nr+1..Nrows(X)]] >;
  for i in [1..#nsgens] do if h(nsgens[i]) eq 0 then
    error "Coefficient error";
  end if; end for;
  gens := [h(g) : g in nsgens];
  //gens := [h(nsgens[i]) : i in [1..#nsgens] | h(nsgens[i]) ne 0];
  //CM`nsgens := [V1 | nsgens[i] : i in [1..#nsgens] | h(nsgens[i]) ne 0];
  CM`Z2 := sub < V2 | gens >;
  // make gens into a matrix
  V3 := RSpace(K,#gens);
  CM`Z2gens := Hom(V3,V2)!(gens);
  vprint ModCoho: "Calculated Z2";
  CM`B2 := Image(CM`cem);
  CM`H2, CM`Z2toH2 := quo< CM`Z2 | CM`B2 >;
  vprint ModCoho: "Calculated H2";

end procedure;

MatrixOfExtensionSG := function(CM,seq)
/* CM`H2 should have been computed already with SecondCohomologyGroup.
 * seq should be an integer sequence representing an element of  CM`H2.
 * A matrix enabling computation to be carried out in the corresponding
 * extension of the module by the group is returned. For the extension
 * itself, call ExtensionOfModuleSG
 */
 local K, d, z2v, gens, w, nsg, lv;

  K := CM`ring;
  d := CM`dim;

  z2v := ((CM`H2)!seq) @@ CM`Z2toH2;
  gens := CM`Z2gens;
  isit, w := IsConsistent(gens,z2v);
  if not isit then
    error "Inconsistent data";
  end if;

  nsg := CM`nsgens;
  lv := ElementToSequence(&+ [Universe(nsg) | nsg[i]*w[i] : i in [1..#nsg] ]);

  return Matrix(K,#lv div d,d,lv);
end function;


EvaluateCocycleSG := function(CM,emat,w)
/* emat should be a matrix defining an extension, as returned by
 * MatrixOfExtensionSG. w should be a word in the strong generators of G.
 * v and ow are returned, where the word evaluates to v*ow where v
 * is in the module, and ow is a canonical word for a group element.
 */
  local GR, sg, sgi, sv, im, mats, imats, cmati, bo, tail, utail, nw,
        pt, ipt, ptno, d, v, ow;

  GR := CM`gr;
  mats:=CM`mats; imats:=CM`imats;
  K:=BaseRing(mats[1]);
  d := CM`dim;
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

  return v, ow;
end function;

TwoCocycleSG := function(CM,s)
  /* returns a two-cocycle G x G -> M corresponding to extensions
   * defined by sequence s.
   */
  local GR,TC,emat;
  emat := MatrixOfExtensionSG(CM, s);
  GR := CM`gr;

  TC := function(gtp)
  /* g1,g2 should be elements of G = CM`gr`gp.
   * First canonical words w1, w2, w3 in the strong generators for
   * g1, g2 and g1*g2 are computed using SGWordH.
   * The value m of the 2-cocycle - i.e. that m in M such that
   * w1*w2 = w3*m is returned.
   */
   local w1, w2, w3, m, s, g1, g2;
   g1 := gtp[1];
   g2 := gtp[2];
   w1 := SGWordH(GR,g1);
   w2 := SGWordH(GR,g2);
   w3 := SGWordH(GR,g1*g2);
   m,s := EvaluateCocycleSG(CM,emat,SWInv(w3) cat w1 cat w2);
   assert s eq [];
   return m;
  end function;
  return TC;
end function;

EvaluateRelator := function(CM, TC, w)
//The word w should be a relator in G
//Use 2-cocycle TC to evaluate it in M
  local K, V, G, rv, suff, g, F, FtoG, invwds, mats, imats, cmat, TC1;

  //We first have to sort out terms for inverses of generators
  F := CM`gr`gf;
  FtoG := CM`gr`f2p;
  G := CM`gr`gp;
  K := CM`ring;
  V := RSpace(K,CM`dim);
  invwds := [];
  for i in [1..Ngens(F)] do
    g := FtoG(F.i);
    invwds[i] := -(V!TC(<g,g^-1>));
  end for;
  TC1 := V!TC(<Id(G),Id(G)>);
  mats := CM`mats; imats:=CM`imats;
  cmat := IdentityMatrix(K,CM`dim);
  suff := Id(G);
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
  return Eltseq(rv);
end function;

IdentifyTwoCocycleSG := function(CM,TC)
/* Here TC must be a function of 2-variables defining a two-cycle
 * The corresponding element of CM`H2 is returned.
 * For each relator w of G, we use the two-cocycle to evaluate  w in M,
 * then cat all the values together to give a vector which identifies.
 * the required element of H2.
 */
  local catrv, w;

  catrv := [];
  for r in Relations(CM`gr`gf) do
    w :=  ElementToSequence(LHS(r)*RHS(r)^-1);
    catrv cat:= EvaluateRelator(CM, TC, w);
  end for;
  catrv := RSpace(CM`ring,#catrv)!catrv;
  if not catrv in CM`Z2 then
    error "Input to IdentifyTwoCocycle is not a cocycle";
  end if;

  return catrv @ CM`Z2toH2;
end function;

IsTwoCoboundarySG := function(CM,TC)
/* Here TC must be a function of 2-variables defining a two-cycle
 * If it is a two coboundary, then a 1-cochain OC is returned
 * such that TC(<g1,g2>) = OC(<g1>)^g2 + OC(<g2>) - OC(g1g2>). 
 * For each relator w of G, we usr the two-cocycle to evaluate  w in M,
 * then cat all the values together to give a vector which identifies.
 * the element of H2.
 */
  local  K, catrv, w, isc, v, d, G, ng, genims, OC, sg, TC1;

  catrv := [];
  for r in Relations(CM`gr`gf) do
    w := ElementToSequence(LHS(r)*RHS(r)^-1);
    catrv cat:= EvaluateRelator(CM, TC, w);
  end for;
  K := CM`ring;
  catrv := Vector(K, catrv);
  isc, v := IsConsistent(CM`cem, catrv);
  if not isc then return false, _; end if;

  d := CM`dim;
  V := RSpace(K, d);

  //now define associated 1-cochain
  ng := Ngens(CM`gf);
  v := Eltseq(v);
  genims := [ V!(v[(i-1)*d+1 .. i*d]) : i in [1..ng] ];
  G := CM`gr`gp;
  sg := CM`gr`sg;
  mats := CM`mats; imats:=CM`imats;
  TC1 := V!TC(<Id(G),Id(G)>);

  OC := function(gtp)
    local w, cmat, ans, g;
    g := gtp[1];
    if g eq Id(G) then return TC1; end if;
    w := ElementToSequence(SGWordH(CM`gr,g));
    cmat := IdentityMatrix(K,d);
    ans := V!0;
    g := Id(G);
    //scan from right hand end
    first := true;
    for k in Reverse(w) do
      if k lt 0 then
        ans := ans + (V!TC( <sg[-k],sg[-k]^-1>) + TC1 )*cmat;
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
    return ans;
  end function;

  return true, OC;
end function;

ExtensionOfModuleSG := function(CM,seq)
/* CM`H2 should have been computed already with SecondCohomologyGroup.
 * seq should be as in MatrixOfExtensionSG.
 * A presentation of a corresponding extension of the module by the
 * group is returned.
 */
 local invar, G, mats, imats, finite, p, K, gens, w, g, RG, nr,
       d, emat, F, rels, rel, phi, Z, E, A;

  emat := MatrixOfExtensionSG(CM, seq);
  Z := Integers();
  G:=CM`gr`gf;
  mats:=CM`mats; imats:=CM`imats;
  K := CM`ring;
  finite := IsFinite(K);
  if finite then p := #K; end if;

  ng := Ngens(G);
  RG := Relations(G);
  nr := #RG;
  d := CM`dim;

  //Now we can construct the extension.
  F := FreeGroup(ng+d);
  rels := [];
  if finite then for i in [1..d] do
    Append(~rels,(F.(ng+i))^p);
  end for; end if;
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
  for k in [1..nr] do
    rel := phi(LHS(RG[k])*RHS(RG[k])^-1);
    for i in [1..d] do
      rel := rel*F.(ng+i)^-(Z!emat[k][i]);
    end for;
    Append(~rels,rel);
  end for;
  
  E := quo<F|rels>;

  //Now we provide a normal form function for Es using EvaluateCocycleSG.
  E`NormalForm := function(w) //put word w in E into normal form
    local ww, V, v, mat;
    //first move acting generators to left to give ww. 
    w := ElementToSequence(w);
    V := RSpace(K,d);
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
    v1, ww := EvaluateCocycleSG(CM,emat,ww);
    // unfortunately EvaluateCocycleSG collects v1 to left!
    v1 := v1 * mat;
    v := v + v1;
    w := Id(E);
    for g in ww do w := w * E.g; end for;
    for i in [1..d] do w := w * E.(ng+i)^(Z!v[i]); end for;
    return w;
  end function;

  A := finite select AbelianGroup([p:i in [1..d]])
                else AbelianGroup([0:i in [1..d]]);
  E`Projection := 
   hom< E -> CM`gr`gp | [g: g in CM`gr`sg] cat [Id(CM`gr`gp) : i in [1..d]] >;
  E`Injection := hom< A-> E |  [E.(ng+i): i in [1..d]] >;
  return E, E`Projection, E`Injection;
end function;

SplitExtensionSG := procedure(CM)
/* Sets CM`SplitExtension to be finite presentation of a split extension
 * of module by G. Strong generators of G come first.
 */
  local G, invar, mats, imats, Z, K, finite, p, d, ng, F, rels, phi, E, A;

  if assigned CM`SplitExtension then return; end if;
  G:=CM`gr`gf;
  mats:=CM`mats; imats:=CM`imats;
  Z:=Integers();
  K := CM`ring;
  finite := IsFinite(K);
  if finite then p := #K; end if;
  d := CM`dim;
  ng := Ngens(G);
  F := FreeGroup(ng+d);
  rels := [];
  if finite then for i in [1..d] do
    Append(~rels,(F.(ng+i))^p);
  end for; end if;
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
  E := quo< F |rels >;

  //Now we provide a normal form function for Es using EvaluateCocycleSG.
  E`NormalForm := function(w) //put word w in E into normal form
    local ww, V, v, p, sg;
    //first move acting generators to left to give ww.
    w := ElementToSequence(w);
    V := RSpace(K,d);
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

  A := finite select AbelianGroup([p:i in [1..d]])
                else AbelianGroup([0:i in [1..d]]);
  E`Projection :=
   hom< E -> CM`gr`gp | [g: g in CM`gr`sg] cat [Id(CM`gr`gp) : i in [1..d]] >;
  E`Injection := hom< A-> E |  [E.(ng+i): i in [1..d]] >;

  CM`SplitExtension := E;
end procedure;

SplitExtensionPermRepSG := procedure(CM)
/* Find faithful perm. rep. of CM`SplitExtension.
 * The semidirect product of M by G is returned as a permutation group
 * with two orbits of lengths |M|, deg(G), where the action on the first
 * orbit has M as a regular normal subgroup, and the action on the
 * second is the same as G.  The images of G, M in this
 * permutation group are also returned.
 */
  local E, G, sg, M, ME, d, p, K, Z, mats, gens, gen, deg;

  if assigned CM`SplitExtensionPermRep then return; end if;
  vprint ModCoho: "Finding permutation representation of split extension";
  if not assigned CM`SplitExtension then
    SplitExtensionSG(CM);
  end if;
  G:=CM`gr`gp; sg := CM`gr`sg;
  if Category(G) eq GrpMat then // have to find faithful perm. rep.
    phi,G := PermutationRepresentation(G);
    sg := [phi(g) : g in sg];
  end if;
  mats:=CM`mats;
  E := CM`SplitExtension;
  d := CM`dim;
  K := CM`ring;
  p := #K;
  M := VectorSpace(K,d);
  ME := [v : v in M];

  /* first generators of G in action on M */
  gens := [];
  for i in [1..#sg] do
    gen := [ Position(ME,ME[j]*mats[i]) : j in [1..#ME] ] cat
           [ #ME + j^sg[i] : j in [1..Degree(G)] ];
    Append(~gens, gen );
  end for;
  /* next generators of M */
  for i in [1..d] do
    gen := [ Position(ME,ME[j]+M.i) : j in [1..#ME] ] cat
           [ #ME + j : j in [1..Degree(G)] ];
    Append(~gens, gen );
  end for;

  deg := #ME + Degree(G);
  CM`SplitExtensionPermRep := sub< Sym(deg) | gens >;
  vprint ModCoho: "Found representation of degree",deg;

end procedure;

AutGroupOnH2SG := function(CM)
/* Compute action of the automorphism group of the pair (G,Module) (obtained
 * from automorphism group of split extension of module by group) on
 * H^2. Return result as sequence of matrices.
 */
  local G, mats, imats, p, K, ng, RG, nr, d, E, P, Q, M, EtoP, EtoG, A,
        H2, dH2, H2mats, H2mat, Gtriv, Mims, Mactmat, w, Gims, Gaut,
        Relims, seq, emat, lv, Relimvals, MtoE, z;

  if not assigned CM`H2 then 
     SecondCohomologyGroupSG(CM);
  end if;
  if not assigned CM`SplitExtensionPermRep then
    SplitExtensionPermRepSG(CM);
  end if;

  G:=CM`gr`gf;
  mats:=CM`mats; imats:=CM`imats;
  K := CM`ring;
  Z := Integers();
  p := #K;

  H2 := CM`H2;
  ng := Ngens(G);
  RG := Relations(G);
  nr := #RG;
  d := CM`dim;
  dH2 := Dimension(H2);

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

  H2mats := []; // list of matrices of degree dH2 giving action

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
    Mactmat := Matrix(K,d,d,[0:i in [1..d^2]]);
    for r in [1..d] do
      w := Mims[r];
      for j in [1..#w] do
        g := GeneratorNumber(Subword(w,j,1));
        if g gt 0 then Mactmat[r][g-ng] +:=1;
        else Mactmat[r][-g-ng] -:=1;
        end if;
      end for;
    end for;
    //If action on P/M is nontrivial need action of A.agno^-1 on group relators.
    if not Gtriv then
      Gims := [P.i @ (A.agno^-1) @@ EtoP @ EtoG : i in [1..ng]];
      Gaut := hom<G->G | Gims >;
      Relims := [ (LHS(r)*RHS(r)^-1) @ Gaut : r in RG ];
    end if;

    H2mat := Matrix(K,dH2,dH2,[0: i in [1..dH2^2]]);
   // the matrix specifying the action of A.agno on H2, which we now compute
    for H2gno in [1..dH2] do
      seq := [0: i in [1..dH2]]; seq[H2gno]:=1;
      emat := MatrixOfExtensionSG(CM,seq);
     if Gtriv then
        lv := &cat [ElementToSequence(emat[i]*Mactmat) : i in [1..nr]];
     else
        Relimvals := [EvaluateCocycleSG(CM,emat,w) : w in Relims];
        lv := &cat [ElementToSequence(Relimvals[i]*Mactmat) : i in [1..nr]];
     end if; 
     H2mat[H2gno] := lv @ CM`Z2toH2;
    end for;

    if H2mat ne IdentityMatrix(K,dH2) then
      Append(~H2mats,H2mat);
    end if;
  end for;

  return H2mats;
end function;

DistinctExtensionsSG := function(CM)
/* Compute orbit representatives of this action, and return
 * a list of presentations of the corresponding extensions.
 */
  local  H2mats, K, cd, orbs;

  if not assigned CM`H2 then
     SecondCohomologyGroupSG(CM);
  end if;
  cd := Dimension(CM`H2);
  if cd eq 0 then
    SplitExtensionSG(CM); return [CM`SplitExtension];
  end if;
  H2mats := AutGroupOnH2SG(CM);
  K:=BaseRing(CM`mats[1]);
  orbs := Orbits(sub<GL(cd,K)|H2mats>);
  return
      [ ExtensionOfModuleSG(CM,ElementToSequence(x[1])) : x in orbs ];
end function;

forward ExtensionMatrixQmodZ;
FirstCohomologyGroupQmodZ := procedure(CM)
/* This and following functions are for the case when CM`ring = integers.
 * We compute H^1(G,M) where M is the Q/Z module defined by the same matrices
 * as M. This is isomorphic to H^2(G,M).
 */
  local Z, F, S, I, d, ng, rf, V, invar;
  if assigned CM`QmodZinvar then return; end if;
  Z := IntegerRing();
  assert CM`ring eq Z;

  //first make sure CM`csm and CM`cem are defined
  ZeroCohomologyGroupG(CM);
  FirstCohomologyGroupG(CM);
  F, S := SmithForm(CM`cem); //S * CM`cem * T eq F
  I := CM`csm * S^-1;
  d := CM`dim;
  ng := Nrows(F) div d;
  rf := Rank(F);
  //do sanity check on theory.
  assert Rank(F) + Rank(I) eq Nrows(F) and
                             ExtractBlock(I,1,1,d,rf) eq ZeroMatrix(Z,d,rf);
  invar := [ F[i][i] : i in [1..rf] ];
  V := RSpace(Z, rf);
  CM`QmodZinvar := invar;
  CM`QmodZH1 := quo< V | [ invar[i]*V.i : i in [1..rf]] >;
  CM`QmodZtrans := S;
  ExtensionMatrixQmodZ(CM);
end procedure;

OneCocycleQmodZ := function(CM, s)
//returns a function G-> module given s in CM`QZH1
  local invar, nzr, S, nt, OC, d, ng, Z, Q, GR, mats, imats, V, genims;
  invar := CM`QmodZinvar;
  nzr := #invar;
  nt := #[i : i in invar | i eq 1];
  s := Eltseq(s);
  assert nt + #s eq nzr;
  Q := Rationals();
  S := Matrix(Q, CM`QmodZtrans);
  ng := Ngens(CM`gf);
  GR := CM`gr;
  d := CM`dim;
  Z := CM`ring; //integers
  mats := CM`mats; imats:=CM`imats;
  V := RSpace(Q, ng*d);
  vec := [1 : i in [1..nt]] cat [ s[i]/invar[i+nt] : i in [1..nzr-nt]] cat
         [ 0: i in [1 .. ng*d - #invar] ];
  genims := Eltseq( V!vec * S );
  //find images of one-cocyle on generators
  genims := [ x - Floor(x) : x in genims ]; //normalise in Q/Z
  V := RSpace(Q, d);
  genims := [ V!(genims[(i-1)*d+1 .. i*d]) : i in [1..ng] ];
  OC := function(gtp) //gtp = <g>
    local w, cmat, ans, g;
    g := gtp[1];
    w := ElementToSequence(SGWordH(GR,g));
    cmat := IdentityMatrix(Q,d);
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
    ans := V![ x - Floor(x) : x in Eltseq(ans) ];
    return ans;
  end function;

  return OC;
end function;

IdentifyOneCocycleQmodZ := function(CM,OC)
  //identify from action on strong generators
  local Z, Q, sg, s, S, invar, nt, vec, H1;
  Z := Integers();
  Q := Rationals();
  sg := CM`gr`sg;
  s := &cat [ ElementToSequence(OC(<sg[i]>)) : i in [1..#sg] ];
  s := RSpace(Q, #s)!s;
  S := Matrix(Q, CM`QmodZtrans);
  s := s*S^-1;
  invar := CM`QmodZinvar;
  nt := #[i : i in invar | i eq 1];
  vec := [ s[i]*invar[i] : i in [nt+1 .. #invar] ];
  if not forall{i : i in vec | i in Z } then 
    error "Input to IdentifyOneCocycle is not a cocycle";
  end if;
  H1 := CM`QmodZH1;
  return H1![Z |  s[i]*invar[i] : i in [nt+1 .. #invar] ];
end function;

CorrespondingTwoCocycle := function(CM, o)
//2-cocycle in Z^2(G,M) corresponding to o in Z^1(G,M_{Q/Z})
  local Q, TC, c, go, H1;
  Q := Rationals();
   
  TC := function(tup)
     local vec;
    vec := o(<tup[1]>) * Matrix(Q, MatrixOfElement(CM,tup[2]) ) + o(<tup[2]>) -
            o(<tup[1]*tup[2]>);
     return (CM`module)!Eltseq(vec);
   end function;
   return TC;
end function;

IsOneCoboundaryQmodZ := function(CM,OC)
//if so then return 0-cochain z such that OC(<g>) = z(<>)^(1-g) for g in G
  local ng, d, Q, isc, sg, v, w, S, Si;

  d := CM`dim;
  Q := Rationals();

  sg := CM`gr`sg;
  w := &cat [ ElementToSequence(OC(<sg[i]>)) : i in [1..#sg] ];
  S := Matrix(Q, CM`QmodZtrans);
  Si := S^-1;
  w := Vector(Q, w) * Si;
  w := Parent(w)![ x - Floor(x) : x in Eltseq(w) ];
  csm := Matrix(Q,CM`csm) *Si;
  isc, v := IsConsistent(csm, w);
  if not isc then return false, _; end if;
  return true, func< tp | -v  >;
end function;

ExtensionMatrixQmodZ := procedure(CM)
/* If H^1(G,M_{Q/Z}) has dimension e, then the first e rows of this matrix
 * are the joins of the vaues of the nr relations in M in the e generating
 * elements. The following d*ng rows are just the rows of CM`cem, which are
 * the 2-coboundaries.
 */
  local  catrv, w, TC, H1, relvals;

  H1 := CM`QmodZH1;
  relvals := [];
  for i in [1..Degree(H1)] do
    TC := CorrespondingTwoCocycle( CM, OneCocycleQmodZ(CM, H1.i) );
    catrv := [];
    for r in Relations(CM`gr`gf) do
      w :=  ElementToSequence(LHS(r)*RHS(r)^-1);
      catrv cat:= EvaluateRelator(CM, TC, w);
    end for;
    Append(~relvals, catrv);
  end for;

  CM`QmodZemat := #relvals eq 0 select CM`cem else
                  VerticalJoin( Matrix(relvals), CM`cem );
end procedure;

IdentifyTwoCocycleQmodZ := function(CM,TC)
/* Here TC must be a function of 2-variables defining a two-cycle
 * The corresponding element of CM`QmodZH1 is returned.
 * For each relator w of G, we use the two-cocycle to evaluate  w in M,
 * then cat all the values together to give a vector which identifies.
 * the required element of H2.
 */
  local  catrv, w,  H1, flag, v;

  catrv := [];
  for r in Relations(CM`gr`gf) do
    w :=  ElementToSequence(LHS(r)*RHS(r)^-1);
    catrv cat:= EvaluateRelator(CM, TC, w);
  end for;
  catrv := RSpace(Integers(), #catrv)!catrv;
  flag, v := IsConsistent( CM`QmodZemat, catrv );
  if not flag then
    error "Input to IdentifyTwoCocycle is not a cocycle";
  end if;

  H1 := CM`QmodZH1;
  return H1![v[i] : i in [1..Degree(H1)] ];
end function;

ExtensionOfModuleQmodZ := function(CM, seq)
/* CM`QmodZH1 should have been computed already with FirstCohomologyGroupQmodZ.
 * seq should element of it
 * A presentation of a corresponding extension of the module by the
 * group is returned.
 */
 local invar, G, mats, imats, finite, Z, gens, w, g, RG, nr,
       d, emat, F, rels, rel, phi, E, A, dH1, TC;

  emat := CM`QmodZemat;
  dH1 := Degree(CM`QmodZH1);
  seq := Eltseq(seq);
  Z := Integers();
  G:=CM`gr`gf;
  mats:=CM`mats; imats:=CM`imats;

  ng := Ngens(G);
  RG := Relations(G);
  nr := #RG;
  d := CM`dim;

  //Now we can construct the extension.
  F := FreeGroup(ng+d);
  rels := [];
  for i in [1..d] do for j in [i+1..d] do
    Append(~rels,(F.(ng+i),F.(ng+j)));
  end for; end for;
  for i in [1..ng] do for j in [1..d] do
    w:=Id(F);
    for k in [1..d] do
      w := w * (F.(ng+k))^(mats[i][j][k]);
    end for;
    Append(~rels,F.i^-1*F.(ng+j)*F.i*w^-1);
  end for; end for;
  TC := CorrespondingTwoCocycle( CM, OneCocycleQmodZ(CM, seq) );
  phi := hom<G->F | [F.i : i in [1..ng]] >;
  pos := 0;
  //we'll use the 2-cocycle to evaluate relators to ensure consistency
  //with normal form
  for k in [1..nr] do
    rel := phi(LHS(RG[k])*RHS(RG[k])^-1);
    v := EvaluateRelator(CM, TC, Eltseq(rel));
    rel *:= &*[F.(ng+i)^-v[i] : i in [1..d]];
    Append(~rels,rel);
    pos +:= d;
  end for;
  
  E := quo<F|rels>;

  //Now we provide a normal form function for Es using EvaluateCocycleSG.
  E`NormalForm := function(w) //put word w in E into normal form
    local ww, wwelt, V, v, mat, nf, rel;
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
    sg := CM`gr`sg;
    w := Id( Group(CM) );
    for g in ww do w := g gt 0 select w * sg[g] else w * sg[-g]^-1; end for;
    nf := SGWordH( CM`gr, w );
    rel := SWInv(nf) cat ww; 
    //TC := CorrespondingTwoCocycle( CM, OneCocycleQmodZ(CM, seq) );
    v +:= V!EvaluateRelator(CM, TC, rel);
    w := Id(E);
    for g in nf do w := w * E.g; end for;
    for i in [1..d] do w := w * E.(ng+i)^(Z!v[i]); end for;
    return w;
  end function;

  A :=  AbelianGroup([0:i in [1..d]]);
  E`Projection := 
   hom< E -> CM`gr`gp | [g: g in CM`gr`sg] cat [Id(CM`gr`gp) : i in [1..d]] >;
  E`Injection := hom< A-> E |  [E.(ng+i): i in [1..d]] >;
  return E, E`Projection, E`Injection;
end function;
