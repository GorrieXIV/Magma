freeze;

import "compab.m":  ReduceAbAutMat, CheckRelationsA,
       IsAutAndInverse, MatrixOfGroupElement;
import "strongpres.m":  SVWordH, SGWordH, SVPermutationH;
MakeGroupRecordMG := function(G : sgwords:=false)
  local SGF, GR, nb, sg, nsg, sgi, sv, bo, pt, ipt, tail, utail, sgword,
        gct, w, reli, rel, rels, nr, g, pos, newpos, o, ol, ct, oct;
  SGF := recformat<
             gp: GrpMat,
             gf: GrpFP,
            f2p: Map,
             sg: SetIndx,
            sgw: SeqEnum,
             sv: SeqEnum,
              b: Tup,
             bo: List,
            sgi: SeqEnum, //sgi[i] is list of nos. of strong gens lying in G(i)
           reli: SeqEnum, //reli[i] is list of relation nos. of rels. in G(i)
         sgword: SeqEnum,
           tail: SeqEnum,
          utail: SeqEnum,
        modvars: RngIntElt >;
  GR := rec<SGF | gp:=G >;
  GR`b := Base(G);
  nb := #GR`b;
  GR`sg := StrongGenerators(G);
  sg := GR`sg;
  nsg := #GR`sg;
  if sgwords then
      /* We need the strong generators as words in the original generators
       * in order to compute their matrices later. Could be inefficient!
       */
      F,phi := FPGroup(G);
      GR`sgw := [ s@@phi : s in sg];
  end if;
  GR`bo := [* *];
  for i in [1..nb] do GR`bo[i] := BasicOrbit(G,i); end for;
  GR`sgi:=[[1..nsg]];
  for bno in [2..nb] do
    GR`sgi[bno] := [k : k in [1..nsg] | GR`sg[k] in BasicStabilizer(G,bno)];
  end for;
  GR`sv := [];
  //There is no SchreierVectors function for matrix groups, so we have
  //to calculate them.
  for bno in [1..nb] do
    o := GR`bo[bno];
    ol := #o;
    sv := [ 0 : i in [1..ol] ]; 
    ct := 0; oct := [1];
    while #oct lt ol do
      ct +:= 1; pt := o[oct[ct]]; 
      for i in GR`sgi[bno] do
        pos := Position(o,pt^sg[i]);
        if pos gt 1 and sv[pos] eq 0 then
          Append(~oct,pos); sv[pos] := i;
          if #oct eq ol then break; end if;
        end if;
        pos := Position(o,pt^(sg[i]^-1));
        if pos gt 1 and sv[pos] eq 0 then
          Append(~oct,pos); sv[pos] := -i;
          if #oct eq ol then break; end if;
        end if;
      end for;
    end while;
    GR`sv[bno] := sv;
  end for;

  GR`gf, GR`f2p := FPGroupStrong(G);
  if  GR`sg ne {@ GR`f2p(GR`gf.i) : i in [1..Ngens(GR`gf)] @} then
     error "FPGroupStrong is misbehaving";
  end if;
  rels := Relations(GR`gf);
  nr := #rels;
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

MakeModuleRecordMG := function(G,M)
/* This is called prior to calling any of the cohomological functions,
 * and returns a cohomology module with fields for the various objects
 * that may get computed.
 * G is a permutation group.
 * M should be a module for G.
 * The cohomological functions take this record as argument.
 */
  local GR, R, sg, r, mats, imats;

  R := Representation(M);
  GR := MakeGroupRecordMG(G);

  sg := GR`sg;
  mats := [ R(sg[i]) : i in [1..#sg] ];
  imats := [ m^-1 : m in mats ];
  r := EmptyCohomologyModule();
  r`modtype := ModGrp;
  r`gptype := GrpMat;
  r`gr := GR;
  r`module := M;
  r`mats := mats; r`imats := imats;
  r`dim := Dimension(M);
  r`ring := BaseRing(M);
  r`gf := GR`gf;
  r`gftoG := GR`f2p;

  return r;
end function;

MakeModuleRecordMGA := function(G,invar,mats)
/* This is called prior to calling any of the cohomological functions,
 * and returns a cohomology module with fields for the various objects
 * that may get computed.
 * G is a permutation group.
 * M should be a module for G.
 * The cohomological functions take this record as argument.
 */

  local GR, R, sg, r, ng, imats;

  ng := Ngens(G);
  if ng ne #mats then
    error "Wrong number of matrices in MakeModuleRecordSGA";
  end if;
  GR := MakeGroupRecordMG(G : sgwords:=true);

  mats := [ ReduceAbAutMat(invar,m) : m in mats];
  imats:=[];
  for i in [1..ng] do
    isit, imats[i] := IsAutAndInverse(invar,mats[i]);
    if not isit then
      error "A matrix in MakeModuleRecordMGA does not define an automorphism";
    end if;
  end for;

  //But we want the matrices of the strong generators!
  mats := [ MatrixOfGroupElement(g,invar,mats,imats) : g in GR`sgw ];
  imats :=[ MatrixOfGroupElement(g^-1,invar,mats,imats) : g in GR`sgw ];

  if not CheckRelationsA(GR`gf,invar,mats:imats:=imats) then
    error "Matrices do not satisfy relations on strong generators";
  end if;

  r := EmptyCohomologyModule();
  r`modtype := GrpAb;
  r`gptype := GrpMat;
  r`gr := GR;
  r`mats := mats; r`imats := imats;
  r`invar:=invar;
  r`dim := #invar;
  r`ring := invar[#invar] eq 0 select Integers() else Integers(invar[#invar]);
  r`gf := GR`gf;

  return r;
end function;
