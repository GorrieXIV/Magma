freeze;

import "initialize.m": NameChange;
import "rearrange.m" : CanCalculateAutGpAndMaxSubs;

ExtendOneSubgroup := function(G,k,subrec)
/* A simple version of ExtendOneSubgroupH (in LowIndexSubgroups for example)
 * Let A/B be  elementary abelian layer k of the stored chief series of
 * LMG group G. subrec described G/A with presentation.
 * We output corresponding subrec for G/B (with presentation)
 * together with any complements of A/B in G/B (without presentation).
 */
  local r,rpc,rad,rtopc,rq,Gtorq,rm,gmacts,m,ptom,rep,p,d,S,ngs,mats,extendsubs,
   mgensG,liftgens,src,Spres,SpresM,SprestoG,RV,rels,w,Z,split,Comps,gen,vec;
  assert subrec`length eq 1;
  r := G`LMGNode;
  rpc := r`radPC;
  rad := r`rad;
  rtopc := r`radtoPC;
  rq := r`radquot;
  Gtorq := r`Gtoradquot;
  rm := r`radmods;
  //gmacts := r`rqradmodactions;
  gmacts := r`radmodactions;
  m := rm[k][1];
  ptom := rm[k][2];
  rep := rm[k][3];
  p := #BaseRing(m); d := Dimension(m);

  S := subrec`subgroup;
  ngs := Ngens(S);
  mats := [ gmacts[k](S.i) : i in [1..ngs] ]; //could be done quicker!
  vprint LMG,3: "    computed acting matrices";
  extendsubs := []; //lifted subgroups to be returned

//first G/B 
  mgensG := [m.i @@ ptom @@ rtopc : i in [1..d]];
  liftgens := [S.i : i in [1..ngs]] cat mgensG;
  vprint LMG,3: "    computed lifted generators";
  src := rec< Format(subrec)| length:=1,
           subgroup:=sub<Generic(G)|liftgens>, order:=subrec`order * p^d >;
  Spres := subrec`presentation;
  SpresM := GModule(Spres,mats);
  SprestoG := hom< Spres->Generic(G) | [ liftgens[i] : i in [1..ngs] ] >;
  vprint LMG,3: "    computed homomorphism FPgroup->G";
  RV:=[];
  rels:=Relations(Spres);
  for rel in rels do
     w := LHS(rel)*RHS(rel)^-1;
     Append(~RV,SpresM!Eltseq(m!(w @ SprestoG @ rtopc @ ptom)));
  end for;
  vprint LMG,3: "    computed RV";
  src`presentation := ModuleExtension(SpresM,RV);
  vprint LMG,3: "    computed lift of whole group";
  Append(~extendsubs, src);

//now complements of A/B in G/B using cohomology calculation! */
  split, Comps := ComplementVectors(SpresM, RV);
  vprint LMG,2: "  split:",split;
  Z := Integers();
  trivact := d eq 1 and forall{m: m in mats|m eq IdentityMatrix(GF(p),d)};
  if split then
    vprint LMG,2: "  ",#Comps,"complements";
    for comp in Comps do
      liftgens := [];
      for i in [1..ngs] do
         gen := S.i;
         vec := comp[i];
         for j in [1..d] do
           gen := gen * mgensG[j]^(Z!vec[j]);
         end for;
         Append(~liftgens,gen);
      end for;
      src := rec< Format(src)| 
           subgroup:=sub<Generic(G)|liftgens>, order:=subrec`order >;
      vprint LMG,3: "    computed lifted complement";
      src`length := trivact select 1 else p^d;
      Append(~extendsubs, src);
    end for;
  end if;
  return extendsubs;
end function;

MaxSubs := function(G : SSF:=5000)
/* use standard MaximalSubgroups on solvable radical and then lift through
 * layers of chief series.
 */
local RF,r,cs,rpc,rad,rtopc,rq,rm,Gtorq,subord,MM,M,mm,s,k,Res;
  RF := recformat<order: RngIntElt,
                 length: RngIntElt,
               subgroup: GrpMat,
           presentation: GrpFP>;
  r := G`LMGNode;
  cs := r`cseriesrad;
  rpc := r`radPC;
  rad := r`rad;
  rtopc := r`radtoPC;
  rq := r`radquot;
  rm := r`radmods;
  Gtorq := r`Gtoradquot;
  subord := #rad;

  MM := [];
  if #rq eq 1 then //group soluble
    M := MaximalSubgroups(rpc);
    for m in M do
      mm := rec< RF| >;
      mm`length := m`length;
      mm`order := m`order;
      s := m`subgroup;
      mm`subgroup := sub< Generic(G) | [s.i @@ rtopc : i in [1..Ngens(s)]] >;
      mm`subgroup`Order := mm`order;
      Append(~MM,mm);
    end for;
    return MM;
  end if;

  M := MaximalSubgroupsTF(rq :
                  SmallSimpleFactor:=SSF, Print:=GetVerbose("LMG"));
  k := #cs;
  Res := [];
  for m in M do
    mm := rec< RF| >;
    mm`length := m`length;
    mm`order := m`order;
    s := m`subgroup;
    if s eq rq then
        mm`subgroup := sub< Generic(G) | [s.i @@ Gtorq : i in [1..Ngens(s)]] >;
        mm`presentation := m`presentation;
        full := mm;
    else
        mm`subgroup := sub< Generic(G) | [s.i @@ Gtorq : i in [1..Ngens(s)]]
                     cat [ cs[k].i @@ rtopc : i in [1..Ngens(cs[k])] ] >;
        mm`order *:= subord;
        mm`subgroup`Order := mm`order;
        Append(~Res,mm);
    end if;
  end for;
  vprint LMG, 1: #Res, "maximals of radical quotient";

  for k in [#cs-1..1 by -1] do
    vprint LMG, 1: "Lifting through level",k;
    subord := subord div #rm[k][1];
    M := ExtendOneSubgroup(G, k, full);
    //first one is whole group
    full := M[1];
    for m in [M[i] : i in [2..#M]] do
        mm := m;
        s := m`subgroup;
        mm`subgroup := sub< Generic(G) | [s.i : i in [1..Ngens(s)]]
                     cat [ cs[k].i @@ rtopc : i in [1..Ngens(cs[k])] ] >;
        mm`order *:= subord;
        mm`subgroup`Order := mm`order;
        Append(~Res, mm);
    end for;
    vprint LMG, 1: #Res, "maximals after lifting";
  end for;
  return Res;
end function;
