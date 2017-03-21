freeze;

/* Some miscellaneous functions for subgroups of free groups.
 */

import "dfa.m": DFAREC;
AddAttribute(GrpFP,"FSInfo");
declare verbose SGCount, 1000000000; //used to number supergroups

forward CosetTableToDFA, FreeGeneratorsSubgp, WriteAsSubgroup;

intrinsic FSInitialize(F :: GrpFP)
{Initialize FSInfo attribute and compute supergroup if not already done}
  local FSInfoRF, FF, FFF, hassg, ct;
  require #Relations(F) eq 0 :
    "Argument of FSInitialize is not a free group";
  FSInfoRF := recformat<
    issupergroup: BoolElt,//true for the largest supergroup - always defined
   supergroupind: RngIntElt,//Id for supergroup of subgroup
      supergroup: GrpFP,  //the largest supergroup of H
                          // defined whenever isovergrp is false
             CT: Map,     //coset table of H in its supergroup 
            dfa: Rec,     //dfa of coset table
       freegens: SeqEnum, //free generators of subgrp as elts of supergroup
             sg: SeqEnum  //Schreier generators for dfa entries
          /**/ >;

  if not assigned F`FSInfo then
    hassg, FF := HasSupergroup(F);
    if not hassg then
      ct := GetVerbose("SGCount") + 1;
      F`FSInfo := rec< FSInfoRF | issupergroup := true,
                                  supergroup := F, supergroupind := ct >;
      SetVerbose("SGCount",ct);
    else
      repeat
        FSInitialize(FF); FFF:=FF;
        hassg, FF := HasSupergroup(FFF);
      until not hassg;
      F`FSInfo := rec< FSInfoRF | issupergroup := false,
                                  supergroup := FFF,
                                  supergroupind := FFF`FSInfo`supergroupind >;
      F`FSInfo`CT := CosetTable(FFF, F : Strategy:="RT");
      F`FSInfo`dfa := CosetTableToDFA(F`FSInfo`CT);
      F`FSInfo`freegens := FreeGeneratorsSubgp(F);
    end if;
  end if;
end intrinsic;

FSRewrite := function(F, H)
/* Return true/false if H is subgroup of free group F and, if so, a list
  of free generators of H as words in the free generators of F.
  The index of H in F (which may be infinity) is also returned.
  Appropriate fields are initialised for further calculations. */
  local FF, r, FS, dfa, sg, fg, cos, wd, s, y, index, ct;
  FSInitialize(F); FSInitialize(H);
  if not F`FSInfo`supergroupind eq H`FSInfo`supergroupind then
   "Arguments of FSRewrite must have the same supergroups";
  end if;
  if F`FSInfo`issupergroup then
    if H`FSInfo`issupergroup then
      return true, [F.i:i in [1..Ngens(F)]],1;
    end if;
    CT := H`FSInfo`CT;
    index := IsComplete(CT) select #CT else Infinity();
    return true, H`FSInfo`freegens, index;
  end if;
  //otherwise there is a larger supergroup
  FF := F`FSInfo`supergroup;
  if H`FSInfo`issupergroup then
    if FSIndex(FF,F) ne 1 then return false,_,_; end if;
    return true, [FF.i:i in [1..Ngens(FF)]],1;
  end if;
  FS := sub< FF | F`FSInfo`freegens >; //F on its free generators
  FS`FSInfo := rec< Format(F`FSInfo) | issupergroup := true, supergroup := FS,
                                                        supergroupind:=0 >;
  //we put supergroupind = 0 becuase we won't be keeping this group
  isin, sgp := WriteAsSubgroup(FF,F,FS,H);
  if not isin then return false,_,_; end if;
  return true, [sgp.i: i in [1..Ngens(sgp)]], FSIndex(FS,sgp);
end function;

WriteAsSubgroup := function(FF,F,FS,H)
/* H <= F=FS <= FF with FF the supergroup of F and H, and FS equal to F on its
 * free generators set up as an supergroup.
 * Decide whether H is a subgroup of F and, if so, return group FH equal
 * to H initialised as subgroup of FS.
 */
local gens, fg, dfa, sg, s, cos, y;
  assert FF`FSInfo`issupergroup and FS`FSInfo`issupergroup;
  assert not F`FSInfo`issupergroup and not H`FSInfo`issupergroup;
  assert [ FS.i : i in [1..Ngens(FS)]] eq F`FSInfo`freegens;
  assert FF`FSInfo`supergroupind eq F`FSInfo`supergroupind and
         FF`FSInfo`supergroupind eq H`FSInfo`supergroupind;
  if not assigned H`FSInfo then 
    error "In WriteAsSubgroup: group not initialised";
  end if;
  //check that FF is supergroup of H
  hgens := [ FS | ];
  fg := F`FSInfo`freegens;
  dfa := F`FSInfo`dfa`transitions;
  sg := F`FSInfo`sg;
  r := Ngens(FF);
  for g in H`FSInfo`freegens do
    //test for membership in F
    s := Eltseq(g);
    cos := 1; wd := [];
    for x in s do
      y := x gt 0 select x else r-x;
      if dfa[cos][y] eq 0 then return false,_,_; end if;
      Append(~wd, sg[cos][y]);
      cos := dfa[cos][y];
    end for;
    if cos ne 1 then return false,_; end if;
    Append(~hgens, FS!wd);
  end for;
  sgp := sub<FS|hgens>;
  //we want FS rather than FF to come out as the supergroup, so do
  //the initialization directly
  sgp`FSInfo := rec< Format(FS`FSInfo) | issupergroup := false,
               supergroup := FS, supergroupind := FS`FSInfo`supergroupind >;
  sgp`FSInfo`CT := CosetTable(FS, sgp : Strategy:="RT");
  sgp`FSInfo`dfa := CosetTableToDFA(sgp`FSInfo`CT);
  sgp`FSInfo`freegens := FreeGeneratorsSubgp(sgp);

  return true, sgp;
end function;

intrinsic FSSupergroup(F :: GrpFP) -> GrpFP
{The largest defined supergroup of free group F}
  FSInitialize(F);
  return F`FSInfo`supergroup;
end intrinsic;

intrinsic FSIndex(F :: GrpFP, H :: GrpFP) -> RngIntElt
{Index of subgroup of free group - natural number or infinity}
  local isin, index;
  FSInitialize(F); FSInitialize(H);
  require F`FSInfo`supergroupind eq H`FSInfo`supergroupind :
    "Arguments of FSIndex must have the same supergroup";
  isin,_,index := FSRewrite(F,H);
  if not isin then
    error "FSIndex: second argument is not subgroup of first";
  end if;
  return index;
end intrinsic;

intrinsic FSFiniteIndex(F :: GrpFP, H :: GrpFP) -> BoolElt
{Is index of subgroup H of free group F finite?}
  return FSIndex(F,H) cmpne Infinity();
end intrinsic;

intrinsic FSIsIn(H :: GrpFP, x) -> BoolElt
{Is element x of subgroup H of free group F?}
  FSInitialize(H);
  return CT(<1,x>) eq 1 where CT := H`FSInfo`CT;
end intrinsic;

intrinsic FSIsSubgroup(H :: GrpFP, K :: GrpFP) -> BoolElt
{Is K a subgroup of free group H? H and K must be subgroups of free group F.}
  FSInitialize(H); FSInitialize(K);
  require H`FSInfo`supergroupind eq K`FSInfo`supergroupind :
    "Arguments of FSIsSubgroup must have the same supergroup";
  return isin where isin,_,_ := FSRewrite(H,K);
end intrinsic;

intrinsic FSEqual(H :: GrpFP, K :: GrpFP) -> BoolElt
{Are free subgroups H,K of a free group F equal?}
  return FSIsSubgroup(H,K) and FSIsSubgroup(K,H);
end intrinsic;

intrinsic FSFreeGenerators(H :: GrpFP) -> SeqEnum, GrpFP
{Free generators of subgroup H of free group F, and also H as a subgroup
 defined on those free generators.}
  local F, gens, sgp;
  FSInitialize(H);
  F := H`FSInfo`supergroup;
  _,gens,_ := FSRewrite(F,H);
  sgp := sub< F | gens >;
  FSInitialize(sgp);
  return gens, sgp;
end intrinsic;

FreeGeneratorsSubgp := function(H)
//free generators of subgroup H of free group - called automatically during
//initialisation in FSRewrite
  local F, dfa, tab, r, n, T, im, sg, ng;
  FSInitialize(H);
  F := H`FSInfo`supergroup;
  dfa := H`FSInfo`dfa;
  r := Ngens(F);
  tab := dfa`transitions;
  n := #tab;
  sg := [ [0: i in [1..2*r]] : j in [1..n] ]; 
  T := [ Id(F) ]; //elements mapping 1 to cosets
  ndefs := 1;
  for c in [1..n] do
    for g in [1..r] do
      im := tab[c][g];
      if im gt 0 and not IsDefined(T,im) then
        T[im] := T[c] * F.g;
        ndefs +:=1;
        if ndefs eq n then break c; end if;
      end if;
    end for;
    for g in [1..r] do
      im := tab[c][r+g];
      if im gt 0 and not IsDefined(T,im) then
        T[im] := T[c] * F.g^-1;
        ndefs +:=1;
        if ndefs eq n then break c; end if;
      end if;
    end for;
  end for;
  gens := [];
  for c in [1..n] do
    for g in [1..r] do
      im := tab[c][g];
      if im gt 0 then
         gen := T[c] * F.g * T[im]^-1;
         if gen ne Id(F) then
           Append(~gens, gen); ng := #gens;
           sg[c][g] := ng; sg[im][r+g] := -ng; 
         end if;
      end if;
    end for;
  end for;
  H`FSInfo`sg := sg;
  return gens;
end function;

FreeGeneratorsDFA := function(F,dfa)
//free generators of a subgroup of F defined by a dfa
  local tab, r, n, T, im, sg, ng;
  tab := dfa`transitions;
  n := #tab;
  r := #tab[1] div 2;
  T := [ Id(F) ]; //elements mapping 1 to cosets
  ndefs := 1;
  for c in [1..n] do
    for g in [1..r] do
      im := tab[c][g];
      if im gt 0 and not IsDefined(T,im) then
        T[im] := T[c] * F.g;
        ndefs +:=1;
        if ndefs eq n then break c; end if;
      end if;
    end for;
    for g in [1..r] do
      im := tab[c][r+g];
      if im gt 0 and not IsDefined(T,im) then
        T[im] := T[c] * F.g^-1;
        ndefs +:=1;
        if ndefs eq n then break c; end if;
      end if;
    end for;
  end for;
  gens := [];
  for c in [1..n] do
    for g in [1..r] do
      im := tab[c][g];
      if im gt 0 then
         gen := T[c] * F.g * T[im]^-1;
         if gen ne Id(F) then
           Append(~gens, gen); ng := #gens;
         end if;
      end if;
    end for;
  end for;

  return gens;
end function;

CosetTableToDFA := function(CT)
  local G, tab, row, ng;
  G := Group(CT);
  ng := Ngens(G);
  tab := [];
  for s in [1..#CT] do
    row := [];
    for i in [1..ng] do
      Append( ~row, CT(< s, G.i >) );
    end for;
    for i in [1..ng] do
      Append( ~row, CT(< s, G.i^-1 >) );
    end for;
    Append(~tab, row);
  end for;
  return rec< DFAREC | initial := {1}, final := {1},
                       alphabetsize := 2*ng, transitions := tab >;
end function;
 
intrinsic FSMeet(H :: GrpFP, K :: GrpFP) -> GrpFP
{H meet K for H, K subgroups of free group F}
  local F, dfaH, dfaK, dfameet, int, sgp;
  FSInitialize(H); FSInitialize(K);
  require H`FSInfo`supergroupind eq K`FSInfo`supergroupind :
    "Arguments of FSMeet must have the same supergroup";
//first deal with case where one or both arguments are supergroups
  if H`FSInfo`issupergroup then return K; end if;
  if K`FSInfo`issupergroup then return H; end if;
  dfaH := H`FSInfo`dfa;
  dfaK := K`FSInfo`dfa;
  dfameet := MinimizeDFA( MeetDFA(dfaH, dfaK) );
  F := H`FSInfo`supergroup;
  int := FreeGeneratorsDFA(F,dfameet); 
  sgp := sub< F | int >;
  FSInitialize(sgp);
  return sgp;
end intrinsic;

intrinsic SubgroupElementsCT(CT :: Map, len :: RngIntElt) -> SetEnum
{Given a (not necessarily complete) coset table for a subgroup H of a
 finitely presented group G, return the elements of G of length at most
 len that are in H}
  local dfa, G;
  dfa := CosetTableToDFA(CT);
  G := Group(CT);
  dfa`alphabet := [G.i : i in [1..Ngens(G)]] cat [G.i^-1 : i in [1..Ngens(G)]];
  return LanguageDFA(dfa, 0, len : words:=true );
end intrinsic;

intrinsic SubgroupElements(G :: GrpFP, H :: GrpFP, len :: RngIntElt) -> SetEnum
{Given a subgroup H of a finitely presented group G, form the coset
 table for H in G, and use it to return the elements of G of length at most
 len that are in H. If options to CosetTable need to be used, then call
 CosetTable first followed by SubgroupElementsCT.}
  local CT;
   if #Relations(G) eq 0 then //G is free so incomplete coset table OK
     CT := CosetTable(G, H : Strategy:="RT");
   else
     CT := CosetTable(G, H);
     if not IsComplete(CT) then
       "WARNING: Coset table is incomplete!";
     end if;
   end if;
   return SubgroupElementsCT(CT, len);
end intrinsic;

//The following functions were written by Raul Moragues Moncho
//as part of a 4th year project at warwick
//WordPrefixes function: creates a sequence of all prefixes of a word u.

WordPrefixes := function(F,u)
  assert Type(u) eq GrpFPElt;
  assert Type(F) eq GrpFP;
  assert u in F;
  S := ElementToSequence(u);
  T := [];
  T[1] := LeadingGenerator(u);
  for i in {2..#u} do
    T[i] := T[i-1]*F.S[i];
  end for;
return T;
end function;

Eltseqaut := function(w,ng);
  s:=Eltseq(w);
  for i in {1..#s} do
    if s[i] lt 0 then
      s[i] := -s[i] + ng;
    end if;
  end for;
  return s;
end function;

Transition := function(F, s, B);
  assert (Type(s) eq SeqEnum) or (Type(s) eq GrpFPElt);
  assert Type(B) eq Rec;
  if Type(s) eq GrpFPElt then
    s:=Eltseqaut(s,Ngens(F));
  end if;
  n := Rep(B`initial);
  for i in {1..#s} do
    if n eq 0 then return 0;
    else n := B`transitions[n][s[i]];
    end if;
  end for;
  return n;
end function;

UnderlyingSubgroup := function(F,dfa)
  sgp := sub< F | FreeGeneratorsDFA(F,dfa) >;
  FSInitialize(sgp);
  return sgp;
end function;

//TransInv function: Takes the position of an element in the automaton
//transitions and returns a word that reaches it as s:=Eltseq(w) for
//some word w (same as T^-1(1, w) but in this language).

TransInv := function(x,B);
  assert Type(x) eq RngIntElt;
  assert Type(B) eq Rec;
  if x eq 1 then return []; end if;
  coor:=[2]; s:=[];
  alpha := B`alphabetsize;
  while coor[1] ne 1 do
    coor:=[];
    for i in {1..#B`transitions} do
      for j in {1..B`alphabetsize} do
        if coor ne [] then break;
        elif B`transitions[i][j] eq x then
          x := i;
          coor := [i,j];
          j2:=j;
          if j gt (alpha div 2) then
            j2 := -1*(j2-(alpha div 2));
          end if;
          s := Insert(s,1,j2);
        end if;
      end for;
    end for;
  end while;
  return s;
end function;

//autAddDefinitions: Adds certain definitions to the automaton.
autAddDefinitions := function(F,A,Def:Coset := 1);
  assert Type(F) eq GrpFP;
  assert Type(A) eq Rec or Type(A) eq GrpFP;
  if Type(A) eq GrpFP then A := A`FSInfo`dfa; end if;
  assert Type(Def) eq SeqEnum;
  assert Type(Coset) eq RngIntElt;
  A`final := {Coset}; A`initial := {Coset};
  for i in { 1 .. #Def} do
    assert F!Def[i] in F;
    if Transition(F,Def[i],A) eq 0 then
      P:=WordPrefixes(F,Def[i]);
      for j in { 1 .. #P } do
	if Transition(F,P[j],A) eq 0 then
  	  A`transitions[#A`transitions + 1] := [0:n in {1..2*#Generators(F)}];
	  if j eq 1 then
  	    A`transitions[1][Eltseqaut(P[1],Ngens(F))[1]] := #A`transitions;
	    A`transitions[#A`transitions][Eltseqaut(P[j]^-1,Ngens(F))[j]] := 1;
	  else
	    A`transitions[Transition(F,P[j-1],A)][Eltseqaut(P[j],Ngens(F))[j]] 
	  			:= #A`transitions;
            A`transitions[#A`transitions][Eltseqaut(P[j]^-1,Ngens(F))[j]] 
				:= Transition(F,P[j-1],A);
	  end if;
        end if;
      end for;
    end if;
  end for;	
  return A;
end function;

//autConjugate: Computes the automaton for u^-1Hu from the one for H.

autConjugate := function(F,H,u);
  assert Type(F) eq GrpFP;
  assert Type(H) eq GrpFP;
  assert Type(u) eq GrpFPElt;
  A:=H`FSInfo`dfa;
  if Transition(F,u,A) eq 0 then
    P:=WordPrefixes(F,u);
    while Transition(F,P[1],A) ne 0 do Remove(~P,1); end while;
  end if;
  A:=autAddDefinitions(F,A,[u]);
  t:=Transition(F,u,A);
  A`final := {t}; A`initial := {t};
  return A;
end function;

//Connections: Calculates the amount of edges from coset n in coset 
//table automaton A.

Connections := function(F,A,n);
  assert Type(F) eq GrpFP;
  assert Type(A) eq Rec;
  assert Type(n) eq RngIntElt;
  assert n le #A`transitions;
  k:=[];
  for i in {1 .. A`alphabetsize} do
    if A`transitions[n][i] ne 0 then Append(~k,i); end if;
  end for;
  return k;
end function;

//autReduce: Reduces the automaton.

autReduce := function(F,A);
  assert Type(A) eq Rec;
  assert Type(F) eq GrpFP;
  k := 0;
  while k ne #A`transitions do
    k := #A`transitions;
    for i in [#A`transitions .. 1 by -1] do
      c:=Connections(F,A,i);
      if #c eq 1 and {i} ne A`initial then
	t:=A`transitions[i][c[1]];
	if c[1] gt #Generators(F) then
	  c[1] := c[1] - #Generators(F);
	else c[1] := c[1] + #Generators(F);
	end if;
        A`transitions[t][c[1]] := 0;
	Remove(~A`transitions,i);
	for j in {1 .. #A`transitions} do
          if Max(A`transitions[j]) gt i then
	    for k in {1 .. A`alphabetsize} do
	      if A`transitions[j][k] gt i then
		A`transitions[j][k] -:= 1;
	      end if;
	    end for;
	  end if;
	end for;
	if Max(A`initial) gt i then A`initial := {Max(A`initial)-1}; end if;
	if Max(A`final) gt i then A`final := {Max(A`final)-1}; end if;
      end if;
    end for;
  end while;
  return A;
end function;

//autCycReduce: Cyclically reduces the DFA representing some coset table.
//The final automaton represents u^-1Hu where H is the initial subgroup.

autCycReduce := function(F,A);
  assert Type(F) eq GrpFP;
  assert Type(A) eq Rec;
  A:=autReduce(F,A);
  u:=[];
  while #Connections(F,A,Max(A`initial)) lt 2 do
    c:=Connections(F,A,Max(A`initial));
    k := Max(A`initial);
    u:=Append(u,c[1]);
    A`initial := {A`transitions[k][c[1]]};
    A`final := {A`transitions[k][c[1]]};
    A:=autReduce(F,A);
  end while;
  return A, u;
end function;

//FSNormaliser: Calculates the Normalizer of a subgroup.
intrinsic FSNormaliser(F :: GrpFP, H :: GrpFP) -> GrpFP
{Normaliser in F of subgroup H of free group F}
  FSInitialize(F); FSInitialize(H);
  require F`FSInfo`supergroupind eq H`FSInfo`supergroupind:
    "Arguments of FSNormaliser must have the same supergroups";
  if H`FSInfo`issupergroup then return F; end if;
  if forall{g : g in Generators(H)|g eq F.0} then
    return F;
  end if;
  if not F`FSInfo`issupergroup then
    FF := F`FSInfo`supergroup;
    FS := sub< FF | F`FSInfo`freegens >; //F on its free generators
    FS`FSInfo := rec< Format(F`FSInfo) | issupergroup := true,
                                         supergroup:=FS, supergroupind:=0  >;
    isin, sgp := WriteAsSubgroup(FF,F,FS,H);
    if not isin then
      error "In FNormaliser: second argument is not a subgroup of first";
    end if;
    N := $$(FS,sgp);
    //but we want it set up as subgroup of FF, not of FS.
    N := sub< FF | Generators(N) >;
    FSInitialize(N);
    return N;
  end if;
/*
  if FSFiniteIndex(F,H) eq true then
    return Normaliser(F,H);
  end if;
*/
  u:=[]; S:=[]; Gen :=[];
  A:=H`FSInfo`dfa;
  A, v:=autCycReduce(F,A);
  for i in [1 .. #v] do
    if v[i] gt #Generators(F) then v[i] := -v[i]+#Generators(F); end if;
  end for;
  v:=F!v;
  k := A`initial;
  G := UnderlyingSubgroup(F,A); 
  for i in {1 .. #A`transitions} do
    u[i] := F!TransInv(i,A);
    bool := true;
    for j in [1 .. Ngens(G)] do
      bool := bool and FSIsIn(G,u[i]^-1*G.j*u[i]);
      bool := bool and FSIsIn(G,u[i]*G.j*u[i]^-1);
    end for;
   if bool then Append(~S,u[i]); end if;
  end for;
  if S ne [Id(F)] then NG:=sub<F|G,S>; else NG := G; end if;
  for i in {1 .. #Generators(NG)} do
    Gen[i] := v*SetToSequence(Generators(NG))[i]*v^-1;
  end for;
  K:=sub<F|Gen>; _,K := FSFreeGenerators(K); //return it on its free generators
  return K;
end intrinsic;

intrinsic FSNormalizer(F :: GrpFP, H :: GrpFP) -> GrpFP
{Normalizer in F of subgroup H of free group F}
  return FSNormaliser(F,H);
end intrinsic;

//FSIsConjugate: Returns whether two subgroups G,H of F are conjugate,
//and in the affirmative case, a word v st v^-1*G*v = H.

intrinsic FSIsConjugate(F :: GrpFP,G :: GrpFP,H :: GrpFP) -> BoolElt, GrpFPElt
{Test subgroups G,H of free group F for conjugacy in F}
  FSInitialize(F); FSInitialize(G); FSInitialize(H);
  require F`FSInfo`supergroupind eq G`FSInfo`supergroupind and
                    F`FSInfo`supergroupind eq H`FSInfo`supergroupind:
    "Arguments of FSIsConjugate must have the same supergroups";
  if not assigned F`FSInfo or not assigned G`FSInfo or
                                                not assigned H`FSInfo then
    error "In FIsConjugate: one of the groups is not initialised";
  end if;
  require FSIsSubgroup(F,G) and FSIsSubgroup(F,H):
    "Second and third arguments must be subgroups of the first";
  if F`FSInfo`supergroupind ne H`FSInfo`supergroupind  or
     G`FSInfo`supergroupind ne H`FSInfo`supergroupind then
    error "In FIsConjugate: arguments have different supergroups";
  end if;
  if FSEqual(G,H) then
    return true, Id(F);
  elif FSIndex(F,G) ne FSIndex(F,H) then
    return false;
  end if;
/*
  if FSFiniteIndex(F,G) eq true then
    return IsConjugate(F,G,H);
  end if;
*/
  if not F`FSInfo`issupergroup then
    FF := F`FSInfo`supergroup;
    FS := sub< FF | F`FSInfo`freegens >; //F on its free generators
    FS`FSInfo := rec< Format(F`FSInfo) | issupergroup := true >;
    isin, sgpG := WriteAsSubgroup(FF,F,FS,G);
    if not isin then
      error "In FIsConjugate: second argument is not a subgroup of first";
    end if;
    isin, sgpH := WriteAsSubgroup(FF,F,FS,H);
    if not isin then
      error "In FIsConjugate: third argument is not a subgroup of first";
    end if;
    return $$(FS,sgpG,sgpH);
  end if;
  GTriv := forall{x: x in Generators(G) | x eq F.0};
  HTriv := forall{x: x in Generators(H) | x eq F.0};
  if not GTriv eq HTriv then return false; end if;
  A, w:=autCycReduce(F,G`FSInfo`dfa);
  B, x:=autCycReduce(F,H`FSInfo`dfa);
  for i in [1..#x] do
    if x[i] gt #Generators(F) then x[i] := -x[i]+#Generators(F); end if;
  end for;
  for i in [1..#w] do
    if w[i] gt #Generators(F) then w[i] := -w[i]+#Generators(F); end if;
  end for;
  for i in [1..#A`transitions] do
    A`initial := {i}; A`final := {i};
    bool := EqualDFA(A,B);
    if bool then
      return true, (F!w * (F!TransInv(i,A)) * (F!x)^-1);
    end if;
  end for;
  return false, _;
end intrinsic;

intrinsic FSCentraliser(F :: GrpFP,x :: GrpFPElt) -> GrpFP
{Centraliser of element x in free group F}
  return FSNormaliser(F, sub<F|x>);
end intrinsic;

intrinsic FSCentralizer(F :: GrpFP,x :: GrpFPElt) -> GrpFP
{Centralizer of element x in free group F}
  return FSNormalizer(F, sub<F|x>);
end intrinsic;

intrinsic FSIsConjugate(F :: GrpFP,x :: GrpFPElt,y :: GrpFPElt) ->
                                                       BoolElt, GrpFPElt
{Test elements x,y of free group F for conjugacy in F}
  local FF, FS, issub, HH;
  FSInitialize(F);
  if x eq y then return true, Id(F); end if;
  if x eq Id(F) or y eq Id(F) then return false,_; end if;
  if F`FSInfo`issupergroup then
    FS := F;
    x := FS!x; y := FS!y; //in case they were defined as words in a subgroup
  else
    FF := F`FSInfo`supergroup;
    FS := sub< FF | F`FSInfo`freegens >; //F on its free generators
    FS`FSInfo := rec< Format(F`FSInfo) | issupergroup := true, supergroup := FS,
                                                        supergroupind:=0 >;
    H := sub< FF | x,y >;
    FSInitialize(H);
    issub, HH := WriteAsSubgroup(FF,F,FS,H);
    if not issub then
       error
"The second and third arguments of FSIsConjugate must be elements of the first";
    end if;
    x := FS!(HH.1); y := FS!(HH.2);
  end if;
  //now we just test if cyclic reduction of y is a cyclic permutation of
  //cyclic reduction of x
  //first cyclically reduce
  lx := #x;
  cx := Max([0] cat //put in 0 to handle empty sequence
           [ t : t in [1..lx div 2] | Subword(x,1,t) eq Subword(x^-1,1,t)]);
  px := Subword(x,1,cx); crx := x^px;
  ly := #y;
  cy := Max([0] cat
           [ t : t in [1..ly div 2] | Subword(y,1,t) eq Subword(y^-1,1,t)]);
  py := Subword(y,1,cy); cry := y^py;
  if #crx ne #cry then return false,_; end if;
  match := false;
  for i in [0..#crx div 2] do if RotateWord(crx,i) eq cry then
    match := true; ans := Subword(cry,1,i)^-1; break;
  end if; end for;
  if not match then
    for i in [1..#crx - (#crx div 2) - 1] do if RotateWord(cry,i) eq crx then
      match := true; ans := Subword(crx,1,i); break;
    end if; end for;
  end if;
  if match then
    ans := px * ans * py^-1; ans; assert x^ans eq y;
    return true, ans;
  end if;
  return false,_;
end intrinsic;

intrinsic FSCentraliser(F :: GrpFP,H :: GrpFP) -> GrpFP
{Centraliser of subgroup H in free group F}
  local fg;
  FSInitialize(F); FSInitialize(H);
  require F`FSInfo`supergroupind eq H`FSInfo`supergroupind :
    "Arguments of FSCentraliser must have the same supergroups";
  require FSIsSubgroup(F,H):
    "Second argument of FSCentraliser must be a subgroup of the first";
  if H`FSInfo`issupergroup then //F = H 
    if Ngens(F) le 1 then return F; end if;
    return s where s := sub<F|>; //don't want second return value
  end if;
  fg := H`FSInfo`freegens;
  if #fg eq 0 then return F; end if;
  if #fg gt 1 then return s where s := sub<F|>; end if;
  return FSCentraliser(F,fg[1]);
end intrinsic;

intrinsic FSCentralizer(F :: GrpFP,H :: GrpFP) -> GrpFP
{Centralizer of subgroup H in free group F}
  return FSCentraliser(F, H);
end intrinsic;
