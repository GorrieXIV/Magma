freeze;
/* 
  A Magma package to construct the W-graph of a Coxeter system (W,S).
  
  In this package an m_ij-sequence is the lower triangular part of the
  Coxeter matrix of (W,S).
  
  from Bob Howlett
  21 June 2011
  
  $Id: wgraphs.m 48480 2014-09-28 02:09:52Z donnelly $

  Intrinsics defined in this file:
    GetCells
    InduceWG
    InduceWGtable
    IsWGsymmetric
    MakeDirected
    Mij2EltRootTable
    Name2Mij
    Partition2WGtable
    TestHeckeRep
    TestWG
    WG2GroupRep
    WG2HeckeRep
    WGelement2WGtable
    WGidealgens2WGtable
    WGtable2WG
    WriteWG
*/

declare verbose WGraph, 4;


import "reftable2.m":refTable;

/*
A W-graph poset P is represented by a pair <seq,tbl> where
seq is the mij-sequence defining the Coxeter group W and tbl is
a table with rows indexed by the integers in [1 .. Rank(W)]
and columns indexed by the integers in [1 .. #P]. If s is
the i-th element of S and v the j-th element of P then
table[i,j] = k if sv is the k-th element of P and sv is not
equal to v, while if sv = v then table[i,j] is either j or  -j
depending on whether s is in A(v) or D(v). The numbering of the
elements of P is chosen so that if v is the j-th element of P
and u is the k-th element then j < k whenever v < u. Hence
the descent set of the j-th element of P is
{ i : i in {1 .. #S} | table[i,j] < j }.
*/

intrinsic Mij2EltRootTable( seq :: SeqEnum ) -> SeqEnum[SeqEnum[RngIntElt]]
{ Return the elementary root action table for the Coxeter
  group defined by the given mij-sequence }
  return refTable( SymmetricMatrix(seq) );
end intrinsic;

mijsequence := func< M | &cat[[M[i,j] : j in [1..i]] : i in [1..Nrows(M)]] >;

intrinsic Name2Mij(name::MonStgElt) -> SeqEnum
{ The mij-sequence of the Coxeter groups of type name }
  return mijsequence(CoxeterMatrix(name));
end intrinsic;


intrinsic WGtable2WG(table::SeqEnum) -> GrphUnd
{ Convert a W-graph table to a W-graph }
 rank:=#table;
 deg:=#table[1];
 descents:=[{s : s in [1..#table] | table[s,j] lt j} : j in [1..deg]];
 klpcontext:=recformat<klp1,pointers1,klp2,pointers2,thepolys>;
 basering:=Integers();
 polyring := PolynomialRing(basering); q := polyring.1;
 
 findPoly:=function(w,y,klp)
  u:=w;
  i:=0;
  desy:=descents[y];
  repeat
   found:=true;
   desu:=descents[u];
   if desu notsubset desy then
    s:=Representative(desu diff desy);
    su:=table[s,u];
    if su lt y then
     return polyring!0;
    elif su eq y then
     return q^i;
    else
     u:=su;
     i +:=1;
     found:=false;
    end if;
   else
    indx:=Index(klp`klp1[y],u);
    if indx ne 0 then
     return q^i*klp`thepolys[klp`pointers1[y,indx]];
    else
     indx:=Index(klp`klp2[y],u);
     if indx ne 0 then
      return q^i*klp`thepolys[klp`pointers2[y,indx]];
     else
      return polyring!0;
     end if;
    end if;
   end if;
  until found;
 end function;
 
 vprint WGraph, 2 : "Computing Kazhdan-Lusztig polynomials ...";
 klp:=rec<klpcontext |
  klp1:=[PowerIndexedSet(Integers())| ],
  pointers1:=[PowerSequence(Integers())|],
  klp2:=[PowerIndexedSet(Integers())| ],
  pointers2:=[PowerSequence(Integers())|],
  thepolys:={@ polyring| @}>;
 numpolys:=0;
 for w in [1..deg] do
  klp`klp1[w]:={@ @};
  klp`pointers1[w]:=[];
  klp`klp2[w]:={@ @};
  klp`pointers2[w]:=[];
 end for;
 for w in [2..deg] do
  for ss in descents[w] do
   sw:=table[ss,w];
   if sw gt 0 then
    s:=ss;
    break;
   end if;
  end for;
  for y:= 1 to sw-1 do
   sy:=table[s,y];
   if sy gt sw then
    if descents[w] subset descents[sy] then
     pol:=findPoly(sw,y,klp);
     if pol ne 0 then
      indx:=Index(klp`thepolys,pol);
      if Coefficient(pol,0) ne 0 then
       Include(~klp`klp1[sy],w);
       if indx ne 0 then
        Append(~klp`pointers1[sy],indx);
       else
        Include(~klp`thepolys,pol);
        numpolys +:=1;
        Append(~klp`pointers1[sy],numpolys);
       end if;
      else
       Include(~klp`klp2[sy],w);
       if indx ne 0 then
        Append(~klp`pointers2[sy],indx);
       else
        Include(~klp`thepolys,pol);
        numpolys +:=1;
       Append(~klp`pointers2[sy],numpolys);
       end if;
      end if;
     end if;
    end if;
   end if;
   if descents[w] subset descents[y] then
    newpoly:=-findPoly(sw,y,klp) div q;
    if sy gt 0 then
     newpoly +:=findPoly(sw,sy,klp);
    end if;
    for t in {1..rank} diff descents[y] do
     x:=table[t,y];
     if x gt y and s notin descents[x] then
      newpoly +:=findPoly(sw,x,klp);
     end if;
    end for;
    for jj in [1..#klp`klp1[y]] do
     x:=klp`klp1[y,jj];
     if s notin descents[x] then
      mu:=Coefficient(klp`thepolys[klp`pointers1[y,jj]],0);
      newpoly +:=mu*findPoly(sw,x,klp);
     end if;
    end for;
    if newpoly ne 0 then
     indx:=Index(klp`thepolys,newpoly);
     if Coefficient(newpoly,0) ne 0 then
      Include(~klp`klp1[y],w);
      if indx ne 0 then
       Append(~klp`pointers1[y],indx);
      else
       Include(~klp`thepolys,newpoly);
       numpolys +:=1;
       Append(~klp`pointers1[y],numpolys);
      end if;
     else
      Include(~klp`klp2[y],w);
      if indx ne 0 then
       Append(~klp`pointers2[y],indx);
      else
       Include(~klp`thepolys,newpoly);
       numpolys +:=1;
       Append(~klp`pointers2[y],numpolys);
      end if;
     end if;
    end if;
   end if;
  end for;
  vprint WGraph, 2 : deg-w,"basis elements still to process.";
 end for;
 klp`klp2:=[];
 vprint WGraph, 2 : "Done";
 vprint WGraph, 2 : "Preparing W-graph...";
  G := NullGraph( : SparseRep );
  AddVertices( ~G, deg, descents );
  edges := [PowerSet(Integers())|];
  weights := [basering|];
  for i in [1..deg] do
    if IsDefined(klp`klp1,i) then
      for e in [1..#klp`klp1[i]] do
        M:=Integers()!(klp`klp1[i,e]);
        Append(~edges, {M,i} );
        Append(~weights, Coefficient(klp`thepolys[klp`pointers1[i,e]],0) );
      end for;
    end if;
    for ss in {1..rank} diff descents[i] do
      e:=table[ss,i];
      if e ne i then
        Append(~edges,{i,e});
        Append(~weights,1);
      end if;
    end for;
  end for;
  AddEdges(~G,edges,weights);
  vprint WGraph, 2 : "All done";
  return G;
end intrinsic;

intrinsic Partition2WGtable(pi :: SeqEnum ) -> SeqEnum, GrpFPCox
{ Returns the W-graph table and the Weyl group for the partition pi }
 require IsPartition(pi) : "pi must be a partition";
 messagenumber:=1000;
 tab1:=[[1..pi[i]]: i in [1..#pi]];
 n:=0;
 k:=0;
 tmp:=Append(pi,0) ;
 while tmp[1] gt 0 do
  k +:=1;
  j:=1;
  repeat
   n +:=1;
   tab1[j,k]:=n;
   tmp[j] +:=-1;
   j +:=1;
  until tmp[j] eq 0;
 end while;
 rank:=n-1;
 r:=#pi;
 st:={@ tab1 @};
 deg:=1;
 table:=[[Integers()|]:s in [1..rank]];
 descents:=[PowerSet(Integers())|];
 vprint WGraph, 2 : "Processing standard tableaux ...";
 current:=1;
 repeat
  tab:=st[current];
  descents[current]:={1..rank};
  for i:=1 to r do
   for j:=1 to pi[i]-1 do
    if tab[i,j+1] eq tab[i,j]+1 then
     Exclude(~descents[current],tab[i,j]);
     table[tab[i,j],current]:=current;
    end if;
   end for;
  end for;
  for i:=1 to r-1 do
   for j:=1 to pi[i+1] do
    if tab[i+1,j] eq tab[i,j]+1 then
     table[tab[i,j],current]:=-current;
    end if;
   end for;
  end for;
  for i:=2 to r do
   for k:=1 to pi[i] do
    for j:=1 to i-1 do
     for l:=k+1 to pi[j] do
      if tab[j,l] eq tab[i,k]+1 then
       Exclude(~descents[current],tab[i,k]);
       newtab:=tab;
       newtab[j,l]:=tab[i,k];
       newtab[i,k]:=tab[j,l];
       newind:=Index(st,newtab);
       if newind eq 0 then
        Include(~st,newtab);
        deg +:=1;
        table[tab[i,k],current]:=deg;
        table[tab[i,k],deg]:=current;
       else
        table[tab[i,k],current]:=newind;
        table[tab[i,k],newind]:=current;
       end if;
      end if;
     end for;
    end for;
   end for;
  end for;
  current +:=1;
  if current eq messagenumber then
    vprint WGraph, 2 :    messagenumber,"standard tableaux done";
    messagenumber +:=1000;
  end if;
 until current gt deg;
 vprint WGraph, 2 : deg,"standard tableaux in total";
 return table, CoxeterGroup(GrpFPCox,"A"*IntegerToString(rank));
end intrinsic;


intrinsic WGelement2WGtable(delt::GrpFPCoxElt,K::SetEnum) -> SeqEnum, SeqEnum
{ Returns the W-graph table and W-graph ideal of a W-graph determining element 
  delt and subset K}
 W := Parent(delt);
 era := ReflectionTable(W);
 g := Eltseq(delt);
 messagenumber:=1000;
 rank:=#era;
 vprint WGraph, 2 : "Converting the element to ShortLex form";
 top:=[];
 n:=1;
 while n le #g do
  k:=#top;
  s:=g[n];
  place:=k+1;
  u:=s;
  while k gt 0 do
   s:=era[top[k]][s];
   if s lt 0 then
    break;
   end if;
   if s lt top[k] then
    u:=s;
    place:=k;
   end if;
   k +:=-1;
  end while;
  if s lt 0 then
   Remove(~top,k);
  else
   Insert(~top,place,u);
  end if;
  n +:=1;
 end while;
 vprint WGraph, 2 : "done";
 vprint WGraph, 2 : "Computing the action of the simple reflections on the ideal ...";
 wgideal:={@ top @};
 deg:=1;
 next:=1;
 table:=[];
 for s in [1..rank] do
  table[s]:=[Integers()|];
 end for;
 repeat
  for s in [1..rank] do
   if not IsDefined(table[s],next) then
    w:=wgideal[next];
    j:=#w;
    s1:=s;
    while j gt 0 do
     s1:=era[w[j]][s1];
     if s1 le 0 then
      break;
     end if;
     j -:=1;
    end while;
    if s1 lt 0 then
     ws:=Remove(w,j);
     ind:=Index(wgideal,ws);
     if ind eq 0 then
      Include(~wgideal,ws);
      deg +:=1;
      table[s][next]:=deg;
      table[s][deg]:=next;
     else
      table[s][next]:=ind;
      table[s][ind]:=next;
     end if;
    elif s1 notin K then
     table[s][next]:=next;
    else
     table[s][next]:=-next;
    end if;
   end if;
  end for;
  next +:=1;
  if next gt messagenumber then
   vprint WGraph, 2 : messagenumber,"elements processed";
   messagenumber +:=1000;
  end if;
 until next gt deg;
 vprint WGraph, 2 : "The ideal has",deg,"elements.";
 for s in [1..rank] do
  table[s]:=[Sign(j)*(deg+1)-j: j in Reverse(table[s])];
 end for;
 return table,wgideal;
end intrinsic;


intrinsic WGidealgens2WGtable(dgens::SeqEnum,K::SetEnum) -> SeqEnum[SeqEnum[RngIntElt]], SetIndx
{ Returns the W-graph table and W-graph ideal of a W-graph determining 
  generators dgens and subset K}
 messagenumber:=1000;
 W := Universe(dgens);
 era := ReflectionTable(W);
 gens := [Eltseq(g) : g in dgens];
 rank:=#era;
 vprint WGraph, 2 : "Converting the generators to ShortLex form";
 lengths:=[Integers()|];
 for g in gens do
  gg:=[];
  n:=1;
  while n le #g do
   k:=#gg;
   s:=g[n];
   place:=k+1;
   u:=s;
   while k gt 0 do
    s:=era[gg[k]][s];
    if s lt 0 then
     break;
    end if;
    if s lt gg[k] then
     u:=s;
     place:=k;
    end if;
    k +:=-1;
   end while;
   if s lt 0 then
    Remove(~gg,k);
   else
    Insert(~gg,place,u);
   end if;
   n +:=1;
  end while;
  if #lengths eq 0 then
   shortlexgens:=[gg];
   lengths:=[#gg];
  else
   i:=1;
   len:=#gg;
   while lengths[i] le len do
    i +:=1;
    if i gt #lengths then
     break;
    end if;
   end while;
   Insert(~shortlexgens,i,gg);
   Insert(~lengths,i,len);
  end if;
 end for;
 vprint WGraph, 2 : "done";
 vprint WGraph, 2 : "Computing the action of the simple reflections on the ideal ...";
 wgideal:={@ PowerSequence(Integers())| @};
 currentlen:=lengths[#lengths];
 deg:=0;
 repeat
  Include(~wgideal,shortlexgens[#lengths]);
  Prune(~shortlexgens);
  Prune(~lengths);
  deg +:=1;
  if #lengths eq 0 then
   break;
  end if;
 until lengths[#lengths] lt currentlen;
 next:=1;
 table:=[];
 for s in [1..rank] do
  table[s]:=[Integers()|];
 end for;
 repeat
  if #wgideal[next] lt currentlen then
   currentlen-:=1;
   if #lengths gt 0 then
    while lengths[#lengths] eq currentlen do
     gen:=shortlexgens[#lengths];
     idx:=Index(wgideal,gen);
     if idx eq 0 then
      Include(~wgideal,gen);
      deg +:=1;
     end if;
     Prune(~shortlexgens);
     Prune(~lengths);
     if #lengths eq 0 then
      break;
     end if;
    end while; 
   end if;
  end if;
  for s in [1..rank] do
   if not IsDefined(table[s],next) then
    w:=wgideal[next];
    j:=#w;
    s1:=s;
    while j gt 0 do
     s1:=era[w[j]][s1];
     if s1 le 0 then
      break;
     end if;
     j -:=1;
    end while;
    if s1 lt 0 then
     ws:=Remove(w,j);
     ind:=Index(wgideal,ws);
     if ind eq 0 then
      Include(~wgideal,ws);
      deg +:=1;
      table[s][next]:=deg;
      table[s][deg]:=next;
     else
      table[s][next]:=ind;
      table[s][ind]:=next;
     end if;
    elif s1 notin K then
     table[s][next]:=next;
    else
     table[s][next]:=-next;
    end if;
   end if;
  end for;
  next +:=1;
  if next gt messagenumber then
   vprint WGraph, 2 : messagenumber,"elements processed";
   messagenumber +:=1000;
  end if;
 until next gt deg;
 vprint WGraph, 2 : "The ideal has",deg,"elements.";
 for s in [1..rank] do
  table[s]:=[Sign(j)*(deg+1)-j: j in Reverse(table[s])];
 end for;
 return table,wgideal;
end intrinsic;


intrinsic InduceWGtable(J::SeqEnum, table::SeqEnum, W::GrpFPCox) -> SeqEnum[SeqEnum[RngIntElt]]
{Returns the table of the W-graph induced from the table of a parabolic
 subgroup defined by J}
 era := ReflectionTable(W);
 rank:=#era;
 drs:={@[Integers()|]@};
 total:=1;
 cosetaction:=[];
 for i:=1 to rank do
  cosetaction[i]:=[];
 end for;
 next:=1;
 messagenumber:=1000;
 vprint WGraph, 2 : "indexing coset representatives ...";
 repeat
  x:=drs[next];
  for s in [1..rank] do
   if not IsDefined(cosetaction[s],next) then
    j:=#x;
    t:=s;
    ok:=true;
    while j gt 0 do
     t:=era[x[j]][t];
     if t lt x[j] then
      ok:=false;
      break;
     end if;
     j +:=-1;
    end while;
    if ok and t notin J then
     Include(~drs,Append(x,s));
     total +:=1;
     cosetaction[s,next]:=total;
     cosetaction[s,total]:=next;
    elif ok then
     cosetaction[s,next]:=-t;
    else
     ind:=Index(drs,x[1..j-1]);
     z:=cosetaction[t,ind];
     if z lt 0 then
      cosetaction[s,next]:=z;
     else
      ind:=Index(drs,drs[z] cat x[j..#x]);
      cosetaction[s,next]:=ind;
      cosetaction[s,ind]:=next;
     end if;
    end if;
   end if;
  end for;
  next +:=1;
  if next gt messagenumber then
   vprint WGraph, 2 : messagenumber,"cosets done";
   messagenumber +:=1000;
  end if;
 until next gt #drs;
 vprint WGraph, 2 : "There are",#drs,"cosets.";
 index:=#drs;
 delete drs;
 deg:=#table[1];
 vprint WGraph, 2 : "Writing the induced table ...";
 newtable:=[[Integers()|] : s in [1..rank]];
 for s in [1..rank] do
  for x in [1..deg] do
   for k in [1..index] do
    h:=cosetaction[s,k];
    if h gt 0 then
     newtable[s,(k-1)*deg+x]:=(h-1)*deg+x;
    else
     y:=table[Index(J,-h),x];
     newtable[s,(k-1)*deg+x]:=Sign(y)*(k-1)*deg+y;
    end if;
   end for;
  end for;
 end for;
 vprint WGraph, 2 : "done";
 return newtable;
end intrinsic;

/*
WG2HeckeRep_ := function(W,wg)
 rank := Rank(W);
 V := Vertices(wg);
 E := Edges(wg);
 L<q>:=FunctionField(Parent(Label(E[1])));
 graphrank := #V;
 JR:=[];
 if Type(wg) eq GrphUnd then
  for s in [1..rank] do
    Q := [ s in Label(u)
      select <i,i,-q^(-1)> else <i,i,q> : u in V | true where i is Index(u) ];
    for e in E do
      u := InitialVertex(e);
      v := TerminalVertex(e);
      if s in Label(u) and s notin Label(v) then
        Append(~Q, <Index(u),Index(v),L!Label(e)>);
      elif s in Label(v) and s notin Label(u) then
        Append(~Q, <Index(v),Index(u),L!Label(e)>);
      end if;
    end for;
    JR[s] := SparseMatrix( L,graphrank,graphrank,Q );
    vprint WGraph, 2 : "Matrix representing generator",s,"constructed";
  end for;
 else
  for s in [1..rank] do
    Q := [ s in Label(u)
      select <i,i,-q^(-1)> else <i,i,q> : u in V | true where i is Index(u) ];
    for e in E do
      u := InitialVertex(e);
      v := TerminalVertex(e);
      if s in Label(u) and s notin Label(v) then
        Append(~Q, <Index(u),Index(v),L!Label(e)>);
      end if;
    end for;
    JR[s] := SparseMatrix( L,graphrank,graphrank,Q );
    vprint WGraph, 2 : "Matrix representing generator",s,"constructed";
  end for;
 end if;
 return JR;
end function;
*/

intrinsic WG2HeckeRep(W::GrpFPCox,wg::GrphUnd) -> SeqEnum
{Returns a sequence of sparse matrices that satisfy the
defining relations of the Hecke algebra.}
  rank := Rank(W);
  V := Vertices(wg);
  E := Edges(wg);
  L<q>:=FunctionField(Parent(Label(E[1])));
  graphrank := #V;
  JR:=[];
  for s in [1..rank] do
    Q := [ s in Label(u)
      select <i,i,-q^(-1)> else <i,i,q> : u in V | true where i is Index(u) ];
    for e in E do
      u := InitialVertex(e);
      v := TerminalVertex(e);
      if s in Label(u) and s notin Label(v) then
        Append(~Q, <Index(u),Index(v),L!Label(e)>);
      elif s in Label(v) and s notin Label(u) then
        Append(~Q, <Index(v),Index(u),L!Label(e)>);
      end if;
    end for;
    JR[s] := SparseMatrix( L,graphrank,graphrank,Q );
    vprint WGraph, 2 : "Matrix representing generator",s,"constructed";
  end for;
  return JR;
end intrinsic;


intrinsic WG2HeckeRep(W::GrpFPCox,wg::GrphDir) -> SeqEnum
{Returns a sequence of sparse matrices that satisfy the
defining relations of the Hecke algebra.}
  rank := Rank(W);
  V := Vertices(wg);
  E := Edges(wg);
  L<q>:=FunctionField(Parent(Label(E[1])));
  graphrank := #V;
  JR:=[];
  for s in [1..rank] do
    Q := [ s in Label(u)
      select <i,i,-q^(-1)> else <i,i,q> : u in V | true where i is Index(u) ];
    for e in E do
      u := InitialVertex(e);
      v := TerminalVertex(e);
      if s in Label(u) and s notin Label(v) then
        Append(~Q, <Index(u),Index(v),L!Label(e)>);
      end if;
    end for;
    JR[s] := SparseMatrix( L,graphrank,graphrank,Q );
    vprint WGraph, 2 : "Matrix representing generator",s,"constructed";
  end for;
  return JR;
end intrinsic;

/*
WG2GroupRep_ := function(W,wg)
 rank := Rank(W);
 V := Vertices(wg);
 E := Edges(wg);
 L:=Parent(Label(E[1]));
 graphrank := #V;
 JR:=[];
 if Type(wg) eq GrphUnd then
  for s in [1..rank] do
    Q := [ s in Label(u) 
      select <i,i,L!-1> else <i,i,L!1> : u in V | true where i is Index(u) ];
    for e in E do
      u := InitialVertex(e);
      v := TerminalVertex(e);
      if s in Label(u) and s notin Label(v) then
        Append(~Q, <Index(u),Index(v),L!Label(e)>);
      elif s in Label(v) and s notin Label(u) then
        Append(~Q, <Index(v),Index(u),L!Label(e)>);
      end if;
    end for;
    JR[s] := SparseMatrix( L,graphrank,graphrank,Q );
    vprint WGraph, 2 : "Matrix representing generator",s,"constructed";
  end for;
 else
  for s in [1..rank] do
    Q := [ s in Label(u) 
      select <i,i,L!-1> else <i,i,L!1> : u in V | true where i is Index(u) ];
    for e in E do
      u := InitialVertex(e);
      v := TerminalVertex(e);
      if s in Label(u) and s notin Label(v) then
        Append(~Q, <Index(u),Index(v),L!Label(e)>);
      end if;
    end for;
    JR[s] := SparseMatrix( L,graphrank,graphrank,Q );
    vprint WGraph, 2 : "Matrix representing generator",s,"constructed";
  end for;
 end if;
 return JR;
end function;
*/

intrinsic WG2GroupRep(W::GrpFPCox,wg::GrphUnd) -> SeqEnum
{ The matrix representation of a W-graph }
  rank := Rank(W);
  V := Vertices(wg);
  E := Edges(wg);
  L:=Parent(Label(E[1]));
  graphrank := #V;
  JR:=[];
  for s in [1..rank] do
    Q := [ s in Label(u) 
      select <i,i,L!-1> else <i,i,L!1> : u in V | true where i is Index(u) ];
    for e in E do
      u := InitialVertex(e);
      v := TerminalVertex(e);
      if s in Label(u) and s notin Label(v) then
        Append(~Q, <Index(u),Index(v),L!Label(e)>);
      elif s in Label(v) and s notin Label(u) then
        Append(~Q, <Index(v),Index(u),L!Label(e)>);
      end if;
    end for;
    JR[s] := SparseMatrix( L,graphrank,graphrank,Q );
    vprint WGraph, 2 : "Matrix representing generator",s,"constructed";
  end for;
  return JR;
end intrinsic;

intrinsic WG2GroupRep(W::GrpFPCox,wg::GrphDir) -> SeqEnum
{ The matrix representation of a W-graph }
  rank := Rank(W);
  V := Vertices(wg);
  E := Edges(wg);
  L:=Parent(Label(E[1]));
  graphrank := #V;
  JR:=[];
  for s in [1..rank] do
    Q := [ s in Label(u) 
      select <i,i,L!-1> else <i,i,L!1> : u in V | true where i is Index(u) ];
    for e in E do
      u := InitialVertex(e);
      v := TerminalVertex(e);
      if s in Label(u) and s notin Label(v) then
        Append(~Q, <Index(u),Index(v),L!Label(e)>);
      end if;
    end for;
    JR[s] := SparseMatrix( L,graphrank,graphrank,Q );
    vprint WGraph, 2 : "Matrix representing generator",s,"constructed";
  end for;
  return JR;
end intrinsic;

intrinsic TestHeckeRep(W::GrpFPCox,r::SeqEnum)
{Tests whether the matrices in r satisfy the defining relations of the
Hecke algebra of the Coxeter group W}
 mij := mijsequence(CoxeterMatrix(W));
 L:=BaseRing(r[1]);
 q:=L.1;
 n:=NumberOfRows(r[1]);
 I:=SparseMatrix(L,n,n,[<i,i,1>: i in [1..n]]);
 i:=1;
 k:=0;
 for j:=1 to #mij do
  k +:=1;
  if mij[j] eq 1 then
   vprint WGraph, 2 : r[i]^2 eq I + (q-q^(-1))*r[i],<i,i>,1;
   assert r[i]^2 eq I + (q-q^(-1))*r[i];
   i +:=1;
   k:=0;
  else
   if mij[j] eq 2 then
    vprint WGraph, 2 : r[i]*r[k] eq r[k]*r[i],<k,i>,2;
    assert r[i]*r[k] eq r[k]*r[i];
   else
    x:=(r[i]*r[k])^(mij[j] div 2);
    if IsEven(mij[j]) then
     vprint WGraph, 2 : x*r[i] eq r[i]*x,<k,i>,mij[j];
     assert x*r[i] eq r[i]*x;
    else
     vprint WGraph, 2 : x*r[i] eq r[k]*x,<k,i>,mij[j];
     assert x*r[i] eq r[k]*x;
    end if;
   end if;
  end if;
 end for;
end intrinsic;


TestWG_ := procedure(W,wg) 
 mij := mijsequence(CoxeterMatrix(W));
 V := Vertices(wg);
 E := Edges(wg);
 try
  L<q>:=FunctionField(Parent(Label(E[1])));
 catch e;
  L := FunctionField(Integers()); q := L.1;
 end try;
 n:=#V;
 I:=SparseMatrix(L,n,n,[<i,i,1>: i in [1..n]]);
 i:=1;
 k:=0;
 if Type(wg) eq GrphUnd then
  Q:= [ i in Label(u) 
    select <h,h,-q^(-1)> else <h,h,q> : u in V | true where h is Index(u) ];
  for e in E do
   u:= InitialVertex(e);
   v:= TerminalVertex(e);
   if i in Label(u) and i notin Label(v) then
    Append(~Q, <Index(u),Index(v),L!Label(e)>);
   elif i in Label(v) and i notin Label(u) then
    Append(~Q, <Index(v),Index(u),L!Label(e)>);
   end if;
  end for;
  S:= SparseMatrix( L,n,n,Q );
  for j:=1 to #mij do
   k +:=1;
   if mij[j] eq 1 then
    flag := (S^2 eq I + (q-q^(-1))*S);
    vprint WGraph, 2 : flag,<i,i>,1;
    error if not flag, "test failed";
    assert S^2 eq I + (q-q^(-1))*S;
    i +:=1;
    k:=0;
    Q:= [ i in Label(u) 
      select <h,h,-q^(-1)> else <h,h,q> : u in V | true where h is Index(u) ];
    for e in E do
     u:= InitialVertex(e);
     v:= TerminalVertex(e);
     if i in Label(u) and i notin Label(v) then
      Append(~Q, <Index(u),Index(v),L!Label(e)>);
     elif i in Label(v) and i notin Label(u) then
      Append(~Q, <Index(v),Index(u),L!Label(e)>);
     end if;
    end for;
    S:= SparseMatrix( L,n,n,Q );
   else
    Q:= [ k in Label(u) 
      select <h,h,-q^(-1)> else <h,h,q> : u in V | true where h is Index(u) ];
    for e in E do
     u:= InitialVertex(e);
     v:= TerminalVertex(e);
     if k in Label(u) and k notin Label(v) then
      Append(~Q, <Index(u),Index(v),L!Label(e)>);
     elif k in Label(v) and k notin Label(u) then
      Append(~Q, <Index(v),Index(u),L!Label(e)>);
     end if;
    end for;
    T:= SparseMatrix( L,n,n,Q );
    if mij[j] eq 2 then
     vprint WGraph, 2 : S*T eq T*S,<k,i>,2;
     error if not flag, "test failed";
     assert S*T eq T*S;
    elif mij[j] eq 3 then
     R:=S*T;
     vprint WGraph, 2 : R*S eq T*R,<k,i>,3;
     error if not flag, "test failed";
    elif mij[j] eq 4 then
     R:=S*T;
     T:=T*R;
     flag := (S*T eq T*S);
     vprint WGraph, 2 : flag,<k,i>,4;
     error if not flag, "test failed";
    elif mij[j] eq 5 then
     R:=(S*T)^2;
     flag := (R*S eq T*R);
     vprint WGraph, 2 : flag,<k,i>,5;
     error if not flag, "test failed";
    else
     R:=(S*T)^(mij[j] div 2);
     if IsEven(mij[j]) then
       flag := (S*R eq R*S);
       vprint WGraph, 2 : flag,<k,i>,mij[j];
       error if not flag, "test failed";
     else
       flag := (T*R eq R*S);
       vprint WGraph, 2 : flag,<k,i>,mij[j];
     error if not flag, "test failed";
     end if;
    end if;
   end if;
  end for;
 else
  Q:= [ i in Label(u) 
    select <h,h,-q^(-1)> else <h,h,q> : u in V | true where h is Index(u) ];
  for e in E do
   u:= InitialVertex(e);
   v:= TerminalVertex(e);
   if i in Label(u) and i notin Label(v) then
    Append(~Q, <Index(u),Index(v),L!Label(e)>);
   end if;
  end for;
  S:= SparseMatrix( L,n,n,Q );
  for j:=1 to #mij do
   k +:=1;
   if mij[j] eq 1 then
    flag := (S^2 eq I + (q-q^(-1))*S);
    vprint WGraph, 2 : flag,<i,i>,1;
     error if not flag, "test failed";
    i +:=1;
    k:=0;
    Q:= [ i in Label(u)
      select <h,h,-q^(-1)> else <h,h,q> : u in V | true where h is Index(u) ];
    for e in E do
     u:= InitialVertex(e);
     v:= TerminalVertex(e);
     if i in Label(u) and i notin Label(v) then
      Append(~Q, <Index(u),Index(v),L!Label(e)>);
     end if;
    end for;
    S:= SparseMatrix( L,n,n,Q );
   else
    Q:= [ k in Label(u) 
      select <h,h,-q^(-1)> else <h,h,q> : u in V | true where h is Index(u) ];
    for e in E do
     u:= InitialVertex(e);
     v:= TerminalVertex(e);
     if k in Label(u) and k notin Label(v) then
      Append(~Q, <Index(u),Index(v),L!Label(e)>);
     end if;
    end for;
    T:= SparseMatrix( L,n,n,Q );
    if mij[j] eq 2 then
     flag := (S*T eq T*S);
     vprint WGraph, 2 : flag,<k,i>,2;
     error if not flag, "test failed";
    elif mij[j] eq 3 then
     R:=S*T;
     flag := (R*S eq T*R);
     vprint WGraph, 2 : flag,<k,i>,3;
     error if not flag, "test failed";
    elif mij[j] eq 4 then
     R:=S*T;
     T:=T*R;
     flag := (S*T eq T*S);
     vprint WGraph, 2 : flag,<k,i>,4;
     error if not flag, "test failed";
    elif mij[j] eq 5 then
     R:=(S*T)^2;
     flag := (R*S eq T*R);
     vprint WGraph, 2 : flag,<k,i>,5;
     error if not flag, "test failed";
    else
     R:=(S*T)^(mij[j] div 2);
     if IsEven(mij[j]) then
       flag := (S*R eq R*S);
       vprint WGraph, 2 : flag,<k,i>,mij[j];
       error if not flag, "test failed";
     else
       flag := (T*R eq R*S);
       vprint WGraph, 2 : flag,<k,i>,mij[j];
     error if not flag, "test failed";
     end if;
    end if;
   end if;
  end for;
 end if;
 print "test passed";
end procedure;

intrinsic TestWG(W::GrpFPCox,wg::GrphUnd) 
{ Test the W-graph wg}
  TestWG_(W,wg);
end intrinsic;

intrinsic TestWG(W::GrpFPCox,wg::GrphDir) 
{ Test the W-graph wg}
  TestWG_(W,wg);
end intrinsic;

intrinsic TestWG(tp::MonStgElt,wg::GrphUnd) 
{ Test the W-graph wg where W is the Coxeter group of type tp}
  W := CoxeterGroup(GrpFPCox,tp);
  TestWG_(W,wg);
end intrinsic;

intrinsic TestWG(tp::MonStgElt,wg::GrphDir) 
{ Test the W-graph wg where W is the Coxeter group of type tp}
  W := CoxeterGroup(GrpFPCox,tp);
  TestWG_(W,wg);
end intrinsic;

intrinsic WriteWG(file::MonStgElt,wg::GrphUnd)
{ Writes the W-graph to a file }
 Write(file,&cat["wg:=Graph<",IntegerToString(NumberOfVertices(wg)),"|"]);
 Write(file,Edges(wg));
 Write(file,": SparseRep >;");
 Write(file,"AssignVertexLabels(~wg,");
 Write(file,VertexLabels(wg),"Magma");
 Write(file,");");
 Write(file,"AssignEdgeLabels(~wg,");
 Write(file,EdgeLabels(wg),"Magma");
 Write(file,");");
end intrinsic;


intrinsic WriteWG(file::MonStgElt,wg::GrphDir)
{ Writes the W-graph to a file }
 Write(file,&cat["wg:=Digraph<",IntegerToString(NumberOfVertices(wg)),"|"]);
 Write(file,Edges(wg));
 Write(file,": SparseRep >;");
 Write(file,"AssignVertexLabels(~wg,");
 Write(file,VertexLabels(wg),"Magma");
 Write(file,");");
 Write(file,"AssignEdgeLabels(~wg,");
 Write(file,EdgeLabels(wg),"Magma");
 Write(file,");");
end intrinsic;

InduceWG_ := function(W,wg,seq) 
 era := ReflectionTable(W);
 klpcontext:=recformat<klp1,pointers1,klp2,pointers2,thepolys>;
 type:=Type(wg);
 try 
   basering:=Parent(Label(Representative(Edges(wg))));
 catch e
   basering:=Integers();
 end try;
 wgdim:=NumberOfVertices(wg);
 V:=Vertices(wg);
 wgdescents:=[{seq[j]: j in Label(V[gamma])}: gamma in [1..wgdim]];
 wgedges:=[PowerIndexedSet(Integers())|];
 wgedgeweights:=[PowerSequence(basering)|];
 for gamma in [1..wgdim] do
  wgedges[gamma]:={@ @};
  wgedgeweights[gamma]:=[];
  if type eq GrphUnd then
   nbs:=Neighbours(V[gamma]);
  else
   nbs:=OutNeighbours(V[gamma]);
  end if;
  for v in nbs do
   delta:=Index(V,v);
   Include(~wgedges[gamma],delta);
   if type eq GrphUnd then
    Append(~wgedgeweights[gamma],Label(Edges(wg)!{V[gamma],V[delta]}));
   else
    Append(~wgedgeweights[gamma],Label(Edges(wg)![V[gamma],V[delta]]));
   end if;
  end for;
 end for;
 polyring := PolynomialRing(basering); q := polyring.1;
 J:=SequenceToSet(seq);
 rank:=#era;
 vprint WGraph, 2 : "Computing coset representatives and action ...";
 drs:={@[Integers()|]@};
 index:=1;
 cosetaction:=[];
 for i:=1 to rank do
  cosetaction[i]:=[];
 end for;
 next:=1;
 messagenumber:=1000;
 vprint WGraph, 2 : "indexing coset representatives ...";
 repeat
  x:=drs[next];
  for s in [1..rank] do
   if not IsDefined(cosetaction[s],next) then
    j:=#x;
    t:=s;
    ok:=true;
    while j gt 0 do
     t:=era[x[j]][t];
     if t lt x[j] then
      ok:=false;
      break;
     end if;
     j +:=-1;
    end while;
    if ok and t notin J then
     Include(~drs,Append(x,s));
     index +:=1;
     cosetaction[s,next]:=index;
     cosetaction[s,index]:=next;
    elif ok then
     cosetaction[s,next]:=-t;
    else
     ind:=Index(drs,x[1..j-1]);
     z:=cosetaction[t,ind];
     if z lt 0 then
      cosetaction[s,next]:=z;
     else
      ind:=Index(drs,drs[z] cat x[j..#x]);
      cosetaction[s,next]:=ind;
      cosetaction[s,ind]:=next;
     end if;
    end if;
   end if;
  end for;
  next +:=1;
  if next gt messagenumber then
   vprint WGraph, 2 : messagenumber,"cosets done";
   messagenumber +:=1000;
  end if;
 until next gt index;
 vprint WGraph, 2 : "There are",index,"cosets.";
 vprint WGraph, 2 : "Determining descent sets ...";
 descents:=[];
 for w in [1..index] do
  descents[w]:=[];
  for gamma in [1..wgdim] do
   descents[w,gamma]:={{1..rank}|};
   for s in [1..rank] do
    sw:=cosetaction[s,w];
    if sw lt 0 then
     if -sw in wgdescents[gamma] then
      Include(~descents[w,gamma],s);
     end if;
    elif sw lt w then
     Include(~descents[w,gamma],s);
    end if;
   end for;
  end for;
 end for;
 vprint WGraph, 2 : "Done.";
 maxbelow:=[];
 maxbelow[1]:={@Integers()|@};
 minmaxbelow:=[0];
 for i in [2..#drs] do
  wordi:=drs[i];
  maxbelow[i]:={@Integers()|@};
  minmaxbelow[i]:=i;
  for k in [1..#drs[i]] do
   removek:=Index(drs,[wordi[m] : m in [1..k-1]]);
   nocancelling:=true;
   for l in [k+1..#drs[i]] do
    next:=cosetaction[wordi[l],removek];
    if next lt removek then
     nocancelling:=false;
     break l;
    else
     removek:=next;
    end if;
   end for;
   if nocancelling then
    Include(~maxbelow[i],removek);
    minmaxbelow[i]:=Minimum(minmaxbelow[i],removek);
   end if;
  end for;
 end for;
 startw:=2;
 while #drs[startw] eq 1 do
  startw +:=1;
 end while;
 
 findPoly:=function(w,gamma,y,delta,klp)
  yy:=y;
  i:=0;
  desw:=descents[w,gamma];
  repeat
   found:=true;
   if yy in maxbelow[w] then
    if gamma eq delta then
     return q^i;
    else
     return polyring!0;
    end if;
   elif yy gt minmaxbelow[w] then
    return polyring!0;
   else
    desyy:=descents[yy,delta];
    if desw notsubset desyy then
     s:=Representative(desw diff desyy);
     syy:=cosetaction[s,yy];
     if syy lt 0 then
      return polyring!0;
     else
      i +:=1;
      yy:=syy;
      found:=false;
     end if;
    else
     indx:=Index(klp`klp1[w,gamma],<yy,delta>);
     if indx ne 0 then
      return q^i*klp`thepolys[klp`pointers1[w,gamma,indx]];
     else
      indx:=Index(klp`klp2[w,gamma],<yy,delta>);
      if indx ne 0 then
       return q^i*klp`thepolys[klp`pointers2[w,gamma,indx]];
      else
       return polyring!0;
      end if;
     end if;
    end if;
   end if;
  until found;
 end function;
 
 vprint WGraph, 2 : "Done";
 vprint WGraph, 2 : "Computing Kazhdan-Lusztig polynomials ...";
 ttt := Cputime();
 klp:=rec<klpcontext |
  klp1:=[PowerSequence(PowerIndexedSet(CartesianPower(Integers(),2)))| ],
  pointers1:=[PowerSequence(PowerSequence(Integers()))|],
  klp2:=[PowerSequence(PowerIndexedSet(CartesianPower(Integers(),2)))| ],
  pointers2:=[PowerSequence(PowerSequence(Integers()))|],
  thepolys:={@ polyring| @}>;
 numpolys:=0;
 for w in [startw..#drs] do
 klp`klp1[w]:=[];
 klp`pointers1[w]:=[];
 klp`klp2[w]:=[];
 klp`pointers2[w]:=[];
 for gamma in [1..wgdim] do
  klp`klp1[w,gamma]:={@ @};
  klp`pointers1[w,gamma]:=[];
  klp`klp2[w,gamma]:={@ @};
  klp`pointers2[w,gamma]:=[];
 end for;
  s:=drs[w][#drs[w]];
  v:=cosetaction[s,w];
  for gamma in [1..wgdim] do
   if v lt startw then
    numvedges:=0;
   else
    numvedges:=#klp`klp1[v,gamma];
   end if;
   for y:=minmaxbelow[w]-1 to 1 by -1 do
    for delta in [1..wgdim] do
     if descents[w,gamma] subset descents[y,delta] then
      sy:=cosetaction[s,y];
      if sy lt 0 then
       newpoly:=(q^2+1)*findPoly(v,gamma,y,delta,klp) div q;
       for e in [1..#wgedges[delta]] do
        theta:=wgedges[delta,e];
        if -sy notin wgdescents[theta] then
         newpoly +:=wgedgeweights[delta,e]*findPoly(v,gamma,y,theta,klp);
        end if;
       end for;
       for zz:=1 to numvedges do
        z:=klp`klp1[v,gamma,zz][1];
        if z gt y then
         zeta:=klp`klp1[v,gamma,zz][2];
         if s in descents[z,zeta] then
          mu:=Coefficient(klp`thepolys[klp`pointers1[v,gamma,zz]],0);
          newpoly-:=mu*findPoly(z,zeta,y,delta,klp);
         end if;
        end if;
       end for;
       for z in maxbelow[v] do
        if s in descents[z,gamma] then
         newpoly-:=findPoly(z,gamma,y,delta,klp);
        end if;
       end for;
       if newpoly ne 0 then
        indx:=Index(klp`thepolys,newpoly);
        if Coefficient(newpoly,0) ne 0 then
         Include(~klp`klp1[w,gamma],<y,delta>);
         if indx ne 0 then
          Append(~klp`pointers1[w,gamma],indx);
         else
          Include(~klp`thepolys,newpoly);
          numpolys +:=1;
          Append(~klp`pointers1[w,gamma],numpolys);
         end if;
        else
         Include(~klp`klp2[w,gamma],<y,delta>);
         if indx ne 0 then
          Append(~klp`pointers2[w,gamma],indx);
         else
          Include(~klp`thepolys,newpoly);
          numpolys +:=1;
          Append(~klp`pointers2[w,gamma],numpolys);
         end if;
        end if;
       end if;
      else
       newpoly:=findPoly(v,gamma,y,delta,klp) div q;
       newpoly +:=findPoly(v,gamma,sy,delta,klp);
       for zz:=1 to numvedges do
        z:=klp`klp1[v,gamma,zz][1];
        if z gt y then
         zeta:=klp`klp1[v,gamma,zz][2];
         if s in descents[z,zeta] then
          mu:=Coefficient(klp`thepolys[klp`pointers1[v,gamma,zz]],0);
          newpoly-:=mu*findPoly(z,zeta,y,delta,klp);
         end if;
        end if;
       end for;
       for z in maxbelow[v] do
        if s in descents[z,gamma] then
         newpoly-:=findPoly(z,gamma,y,delta,klp);
        end if;
       end for;
       if newpoly ne 0 then
        indx:=Index(klp`thepolys,newpoly);
        if Coefficient(newpoly,0) ne 0 then
         Include(~klp`klp1[w,gamma],<y,delta>);
         if indx ne 0 then
          Append(~klp`pointers1[w,gamma],indx);
         else
          Include(~klp`thepolys,newpoly);
          numpolys +:=1;
          Append(~klp`pointers1[w,gamma],numpolys);
         end if;
        else
         Include(~klp`klp2[w,gamma],<y,delta>);
         if indx ne 0 then
          Append(~klp`pointers2[w,gamma],indx);
         else
          Include(~klp`thepolys,newpoly);
          numpolys +:=1;
          Append(~klp`pointers2[w,gamma],numpolys);
         end if;
        end if;
       end if;
      end if;
     end if;
    end for;
   end for;
  end for;
  vprint WGraph, 2 : w,"cosets done.","Computation time:",Cputime(ttt),
    "Memory usage:",GetMemoryUsage();
 end for;
 klp`klp2:=[];
 consts:=[];
 for j:=1 to #klp`thepolys do
  Append(~consts,Coefficient(klp`thepolys[j],0));
 end for;
 delete klp`thepolys;
 deg:=index*wgdim;
 vprint WGraph, 2 : "Assembling graph ...";
 if type eq GrphUnd then
  indwg:= Graph< deg | : SparseRep>;
 else
  indwg:= Digraph< deg | : SparseRep>;
 end if;
 vprint WGraph, 2 : "Assigning vertex labels ...";
 AssignVertexLabels( ~indwg,[descents[i+1,j+1] where i,j is Quotrem(N-1,wgdim) : N in [1..deg]]);
 delete descents;
 vprint WGraph, 2 : "done";
 vprint WGraph, 2 : "Adding horizontal edges ...";
 for w:=1 to index do
  for gamma in [1..wgdim] do
   for delta in wgedges[gamma] do
    n:=(w-1)*wgdim+gamma;
    m:=(w-1)*wgdim+delta;
    if Label(Vertices(indwg)[n]) notsubset Label(Vertices(indwg)[m]) then
     AddEdge(~indwg,n,m,wgedgeweights[gamma,Index(wgedges[gamma],delta)]);
    end if;
   end for;
  end for;
 end for;
 vprint WGraph, 2 : "done";
 vprint WGraph, 2 : "Adding vertical edges ...";
 for w:=2 to index do
  for v in maxbelow[w] do
   for gamma in [1..wgdim] do
   n:=(w-1)*wgdim+gamma;
   m:=(v-1)*wgdim+gamma;
    if Label(Vertices(indwg)[n]) notsubset Label(Vertices(indwg)[m]) then
     AddEdge(~indwg,n,m,basering!1);
    end if;
    if Label(Vertices(indwg)[m]) notsubset Label(Vertices(indwg)[n]) then
     AddEdge(~indwg,m,n,basering!1);
    end if;
   end for;
  end for;
 end for;
 vprint WGraph, 2 : "done";
 vprint WGraph, 2 : "Adding transverse edges ...";
 for w:=startw to index do
  for gamma:=1 to wgdim do
   ee:=klp`klp1[w,gamma];
   for e in ee do
    n:=(e[1]-1)*wgdim+e[2];
    m:=(w-1)*wgdim+gamma;
    if Label(Vertices(indwg)[n]) ne Label(Vertices(indwg)[m]) then
     AddEdge(~indwg,n,m,consts[klp`pointers1[w,gamma,Index(ee,e)]]);
    end if;
   end for;
  end for;
 end for;
 vprint WGraph, 2 : "All done";
 return indwg;
end function;

intrinsic InduceWG(W::GrpFPCox,wg::GrphUnd,seq::SeqEnum) -> GrphUnd
{Induces a W-graph from a standard parabolic subgroup}
  return InduceWG_(W,wg,seq);
end intrinsic;

intrinsic InduceWG(W::GrpFPCox,wg::GrphDir,seq::SeqEnum) -> GrphDir
{Induces a W-graph from a standard parabolic subgroup}
  return InduceWG_(W,wg,seq);
end intrinsic;

intrinsic MakeDirected(wg::GrphUnd) -> GrphDir
{ Convert an undirected W-graph to a directed W-graph }
 V:=Vertices(wg);
 E:=Edges(wg);
 D:=Digraph<#V | : SparseRep >;
 AssignVertexLabels(~D,VertexLabels(wg));
 edges:=[];
 edgelabels:=[];
 for i in [1..#E] do
  e:=E[i];
  u:=InitialVertex(e);
  j:=Index(V,u);
  v:=TerminalVertex(e);
  k:=Index(V,v);
  Lu:=Label(u);
  Lv:=Label(v);
  if Lu notsubset Lv then
   Append(~edges,[j,k]);
   Append(~edgelabels,Label(e));
  end if;
  if Lv notsubset Lu then
   Append(~edges,[k,j]);
   Append(~edgelabels,Label(e));
  end if;
 end for;
 AddEdges(~D,edges,edgelabels);
 return D;
end intrinsic;


intrinsic IsWGsymmetric(wg::GrphUnd) -> BoolElt, GrphUnd
{ Test a W-graph for symmetry }
  return true,wg;
end intrinsic;

intrinsic IsWGsymmetric(wg::GrphDir) -> BoolElt, GrphUnd
{ Test a W-graph for symmetry }
  E:=Edges(wg);
  edges:={@ @};
  weights:=[];
  sym:=true;
  for e in E do
   u:=InitialVertex(e);
   v:=TerminalVertex(e);
   l:=Label(e);
   if v notadj u then
    if Label(v) notsubset Label(u) then
     sym:=false;
     break;
    else
     Include(~edges,{u,v});
     Append(~weights,l);
    end if;
   elif Label(E![v,u]) ne l then
    sym:=false;
    break;
   elif {u,v} notin edges then
    Include(~edges,{u,v});
    Append(~weights,l);
   end if;
  end for;
  if sym then
   uwg:=Graph<NumberOfVertices(wg) | : SparseRep >;
   AssignVertexLabels(~uwg,VertexLabels(wg));
   AddEdges(~uwg,IndexedSetToSequence(edges),weights);
   return sym,uwg;
  else
   return sym, _;
  end if;
end intrinsic;

intrinsic GetCells(wg::GrphUnd) -> SeqEnum
{ Return the cells of  W-graph }
  comps:= StronglyConnectedComponents(MakeDirected(wg)); 
  return [{Index(j) : j in comps[i]} : i in [1..#comps]];
end intrinsic;

intrinsic GetCells(wg::GrphDir) -> SeqEnum
{ Return the cells of  W-graph }
  comps:= StronglyConnectedComponents(wg);
  return [{Index(j) : j in comps[i]} : i in [1..#comps]];
end intrinsic;

/* Use Transversal(W,J) instead of DReps

intrinsic DReps(W::GrpFPCox,J::SetEnum) -> SeqEnum
{The sequence of distinguished coset reoresentatives for a standard
parabolic subgroup of a Coxeter group}
 era := ReflectionTable(W);
 drs:=[[Integers()|]];
 next:=1;
 repeat
  x:=drs[next];
  for s in [1..#era] do
   j:=#x;
   t:=s;
   ok:=true;
   while j gt 0 do
    t:=era[x[j]][t];
    if t lt x[j] then
     ok:=false;
     break;
    end if;
    j +:=-1;
   end while;
   if ok and t notin J then
    Append(~drs,Append(x,s));
   end if;
  end for;
  next +:=1;
 until next gt #drs;
 return drs;
end intrinsic;
*/

function renumberverts(wg,perm)
 type:=Type(wg);
 n:=NumberOfVertices(wg);
 invperm:=[];
 for i in [1..#perm] do
  invperm[perm[i]]:=i;
 end for;
 if type eq GrphDir then
  newwg:=Digraph< n | : SparseRep >;
  AssignVertexLabels(~newwg, [Label(Vertices(wg)[perm[i]]) : i in [1..n]]);
  AddEdges(~newwg,[[invperm[Index(Vertices(wg),InitialVertex(Edges(wg)[i]))],invperm[Index(Vertices(wg),TerminalVertex(Edges(wg)[i]))]]: i in [1..#Edges(wg)]],[Label(Edges(wg)[i]): i in [1..#Edges(wg)]]);
 else
  newwg:=Graph< n | : SparseRep >;
  AssignVertexLabels(~newwg, [Label(Vertices(wg)[perm[i]]) : i in [1..n]]);
  AddEdges(~newwg,[{invperm[Index(Vertices(wg),InitialVertex(Edges(wg)[i]))],invperm[Index(Vertices(wg),TerminalVertex(Edges(wg)[i]))]}: i in [1..#Edges(wg)]],[Label(Edges(wg)[i]): i in [1..#Edges(wg)]]);
 end if;
 return newwg;
end function;

procedure mult(~w,s,era )
u:=s;
place:=#w + 1;
j:=#w;
t:=s;
while j gt 0 do
 t:=era[w[j]][t];
 if t le 0 then
  break;
 end if;
 if t lt w[j] then
  u:=t;
  place:=j;
 end if;
 j:=j-1;
end while;
if t lt 0 then
 Remove(~w,j);
else
 Insert(~w,place,u);
end if;
end procedure;

