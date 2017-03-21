// functions written by Jon F. Carlson and Nham Ngo, June, 2012

freeze;

//////////////////////////////////////////////////////////////////////////

intrinsic SocleLayers(M::ModRng) -> SeqEnum, ModMatFld
{Return the list of dimensions of each Socle layer, and the basis matrix 
of the Socle filtration. The matrix is structured so that the last few
rows are a basis for the socle.}

S,f:=Socle(M);
m:=Dimension(M);
n:=Dimension(S);
Dim:=[n];
B1:=[ Image(f,x): x in Basis(S)];
BasisMatrix:=B1;
while n ne m do
   Q,q:=quo<M|S>;
   N:=Socle(Q);
   B:=Basis(N);
   L:=[ x@@q : x in B];
   S:=sub<M|B1, L>;
   B1:=Basis(S);
   n:=#B1;
   Append(~Dim,n);
   for i:=1 to #L do
      Append(~BasisMatrix, L[i]);
   end for;
end while;

	return Dim, KMatrixSpace(Field(M),m,m)!BasisMatrix;

end intrinsic;

/////////////////////////////////////////////////////////////////

RadicalMaps:=function(M)

W,f:=JacobsonRadical(M);
rad:=[M, W];
map:=[* f *];
while Dimension(W) ne 0 do
W,g:=JacobsonRadical(W);
Append(~rad,W);
h:=g*map[#map];
Append(~map,h);
end while;

	return rad, map;

end function;

///////////////////////////////////////////////////////////////////

intrinsic RadicalLayers(M::ModRng) -> SeqEnum, ModMatFld
{Returns list of dimensions of each powers of the Jacobson radical and 
the basis matrix of radical filtration. If d is the dimension of J^n,
the n-th power of the Jacobson radical, then the last d rows of the 
matrix are a basis of J^n.}

RL,Ma:=RadicalMaps(M);
n:=#RL;
k:=Dimension(M);
L:=[k];
B:=[* Basis(M) *];
for i:=2 to n do
   Append(~L,Dimension(RL[i]));
   Ba:=Basis(RL[i]);
   Append(~B, [Image(Ma[i-1],x): x in Ba ]);
end for;
B1:=Reverse(B);
m:=#B1;
BasisMatrix:=B1[1];
for i:=2 to m do
   C:=Reverse(B1[i]);
   for j:=1 to #C do
      if C[j] notin BasisMatrix then
         C1 := Append(BasisMatrix,C[j]);
         if IsIndependent(C1) then
            BasisMatrix:=C1;
         end if;
      end if;
   end for;
end for;

	return L, KMatrixSpace(Field(M),k,k)!Reverse(BasisMatrix);

end intrinsic;

/////////////////////////////////////////////////////////////////////

Classify:=function(S,m)

n:=#S;
T:=[m];
for i:=m+1 to n do
   if IsIsomorphic(S[i],S[m]) then
      Append(~T,i);
   end if;
end for;

	return T;

end function;

///////////////////////////////////////////////////////////////////

intrinsic IsomorphismClasses(S::SeqEnum) -> SeqEnum, SeqEnum
{Returns a sequence of representatives of isomorphism classes of modules 
in sequence of modules S and a list of the indices of the elements of S
that are isomorphic to each element in the sequence of classes. }

i:=1;
F:=[];
n:=#S;
mll :=[];
while i le n do
   if i notin mll then
      Filter := Classify(S,i);
      Append(~F,Filter);
      mll  cat:=Filter;
   end if;
   i:=i+1;
end while;
B := [S[x[1]]:x in F];

	return B, F;

end intrinsic;

/////////////////////////////////////////////////////////////////////////


intrinsic IsomorphismTypes(S::SeqEnum) -> SeqEnum, SeqEnum
{Return the sequence of isomorphic classes of modules in the sequence S
and sequence listing the index in the sequence of isomorphism classes 
of each element of S.}

M, F :=IsomorphismClasses(S);
C:=[];
for i:=1 to #F do
   for j:=1 to #F[i] do
      C[F[i][j]]:=i;
   end for;
end for;

	return M, C;

end intrinsic;

//////////////////////////////////////////////////////////////////////

intrinsic IsomorphismTypesComparedToList
			(L::SeqEnum, S::SeqEnum) -> SeqEnum
{Returns a sequence whose i-th element is the index of the element of 
S that that is isomorphic to L[i]. In the event that  L[i] is not isomorphic 
to any element in S, then the i-th element in the sequence is 0.}

I, C :=IsomorphismClasses(L);
B:=[];
for i:=1 to #I do
   B[i]:=0;
   for j:=1 to #S do
      if IsIsomorphic(I[i],S[j]) then
         B[i]:=j;
      end if;
   end for;
end for;
V:=[];
n:=#B;
for b:=1 to n do
   for c:=1 to #C[b] do
      V[C[b][c]]:=B[b];
   end for;
end for;

	return V;

end intrinsic;

///////////////////////////////////////////////////////////////////////

intrinsic IsomorphismTypesOfBasicAlgebraSequence(S::SeqEnum) -> SeqEnum
{Given a sequence of irreducible modules S over a Basic algebra A. 
Return a sequence of isomorphism types comparing with the simple 
modules of A.}

require Type(S[1]) eq ModAlgBas: "Not Module over Basic algebra";
A:=Algebra(S[1]);
I:=IdempotentGenerators(A);
T:=[];
for i:=1 to #S do
   B:=[j:j in [1..#I]|Action(S[i]).j ne 0];
   Append(~T,B[1]);
end for;

	return T;

end intrinsic;

///////////////////////////////////////////////////////////////////////

intrinsic IsomorphismTypesOfRadicalLayers(M::ModAlgBas) -> SeqEnum
{Given a module M over a basic algebra, return the sequence of Isomorphism 
types of simple composition factors in each radical layer.}

A:=Algebra(M);
W:=M;
L:=[];
n:=#IdempotentGenerators(A);
while Dimension(W) ne 0 do
   J:=JacobsonRadical(W);
   Q:=quo<W|J>;
   Act:=Action(Q);
   Append(~L,&cat[[i:j in [1..Rank(Act.i)]]:i in [1..n]]);
   W:=J;
end while;

	return L;

end intrinsic;

////////////////////////////////////////////////////////////////////

intrinsic IsomorphismTypesOfRadicalLayers(M::ModRng,L::SeqEnum) -> SeqEnum
{Given a module M and a sequence of simple modules L, returns a sequence of 
Isomorphism types of simple composition factors in each radical layer.}

W:=M;
List:=[];
while Dimension(W) ne 0 do
   S:=CompositionFactors(quo<W|JacobsonRadical(W)>);
   Append(~List, IsomorphismTypesComparedToList(S,L));
   W:=JacobsonRadical(W);
end while;

	return List;

end intrinsic;

/////////////////////////////////////////////////////////////////////

intrinsic IsomorphismTypesOfSocleLayers(M::ModAlgBas) -> SeqEnum
{Given a module M over a basic algebra, return a sequence of isomorphism 
types of simple composition factors in each socle layer with reversed 
order, i.`e isomorphism types of the socle of M will appear last.}

A:=Algebra(M);
L:=[];
n:=#IdempotentGenerators(A);
Q:=M;
while Dimension(Q) ne 0 do
   S:=Socle(Q);
   Act:=Action(S);
   Append(~L,&cat[[i:j in [1..Rank(Act.i)]]:i in [1..n]]);
   Q:=quo<Q|Socle(Q)>;
end while;

	return Reverse(L);

end intrinsic;

//////////////////////////////////////////////////////////////////////

intrinsic IsomorphismTypesOfSocleLayers(M::ModRng,L::SeqEnum) -> SeqEnum
{Given a module M and a list of simple modules L, returns a sequence 
of isomorphism types of simple composition factors in each socle layer 
with reversed order, that it, isomorphism types of the socle of M will 
appear last.}

Q:=M;
List:=[];
while Dimension(Q) ne 0 do
   S:=Socle(Q);
   CF:=CompositionFactors(S);
   Append(~List, IsomorphismTypesComparedToList(CF,L));
   Q:=quo<Q|Socle(Q)>;
end while;

	return Reverse(List);

end intrinsic;

///////////////////////////////////////////////////////////////////////

intrinsic Blocks(S::SeqEnum) -> SeqEnum
{Returns a sequence of sequences each of which is an equivalence class
of modules in S under the relation which is the smallest equivalence
relation that equates two modules that have a simple constituent in
common.}

lst := S;
n := #S;
inds := {1 .. n};
Irr := [quo<x | JacobsonRadical(x)>:x in lst];
dims := [Dimension(x):x in Irr];
singles := [i: i in [1 .. n]|dims[i] eq 1];
tm := 1;
if #singles eq 1 then
   tm := singles[1];
else
   if exists(t){i: i in singles |
          IsIsomorphic(Irr[i],
                 TrivialModule(Group(lst[1]), BaseRing(lst[1])))}
              then
      tm := t;
   end if;
end if;
wlst := [Seqset(IsomorphismTypesComparedToList(
                CompositionFactors(lst[i]),Irr)): i in [1 .. n]];
pblock := wlst[tm];
flag := true;
blocks := [];
while flag do             // flag true if need new block
   pblock2 := &join[wlst[j]:j in pblock];
   if pblock2 eq pblock then
      flag := false;
   else
      pblock := pblock2;
   end if;
end while;
if tm eq 1 then
   blocks[1] := [S[i]: i in pblock];
else
   blocks[1] := [S[tm]] cat [S[i]:i in pblock| i ne tm];
end if;
blkinds := pblock;
if pblock ne inds then
   while blkinds ne inds do
      u := exists(t){i: i in [1 .. n]| not i in blkinds};
      bbb := {t};
      flag := true;
      while flag do
         bbb2 := &join[wlst[j]:j in bbb];
         if bbb2 eq bbb then
            flag := false;
         else
            bbb := bbb2;
         end if;
      end while;
      blkinds := blkinds join bbb;
      Append(~blocks, [S[i]: i in bbb]);
   end while;
end if;

        return blocks;

end intrinsic;

