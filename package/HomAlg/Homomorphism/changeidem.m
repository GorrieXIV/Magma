freeze;

// Jon F. Carlson, June 2012

BuildHomomorphismFromGenerators := function(A,B,lst);
// lst is a list of vectors of elements of B, that are the images of the
// generators of A, under the homomorphism to be built. The
// constructs the matrix of that homomorphism.

np := NumberOfProjectives(A);
dimp := DimensionsOfProjectiveModules(A);
rct := 0;
mat := KMatrixSpace(BaseRing(A), Dimension(A), Dimension(B))!0;
for i := 1 to np do
   pt := PathTree(A,i);
   for j := 1 to dimp[i] do
      if pt[j][1] eq 1 then
         mat[rct+j] := lst[pt[j][2]];
      else
         mat[rct+j] := Vector( (B!mat[rct+pt[j][1]]) * (B!lst[pt[j][2]]) );
      end if;
   end for;
   rct +:= dimp[i];
end for;

        return hom<A->B|mat>;

end function;

////////////////////////////////////////////////////////////////

ChangeIdempotentsFunc := function(A,S)
// Returns the basic algebra isomorphic to A, obtained by permuting the 
//order of the idempotents as in the sequence S.
  
k := CoefficientRing(A);
dim := DimensionsOfProjectiveModules(A);
np := NumberOfProjectives(A);
ng := #Generators(A);
ends := GeneratorAssociatedIdempotents(A);
sort1 := [[i:i in [np+1 .. ng]|ends[i][1] eq S[j]]:j in [ 1 .. np]];
mu := (Sym(np)!S)^-1;
sort2 := &cat[&cat[[x:x in sort1[i]|(ends[x][2])^mu eq j]:j in [1 .. np]]: 
                    i in [1 .. np]];
sigma1 := Sym(ng)!([1 .. np] cat sort2);
sigma := Sym(ng)!(S cat [np+1 .. ng]) * sigma1^-1;
MA := [];
tau := sigma^-1;
for i := 1 to np do
   j := i^sigma;
   ptold := PathTree(A,j);
   ptnew := [<ptold[t][1], ptold[t][2]^tau>:t in [1 .. #ptold]];
   matold := Action(ProjectiveModule(A,j));
   matnew := MatrixAlgebra<k, dim[j]|[matold.(t^sigma):t in [1 .. ng]]>;
   Append(~MA, <matnew, ptnew>);
end for;
B := BasicAlgebra(MA);
oldgens := Generators(B);
newgens := [Vector(oldgens[i^tau]): i in [1 .. ng]];
nmat := BuildHomomorphismFromGenerators(A,B,newgens);

	return  B, nmat;

end function;


/////////////////////////////////////////////////////////////////

intrinsic ChangeIdempotents(A::AlgBas, S::SeqEnum) -> AlgBas, Map
{Returns the basic algebra isomorphic to A, obtained by permuting the
order of the idempotents by the permutation X.}

a, b := ChangeIdempotentsFunc(A,S);

        return a, b;

end intrinsic;

/////////////////////////////////////////////////////////////////

intrinsic ChangeIdempotents(A::AlgBas, X::GrpPermElt) -> AlgBas, Map
{Returns the basic algebra isomorphic to A, obtained by permuting the
order of the idempotents by the permutation X.}

SS := [i^X:i in [1 .. NumberOfProjectives(A)]];
a, b := ChangeIdempotentsFunc(A,SS);

	return a, b;

end intrinsic; 
