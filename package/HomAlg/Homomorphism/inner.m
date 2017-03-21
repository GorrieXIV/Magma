freeze;

intrinsic GeneratorsOfGroupOfUnits(A::AlgBas) -> SeqEnum, SeqEnum
{Returns a sequence of elements of the basic algebra A that generate the group
of invertible elements in A and the sequence of inverses of those elements.}

I := A!1;
k := BaseRing(A);
B := IdempotentGenerators(A);
ZZ, phi := Center(A);
idps := IdempotentPositions(A);
mat := KMatrixSpace(BaseRing(A), Dimension(A), Dimension(A)-#idps)!0;
count :=0;
for i := 1 to Dimension(A) do
   if i in idps then 
      count +:= 1;
   else 
      mat[i,i-count] := 1;
   end if;
end for;
tmat := Transpose(mat);
V := VectorSpace(k,Dimension(A) -#idps);
W := sub<V| [Vector(phi(x))*mat: x in Basis(ZZ)]>;
UU := ExtendBasis(W, V);
C := [A!(UU[j]*tmat): j in [Dimension(W)+1 .. Dimension(V)]];
zinds := [i: i in [1 .. Dimension(ZZ)]| not i in IdempotentPositions(ZZ)];
D := [phi(Basis(ZZ)[j]):j  in zinds];
m := Factorization(#k)[1][2];
a := PrimitiveElement(k);
if #k gt 2 then
   W := [I+(a-k!1)*x: x in B] cat [I-a^j*y : j in [0 ..m-1], y in C];
   WZ := [I-a^j*y : j in [0 ..m-1], y in D];
   WW := [I+(a^-1-k!1)*x : x in B];
else 
   W:= [I-y : y in C];
   WZ := [I-y : y in D];
   WW := [];
end if;
for y in C do
   t := 1;
   z := y;
   x := y;
   while z ne 0 do
      z *:= x;
      t := t+1;
   end while;
   WW cat:= [I + &+[(a^j*y)^i : i in [1 .. t-1]]: j in [0 .. m-1]];
end for;
WT := W cat WZ;
WWT := WW;
for y in D do
   t := 1;
   z := y;
   x := y;
   while z ne 0 do
      z *:= x;
      t := t+1;
   end while;
   WWT cat:= [I + &+[(a^j*y)^i : i in [1 .. t-1]]: j in [0 .. m-1]];
end for;

	return WT, WWT;

end intrinsic;

//////////////////////////////////////////////////////////////////////////

intrinsic NoncentralGeneratorsOfGroupOfUnits(A::AlgBas) -> SeqEnum, SeqEnum
{Returns a sequence of elements of the basic algebra A that generate the
 quotient of the group of invertible elements in A by the subgroup of 
 invertible central elements and returns the sequence of inverses of those 
 elements.}

I := A!1;
k := BaseRing(A);
B := IdempotentGenerators(A);
ZZ, phi := Center(A);
idps := IdempotentPositions(A);
mat := KMatrixSpace(BaseRing(A), Dimension(A), Dimension(A)-#idps)!0;
count :=0;
for i := 1 to Dimension(A) do
   if i in idps then 
      count +:= 1;
   else 
      mat[i,i-count] := 1;
   end if;
end for;
tmat := Transpose(mat);
V := VectorSpace(k,Dimension(A) -#idps);
W := sub<V| [Vector(phi(x))*mat: x in Basis(ZZ)]>;
UU := ExtendBasis(W, V);
C := [A!(UU[j]*tmat): j in [Dimension(W)+1 .. Dimension(V)]];
// zinds := [i: i in [1 .. Dimension(ZZ)]| not i in IdempotentPositions(ZZ)];
// D := [phi(Basis(ZZ)[j]):j  in zinds];
m := Factorization(#k)[1][2];
a := PrimitiveElement(k);
if #k gt 2 then
   W := [I+(a-k!1)*x: x in B] cat [I-a^j*y : j in [0 ..m-1], y in C];
   WW := [I+(a^-1-k!1)*x : x in B];
else
   W:= [I-y : y in C];
   WW := [];
end if;
for y in C do
   t := 1;
   z := y;
   x := y;
   while z ne 0 do
      z *:= x;
      t := t+1;
   end while;
   WW cat:= [I + &+[(a^j*y)^i : i in [1 .. t-1]]: j in [0 .. m-1]];
end for;

        return W, WW;

end intrinsic;


//////////////////////////////////////////////////////////////////////////

intrinsic InnerAutomorphismGroup(A::AlgBas) -> GrpMat
{Computes the group of inner automorphisms of the basic algebra A}

k := BaseRing(A);
X, Y := NoncentralGeneratorsOfGroupOfUnits(A);
n := Dimension(A);
Zero := KMatrixSpace(k,n,n)!0;
Mats := [];
for i := 1 to #X do
   M := Zero;
   for j := 1 to n do
      M[j] := Vector(X[i]*A.j*Y[i]);
   end for;
   Append(~Mats, M);
end for;
GL := GL(Dimension(A),k);
G := sub<GL | Mats>;

	return G;

end intrinsic;


