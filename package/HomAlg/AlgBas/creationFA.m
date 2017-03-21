freeze;

ObviousRelations := function(F,n,L);
// F is a finitely generated algebra, n is the number of idempotents
// in the basic algebra and L is the list of beginning and ending
// nodes of the nonidempotent generators. Note that the first n generators
// of F are the idempotents.

ni := n;
nn := Rank(F)-n;

    L1 := [F!1- &+[F.i: i in [ 1 .. n]]] cat [F.i-F.i^2:i in [1 .. ni]];

if ni gt 1 then 
    L2 := [F.i*F.j:i in [1 .. ni], j in [1 .. ni]|i ne j];
else
    L2 := [];
end if;
    L3 := [F.(L[j-ni][1])*F.(j)-F.(j): 
	      j in [ni+1 .. ni+nn]] 
      cat [F.(j)*F.(L[j-ni][2])-F.(j): 
	      j in [ni+1 .. ni+nn]];

    L4 := [F.i*F.j:i in [1 .. ni], j in [ni+1 .. ni+nn]|i ne 
	L[j-ni][1]];

    L5 := [F.j*F.i:i in [1 .. ni], j in [ni+1 .. ni+nn]|i ne 
	L[j-ni][2]];

    return L1 cat L2 cat L3 cat L4 cat L5;

end function;

//******************************************************************

ListMonomials := function(A, B, I);
// A is the beginning list, B is the list of variables that we will
// multiply times the elements of A and I is the filter, the ideal
// of elements that we are not interested in.

N := {@ <x[1]*y[1], x[2] cat y[2]> : x in B,y in A|x[1]*y[1] notin I @};

return N;

end function;

//******************************************************************

ListGradedMonomialBasis := function(F,I,n);

II := LeadingMonomialIdeal(I);
AM := {@ <F.i,[i]>: i in [1 .. Rank(F)] @};
BM := AM;
if n gt 1 then
for j := 2 to n do
 BM := ListMonomials(BM, AM, II);
end for;
end if;

       return BM;

end function;

//*******************************************************************

ListOfAllMonomials := function(F,I,n,N);

BB := {@ <F.i,[i]>: i in [n+1 .. Rank(F)]|F.i notin I @};
CC := {@ <F.i,[i]>: i in [n+1 .. Rank(F)]|F.i notin I @};
LL := {@ <F.i,[i]>: i in [1 .. n] @} join BB;

flag := true;
while flag do
   CC := ListMonomials(BB,CC,I); 
   if #CC eq 0 then 
      flag := false;
   else 
      LL := LL join CC;
   end if;
end while;
LLL := [];
for i := 1 to #LL do
   if LL[i][2][1] gt n then
      LLL[i] := <LL[i][1],[N[LL[i][2][1]-n][1]] cat LL[i][2]>;
   else 
      LLL[i] := LL[i];
   end if;
end for;

    return LLL;

end function;

ZeroMatrix := function(R,m,n);

M := Matrix(R,m,n,[0:i in [1 .. m*n]]);
  return M;

end function;

//**********************************************************************

MakeBasicAlgebraFP := function(F,n,N,r);
// This function is meant to make a basic algebra from a finitely 
// presented algebra F with relation set r. The integer n should be 
// number of idempotent generators, and the list N should be the list
// of beginning and ending nodes of the quiver for the algebra. That
// is if a is a nonidempotent generator (say represented by the 
// the i^th variable in F, then the n-i entry in N should be the 
// pair <u,v>, where u and v are the numbers of the idempotents 
// e_u, e_v such that e_u.a.e_v = a. 

ff := BaseRing(F);
OR := ObviousRelations(F,n,N);
I := ideal<F|r,OR>;
J := LeadingMonomialIdeal(I);
LM := ListOfAllMonomials(F,J,n,N);
// This is the basis for the basic algebra.
AlgList := [];

for j := 1 to n do

   LMj := {@ LM[j] @} join {@ LM[k]: k in [n+1 .. #LM]| 
           LM[k][2][1] eq j  @};
   mm := #LMj;
   B := Basis(VectorSpace(ff,mm));

   // This is the basis for the jth projective module.
   // Now we want to sort this set

   if #LMj eq 1 then 

      PTj := [<1,j>];
   
   else

      Mj := {@ LMj[1][1] @} join Sort({@ x[1]:x in [LMj[l]: 
               l in [2 .. #LMj]] @});
      LMj := {@ [x: x in LMj|x[1] eq Mj[i]][1]:i in [1 .. mm] @};
      PTj := [<1,j>] cat [<1,LMj[i][2][2]>:i in [2 .. #LMj]|#LMj[i][2] eq 2];

      if #PTj ne mm then 
         for l := #PTj+1 to mm do 
            u := exists(t){k : k in [1 .. mm]|LMj[k][2] eq Prune(LMj[l][2])}; 
            Append(~PTj,<t,LMj[l][2][#LMj[l][2]]>);

          end for;
      end if; 
   end if;
   // This is the path tree for the projective module.
   // Now to create the matrix algebra.
   Matlst:= [];
   for t := 1 to n do
      Z := ZeroMatrix(ff,mm,mm);
      if t eq j then 
         Z[1,1] := ff!1;
      end if;
      for k := 2 to mm do
	 if N[LMj[k][2][#LMj[k][2]]-n][2] eq t then 
	    Z[k,k] := ff!1;
	 end if;
      end for;
      Append(~Matlst,Z);
   end for;
   // These are the matrices for the idempotent. For the other
   // generators it is not as easy. 

   for t := n+1 to Rank(F) do
      Z := ZeroMatrix(ff,mm,mm);
      for k := 1 to mm do
	 w := NormalForm(LMj[k][1]*F.t,I);
	 if w ne 0 then
	    x := Monomials(w);
	    v := Coefficients(w);
	    Z[k] := &+[B[Index(Mj,x[i])]*v[i]:i in [1 .. #x]];
	 end if;
      end for;
      Append(~Matlst, Z);
   end for;
   Append(~AlgList,<sub<MatrixAlgebra(ff,mm)|Matlst>,PTj>);
end for;
A := BasicAlgebra(AlgList);
//phi := hom<F -> A|Generators(A)>;
//		  return A, F, phi;
return A;
end function;

//********************************************************************

intrinsic BasicAlgebra(F::AlgFr,R::SeqEnum,n::RngIntElt,p::SeqEnum) -> AlgBas
{Creates the basic algebra from the algebra given by the presentation.
F is a free algebra where the first n variables represent idempotent
elements. The sequence R is the relations in F among the nonidempotent
generators. The sequence p consists of tuples giving the indexes of 
the beginning an ending vertices (idempotents) of the nonidempotent
generators of the algebra.}

return MakeBasicAlgebraFP(F,n,p,R);

end intrinsic;

//********************************************************************

MakeBasicAlgebraLA := function(F,R);

n := Rank(F);
G := FreeAlgebra(BaseRing(F),Rank(F)+1);
phi := hom<F -> G|[G.(i+1): i in [1 .. n]]>;
rel := [phi(x):x in R];
S := [<1,1>:i in [ 1 .. n]];
A := MakeBasicAlgebraFP(G,1,S,rel);

return A;

end function;

//*********************************************************************

intrinsic BasicAlgebra(F::AlgFr,R::SeqEnum) -> AlgBas
{Creates the basic algebra from the local algebra given by the presentation.
F is the free algebra on the nonidempotent generators of the algebra. The 
sequence R is a collection of generators for the ideal of relations. }

return MakeBasicAlgebraLA(F,R);

end intrinsic;
