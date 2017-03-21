freeze;

////////////////////////////////////////////////////////////////////

PowerIdempotent := function(e);
// Returns the idempotent element E of a basic algebra having the 
// property that E is congruent to e modulo the radical of the basic 
// algebra. 

if e^2 -e eq 0 then 
	return e;
end if;
f := MinimalPolynomial(e^2-e);
d := Degree(f);
p := Characteristic(CoefficientRing(Parent(e)));
flag := true;
n := 0;
while flag do
   n +:=1;
   if p^n ge d then 
      flag := false;
   end if;
end while;
E := e^(p^n);

	return E;

end function;

/////////////////////////////////////////////////////////////////////

intrinsic MaximalIdempotent(A::AlgBas, S::SeqEnum) -> AlgBasElt
{A is a basic algebra, S is a subspace of the vector space of A
that is closed under multiplication. The function returns an 
idempotent in A which has maximal rank among all idemptents 
contained in S.} 

k := CoefficientRing(A);
RR := RightRegularModule(A);
J := JacobsonRadical(RR);
Q, rho := quo<RR|J>;
mat := BasisMatrix(sub<VectorSpace(k,Dimension(RR))|[Vector(x): x in S]>);
a, mu := HasMatrix(rho);
phi := mat*mu;
if Rank(phi) eq 0 then 
   return A!0;
end if;
V := RowSpace(phi);
E := &+[x@@mu: x in Basis(V)];

	return PowerIdempotent(A!Vector(E));

end intrinsic;

//////////////////////////////////////////////////////////////////////

RightRepresentationMatrix := function(A,a);
// Returns the matrix of the action of a, an element of the 
// basic algebra A, on the right regular module of A. 

dim := Dimension(A);
mat := KMatrixSpace(CoefficientRing(A),dim,dim)!0;
for i := 1 to dim do
   mat[i] := Vector(A.i*a);
end for;

	return mat;

end function;

//////////////////////////////////////////////////////////////////////

LeftRepresentationMatrix := function(A,a);
// Returns the matrix of the action of a, an element of the
// basic algebra A, on the right regular module of A.

dim := Dimension(A);
mat := KMatrixSpace(CoefficientRing(A),dim,dim)!0;
for i := 1 to dim do
   mat[i] := Vector(a*A.i);
end for;

        return mat;

end function;


/////////////////////////////////////////////////////////////////////

intrinsic LeftAnnihilator(A::AlgBas,S::SeqEnum[AlgBasElt]) 
		-> SeqEnum[AlgBasElt]
{Returns the left annihilator of a sequence S of elements in the 
basic algebra A.} 

V := VectorSpace(CoefficientRing(A),Dimension(A));
B := [A!x: x in Basis(sub<V| [Vector(y): y in S]>)];
W := V;
for x in B do
   W := W meet NullSpace(RightRepresentationMatrix(A,x));
end for;

	return [A!x: x in Basis(W)];

end intrinsic;

//////////////////////////////////////////////////////////////////////

intrinsic RightAnnihilator(A::AlgBas,S::SeqEnum[AlgBasElt]) 
                 -> SeqEnum[AlgBaselt]
{Returns the right annihilator of a sequence S of elements in the 
basic algebra A. }

V := VectorSpace(CoefficientRing(A),Dimension(A));
B := [A!x: x in Basis(sub<V| [Vector(y): y in S]>)];
W := V;
for x in B do
   W := W meet NullSpace(LeftRepresentationMatrix(A,x));
end for;

        return [A!x: x in Basis(W)];

end intrinsic;

//////////////////////////////////////////////////////////////////////

intrinsic Annihilator(A::AlgBas,S::SeqEnum[AlgBasElt]) ->
                     SeqEnum[AlgBasElt]
{Returns the two-sided annihilator of the sequence of elements S
of the basic algebra. }

V := VectorSpace(CoefficientRing(A),Dimension(A));
BL := sub<V|[Vector(x): x in LeftAnnihilator(A,S)]>;
BR := sub<V|[Vector(x): x in RightAnnihilator(A,S)]>;

	return [A!x: x in Basis(BL meet BR)];

end intrinsic;

/////////////////////////////////////////////////////////////////////

intrinsic MinimalIdentity(A::AlgBas, S::SeqEnum[AlgBasElt]) -> AlgBasElt
{Returns the idempotent of smallest rank that is a two sided identity for
the elements in the set S.}

N := Annihilator(A,S);
E := MaximalIdempotent(A,N);

	return A!1 - E;

end intrinsic;

