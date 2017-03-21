freeze;

/*****************************************************
  Construction of the Clifford algebra associated to
  a quadratic form defined on a vector space
  
  This package depends on quadform.m for utilities
  related to quadratic forms.
  
  July 2010 Don Taylor
  

  $Id: clifford.m 52756 2016-05-24 02:17:10Z don $
  
******************************************************/


/* Suppose that Q is a quadratic form defined on a
   vector space V of dimension n over a field F.
   Represent the elements of the Clifford algebra C(V)
   by sequences of "monomials" <S,a>, where S is a subset
   of {1..n}, represented by an ordered sequence and
   a is a field element.
   
   Ensure that the monomials in every element of the 
   Clifford algebra are ordered by their first component.
   
   A quadratic form is represented by an n x n upper 
   triangular matrix Q.  The polar form is represented
   by the symmmetric matrix Q + Transpose(Q).
   
   The zero element is the empty sequence [].
   The identity element is <[Integers()|],1>.
*/

declare attributes AlgClff :
  space,
  embedding,
  vectors,
  pRing,
  antiAutMat;
  
/* space:      the quadratic space from which the Clifford algebra is 
               derived

   embedding:  the standard embedding of the quadratic space into the
               Clifford algebra
        
   vectors:    the image of embedding (as a vector subspace of the 
               Clifford algebra)

   pRing:      a multivariate polynomial ring representing elements
               of the Clifford algebra

   antiAutMat: the matrix of the antiautomorphism which reverses the 
               multiplication.
*/

cadd := function(s1,s2)
// Add the values of terms with the same first component
  if IsEmpty(s1) then
    vec := s2;
  elif IsEmpty(s2) then
    vec := s1;
  else
    U := Universe(s1);
    ndx1 := {@ p[1] : p in s1 @};
    ndx2 := {@ p[1] : p in s2 @};
    ndx := Sort(ndx1 join ndx2);
    vec := [U|];
    for i in ndx do
      i1 := Position(ndx1,i);
      i2 := Position(ndx2,i);
      if i1 gt 0 then
        if i2 gt 0 then
          val := s1[i1][2]+s2[i2][2];
          if val ne 0 then
            Append(~vec,<i,val>);
          end if;
        else
          Append(~vec,s1[i1]);
        end if;
      else
        Append(~vec,s2[i2]);
      end if;
    end for;
  end if;
  return vec;
end function;

forward termbyterm;
seqbyterm := function(B,s1,t2)
  vec := [Universe(s1)|];
  for t1 in s1 do
    vec := cadd(vec,termbyterm(B,t1,t2));
  end for;
  
  return vec;
end function;

mprod := function(B,L1,j)
// B is the bilinear form - not assumed symmetric
// L1 represents a basis element of the Clifford algebra
// j is the index of a basis vector of the vector space
  K := BaseRing(B);
  if IsEmpty(L1) then
    return [<[j],K!1>];
  end if;
  last := L1[#L1];
  stub := Prune(L1);
  if last lt j then
    vec := [<Append(L1,j),K!1>];
  elif last eq j then
    vec := [<stub,B[j,j]>];
  else // last gt j
    vec := seqbyterm(B,termbyterm(B,<stub,K!1>,<[j],-K!1>),<[last],K!1>);
    vec := cadd(vec,termbyterm(B,<stub,K!1>,<[Integers()|],B[last,j]+B[j,last]>));
  end if;

  return vec;
end function;

termbyterm := function(B,t1,t2)
  // Return the product of two terms <i1,a1> and <i2,a2>
  L1 := t1[1];
  L2 := t2[1];
  val := t1[2]*t2[2];
  if val eq 0 then
    vec := [car<Parent(L1),Parent(val)>|]; // This should not occur unless called directly
  elif IsEmpty(L1) then
    vec := [<L2,val>];
  elif IsEmpty(L2) then
    vec := [<L1,val>];
  else
    vec := seqbyterm(B,mprod(B,L1,L2[1]),<Remove(L2,1),val>);
  end if;
  return vec;
end function;


aprod := function(B,s1,s2)
// s1 and s2 are sequences of pairs <i,a>
  vec := [Universe(s1)|];
  for q in s2 do
    vec := cadd(vec,seqbyterm(B,s1,q));
  end for;
  return vec;
end function;

/* Construction of a Clifford algebra of dimension n as a structure constant 
   algebra.  The basis elements are indexed by subset of {1..n}. In order
   to construct the structure constant algebra, the subsets are represented
   by integers in the range [1..2^n]
*/

decode := func< k | [Integers()| x : x in [1..#S] | S[x] eq 1] where S is Intseq(k-1,2) >;
encode := func< L | IsEmpty(L) select 1 else 1 + &+[ 2^(k-1) : k in L ] >;

intrinsic CliffordAlgebra(Q::AlgMatElt) -> AlgClff, ModTupFld, Map
{The triple C, V, f, where C is Clifford algebra of the quadratic form Q,
  V is the quadratic space of Q, and f is the standard embedding of V in C}
  V := QuadraticSpace(Q);
  K := BaseRing(V);
  require IsExact(K) : "Available only for rings with exact arithmetic";
  n := Dimension(V);
  d := 2^n;
  // T will hold the multiplication table as a sequence of 4-tuples
  T := [];
  for i := 1 to d do
    e := [<decode(i),K!1>];
    for j := 1 to d do
      for p in aprod(Q,e,[<decode(j),K!1>]) do
        Append(~T,<i,j,encode(p[1]),K ! p[2]>);
      end for;
    end for;
  end for;
  A := CliffordAlgebra<K, 2^n | T >;
  f := hom< V -> A | [A.encode([i]) : i in [1..n]] >;
//  f := hom< V -> Module(A) | [Vector(A.encode([i])) : i in [1..n]] >;
  A`vectors := sub< Module(A) | [Vector(A.encode([i])) : i in [1..n]] >;
  A`space := V;
  A`embedding := f;
  return A, V, f;
end intrinsic;

intrinsic CliffordAlgebra(V::ModTupFld) -> AlgClff, Map
{The pair C, f, where C is the Clifford algebra of the quadratic
 space V and f is the standard embedding of V into C}
  Q := QuadraticFormMatrix(V);
  C, _, f := CliffordAlgebra(Q);
  return C, f;
  
end intrinsic;

/*
  K is a field, Q is an n x n matrix (not necessarily symmetric) over K 
  The Clifford algebra is an associative K-algebra of dimension 2^n

  Deprecated: this is only here for consistency with the previous release
*/
intrinsic CliffordAlgebra(K::Fld,Q::AlgMatElt) -> AlgClff, ModTupFld, Map
{The Clifford algebra C of the n x n quadratic form Q over a field K,
 the quadratic space K^n, and the standard embedding of K^n into C}

  return CliffordAlgebra(Q);

end intrinsic;

intrinsic GeneratorMatrix(C::AlgClff) -> ModMatRngElt
{The matrix whose rows are algebra generators of C}
  return Matrix(Basis(C`vectors));
end intrinsic;

intrinsic Ngens(C::AlgClff) -> RngIntElt
{The number of generators of the Clifford algebra}
  return Dimension(C`space);
end intrinsic;

intrinsic Rank(C::AlgClff) -> RngIntElt
{The rank of the Clifford algebra C}
  return Dimension(C`space);
end intrinsic;

intrinsic MainInvolution(C::AlgClff) -> Map
{The main involution of the Clifford algebra C}
  nu := Dimension(C);
  return hom< C -> C | [ IsEven(#decode(i)) select C.i else -C.i : i in [1..nu]]>;
end intrinsic;

intrinsic BasisProduct(C::AlgClff, L::SeqEnum) -> AlgClffElt
{ The product of the basis elements (indexed by L) of the 
  quadratic space of C }
  return IsEmpty(L) select One(C) else &*[C.encode([i]) : i in L];
end intrinsic;

intrinsic BasisElement(C::AlgClff, L::SetEnum) -> AlgClffElt
{ The basis element of C indexed by the set L }
  return C.encode(L);
end intrinsic;

intrinsic MainAntiautomorphism(C::AlgClff) -> Map
{The main anti-automorphism of the Clifford Algebra C}
  if not assigned C`antiAutMat then
    m := Dimension(C);
    C`antiAutMat := 
      Matrix(m,m,[ElementToSequence(BasisProduct(C,Reverse(decode(i))))
           : i in [1..m]]);
  end if;
  return map< C -> C | x :-> x*C`antiAutMat >;
end intrinsic;

intrinsic SeqToClifford(C::AlgClff, ss::SeqEnum) -> AlgClffElt
{ Convert a sequence of Clifford monomials to an element of C }
// First check that the sequence is valid
  tt := [<encode(term[1]),term[2]> : term in ss ];
  require forall{ term : term in tt | 
      Type(i) eq RngIntElt and i le Dimension(C) 
      where i is term[1]} : "Invalid monomial sequence";
  return IsEmpty(ss) select C!0 
      else &+[ term[2]*C.i : term in tt | true where i is term[1]];
end intrinsic;

intrinsic SeqFromClifford(v::AlgClffElt) -> SeqEnum
{ Convert a Clifford algebra element to a sequence of Clifford monomials }
  return [<decode(i), v[i]> : i in Support(v)];
end intrinsic;

intrinsic AsPolynomial(xi::AlgClffElt)
{Print the Clifford algebra element xi as a polynomial
 in the basis elements of its quadratic space}
  C := Parent(xi);
  n := Ngens(C);
  if not assigned C`pRing then
    P := PolynomialRing(BaseRing(C),n);
    AssignNames(~P,["e" cat IntegerToString(i) : i in [1..n]]);
    C`pRing := P;
  else
    P := C`pRing;
  end if;
  eseq := Eltseq(xi);
  m := #eseq;
  f := P!0;
  for i := 1 to #eseq do
    if eseq[i] ne 0 then
      L := [0 : ndx in [1..n]];
      for j in decode(i) do L[j] := 1; end for;
      f +:= eseq[i]*Monomial(P,L);
    end if;
  end for;

  print f;
end intrinsic;

intrinsic AssignNames(~C::AlgClff, S::SeqEnum[MonStgElt] )
{Assign the strings in S as the print names of the generators of C}
  n := Ngens(C);
  require #S le n: "argument 2 should have length at most " cat 
      IntegerToString(n);
  if #S lt n then
    S cat:= (assigned C`pRing) select
      [Sprint(Name(C`pRing,i)) : i in [#S+1..n]] else
      ["e" cat IntegerToString(i) : i in [#S+1..n]];
  end if;
  if not assigned C`pRing then
    C`pRing := PolynomialRing(BaseRing(C),n);
  end if;
  AssignNames(~C`pRing,S);
end intrinsic;

intrinsic Name(C::AlgClff, i::RngIntElt) -> AlgClffElt
{The i-th generator of the Clifford algebra}
  n := Ngens(C);
  require i le n: "index should be at most " cat n;
  return C`embedding(C`space.i);
end intrinsic;

intrinsic NumberOfNames(M::AlgClff) -> RngIntElt {}
  return Dimension(M`space);
end intrinsic;

intrinsic HomogeneousComponent(v::AlgClffElt, k::RngIntElt) -> AlgClffElt
{The homogeneous component of degree k of the Clifford algebra element v}
  L := [ <tt,v[i]> : i in Support(v) | #tt eq k where tt is decode(i) ];
  return SeqToClifford(Parent(v),L);
end intrinsic;

intrinsic EvenSubalgebra(C::AlgClff) -> AlgAss, Map
{The even subalgebra of the Clifford algebra C and its embeddding in C}
  return sub< C | [ C.i : i in [1..Dimension(C)] | IsEven(#decode(i)) ] >;
/*
  B := [ i : i in [1..Dimension(C)] | IsEven(#decode(i)) ];
  d := #B;
  K := BaseRing(C);
  M := ZeroMatrix(K,d,2*d);
  for i := 1 to d do M[i,B[i]] := 1; end for;
  coords := [ Coordinates( C, C.i*C.j ) : i,j in B ];
  consts := [ [ u[B[i]] : i in [1..d] ] : u in coords ];
  A := AssociativeAlgebra< K, d | consts : Rep := Rep, Check := false >;
  h := hom< A -> C |  x :-> C!(Vector(x)*M) >;
  return A, h;
*/
end intrinsic;

intrinsic Centre(C::AlgClff) -> AlgAss, Map
{The centre of the Clifford algebra C and its embedding in C}
  d := Dimension(C);
  K := BaseRing(C);
  coords := [ Coordinates( C, C.i*C.j ) : i,j in [1..d] ];
  A := AssociativeAlgebra< K, d | coords >;
  Z := Centre(A);
  h := hom< Z -> C | x :-> C!(Coordinates(A,A!x)) >;
  return Z, h;
end intrinsic;

intrinsic VectorAction(g::AlgClffElt) -> AlgMatElt
{The matrix of the invertible Clifford algebra element g acting on
the quadratic space by conjugation}
  require IsUnit(g) : "the element is not a unit";
  C := Parent(g);
  V := C`vectors;
  require forall{ b : b in Basis(V) | g^-1*b*g in V } :
      "the element does not preserve the quadratic space";
  n := Dimension(V);
  f := C`embedding;

  return  Matrix(n,n,[ (g^-1*V.i*g)@@f : i in [1..n]]);
end intrinsic;

/*
intrinsic SiegelElement(C::AlgClff,u::ModTupFldElt,v::ModTupFldElt) -> AlgClffElt
{Returns an element which acts by conjugation on the quadratic space of 
 the Clifford algebra and induces the Siegel transformation defined by the 
 pair of vectors (u, v).  The second return value is the matrix of the Siegel
 Transformation}

  V := C`space;
  require V eq Parent(u) : "the first vector is not in the quadratic space of C";
  require V eq Parent(v) : "the second vector is not in the quadratic space of C";
  require QuadraticNorm(u) eq 0 :"the first vector must be singular";
  require DotProduct(u,v) eq 0 : "the vectors must be orthogonal";

  f := C`embedding;
  s := f(u)*f(v)-C.1;
  n := Dimension(V);
  A := Matrix(n,n,[ (s^-1*f(V.i)*s)@@f : i in [1..n]]);

  return s, A;
end intrinsic;
*/

intrinsic ActionMatrix(M::AlgAss,s::AlgAssElt) -> AlgMatElt
{The matrix representing the action of s on the right ideal M}
  n := Dimension(M);
  return Matrix(n,n,[Coordinates(M,M.i*s) : i in [1..n]]);
end intrinsic;

intrinsic ChangeRing(C::AlgClff,S::Rng) -> AlgClff, ModTupFld, Map
{Given a Clifford algebra C with base ring R and a ring S, construct the
 Clifford algebra D with base field S obtained by coercing the coefficients
 of the elements of C into S.}
  Q_ := QuadraticFormMatrix(C`space);
  try
    Q := ChangeRing(Q_,S);
  catch e
    error e`Object;
  end try;
  V := QuadraticSpace(Q);
  d := Dimension(C);
 
  T := [];
  for i := 1 to d do
    e := C.i;
    for j := 1 to d do
      coords := Coordinates(C,e*C.j);
      for k := 1 to d do
        c := coords[k];
        if c ne C!0 then
          Append(~T,<i,j,k,S!c >);
        end if;
      end for;
    end for;
  end for;
  A := CliffordAlgebra< S, d | T >;
  A`space := V;
  n := Dimension(V);
  A`vectors := sub< Module(A) | [Vector(A.encode([i])) : i in [1..n]] >;
  f := hom< V -> A | [A.encode([i]) : i in [1..n]] >;
  A`embedding := f;
  if assigned C`pRing then
    P := PolynomialRing(S,n);
    AssignNames(~P,["e" cat IntegerToString(i) : i in [1..n]]);
    C`pRing := P;
  end if;
  if assigned antiAutMat then
    A`antiAutMat := 
      Matrix(d,d,[ ElementToSequence(BasisProduct(A,Reverse(decode(i))))
           : i in [1..d]]);
  end if;

  return A,V,f;

end intrinsic;
