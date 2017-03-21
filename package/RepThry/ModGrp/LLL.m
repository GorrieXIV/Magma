freeze;
//

/* 
 <example>
   SetIsClaus(false);
   SetInterrupt(false);
   G := PCGroup(WreathProduct(Sym(3), DihedralGroup(4)));
   L := AbsolutelyIrreducibleRepresentationsSchur(G, Q);
   R := L[16];
   L := CyclotomicField(5);
   P := MatrixAlgebra(L,4);
   p := P![Random(L, 2) : x in [1..4^2]];
   pi := p^-1;
   m := [ R(i) : i in Generators(G)];
   mm := [ pi*P!Eltseq(x)*p : x in m]; 
   T, Ti, Mo, L := MakeIntegral(mm);
   q,w := RelLLL(Mo);

   </example>
*/     

import "Reduce.m" : InduceAut;  


declare attributes FldAlg : ComplexConjugate;
declare verbose RelLLL, 10;
eps := 0.00000001;

intrinsic IsTotallyReal(Q::FldRat) -> BoolElt
  {Tests if Q is a totally real number field.}
  return true;
end intrinsic;

intrinsic IsTotallyComplex(Q::FldRat) -> BoolElt
  {Tests if Q is a totally complex number field.}
  return false;
end intrinsic;

intrinsic HasComplexConjugate(A::AlgQuat) -> BoolElt, .
{Returns true and the Conjugate intrinsic}
 return true,Conjugate; end intrinsic;

intrinsic HasComplexConjugate(K::FldAlg : Weak := false) -> BoolElt, .
{True iff K has an automorphism that acts as complex conjugation.
If so, also returns the automorphism.  'Weak' means the automorphism
is only required to agree with complex conjugation in one embedding.}

  if assigned K`ComplexConjugate then
    return true, K`ComplexConjugate;
  end if;

  if Type(K) in {FldCyc, FldQuad} then
    K`ComplexConjugate := ComplexConjugate;
    return true, ComplexConjugate;
  elif IsTotallyReal(K) then
    K`ComplexConjugate := map<K -> K | x :-> x>;
    return true, K`ComplexConjugate;
  elif Type(K) eq FldOrd then
    L := NumberField(K);
    f, c := HasComplexConjugate(L:Weak := Weak);
    if f then
      c := func<x|K!(c(L!x))>;
      K`ComplexConjugate := c;
      return true, c;
    else
      return false, _;
    end if;
  elif IsTotallyReal(BaseField(K)) and Degree(K) eq 2 then 
    K`ComplexConjugate := map<K -> K | x :-> Trace(x)-x>;
    return true, K`ComplexConjugate;
  else
    Ka := AbsoluteField(K);
    L := Automorphisms(Ka);
    p := PrimitiveElement(Ka);
    n := Degree(Ka);
    c := [ComplexConjugate(x) : x in Conjugates(p)];
    neps := eps;
    repeat
      found := [];
      for i in L do
        d := Conjugates(i(p));
        if Weak and Abs(c[n] - d[n]) lt eps then
          Append(~found, i);
        elif not Weak and forall{ r : r in [1..#d] | Abs(d[r]-c[r]) lt neps} then
          Append(~found, i);
        end if;
      end for;
      if #found eq 0 then
        return false, _ ;
      end if;
      assert #found eq 1;
      /* If this fails, it's an infinite loop!
       * (Apparently the intention was to increase neps) */
    until #found eq 1;  
    c := func<x | K!(found[1](x))>;
    K`ComplexConjugate := c;
    return true, c;
  end if;
  return false, _;
end intrinsic;

intrinsic ComplexConjugate(x::FldAlgElt : Weak := false) -> FldAlgElt
{The image of x under the automorphism returned by HasComplexConjugate.}

  K := Parent(x);
  f, c := HasComplexConjugate(K:Weak := Weak);
  require f: "ComplexConjugate is not defined for this field";
  return c(x);
end intrinsic;

intrinsic InternalScalarProduct(a::ModTupFldElt, b::ModTupFldElt:Gram := false, Hermite := false) -> RngElt
  {}
  
  if Hermite then
    _, f := HasComplexConjugate(K) where K := BaseRing(a);
    b := InduceAut(b, f);
  end if;
  if Gram cmpeq false then
//    s := InnerProduct(a, b);
    s := (a* Transpose(Matrix(b)))[1];
  else
    s := (a*Gram * Transpose(Matrix(b)))[1];
  end if;
  return s;
end intrinsic;

intrinsic InternalScalarProduct(a::ModDedElt, b::ModDedElt:Gram := false, Hermite := false) -> RngElt
  {}
  
  V := EmbeddingSpace(Parent(a));  
  a := V!Eltseq(a);
  b := V!Eltseq(b);
  if Hermite then
    _, f := HasComplexConjugate(K) where K := NumberField(BaseRing(a));
    b := InduceAut(b, f);
  end if;
  if Gram cmpeq false then
    s := InnerProduct(a, b);
    error "errpr";
  else
    s := (a*Gram * Transpose(Matrix(b)))[1];
  end if;
  return s;
end intrinsic;

intrinsic InternalExactLength(x::RngOrdElt) -> RngIntElt
  {}
  
  K := NumberField(Parent(x));
  n := Degree(K);
  f, c := HasComplexConjugate(K);
  if f then
    return Integers()!Trace(x*c(x));
  end if;

  require IsAbelian(K) or Signature(K) eq n: "Exact length only works for abelian or totally real fields";
end intrinsic;

intrinsic InternalExactLength(x::FldAlgElt) -> FldRatElt
  {}
    
  K := Parent(x);

  f, c := HasComplexConjugate(K);
  if f then
    return Trace(x*c(x));
  end if;

  n := Degree(K);
  require IsAbelian(K) or Signature(K) eq n: "Exact length only works for abelian or totally real fields";

end intrinsic;

intrinsic InternalExactScalarProduct(x::FldAlgElt, y::FldAlgElt) -> FldRatElt
  {}

  K := Parent(x);
  f, c := HasComplexConjugate(K);
  if f then
    return Trace(x*c(y));
  end if;
  n := Degree(K);
  require IsAbelian(K) or Signature(K) eq n: "Exact length only works for abelian or totally real fields";
  
end intrinsic;    

intrinsic InternalExactScalarProduct(x::RngOrdElt, y::RngOrdElt) -> RngIntElt
  {}

  K := NumberField(Parent(x));
  f, c := HasComplexConjugate(K);
  if f then
    return Integers()!Trace(x*c(y));
  end if;
  n := Degree(K);
  require IsAbelian(K) or Signature(K) eq n: "Exact length only works for abelian or totally real fields";
  
end intrinsic;    

intrinsic InternalExactLattice(I::RngOrdFracIdl: T := false, Mu := false) -> Lat, Map
  {}
  
  K := NumberField(Order(I));
  n := Degree(K);
  require Signature(K) eq n or IsAbelian(K): "Exact lattice only works for abelian or totally real fields";

  if IsIntegral(I) then
    G := IdentityMatrix(Integers(), n);
    P := Order(I);
  else
    G := IdentityMatrix(Rationals(), n);
    P := FieldOfFractions(Order(I));
  end if;

  if T cmpne false then
    B := BasisMatrix(I);
    if Mu cmpne false then
      Mu := RepresentationMatrix(Mu);
      B := B *Mu;
    end if;
    G := B*T*Transpose(B);
  else
    B := Basis(I);
    if Mu cmpne false then
      Mu := RepresentationMatrix(Mu);
      B := Matrix([Eltseq(x) : x in B]);
      B := B*Mu;
      B := [P!Eltseq(B[i]) : i in [1..n]];
    end if;

    for i in [1..n] do
      G[i][i] := InternalExactLength(B[i]);
      for j in [i+1..n] do
        G[i][j] := InternalExactScalarProduct(B[i], B[j]);
        G[j][i] := G[i][j];
      end for;
    end for;
  end if;

  //l := Lattice(BasisMatrix(I), G); // the basis is IGNORED!!!
//  "LatticeWithGram";
//  time l := LatticeWithGram(G: CheckPositive:=false);
  l := LatticeWithGram(G:CheckPositive := false);

  B := BasisMatrix(I);

  return l, map<l->P | x :->P!Eltseq(Matrix(BaseRing(B), x)*B),
                              y :->l!Eltseq(Solution(B, Matrix([Eltseq(y)])))>;
end intrinsic;

intrinsic Denominator(x::RngOrdElt) -> RngIntElt
  {The denominator of x (i.e. 1)}
  return 1;
end intrinsic;

intrinsic Height(x::FldRatElt) -> RngElt
  {The maximum of the (absolute values of the) numerator and denominor
  of the rational number x}
  return Maximum(Denominator(x), Abs(Numerator(x)));
end intrinsic;

intrinsic Qround(r::FldRatElt, M::RngIntElt: ContFrac := false) -> FldRatElt
  {Finds and approximation of r with denominator bounded by M.}
  if M eq 0 then
    return r;
  end if;

  if ContFrac then
    p1 := 1;
    x := r;
    p0 := Floor(x);
    q1 := 0;
    q0 := 1;
    a := p0;
    while q0 le M do
      x -:= a;
      if x eq 0 then
        return p0/q0;
      end if;
      x := 1/x;
      if x lt M then
        a := Floor(x);
      else
        a := M;
      end if;
      p := a*p0+p1;
      p1 := p0;
      p0 := p;

      q := a*q0+q1;
      q1 := q0;
      q0 := q;
    end while;
    return p1/q1;
  end if;

  a := Numerator(r);
  b := Denominator(r);
  return ((a*M + b-1) div b) / M;
end intrinsic;

intrinsic Qround(r::FldAlgElt, M::RngIntElt:ContFrac := false) -> FldRatElt
  {Finds and approximation of r with denominator bounded by M.}
  if M eq 0 then
    return r;
  end if;
  a := Parent(r)![Qround(x, M:ContFrac := ContFrac): x in Eltseq(r)];
  return a;
end intrinsic;

intrinsic InternalApprox(s::RngElt, I :: RngOrdFracIdl: T:= false) -> RngElt
  {}
 
  L, mL := InternalExactLattice(I:T := T);  
  B := Matrix(Rationals(), BasisMatrix(I));
  if true then
    vprint RelLLL, 2: "LLL:"; 
    vtime RelLLL, 2: LL, T := LLL(L:Sort := false);

    ss := Solution(B, Matrix([Eltseq(s)]));
    ss := Solution(Matrix(Rationals(), T), ss);
    st := Eltseq(ss);
    st := [Round(x)/1 : x in st];

    l := Parent(s)!Eltseq(Matrix([st])*Matrix(Rationals(), T)*B);
   
    vprint RelLLL, 2: "ExactLength", InternalExactLength(s-l)*1.0;
    return l;
  else
    ss := CoordinateSpace(L)!Eltseq(Solution(B, Matrix([Eltseq(s)])));
    st := Eltseq(ss);
    st := [x - Round(x) : x in st];
    st := Parent(ss)!st;

    l := L!(ss-st);

    vprint RelLLL, 2: "ExactLength", InternalExactLength(s-mL(l))*1.0;
    
    return mL(l);
  end if;

end intrinsic;    

intrinsic InternalSingleStep(a::Tup, b::Tup:Gram := false) -> Tup, RngElt
  {}
  
  IdA := a[1];
  IdB := b[1];
  IdR := IdA/IdB;

  ab := InternalScalarProduct(a[2], b[2]:Gram := Gram,Hermite);
  aa := InternalScalarProduct(a[2], a[2]:Gram := Gram,Hermite);

  // Task: find r in IdR such that r^2 is "close" to ab^2/(aa)
  // and points to the same direction...
  
  r := InternalApprox(ab/ aa, IdR);
  r := ComplexConjugate(r);
  return <IdB, b[2] - r*a[2]>, r;
end intrinsic;  
  
function MyNorm(x:Integral := true)

  K := Parent(x);
  if Type(K) eq FldCyc then
    A, mA := CyclotomicAutomorphismGroup(K);
  else
    A, _, mA := AutomorphismGroup(K);
    assert IsAbelian(A);
  end if;
  if Integral then
    d := Denominator(x);
    x *:= d;
  end if;
  for i in [1..Ngens(A)] do
    y := x;
    s := mA(A.i);
    lx := [x];
    for j in [2..Order(A.i)] do
      y := s(y);
      Append(~lx, y);
    end for;
    x := &* lx;
  end for;
  if Integral then
    return Integers()!x/d^#A;
  else
    return Rationals()! x;
  end if;
end function;

function MyInv(x:Integral := true) 

  K := Parent(x);
  if ISA(Type(K), RngOrd) then
    K := NumberField(K);
  end if;
  if Type(K) eq FldCyc then
    C, mC := CyclotomicAutomorphismGroup(K);
  else
    A, _, mA := AutomorphismGroup(K);
    assert IsAbelian(A);
    B, mB := AbelianGroup(A);
    C := PrimaryRepresentation(B);
    mC := Coercion(C, B)*Inverse(mB)*mA;
  end if;
  g := 1;


  if Integral then
    d := Denominator(x);
    x *:= d;
  end if;

  inv := 1;

  for i in [1..Ngens(C)] do
    z := Parent(x)!1;
    s := C.i@mC;
    y := s(x);
    if y ne x then
      g *:= Order(C.i);
      z := y;
      for j in [3..Order(C.i)] do
        y := s(y);
        z *:= y;
      end for;
    end if;
    inv *:= z;
    x := x*z;
  end for;

  if Integral then
    x := Integers()!x;
    return inv*d / x;
  else
    return inv / Rationals()! x;
  end if;
end function;

intrinsic InternalSingleIdeal(a::Tup:Mu := false, T := false) -> Tup
  {}

  vprint RelLLL, 2: "Lattice creation";
  vtime RelLLL, 2: L, mL := InternalExactLattice(a[1]: T := T, Mu := Mu);
  vprint RelLLL, 2: "LLL";
  vtime RelLLL, 2: LL := LLL(L);
  m := mL(L!LL.1);
  vprint RelLLL, 3: "Inverse";
  vtime RelLLL, 3: mi := MyInv(m);
  if Denominator(m) ne 1 or Denominator(mi) ne 1 then
    a[1] := a[1]*mi;
  end if;
  a[2] := a[2] *m;
  return a, m, mi;
end intrinsic;

intrinsic InternalLLL(p::[]:Gram := false) -> [], Mtrx
  {}
  n := #p;
  K := NumberField(Order(p[1][1]));
  T := IdentityMatrix(K, n);

  L := InternalExactLattice(1*MaximalOrder(K));
  L := GramMatrix(L);


  mu := 0;
  if not false then
    vprint RelLLL, 1: "SingelSteps...";
    for i in [1..#p] do
      vprint RelLLL, 2: "i:", i;
      a, m := InternalSingleIdeal(p[i]:Mu := InternalScalarProduct(p[i][2], p[i][2]:Gram := Gram, Hermite), T := L);
      p[i] := a;
      MultiplyRow(~T, m, i);
    end for;
    vprint RelLLL, 1: "done";
  end if;
  b := [p[1][2]];
  B := [InternalScalarProduct(b[1], b[1]:Gram := Gram, Hermite)];
  nB := [MyNorm(B[1])];
  assert nB[1] gt 0;

  k := 2;

  M := 2^20;
//  M := 0;
  CF := true;
  while k le n do
    b[k] := p[k][2];
    for l in [1..k-2] do
      vprintf RelLLL, 2: "%o, ", <k, l>;
      m := InternalScalarProduct(p[k][2], b[l]:Gram := Gram, Hermite)/B[l];
      mu := Qround(m, M:ContFrac := CF);
      r := InternalApprox(mu, p[l][1]/p[k][1]: T := L);
//      "trivial?", r eq 0;
      AddRow(~T, -r, l, k);
      p[k][2] := p[k][2] -r*p[l][2];
      b[k] := b[k] - mu*b[l];
      assert M ne 0 or InternalScalarProduct(b[k], b[l]:Gram := Gram, Hermite) eq 0;
      b[k] := Parent(b[k])![Qround(x, M:ContFrac := CF): x in Eltseq(b[k])];
    end for;
    B[k] := InternalScalarProduct(p[k][2], b[k]:Gram := Gram, Hermite);
    assert M ne 0 or B[k] eq InternalScalarProduct(b[k], b[k]:Gram := Gram, Hermite);
    nB[k] := MyNorm(B[k]);
    if nB[k] le 0 or Trace(B[k]) le 0 then
      vprintf RelLLL, 1: "Loss of Precision!";
      M *:= M;
      k := 2;
      continue;
    end if;
    assert nB[k] gt 0;

    q := nB[k]/nB[k-1]*Norm(p[k][1])/Norm(p[k-1][1]);
    if q lt 9/10 or Random(8) ge 6 then
      vprint RelLLL, 1: "SWAP", k, k-1;
      SwapRows(~T, k, k-1);
      z := p[k-1];
      p[k-1] := p[k];
      p[k] := z;
      
      B[k-1] := B[k];
      nB[k-1] := nB[k];
      b[k-1] := b[k];
      assert b[1] eq p[1][2];
      k -:= 1;
      if k eq 1 then
        k := 2;
      end if;
    else
      vprint RelLLL, 1: "no swap", k, k-1;
      l := k-1;
      vprint RelLLL, 2: <k, l>;
      m := InternalScalarProduct(p[k][2], b[l]:Gram := Gram, Hermite)/B[l];
      mu := m;
      mu := Qround(m, M:ContFrac := CF);
      r := InternalApprox(mu, p[l][1]/p[k][1]);
      AddRow(~T, -r, l, k);
      p[k][2] := p[k][2] - r*p[l][2];
      b[k] := b[k] - mu*b[l];
      assert M ne 0 or InternalScalarProduct(b[k], b[l]:Gram := Gram, Hermite) eq 0;
      b[k] := Parent(b[k])![Qround(x, M:ContFrac := CF): x in Eltseq(b[k])];
      B[k] := InternalScalarProduct(p[k][2], b[k]:Gram := Gram, Hermite);
      assert M ne 0 or B[k] eq InternalScalarProduct(b[k], b[k]:Gram := Gram, Hermite);
      nB[k] := MyNorm(B[k]);
      if nB[k] le 0 or Trace(B[k]) le 0 then
        M *:= M;
        "Loss of Precision!";
        k := 2;
        continue;
      end if;
      assert nB[k] gt 0;

      k +:= 1;
    end if;
  end while;

  return p, T;
end intrinsic;

