freeze;

declare verbose RLLL, 5;
declare attributes FldAlg : ComplexConjugate;

import "Reduce.m" : InduceAut, GetX;  


intrinsic ScalarProduct
(a::ModTupFldElt, b::ModTupFldElt:Gram := false, Hermite := false) -> RngElt
  {ScalarProduct of two vectors. The Gram option takes a matrix.
   The Hermite option applies conjugation to the second vector.}
  
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

intrinsic ScalarProduct
(a::ModDedElt, b::ModDedElt:Gram := false, Hermite := false) -> RngElt
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

intrinsic ExactLength(x::RngOrdElt) -> RngIntElt
  {}
  
  K := NumberField(Parent(x));
  n := Degree(K);
  f, c := HasComplexConjugate(K);
  if f then
    return Integers()!Trace(x*c(x));
  end if;

  require IsAbelian(K) or Signature(K) eq n: "Exact length only works for abelian or totally real fields";
end intrinsic;

intrinsic ExactLength(x::FldAlgElt) -> FldRatElt
  {}
    
  K := Parent(x);

  f, c := HasComplexConjugate(K);
  if f then
    return Trace(x*c(x));
  end if;

  n := Degree(K);
  require IsAbelian(K) or Signature(K) eq n: "Exact length only works for abelian or totally real fields";

end intrinsic;

intrinsic ExactScalarProduct(x::FldAlgElt, y::FldAlgElt) -> FldRatElt
  {}

  K := Parent(x);
  f, c := HasComplexConjugate(K);
  if f then
    return Trace(x*c(y));
  end if;
  n := Degree(K);
  require IsAbelian(K) or Signature(K) eq n: "Exact length only works for abelian or totally real fields";
  
end intrinsic;    

intrinsic ExactScalarProduct(x::RngOrdElt, y::RngOrdElt) -> RngIntElt
  {}

  K := NumberField(Parent(x));
  f, c := HasComplexConjugate(K);
  if f then
    return Integers()!Trace(x*c(y));
  end if;
  n := Degree(K);
  require IsAbelian(K) or Signature(K) eq n: "Exact length only works for abelian or totally real fields";
  
end intrinsic;    

intrinsic ExactLattice(I::RngOrdFracIdl: T := false, Mu := false) -> Lat, Map
  {}
  
  K := NumberField(Order(I));
  n := Degree(K);
  require IsAbelian(K) or Signature(K) eq n: "Exact lattice only works for abelian or totally real fields";

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
      G[i][i] := ExactLength(B[i]);
      for j in [i+1..n] do
        G[i][j] := ExactScalarProduct(B[i], B[j]);
        G[j][i] := G[i][j];
      end for;
    end for;
  end if;

  //l := Lattice(BasisMatrix(I), G); // the basis is IGNORED!!!
//  "LatticeWithGram";
//  time l := LatticeWithGram(G: CheckPositive:=false);
  l := LatticeWithGram(G);

  B := BasisMatrix(I);

  return l, map<l->P | x :->P!Eltseq(Matrix(BaseRing(B), x)*B),
                              y :->l!Eltseq(Solution(B, Matrix([Eltseq(y)])))>;
end intrinsic;

/*

  G := Sp(4,3);
    C:=CharacterTable(G);
T := GModule(C[13]:SparseCyclo := false);
T;
SchurIndices(C[13]);
ActionGenerators(T)[1];
SetVerbose("Reduce", 2); SetVerbose("Cohomology", 2); S := 
AbsoluteModuleOverMinimalField(T);
S := AlmostIntegralGModule(T);
M := InvariantForm(S:eps := 10.0^-10);
NN := Matrix(Nrows(M), Ncols(M), [Approx(#G*x, 1*MaximalOrder(K)) : x in 
Eltseq(M)]);
K := CoefficientRing(M);
_, s := HasComplexConjugate(CoefficientRing(N));
a[1]*NN*Transpose(InduceAut(a[1], s)) eq NN;


*/

intrinsic AlmostInvariantForm(M::ModGrp) -> Mtrx
  {Computes &+ g*Transpose(g) for g the geenrators of the group}

  if assigned M`InvForm then
    return M`InvForm;
  end if;

  a := ActionGenerators(M);
  K := CoefficientRing(M);
  fl, s := HasComplexConjugate(K);
  require fl: "GModule must be defined over a field with complex conjugation";
  n := Nrows(a[1]);
  b := [ InduceAut(x, s) : x in a];
  h := hom<Group(M) -> GL(n, K)| a>;
  j := hom<Group(M) -> GL(n, K)| b>;
  //f  :=  &+ [Matrix(h(g)*Transpose(j(g))) where g := Random(Group(M)): i in [1..20]];
  f  :=  &+ [Matrix(h(g)*Transpose(j(g))): g in Generators(Group(M))];
  return f;
end intrinsic;


intrinsic Approx(s::RngElt, I :: RngOrdFracIdl: T:= false, Test := true) -> RngElt
  {Finds an element in the ideal I that is "close" to the field element s.}
 
  L, mL := ExactLattice(I:T := T);  
  Tin := T;
  B := Matrix(Rationals(), BasisMatrix(I));
  FO := FieldOfFractions(Order(I));
  if true then
    vprint RLLL, 3: "LLL:"; 
    vtime RLLL, 3: LL, T := LLL(L:Sort := false);

    ss := Solution(B, Matrix([Eltseq(FO!s)]));
    ss := Solution(Matrix(Rationals(), T), ss);
    st := Eltseq(ss);
    if not true then
      st := [Ceiling(x+1/2)/1 : x in st];
    elif not true then
      vprint RLLL, 3: "Closest vectors";
      vtime RLLL, 3: st, r := ClosestVectors(LL, AmbientSpace(LL)!Eltseq(st));
      if exists(x){x : x in st | IsZero(x)} then
        st := x;
      else
        st := st[1];
      end if;
      st := Eltseq(st);
      ChangeUniverse(~st, Rationals());
    elif true then
      st := [Round(x)/1 : x in st];
    elif true then
      st := [Floor(x+1/2)/1 : x in st];
    elif not false then
      st := [ x lt 0 select -Round(-x)/1 else Round(x)/1 : x in st];
    end if;

    l := Parent(s)!FO!Eltseq(Matrix([st])*Matrix(Rationals(), T)*B);
  
    vprint RLLL, 3: "Approximating ", s, " by ", l;
    vprint RLLL, 3: "ExactLength of distance", ExactLength(s-l)*1.0;
    if false and Test then
      assert Approx(s-l, I: T := Tin, Test := false) eq 0;
    end if;
    return l;
  else
    ss := CoordinateSpace(L)!Eltseq(Solution(B, Matrix([Eltseq(FO!s)])));
    st := Eltseq(ss);
    if  true then
      st := [x - Ceiling(x+1/2) : x in st];
    elif true then
      st := [x - Round(x) : x in st];
    elif false then
      st := [ x - (x lt 0 select Ceiling(x+1/2) else Ceiling(x-1/2)) : x in st];
    end if;
    st := Parent(ss)!st;

    l := L!(ss-st);

    vprint RLLL, 3: "ExactLength of distance", ExactLength(s-mL(l))*1.0;
    
    return mL(l);
  end if;

end intrinsic;    


// Main applicatioin:
// Let K be a numberfield with complex conjugation.
//  Let r:G -> Aut(L) be a represetntation where L is a O_K module
//  represented by a PMat. So the image of the rep are matrices where the
//  coefficients are in quotients of the coeff. ideals.
//
//  Now, B := sum_g r(g) r(g)^* is a pos. def. hermitian matrix (form) that
//  should be preserved by r:
//  Let x, y in L arbitrary, then x B y^* = x r(h) B (y r(h))^*
//  (provided r(h) acts via :L -> L x -> x r(h))
//  Since: 
//    r(h)Br^*(h) = sum_g r(h)r(g) r^*(g)r^*(h) 
//                = sum_g r(hg) r^*(hg)
//  ((ab)^* = b^* a^*)
//  
//  Then (x,y) -> Tr(x B y^*) defines a pos. def. quadratic form on the
//  Z-lattice L.
//
//  if L = (M, A) where M is a matrix, A the coeff ideals, then
//  B := M B M^* implies we can assume M to be the identity matrix.
//  (but with non-trivial coeff. ideals)
//
//
//
/*
  G := TransitiveGroup(8, 5);
  #G;
  CharacterTable(G);
  R := GModule($1[5]);
  RR := WriteGModuleOver(R, CyclotomicField(5));
  RRR := AbsoluteModuleOverMinimalField(RR);
  q := AlmostIntegralGModule(RRR);
  ShortSubset(InvariantModule(q):Gram := InvariantForm(q));

  G := GL(3, 3);
  T := CharacterTable(G);
  T;
  R := GModule(T[7]:SparseCyclo := false);
  SetVerbose("Cohomology", 2); 
  SetVerbose("Reduce", 2); 
  RR := AbsoluteModuleOverMinimalField(R: Character := R`Character);
  //Nice(RR);
  R := AlmostIntegralGModule(RR);
  M := InvariantForm(R);

  //G too large, InvForm takes too long.
  Q:
    A, B are G invariant. Then
    A+B should also be invariant?
    x in A+B => a = a+b for some a in A and b in B  
    s(x) = s(a+b) = ~a + ~b since A and B are invariant.  

*/
intrinsic QuaternionicDual(R::ModGrp) -> ModGrp
  {The transpose inverse complex conjugate of R}
  K := BaseRing(R);
  require ISA(Type(K),AlgQuat): "Not over a quaternion algebra";
   E := ActionGenerators(R);
   E := [InduceAut(Transpose(x^-1), Conjugate) : x in E];
   return GModule(Group(R), E: Check := false);
end intrinsic;

intrinsic HermitianDual(R::ModGrp) -> ModGrp
  {The transpose inverse complex conjugate of R}
  K := BaseRing(R);
  require ISA(Type(K),FldNum) or Type(K) eq AlgQuat or K eq Rationals():
  "Need to be over a number field or a qauternion algebra";
   b, s := HasComplexConjugate(K);
   require b: "Complex Conjugation does not exist";
   E := ActionGenerators(R);
   E := [InduceAut(Transpose(x^-1), s) : x in E];
   return GModule(Group(R), E: Check := false);
end intrinsic;

intrinsic InvariantForm(R::ModGrp:eps := 10.0^-1, Hermite := true, GroupOrder := false, IsAbsIrreducible := true, GroupRandom := false, OneEntry := false) -> Mtrx
  {For a (almost) integral G module of some finite group, compute a (hermitian) form that is invariant}
  if assigned R`InvForm then
    return R`InvForm;
  end if;

  if IsAbsIrreducible then
    if Hermite then
      RR := HermitianDual(R);
    else
      RR := Dual(R);
    end if;
    X := GetX(ActionGenerators(R), ActionGenerators(RR));
    //X := AHom(R, RR);
    //X := Matrix(X.1);
    X := X/X[1][1];
    R`InvForm := X;
    return X;
  end if;

  require assigned R`PMat : "GModule must be (almost) integral, call AlmostIntegralGModule first";

  if GroupOrder cmpeq false then
    GroupOrder := Order(Group(R));
  end if;
  G := Group(R);
  if GroupRandom then
    rp := G;
  else
    rp := RandomProcess(G);
  end if;
  //All action matrices have denominators bounded by the
  //denominator of quotients of coefficient ideals, thus products of
  //mat * Transpose(mat) is bounded by the square. 
  //Careful: this is not entirely correct...
  //It is when one scales by the PMat-Matrix.
  c := CoefficientIdeals(R`PMat);
  d := Lcm([Denominator(x) : x in c cat [y^-1 : y in c]]);
  d *:= d;


  E := ActionGenerators(R);
  BasisM := Matrix(R`PMat);
  BasisM_inv := BasisM^-1;
  E := [BasisM*x*BasisM_inv : x in E];
  ER := E;
  Append(~E, Id(Universe(E)));
  if GroupRandom then
    h := Representation(R);
  end if;
  vprint RLLL, 1: "starting random...";
  for i in [1..2] do
    Append(~E, BasisM*h(Random(rp))*BasisM_inv);
  end for;
  vprint RLLL, 1: "using elements of orders", [Order(x) : x in E], 
      "for Plesken/Souvignier iteration";


  //plesken souvignier:
  //r_e(X) := 1/#E sum_e in E e(X)
  //when iterated converges to 1/#G sum_g in G e(G)

  K := CoefficientRing(E[1]);
  M := MaximalOrder(K);
  M := 1*M;
  T := GramMatrix(ExactLattice(M));

  if Hermite then
    _, s := HasComplexConjugate(K);
  else
    s := func<x|x>;
  end if;

  //TODO: projective matrices, ie. integral + denominator/ scalar factor
  //Test: scalar factor in Z or in K?

  A := [E[x] : x in [1..#ER]];
  As := [Transpose(InduceAut(x, s)) : x in A];
  function projMat(X)
    d := LCM([Denominator(x) : x in Eltseq(X)]);
    X := d*X;
    return <d, X, 0>;
  end function;
  procedure projMatSimplify(~X)
    if X[3] eq 0 then
      return;
    end if;
    X[3] := 0;
    if X[1] eq 1 then
      return;
    end if;
    d := GCD([X[1]] cat &cat [ChangeUniverse(Eltseq(x), Integers()) : x in Eltseq(X[2])]);
    if d eq 1 then
      return;
    end if;
    X[1] div:= d;
    X[2] := X[2]/d;
    return;
  end procedure;

  function projMatAdd(X, Y)
    C := <X[1]*Y[1], X[1]*Y[2]+Y[1]*X[2], X[3]+Y[3]+1>;
    return C;
  end function;
  function projMatMult(X, Y)
    C := <X[1]*Y[1], X[2]*Y[2], X[3]+Y[3]+2>;
    return C;
  end function;
  
  E := <"P", [ <"S", ox, [ <projMat(y), projMat(Transpose(InduceAut(y, s)))> 
            where y := x^i : i in [0..Order(x)-1]]> where ox := Order(x) : x in E ]>;

//  E := <"S", [ <1/#E*y, 1/1*Transpose(InduceAut(y, s))> : y in E ]>;
//  E := <"P", [ <"S", [ <1/2*Id(Universe(A)), Id(Universe(A))>, 
//               <1/2*y, Transpose(InduceAut(y, s))>]> : y in A ]>;

  function rho(X, F)
    projMatSimplify(~X);
    if F[1] cmpeq "S" then
      s := rho(X, F[3][1]);
      for x := 2 to #F[3] do
        s := projMatAdd(s, rho(X, F[3][x]));
      end for;
      s[1] *:= F[2];
      return s;
    elif F[1] cmpeq "P" then
      for p in F[2] do
        X := rho(X, p);
      end for;
      return X;
    else
      if OneEntry then
        s := projMatMult(F[1],X);
      else
        s := projMatMult(projMatMult(F[1],X),F[2]);
      end if;
      return s;
    end if;
  end function;

  X := Id(Universe(A));
  if OneEntry then
    X := projMat(Transpose(X[1]));
  else
    X := projMat(X);
  end if;
  it := 0;
  repeat
    repeat
      if GetVerbose("RLLL") eq 2 then
        vprint RLLL, 2: "Iteration....";
      else
        vprint RLLL, 3: "Iteration....", X;
      end if;
      Y := X;

      vtime RLLL, 2: X := rho(X, E);
      //time m := Maximum([Length(#G*(x[i]-y[i])) where x := Eltseq(X[2]/X[1]) where y := Eltseq(Y[2]/Y[1]) : i in [1..Nrows(X[2])*Nrows(X[2])]]);
      vtime RLLL, 2: 
          m := Maximum([Maximum([Abs(t) : t in Eltseq(d*GroupOrder*x)])*1.0 
                           : x in Eltseq(Y[2]*X[1] - X[2]*Y[1])])/X[1]/Y[1];
      vprint RLLL, 2: "current distance", m;
      it +:=1;
      if false and it gt 4 then return X; end if;

    until m lt eps;

    projMatSimplify(~X);
    vprint RLLL, 2: "rounding...";
    vtime RLLL, 2:
      Y := Matrix(Nrows(X[2]), Ncols(X[2]), [Approx(d*GroupOrder*x/X[1], M:T := T) :
               x in Eltseq(X[2])]);
    vprint RLLL, 2: "test for invariance .. ";         
    eps := eps/10;           
    if OneEntry then
      IsInv := forall{x : x in [1..#ActionGenerators(R)] | A[x]*Y eq Y};  
    else
      IsInv := forall{x : x in [1..#ActionGenerators(R)] | A[x]*Y*As[x] eq Y};  
    end if;
  until IsInv;
  if OneEntry then
    Y := BasisM_inv * Y;
  else
    Y := BasisM_inv * Y * Transpose(InduceAut(BasisM_inv, s));
  end if;
  R`InvForm := Y;
  return Y;
end intrinsic;
  
intrinsic NormalizeIdeals(P::PMat) -> PMat, Mtrx
  {Replacs the coefficient ideals by canonical (small) ones}

  C := CoefficientIdeals(P);
  d := [];
  for c :=1 to #C do
    C[c], d[c] := ClassRepresentative(C[c]);
  end for;
  X := DiagonalMatrix(d);
  return PseudoMatrix(C, X*Matrix(P)), X;
end intrinsic;

intrinsic CoefficientRing(P::PMat) -> Rng
  {The coefficient ring (order) that acts on P}
  return CoefficientRing(Matrix(P));
end intrinsic;

intrinsic CoefficientIdeal(M::PMat, L::Mtrx) -> RngOrdFracIdl
  {The coefficient ideal of L wrt to the module represented by M}

  require L ne 0*L : "The element cannot be zero";
  C := CoefficientIdeals(M);
  L := Matrix(FieldOfFractions(Order(C[1])), L);
  fl, X := IsConsistent(Matrix(M), L);
  require fl: "The element must be contained in the vectorspace generated by M";
  X := Eltseq(X);

  return &meet [C[i]/X[i] : i in [1..#C] | X[i] ne 0];
end intrinsic;

intrinsic AdaptedBasis(L::PMat, B::[]) -> PMat, Mtrx
  {Finds a basis for L meet B*Q such that the transformation to B is triangular}
  K := NumberField(CoefficientRing(Matrix(L)));
  // Step 1: find the representation of B in terms of L
  vprint RLLL, 2: "Finding representation of short vectors in starting basis";
  vtime RLLL, 2: 
  fl, T := IsConsistent(Matrix(K, Matrix(L)), Matrix(K, [Eltseq(x) : x in B]));
  assert fl;
  Tp := PseudoMatrix([x^-1 : x in CoefficientIdeals(L)], Transpose(T));
  vprint RLLL, 2: "Hermite form on trafo";
  vtime RLLL, 2:
  H, Ht := HermiteForm(Tp); //lower triang  Ht*Tp = H
  p := [i : i in [1..Nrows(Matrix(H))] | not IsZero(Matrix(H)[i])];

  C := CoefficientIdeals(H);
  Ht := Ht^-1;
  P :=  PseudoMatrix([C[i]^-1 : i in p], 
    Matrix([Transpose(Ht)[i] : i in p])*Matrix(L));
  return P;  
    
end intrinsic;    

intrinsic AdaptedBasisIndex(L::PMat, B::[]) -> RngOrdFracIdl, RngIntElt
  {Finds a basis for L meet B*Q such that the transformation to B is triangular}
  K := NumberField(CoefficientRing(Matrix(L)));
  // Step 1: find the representation of B in terms of L
  vprint RLLL, 2: "Finding representation of short vectors in starting basis";
  vtime RLLL, 2: 
  fl, T := IsConsistent(Matrix(K, Matrix(L)), Matrix(K, [Eltseq(x) : x in B]));
  assert fl;
  Tp := PseudoMatrix([x^-1 : x in CoefficientIdeals(L)], Transpose(T));
  vprint RLLL, 2: "Hermite form on trafo";
  vtime RLLL, 2:
  H, Ht := HermiteForm(Tp); //lower triang  Ht*Tp = H
  p := [i : i in [1..Nrows(Matrix(H))] | not IsZero(Matrix(H)[i])];
  if #p lt #B then
    return 0, #p;
  end if;
  C := CoefficientIdeals(H);
  Ht := Ht^-1;
  P :=  PseudoMatrix([C[i]^-1 : i in p], 
    Matrix([Transpose(Ht)[i] : i in p])*Matrix(L));
  fl, T := IsConsistent(Matrix(K, Matrix(P)), Matrix(K, [Eltseq(x) : x in B]));
  assert fl;
  return Determinant(T)*(&*CoefficientIdeals(P))^-1, #B;
end intrinsic;    

intrinsic AdaptedBasisProcessInit(L::PMat) -> SetEnum
  {}
  s := {1};
  AddAttributes(Type(s), ["PMat", "T", "H", "B", "Type"]);
  s`PMat := L;
  s`B := [];
  s`Type := "ABIP";
  return s;
end intrinsic;

intrinsic AdaptedBasisProcessAddTest(s::SetEnum, B::Mtrx) -> .
  {}
  if s`B eq [] then
    if B eq 0 then
      error "";
    end if;
    return CoefficientIdeal(s`PMat, B);
  end if;

  B := s`T*B;
  if IsZero(B) then
    return 0;
  end if;
  N := PseudoMatrix(CoefficientIdeals(s`H), VerticalJoin(Matrix(s`H), B));
  H, Ht := HermiteForm(N);
  p := [i : i in [1..Nrows(Matrix(H))] | not IsZero(Matrix(H)[i])];
  if #p lt Ncols(H) then
    return 0;
  end if;
  K := NumberField(CoefficientRing(Matrix(s`PMat)));
  C := CoefficientIdeals(H);
  Ht := Ht^-1;
  P :=  PseudoMatrix([C[i]^-1 : i in p], 
    Matrix([Transpose(Ht)[i] : i in p])*Matrix(s`PMat));
  assert Transpose(H)* Matrix(P) eq Matrix(K, [Eltseq(x) : x in B]);
  return Determinant(H);
end intrinsic;

intrinsic AdaptedBasisProcessAdd(s::SetEnum, B::Mtrx) -> .
  {}
  if s`B cmpeq [] then
    if B eq 0 then
      error "";
    end if;
    s`H := PseudoMatrix(Matrix(B));
    s`T := IdentityMatrix(CoefficientRing(B), Ncols(B));
    s`B := Matrix(B);
    return 1;
  end if;

  B := s`T*B;
  if IsZero(B) then
    error "";
  end if;
  N := PseudoMatrix(CoefficientIdeals(s`H), VerticalJoin(Matrix(s`H), B));
  H, Ht := HermiteForm(N);
  p := [i : i in [1..Nrows(Matrix(H))] | not IsZero(Matrix(H)[i])];
  if #p lt Ncols(H) then
    error "";
  end if;
  if true then
    K := NumberField(CoefficientRing(Matrix(s`PMat)));
    C := CoefficientIdeals(H);
    HT := Ht^-1;
    P :=  PseudoMatrix([C[i]^-1 : i in p], 
      Matrix([Transpose(HT)[i] : i in p])*Matrix(s`PMat));
    assert Transpose(H)* Matrix(P) eq Matrix(K, [Eltseq(x) : x in B]);
  end if;
  s`H := H;
  s`T := s`T*Ht;
  s`B := VerticalJoin(s`B, B);
  return 1;
end intrinsic;




intrinsic GramSchmidtProcess(L::[]: Gram := false, Hermite := true) -> [], Mtrx
{Performs a Gram-Schmidt reduction on the pseudo basis}

  // now the size reduction...
  // The 1st basis vector is correct - it's a multiple of B[1]
  // which is supposedly (very) short.
  // Now induction: we compute the Gram-Schmidt coefficients and "round" them
  // to the nearest (algebraic) integer...
 
  M := Matrix(L);
  m := Nrows(M);
  GS := Matrix([Eltseq(M[1])]);
  K := CoefficientRing(M);
  mu := ZeroMatrix(K, m, m);
  if Gram cmpne false then
    Gram := Matrix(K, Gram);
  end if;


  vprint RLLL, 2: "Start GS stuff";
  mu[1][1] := ScalarProduct(M[1], M[1]:Gram := Gram, Hermite := Hermite);
  for i := 2 to m do
    vprint RLLL, 2: "building mu for i=", i;
    vtime RLLL, 2:
    for j := 1 to i-1 do
      mu[i][j] := ScalarProduct(M[i], GS[j]: Gram := Gram, Hermite := Hermite);
    end for;

    GSn := M[i] - &+ [mu[i][j] / mu[j][j] * 
                 GS[j] : j in [1..i-1] ];
    GS := VerticalJoin(GS, GSn);
    assert forall{x : x in [1..i-1] | IsZero(ScalarProduct(GS[i], GS[x] : Gram := Gram, Hermite := Hermite))};             
    mu[i][i] := ScalarProduct(GS[i], GS[i]:Gram := Gram, Hermite := Hermite);             
  end for;
  return GS;
end intrinsic;


intrinsic GramSchmidtReduction(L::PMat: Gram := false, Hermite := true) -> PMat, Mtrx
{Performs a Gram-Schmidt reduction on the pseudo basis}

  // now the size reduction...
  // The 1st basis vector is correct - it's a multiple of B[1]
  // which is supposedly (very) short.
  // Now induction: we compute the Gram-Schmidt coefficients and "round" them
  // to the nearest (algebraic) integer...
 
  M := Matrix(L);
  C := CoefficientIdeals(L);
  m := Nrows(M);
  GS := Matrix([Eltseq(M[1])]);
  K := CoefficientRing(M);
  mu := ZeroMatrix(K, m, m);
  if Gram cmpne false then
    Gram := Matrix(K, Gram);
  end if;

  vprint RLLL, 1: "Start length";
  vprint RLLL, 1: [Trace(ScalarProduct(M[i], M[i]: Gram := Gram, Hermite := Hermite)) : i in [1..Nrows(M)]];

  vprint RLLL, 2: "Start GS stuff";
  mu[1][1] := ScalarProduct(M[1], M[1]:Gram := Gram, Hermite := Hermite);
  for i := 2 to m do
    vprint RLLL, 2: "building mu for i=", i;
    vtime RLLL, 2:
    for j := 1 to i-1 do
      mu[i][j] := ScalarProduct(M[i], GS[j]: Gram := Gram, Hermite := Hermite);
    end for;

    for j := i-1 to 1 by -1 do
      vprint RLLL, 2: "basis reduction ...";
      N := Approx(mu[i][j]/mu[j][j], C[j]/C[i])*M[j];
      M[i] := M[i] - N;
      if not IsZero(N) then
        vprint RLLL, 2: "Correcting by", N, "of length", ScalarProduct(N, N: Gram := Gram, Hermite := Hermite);
      end if;
      for k := 1 to j do
        mu[i][k] := ScalarProduct(M[i], GS[k]: Gram := Gram, Hermite := Hermite);
      end for;
    end for;  
    vprint RLLL, 2: "GS....";
    vtime RLLL, 2:
    GSn := M[i] - &+ [mu[i][j] / mu[j][j] * 
                 GS[j] : j in [1..i-1]];
    GS := VerticalJoin(GS, GSn);
    assert forall{x : x in [1..i-1] | IsZero(ScalarProduct(GS[i], GS[x] : Gram := Gram, Hermite := Hermite))};             
    mu[i][i] := ScalarProduct(GS[i], GS[i]:Gram := Gram, Hermite := Hermite);             
  end for;
  vprint RLLL, 1: "Result length";
  vprint RLLL, 1: [Trace(ScalarProduct(M[i], M[i]: Gram := Gram, Hermite := Hermite)) : i in [1..Nrows(M)]];
  vprint RLLL, 2: "computing total trafo";
  vtime RLLL, 2:
  fl, T := IsConsistent(Matrix(L), M);
  res := PseudoMatrix(C, M);
  assert HermiteForm(res) eq HermiteForm(L);
  return res, T;
end intrinsic;

intrinsic ReconstructBasis(L::PMat, B::[]:Gram := false, Hermite := true) -> PMat, Mtrx
  {Finds a basis for L that is short wrt to B}
  K := NumberField(CoefficientRing(Matrix(L)));
  B := Reverse(B);
  // Step 1: find the representation of B in terms of L
  vprint RLLL, 2: "Finding representation of short vectors in starting basis";
  vtime RLLL, 2: 
  fl, T := IsConsistent(Matrix(K, Matrix(L)), Matrix(K, [Eltseq(x) : x in B]));
  assert fl;
  // Step 2: make the transformation involved triangular
  // Step 3: size reduction.
  // Let's think this through:
  // B = T*M    where M is the matrix part of L
  // Now I want a transformation S of L such that SL = L and TS = triangular
  // (lower triangular in fact)
  // for S to be valid, S[i][j] in C[j]/C[i] (up to swapping i and j and
  // transposing)
  // So we try to put te coeff. ideals of M on T and hope that no scaling
  // takes place. We might have to ensure this in the c-kernel.
  // (This is essentially the same as the  SNF algo, but we don't
  // want (need) a diagonal transformation, we use a triagonal one to
  // preserve B)
  //
  // T*L = B
  // Ht*Transpose(T) = triang = H
  // T*Transpose(Ht) = triang = Transpose(H)
  // T*Tran(Ht)*Tran(Ht)^-1*L = B
  Tp := PseudoMatrix([x^-1 : x in CoefficientIdeals(L)], Transpose(T));
  vprint RLLL, 2: "Hermite form on trafo";
  vtime RLLL, 2:
  H, Ht := HermiteForm(Tp); //lower triang  Ht*Tp = H
  m := Transpose(Ht)^-1*Matrix(L); 
  for i := 1 to Nrows(m) div 2 do
    SwapRows(~m, i, Nrows(m)+1-i);
  end for;
  LL := PseudoMatrix([x^-1 : x in Reverse(CoefficientIdeals(H))], m);

  if not false and GetAssertions() gt 0 then
    B := Reverse(B);
    assert HermiteForm(LL) eq HermiteForm(L);
    fl, _T := IsConsistent(Matrix(K, Matrix(LL)), Matrix(K, [Eltseq(x) : x in B]));
    assert IsLowerTriangular(_T);
    assert Determinant(_T) eq 1;
  end if;

  // now the size reduction...
  // The 1st basis vector is correct - it's a multiple of B[1]
  // which is supposedly (very) short.
  // Now induction: we compute the Gram-Schmidt coefficients and "round" them
  // to the nearest (algebraic) integer...


  M := GramSchmidtReduction(LL:Gram := Gram, Hermite := Hermite);
  fl, T := IsConsistent(Matrix(L), Matrix(M));
  assert HermiteForm(M) eq HermiteForm(L);
  return M, T;
end intrinsic;

intrinsic ReducedBasis(L::Lat) -> []
  {Returns a LLL reduced basis for L}
  if true or Dimension(L) gt 100 then
//    X := LLLBlock(BasisMatrix(L), 100);
    X := LLL(L);
    repeat
      o := &+ [Norm(X.i) : i in [1..Dimension(X)]];
      time X := LLL(X:Delta := 0.9999, InitialSort, DeepInsertions);
    until true or [Norm(X.i) : i in [1..Dimension(X)]] ge o;
    return [L!Eltseq(X.i) : i in [1..Dimension(X)]];
  else
    return [L!x : x in Basis(Seysen(LLL(L:Delta := 0.999)))];
  end if;
end intrinsic;

intrinsic LatticeToZGram(L::PMat: Gram := false) -> Mtrx, UserProgram
  {Computes the corresponding Z-form as a gram matrix}

  C := CoefficientIdeals(L);
  M := Matrix(L);
  K := FieldOfFractions(CoefficientRing(M));
  _, s := HasComplexConjugate(K);

  assert Gram eq Transpose(InduceAut(Gram, s));

  Ms := InduceAut(M, s);
  if Gram cmpne false then
    gram := M*Gram*Transpose(Ms);
  else
    gram := M*Ms;
  end if;
  assert gram eq Transpose(InduceAut(gram, s));

  K := CoefficientRing(Gram);

  n := Nrows(Gram);
  m := Degree(K);

  vprint RLLL, 2: "Building Z-lattice...";
  Z := Integers();
  Q := Rationals();
  G := ZeroMatrix(Q, n*m,n*m);
  e := IdentityMatrix(K, n);
  for i:= 1 to n do
    Bi := Basis(C[i]);
    for j := 1 to n do
      Bj := Basis(C[j]);
      Bjc := [s(x) : x in Bj];
      M := Matrix([[Q|Trace(bi*gram[i][j]*bj) : bj in Bjc] : bi in Bi]);
      InsertBlock(~G, M, (i-1)*m+1, (j-1)*m+1);
    end for;
  end for;
  assert IsSymmetric(G);
//  assert IsPositiveDefinite(G);

  ZtoK := function(x)
    return &+ [x[i+(j-1)*m]*Basis(C[j])[i]*Matrix(L)[j] : i in [1..m], j in [1..n]];
    return Vector(K,[ &+ [x[i+(j-1)*m]*Basis(C[j])[i] : i in [1..m]] : j in [1..n]]);
  end function;

  if false then
    ei := [ZtoK(Eltseq(M[i])) : i in [1..n*m]] where M := IdentityMatrix(Z, n*m);
    for i in [1..n*m] do
      for j in [1..n*m] do
        "??", <i,j>, G[i][j], 
        Trace(ScalarProduct(ei[i], ei[j]:Gram := Gram, Hermite));
        assert Trace(ScalarProduct(ei[i], ei[j]:Gram := Gram, Hermite)) eq G[i][j];
      end for;
    end for;
  end if;

  G *:= Lcm([Denominator(x) : x in Eltseq(G)]);
  G := Matrix(Integers(), G);
  g := Gcd([x : x in Eltseq(G)]);
  if g ne 1 then
    G := Matrix(Integers(), G*(1/g));
  end if;

  return G, ZtoK;
end intrinsic;

intrinsic GSShortOrbitSubset(L::ModGrp, e::Mtrx: Gram := false, OrbitLimit := 500, StartOrbit := false) -> [], []
  {Tries to find Rank(L) many, independent elements in L such that their Gram-Schmit coefficients are not decreasing too fast}
  Z := Integers();

  K := CoefficientRing(L);
  A := ActionGenerators(L);
  e := Vector(K, e);
  assert CoefficientRing(A[1]) eq K;
  n := Ncols(A[1]);
  o := {};
  if StartOrbit cmpeq false then
    n_o := [e];
  else
    n_o := {Vector(K, x) : x in StartOrbit};
  end if;
  j := 2;
  sb := [e];
  GS := [e];
  fl := [0];
  mu := ZeroMatrix(K, n, n);
  B := 2^100;
  red := func<x|Qround(x, B)>;
  red := func<x|x>;
  mu[1][1] := red(ScalarProduct(e, e: Gram := Gram, Hermite));
  min_l := Trace(mu[1][1]/2);
  assert min_l in Rationals();
  assert min_l gt 0;
  "Cut-off", min_l;
  f, c := HasComplexConjugate(K);
  if not f then
    c := func<x|x>;
  end if;
  for i := 2 to n do
    repeat
      if Maximum(fl) lt min_l then
        C := {x*a : a in A, x in n_o} diff o;
        while #C gt OrbitLimit do
          Exclude(~C, Random(C));
        end while;  
        n_o := C;
        o join:= C;
        vprint RLLL, 3: "found", #C, "new ones", "total orbit now", #o;
        C := SetToSequence(C);
        D := C;
        for j in [1..#C] do
          l := ScalarProduct(C[j], C[j]:Gram := Gram, Hermite);
          l := red(l);
          for ii := 1 to i-1 do
            m := ScalarProduct(C[j], GS[ii]:Gram := Gram, Hermite);
            m := red(m);
            C[j] := C[j] - m/mu[ii][ii] * GS[ii];
            C[j] := InduceAut(C[j], red);
            l := l-m*c(m)/mu[ii][ii];
            l := red(l);
//            assert ScalarProduct(C[j], C[j]:Gram := Gram, Hermite) eq l;
            if Trace(l) lt min_l then
              C[j] := 0*C[j];
              "Leaving at level", ii, "of", i-1;
              break;
            end if;
          end for;
        end for;
        D := [D[x] : x in [1..#D] | not IsZero(C[x])];
        C := [C[x] : x in [1..#C] | not IsZero(C[x])];
      end if;  
      if #C eq 0 then
        continue;
      end if;
      for j in [1..#C] do
        C[j] := C[j] - ScalarProduct(C[j], GS[i-1]:Gram := Gram, Hermite)/mu[i-1][i-1] * GS[i-1];
        C[j] := InduceAut(C[j], red);
      end for;
      fl := [Trace(ScalarProduct(C[i], C[i]:Gram := Gram, Hermite)) : i in [1..#C]];
      vprint RLLL, 3: "rel GS length at level ", i, "are", ChangeUniverse(fl, RealField(10));
      m, p := Maximum(fl);
    until #C gt 0 and m gt min_l;
    vprint RLLL, 3: "using element at pos.", p, "and length", m, "basis now", #sb+1;
    Append(~GS, C[p]);
    Append(~sb, D[p]);
    for j := 1 to i do
      mu[i][j] := red(ScalarProduct(D[p], GS[j]: Gram := Gram, Hermite));
    end for;
    D := [D[x] : x in [1..#D] | fl[x] ge min_l];
    C := [C[x] : x in [1..#C] | fl[x] ge min_l];
  end for;

//  [Trace(ScalarProduct(x,x:Gram := Gram, Hermite)) : x in sb];

  return sb, o;
end intrinsic;




intrinsic GSShortSubset(L::PMat: Gram := false, List := false) -> [], []
  {Tries to find Rank(L) many, independent elements in L such that their Gram-Schmit coefficients are not decreasing too fast}
  Z := Integers();

  K := CoefficientRing(L);
  n := Nrows(Matrix(L));
  m := Degree(K);
  if List cmpeq false then
    G, ZtoK := LatticeToZGram(L: Gram := Gram);

    vprint RLLL, 3: "Creating lattice from gram";
    vtime RLLL, 3:
    l := LatticeWithGram(G:CheckPositive := false);
    vprint RLLL, 2: "computing short elements...";
    vtime RLLL, 2: b := ReducedBasis(l);
    vprint RLLL, 3: "creating short elements in modules";
    bb := [ZtoK(x): x in b];
  else
    bb := List;
  end if;
  j := 2;
  sb := [bb[1]];
  // we want to find the next vector with maximal length of the GS
  // projection (ie, as orthogonal to the previous ones as possible)

  if Gram cmpne false then
    Gram := Matrix(CoefficientRing(bb[1]), Gram);
  end if;
  GS := [bb[1]];
  mu := ZeroMatrix(K, n, n);
  mu[1][1] := ScalarProduct(bb[1], bb[1]: Gram := Gram, Hermite);
  C := bb;
  for i := 2 to n do
    for j in [1..#C] do
      C[j] := C[j] - ScalarProduct(C[j], GS[i-1]:Gram := Gram, Hermite)/mu[i-1][i-1] * GS[i-1];
    end for;
    fl := [Trace(ScalarProduct(C[i], C[i]:Gram := Gram, Hermite)) : i in [1..#C]];
    vprint RLLL, 3: "rel GS length at level ", i, "are", ChangeUniverse(fl, RealField(10));
    m, p := Maximum(fl);
    vprint RLLL, 3: "using element at pos.", p, "and length", m;
    Append(~GS, C[p]);
    Append(~sb, bb[p]);
    for j := 1 to i do
      mu[i][j] := ScalarProduct(bb[p], GS[j]: Gram := Gram, Hermite);
    end for;
  end for;

//  [Trace(ScalarProduct(x,x:Gram := Gram, Hermite)) : x in sb];

  return sb, bb;
end intrinsic;


intrinsic ShortSubset(L::PMat: Gram := false, List := false) -> [], []
  {Tries to find Rank(L) many short, independent elements in L}
 
  // Step 1: find the isometric Z-Latice. I think we need a quadratic form
  // somewhere, but we try without first

  n := Nrows(Matrix(L));
  m := Degree(CoefficientRing(L));
  if List cmpeq false then
    vprint RLLL, 1: "Computing Z-gram matrix";
    G, ZtoK := LatticeToZGram(L: Gram := Gram);
    vprint RLLL, 3: "Creating lattice from gram";
    vtime RLLL, 3:
    l := LatticeWithGram(G:CheckPositive := false);
    vprint RLLL, 2: "computing short elements...";
    vtime RLLL, 2: b := ReducedBasis(l);
    b := Sort(b, func<x,y|Norm(x) - Norm(y)>);
    b := Reverse(b);
  //  b := PermuteSequence(b, Random(Sym(#b)));
    vprint RLLL, 3: "creating short elements in modules";
    bb := [ZtoK(x): x in b];
    assert forall{x : x in bb| x in Module(L)};
  else
    bb := List;
  end if;
  j := 2;
  sb := [bb[1]];
  if false then
    //TODO: do modular rank computations!!!
    //possibly with incremental echelon
    vprint RLLL, 1: "finding K-independent elements";
    vtime RLLL, 1:
    for i := 2 to n do
      while Rank(Matrix([Eltseq(x): x in sb] cat [Eltseq(bb[j])])) lt i do
        j +:= 1;
      end while;
      Append(~sb, bb[j]);
    end for;
  elif true then
    for i := 2 to n do
      min := 0;
      pos := 0;
      for l := 2 to #bb do
        if IsZero(bb[l]) then
          continue;
        end if;
        a,b := AdaptedBasisIndex(L, sb cat [bb[l]]);
        if a cmpne 0 then
          if min eq 0 or min gt Norm(a) then
            min := Norm(a);
            pos := l;
          end if;
          if min eq 1 then
            break;
          end if;
        else 
          "setting to zero", l;
          bb[l] *:= 0;
        end if;
      end for;
      "Using index", min, "for", i;
      Append(~sb, bb[pos]);
      bb[pos] *:= 0;
    end for;
  else
    ps := [<1,1>] cat [<i-1, 0> : i in [2..n]];
    best := 0; bp := 0;
    st := 2;
    repeat
      for i := st to n do
        min := 0;
        pos := 0;
        for l := ps[i][1]+1 to n*m do
          a,b := AdaptedBasisIndex(L, [bb[x[1]] : x in ps[1..i-1]] cat [bb[l]]);
          if a cmpne 0 then
            if min eq 0 or min gt Norm(a) then
              min := Norm(a);
              pos := l;
            end if;
            if min eq 1 then
              break;
            end if;
          else
//            "no a";
          end if;
        end for;
//        "Using index", min, "for", i, pos;
        ps[i] := <pos, min>;
        ps[i+1] := <pos, min>;
        if min eq 0 then break; end if;
      end for;
      xp := &* [ x[2] : x in ps];
      "now at", xp, bp, [x[1] : x in ps];
      if best cmpeq 0 and xp ne 0 then
        best := ps;
        bp := xp;
      elif best cmpne 0 and xp lt bp and xp ne 0 then
        best := ps;
        bp := xp;
      end if;
      if xp eq 1 then
        break;
      end if;
      if xp ne 0 then
        st := n-1;
      else
        st -:= 1;
        if st eq 0 then
          "no more vectors";
          break;
        end if;
      end if;
      ps[st][1] +:= 1;
    until false;
    sb := [bb[x[1]] : x in ps];
  end if;
//  "final short elts have length";
//  [Trace(ScalarProduct(x,x:Gram := Gram, Hermite)) : x in sb];

  return sb, bb;
end intrinsic;

intrinsic ReduceBasis(L::PMat:Gram := false, UseGS := false) -> PMat, Mtrx
  {Tries to find a 'nice' basis for L}
  if UseGS then
    return ReconstructBasis(L, GSShortSubset(L:Gram := Gram):Gram := Gram, Hermite);
  else
    return ReconstructBasis(L, ShortSubset(L:Gram := Gram):Gram := Gram, Hermite);
  end if;
end intrinsic;

intrinsic Nice(L::ModGrp:UseAlmostInvariantForm := "Automatic", UseGS := false, GroupOrder := false) -> ModGrp
  {Tries to find a nicer version of L}
  if Type(CoefficientRing(L))  eq FldRat then
    return GModule(Clean(GModule(L, Integers())), Rationals());
  elif Type(CoefficientRing(L)) eq RngInt then
    return Clean(L);
  else
    require ISA(Type(CoefficientRing(L)), FldAlg):
      "GModule must be over the rationals of a number field";
  end if;
  if not assigned L`PMat then
    _ := IsAlmostIntegral(L);
  end if;
  P := L`PMat;
  PT := Matrix(P);
  if UseAlmostInvariantForm cmpeq "Automatic" then
    if #Sprint(ActionGenerators(L)) ge 10^6 then
      L := Nice(L:UseAlmostInvariantForm);
      delete L`InvForm;
    end if;
    UseAlmostInvariantForm := false;
  end if;
  if UseAlmostInvariantForm then
    vprint RLLL, 1: "using almost invariant form only";
    F := AlmostInvariantForm(L);
  else
    vprint RLLL, 1: "using invariant form";
    vtime RLLL, 1: F := InvariantForm(L: GroupOrder := GroupOrder);
  end if;
  _, s := HasComplexConjugate(CoefficientRing(L));
  PR := PseudoMatrix(CoefficientIdeals(P), 
                          IdentityMatrix(CoefficientRing(PT), Nrows(PT)));
  FR := PT*F*Transpose(InduceAut(PT, s));
  FR /:= &* [FR[i][i] : i in [1..Nrows(FR)]];
  //FR /:= &+ [FR[i][i] : i in [1..Nrows(FR)]];
  //FR /:= FR[1][1];

  l, x := ReduceBasis(PR: Gram := FR, UseGS := UseGS);
  x := Matrix(CoefficientRing(L), x*PT);
  xi := x^-1;
  N := GModule(Group(L), [x*y*xi : y in ActionGenerators(L)]);
  if assigned L`Character then
    N`Character := L`Character;
  end if;
  if assigned L`InvForm then
    N`InvForm := x*L`InvForm*Transpose(InduceAut(x, s)) 
      where _, s := HasComplexConjugate(CoefficientRing(x));
  end if;    
  N`PMat := PseudoMatrix(CoefficientIdeals(l), 
                              IdentityMatrix(CoefficientRing(PT), Nrows(PT)));
  return N;
end intrinsic;

