freeze;
// W.A. de Graaf & J. Pilnikova.

//  A  - algebra (csa of deg 2)
//  zd - zero divisor in A
function MinimalLeftIdeal(A, zd)

  rho := KMatrixSpace(CoefficientRing(A), 4, 4) ! 0;
  for i := 1 to 4 do
    rho[i] := Vector(Coordinates(A, Basis(A)[i]*zd));
  end for;

  leftId := Kernel(rho);

  b := [A | 0,0 ];
  for i := 1 to 2 do
    for k := 1 to 4 do
      b[i] +:= Basis(leftId)[i][k] * Basis(A)[k];
    end for;
  end for;

  return b;

end function;

//  A - algebra (csa of deg 2)
//  L - list of 2 elements forming a basis 
//      of a minimal (2-dimensional) left ideal
//  output: matica 4x4, riadky su suradnice std bazy M2(Q) v baze A
function SplitAlgebra(A,L)

  F := CoefficientRing(A);

  m := KMatrixSpace(F, 3, 4) ! 0;
  for i := 1 to 2 do
    m[i] := Vector(Coordinates(A, L[i]));
  end for;

  M2 := MatrixAlgebra(F, 2);
  v := M2 ! 0;
  V := [M2 | ];
  for i := 1 to 4 do
    for j := 1 to 2 do
      m[3] := Vector(Coordinates(A, Basis(A)[i]*L[j]));
      ker := Basis(Kernel(m))[1];
      v[j] := Vector([-ker[1]/ker[3], -ker[2]/ker[3]]);
    end for;
    V[i] := Transpose(v);
  end for;

  //  splitM - matrix of transformation A -> M2
  splitM := KMatrixSpace(F, 4, 4) ! 0;
  for i := 1 to 4 do
    splitM[i] := Vector(Coordinates(M2, V[i]));
  end for;

  rSplitM := splitM^-1;

  return rSplitM;

end function;


/*
//  test the matrix rMapM mapping M2 -> A
//  rows of rMapM should contain coordinates of std basis M2 
//  w.r.t. the basis of A
function TestIsomorphism(M2, A, rMapM)

  its_fine := true;

  for i := 1 to 4 do
    for j := 1 to 4 do
      r1 := Vector(Coordinates(M2, Basis(M2)[i]*Basis(M2)[j])) * rMapM;

      vi := Vector(Coordinates(M2, Basis(M2)[i])) * rMapM;
      vj := Vector(Coordinates(M2, Basis(M2)[j])) * rMapM;
      wi := A ! 0;
      wj := A ! 0;
      for k := 1 to 4 do
        wi +:= vi[k] * Basis(A)[k];
        wj +:= vj[k] * Basis(A)[k];
      end for;
      r2 := Vector(Coordinates(A, wi * wj));

      if (r1 ne r2) then
        //print "not good:",i,j;
        its_fine := false;
      end if;
    end for;
  end for;

  return its_fine;

end function;
*/


//  x - cyclic element
//  find b s.t. bxb^{-1} = sigma(x)
function ConjugatingElement(A, x)

  F := CoefficientRing(A);

  poly := MinimalPolynomial(x);
  K<y> := NumberField(poly);
  roots := Roots(poly, K);

  if (roots[1][1] eq y) then
    sigma_x := roots[2][1];
  else
    sigma_x := roots[1][1];
  end if;
  coords := Eltseq(sigma_x);
  sx := coords[1]*(Parent(x) ! 1) + coords[2]*x;

  //  find b s.t. b * a = sx * b
  lhs := KMatrixSpace(F, 4, 4) ! 0;
  rhs := KMatrixSpace(F, 4, 4) ! 0;
  
  c_x := Coordinates(A, x);
  c_sx := Coordinates(A, sx);

  //  the table of structure constants
  struct := [];
  for i := 1 to 4 do
    str := [];
    for j := 1 to 4 do
      str[j] := Coordinates(A, Basis(A)[i]*Basis(A)[j]);
    end for;
    struct[i] := str;
  end for;

  for i := 1 to 4 do
    for j := 1 to 4 do
      c := 0;
      for k := 1 to 4 do
        c +:= c_x[k]*struct[j,k,i];
      end for;
      lhs[i][j] := c;
    end for;
  end for;

  for i := 1 to 4 do
    for j := 1 to 4 do
      c := 0;
      for k := 1 to 4 do
        c +:= c_sx[k]*struct[k,j,i];
      end for;
      rhs[i][j] := c;
    end for;
  end for;

  sol := Nullspace(Transpose(lhs-rhs));

  c_b := Basis(sol)[1];
  b := A ! 0;
  for k := 1 to 4 do
    b +:= c_b[k] * Basis(A)[k];
  end for;

  return b;

end function;


//  vrati true,  a, b   - ak a,b su generatory A ako cyklickej algebry
//        false, d, _   - ak d je delitel nuly
//        false, _, _   - ak d je v centre A
function CyclicAlgebra(A, x)

  if (x in Center(A)) then 
    //print "input element in the center";
    return false, _, _;
  end if;

  //  whether x is a zero divisor
  if not IsInvertible(x) then
    //print "special case: noninvertible element";
    return false, x, _;
  end if;

  //  whether x has reducible minimal polynomial
  //  -> find a zero divisor
  m_x := MinimalPolynomial(x);
  fs := Factorization(m_x);
  if (#fs gt 1) or (fs[1][2] gt 1) then
    //print "special case: reducible minimal polynomial";
    zd := Evaluate(fs[1][1], x);
    return false, zd, _;
  end if;

  //  x is cyclic
  //  find b s.t. b * a = sa * b
  b := ConjugatingElement(A,x);

  return true, x, b;

end function;



//  A - algebra (csa of deg 2)
//  output: matica 4x4, riadky su suradnice std bazy M2(Q) v baze A
function SplitDeg2Algebra(A)

  r := Basis(A)[1];
  if r in Center(A) then
    r := Basis(A)[2];
  end if;

  bool, a, b := CyclicAlgebra(A, r);
  if bool then
    beta := (b*b)[1][1];
    poly := MinimalPolynomial(a);
    K<y> := NumberField(poly);
    is_split, sol := NormEquation(K, 1/beta);
    if is_split then
      n := sol[1][1] + sol[1][2]*a;
      e := 1 + n*b;
      L := [e, a*e];
    end if;
  else
    // a is a zero divisor
    L := MinimalLeftIdeal(A, a);
  end if;

  M2 := MatrixAlgebra(CoefficientField(A), 2);
  rM := SplitAlgebra(A, L);
  //TestIsomorphism(M2, A, rM);

  return rM;

end function;

