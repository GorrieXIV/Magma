freeze;
// W.A. de Graaf & J. Pilnikova.

//  ###################################################
//  ##  input: A = algebra (csa of deg 3)
//  ##         zd = zero divisor in A
//  ###################################################
MinimalLeftIdeal := function(A, zd)

  if (IsInvertible(zd)) then
    //print "the element is invertible";
  end if;

  rho := KMatrixSpace(Rationals(), 9, 9) ! 0;
  for i := 1 to 9 do
    rho[i] := Vector(Coordinates(A, Basis(A)[i]*zd));
  end for;

  leftId := Kernel(rho);
  if (Dimension(leftId) ne 3) then
    leftId := Image(rho);
  end if;

  b := [A | 0,0,0];
  for i := 1 to 3 do
    for k := 1 to 9 do
      b[i] +:= Basis(leftId)[i][k] * Basis(A)[k];
    end for;
  end for;

  return b;

end function;



IsLeftIdeal := function(A,L)

  //F := CoefficientRing(A);
  F := Rationals();

  m := KMatrixSpace(F, 4, 9) ! 0;
  for i := 1 to 3 do
    m[i] := Vector(Coordinates(A, L[i]));
  end for;

  ker := Kernel(m);
  dim := 4 - Dimension(ker);
  if (dim ne 3) then
    //print "The dimension is only ", dim;
    return false;
  end if;

  for i := 1 to 9 do
    for j := 1 to 3 do
      m[4] := Vector(Coordinates(A, Basis(A)[i]*L[j]));
      ker := Kernel(m);
      if (Dimension(ker) eq 0) then
        //print "basis(A)[",i,"] * L[",j,"]  is not in L";
        return false;
      end if;
    end for;
  end for;

  return true;

end function;





//  ###################################################
//  ## input: A - algebra (csa of deg 3)
//  ##        L - list of 3 elements forming a basis 
//  ##            of a minimal (3-dimensional) left ideal
//  ## output: 9x9 matrix, rows are coords of std basis of M3(Q) 
//  ##         with respect to the basis of A
//  ###################################################
SplitAlgebra := function(A,L)

  F := Rationals();

  m := KMatrixSpace(F, 4, 9) ! 0;
  for i := 1 to 3 do
    m[i] := Vector(Coordinates(A, L[i]));
  end for;

  M3 := MatrixAlgebra(F, 3);
  v := M3 ! 0;
  V := [M3 | ];
  for i := 1 to 9 do
    for j := 1 to 3 do
      m[4] := Vector(Coordinates(A, Basis(A)[i]*L[j]));
      ker := Basis(Kernel(m))[1];
      v[j] := Vector([-ker[1]/ker[4], -ker[2]/ker[4], -ker[3]/ker[4]]);
    end for;
    V[i] := Transpose(v);
  end for;

  //  splitM - matrix of transformation A -> M3
  splitM := KMatrixSpace(F, 9, 9) ! 0;
  for i := 1 to 9 do
    splitM[i] := Vector(Coordinates(M3, V[i]));
  end for;

  rSplitM := splitM^-1;

  return rSplitM;

end function;


//  construction: Lemma 6.5, Lemma 6.6 
CubicRoot := function(A, x)

  for ind := 1 to 9 do
    t := Basis(A)[ind];
    tx := t*x - x*t;
    //  if tx = 0, we need another t
    if (tx eq 0) then
      continue;
    end if;
    bool, inv_tx := IsInvertible(tx);
    if (not bool) then
      return false, tx;
    end if;
    //  if tx*x = x*tx, we need another t
    if (tx*x eq x*tx) then
      continue;
    end if;
    break;
  end for;

  y := tx * x * inv_tx;
  z := x*y - y*x;

  return true, z;

end function;


//  a - cyclic element
//  find b s.t. bab^{-1} = sigma(a)
ConjugatingElement := function(A, a)

  F := Rationals();

  poly := MinimalPolynomial(a);
  K<y> := NumberField(poly);
  roots := Roots(poly, K);

  if (roots[1][1] eq y) then
    sig_a := roots[2][1];
  else
    sig_a := roots[1][1];
  end if;
  sa := sig_a[1]*(Parent(a) ! 1) + sig_a[2]*a + sig_a[3]*a*a;

  //  find b s.t. b * a = sa * b
  lhs := KMatrixSpace(F, 9, 9) ! 0;
  rhs := KMatrixSpace(F, 9, 9) ! 0;
  
  c_a := Coordinates(A, a);
  c_sa := Coordinates(A, sa);

  //  the table of structure constants
  struct := [];
  for i := 1 to 9 do
    str := [];
    for j := 1 to 9 do
      str[j] := Coordinates(A, Basis(A)[i]*Basis(A)[j]);
    end for;
    struct[i] := str;
  end for;

  for i := 1 to 9 do
    for j := 1 to 9 do
      c := 0;
      for k := 1 to 9 do
        c +:= c_a[k]*struct[j,k,i];
      end for;
      lhs[i][j] := c;
    end for;
  end for;

  for i := 1 to 9 do
    for j := 1 to 9 do
      c := 0;
      for k := 1 to 9 do
        c +:= c_sa[k]*struct[k,j,i];
      end for;
      rhs[i][j] := c;
    end for;
  end for;

  sol := Nullspace(Transpose(lhs-rhs));

  //print Basis(sol);

  c_b := Basis(sol)[1];
  b := A ! 0;
  for k := 1 to 9 do
    b +:= c_b[k] * Basis(A)[k];
  end for;

  return b;

end function;


//  ###################################################
//  ##  returns:
//  ##    true, a, b    - if a,b are generators of A 
//  ##                    as a cyclic algebra
//  ##    false, d, 0   - ak d is a zero divisor
//  ##    false, 0, 0   - ak d is in centre of A (should be avoided!)
//  ###################################################
CyclicAlgebra := function(A, x)

  if (x in Center(A)) then 
    //print "input element in the center";
    return false, 0, 0;
  end if;

  //  whether x is a zero divisor
  if not IsInvertible(x) then
    //print "special case: noninvertible element";
    return false, x, 0;
  end if;

  //  whether x has reducible minimal polynomial
  //  -> find a zero divisor
  m_x := MinimalPolynomial(x);
  fs := Factorization(m_x);
  if (#fs gt 1) then
    //print "special case: reducible minimal polynomial";
    zd := Evaluate(fs[1][1], x);
    return false, zd, 0;
  end if;

  //  whether x is cyclic
  //  -> easier work
  K<y> := NumberField(m_x);
  roots := Roots(m_x, K);
  if (#roots eq 3) then
    //print "special case: cyclic element";
    b := ConjugatingElement(A,x);
    return true, x, b;
  end if;

  if (x*x*x in Center(A)) then
    //print "special case: cubic root";
    b := x;
  else
    bool, b := CubicRoot(A, x);
    if (not bool) then
      //  b is a zero divisor 
      //print "special case: zero divisor hit 1";
      return false, b, 0;
    end if;
  end if;
  bool, z := CubicRoot(A, b);
  if (not bool) then
    //  z is a zero divisor 
    //print "special case: zero divisor hit 2";
    return false, z, 0;
  end if;

  return true, b*z, z;

end function;








