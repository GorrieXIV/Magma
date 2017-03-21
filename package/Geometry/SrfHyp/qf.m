freeze;

/********************************************************************
This file is a compilation of the original files nrs.mag, qf2.mag,
qf3.mag,qf4.mag and qf5.mag by Tobias Beck and Josef Schicho.

Some redundant functions/intrinsics and the test intrinsics
have been removed.

The nrs.mag intrinsics have been converted to functions and
renamed with QF at the start.

The functions/intrinsics here check for solvability and
find a solution of a (non-degenerate) quadratic form over the
integers in n >= 2 variables. The intrinsics 'IsotropicVector'
are at the end of the file.

There is also functionality to work with elements in K* /K*^2
where K is the local field R or Q_p (from nrs.mag) that is
used for forms in 4 variables.
[Conversion - mch - 11/08]
*********************************************************************/

/********************************************************************/
/** ResidueClassRecord structure and functions for working with    **/
/**          K* /K*^2 where K is local field R or Q_p              **/
/********************************************************************/

// not all fields of the record are always used:
// prime: used always; for infinity prime is set to 0
// if prime = infinity, used are
//   nonsquare
// if prime = 2, used are
//   gener_2, gener_minus1, gener_5
// if prime = any odd prime, used are
//   nonsquare, withprime
ResidueClassRec := recformat<
  prime: RngIntElt, 
  nonsquare, withprime: BoolElt, 
  gener_2, gener_minus1, gener_5: BoolElt>;

// **************************************************************
// ** Tables for Norm Residue Symbol:
// **   Cassels p.43-44
// **************************************************************
// for prime = 2
// the order of representatives: 1, 5, -1, -5, 2, 10, -2, -10
NRS_2 := Matrix(IntegerRing(), 8,8,
  [1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1,-1,-1,-1,-1,
   1, 1,-1,-1, 1, 1,-1,-1,
   1, 1,-1,-1,-1,-1, 1, 1,
   1,-1, 1,-1, 1,-1, 1,-1,
   1,-1, 1,-1,-1, 1,-1, 1,
   1,-1,-1, 1, 1,-1,-1, 1,
   1,-1,-1, 1,-1, 1, 1,-1]);

// for prime = infinity
// the order of representatives: 1, -1
NRS_infinity := Matrix(IntegerRing(), 2,2,
  [1, 1,
   1,-1]);

// for odd finite prime
// -1 is a square in p-adic numbers 
//   ... (iff p is congruent to 1 modulo 4
// the order of representatives: 1, r, prime, r*prime
// (r is not congruent to a square modulo prime)
NRS_odd_prime1 := Matrix(IntegerRing(), 4,4, 
  [1, 1, 1, 1,
   1, 1,-1,-1,
   1,-1, 1,-1,
   1,-1,-1, 1]);

// norm residue symbol for odd finite prime
// -1 is not square in p-adic numbers 
NRS_odd_prime2 := Matrix(IntegerRing(), 4,4, 
  [1, 1, 1, 1,
   1, 1,-1,-1,
   1,-1,-1, 1,
   1,-1, 1,-1]);


// **************************************************************
// ** Equality
// **************************************************************
function QFEqual(a_rc, b_rc)
// compares two residue clases a_rc, b_rc for equality.

  if (a_rc`prime ne b_rc`prime) then
    return false;
  end if;

  if (a_rc`prime eq 0) then
    return (a_rc`nonsquare eq b_rc`nonsquare);
  elif (a_rc`prime eq 2) then
    return(
      (a_rc`gener_2 eq b_rc`gener_2) and
      (a_rc`gener_minus1 eq b_rc`gener_minus1) and
      (a_rc`gener_5 eq b_rc`gener_5));
  else
    return(
      (a_rc`nonsquare eq b_rc`nonsquare) and
      (a_rc`withprime eq b_rc`withprime));
  end if;
end function;


// **************************************************************
// ** '*':
// **************************************************************
function QFResMult(a_rc, b_rc)
// multiplies two residue clases a_rc and b_rc

  product := rec< ResidueClassRec | prime := a_rc`prime >;

  if (a_rc`prime eq 2) then
    product`gener_2 := a_rc`gener_2 xor b_rc`gener_2;
    product`gener_minus1 := a_rc`gener_minus1 xor b_rc`gener_minus1;
    product`gener_5 := a_rc`gener_5 xor b_rc`gener_5;
  elif (a_rc`prime eq 0) then
    product`nonsquare := a_rc`nonsquare xor b_rc`nonsquare;
  else
    product`nonsquare := a_rc`nonsquare xor b_rc`nonsquare; 
    product`withprime := a_rc`withprime xor b_rc`withprime;
  end if;

  return product;
end function;


// **************************************************************
// ** ConvertRCToIndex:
// **************************************************************
function ConvertRCToIndex(rc)
  if (rc`prime eq 0) then
    index := (rc`nonsquare) select 2 else 1;
  elif (rc`prime eq 2) then
    index := 1;
    if (rc`gener_2) then index := index + 4; end if;
    if (rc`gener_minus1) then index := index + 2; end if;
    if (rc`gener_5) then index := index + 1; end if;
  else
    index := 1;
    if (rc`nonsquare) then index := index + 1; end if;
    if (rc`withprime) then index := index + 2; end if;
  end if;

  return index;
end function;


// **************************************************************
// ** ConvertIndexToRC:
// **************************************************************
function ConvertIndexToRC(index, p)
  rc := rec<ResidueClassRec | prime := p>;

  if (p eq 0) then
    rc`nonsquare := index eq 2;
  elif (p eq 2) then
    rc`gener_2 := index gt 4;
    rc`gener_minus1 := (index mod 4) in {0,3};
    rc`gener_5 := (index mod 2) eq 0;
  else
    rc`nonsquare := (index mod 2) eq 0;
    rc`withprime := index gt 2;
  end if;

  return rc;
end function;


// **************************************************************
// ** QFRepresentative:
// **   "converse" function to QFResidueClass
// **************************************************************
function QFRepresentative(rc)
// integer representative of the residue class rc
  if rc`prime eq 0 then
    rep := (rc`nonsquare) select -1 else 1;
  elif rc`prime eq 2 then
    rep := 1;
    if (rc`gener_2) then rep := 2*rep; end if;
    if (rc`gener_minus1) then rep := -1*rep; end if;
    if (rc`gener_5) then rep := 5*rep; end if;
  else
    rep := 1;
    if (rc`nonsquare) then
      FF := FiniteField(rc`prime);
      for i:=2 to rc`prime-1 do
        if not IsSquare(FF ! i) then
          rep := i * rep;
          break i;
        end if;
      end for;
    end if;
    if (rc`withprime) then rep := rc`prime * rep; end if;
  end if;

  return rep;
end function;


// **************************************************************
// ** QFNormResidueSymbol:
// **************************************************************
function QFNormResidueSymbol(a_rc, b_rc)
// Hilbert Norm Residue Symbol  (a_rc,b_rc)_2
  if (a_rc`prime ne b_rc`prime) then
    print "ERROR";
    return 0;
  end if;

  index_a := ConvertRCToIndex(a_rc);
  index_b := ConvertRCToIndex(b_rc);

  if (a_rc`prime eq 0) then
    return NRS_infinity[index_a][index_b];
  end if;

  if (a_rc`prime eq 2) then
    return NRS_2[index_a][index_b];
  end if;

  if (a_rc`prime mod 4 eq 1) then
    return NRS_odd_prime1[index_a, index_b];
  else 
    return NRS_odd_prime2[index_a, index_b];
  end if;
end function;


// **************************************************************
// ** QFNormResidueSymbolTableFor:
// **   returns the whole line from the table belonging to rc
// **************************************************************
function QFNormResidueSymbolTableFor(rc)
  index := ConvertRCToIndex(rc);

  if (rc`prime eq 0) then
    return NRS_infinity[index];
  end if;

  if (rc`prime eq 2) then
    return NRS_2[index];
  end if;

  if (rc`prime mod 4 eq 1) then
    return NRS_odd_prime1[index];
  else 
    return NRS_odd_prime2[index];
  end if;
end function;


// **************************************************************
// ** QFResidueClass:
// **   "converse" function to QFRepresentative
// **   input: a - integer, p - prime or 0 (for infinity)
// **   output: class of a in Q*p|((Q*p)^2)
// **************************************************************
function QFResidueClass(a, p)
// residue class of integer a in Q_p*/Q_p*^2
  if (a eq 0) then
    print "non-zero input required";
    return 0;
  end if;

  if (p eq 0) then
    rc := rec<ResidueClassRec | 
      prime := 0, 
      nonsquare := (Sign(a) lt 0)>;
    return rc;
  end if;

  if ((not IsPrime(p)) or (p lt 0)) then
    print "positive prime required";
    return 0;
  end if;

  if (p eq 2) then
    rc := rec<ResidueClassRec | 
      prime := 2,
      gener_2 := false,
      gener_minus1 := false,
      gener_5 := false >;

    aux := a;
    while IsDivisibleBy(aux, 4) do
      aux := aux div 4;
    end while;
    if IsDivisibleBy(aux, 2) then
      rc`gener_2 := true;
      aux := aux div 2;
    end if;
    aux := aux mod 8;
    if (aux eq 3) then
      rc`gener_minus1 := true;
      rc`gener_5 := true;
    elif (aux eq 5) then
      rc`gener_5 := true;
    elif (aux eq 7) then
      rc`gener_minus1 := true;
    end if;

    return rc;
  end if;

  //factor_a1, factor_a2 := SquarefreeFactorization(AbsoluteValue(a));
  //new_a := Sign(a) * factor_a1;

  rc := rec<ResidueClassRec | prime := p, nonsquare := false, withprime := false>;
  v,new_a := Valuation(a,p : Check := false);
  rc`withprime := IsOdd(v);
  rc`nonsquare := (JacobiSymbol(new_a,p) eq -1);

  return rc;
end function;

// **************************************************************
// ** QFNormResidueSymbol:
// **************************************************************
//function QFNormResidueSymbol(a, b, p)
// Hilbert Norm Residue Symbol (a,b) with the given prime p
//  a_rc := QFResidueClass(a, p);
//  b_rc := QFResidueClass(b, p);
//
//  return QFNormResidueSymbol(a_rc, b_rc);
//end function;

/********************************************************************/
/********************************************************************/

/***** Function for 2 variable quadratic forms **********************/

// *************************************************************************
// ** IsotropicVector2:
// **   looks for an isotropic vector of the diagonal form
// **   output: (0 0) if the form is anisotropic
// **           (a b) - isotropic vector if the form is isotropic
// *************************************************************************
function IsotropicVector2(a1, a2)

  // solve trivial case: zero occurs on diagonal
  if (a1 eq 0) then
    return Vector([1,0]);
  elif (a2 eq 0) then
    return Vector([0,1]);
  end if;

  Is, root := IsSquare(-a2/a1);
  if Is then
    return Vector([Numerator(root), Denominator(root)]);
  else
    return Vector([0,0]); 
  end if;

end function;

/***** Functions for 3 variable quadratic forms **********************/

// *************************************************************************
// ** DiagonalQFValue:
// *************************************************************************
function DiagonalQFValue(a1, a2, a3, u)
  val := a1 * u[1]^2 + a2 * u[2]^2 + a3 * u[3]^2;
  return val;
end function;


// *************************************************************************
// ** MakeQFSquareFree:
// **   transforms fiven quadratic form a1,a2,a3 to b1,b2,b3
// **     so that b1*b2*b3 is squarefree
// **   output: coeffs of new quadratic form and
// **           the transformation matrix of the solution: 
// **             if input (a1,a2,a3) had solution (x1,x2,x3)*T then
// **             output (b1,b2,b3) has solution (x1,x2,x3)
// *************************************************************************

function MakeQFSquareFree(a1, a2, a3)
  d := GCD([a1,a2,a3]);

  b := [IntegerRing() |];
  T := [IntegerRing() |];
  b[1] := a1 div d;
  b[2] := a2 div d;
  b[3] := a3 div d;

  for i:=1 to 3 do
    b[i], T[i] := Squarefree(b[i]);
  end for;

  for i:=1 to 3 do
    i1 := 1+((i-1) mod 3);
    i2 := 1+((i) mod 3);
    i3 := 1+((i+1) mod 3);

    d := GCD(b[i1],b[i2]);
    if (d gt 1) then
      b[i1] := b[i1] div d;
      b[i2] := b[i2] div d;
      b[i3] := b[i3] * d;
      T[i1] := d * T[i1];
      T[i2] := d * T[i2];
    end if;
  end for;

  //  now if quad form (a1, a2, a3) had solution (x1 x2 x3)*T then the new
  //  form (b1, b2, b3) has solution (x1 x2 x3)

  lcm := LCM([T[1], T[2], T[3]]);
  Transf := DiagonalMatrix(
    IntegerRing(), 3, [lcm div T[1], lcm div T[2], lcm div T[3]]);

  return b[1], b[2], b[3], Transf;
end function;


// *************************************************************************
// ** TransformSolution:
// **   transforms solution of the square free quadratic form 
// **   using the transrofmation T returned by MakeQFSquareFree
// *************************************************************************
function TransformSolution(X, T)
  return X*T;
end function;


// *************************************************************************
// ** MakeSolutionPrimitive3:
// **   transforms solution of the quadratic form such that 
// **   its components are coprime (no integer divides all of them) 
// *************************************************************************
function MakeSolutionPrimitive3(v)
  if (v eq Vector([0,0,0])) then
    return v;
  end if;

  gcd := GCD(v[1], GCD(v[2], v[3]));
  if (gcd ne 1) then
    v[1] := v[1] div gcd;
    v[2] := v[2] div gcd;
    v[3] := v[3] div gcd;
  end if;

  return v;
end function;


// *************************************************************************
// ** SolubilityCertificate:
// **   input: b3 should be odd!
// **   output: r, er (linear condition for x1, x2 (mod b3))
// **           x2 = c*x1 (mod b3)
// **           or (equivalently) r = sqrt(-b1/b2) (mod b3)
// **           er = false  if no error occured
// **                true   otherwise (then r is not valid)
// *************************************************************************
function SolubilityCertificate(b1, b2, b3)
  factor_b3 := Factorization(AbsoluteValue(b3));

  r_list := [IntegerRing() |];
  m_list := [IntegerRing() |];

  len := #factor_b3;
  for i in [1..len] do
    //                           b1 + r2*b2 = 0 (mod factor_b3[i][1])
    //  => the linear condition: x2 = root*x1 (mod factor_b3[i][1])
    //  (root = sqrt(r2))
    r2 := -1 * b1 * InverseMod(b2, factor_b3[i][1]);
    Is, root := IsSquare(FiniteField(factor_b3[i][1]) ! r2);
    if (Is) then
      r_list[i] := IntegerRing() ! root;  //  for -root: other solutions
      m_list[i] := factor_b3[i][1];
    else
      // r2 is not perfect sqare mod factor_b3[i][1])
      return 0, true;
    end if;
  end for;

  r := CRT(r_list, m_list);

  return r, false;
end function;


// *************************************************************************
// ** IsotropicVector3:
// **   looks for an isotropic vector of the diagonal form
// **   output: (0 0 0) if the form is anisotropic
// **           (a b c) - isotropic vector if the form is isotropic
// *************************************************************************
function IsotropicVector3(coef1, coef2, coef3)

  // solve trivial case: zero occurs on diagonal
  if (coef1 eq 0) then
    return Vector([1,0,0]);
  elif (coef2 eq 0) then
    return Vector([0,1,0]);
  elif (coef3 eq 0) then
    return Vector([0,0,1]);
  end if;

  //  simple test of solvability
  if ((coef1 gt 0) and (coef2 gt 0) and (coef3 gt 0)) or 
     ((coef1 lt 0) and (coef2 lt 0) and (coef3 lt 0)) then 
    return Vector([0,0,0]); 
  end if;

  a1, a2, a3, T := MakeQFSquareFree(coef1, coef2, coef3);

  abs_a1 := AbsoluteValue(a1);
  abs_a2 := AbsoluteValue(a2);
  abs_a3 := AbsoluteValue(a3);

  Za4 := ResidueClassRing(4*abs_a1*abs_a2*abs_a3);

  x1_list := [IntegerRing() |];
  x2_list := [IntegerRing() |];
  x3_list := [IntegerRing() |];
  m_list := [IntegerRing() |];
  index := 0;

  //  solving first modular linear system by CRT 
  modulo1 := ((abs_a3 mod 2) eq 0) select (abs_a3 div 2) else abs_a3;
  if (modulo1 ne 1) then
    r, er := SolubilityCertificate(a1, a2, modulo1);
    if (er) then
      return Vector([0,0,0]); 
    end if;
    index := index+1;
    x1_list[index] := r;
    x2_list[index] := modulo1-1;
    x3_list[index] := 0;
    m_list[index] := modulo1;
    //  ..  r*x1 - x2 = 0 (mod modulo1)
  end if;

  //  solving second modular linear system by CRT
  modulo2 := ((abs_a1 mod 2) eq 0) select (abs_a1 div 2) else abs_a1;
  if (modulo2 ne 1) then
    r, er := SolubilityCertificate(a2, a3, modulo2);
    if (er) then 
      return Vector([0,0,0]);
    end if;
    index := index+1;
    x1_list[index] := 0;
    x2_list[index] := r;
    x3_list[index] := modulo2-1;
    m_list[index] := modulo2;
    //  ..  r*x2 - x3 = 0 (mod modulo2)
  end if;

  //  solving third modular linear system by CRT
  modulo3 := ((abs_a2 mod 2) eq 0) select (abs_a2 div 2) else abs_a2;
  if (modulo3 ne 1) then
    r, er := SolubilityCertificate(a3, a1, modulo3);
    if (er) then 
      return Vector([0,0,0]); 
    end if;
    index := index+1;
    x1_list[index] := modulo3-1;
    x2_list[index] := 0;
    x3_list[index] := r;
    m_list[index] := modulo3;
    //  ..  r*x3 - x1 = 0 (mod modulo3)
  end if;

  //  building linear system by introducing 3 new aux vars
  if (#m_list gt 0) then
    k1 := CRT(x1_list, m_list);
    k2 := CRT(x2_list, m_list);
    k3 := CRT(x3_list, m_list);
  else
    k1 := 0;
    k2 := 0;
    k3 := 0;
  end if;

  M_el := [Za4|];
  for i in [1..3*6] do
    M_el[i] := 0;
  end for;

  M_el[1] := k1;
  M_el[2] := k2;
  M_el[3] := k3;
  M_el[4] := modulo1 * modulo2 * modulo3;

  if IsOdd(a1) and IsOdd(a2) and IsOdd(a3) then
    if IsDivisibleBy(a1+a2, 4) then
      // add: x1 = x2 mod 2
      //      x3 = 0  mod 2
      M_el[7] := 1;
      M_el[8] := 1;

      M_el[15] := 1;

    elif IsDivisibleBy(a2+a3, 4) then
      // add: x2 = x3 mod 2
      //      x1 = 0  mod 2
      M_el[8] := 1;
      M_el[9] := 1;

      M_el[13] := 1;

    else
      // add: x1 = x3 mod 2
      //      x2 = 0  mod 2
      M_el[7] := 1;
      M_el[9] := 1;

      M_el[14] := 1;

    end if;

    M_el[11] := 2;
    M_el[18] := 2;

  else
    if IsEven(a1) then
      //  add: x2 = x3 mod 4
      //       x1 = s*x3 mod 2; where s in {0,1} 
      //                        and s*a1 + a2 + a3 is divisible by 8
      M_el[8] := 1;
      M_el[9] := 3;

      M_el[13] := 1;
      if IsDivisibleBy(a1+a2+a3, 8) then M_el[15] := 1; end if;

    elif IsEven(a2) then
      //  add: x1 = x3 mod 4
      //       x2 = s*x1 mod 2; where s in {0,1} 
      //                        and a1 + s*a2 + a3 is divisible by 8
      M_el[7] := 1;
      M_el[9] := 3;

      M_el[14] := 1;
      if IsDivisibleBy(a1+a2+a3, 8) then M_el[13] := 1; end if;

    else 
      //  add: x1 = x2 mod 4
      //       x3 = s*x2 mod 2; where s in {0,1} 
      //                        and a1 + a2 + s*a3 is divisible by 8
      M_el[7] := 1;
      M_el[8] := 3;

      M_el[15] := 1;
      if IsDivisibleBy(a1+a2+a3, 8) then M_el[14] := 1; end if;

    end if;

    M_el[11] := 4;
    M_el[18] := 2;
  end if;

  //  last system solving
  M := Matrix(Za4, 3, 6, M_el);
  NullSp := NullspaceOfTranspose(M);
  N := [IntegerRing()|];
  for i:=1 to 3 do      
    for j:=1 to 3 do
      N[3*i-3+j] := (NullSp.i)[j];
    end for;
  end for;

  ModSol:= Matrix(IntegerRing(),3,3,N);
//  ModSol := Submatrix(NullSp, 1,1, 3,3);

  G := Matrix(IntegerRing(), 3,3, [abs_a1,0,0, 0,abs_a2,0, 0,0,abs_a3]);
  L := Lattice(ModSol, G);
  v := ShortestVectors(L);
  shortest := Vector([v[1][1], v[1][2], v[1][3]]);
  
  if (DiagonalQFValue(a1, a2, a3, shortest) ne 0) then
    print "!!! No solution found by LLL.";
    return Vector([0,0,0]);
  end if;

  return MakeSolutionPrimitive3(TransformSolution(shortest, T));

end function;

/***** Functions for 4 variable quadratic forms **********************/

// *************************************************************************
// ** MakeSolutionPrimitive4:
// **   transforms solution of the quadratic form such that 
// **   its components are coprime (no integer divides all of them) 
// *************************************************************************
function MakeSolutionPrimitive4(v)
  if (v eq Vector([0,0,0,0])) then
    return v;
  end if;

  gcd := GCD(GCD(v[1], v[2]), GCD(v[3], v[4]));
  if (gcd ne 1) then
    v[1] := v[1] div gcd;
    v[2] := v[2] div gcd;
    v[3] := v[3] div gcd;
    v[4] := v[4] div gcd;
  end if;

  return v;
end function;

// **************************************************************
// ** IsotropicVector4:
// **   output: (0 0 0 0) if the form is anisotropic
// **           otherwise isotropic vector of the form
// **************************************************************
function IsotropicVector4(a1, a2, a3, a4)

  // solve trivial case: zero occurs on diagonal
  if (a1 eq 0) then
    return Vector([1,0,0,0]);
  elif (a2 eq 0) then
    return Vector([0,1,0,0]);
  elif (a3 eq 0) then
    return Vector([0,0,1,0]);
  elif (a4 eq 0) then
    return Vector([0,0,0,1]);
  end if;

  //  create set of all relevant primes:
  //  infinity, 2, every prime dividing a coefficient
  set_of_primes := {IntegerRing() | 0, 2};

  for i:=1 to 4 do
    if i eq 1 then a := a1; 
    elif i eq 2 then a := a2;
    elif i eq 3 then a := a3;
    else a := a4;
    end if;

    factor := Factorization(AbsoluteValue(a));
    len := #factor;
    for j:=1 to len do
      Include(~set_of_primes, factor[j][1]);
    end for;
  end for;

  //  solving...

  prime_list := [IntegerRing() |];
  nrs_a_list := [IntegerRing() |];
  nrs_b_list := [IntegerRing() |];
  a_rc_list := [];
  b_rc_list := [];

  p_power_prod := 1;
  record_num := 0;
  for prime in set_of_primes do
    if (prime ne 0) then
      record_num := record_num + 1;
    end if;

    a1_rc := QFResidueClass(a1, prime);
    a2_rc := QFResidueClass(a2, prime);
    b1_rc := QFResidueClass(-a3, prime);
    b2_rc := QFResidueClass(-a4, prime);

    nrs_a := QFNormResidueSymbol(a1_rc, a2_rc);
    nrs_b := QFNormResidueSymbol(b1_rc, b2_rc);

    minus1_rc := QFResidueClass(-1, prime);

    a_rc := QFResMult(minus1_rc, QFResMult(a1_rc, a2_rc));
    b_rc := QFResMult(minus1_rc, QFResMult(b1_rc, b2_rc));

    if ((nrs_a ne nrs_b) and QFEqual(a_rc, b_rc)) then
      //  there is apparently no t_rc such that 
      //    NRS(t_rc, a_rc) = a_rc  and
      //    NRS(t_rc, b_rc) = b_rc
      return Vector([0,0,0,0]);
    end if;

    if (prime ne 0) then
      prime_list[record_num] := prime;
      nrs_a_list[record_num] := nrs_a;
      nrs_b_list[record_num] := nrs_b;
      a_rc_list[record_num] := a_rc;
      b_rc_list[record_num] := b_rc;
    end if;

    a_rc_line := QFNormResidueSymbolTableFor(a_rc);
    b_rc_line := QFNormResidueSymbolTableFor(b_rc);

    length := OverDimension(a_rc_line);
    i := 0;
    found := false;
    while ((i lt length) and not found) do
      i := i+1;
      found := ((a_rc_line[i] eq nrs_a) and (b_rc_line[i] eq nrs_b));
    end while;

    t_rc := ConvertIndexToRC(i, prime);

    if (prime eq 0) then
      if (t_rc`nonsquare) then
         p_power_prod := -1 * p_power_prod;
      end if;
    elif (prime eq 2) then
      if (t_rc`gener_2) then
        p_power_prod := p_power_prod * 2;
      end if;
    else
      if (t_rc`withprime) then
        p_power_prod := p_power_prod * prime;
      end if;
    end if;
  end for;

  //  t should be of the form (-)p0 * product_of_some_primes_dividing_coeffs
  //  where p0 is a (special) prime.
  //  (-)product_of... is computed already
  //  suitable p0 is looked for by searching all primes
  found := false;
  p_zero := 0;
  while not found do
    p_zero := NextPrime(p_zero);
    t := p_zero * p_power_prod;
    for i := 1 to record_num do
      t_rc := QFResidueClass(t, prime_list[i]);
      found := true;
      if (QFNormResidueSymbol(t_rc, a_rc_list[i]) ne nrs_a_list[i]) or
         (QFNormResidueSymbol(t_rc, b_rc_list[i]) ne nrs_b_list[i]) then
        found := false;
        break i;
      end if;
    end for;
  end while;

  //  solve ternary forms and combine the solutions
  a_sol := IsotropicVector3(a1, a2, -t);
  b_sol := IsotropicVector3(a3, a4, t);

  if ((a_sol[3] eq 0) and (b_sol[3] eq 0)) then
    solution := Vector([a_sol[1], a_sol[2], b_sol[1], b_sol[2]]);
  else 
    solution := Vector([a_sol[1]*b_sol[3], a_sol[2]*b_sol[3],
                        b_sol[1]*a_sol[3], b_sol[2]*a_sol[3]]);
  end if;

  return MakeSolutionPrimitive4(solution);

end function;

/***** Function for 5 variable quadratic forms **********************/

// **************************************************************
// ** IsotropicVector5:
// **   output: (0 0 0 0 0) if the form is anisotropic
// **           otherwise isotropic vector of the form
// **************************************************************
function IsotropicVector5(a1, a2, a3, a4, a5)

  // solve trivial case: zero coefficient occurs 
  if (a1 eq 0) then
    return Vector([1,0,0,0,0]);
  elif (a2 eq 0) then
    return Vector([0,1,0,0,0]);
  elif (a3 eq 0) then
    return Vector([0,0,1,0,0]);
  elif (a4 eq 0) then
    return Vector([0,0,0,1,0]);
  elif (a5 eq 0) then
    return Vector([0,0,0,0,1]);
  end if;

  //  test solvability:
  //  is equivalent to the solvability over reals
  if ((a1 gt 0) and (a2 gt 0) and (a3 gt 0) and (a4 gt 0) and (a5 gt 0)) or 
     ((a1 lt 0) and (a2 lt 0) and (a3 lt 0) and (a4 lt 0) and (a5 lt 0)) then 
    return Vector([0,0,0,0,0]); 
  end if;

  //  find t such that
  //    f1(X) = a1*x1^2 + a2*x2^2 - t*u^2 is isotropic and
  //    f2(X) = a3*x3^2 + a4*x4^2 + a5*x5^2 + t*v^2 is isotropic

  //  if t = a1*b1^2 + a2*b2^2 then f1 is isotropic ...
  //  generate all numbers representable by a1*x1^2 + a2*x2^2 and test 
  //  if f2 with the generated t is isoptropic 

  solution := Vector([0,0,0,0,0]);
  sum := 1;
  found := false;

  while (not found) do
    for b1 := 0 to sum do
      //print ".";
      b2 := sum - b1;
      t := a1*b1^2 + a2*b2^2;

      if (t ne 0) then
        v := IsotropicVector4(a3,a4,a5,t);
        if (not IsZero(v)) then
          // construct the solution
          solution := Vector([b1*v[4], b2*v[4], v[1], v[2], v[3]]);
          found := true;
          break b1;
        end if;
      else
        solution := Vector([b1, b2, 0, 0, 0]);
        found := true;
        break b1;
      end if;
    end for;

    sum := sum+1;
  end while;

  return solution;

end function;

/**************** Main IsotropicVector Intrinsics ******************/
/*******************************************************************/

// **************************************************************
// ** IsotropicVector:
// **   output: zero vector if the form is anisotropic
// **           otherwise isotropic vector of the form
// **************************************************************
intrinsic IsotropicVector(a::ModTupRngElt) -> ModTupRngElt
{ An isotropic vector of the quadratic form }

  length := Ncols(a);
  require (length ge 2): "Too short vector.";
  if (length eq 2) then return IsotropicVector2(a[1], a[2]);
  elif (length eq 3) then return IsotropicVector3(a[1], a[2], a[3]);
  elif (length eq 4) then return IsotropicVector4(a[1], a[2], a[3], a[4]);
  elif (length eq 5) then return IsotropicVector5(a[1], a[2], a[3], a[4], a[5]);
  end if;

  V := RSpace(IntegerRing(), length);
  solution := V ! 0;

  // solve trivial case: zero coefficient occures 
  for i:=1 to length do
    if (a[i] eq 0) then
      solution[i] := 1;
      return solution;
    end if;
  end for;

  //  test solvability:
  //  is equivalent to the solvability over reals
  sign := Sign(a[3]);
  for i:=4 to length do
    if (Sign(a[i]) ne sign) then
      sign := 0;
      break i;
    end if;
  end for;

  if (sign ne 0) then
    if (Sign(a[1]) eq sign) and (Sign(a[2]) eq sign) then 
      return solution;
    end if; 
  end if;

  //  find t such that
  //    f1(X) = a1*x1^2 + a2*x2^2 - t*u^2 is isotropic and
  //    f2(X) = a3*x3^2 + .. + a_k*x_k^2 + t*v^2 is isotropic

  //  if t = a1*b1^2 + a2*b2^2 then f1 is isotropic 
  //  f2 is isotropic if it is isotropic over reals ...
  //  generate numbers representable by a1*x1^2 + a2*x2^2 and 
  //  test posibly test if the signs in f2 are not all the same 

  b1 := 0;
  b2 := 0;

  sum := 1;
  found := false;

  while (not found) do
    b1 := -1;
    while not found and (b1 le sum) do
      b1 := b1+1;
      b2 := sum - b1;
      t := a[1]*b1^2 + a[2]*b2^2;

      if (sign eq 0) or (Sign(t) ne sign) then
        found := true;
      end if;
    end while;

    sum := sum+1;
  end while;

  if (t eq 0) then
    solution[1] := b1;
    solution[2] := b2;
  else
    if (length eq 6) then
      v := IsotropicVector5(a[3], a[4], a[5], a[6], t);
    else
      b := RSpace(IntegerRing(), length-1) ! 0;
      for i:=3 to length do
        b[i-2] := a[i];
      end for;
      b[length-1] := t;

      v := IsotropicVector(b);
    end if;
    solution[1] := b1 * v[length-1];
    solution[2] := b2 * v[length-1];
    for i:=3 to length do
      solution[i] := v[i-2];
    end for;
  end if;

  return solution;
end intrinsic;

// *************************************************************************
// ** IsotropicVector:
// **   output: zero vector if the form is anisotropic
// **           otherwise isotropic vector of the form
// *************************************************************************
intrinsic IsotropicVector(QF_M::AlgMatElt) -> ModTupRngElt
{ An isotropic vector of the quadratic form QF_M }

  require IsSymmetric(QF_M): "Symmetric matrix required.";
  n := NumberOfRows(QF_M);
  require (n ge 2): "At least 2x2 matrix required.";

  QF_M1, T, rank := OrthogonalizeGram(QF_M);

  if (n eq 2) then
    return IsotropicVector2(QF_M1[1][1], QF_M1[2][2]) * T;
  elif (n eq 3) then
    return IsotropicVector3(QF_M1[1][1], QF_M1[2][2], QF_M1[3][3]) * T;
  elif (n eq 4) then
    return IsotropicVector4(QF_M1[1][1], QF_M1[2][2], QF_M1[3][3], QF_M1[4][4]) * T;
  elif (n eq 5) then
    return IsotropicVector5(QF_M1[1][1], QF_M1[2][2], QF_M1[3][3], QF_M1[4][4], QF_M1[5][5]) * T;
  else
    a := RSpace(IntegerRing(), n) ! 0;
    for i:=1 to n do
      a[i] := QF_M1[i][i];
    end for;
  return IsotropicVector(a) * T;
  end if;
end intrinsic; 
