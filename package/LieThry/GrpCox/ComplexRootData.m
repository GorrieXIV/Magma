freeze;
/*=============================================================
  Don Taylor

  14 February 2003
  8 September 2010

  $Id: ComplexRootData.m 48480 2014-09-28 02:09:52Z donnelly $
 
===============================================================
 This file defines complex root data for all finite irreducible
 complex reflection groups.  The root data are constructed from
 basic root matrices.  The groups themselves can be constructed
 from the root matrices using the intrinsic PseudoReflectionGroup,
 defined in reflections.m.

 Intrinsics defined in this file:
  BasicCodegrees
  BasicDegrees
  CohenCoxeterName
  ComplexCartanMatrix
  ComplexRootDatum
  ComplexRootMatrices
  HermitianCartanMatrix
  ShephardToddNumber
 
 In all cases the matrix entries belong to a maximal order
 of the field of definition of the complex reflection group.
 By default the base field of the reflection group is cyclotomic
 and in some cases this is strictly larger than the field of
 definition.  To ensure that the bnase field equals the field
 of definition set NumFld := true. 
 
 The intrinsics generally have two signatures:
   X( n )       for the primitive groups
   X( m, p, n ) for the imprimitive groups
===============================================================*/

// Basic root matrices
// -------------------
intrinsic ComplexRootMatrices( k::RngIntElt : NumFld := false ) -> AlgMatElt, AlgMatElt, AlgMatElt, RngElt, RngIntElt
{ Basic root and coroot matrices for the primitive Shephard and Todd group G_k.
  This intrinsic also returns an invariant hermitian form, a generator
  for the group of roots of unity of the ring of definition, and its order}

  // The Cartan matrix is A*Transpose(B)
  
  requirerange k, 4, 37;
  if NumFld then
    P := PolynomialRing(Rationals()); x := P.1;
  end if;

/*
  Give an explicit generator for the roots of unity in the field of
  definition of a reflection group in order to speed up the calculation
  of root data.
*/

  // for 12, 23, 24, 28, 30, 35, 36, 37
  gen := -1;
  ord := 2;
  
  case k:

// Rank 2 groups
// Tetrahedral type
   when 4: // L2
     if NumFld then
       F<omega> := NumberField(x^2+x+1);
     else
       F := CyclotomicField(3); omega := F.1;
     end if;
     gen := -omega; ord := 6;
     A := IdentityMatrix(F,2);
     B := Matrix(F,2,2,[1-omega,-omega^2, omega^2,1-omega]);
     J := Matrix(F,2,2,[3,-2*omega-1, 2*omega+1, 3]);
/*
     B := Matrix(F,2,2,[1-omega,-omega, 1,1-omega]);
     J := Matrix(F,2,2,[3,omega+2, -omega+1, 3]);
*/

   when 5:
     if NumFld then
       F<omega> := NumberField(x^2+x+1);
     else
       F := CyclotomicField(3); omega := F.1;
     end if;
     gen := -omega; ord := 6;
     A := IdentityMatrix(F,2);
     B := Matrix(F,2,2,[1-omega,2*omega+2, omega^2,1-omega]);
     J := Matrix(F,2,2,[3,-4*omega-2, 4*omega+2,6]);
/*
     B := Matrix(F,2,2,[1-omega,-2*omega, 1,1-omega]);
     J := Matrix(F,2,2,[3,2*omega+4, -2*omega+2,6]);
*/

   when 6:
     if NumFld then
       F<i,omega> := NumberField([x^2+1,x^2+x+1] : Abs);
     else
       F := CyclotomicField(12); z := F.1;
       i := z^3;
       omega := z^4;
     end if;
     gen := -i*omega; ord := 12;
     A := IdentityMatrix(F,2);
     B := Matrix(F,2,2,[2,i+2*omega+1, omega^2,1-omega]);
     J := Matrix(F,2,2,[2,-i-2*omega-1, i+2*omega+1,-2*i*omega-i+3]);
/*
     B := Matrix(F,2,2,[2,1-omega+i*omega^2, 1,1-omega]);
     J := Matrix(F,2,2,[2,(1-i)*omega+2, i*omega^2-omega+1,-2*i*omega-i+3]);
*/

   when 7:
     if NumFld then
       F<i,omega> := NumberField([x^2+1,x^2+x+1] : Abs);
     else
       F := CyclotomicField(12); z := F.1;
       i := z^3;
       omega := z^4;
     end if;
     gen := -i*omega; ord := 12;
     A := Matrix(F,3,2,[i*omega + 2*i + omega, -i*omega - i,
                        i*omega - i - omega - 1, -i*omega + i,
                        1, 0]);
     B := Matrix(F,3,2,[-i, -i*omega - i - omega - 1,
                        0, -i, -omega + 1, -i*omega - i - omega + 1]);
     J := Matrix(F,2,2,[3,-2*i*omega-i+3, -2*i*omega-i+3,-4*i*omega-2*i+6]);
/*
     A := Matrix(F,3,2,[1,0, 0,1, -i*omega^2+omega-1,-omega+1 ]);
     B := Matrix(F,3,2,[-omega+1,i*omega^2-omega+1, 1,2, 0,1]);
     J := Matrix(F,2,2,[3,-2*i*omega-i+3, -2*i*omega-i+3,-4*i*omega-2*i+6]);
*/

// Octahedral type
   when 8:
     if NumFld then
       F<i> := NumberField(x^2+1);
     else
       F := CyclotomicField(4); i := F.1;
     end if;
     gen := i; ord := 4;
     A := IdentityMatrix(F,2);
     B := Matrix(F,2,2,[1-i,i, -1,1-i]);
     J := Matrix(F,2,2,[2,-i-1, i-1,2]);
/*
     B := Matrix(F,2,2,[1-i,-i, 1,1-i]);
     J := Matrix(F,2,2,[2,i+1, -i+1,2]);
*/

   when 9:
     if NumFld then
       F<i,a> := NumberField([x^2+1,x^2-2] : Abs);
     else
       F := CyclotomicField(8); z := F.1;
       i := z^2;
       a := z + z^7;
     end if;
     gen := (1-i)/a; ord := 8;
     A := IdentityMatrix(F,2);
     B := Matrix(F,2,2,[2,-i*(a+1), -gen,1+i]);
     J := Matrix(F,2,2,[2,i*(a+1), -i*(a+1),a+2]);
/*
     B := Matrix(F,2,2,[2,1+i+z8, 1,1+i]) where z8 is (1+i)/a;
     J := Matrix(F,2,2,[2,gen+1-i, z8+1+i,a+2]) where y8 is (1-i)/a where z8 is (1+i)/a;
*/

   when 10:
     if NumFld then
       F<i,omega> := NumberField([x^2+1,x^2+x+1] : Abs);
     else
       F := CyclotomicField(12); z := F.1;
       i := z^3;
       omega := z^4;
     end if;
     gen := -i*omega; ord := 12;
     A := IdentityMatrix(F,2);
     B := Matrix(F,2,2,[1+i,omega*i-omega^2, omega^2,1-omega]);
     J := Matrix(F,2,2,[2,i-2*omega-1, -i+2*omega+1,2*i*omega+i+3]);
/*
     B := Matrix(F,2,2,[1-omega,-i-omega, 1,1-i]);
     J := Matrix(F,2,2,[3,-i*omega+i+omega+2, -i*omega-2*i-omega+1,-2*i*omega-i+3]);
*/

   when 11:
     if NumFld then
       F<i,omega,a> := NumberField([x^2+1,x^2+x+1,x^2-2] : Abs);
     else
       F := CyclotomicField(24); z := F.1;
       i := z^6;
       omega := z^8;
       a := z^3 + z^21;
     end if;
     y8 := (1-i)/a;
     gen := -y8*omega^2; ord := 24;
     A := Matrix(F,3,2,[1,0,  y8+1-i,-1, 
           -omega*y8+i*omega+i*a+i-omega,i*omega^2+omega]);
     B := Matrix(F,3,2,[i+1,-y8^3+i+1, i,-y8^3+i-1, -omega*y8+y8^3,
                 -omega*y8+y8^3-omega-i-1]);
     J := Matrix(F,2,2,[2,a+2, a+2,2*a+4]);
     // y8^3 = -z8
/*
     A := Matrix(F,3,2,[1,0, 0,1, (y8-i)*omega^2-omega,-y8*omega^2 ]) where y8 is (1-i)/a;
     B := Matrix(F,3,2,[i+1,-y8^3+i+1, 1,2, 1,y8^3*omega+y8+1]) where y8 is (1-i)/a;
     J := Matrix(F,2,2,[2,a+2, a+2,2*a+4]);
*/

   when 12:
     if NumFld then
       F<b> := NumberField(x^2+2);
     else
       F := CyclotomicField(8); z := F.1;
       b := z + z^3;
     end if;
     A := Matrix(F,3,2,[1,0, 0,1, -b-1,-b]);
     B := Matrix(F,3,2,[2,b-1, -b-1,2, b,-1]);
     J := Matrix(F,2,2,[2,-b-1, b-1,2]);
/*
     A := Matrix(F,3,2,[1,0, 0,1, -b,-b+1]);
     B := Matrix(F,3,2,[2,b-1, -b-1,2, 1,b]);
     J := Matrix(F,2,2,[2,-b-1, b-1,2]);
*/
   when 13:
     if NumFld then
       F<i,a> := NumberField([x^2+1,x^2-2] : Abs);
     else
       F := CyclotomicField(8); z := F.1;
       i := z^2;
       a := z + z^7;
     end if;
     gen := (1-i)/a; ord := 8;
     A := Matrix(F,3,2,[1,0, gen^3-i-1,1, (a+1)*(i+1),gen^3-i-1]);
     B := Matrix(F,3,2,[2,a+2, i,-gen+i+1, gen+i-1,i-1]);
     J := Matrix(F,2,2,[2,a+2, a+2,2*a+4]);
/*     // y8^3 = -z8
     A := Matrix(F,3,2,[1,0, 0,1, -z8-1-i,1]) where z8 is (1+i)/a;
     B := Matrix(F,3,2,[2,a+2, 1,2, i,-y8+1+i]) where y8 is (1-i)/a;
     J := Matrix(F,2,2,[2,a+2, a+2,2*a+4]);
*/    
   when 14:
     if NumFld then
     F<b,omega> := NumberField([x^2+2,x^2+x+1] : Abs);
     else
       F := CyclotomicField(24); z := F.1;
       b := z^3 + z^9;
       omega := z^8;
     end if;
     gen := -omega^2; ord := 6;
     A := IdentityMatrix(F,2);
     B := Matrix(F,2,2,[1-omega,-omega^2, b-2*omega-1,2]);
     J := Matrix(F,2,2,[3,-2*omega-1, 2*omega+1,-4*b*omega-2*b+6]);
/*
     A := IdentityMatrix(F,2);
     B := Matrix(F,2,2,[1-omega,1-omega+b*omega^2, 1,2]);
     J := Matrix(F,2,2,[3,-2*b*omega-b+3, -2*b*omega-b+3,-4*b*omega-2*b+6]);
*/

   when 15:
     if NumFld then
       F<i,omega,a> := NumberField([x^2+1,x^2+x+1,x^2-2] : Abs);
     else
       F := CyclotomicField(24); z := F.1;
       i := z^6;
       omega := z^8;
       a := z^3 + z^21;
     end if;
     y8 := (1-i)/a;
     gen := -y8*omega^2; ord := 24;
     A := Matrix(F,3,2,[1,0, y8-i-omega^2,-y8, i*(a+2),-i*(a+1)]);
     B := Matrix(F,3,2,[2,a+2, omega^2,-omega*y8+omega^2-a, i*(a-1),i*a]);
     J := Matrix(F,2,2,[2,a+2, a+2,2*a+4]);
/*
     A := Matrix(F,3,2,[1,0, 0,1, (y8-i)*omega^2-omega,-y8*omega^2]) where y8 is (1-i)/a;
     B := Matrix(F,3,2,[2,a+2, 1,2, 1,y8^3*omega+y8+1]) where y8 is (1-i)/a;
     J := Matrix(F,2,2,[2,a+2, a+2,2*a+4]);
*/

// Icosahedral type
   when 16:
     if NumFld then
       F<z5> := NumberField(x^4+x^3+x^2+x+1);
     else
       F := CyclotomicField(5); z5 := F.1;
     end if;
     gen := -z5; ord := 10;
     A := IdentityMatrix(F,2);
     B := Matrix(F,2,2,[1-z5,-1, z5,1-z5]);
     J := Matrix(F,2,2,[5,z5^3+2*z5^2+3*z5-1,-z5^3-2*z5^2-3*z5-4,5]);
//     B := Matrix(F,2,2,[1-z5,-z5, 1,1-z5]);
//     J := Matrix(F,2,2,[5,z5^3+2*z5^2+3*z5+4,-z5^3-2*z5^2-3*z5+1,5]);

   when 17:
     if NumFld then
       F<i,z5> := NumberField([x^2+1,x^4+x^3+x^2+x+1] : Abs);
     else
       F := CyclotomicField(20); z := F.1;
       i := z^5;
       z5 := z^4;
     end if;
     gen := i*z5^-1; ord := 20;
     A := IdentityMatrix(F,2);
     B := Matrix(F,2,2,[2,-i+z5^2-z5^3, z5^3,1-z5]);
     J := Matrix(F,2,2,[2,i+z5^3-z5^2, -i-z5^3+z5^2, -i*z5^3+i*z5^2+z5^3+z5^2+3]);
/*
     B := Matrix(F,2,2,[2,1-z5-i*z5^3, 1,1-z5]);
     J := Matrix(F,2,2,[2,i*z5^2+z5^3+z5^2+z5+2,
                -i*z5^3-z5+1,-i*z5^3+i*z5^2+z5^3+z5^2+3]);
*/
   when 18:
     if NumFld then
       F<omega,z5> := NumberField([x^2+x+1,x^4+x^3+x^2+x+1] : Abs);
     else
       F := CyclotomicField(15); z := F.1;
       omega := z^5;
       z5 := z^3;
     end if;
     gen := -z5^2*omega^2; ord := 30;
     A := IdentityMatrix(F,2);
     B := Matrix(F,2,2,[1-omega,-omega*z5^2-z5^3, z5^3,1-z5]);
     J := Matrix(F,2,2,[
      3, omega*z5^3+omega*z5^2+2*z5^3-z5^2,
     -omega*z5^3-omega*z5^2-2*z5^3+z5^2, -omega*z5^3-omega*z5^2-2*omega*z5-omega+z5^3+z5^2-z5+4]);
/*
     B := Matrix(F,2,2,[1-omega,-omega-z5, 1,1-z5]);
     J := Matrix(F,2,2,[3,-omega*z5^3-omega*z5^2-omega*z5+z5^3+z5^2+z5+3,
            -omega*z5-omega-2*z5+1,-omega*z5^3-omega*z5^2-2*omega*z5-omega+z5^3+z5^2-z5+4]);
*/

   when 19:
     if NumFld then
       F<i,omega,z5> := NumberField([x^2+1,x^2+x+1,x^4+x^3+x^2+x+1] : Abs);
     else
       F := CyclotomicField(60); z := F.1;
       i := z^15;
       omega := z^20;
       z5 := z^12;
     end if;
     gen := -i*omega^2*z5^3; ord := 60;

     A := Matrix(F,3,2,[1,0, 0, omega,
      -i-omega*z5^3-omega*z5^2-omega*z5-omega-z5^3,
       omega*z5^3+omega*z5^2+omega*z5+omega]);
     B := Matrix(F,3,2,[1-z5,-omega-z5, omega^2,omega^2-1,
       i, -i*omega*z5^3-i*omega*z5^2-i*omega*z5-i*omega-i*z5^3-i*z5^2-i*z5+omega*z5+z5]);

     J := Matrix(F,2,2,[5,-omega*z5^3-2*omega*z5^2-3*omega*z5+omega+5,
        -omega*z5^3-2*omega*z5^2-3*omega*z5-4*omega-z5^3-2*z5^2-3*z5+1,
        -2*omega*z5^3-4*omega*z5^2-6*omega*z5-3*omega-z5^3-2*z5^2-3*z5+6]);
/*
     A := Matrix(F,3,2,[1,0, 0,1,
       -i*omega*z5^3-i*omega*z5^2-i*omega*z5-i*omega-i*z5^3+1,
        i*omega*z5^3+i*omega*z5^2+i*omega*z5+i*omega]);
     B := Matrix(F,3,2,[-z5+1,-omega-z5, 1,-omega+1, 1,
        -i*omega*z5-i*z5-omega*z5^3-omega*z5^2-omega*z5-omega-z5^3-z5^2-z5]);
     J := Matrix(F,2,2,[5,-omega*z5^3-2*omega*z5^2-3*omega*z5+omega+5,
        -omega*z5^3-2*omega*z5^2-3*omega*z5-4*omega-z5^3-2*z5^2-3*z5+1,
        -2*omega*z5^3-4*omega*z5^2-6*omega*z5-3*omega-z5^3-2*z5^2-3*z5+6]);

[
    (1 0),
    (    0 omega),
    (-i - omega*z5^3 - omega*z5^2 - omega*z5 - omega - z5^3 omega*z5^3 + 
        omega*z5^2 + omega*z5 + omega)
]
> [S[p] : p in seq];
[
    (    -z5 + 1 -omega - z5),
    (-omega - 1 -omega - 2),
    (i -i*omega*z5^3 - i*omega*z5^2 - i*omega*z5 - i*omega - i*z5^3 - i*z5^2 - 
        i*z5 + omega*z5 + z5)
]
*/
   when 20:
     if NumFld then
       F<omega,tau> := NumberField([x^2+x+1,x^2-x-1] : Abs);
     else
       F := CyclotomicField(15); z := F.1;
       omega := z^5;
       tau := 1+z^3+z^12;
     end if;
     gen := -omega; ord := 6;
     A := IdentityMatrix(F,2);
     B := Matrix(F,2,2,[1-omega,omega^2*(tau-2), omega^2,1-omega]);
     J := Matrix(F,2,2,[3,(2*omega+1)*(tau-2), -(2*omega+1)*(tau-2), 6-3*tau]);
/*           
     B := Matrix(F,2,2,[1-omega,omega*(tau-2), 1,1-omega]);
     J := Matrix(F,2,2,[3,-omega*tau+2*omega-2*tau+4,
           omega*tau-2*omega-tau+2,-3*tau + 6]);
*/

   when 21:
     if NumFld then
       F<i,omega,tau> := NumberField([x^2+1,x^2+x+1,x^2-x-1] : Abs);
     else
       F := CyclotomicField(60); z := F.1;
       i := z^15;
       omega := z^20;
       tau := 1+z^12+z^48;
     end if;
     gen := -i*omega; ord := 12;
     A := IdentityMatrix(F,2);
     B := Matrix(F,2,2,[2,-i*tau+2*omega+1, omega^2,1-omega]);
     J := Matrix(F,2,2,[2,i*tau-2*omega-1, -i*tau+2*omega+1, (2*omega+1)*i*tau+3]);
/*
     B := Matrix(F,2,2,[2,1-omega-i*omega^2*tau, 1,1-omega]);
     J := Matrix(F,2,2,[2,i*omega*tau+omega+2,
           i*omega*tau+i*tau-omega+1,2*i*omega*tau+i*tau+3]);
*/
   when 22:
     if NumFld then
       F<i,tau> := NumberField([x^2+1,x^2-x-1] : Abs);
     else
       F := CyclotomicField(20); z := F.1;
       i := z^5;
       tau := 1+z^4+z^16;
     end if;
     gen := i; ord := 4;
     A := Matrix(F,3,2,[1,0, 0,-1, i+tau-2, (1-i)*(tau-1)]);
     B := Matrix(F,3,2,[2,-i+tau-1, -i-tau+1,-2, -i-1,i]);
     J := Matrix(F,2,2,[2,i+tau-1, -i+tau-1,2]);
/*
     A := Matrix(F,3,2,[1,0, 0,1, i+tau-2, (1-i)*(tau-1)]);
     B := Matrix(F,3,2,[2,-i+tau-1, i+tau-1,2, -i-1,i]);
     J := Matrix(F,2,2,[2,i+tau-1, -i+tau-1,2]);
*/

// Rank 3 groups
   when 23:  // H3
     if NumFld then
       F<tau> := NumberField(x^2-x-1);
     else
       F := CyclotomicField(5); z := F.1;
       tau := 1+z+z^4;
     end if;
     A := IdentityMatrix(F,3);
     B := Matrix(F,3,3,[
        2, -tau,  0,
     -tau,    2, -1,
        0,   -1,  2]);
     J := B;

   when 24:  // J3(4)
     if NumFld then
       F<lambda> := NumberField( x^2+x+2 );
     else
       F := CyclotomicField(7); z := F.1;
       lambda := -1-z-z^2-z^4;
     end if;
     A := IdentityMatrix(F,3);
     B := Matrix(F,3,3,[
            2,    -1, 1+lambda,
           -1,     2,  -1,
         -lambda, -1,   2]);
     J := Transpose(B);
/*
     A := Matrix(F,3,3,[
             1,  0,  0,
             0,  1,  0,
      lambda+1,  0,  1]);
     B := Matrix(F,3,3,[
             2,  -1, -1-lambda,
            -1,   2,    lambda,
       -lambda,  -1,         0]);
     J := Matrix(3,3,[
             2,     -1,    lambda,
            -1,      2, -lambda-1,
     -lambda-1, lambda,         2]);

     A := IdentityMatrix(F,3);
     B := Matrix(F,3,3,[
              2,        -1, -1-lambda,
             -1,         2,    lambda,
         lambda, -1-lambda,         2]);
     J := Transpose(B);
*/
   when 25:  // L3
     if NumFld then
       F<omega> := NumberField(x^2+x+1);
     else
       F := CyclotomicField(3); omega := F.1;
     end if;
     gen := -omega; ord := 6;
     A := IdentityMatrix(F,3);
     B := Matrix(F,3,3,[
        1-omega, -omega^2,       0,
        omega^2,  1-omega, omega^2,
              0,  -omega^2, 1-omega]);
     J := Matrix(F,3,3,[
           3, -2*omega-1,       0,
    2*omega+1,         3, 2*omega+1,
           0, -2*omega-1,       3]);

   when 26:  // M3
     if NumFld then
       F<omega> := NumberField(x^2+x+1);
     else
       F := CyclotomicField(3); omega := F.1;
     end if;
     gen := -omega; ord := 6;
     A := IdentityMatrix(F,3);
     B := Matrix(F,3,3,[
         1-omega, omega^2,   0,
        -omega^2, 1-omega, -1+omega,
               0,      -1,   2]);
     J := Matrix(F,3,3,[
             3,  2*omega+1,    0,
    -2*omega-1,          3,   -3,
             0,         -3,    6]);

   when 27:  // J3(5)
     if NumFld then
       F<omega,tau> := NumberField([x^2+x+1,x^2-x-1] : Abs);
     else
       F := CyclotomicField(15); z := F.1;
       omega := z^5;
       tau := 1+z^3+z^12;
     end if;
     gen := -omega; ord := 6;
     A := IdentityMatrix(F,3);
     B := Matrix(F,3,3,[
              2,   -1, -omega^2*tau,
             -1,    2,            -1,
     -omega*tau,   -1,             2]);
     J := Transpose(B);
   
/*
    A := Matrix(F,3,3,[
        1,       0,       0,
        0,       0,  -omega,
        0, omega^2,       0]);
     B := Matrix(F,3,3,[
            2,    -tau,     omega^2,
           -1,   -omega, -2*omega^2,
   -omega*tau,  2*omega,    omega^2]);
      J := Matrix(F,3,3,[
            2,  -tau,   omega,
         -tau,     2, omega^2,
      omega^2, omega,       2]);
   
     A := IdentityMatrix(F,3);
     B := Matrix(F,3,3,[
              2,   -tau, omega^2,
           -tau,      2,   omega,
          omega, omega^2,      2]);
     J := Transpose(B);
     
     A := IdentityMatrix(F,3);
     B := Matrix(F,3,3,[
              2,  -tau,  -omega^2,
           -tau,     2,   -omega,
         -omega, -omega^2,      2]);
     J := Transpose(B);
*/

// Rank 4 groups
   when 28:  // F4
     F := Rationals();
     A := IdentityMatrix(F,4);
     B := Matrix(F,4,4,[
        2, -1,  0,  0,
       -1,  2, -1,  0,
        0, -2,  2, -1,
        0,  0, -1,  2]);
     J := Matrix(F,4,4,[
        4, -2,  0,  0,
       -2,  4, -2,  0,
        0, -2,  2, -1,
        0,  0, -1,  2]);

   when 29:  // N4
     if NumFld then
       F<i> := NumberField(x^2+1);
     else
       F := CyclotomicField(4); i := F.1;
     end if;
     gen := i; ord := 4;
     A := IdentityMatrix(F,4);
     B := Matrix(F,4,4,[
        2,  -1,  -i,   0,
       -1,   2,  -1,   0,
        i,  -1,   2,  -1,
        0,   0,  -1,   2]);
     J := Transpose(B);
/*
     A := IdentityMatrix(F,4);
     B := Matrix(F,4,4,[
        2,  -1,  -i,   0,
       -1,   2,  -1,   0,
        i,  -1,   2,  -i,
        0,   0,   i,   2]);
     J := Transpose(B);

     A := IdentityMatrix(F,4);
     B := Matrix(F,4,4,[
        2,     -1,  -i + 1,      0,
       -1,      2,       i,      0,
    i + 1,     -i,       2,     -1,
        0,      0,      -1,      2]);
     J := Transpose(B);
*/

   when 30:  // H4
     if NumFld then
       F<tau> := NumberField(x^2-x-1);
     else
       F := CyclotomicField(5); z := F.1;
       tau := 1+z+z^4;
     end if;
     A := IdentityMatrix(F,4);
     B := Matrix(F,4,4,[
        2, -tau,  0,  0,
     -tau,    2, -1,  0,
        0,   -1,  2, -1,
        0,    0, -1,  2]);
     J := B;

   when 31:  // O4
     if NumFld then
       F<i> := NumberField(x^2+1);
     else
       F := CyclotomicField(4); i := F.1;
     end if;
     gen := i; ord := 4;
     A := Matrix(F,5,4,[1,0,0,0, 0,1,0,0, 0,0,i,0, 0,0,0,i, -1,0,i,0]);
     B := Matrix(F,5,4,[
        2,   -1, -i + 1,    0,
       -1,    2,      i,    0,
   -i + 1,   -1,   -2*i,    i,
        0,    0,      i, -2*i,
   -i - 1,    0, -i - 1,    i]);
      J := Matrix(F,4,4,[
        2,   -1,  i + 1,   0,
       -1,    2,     -i,   0,
   -i + 1,    i,      2,  -1,
        0,    0,     -1,   2]);
/*
     A := Matrix(F,5,4,[1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1, i,0,1,0]);
     B := Matrix(F,5,4,[
        2,   -1,  -i + 1,  0,
       -1,    2,     i,    0,
    i + 1,   -i,     2,   -1,
        0,    0,     -1,   2,
   -i + 1,    0, -i + 1,  -1]);
      J := Matrix(F,4,4,[
        2,   -1,  i + 1,   0,
       -1,    2,     -i,   0,
   -i + 1,    i,      2,  -1,
        0,    0,     -1,   2]);

      A := Matrix(F,5,4,[
       0,  1,  i, 0,
       1,  0,  0, 0,
    -i-1,  0,  i, 0,
       i,  0, -i, 0,
       0,  0,  0, 1]);
     B := Matrix(F,5,4,[
      -i,   1,   -i,  i,
       2,  -1, -i+1,  0,
     i-1,  -i,    0,  i,
    -i-1, i+1,  i-1, -i,
       0,   0,   -1,  2]);
      J := Matrix(F,4,4,[
        2,   -1,  i + 1,   0,
       -1,    2,     -i,   0,
   -i + 1,    i,      2,  -1,
        0,    0,     -1,   2]);

     A := Matrix(F,5,4,[1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1, i,0,1,0]);
     B := Matrix(F,5,4,[
        2,   -1,  -i + 1,  0,
       -1,    2,     i,    0,
    i + 1,   -i,     2,   -1,
        0,    0,     -1,   2,
   -i + 1,    0, -i + 1,  -1]);
      J := Matrix(F,4,4,[
        2,   -1,  i + 1,   0,
       -1,    2,     -i,   0,
   -i + 1,    i,      2,  -1,
        0,    0,     -1,   2]);
*/

   when 32:  // L4
     if NumFld then
       F<omega> := NumberField(x^2+x+1);
     else
       F := CyclotomicField(3); omega := F.1;
     end if;
     gen := -omega; ord := 6;
     A := IdentityMatrix(F,4);
     B := Matrix(F,4,4,[
       1-omega, -omega^2,        0,        0,
       omega^2,  1-omega,  omega^2,        0,
             0, -omega^2,  1-omega, -omega^2,
             0,        0,  omega^2,  1-omega]);
     J := Matrix(F,4,4,[
           3, -2*omega-1,          0,          0,
   2*omega+1,          3,  2*omega+1,          0,
           0, -2*omega-1,          3, -2*omega-1,
           0,          0,  2*omega+1,          3]);

// Rank 5 group
   when 33:  // K5
     if NumFld then
       F<omega> := NumberField(x^2+x+1);
     else
       F := CyclotomicField(3); omega := F.1;
     end if;
     gen := -omega; ord := 6;
     A := IdentityMatrix(F,5);
     B := Matrix(F,5,5,[
          2,      -1,    0,        0,   0,
         -1,       2,   -1, -omega^2,   0,
          0,      -1,    2,       -1,   0,
          0,  -omega,   -1,        2,  -1,
          0,       0,    0,       -1,   2]);
     J := Transpose(B);
/*
     A := IdentityMatrix(F,5);
     B := Matrix(F,5,5,[
          2,       -1,      0,        0,      0,
         -1,        2,     -1,    omega,      0,
          0,       -1,      2,  omega^2,      0,
          0,  omega^2,  omega,        2,  omega,
          0,        0,      0,  omega^2,      2]);
     J := Transpose(B);
     
     B := Matrix(F,5,5,[
        2,   -1,         0,        0,        0,
       -1,    2,        -1,       -1,        0,
        0,   -1,         2, -omega^2,        0,
        0,   -1,    -omega,        2,   -omega,
        0,    0,         0, -omega^2,        2]);
     J := Transpose(B);
*/

// Rank 6
   when 34:  // K6 
     if NumFld then
       F<omega> := NumberField(x^2+x+1);
     else
       F := CyclotomicField(3); omega := F.1;
     end if;
     gen := -omega; ord := 6;
     A := IdentityMatrix(F,6);
     B := Matrix(F,6,6,[
          2,      -1,    0,        0,   0,  0,
         -1,       2,   -1, -omega^2,   0,  0,
          0,      -1,    2,       -1,   0,  0,
          0,  -omega,   -1,        2,  -1,  0,
          0,       0,    0,       -1,   2, -1,
          0,       0,    0,        0,  -1,  2]);
     J := Transpose(B);
/*
     A := IdentityMatrix(F,6);
     B := Matrix(F,6,6,[
        2,   -1,        0,      0,        0,      0,
       -1,    2,       -1,      0,        0,      0,
        0,   -1,        2,     -1,    omega,      0,
        0,    0,       -1,      2,  omega^2,      0,
        0,    0,  omega^2,  omega,        2,  omega,
        0,    0,        0,      0,  omega^2,      2]);
     J := Transpose(B);
     
     B := Matrix(F,6,6,[
        2,   -1,    0,      0,        0,      0,
       -1,    2,   -1,      0,        0,      0,
        0,   -1,    2,     -1,       -1,      0,
        0,    0,   -1,      2, -omega^2,      0,
        0,    0,   -1, -omega,        2, -omega,
        0,    0,    0,      0, -omega^2,      2]);
     J := Transpose(B);
*/

   when 35:  // E6
     F := Rationals();
     A := IdentityMatrix(F,6);
     B := Matrix(F,6,6,[
       2,  0, -1,  0,  0,  0,
       0,  2,  0, -1,  0,  0,
      -1,  0,  2, -1,  0,  0,
       0, -1, -1,  2, -1,  0,
       0,  0,  0, -1,  2, -1,
       0,  0,  0,  0, -1,  2]);
     J := B;

// Rank 7
   when 36:  // E7
     F := Rationals();
     A := IdentityMatrix(F,7);
     B := Matrix(F,7,7,[
       2,  0, -1,  0,  0,  0,  0,
       0,  2,  0, -1,  0,  0,  0,
      -1,  0,  2, -1,  0,  0,  0,
       0, -1, -1,  2, -1,  0,  0,
       0,  0,  0, -1,  2, -1,  0,
       0,  0,  0,  0, -1,  2, -1,
       0,  0,  0,  0,  0, -1,  2]);
     J := B;

// Rank 8
   when 37:  // E8
     F := Rationals();
     A := IdentityMatrix(F,8);
     B := Matrix(F,8,8,[
       2,  0, -1,  0,  0,  0,  0,  0,
       0,  2,  0, -1,  0,  0,  0,  0,
      -1,  0,  2, -1,  0,  0,  0,  0,
       0, -1, -1,  2, -1,  0,  0,  0,
       0,  0,  0, -1,  2, -1,  0,  0,
       0,  0,  0,  0, -1,  2, -1,  0,
       0,  0,  0,  0,  0, -1,  2, -1,
       0,  0,  0,  0,  0,  0, -1,  2]);
     J := B;

   else // should never get here
    error "ComplexRootMatrices: out of range";
  end case;

  return A, B, J, gen, ord;
end intrinsic;

intrinsic ComplexRootMatrices( m::RngIntElt, p::RngIntElt, n::RngIntElt : Minimal := false) -> AlgMatElt, AlgMatElt, AlgMatElt, RngElt, RngIntElt
{ Basic root and coroot matrices for the imprimitive complex reflection 
  group G(m,p,n).  This intrinsic also returns an invariant hermitian form, 
  a generator for the group of roots of unity of the ring of definition, 
  and its order}
// -----------------------------------------------------------
// If m = p = 1, this intrinsic returns roots for Sym(n) in its
// natural permutation representation -- it is reducible.
  require m mod p eq 0 : "second argument must divide first argument";
  require m gt 0 and p gt 0 and n gt 0: "arguments must be greater than 0";
  if n eq 1 then
    m := m div p;
    p := 1;
  end if;
  require m*p*n gt 1: "not a reflection group";
  if m gt 2 then
  // Do not use a sparse representation here or bad things will happen
    K := CyclotomicField(m); z := K.1;
    if IsEven(m) then
      gen := z; ord := m;
    else
      gen := -z; ord := 2*m;
    end if;
  else
  // this is amost the same as CyclotomicField(2), but the type is different
    K := RationalField();
    gen := -1; ord := 2;
    z := m eq 2 select -1 else 1;
  end if;
  J := One(MatrixAlgebra(K,n));  // the invariant Hermitian form
  V := VectorSpace(K,n);
  if n eq 1 then
    A := [V.1];
    B := [(1-z)*V.1];
  else
    A := [V.i - V.(i+1) : i in [1..n-1]];
    B := A;
    if m gt 1 then
      if m eq p then
        if Minimal and (n eq 2) and (m gt 2) then
          gen := -1; ord := 2;
          A := [V.1,V.2];
          if IsEven(m) then
            B := [2*V.1 + V.2, (2+z+z^-1)*V.1+2*V.2];
            J := Matrix(K,2,2, [2*e,e, e,2]) where e is 2+z+z^-1;
          else
            B := [2*V.1 + e*V.2, e*V.1+2*V.2] where e is z+z^-1;
            J := Transpose(Matrix(B));
          end if;
        else
          Append(~A,V.(n-1) - z*V.n);
          Append(~B,V.(n-1) - z^-1*V.n);
        end if;
      elif p eq 1 then
        Append(~A,V.n);
        Append(~B,(1-z)*V.n);
      else // 1 < p < m
        Append(~A,V.(n-1) - z*V.n);
        Append(~B,V.(n-1) - z^-1*V.n);
        Append(~A,V.n);
        Append(~B,(1-z^p)*V.n);
      end if;
    end if;
  end if;
  return Matrix(A), Matrix(B), J, gen, ord;
end intrinsic;

// Conversion functions: name / number
// -----------------------------------
// The names and ranks of the Shephard and Todd groups (for ranks > 2).
names := [<"H",3>,<"J4",3>,<"L",3>,<"M",3>,<"J5",3>,
          <"F",4>,<"N",4>,<"H",4>,<"O",4>,<"L",4>,
          <"K",5>,<"K",6>,<"E",6>,<"E",7>,<"E",8>];

intrinsic CohenCoxeterName( k::RngIntElt ) -> MonStgElt, RngIntElt
{ Cohen's string name and rank of the Shephard and Todd group G_k }
  if k eq 4 then
    return "L",2;
  end if;
  requirerange k, 23, 37;
  return Explode(names[k-22]);
end intrinsic;


intrinsic ShephardToddNumber( X::MonStgElt, n::RngIntElt ) -> RngIntElt
{ The Shephard and Todd number of the complex reflection group of type X_n }
//  <"H",3>,<"J4",3>,<"L",3>,<"M",3>,<"J5",3>,
//    23      24       25      26      27
//  <"F",4>,<"N",4>,<"H",4>,<"O",4>,<"L",4>,
//    28      29       30      31      32
//  <"K",5>,<"K",6>,<"E",6>,<"E",7>,<"E",8>
//    33      34       35      36      37

  case X:
  when "E", "e":
    requirerange n, 6, 8;	// for type E, the rank must be 6, 7 or 8
    stnum := n + 29;

  when "F", "f":
    require n eq 4: "for type F, the rank must be 4";
    stnum := 28;

  when "H", "h":
    requirerange n, 3, 4; 	// for type H, the rank must be 3 or 4
    stnum := n eq 3 select 23 else 30;

  when "J4", "j4":
    require n eq 3: "for type J4, the rank must be 3";
    stnum := 24;

  when "J5", "j5":
    require n eq 3: "for type J5, the rank must be 3";
    stnum := 27;

  when "K", "k":
    requirerange n, 5, 6;	// for type K, the rank must be 5 or 6
    stnum := n + 28;

  when "L", "l":
    requirerange n, 2, 4;	// for type L, the rank must be 2, 3 or 4
    if n eq 2 then
      stnum := 4;
    else
      stnum := (n eq 3) select 25 else 32;
    end if;

  when "M", "m":
    require n eq 3: "for type M, the rank must be 3";
    stnum := 26;

  when "N", "n":
    require n eq 4: "for type N, the rank must be 4";
    stnum := 29;

  when "O", "o", "EN":
    require n eq 4: "for type O, the rank must be 4";
    stnum := 31;

  else
    error
    "the type must be one of E, F, H, J4, J5, K, L, M, N or O";

  end case;
  return stnum;

end intrinsic;

// Cartan matrices
// ---------------
intrinsic ComplexCartanMatrix( k::RngIntElt : NumFld := false ) -> AlgMatElt
{ The complex Cartan matrix for the Shephard and Todd group G_k. }
  A,B,_,_,_ := ComplexRootMatrices(k : NumFld := NumFld);
  return A*Transpose(B);
end intrinsic;

intrinsic ComplexCartanMatrix( m::RngIntElt, p::RngIntElt, n::RngIntElt ) -> AlgMatElt
{ The complex Cartan matrix for the imprimitive complex reflection group G(m,p,n). }
  A,B,_,_,_ := ComplexRootMatrices(m,p,n);
  return A*Transpose(B);
end intrinsic;

/*
If the field F has unique complex conjugation,
return the conjugation map, otherwise return the
identity homomorphism.
*/

fldaut := function(F)
  if Type(F) eq FldRat then
    fn := IdentityHomomorphism(F);
  else
    flag, fn := HasComplexConjugate(F);
    if not flag then
      fn := IdentityHomomorphism(F);
    end if;
  end if;
  return fn;
end function;  

/*
conj := func< M, sigma |
  Generic(Parent(M))!Matrix(Nrows(M),Ncols(M), [sigma(e) : e in Eltseq(M)])>;
*/
hCartanMatrix := function(A,B,J)
  C := A*Transpose(B);
  F := BaseRing(C);
  sigma := fldaut(F);
  len := func<v | (v*J*Transpose(Matrix(1,Ncols(v),[sigma(e) : e in Eltseq(v)])))[1]>;
  return C*DiagonalMatrix(F,[len(A[i])/C[i,i] : i in [1..Ncols(C)]]);
end function;

intrinsic HermitianCartanMatrix( k::RngIntElt : NumFld := false ) -> AlgMatElt
{ The symmetrized complex Cartan matrix for the Shephard and Todd group G_k }
  A,B,J,_,_ := ComplexRootMatrices(k : NumFld := NumFld);
  return hCartanMatrix(A,B,J);
end intrinsic;


intrinsic HermitianCartanMatrix( m::RngIntElt, p::RngIntElt, n::RngIntElt ) -> AlgMatElt
{ The symmetrized complex Cartan matrix for the imprimitive complex reflection group G(m,p,n) }
  A,B,J,_,_ := ComplexRootMatrices(m,p,n);
  return hCartanMatrix(A,B,J);
end intrinsic;


// Complex root data
// -----------------
complexRootDatum_ := function(A,B,gen,ord)
  W := PseudoReflectionGroup(A,B);
  VA := {@ v : v in Rows(A) @};
  VB := {@ v : v in Rows(B) @};
  roots := {@ gen^k*v : v in VA, k in [0..ord-1]  @};
  dualroots := {@ gen^-k*v : v in VB, k in [0..ord-1] @};
  genpairs := [[w,Transpose(w^-1)] : w in Generators(W)];
  ndx := 0;
  while ndx lt #roots do
    ndx +:= 1;
    a := roots[ndx];
    b := dualroots[ndx];
    for p in genpairs do
      w := p[1];
      ww := p[2];
      c := a*w;
      d := b*ww;
      Include(~roots,c);
      Include(~dualroots,d);
    end for;
  end while;
  rho := map<roots -> dualroots | {<roots[i],dualroots[i]> : i in [1..#roots]}>; 
  return roots,dualroots,rho,W;
end function;

intrinsic ComplexRootDatum( k::RngIntElt : NumFld := false ) -> SetIndx, SetIndx, Map, GrpMat, AlgMatElt
{ The complex root datum for the Shephard and Todd group G_k.
  The return values are: roots, coroots, a bijection, the reflection group, and
  an invariant hermitian form}

  A, B, J, gen, ord := ComplexRootMatrices(k : NumFld := NumFld);
  roots, dualroots, rho, W := complexRootDatum_(A,B,gen,ord);
  return roots,dualroots,rho,W,J;
end intrinsic;

// k is the Shephard and Todd number
// A is the matrix of roots
// B is the matrix of coroots
// W is the complex reflection group
// J is the Hermitian form

intrinsic ComplexRootDatum( m::RngIntElt, p::RngIntElt, n::RngIntElt ) -> SetIndx, SetIndx, Map, GrpMat, AlgMatElt
{ The complex root datum for the imprimitive complex reflection group G(m,p,n).
  The return values are: roots, coroots, a bijection, the reflection group, and
  an invariant hermitian form}
  A, B, J, gen, ord := ComplexRootMatrices(m,p,n);
  roots, dualroots, rho, W := complexRootDatum_(A,B,gen,ord);
  return roots,dualroots,rho,W,J;
end intrinsic;

// Basic degrees and codegrees
// ---------------------------
intrinsic BasicDegrees( m::RngIntElt, p::RngIntElt, n::RngIntElt ) -> SeqEnum
{ The degrees of the basic polynomial invariants of the imprimitive reflection group G(m,p,n) }
  require m mod p eq 0: "second argument must divide the first argument";
  degseq := [ i*m : i in [1..n-1] ];
  Append(~degseq, n*m div p);
  return degseq;
end intrinsic;

intrinsic BasicCodegrees( m::RngIntElt, p::RngIntElt, n::RngIntElt ) -> SeqEnum
{ The degrees of the basic polynomial invariants of the imprimitive reflection group G(m,p,n) }
  require m mod p eq 0: "second argument must divide the first argument";
  if m ne p then
    degseq := [ (i-1)*m : i in [1..n] ];
  else
    degseq := [ (i-1)*m : i in [1..n-1] ];
    Append(~degseq, n*m-m-n);
  end if;
  return degseq;
end intrinsic;

