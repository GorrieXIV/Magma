freeze;

//
// Isometry and similarity of classical forms
//
// The following groups are constructed at the C level:
// GL, Sp, 

// The type of A as a bilinear form -- only useful in odd characteristic
bilinearFormType := function( A )
  if A eq -Transpose(A) then
    return "symplectic";
  elif IsSymmetric( A )  then
    d := Nrows(A);
    if IsOdd( #BaseRing(A) ) then
      m := d div 2;
      if IsOdd( d ) then
          return "orthogonalcircle";
      elif IsSquare( (-1)^m * Determinant(A) ) then
          return "orthogonalplus";
      else
          return "orthogonalminus";
      end if;
    else // this will never be reached
      return IsOdd( d ) select "orthogonalcircle" else "orthogonalplus";
    end if;
  else
    return "unknown";
  end if;
end function;

// The sign of A as a symmetric bilinear form
bilinearFormSign := function( A )
  d := Nrows(A);
  if IsOdd( #BaseRing(A) ) then
    m := d div 2;
    if IsOdd( d ) then
        return 0;
    elif IsSquare( (-1)^m * Determinant(A) ) then
        return +1;
    else
        return -1;
    end if;
  else
    return IsOdd( d ) select 0 else 1;  // -1 forms degenerate
  end if;
end function;

// The following function assumes that A and B are defined
// over a common finite field, in which case they are similar
// if and only if they have the same type.
isSimilar := function( A, B ) 
  A := Matrix(A);  B := Matrix(B);
  typeA := bilinearFormType(A);
  typeB := bilinearFormType(B);
  if typeA ne typeB then return false, _, _; end if;

  T := TransformForm(B,typeB) * TransformForm(A,typeA)^-1;
  A2 := T*A*Transpose(T);
  d := Nrows(A);
  if d eq 0 then
    lambda := BaseRing(A)!1;
  else
    _ := exists(i){ i : i in [1..d] | A2[1,i] ne 0 };
    lambda := A2[1,i] / B[1,i];
  end if;
  assert T*A*Transpose(T) eq lambda*B;
  return true, T, lambda;
end function;

intrinsic TransformBilinearForm( A::AlgMatElt ) -> BoolElt
{Transform A to the standard form}
  n := Nrows(A);
  require n eq Ncols(A) : "Matrix must be square";
  require IsInvertible(A) : "Degenerate form";
  F := BaseRing(A);
  require IsFinite(F) : "Matrix must be defined over a finite field";
  type := bilinearFormType(A);
  J := case< type |
    "symplectic" : StandardAlternatingForm( n, F ),
    "orthogonalcircle" : SymmetricBilinearForm( n, F ),
    "orthogonalplus" : SymmetricBilinearFormPlus( n, F ),
    "orthogonalminus" : SymmetricBilinearFormMinus( n, F ),
    default : false >;
  require J cmpne false : "Invalid form";
  _, T, lambda := isSimilar(A,J);
  return J, T, lambda;
end intrinsic;


// ---------------------------------------------------------
//
// Direct sums
//
//
interlacedSum := function( A,m,r, B,n,s )
  F := BaseRing(A);
  d := 2*m+r;  e := 2*n+s;
  X := ZeroMatrix(F,d+e,d+e);
  
  // Blocks from A
  InsertBlock( ~X, ExtractBlock(A,1,1,m,m), 1,1);
  InsertBlock( ~X, ExtractBlock(A,1,m+1,m,r), 1,m+n+1);
  InsertBlock( ~X, ExtractBlock(A,1,m+r+1,m,m), 1,m+r+e+1);

  InsertBlock( ~X, ExtractBlock(A,m+1,1,r,m), m+n+1,1);
  InsertBlock( ~X, ExtractBlock(A,m+1,m+1,r,r), m+n+1,m+n+1);
  InsertBlock( ~X, ExtractBlock(A,m+1,m+r+1,r,m), m+n+1,m+r+e+1);

  InsertBlock( ~X, ExtractBlock(A,m+r+1,1,m,m), m+r+e+1,1);
  InsertBlock( ~X, ExtractBlock(A,m+r+1,m+1,m,r), m+r+e+1,m+n+1);
  InsertBlock( ~X, ExtractBlock(A,m+r+1,m+r+1,m,m), m+r+e+1,m+r+e+1);
  
  // Blocks from B
  InsertBlock( ~X, ExtractBlock(B,1,1,n,n), m+1,m+1);
  InsertBlock( ~X, ExtractBlock(B,1,n+1,n,s), m+1,m+n+r+1);
  InsertBlock( ~X, ExtractBlock(B,1,n+s+1,n,n), m+1,m+n+r+s+1);

  InsertBlock( ~X, ExtractBlock(B,n+1,1,s,n), m+n+r+1,m+1);
  InsertBlock( ~X, ExtractBlock(B,n+1,n+1,s,s), m+n+r+1,m+n+r+1);
  InsertBlock( ~X, ExtractBlock(B,n+1,n+s+1,s,n), m+n+r+1,m+n+r+s+1);

  InsertBlock( ~X, ExtractBlock(B,n+s+1,1,n,n), m+n+r+s+1,m+1);
  InsertBlock( ~X, ExtractBlock(B,n+s+1,n+1,n,s), m+n+r+s+1,m+n+r+1);
  InsertBlock( ~X, ExtractBlock(B,n+s+1,n+s+1,n,n), m+n+r+s+1,m+n+r+s+1);
  
  return X;
end function;


centralSum := function( A, B )
  d := Nrows(A);  m := d div 2;  r := d mod 2;
  e := Nrows(B);  n := e div 2;  s := e mod 2;
  return interlacedSum( A,m,r, B,n,s );
end function;


/* test code
for d in [1..5] do
  for e in [1..5] do
    print d, e;
    F<[a]> := RationalFunctionField( Rationals(), d^2 );
    E<[b]> := RationalFunctionField( F, e^2 );
    ChangeUniverse( ~a, E );
    A := Matrix(d,d,a);
    B := Matrix(e,e,b);
    print centralSum(A,B);
    print "";
  end for;
end for;
*/

intrinsic UnitaryDirectSum( A::Mtrx, B::Mtrx ) -> GrpMatElt
{Given A, B in unitary groups, return a unitary matrix conjugate to their direct 
sum}
  F := BaseRing(A);
  require F cmpeq BaseRing(B) : "Not defined over the same ring";
  n := Nrows(A);  m := Nrows(B);
  return GL(n+m,F)!centralSum( A, B );
end intrinsic;
  
intrinsic SymplecticDirectSum( A::Mtrx, B::Mtrx ) -> GrpMatElt
{Given A, B in symplectic groups, return a symplectic matrix conjugate to their direct sum}
  F := BaseRing(A);
  require F cmpeq BaseRing(B) : "Not defined over the same ring";
  n := Nrows(A);  m := Nrows(B);
  return GL(n+m,F)!centralSum( A, B );
end intrinsic;
  
/* test code
for d in [2..10 by 2] do
  for e in [2..10 by 2] do
    for q in [2,3,4,5,7,8,9,11] do
      _ := SymplecticDirectSum( Random(Sp(d,q)), Random(Sp(d,q)) );
    end for;
  end for;
end for;
*/

intrinsic OrthogonalDirectSum( A::Mtrx, B::Mtrx : ASign:=false, BSign:=false,
  Sign:=false ) -> GrpMatElt
{Given A, B in orthogonal groups, return an orthogonal matrix conjugate to their direct sum}
  F := BaseRing(A);
  require F cmpeq BaseRing(B) : "Not defined over the same ring";

  //ASign,BSign,Sign;
  d := Nrows(A);  e := Nrows(B);
  if ASign cmpeq false then 
    ASign := IsEven(d) select +1 else 0;
  end if;
  if BSign cmpeq false then 
    BSign := IsEven(e) select +1 else 0;
  end if;
/*  require (IsEven(d) and ASign in [+1,-1]) or (IsOdd(d) and ASign eq 0) :
    "Invalid sign";
  require (IsEven(e) and BSign in [+1,-1]) or (IsOdd(e) and BSign eq 0) :
    "Invalid sign";*/
  assert IsScalar( A*J*Transpose(A) * J^-1 ) where
    J is SymmetricBilinearForm( ASign, d, F );
  assert IsScalar( B*J*Transpose(B) * J^-1 ) where
    J is SymmetricBilinearForm( BSign, e, F );

  r := IsOdd(d) select 1 else ((ASign eq -1) select 2 else 0);
  s := IsOdd(e) select 1 else ((BSign eq -1) select 2 else 0);
  m := (d-r) div 2;  n := (e-s) div 2;
  
  X1 := interlacedSum( A,m,r, B,n,s );

  J := DiagonalJoin( SymmetricBilinearForm(ASign,r,F), 
    SymmetricBilinearForm(BSign,s,F) );
  _, T, lambda := TransformBilinearForm( J );
  I := IdentityMatrix( F, m+n );
  TX := DiagonalJoin(lambda*I,DiagonalJoin(T,I));

  X := TX*X1*TX^-1;
  if IsOdd(d+e) then
    XSign := 0;
  elif IsOdd(d) and IsOdd(e) then 
    XSign := bilinearFormSign( J );
  else
    XSign := ASign*BSign;
  end if;

/*  JA := SymmetricBilinearForm( ASign, d, F );
  JB := SymmetricBilinearForm( BSign, e, F );
  JAB := interlacedSum( JA,m,r, JB,n,s );
  JX := SymmetricBilinearForm( XSign, d+e, F );
  assert X1*JAB*Transpose(X1) * JAB^-1;
  assert TX*JAB*Transpose(TX) eq lambda*JX;
  assert IsScalar( X*JX*Transpose(X) * JX^-1 );*/
  if Sign cmpeq false then
    Sign := XSign;
  elif Sign ne XSign then
    _, T, lambda := TransformBilinearForm( SymmetricBilinearForm( Sign, d+e, F ) );
    X := T^-1*X*T;
  end if;
  assert IsScalar( X*J*Transpose(X) * J^-1 ) where
    J is SymmetricBilinearForm( Sign, d+e, F );
  
  return X, Sign;
end intrinsic;



/* test:
F := GF(17);
d := Random([4..10]);  e := Random([4..10]);
ASign := IsEven(d) select Random([1,-1]) else 0;
BSign := IsEven(e) select Random([1,-1]) else 0;
A := Random( Omega( ASign, d, F ) );
B := Random( Omega( BSign, e, F ) );
JA := SymmetricBilinearForm( ASign,d,F );
JB := SymmetricBilinearForm( BSign,e,F );
A*JA*Transpose(A) eq JA;
B*JB*Transpose(B) eq JB;

X, sign := OrthogonalDirectSum(A,B:ASign:=ASign,BSign:=BSign);
JX := SymmetricBilinearForm( sign, d+e, F );
X*JX*Transpose(X) eq JX;
*/


intrinsic UnitaryTensorProduct( A::Mtrx, B::Mtrx ) -> GrpMatElt
{Given A, B in symplectic groups, return a unitary matrix conjugate to their tensor 
product}
  F := BaseRing(A);
  require F cmpeq BaseRing(B) : "Not defined over the same ring";
  n := Nrows(A);  m := Nrows(B);  
  return GL(n*m,F)!KroneckerProduct( A, B );
end intrinsic;

intrinsic SymplecticTensorProduct( A::Mtrx, B::Mtrx ) -> GrpMatElt
{Given A, B in symplectic groups, return an orthogonal matrix conjugate to their 
tensor product}
  F := BaseRing(A);
  require F cmpeq BaseRing(B) : "Not defined over the same ring";
  d := Nrows(A);  e := Nrows(B);
  m := d div 2;   n := e div 2;
  neg := &cat[ [(i-1)*e+n+1..(i-1)*e+e] : i in [1..m] ];
  p := DiagonalMatrix( [ F | (i in neg) select -1 else 1 : i in [1..d*e] ] );
  return p*(GL(d*e,F)!KroneckerProduct( A, B ))*p;
end intrinsic;


intrinsic OrthogonalTensorProduct( A::Mtrx, B::Mtrx :
  ASign:=false, BSign:=false, Sign:=false ) -> GrpMatElt
{Given A, B in orthogonal groups, return an orthogonal matrix conjugate to their 
direct sum}
  F := BaseRing(A);
  require F cmpeq BaseRing(B) : "Not defined over the same ring";

  d := Nrows(A);  e := Nrows(B);
  if ASign cmpeq false then
    ASign := +1;//IsEven(d) select +1 else 0;
  end if;
  if BSign cmpeq false then
    BSign := +1;//IsEven(e) select +1 else 0;
  end if;
/*  require (IsEven(d) and ASign in [+1,-1]) or (IsOdd(d) and ASign eq 0) :
    "Invalid sign";
  require (IsEven(e) and BSign in [+1,-1]) or (IsOdd(e) and BSign eq 0) :
    "Invalid sign";*/

  // Which indices need fixing
  // This could be used to improve efficiency
  /*r := IsOdd(d) select 1 else ((ASign eq -1) select 2 else 0);
  s := IsOdd(e) select 1 else ((BSign eq -1) select 2 else 0);
  m := (d-r) div 2;  n := (e-s) div 2;
  idxs := &cat[ [(i-1)*e+n+1..(i-1)*e+n+s] : i in [1..m] ] cat
   &cat[ [(i-1)*e+1..(i-1)*e+e] : i in [m+1..m+r] ] cat
   &cat[ [(i-1)*e+n+1..(i-1)*e+n+s] : i in [m+r+1..d] ]*/

  X := KroneckerProduct( A, B );
  
  J := KroneckerProduct( SymmetricBilinearForm(ASign,d,F),
    SymmetricBilinearForm(BSign,e,F) );
  assert IsScalar( X*J*Transpose(X) * J^-1 );
  _, T, lambda := TransformBilinearForm( J );
  //I := IdentityMatrix( F, m+n );
  TX := T; //DiagonalJoin(lambda*I,DiagonalJoin(T,I)); 

  X := TX*X*TX^-1;
  /*if IsOdd(d+e) then
    sign := 0;
  elif IsOdd(d) and IsOdd(e) then
    sign := bilinearFormSign( J );
  else
    sign := ASign*BSign;  
  end if;*/

  XSign := bilinearFormSign( J );
  if Sign cmpeq false then
    Sign := XSign;
  elif Sign ne XSign then
    _, T, lambda := TransformBilinearForm( SymmetricBilinearForm( Sign, d*e, F ) );
    X := T^-1*X*T;
  end if;
  assert IsScalar( X*JX*Transpose(X) * JX^-1 ) where
    JX is SymmetricBilinearForm( Sign, d*e, F );
      
  return X, Sign;
end intrinsic;




/* test code
for d in [2..10 by 2] do
  for e in [2..10 by 2] do
    for q in [2,3,4,5,7,8,9,11] do
      J := SymmetricBilinearFormPlus(d*e,q);
      A := SymplecticTensorProduct( Random(Sp(d,q)), Random(Sp(e,q)) );
      print d,e,q,"Sp", A*J*Transpose(A) eq J;

      J := UnitaryForm(d*e,q^2); 
      A := UnitaryTensorProduct( Random(GU(d,q)), Random(GU(e,q)) );
      print d,e,q,"GU", A*J*Transpose(Parent(A)![x^q:x in Eltseq(A)]) eq J;
    end for;
  end for;
end for;

for d in [1..10] do
  for e in [1..10] do
    for q in [3,5,7,9,11,25] do
      for sA in IsEven(d) select [+1,-1] else [0] do
        for sB in IsEven(e) select [+1,-1] else [0] do
          G := (d eq 1) select GL(1,q) else CO(sA,d,q);  A := Random(G);
          H := (e eq 1) select GL(1,q) else CO(sB,e,q);  B := Random(H);
          X,s := OrthogonalTensorProduct( A, B 
            : ASign := sA, BSign := sB );
          J := SymmetricBilinearForm(s,d*e,q);
          if not (IsSimilar(X,KroneckerProduct(A,B)) and 
          IsScalar(X*J*Transpose(X) * J^-1)) then
            error q,d,e,sA,sB;
          end if;
	end for;
      end for;
    end for;  
  end for;
end for;
  

*/

