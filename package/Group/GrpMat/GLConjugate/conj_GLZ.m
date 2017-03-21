freeze;

// Decide whether two matrices A,B in Mat(n,QQ)
// are conjugate in GL(n,ZZ).
// Besides some trivial cases, only the case
// n = 2 (by David Husert) as well as the finite 
// order cases are currently implemented.

declare verbose IntConj, 2;
forward IsConjugate2x2, Centralizer2x2;

InputOK:= function(A, B)
  n:= Nrows(A);
  if n eq 0 then 
    return false, "The matrices must have positive degree";
  end if;
  if n ne Nrows(B) then
    return false, "The matrices must be of the same size";
  end if;
  if not ({Type(BaseRing(A)), Type(BaseRing(A))} subset {RngInt, FldRat}) then
    return false, "The matrices must be over the integers or rationals";
  end if;
  return true, _;
end function;

intrinsic IsGLZConjugate(A::AlgMatElt, B::AlgMatElt) -> BoolElt, GrpMatElt
{Tests if A and B are conjugate in GL(n,Z).
 If so, the second return value x satisfies A^x == B}

  ok, err:= InputOK(A, B);
  require ok: err;

  n:= Nrows(A);
  if A eq B then return true, GL(n, Integers()) ! 1; end if;
  if IsScalar(A) or IsScalar(B) then return false, _; end if;

  d:= Denominator(A);
  if d ne Denominator(B) then return false, _; end if;
  A := Matrix(Integers(), A*d);			// rewrite over ZZ
  B := Matrix(Integers(), B*d);			// in all cases

  c:= Content(A);
  if c ne Content(B) then return false, _; end if;
  if c ne 1 then A div:= c; B div:= c; end if;

  ok, T:= IsSimilar(Matrix(Rationals(), A), Matrix(Rationals(), B));
  if not ok then return false, _; end if;

  if n eq 2 then 
    ok, g:= IsConjugate2x2(B, A);		// mind the order
    if not ok then return false, _; end if;
    return true, g;
  end if;

  if HasFiniteOrder(A) then
    // A,B now both have finite order since A^T=B.
    GLn:= GL(n, Integers());
    GA:= sub<GLn | A>;
    GB:= sub<GLn | B>;
    ok, h:= IsGLZConjugate(GA, GB); 
    if not ok then return false, _; end if;
    AA:= h^-1*A*h;
    if AA eq B then return true, h; end if;
    assert GB`PerfectForms`Complete;
    N:= GeneratorsSequence(NormalizerGLZ(GB));
    NI:= [ n^-1: n in N ];
    Orb:= {@ B @};
    Paths:= [ GLn | 1 ];
    i:= 1; 
    while i le #Orb do
      for j in [1..#N] do 
        X:= N[j] * Orb[i] * NI[j];
        if X in Orb then continue; end if;
        p:= N[j] * Paths[i];
        if X eq AA then return true, h*p; end if;
        Include(~Orb, X); Append(~Paths, p);
      end for;
      i +:= 1;
    end while;
    return false, _;
  end if;
  
  error "not implemented"; 
end intrinsic;

intrinsic IsGLZConjugate(A::GrpMatElt, B::GrpMatElt) -> BoolElt, GrpMatElt
{"} // "
  ok, err:= InputOK(A, B);
  require ok: err;
  return IsGLZConjugate(Matrix(A), Matrix(B));
end intrinsic;

intrinsic IsSLZConjugate(A::AlgMatElt, B::AlgMatElt) -> BoolElt, GrpMatElt
{Tests if A and B are conjugate in SL(n,Z).
 If so, the second return value x satisfies A^x == B}

  ok, err:= InputOK(A, B);
  require ok: err;

  ok, g:= IsGLZConjugate(A, B);
  if ok and Determinant(g) ne 1 then
    C:= CentralizerGLZ(B);
    ok:= exists(c){C.i: i in [1..Ngens(C)] | Determinant(C.i) eq -1};
    if ok then g:= g*c; end if;
  end if;
  if ok then return true, g; end if;
  return false, _;
end intrinsic;

intrinsic IsSLZConjugate(A::GrpMatElt, B::GrpMatElt) -> BoolElt, GrpMatElt
{"} // "
  ok, err:= InputOK(A, B);
  require ok: err;
  return IsSLZConjugate(Matrix(A), Matrix(B));
end intrinsic;

intrinsic CentralizerGLZ(A::AlgMatElt) -> GrpMat
{Returns the centralizer of A in GL(n,Z)}

  ok, err:= InputOK(A, A);
  require ok: err;

  n:= Nrows(A);
  if IsScalar(A) then return GL(n, Integers()); end if;

  if Type(BaseRing(A)) eq FldRat then
    A := Matrix(Integers(), A*Denominator(A));
  end if;
  c:= Content(A);
  if c ne 1 then A div:= c; end if;

  if n eq 2 then return Centralizer2x2(A); end if; 

  if HasFiniteOrder(A) then
    GLn:= GL(n, Integers());
    G:= sub< GLn | A >;
    C:= GeneratorsSequence(CentralizerGLZ(G));
    CI:= [ c^-1: c in C ];
    Orb:= {@ A @};
    Paths:= [ GLn | 1 ];
    Stab:= [];
    i:= 1;
    while i le #Orb do
      for j in [1..#C] do	
        X:= C[j] * Orb[i] * CI[j];
        p:= C[j] * Paths[i];
        idx:= Index(Orb, X);
        if idx ne 0 then
          s:= Paths[i]^-1*p;
          if not IsOne(s) and s notin Stab and s^-1 notin Stab then
            Append(~Stab, s);
          end if;
        else
          Include(~Orb, X); Append(~Paths, p);
        end if;
      end for;
      i +:= 1;
    end while;
    return sub< GLn | Stab >;
  end if;

  error "Not implemented";
end intrinsic;

intrinsic CentralizerGLZ(A::GrpMatElt) -> GrpMat
{"} // "
  ok, err:= InputOK(A, A);
  require ok: err;
  return CentralizerGLZ(Matrix(A));
end intrinsic;


// Code for the GL(2,ZZ) - conjugacy test by David Husert.


//+++++++++++++++++++++++++++++++++++++++++
//+++  D E C I D E  B Y  I D E A L S  +++
//+++++++++++++++++++++++++++++++++++++++++

function IsEquivalent( a, b )
// Decides whether two ideals of a quadratic order are equivalent.
// If so, true and an element c with b = c*a are returned; false (and zero) otherwise.
// Relies on a pricipal ideal test applied to an ideal of an order which is not maximal in general.

    o := MultiplicatorRing( a );
    if o ne MultiplicatorRing( b ) then
        vprint IntConj, 1 : "Ideals are not equivalent. Multiplicator rings differ.";
        return false, _;
    end if;
    a := o !! a;
    b := o !! b;
    // a and b are equivalent iff c is principal.
    c := b * IdealQuotient( 1*o, a );
    d := Denominator( c );
    c := o !! ( d * c );
    equivalent, gamma := IsPrincipal( c );
    if not equivalent then
        vprint IntConj, 1 : "Ideals are not equivalent.";
        return false, _;
    else
        vprint IntConj, 2 : "Ideals are equivalent.";
        return true, gamma / d;
    end if;
end function;

function ConjugatingMatrix_IrreducibleCase( x, y )
// Returns a matrix C which fulfills B = CAC^(-1).
// x and y contain bases for an ideal of an order.
// C is the matrix which changes the basis.

    M := [];
    C := [];
    Z2 := RSpace( Integers(), 2 );
    MatZ := MatrixRing( Integers(), 2 );
    for b in y do
        M cat:= Eltseq(b);
    end for;
    M := MatZ ! M;
    for b in x do
        help := Z2 ! Eltseq( b );
        C cat:= Eltseq( Solution( M, help ) );
    end for;
    C := MatZ ! C;
    return Transpose( C );
end function;

function DecideByIdeals( A, B, f )
// Decides whether A and B are integrally conjugate.
// If so, true and a suitable matrix C are returned; false otherwise.
// f is the characteristic polynomial of both A and B and has to be irreducible.

    o := EquationOrder( f );
    K := FieldOfFractions( o );
    MatK := MatrixRing( K, 2 );
    A := MatK ! A;
    B := MatK ! B;
    x := Basis( Eigenspace( A, o.2 ) )[1];
    y := Basis( Eigenspace( B, o.2 ) )[1];
    x *:= Denominator( x );
    y *:= Denominator( y );
    a := ideal< o | Eltseq( x ) >;
    b := ideal< o | Eltseq( y ) >;
    equivalent, c := IsEquivalent( a, b );
    if not equivalent then
        return false, _;
    else
        x *:=  c;
        return true, ConjugatingMatrix_IrreducibleCase( Eltseq( x ), Eltseq( y ) );
    end if;
end function;

function CentralizerByOrder( A, f )
// Returns the centralizer in GL_2(Z) of a matrix A with irrducible characteristic polynomial f.

    o := EquationOrder(f);
    K := FieldOfFractions( o );
    MatK := MatrixRing( K, 2 );
    A := MatK ! A;
    x := Basis( Eigenspace( A, o.2 ) )[1];
    x *:= Denominator( x );
    a := ideal< o | Eltseq( x ) >;
    O := MultiplicatorRing( a );
    U, map := UnitGroup( O );
    Gens := [];
    for c in Generators( U ) do
        C := ConjugatingMatrix_IrreducibleCase( Eltseq( map(c) * x ), Eltseq( x ) );
        Append( ~Gens, C );
    end for;
    return MatrixGroup< 2, Integers() | Gens >;
end function;

//+++++++++++++++++++++++++++++++++++++++++++
//+++  D E C I D E  B Y  K E R N E L S  +++
//+++++++++++++++++++++++++++++++++++++++++++

function ConjugatingMatrix_NilpotentCase( phi )
// Returns a matrix C which fulfills B = CAC^(-1).

    Z2 := RSpace( Integers(), 2 );
    MatZ := MatrixRing( Integers(), 2 );
    C := [];
    for b in Basis( Z2 ) do
        C cat:= Eltseq( phi( b ) );
    end for;
    C := MatZ ! C;
    return Transpose( C );
end function;

function DecideByKernels( A, B )
// Decides whether A and B are integrally conjugate where A and B are both nilpotent.
// If so, true and a suitable matrix C are returned; false otherwise.
   
    A := Transpose( A );
    B := Transpose( B );
    Z2 := RSpace( Integers(), 2 );
    MatZ := MatrixRing( Integers(), 2 );
    v1 := Basis( Kernel( A ) )[1];
    w1 := Basis( Kernel( B ) )[1];

    // Choose a vector v2 such that v1, v2 is a Basis of Z^2.
    _, v2 := ExtendedGreatestCommonDivisor( Eltseq( v1 ) );
    v2 := Z2 ! Reverse( v2 );
    v2[1] *:= -1;
    error if sub< Z2 | [v1, v2] > ne Z2, "Completition of basis failed.";
    R := RSpaceWithBasis( [v1, v2] );

    // Compute m with A*v2 = m*v1.
    m := (v2 * A)[1] / v1[1];

    solvable, w2 := IsConsistent( B, m * w1 );
    if not solvable then
        vprint IntConj, 1 : "No candidate for an image v2 --> w2";
        return false, _;
    end if;
    if sub< Z2 | [w1, w2] > ne Z2 then
        vprint IntConj, 1 : "Image found, but does not work as basis vector";
        return false, _;
    end if;
    S := RSpaceWithBasis( [w1, w2] );
    phi := hom< R -> S | [w1, w2] >;
    return true, ConjugatingMatrix_NilpotentCase( phi );
end function;

function CentralizerByKernels( A )
// Returns the centralizer in GL_2(Z) of a matrix A which is nilpotent.

    v1 := Basis( Kernel( Transpose( A ) ) )[1];
    v1 := Eltseq( v1 );
    _, v2 := ExtendedGreatestCommonDivisor( v1 );
    v2 := Reverse( v2 );
    v2[1] *:= -1;
    MatZ := MatrixRing( Integers(), 2 );
    C := MatZ ! ( v1 cat v2 );
    C := Transpose( C );
    E := MatZ ! -1;
    H := ScalarMatrix( MatZ, 1 ) + MatrixUnit( MatZ, 1, 2 );
    return MatrixGroup< 2, Integers() | E, C * H * C ^ -1 >;
end function;

//+++++++++++++++++++++++++++++++++++++++++++++++++++
//+++  D E C I D E  B Y  E I G E N S P A C E S  +++
//+++++++++++++++++++++++++++++++++++++++++++++++++++

function DirectSumOfEigenspaces( A, zeros )
// Returns the direct sum Eig( A, z1 ) + Eig( A, z2 ) where z1 nad z2 are the eigenvalues of A containd in zeros.

    Z2 := RSpace( Integers(), 2 );
    A := Transpose( A );
    Eigenvectors := [];
    for z in zeros do
        Eigenvectors cat:= Basis( Eigenspace( A, z ) );
    end for;
    return sub< Z2 | Eigenvectors >;
end function;

function ConjugatingMatrix_EigenspaceCase( psi, kappa, m )
// Returns a matrix C which fulfills B = CAC^(-1).
   
    Q2 := KSpace( Rationals(), 2 );
    MatZ := MatrixRing( Integers(), 2 );
    C := [];
    for b in Basis(Q2) do
        c := Q2 ! kappa( psi( m * b ) );
        c /:= m;
        C cat:= Eltseq( c );
    end for;
    C := MatZ ! C;
    return Transpose( C );
end function;

function DecideByEigenspaces( A, B, zeros )
// Decides whether A and B are integrally conjugate where both A and B have two different integer eigenvalues.
// If so, true and a suitable matrix C are returned; false otherwise.
// zeros contains the eigenvalues for A resp. B.
   
    MA := DirectSumOfEigenspaces( A, zeros );
    MB := DirectSumOfEigenspaces( B, zeros );
    psi := hom< MA -> MB | MA.1 -> MB.1, MA.2 -> MB.2 >;
    Z2 := RSpace( Integers(), 2 );
    m := AbsoluteValue( zeros[1] - zeros[2] );
    NA := sub< MB | psi( m * Z2.1 ), psi( m * Z2.2 ) >;
    NB := sub< MB | m * Z2.1, m * Z2.2 >;
    if NA eq NB then
        kappa := hom< MB -> MB | MB.1 -> MB.1, MB.2 -> MB.2 >;
    else
        kappa := hom< MB -> MB | MB.1 -> MB.1, MB.2 -> -MB.2 >;
        if kappa(NA) ne NB then
            vprint IntConj, 1 : "Suitable kappa does not exist.";
            return false, _;
        end if;
    end if;
    return true, ConjugatingMatrix_EigenspaceCase( psi, kappa, m );
end function;

function CentralizerByEigenspaces( A, zeros )
// Returns the centralizer in GL_2(Z) of a matrix A which has two different integer eigenvalues.

    MA := DirectSumOfEigenspaces( A, zeros );
    psi := hom< MA -> MA | MA.1 -> MA.1, MA.2 -> MA.2 >;
    Z2 := RSpace( Integers(), 2 );
    MatZ := MatrixRing( Integers(), 2 );
    m := AbsoluteValue( zeros[1] - zeros[2] );
    NA := sub< MA | m * Z2.1, m * Z2.2 >;
    kappa := hom< MA -> MA | MA.1 -> MA.1, MA.2 -> -MA.2 >;
   
    if kappa( NA ) ne NA then
        return MatrixGroup< 2, Integers() | ScalarMatrix( MatZ, -1 ) >;
    else
        C := ConjugatingMatrix_EigenspaceCase( psi, kappa, m );
        return MatrixGroup< 2, Integers() | ScalarMatrix( MatZ, -1 ), C >;
    end if;
end function;

function IsConjugate2x2(A,B)
    f := CharacteristicPolynomial( A );

    if IsIrreducible( f ) then
        conjugate, C := DecideByIdeals( A, B, f );
    else
        zeros := Roots( f );
        zeros := [ z[1] : z in zeros ];
        if #zeros eq 1 then
            conjugate, C := DecideByKernels( A - zeros[1], B - zeros[1] );
        else
            conjugate, C := DecideByEigenspaces( A, B, zeros );
        end if;
    end if;
    if not conjugate then return false, _; end if;
    return true, C;
end function;

function Centralizer2x2(A)
    f := CharacteristicPolynomial( A );
    if IsIrreducible( f ) then
        return CentralizerByOrder( A, f );
    else
        zeros := Roots( f );
        zeros := [ z[1] : z in zeros ];
        if #zeros eq 1 then
            return CentralizerByKernels( A - zeros[1] );
        else
            return CentralizerByEigenspaces( A, zeros );
        end if;
    end if;
end function;
