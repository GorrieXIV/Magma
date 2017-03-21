freeze;
//
// Constructing classical groups
//
// Moved all code for the conformal groups to conformal.m 2011-05-10 (DET)
//
// NB: Most classical groups are constructed at the C level
//

import "standard.m" : IsSquarish, Nonsquarish;

declare attributes GrpMat:

// Attributes uniquely defining a classical group
// The degree and field are given by the matrix group
  IsClassical,          // NB: only set to false if the group is known not to be classical
  ClassicalType,        // Linear, Unitary, Symplectic, or Orthogonal
  IsStandardClassical,  // Does the group preserve one of the standard forms
                        // Always true for Linear type
  ClassicalSign,        // +1, -1, or 0.  Only set for orthogonal groups
  SesquilinearForm,     // Matrix of the sesquilinear form preserved
  FormAuto,             // The field automorphism of order 1 or 2.
                        // Order 2 for Unitary type, trivial otherwise.
  QuadraticForm,        // Matrix of the quadratic form preserved.  
                        // Only set for orthogonal groups
  OmegaQuotient,        // The subgroup of the standard representation of Delta/Omega	
                        // This determines precisely which group we have

// Additional attributes
  ClassicalForms,       // The record used in Derek Holt's recognition code
  ClassicalName,        // The full name of the group (if it has one)
  ClassicalNameShort;   // The abbreviated name of the group
  
/* Classical group name	      Abbreviation        Kleidman-Liebeck symbol
  GeneralLinearGroup               GL                 I = Delta 
  SpecialLinearGroup               SL                 S = Omega
  
  GeneralUnitaryGroup              GU                 I
  SpecialUnitaryGroup              SU                 S = Omega
  
  SymplecticGroup                  Sp                 I = S = Omega
 
  GeneralOrthogonalGroup(*)        GO                 I
  SpecialOrthogonalGroup(*)        SO                 S
  OmegaGroup(*)                  Omega(*)           Omega
  
(*) = Plus, Minus, or nothing.
Every group has a projective version.
(Half)Spin groups don't fit into this classification since they are not in the natural representation.


The standard representation of the OmegaQuotient is:
Linear:			< a | a^(q-1) >
Unitary:		< a, b | a^(q-1)=b^d, b^(q+1), [a,b] >
Orthogonal: 
  q even		< c, r0 | r0^2, c^(q-1), [r0,c] >
  q odd, d odd		< c, r0, r1 | r0^2, r1^2, (r0 r1)^2, c^((q-1)/2, [r0,c] > 
  q odd, d even		< c, r0, r1 | r0^2, r1^2, (r0 r1)^2, c^(q-1), 
  				r0^c=r1, r1^c=r0, [r0,c], [r1,c] > 
*/
  
// ========================================================
//
// Omega quotient group
//
// See [Murray, Roney-Dougal] for the theory.
//
// 

/* Don's form
F2minus := function(q)
  k := GF(q);  
  K := ext<k|PrimitivePolynomial(GF(q),2)>;
  nu := PrimitiveElement(K);
  N := Norm( nu, k );  T := Trace( nu, k );
  return Matrix( k, 2, 2, [ -2,-T, -T, -2*N ] );
end function;
*/

// ---------------------------------------------------------
//
// OmegaMinus
//

intrinsic OmegaMinus( n::RngIntElt, F::FldFin ) -> GrpMat
{The matrix group Omega-(n,F)}
  require n ge 2 and IsEven(n): "Dimension must be even, and at least 2";
  ford := FactoredOrder(OldOmegaMinus(n,F));
  if n eq 2 then
    G := OmegaMinus( 4, F );
    H := MatrixGroup< 2, F | ExtractBlock(G.1,2,2,2,2)^2 >;
    H`Order := ford;
    return H;
  end if;      

  d := n;  q := #F;
  m := d div 2 -1;   // isotropic rank
  
  nu := PrimitiveElement( ext<F|2> );
  nt := nu^q;
  T := F!(nu + nt);
  N := F!(nu*nt);
  delta0 := F!((nu-nt)^2);
  delete nu;
  
  I := IdentityMatrix( F, m-1 );
  diag3 := func< a,b,c | DiagonalJoin(a,DiagonalJoin(b,c)) >;
  
  if IsOdd(q) then
    delta := Nonsquare(F);
    b := Sqrt(delta0/delta);
    h := diag3(I,
      Matrix(4,4,[F|N,0,0,0, 0,(T^2-2*N)/(2*N),T*b/(2*N),0,
      0,T*b*delta/(2*N),(T^2-2*N)/(2*N),0, 0,0,0,1/N]), I);
    n := ZeroMatrix( F, d, d );
    for i in [1..m-1] do
      n[i,i+1]:=1; n[2*m+3-i,2*m+3-i-1]:= 1;
    end for;
    n[m,d] := (-1)^(m-1);  n[m+3,1] := (-1)^(m-1);

    if IsSquare(F!-2) then
      a := Sqrt(F!-2);
      x := diag3(I,
    	Matrix(4,4,[F|1,a,0,1, 0,1,0,-a,
    	0,0,1,0, 0,0,0,1]), I);
      n[m+1,m+1] := -1;
      n[m+2,m+2] := 1;
    elif not IsSquare(F!2) then
      a := Sqrt(2*delta0);
      x := diag3(I,
    	Matrix(4,4,[F|1,0,a/(b*delta),1, 0,1,0,0,
    	0,0,1,a/b, 0,0,0,1]), I);
      n[m+1,m+1] := 1;
      n[m+2,m+2] := -1;
    else
      a := Sqrt(-2*N);
      x := diag3(I,
    	Matrix(4,4,[F|1,T*a/(2*N),-a*b/(2*N),1, 0,1,0,-T*a/(2*N),
    	0,0,1,-a*b*delta/(2*N), 0,0,0,1]), I);
      n[m+1,m+1] := -(T^2-2*N)/(2*N);
      n[m+2,m+2] :=  (T^2-2*N)/(2*N);
      n[m+1,m+2] := T*b/(2*N);
      n[m+2,m+1] := -T*delta*b/(2*N);
    end if;
  else  // q even
    delta := Nonsquarish(F);
    ok, b := IsSquarish( N/T^2+delta );
    assert ok;
    h := diag3(I,
      Matrix(4,4,[F|N,0,0,0, 0,T^2*b/N+1,T^2/N,0, 
      0,T^2*delta/N,T^2*(b+1)/N+1,0, 0,0,0,1/N]), I);
    x := diag3(I,
      Matrix(4,4,[F|1,1,0,1, 0,1,0,0, 0,0,1,1, 0,0,0,1]), I);
    n := ZeroMatrix( F, d, d );
    for i in [1..m-1] do
      n[i,i+1]:=1; n[2*m+3-i,2*m+3-i-1]:= 1;
    end for;
    n[m,d] := 1;  n[m+3,1] := 1;
    n[m+1,m+1] := 1;  n[m+2,m+2] := 1;
    n[m+2,m+1] := 1;
  end if;
  
  G := MatrixGroup< d, F | [ h, x*n ] >;
  G`IsClassical := true;
  G`ClassicalName := "OmegaMinus";
  G`ClassicalNameShort := "Omega-";
  G`QuadraticForm := QuadraticFormMinus(d, F);
  G`SesquilinearForm := SymmetricBilinearFormMinus(d, F);
  G`ClassicalForms := 1;
  G`IsStandardClassical := true;
  G`Order := ford;
  
  return G;
end intrinsic;

intrinsic OmegaMinus(d::RngIntElt, q::RngIntElt) -> GrpMat
{The matrix group Omega-(d,K)}
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  require d ge 2 and IsEven(d): "Dimension must be even, and at least 2";
  return OmegaMinus(d,GF(q));
end intrinsic;

intrinsic OmegaMinus(V::ModTupFld) -> GrpMat
{The matrix group Omega-(V)}
  d := Dimension(V);  K := BaseRing(V);
  require Type(K) eq FldFin : "Base field is not finite";
  require d ge 2 and IsEven(d): "Dimension must be even, and at least 2";
  return OmegaMinus(d,K);
end intrinsic;


// ---------------------------------------------------------
//
// GOMinus
//

// The extra generators for the old C-level function do not involve the
// central 2x2 block, so we can still use them


intrinsic GeneralOrthogonalGroupMinus(d::RngIntElt, q::RngIntElt) -> GrpMat
{The general orthogonal matrix group GO-(d,q)}
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsEven(d) : "Invalid dimension -- should be even";
  require IsPrimePower(q) : "Invalid field size";
  G2 := OldGeneralOrthogonalGroupMinus(d,q);
  ford := FactoredOrder(G2);
  if d eq 2 then
    F := GF(q);
    G := OmegaMinus( 4, F );
    H := MatrixGroup< 2, F | [ExtractBlock(G.i,2,2,2,2): i in [1..2]] >;
    H`Order := ford;
    return H;
  end if;      
  G1 := OmegaMinus(d,q);
  G3 := MatrixGroup< d, q | [G1.1, G1.2] cat [G2.i : i in [3..Ngens(G2)]] >;
  G3`Order := ford;
  return G3;
end intrinsic;

intrinsic GeneralOrthogonalGroupMinus(d::RngIntElt, K::FldFin) -> GrpMat
{The general orthogonal matrix group GO-(d,q)}
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsEven(d) : "Invalid dimension -- should be even";
  G := GeneralOrthogonalGroupMinus(d,#K);
  return ChangeRing( G, K );
end intrinsic;

intrinsic GeneralOrthogonalGroupMinus(V::ModTupFld) -> GrpMat
{The general orthogonal matrix group GO-(V)}
  d := Dimension(V);  K := BaseRing(V);
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsEven(d) : "Invalid dimension -- should be even";
  G := GeneralOrthogonalGroupMinus(d,#K);
  return ChangeRing( G, K );
end intrinsic;
intrinsic GOMinus(V::ModTupFld) -> GrpMat
{The general orthogonal matrix group GO-(V)}
  return GeneralOrthogonalGroupMinus(V);
end intrinsic;

// ---------------------------------------------------------
//
// SOMinus
//

intrinsic SpecialOrthogonalGroupMinus(d::RngIntElt, q::RngIntElt) -> GrpMat
{The special orthogonal matrix group SO-(d,q)}
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsEven(d) : "Invalid dimension -- should be even";
  require IsPrimePower(q) : "Invalid field size";
  G2 := OldSpecialOrthogonalGroupMinus(d,q);
  ford := FactoredOrder(G2);
  if d eq 2 then
    if IsEven(q) then return GOMinus(d,q); end if;
    F := GF(q);
    G := OmegaMinus( 4, F );
    H := MatrixGroup< 2, F | ExtractBlock(G.1,2,2,2,2) >;
    H`Order := ford;
    return H;
  end if;      
  G := GOMinus(d,q);
  if IsOdd(q) then  // lose 4th generator
    G := MatrixGroup< d, q | G.1, G.2, G.3 >;
  end if;
  G`Order := ford;
  return G;
end intrinsic;

intrinsic SpecialOrthogonalGroupMinus(d::RngIntElt, K::FldFin) -> GrpMat
{The special orthogonal matrix group SO-(d,q)}
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsEven(d) : "Invalid dimension -- should be even";
  G := SpecialOrthogonalGroupMinus(d,#K);
  return ChangeRing( G, K );
end intrinsic;

intrinsic SpecialOrthogonalGroupMinus(V::ModTupFld) -> GrpMat
{The special orthogonal matrix group SO-(V)}
  d := Dimension(V);  K := BaseRing(V);
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsEven(d) : "Invalid dimension -- should be even";
  G := SpecialOrthogonalGroupMinus(d,#K);
  return ChangeRing( G, K );
end intrinsic;

// Test code moved to test_classical.m

// ---------------------------------------------------------
//
// Spin
//
intrinsic Spin( n::RngIntElt, q::RngIntElt ) -> GrpMat
{The spin group Spin(n,q)}
  require n gt 0 : "Invalid dimension -- should be positive";
  require IsOdd( n ) : "Dimension must be odd";
  require q ge 2 and IsPrimePower( q ) : "q must be a prime power";
  l := n div 2;
  R := IrreducibleRootDatum( "B", l : Isogeny:="SC" );
  G := GroupOfLieType( R, GF(q) );
  wt := StandardLattice( l ).l;
  rho := HighestWeightRepresentation(G, wt);
  Sp := Image(rho);
  Sp`Order := FactoredChevalleyGroupOrder("B",l,q : Version:="Universal");
  std := StandardRepresentation(G);
  Om := Image(std);
  return Sp, hom< Sp -> Om | x :-> (x@@rho)@std >;
end intrinsic;

intrinsic Spin(d::RngIntElt, K::FldFin) -> GrpMat
{The spin group Spin(n,K)}
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsOdd(d) : "Invalid dimension -- should be odd";
  require IsFinite(K) : "Invalid field -- should be finite";
  G := Spin(d,#K);
  return ChangeRing( G, K );
end intrinsic;

intrinsic Spin(V::ModTupFld) -> GrpMat
{The spin group Spin(V)}
  d := Dimension(V);  K := BaseRing(V);
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsOdd(d) : "Invalid dimension -- should be odd";
  require IsFinite(K) : "Invalid field -- should be finite";
  return Spin(d,K);
end intrinsic;

intrinsic SpinPlus( n::RngIntElt, q::RngIntElt ) -> GrpMat
{The Spin group Spin^+(n,q)}
  require IsEven( n ) : "Dimension must be even";
  require n ge 0 : "Invalid dimension -- should be positive";
  require q ge 2 and IsPrimePower( q ) : "q must be a prime power";
  l := n div 2;
  R := IrreducibleRootDatum( "D", l : Isogeny:="SC" );
  G := GroupOfLieType( R, GF(q) );
  wts := StandardLattice( l );
  rho1 := HighestWeightRepresentation(G, wts.l);
  rho2 := HighestWeightRepresentation(G, wts.(l-1));
  rho := DirectSum( rho1, rho2 );
  Sp := Image(rho);
  Sp`Order := FactoredChevalleyGroupOrder("D",l,q : Version:="Universal");
  std := StandardRepresentation(G);
  Om := Image(std);
  return Sp, hom< Sp -> Om | x :-> (x@@rho)@std >;
end intrinsic;

intrinsic SpinPlus(d::RngIntElt, K::FldFin) -> GrpMat
{The spin group Spin^+(n,K)}
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsEven( d ) : "Dimension must be even";
  G := SpinPlus(d,#K);
  return ChangeRing( G, K );
end intrinsic;
intrinsic SpinPlus(V::ModTupFld) -> GrpMat
{The spin group Spin(V)}
  d := Dimension(V);  K := BaseRing(V);
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsEven(d) : "Invalid dimension -- should be odd";
  require IsFinite(K) : "Invalid field -- should be finite";
  return SpinPlus(d,K);
end intrinsic;

intrinsic SpinMinus( n::RngIntElt, q::RngIntElt ) -> GrpMat
{The Spin group Spin^-(n,q)}
  require IsEven( n ) : "Dimension must be even";
  require n ge 6 : "Invalid dimension -- should be at least 6";
  require q ge 2 and IsPrimePower( q ) : "q must be a prime power";
  l := n div 2;
  R := RootDatum( "D" cat IntegerToString(l) : Isogeny:="SC", Twist:=2 );
  G := TwistedGroupOfLieType( R, GF(q), GF(q^2) );
  Over := UntwistedOvergroup(G);
  wts := StandardLattice( l );
  rho1 := HighestWeightRepresentation(Over, wts.l);
  rho2 := HighestWeightRepresentation(Over, wts.(l-1));
  rho := DirectSum( rho1, rho2 );
  std := StandardRepresentation(Over);
  S := RelativeRootDatum( R );
  N := NumPosRoots( S );
  Sp := sub< Codomain(rho) | 
    [ RelativeRootElement(G,i,[x])@rho :
      i in [1..RelativeRank(R)] cat [N..N+RelativeRank(R)],
      x in Basis(GF(q^2)) ] >;
  Sp`Order := FactoredChevalleyGroupOrder("2D",l,q : Version:="Universal");
  return Sp, hom< Sp -> Codomain(std) | x :-> (x@@rho)@std >;
end intrinsic;

intrinsic SpinMinus(d::RngIntElt, K::FldFin) -> GrpMat
{The spin group Spin^-(n,K)}
  require d gt 6 : "Invalid dimension -- should be at least 6";
  require IsEven( d ) : "Dimension must be even";
  G := SpinPlus(d,#K);
  return ChangeRing( G, K );
end intrinsic;

intrinsic SpinMinus(V::ModTupFld) -> GrpMat
{The spin group Spin^-(V)}
  d := Dimension(V);  K := BaseRing(V);
  require d gt 6 : "Invalid dimension -- should be at least 6";
  require IsEven(d) : "Invalid dimension -- should be odd";
  require IsFinite(K) : "Invalid field -- should be finite";
  return SpinPlus(d,K);
end intrinsic;


