freeze;

/*
  diag.m
  
  by Scott H. Murray
  
  Algorithms to compute common eigenspaces and diagonalisations of
  commutative algebras.
  
*/


commonEigenspaces := function( Q : U:= false )
  A := Universe( Q );
  n := Degree( A );  k := BaseRing( A );
  V := BaseModule( A );
  restrict := function( g, U, k )
    d := Dimension( U );  U := ChangeRing( U, k );
    return MatrixAlgebra(k,d)!&cat[ Coordinates( U, u*g ) : u in Basis(U) ],
    func< v, V | &+[ v[i]*V!(U.i) : i in [1..d] ] >;
  end function;
  if Category( U ) eq BoolElt then  U := BaseModule(A);  end if;
  spaces := [* U *];  wts := [ [] ];
  for idx in [1..#Q] do
    g := Q[idx];
    newspaces := [**];  newwts := [];
    for idx2 in [1..#spaces] do
      U := spaces[idx2];  wt := wts[idx2];
      X, h := restrict( g, U, k );
      p := CharacteristicPolynomial( X );
      K := SplittingField( p );
      if K ne k then
	Q := [ ChangeRing( g, K ) : g in Q ];  g := ChangeRing( g, K );
	for i in [1..#spaces] do  spaces[i] := ChangeRing( spaces[i], K );  end for;
	for i in [1..#newspaces] do  newspaces[i] := ChangeRing( newspaces[i], K );  end for;
	X := ChangeRing( X, K );  A := ChangeRing( A, K );
	p := PolynomialRing(K)!p;  V := ChangeRing( V, K );
	k := K;  
      end if;
      for e in Eigenvalues( X ) do
	Append( ~newspaces, 
          sub<V| [ h(Vector(b),V) : b in Basis(Eigenspace(X,e[1])) ]> );
        newwts := newwts cat [ wt cat [e[1]] ]; 
          // We do not use Append because it fails when the field is extended
      end for;
    end for;
    spaces := newspaces;  wts := newwts;
  end for;
  return spaces, wts;
end function;

function ring_supported(R)
    ringtype := Category(R);
    return ringtype in {FldRat, FldFin, FldAC} or ISA(ringtype, FldAlg);
end function;

intrinsic CommonEigenspaces( Q::[AlgMatElt] ) -> [], []
{Common eigenspaces for a sequence of commuting matrices}
  require ring_supported(BaseRing(Universe(Q))) :
    "The base field must be the rationals, finite, algebraic, or algebraically closed";
  require forall{ i : j in [i+1..#Q], i in [1..#Q] | 
    Q[i]*Q[j] eq Q[j]*Q[i] } : "The matrices must commute";
  return commonEigenspaces( Q );
end intrinsic;

intrinsic CommonEigenspaces( A::AlgMat ) -> [], []
{Common eigenspaces for a sequence of commuting matrices}
  require ring_supported(BaseRing(A)) :
    "The base field must be the rationals, finite, algebraic, or algebraically closed";
  require IsCommutative( A ) : "The algebra must be commutative";
  return commonEigenspaces( [ A.i : i in [1..Ngens(A)] ] );
end intrinsic;


intrinsic Diagonalisation( Q::[AlgMatElt] ) -> [], AlgMatElt
{Diagonalisation of a sequence Q of commuting matrices}
  require ring_supported(BaseRing(Universe(Q))) :
    "The base field must be the rationals, finite, algebraic, or algebraically closed";
  require forall{ i : j in [i+1..#Q], i in [1..#Q] | 
    Q[i]*Q[j] eq Q[j]*Q[i] } : "The matrices must commute";
  V := BaseModule( Universe(Q) );
  spaces := commonEigenspaces( Q );
  F := (#spaces ne 0) select BaseRing(spaces[1]) else BaseRing(V);
  V := ChangeRing( V, F );
  P := Matrix( &cat[ ChangeUniverse( Basis( U ), V ) : U in spaces ] );
  return [ P*g*P^-1 : g in Q ], P;
end intrinsic;

intrinsic Diagonalization( Q::[AlgMatElt] ) -> [], AlgMatElt
{Diagonalisation of a sequence Q of commuting matrices}
  return Diagonalisation(Q);
end intrinsic;

intrinsic Diagonalisation( A::AlgMat ) -> AlgMat, AlgMatElt
{Diagonalisation of the commutative matrix algebra A}
  require ring_supported(BaseRing(A)) :
    "The base field must be the rationals, finite, algebraic, or algebraically closed";
  require IsCommutative( A ) : "The algebra must be commutative";
  Q, P := Diagonalisation( [ A.i : i in [1..Ngens(A)] ] );
  return sub< Universe(Q) | Q >, P;
end intrinsic;

intrinsic Diagonalization( A::AlgMat ) -> [], AlgMatElt
{Diagonalisation of the commutative matrix algebra A}
  return Diagonalisation(A);
end intrinsic;


