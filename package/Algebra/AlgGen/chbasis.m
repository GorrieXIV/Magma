freeze;

//
// Changing the basis of an AlgGen
//
// Note that the new algebra is not a subalgebra of the old one.
//

intrinsic ChangeBasis( A::AlgGen, B::{[AlgGenElt]} : Rep:="Dense" ) -> AlgGen, Map
{Change the basis of a structure constant algebra}
  d := Dimension(A);  F := BaseRing(A);
  B := [ b : b in B ];  // convert sets to sequences
  ok, BV := CanChangeUniverse( B, Module(A) );
  require ok : "Invalid basis elements";
  require #B eq d and IsInvertible( Matrix(B) ) : "Not a basis";
  V := RSpaceWithBasis( BV );
  consts := [ Coordinates( V, V!(B[i]*B[j]) ) : i,j in [1..d] ];
  if Category(A) eq AlgLie then
    A0 := LieAlgebra< F, d | consts : Rep:=Rep, Check:=false >;
  elif Category(A) eq AlgAss then
    A0 := AssociativeAlgebra< F, d | consts : Rep:=Rep, Check:=false >;
  elif Category(A) eq AlgClff then
    A0 := CliffordAlgebra< F, d | consts : Rep:=Rep, Check:=false >;
    A0`space := A`space;
    A0`embedding := A`embedding;
    A0`vectors := A`vectors;
    if assigned A`pRing then A0`pRing := A`pRing; end if;
    if assigned A`antiAutMat then A0`antiAutMat := A`antiAutMat; end if;
  else
    A0 := Algebra< F, d | consts : Rep:=Rep >;
  end if; 
  h := iso< A -> A0 | x :-> A0!Coordinates( V, V!x ), y :-> A!(Vector(y)*Matrix(B)) >;
  return A0, h;
end intrinsic;

intrinsic ChangeBasis( A::AlgGen, B::{[ModTupRngElt]} : Rep:="Dense" ) -> AlgGen, Map
  {"} // "
  ok, B := CanChangeUniverse( B, A );
  require ok : "Invalid basis elements";
  return ChangeBasis( A, B );
end intrinsic;  

intrinsic ChangeBasis( A::AlgGen, B::Mtrx : Rep:="Dense" ) -> AlgGen, Map
  {"} // "
  B := [ B[i] : i in [1..Nrows(B)] ];
  return ChangeBasis( A, B );
end intrinsic;  

