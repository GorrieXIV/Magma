freeze;

/* 
  This file contains all the homotopism constructors.
*/


__GetHomotopism := function( B, C, M : Cat := 0 )
  H := New(Hmtp);
  H`Maps := M;
  H`Domain := B;
  H`Codomain := C;
  if Type(Cat) eq TenCat then
    H`Cat := Cat;
  else
    H`Cat := B`Cat;
  end if;
  return H;
end function;

// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
intrinsic Homotopism( t::TenSpcElt, s::TenSpcElt, M::List ) -> Hmtp
{Constructs the homotopisms from t to s given by the maps in M.}
  require #M eq t`Valence+1 : "Incorrect number of maps.";
  require t`Cat eq s`Cat : "Tensor categories are incompatible.";
  return __GetHomotopism( t, s, M );
end intrinsic;

intrinsic Homotopism( t::TenSpcElt, s::TenSpcElt, M::List, C::TenCat ) -> Hmtp
{Constructs the homotopisms from t to s given by the maps in M and the tensor category C.}
  require #M eq t`Valence+1 : "Incorrect number of maps.";
  require #M eq C`Valence+1 : "Valence does not match the valence of tensors.";
  require t`Cat eq s`Cat : "Tensor categories are incompatible.";
  return __GetHomotopism( t, s, M : Cat := C );
end intrinsic;
