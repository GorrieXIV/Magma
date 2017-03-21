freeze;

/*
  This file contains basic functions for tensor categories (TenCat).
*/


// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
intrinsic Valence( C::TenCat ) -> RngIntElt
{Returns the valence of the tensor category.}
  return (C`Contra) select C`Valence-1 else C`Valence;
end intrinsic;

intrinsic RepeatPartition( C::TenCat ) -> SetEnum
{Returns the repeat partition of the tensor category.}
  P := C`Repeats;
  if C`Contra then
    assert {0} in P;
    Exclude(~P,{0});
  end if;
  return P;
end intrinsic;

intrinsic IsCovariant( C::TenCat ) -> BoolElt
{Decides if the tensor category is covariant .}
  return not C`Contra;
end intrinsic;

intrinsic IsContravariant( C::TenCat ) -> BoolElt
{Decides if the tensor category is contravariant.}
  return C`Contra;
end intrinsic;

intrinsic Arrows( C::TenCat ) -> SeqEnum
{Returns the directions of the arrows of the category. 
A -1 signifies an up arrow, a 0 signifies an equal arrow, and a 1 signifies a down arrow.}
  return C`Contra select [ i @ C`Arrows : i in Reverse([1..C`Valence]) ] else [ i @ C`Arrows : i in Reverse([0..C`Valence]) ];
end intrinsic;
