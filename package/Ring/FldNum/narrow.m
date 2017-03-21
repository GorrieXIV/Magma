freeze;

// SRD, September 2007

intrinsic NarrowClassGroup(F::FldNum) -> GrpAb, Map
{The narrow class group of the number field F}
  return RayClassGroup( &+ ChangeUniverse(RealPlaces(F), DivisorGroup(F)) );
end intrinsic;

intrinsic NarrowClassGroup(O::RngOrd) -> GrpAb, Map
{The narrow class group of the maximal order O}
  return NarrowClassGroup(NumberField(O));
end intrinsic;

intrinsic NarrowClassNumber(F::FldNum) -> RngIntElt
{The narrow class number of the number field F}
  return #NarrowClassGroup(F);
end intrinsic;

intrinsic NarrowClassNumber(O::RngOrd) -> RngIntElt
{The narrow class number of the maximal order O}
  return NarrowClassNumber(NumberField(O));
end intrinsic;
