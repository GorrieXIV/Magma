freeze;


// this is intended to be temporary -- the generic IsWeaklyZero currently gets it wrong
intrinsic IsWeaklyZero(a::RngUPolResElt) -> BoolElt
{True iff the given element is zero up to the known precision}
   PolRing := PreimageRing(Parent(a));
   return IsWeaklyZero(PolRing! a);
end intrinsic;
