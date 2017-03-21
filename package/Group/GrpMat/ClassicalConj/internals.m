freeze;

// The internal intrinsics used to compute classes

intrinsic InternalClassesClassical( G::GrpMat ) -> BoolElt
{Internal function: The conjugacy classes of a classical group}
  vprint Classes: "Trying Classical group methods";
  ok := InternalClassesExtendedSL( G ) or
        //InternalClassesExtendedSU( G ) or
        InternalClassesExtendedSp( G ) or
        InternalClassesExtendedOmega( G )
        ;
    
  // try other types
  return ok;
end intrinsic; 
/*
intrinsic InternalClassRepClassical( G::GrpMat, g::GrpMatElt ) -> BoolElt, GrpMatElt, GrpMatElt
{Internal function: The conjugacy classes of a classical}
  vprint Classes: "Trying Classical group methods";
  return false;
end intrinsic; 

intrinsic InternalNclassesClassical( G::GrpMat ) -> BoolElt, RngIntElt
{Internal function: The conjugacy classes of a classical}
  vprint Classes: "Trying Classical group methods";
  return false;
end intrinsic; 

intrinsic InternalCentraliserClassical( G::GrpMat ) -> BoolElt, GrpMat
{Internal function: The conjugacy classes of a classical}
  vprint Classes: "Trying Classical group methods";
  return false;
end intrinsic;
*/

/*

intrinsic AllClassInvariants( G::GrpMat ) -> SeqEnum
{}
end intrinsic;

intrinsic ClassInvariants( G::GrpMat, g::GrpMatElt ) -> Tup
{}
  return OldClassInvariants(G,g);
end intrinsic;

intrinsic ClassInvariants( G::GrpMat, i::RngIntElt ) -> Tup
{}
  return OldClassInvariants(G,i);
end intrinsic;

intrinsic ClassRepresentativeFromInvariants( G::GrpMat, inv::Tup )  -> GrpMatElt
{}
end intrinsic;
*/

// No internals for class map or power map -- these can be found by standard methods 
// once classes are assigned.


