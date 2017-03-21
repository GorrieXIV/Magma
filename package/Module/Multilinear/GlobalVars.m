freeze;

/*
  Global variables
*/
__SANITY_CHECK := false;
__LIST := { ModTupFld, ModFld, ModMatFld }; // suitable types we can do most computations with.
__GLUE := function( T ) // returns the 'domain' and the 'codomain'.
  if Type(T) eq TenSpcElt then
    return T`Domain cat [*T`Codomain*];
  else
    return T`Frame;
  end if;
end function;
