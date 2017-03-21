freeze;

/*
contains:
DerivedTrick

takes an absolutely irreducible group G and optionally G'. 

Returns GL(n,q) or overgroup for normaliser in GL(n,q) of G' which is also an overgroup for normaliser in GL(n,q) of G. Both in group_norm record format.
*/

import "GLNormaliser_functions.m": get_derived_group;

group_norm:=recformat<overgroup,cob,got_overgroup,full_norm, derived_group>;


/****************************/

function DerivedTrick(group: der_group:=0,Print:=0)
  n:=Dimension(group);
  q:=#BaseRing(group);
  assert IsAbsolutelyIrreducible(group);

  if Type(der_group) eq GrpMat then
    D:=der_group;
  else
    D:=get_derived_group(group);
  end if;

  if not (false in [IsScalar(d):d in Generators(D)]) then       
    //G' only scalars 
    return rec<group_norm| overgroup:=GL(n,q), cob:=GL(n,q).0, got_overgroup:=true, full_norm:=false>;
  
  else N:=GLNormaliser(D:Overgroup:=true,Print:=Print);
    if N`got_overgroup then
      N`derived_group:=D;
      return N; 
    else return rec<group_norm| overgroup:=GL(n,q), cob:=GL(n,q).0, got_overgroup:=true, full_norm:=false>;
    end if;
  end if;  

end function;

/*****************************************/

