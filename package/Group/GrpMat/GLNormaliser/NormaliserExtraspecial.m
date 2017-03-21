freeze;

/*
contains:
NormaliserExtraspecial

Takes an extraspecial group < GL(n,q) and its order. If successful then returns its normaliser in GL(n,q) in group_norm format. 

Otherwise, carry on with GLNormaliser
*/

function NormaliserExtraspecial(group,og)
  group_norm:=recformat<overgroup,cob,got_overgroup,full_norm, derived_group>;
  n:=Dimension(group);
  q:=#BaseRing(group);
  exspec_norm:=ClassicalMaximals("L",n,q: classes:={6}, general:=true);
  if #exspec_norm eq 0 then 
    return rec<group_norm|got_overgroup:=false>;
  end if;
  E:=exspec_norm[1];
  norms:=[norm`subgroup:norm in NormalSubgroups(E:OrderEqual:=og)];
  if #norms eq 1 then
    bool,x:=IsConjugate(GL(n,q),group,norms[1]);
    if bool then 
      return rec<group_norm|overgroup:=E ,cob:=x, got_overgroup:=true, full_norm:=false>;
    else return rec<group_norm|got_overgroup:=false>; 
  end if;
   
  else return rec<group_norm|got_overgroup:=false>;
  end if;  
end function;

