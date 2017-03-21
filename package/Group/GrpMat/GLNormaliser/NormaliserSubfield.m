freeze;

/*
contains:
NormaliserSubfiled
*/
 

/*
Takes subfield group and returns a record in group_norm format

input comes from 
bool, small_field_gp:=IsOverSmallerField (group: Scalars:=false);
in GLNormaliser

If the group is subfield but only conj to a subgp of GL(n,q0) plus scalars then carry on to other classes:

Returns record in group_norm format
*/

group_norm:=recformat<overgroup,cob,got_overgroup,full_norm, derived_group>;

/************************************/

function NormaliserSubfield(group,small_field_gp : Print:=0)
  n:=Dimension(group);
  q:=#BaseRing(group);
  mat:=SmallerFieldBasis(group);
  norm:=GLNormaliser(small_field_gp:Overgroup:=true,Print:=Print);
  ovgroup:=sub<GL(n,q)|[gen:gen in Generators(norm`overgroup^norm`cob^-1)], Centre(GL(n,q))>;
  return rec<group_norm|overgroup:=ovgroup,cob:=mat, got_overgroup:=true,full_norm:=false>;
end function;



