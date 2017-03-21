freeze;

import "lifns.m":LowIndexSubgroupsH, LISubsModN;
intrinsic
LowIndexSubgroups(G::GrpPerm, maxind:: RngIntElt :
                  Presentation:=false, Print:=0, Algorithm := "Recursive",
		  Limit := Infinity ) -> SeqEnum
{Subgroups of index up to maxind in permutation group G}

  if Algorithm eq "Recursive" then
      s := LowIndexSubgroupsH(G,maxind :
             Presentation:=Presentation, trynormsub:=true, Print:=Print);
    elif Algorithm eq "Subgroups" then
	s := Subgroups(G : IndexLimit := maxind, Presentation := Presentation,
                                                          Print := Print);
    else 
	return LowIndexSubgroupsSn(G,<1,maxind>:Limit:=Limit,Print:=Print);
    end if;
    if Presentation then
	return [ x`subgroup : x in s ], [x`presentation:x in s];
    else
	return [ x`subgroup : x in s ], _;
    end if;
end intrinsic;

intrinsic
LowIndexSubgroups(G::GrpPerm, T:: Tup :
                  Presentation:=false, Print:=0, Algorithm := "Recursive",
		  Limit := Infinity ) -> SeqEnum
{Subgroups of index between T[1] and T[2] in permutation group G}

  if #T eq 1 then a:= 1; b := T[1]; 
  elif #T eq 2 then
      a := T[1]; b := T[2];
  else
    error "Second argument must be a pair of integers";
  end if;
  require Type(a) eq RngIntElt and Type(b) eq RngIntElt: 
    "Second argument must be a pair of integers";
  
  if Algorithm eq "Recursive" then
      s := LowIndexSubgroupsH(G,b :
              Presentation:=Presentation, trynormsub:=true, Print:=Print);
    elif Algorithm eq "Subgroups" then
	s := Subgroups(G : IndexLimit := b, Print := Print,
                                         Presentation:=Presentation);
    else 
	return LowIndexSubgroupsSn(G,T:Limit:=Limit,Print:=Print);
    end if;
    if Presentation then
      return [ x`subgroup : x in s | Index(G, x`subgroup) ge a],
	  [ x`presentation : x in s | Index(G, x`subgroup) ge a];
    else
	return [ x`subgroup : x in s | Index(G, x`subgroup) ge a], _;
    end if;
end intrinsic;

intrinsic
LowIndexSubgroups(G::GrpPerm, N::GrpPerm, maxind:: RngIntElt :
                                                    Print:=0) -> SeqEnum
{Subgroups of index up to maxind in permutation group G that contain the
 normal subgroup N of G}
  require IsNormal(G,N) :
      "Second argument must be a normal subgroup of the first";
  return LISubsModN(G,N,maxind : Print:=Print);
end intrinsic;

intrinsic
LowIndexSubgroups(G::GrpPerm, N::GrpPerm, T:: Tup : Print:=0) -> SeqEnum
{Subgroups of index between T[1] and T[2] in permutation group G that contain
 the normal subgroup N of G}
  local subs;
  require IsNormal(G,N) :
      "Second argument must be a normal subgroup of the first";
  if #T eq 1 then a:= 1; b := T[1];
  elif #T eq 2 then
      a := T[1]; b := T[2];
  else
    error "Second argument must be a pair of integers";
  end if;
  require Type(a) eq RngIntElt and Type(b) eq RngIntElt:
    "Second argument must be a pair of integers";
  subs := [s`subgroup: s in LISubsModN(G,N,b : Print:=Print)];
  return [ s`subgroup: s in subs | s`index ge a ];
end intrinsic;

intrinsic
LowIndexSubgroups(G::GrpMat, maxind:: RngIntElt :
                  Presentation:=false, Print:=0, Algorithm := "Recursive",
		  Limit := Infinity ) -> SeqEnum
{Subgroups of index up to maxind in matrix group G}

  if Algorithm eq "Recursive" then
      s := LowIndexSubgroupsH(G,maxind :
                   Presentation:=Presentation, trynormsub:=true, Print:=Print);
    elif Algorithm eq "Subgroups" then
	s := Subgroups(G : IndexLimit := maxind,
                      Presentation := Presentation, Print := Print);
    else 
	return LowIndexSubgroupsSn(G,<1,maxind>:Limit:=Limit,Print:=Print);
    end if;
    if Presentation then
	return [ x`subgroup : x in s ], [x`presentation:x in s];
    else
	return [ x`subgroup : x in s ];
    end if;
end intrinsic;

intrinsic
LowIndexSubgroups(G::GrpMat, T:: Tup :
                  Presentation:=false, Print:=0, Algorithm := "Recursive",
		  Limit := Infinity ) -> SeqEnum
{Subgroups of index between T[1] and T[2] in matrix group G}

  if #T eq 1 then a:= 1; b := T[1]; 
  elif #T eq 2 then
      a := T[1]; b := T[2];
  else
    error "Second argument must be a pair of integers";
  end if;
  require Type(a) eq RngIntElt and Type(b) eq RngIntElt: 
    "Second argument must be a pair of integers";
  
  if Algorithm eq "Recursive" then
      s := LowIndexSubgroupsH(G,b :
                   Presentation:=Presentation, trynormsub:=true, Print:=Print);
    elif Algorithm eq "Subgroups" then
	s := Subgroups(G : IndexLimit := b, Print := Print,
                                      Presentation:=Presentation);
    else 
	return LowIndexSubgroupsSn(G,T:Limit:=Limit,Print:=Print);
    end if;
    if Presentation then
      return [ x`subgroup : x in s | Index(G, x`subgroup) ge a],
	  [ x`presentation : x in s | Index(G, x`subgroup) ge a];
    else
	return [ x`subgroup : x in s | Index(G, x`subgroup) ge a];
    end if;
end intrinsic;

intrinsic
LowIndexSubgroups(G::GrpMat, N::GrpMat, maxind:: RngIntElt :
                                                    Print:=0) -> SeqEnum
{Subgroups of index up to maxind in matrix group G that contain the normal
 subgroup N of G}
  require IsNormal(G,N) :
      "Second argument must be a normal subgroup of the first";
  return [s`subgroup: s in LISubsModN(G,N,maxind : Print:=Print)];
end intrinsic;

intrinsic
LowIndexSubgroups(G::GrpMat, N::GrpMat, T:: Tup : Print:=0) -> SeqEnum
{Subgroups of index between T[1] and T[2] in matrix group G that contain the
 normal subgroup N of G}
  local subs;
  require IsNormal(G,N) :
      "Second argument must be a normal subgroup of the first";
  if #T eq 1 then a:= 1; b := T[1];
  elif #T eq 2 then
      a := T[1]; b := T[2];
  else
    error "Second argument must be a pair of integers";
  end if;
  require Type(a) eq RngIntElt and Type(b) eq RngIntElt:
    "Second argument must be a pair of integers";
  subs := LISubsModN(G,N,b : Print:=Print);
  return [ s`subgroup: s in subs | s`index ge a ];
end intrinsic;
