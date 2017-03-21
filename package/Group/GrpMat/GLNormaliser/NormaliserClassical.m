freeze;

/*
GetOMinusDelta
GetOvergroup
NormaliserClassical
*/


/*************************************/

/*
delta element for OMinus
associated with Kleidman and Lieback form
*/

GetOMinusDelta:=function(n,q)
  F:=GF(q);
  z:= PrimitiveElement(F);

  done:=0;
  i:=1;
  while done eq 0 and i le q-1 do
    a:=z^i;
    Bs:=[f:f in F|a^2+f^2 eq z];
    if #Bs gt 0 then
      b:=Bs[1];
      done :=1;
    end if;
    i:=i+1;
  end while;

  ab:=Matrix([[a,b],[b,-a]]);

   if IsEven((n*(q-1)) div 4) then
    disc:= "nonsquare";
  else
    disc:= "square";
  end if;

  if disc eq "square" then
    delta:= GL(n,q)!DiagonalJoin([ab:i in [1..n div 2]]);
  else
    delta:= GL(n,q)!DiagonalJoin([ab:i in [1..((n div 2)-1)]] cat [Matrix([[0,1],[z,0]])]);
  end if;
  //gets Kleidman and Liebeck form delta
  bool, form:= SymmetricBilinearForm(GOMinus(n,q));
  x:= GL(n, q)!CorrectForm(form, n, q, "orth-");

  /* this matrix would conjugate gominus into a group  preserving the diagonal form given in kleidman and liebeck.*/

  return delta^(x^(-1));
end function;



/**********************************/
//gets the conformal group

function GetOvergroup(type, n, q)
  F:=GF(q);
  z:= PrimitiveElement(F);
  mat:=GL(n, q)!DiagonalMatrix([z : i in [1..(n div 2)]] cat [1 : i in [((n div 2) + 1)..n]]);
  prim_scal:= GL(n, q)!ScalarMatrix(n, z);
  case (type):
  when "symplectic":
    if IsOdd(q) then
      return sub<GL(n, q)|Sp(n, q), mat>;
    else
      return sub<GL(n, q)|Sp(n, q),prim_scal>;
    end if;

  when "unitary":
    return sub<GL(n, q)|GU(n, Integers()!Round(Sqrt(q))),prim_scal>;

  when "orthogonalcircle":
    return sub<GL(n, q)|GO(n, q), prim_scal>;

  when "orthogonalminus":
    if n eq 2 and q eq 3 then 
      return GL(n,q);
    elif IsEven(q) then //I \times F^*
      return sub<GL(n, q)|GOMinus(n,q), prim_scal>;
    end if;

    delta:=GetOMinusDelta(n,q);
    return sub<GL(n, q)|GOMinus(n, q), delta>;

  when "orthogonalplus":
    if n eq 2 and q in [2,3,5] then
      return GL(n,q);
    else 
      return sub<GL(n, q)|GOPlus(n, q), mat>;
    end if;
  else:
    "can't identify form";
    return "unknown";
  end case;
end function;

/**************************************************/

/*given a classical group G with quasisimple group C for which N_GL(G) \neq N_GL(C), return an overgroup for N_GL(G) which is the conformal group N_GL(C) plus scalars

recognise classical fails - G doesn't contain quasisimple group
normaliser preserves form mod scalars

Adds scalars on to conformal group and calculate normaliser

class_form is ClassicalForms(group) fed in from main function

group preserves a classical form up to scalars and maybe absolutely

returns a record in group_norm format

contains_QS=RecogniseClassical=true if group contains q.s. classical

*****/

group_norm:=recformat<overgroup,cob,got_overgroup,full_norm, derived_group>;


NormaliserClassical:=function(group, class_form:contains_QS:=true)
  assert IsAbsolutelyIrreducible(group);
  n:=Dimension(group);
  q:=#BaseRing(group);
  z:= PrimitiveElement(GF(q));
  prim_scal:= GL(n, q)!ScalarMatrix(n, z);
  type:=class_form`formType;

  if n eq 2 and type in ["orthogonalplus","orthogonalminus"] then
  //can't get overgroup this way - QS group is not abs irred
    return rec<group_norm|got_overgroup:=false>;
  end if;

  if type eq "linear" then
    if contains_QS then 
      return rec<group_norm|overgroup:=GL(n,q), cob:=GL(n,q).0, got_overgroup:=true, full_norm:=true>;
    else return rec<group_norm|got_overgroup:=false>;
    end if;
  end if;

  if type eq "unitary" then
    f:=class_form`sesquilinearForm;
  elif IsEven(q) and type in ["orthogonalplus","orthogonalminus"] then
    f:=class_form`quadraticForm;
  else f:=class_form`bilinearForm;
  end if;

  mat:=TransformForm(f,type);
  //conjugates into subgroup of standard classical group
  nglc:=GetOvergroup(type,n,q);

  if contains_QS then
    //nglg=nglc except if group orthogonal, n even and q odd
    if IsEven(n) and IsOdd(q) and type in ["orthogonalplus", "orthogonalminus"] then
      ovgroup:=sub<GL(n,q)|nglc,prim_scal>;
      return rec<group_norm|overgroup:=ovgroup, cob:=mat, got_overgroup:=true, full_norm:=false>;

    else
      return rec<group_norm|overgroup:=nglc, cob:=mat, got_overgroup:=true, full_norm:=true>;
    end if;

  else 
    ovgroup:=sub<GL(n,q)|nglc,prim_scal>;
    return rec<group_norm|overgroup:=ovgroup, cob:=mat, got_overgroup:=true, full_norm:=false>;
end if;
end function;

/*****************************************/


NormaliserClassical_notAbsIrred:=function(group)
  n:=Dimension(group);
  q:=#BaseRing(group);
  z:= PrimitiveElement(GF(q));
  prim_scal:= GL(n, q)!ScalarMatrix(n, z);
  type:=ClassicalType(group);

  nglc:=GetOvergroup(type,n,q);

  if type eq "orthogonalplus" then
   H:=OmegaPlus(n,q);
    if #group eq #H then
     bool, x:=IsGLConjugate(group,H);
    else 
      H:=SOPlus(n,q);
      assert #group eq #H;
      bool, x:=IsGLConjugate(group,H);
    end if;

  else //type eq "orthogonalminus"
    H:=OmegaMinus(n,q);
    if #group eq #H then
     bool, x:=IsGLConjugate(group,H);
    else 
      H:=SOMinus(n,q);
      assert #group eq #H;
      bool, x:=IsGLConjugate(group,H);
    end if;
  end if;


  //nglg=nglc except if group orthogonal, n even and q odd
  if IsEven(n) and IsOdd(q) then
    ovgroup:=sub<GL(n,q)|nglc,prim_scal>;

    return rec<group_norm|overgroup:=ovgroup, cob:=x, got_overgroup:=true, full_norm:=false>;

  else
    return rec<group_norm|overgroup:=nglc, cob:=x, got_overgroup:=true, full_norm:=true>;
  end if;

end function;



