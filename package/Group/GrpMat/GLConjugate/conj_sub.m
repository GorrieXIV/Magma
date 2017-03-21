freeze;

/* 
 Function names in this file:
 IsGLConjugateSubfield(H, K: Print)
 */

//If G and H can be shown to be conjugate inside some GL(d, q_0) then
//return true and a conjugating element. If can be shown not to be 
//conjugate in GL then return false. Otherwise return unknown.
//If print gt 0 then we print progress reports, and reason why 
//unknown or false is returned.
intrinsic IsGLConjugateSubfield(H::GrpMat, K::GrpMat: Print:=0) 
-> BoolElt, GrpMatElt 
{If conjugates of H and K are shown to be conjugate in a maximal
subfield subgroup of the general linear group then returns true and a 
matrix conjugating H to K. If H and K are shown not to be 
conjugate in the general linear group then returns false. 
Otherwise returns "unknown".} 


  d:= Degree(H);
  require d eq Degree(K): "Groups must have same dimension";
  p:= #BaseRing(H); 
  require p eq #BaseRing(K): "Groups must be over same field";

  require IsAbsolutelyIrreducible(H) : "Groups must be absolutely irreducible";
  require IsAbsolutelyIrreducible(K) : "Groups must be absolutely irreducible";

  

  //we check that they are both subfield groups. x1 and x2 are the
  //images of the part of the group that is conjugate to a subgroup of
  //GL(d, smallfield), written AS a subgroup of GL(d, smallfield), so we 
  //coerce back into the larger field for later. 
  if Print gt 0 then "checking are subfield groups"; end if;
  H_subfield, x1:= IsOverSmallerField(H);
  K_subfield, x2:= IsOverSmallerField(K);
  
  if not (H_subfield cmpeq K_subfield) then 
     return false, _;
  end if;
    
  if H_subfield cmpeq true then
    strong_subfield:= true;
  else  
    H_subfield:= IsOverSmallerField(H: Scalars:= true);
    K_subfield:= IsOverSmallerField(K: Scalars:= true);
    strong_subfield:= false;
  end if;
    
  if not (H_subfield cmpeq K_subfield) then
    return false, _; 
  elif not (K_subfield cmpeq true) then
    return "unknown", _;
  end if;

  if not H`SmallerField eq K`SmallerField then
    return false, _;
  end if;

  
  conj1:= GL(d, p)!H`SmallerFieldChangeOfBasis;
  conj2:= GL(d, p)!K`SmallerFieldChangeOfBasis;

  H1:= sub<GL(d, p)| [conj1^-1*(H.i)*conj1 : i in [1..Ngens(H)]]>;
  K1:= sub<GL(d, p)| [conj2^-1*(K.i)*conj2 : i in [1..Ngens(K)]]>;
  
  if Print gt 0 then "constructing overgroup"; end if;
  sub_field:= H`SmallerField;
  z:= PrimitiveElement(GF(p));
  scal:= GL(d, p)!ScalarMatrix(d, z);
  overgroup:= sub<GL(d, p)|GL(d, sub_field).1, GL(d, sub_field).2, scal>;
  //phi, ov_perm:= OrbitAction(overgroup, RSpace(overgroup).1);

  if Print gt 0 then "testing conjugacy in overgroup"; end if;
  bool, conj_mat:= IsConjugate(overgroup, H1, K1);
  if not bool then 
    if strong_subfield then
      return false, _;
    else
      return "unknown", _; 
    end if;
end if;

  return true, conj1*conj_mat*(conj2^-1);

end intrinsic;









