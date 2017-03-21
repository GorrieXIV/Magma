freeze;

/* function names in this file:
TestExtraSpec(grp)
IsGLConjugateExtraspecial(H, K: Print)
*/

/**********************************************************
These functions looks for an element of GL(d, q) which will
conjugate H to K. They are assumed to be extraspecial groups. 

We find the extraspecial normal subgroups extraspec1 and extraspec2
of order p^(1+2r). Since they can be represented by monomial
matrices, we can use the function ConjImprim to conjugate them to one
another. We then need only check in their normaliser for a conjugating
element.

The only problem we may have is that it is possible that there are two
extraspecial subgroups of the same order. This can only occur if the
extraspecial group has order 2^(1+2m) where d:= 2^m. In this case we
may need to take a random conjugate several times to ensure success.

***********************************************************************
***********************************************************************/

//this function is just because IsExtraSpecialNormaliser changes its
//mind. 
function TestExtraSpec(grp)
  for i in [1.3] do
    if IsExtraSpecialNormaliser(grp) cmpeq true then
      return true;
    elif IsExtraSpecialNormaliser(grp) cmpeq false then
      return false;
    end if;
  end for;
  return "unknown";
end function;

/**********************************************************************/
//the main function: input two matrix groups of same degree and 
//fieldsize. 

intrinsic IsGLConjugateExtraspecial(H::GrpMat, K::GrpMat: Print:=0) -> BoolElt, GrpMatElt 
{If conjugates of H and K are conjugate inside an extraspecial normaliser 
then returns true and a matrix conjugating H to K. Otherwise 
returns "unknown".}
  d:= Degree(H);
  require d eq Degree(K): "Groups must have same dimension";
  q:= #BaseRing(H); 
  require q eq #BaseRing(K): "Groups must be over same field";
 

  require IsAbsolutelyIrreducible(H) : "Groups must be absolutely irreducible";
  require IsAbsolutelyIrreducible(K) : "Groups must be absolutely irreducible";


  proc:= RandomProcess(GL(d, q));
  
  //function TestExtraSpec is because IsExtraSpecialNormaliser
  //occasionally changes its mind. 
  extra_H:= TestExtraSpec(H); extra_K:= TestExtraSpec(K);
  if not (extra_H cmpeq true) then return "unknown", _; end if;
  if not (extra_K cmpeq true) then return "unknown", _; end if;

  //pull out the extraspecial subgroups
  ext1:= ncl<H|ExtraSpecialGroup(H)>;
  ext2:= ncl<K|ExtraSpecialGroup(K)>;
  ext_order:= #ext1;
  if ext_order lt 129 then small:= true; 
  else small:= false; end if;

  if Print gt 0 then 
    "conjugating normal subgroups to each other";
  end if;
  //use is IsGLConjugateImprimitive to conjugate the extraspecial
  //groups to one another, as both are conjugate to groups of 
  //monomial matrices. 
  H_conj_temp:= GL(d, q).0;
  K_conj_temp:= GL(d, q).0;
  a:= false;
  for i in [1..50] do
    temp_H:= H^H_conj_temp;
    temp_K:= K^K_conj_temp;
    
    temp_H_extra:= TestExtraSpec(temp_H);
    if not temp_H_extra cmpeq true then return "unknown"; end if;
    H_extraspec:= ExtraSpecialGroup(temp_H);

    temp_K_extra:= TestExtraSpec(temp_K);
    if not temp_K_extra cmpeq true then return "unknown", _; end if;
    K_extraspec:= ExtraSpecialGroup(temp_K);

    for j in [1..5] do
      if small then 
        if not (IdentifyGroup(H_extraspec) eq IdentifyGroup(K_extraspec)) then
          break;
        end if;
      end if;
      a, conj:= IsGLConjugateImprimitive(H_extraspec, K_extraspec:Print := Print-1);
      if (a cmpeq true) then
        conj1:= H_conj_temp*conj*K_conj_temp^-1;
        break i;
      end if;
    end for;
  end for;

  /* The following if statement should *never* be acted on , since 
   * extraspecial groups + 2-grps of symplectic type can be represented
   * by monomial matrices.
   */
  if not (a cmpeq true) then
    if Print gt 0 then
      "couldn't conjugate extra-special groups to one another";
    end if;
    return "unknown", _;
  end if;

  new_H:= H^conj1;

  /* Now the two groups have identical extraspecial parts, so we can look
   * inside the full normaliser of the extraspecial group - making sure
   * to choose the correct extraspecial group! 
   */
  if Print gt 0 then "computing overgroup"; end if;
  overgroup:= Normaliser(GL(d, q), K_extraspec^(K_conj_temp^-1));
  phi, ov_p:= OrbitAction(overgroup, RSpace(overgroup).1);

  //finally ask if they're conjugate in the extraspecial normaliser.
  if Print gt 0 then "checking conjugacy in overgroup"; end if;
  a, conj2:= IsConjugate(ov_p, new_H@phi, K@phi);
  if a then
    return true, conj1*(conj2@@phi);
  end if;
  return "unknown", _;
end intrinsic;







