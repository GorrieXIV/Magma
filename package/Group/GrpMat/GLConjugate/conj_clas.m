freeze;

/* function names in this file:
SameForm(H, K, d, p, type)
WhichForm(H, K, d, q)
GetOvergroup(type, d, q, group)
IsGLConjugateClassical(H, K: Print)
IsGLConjugateBigClassical(H, K: Print)
*/
//There's a file correct_form.m which Derek has, and also form.m 

import "correct_form.m": CorrectForm;
import "form.m": OrthogonalFormIGLC, SymplecticFormIGLC, UnitaryFormIGLC;

/***********************************************************/

//this function just checks for each type of form to see if H and 
//K both preserve a form of that type.
SameForm:= function(H, K, d, p, type)

  if type cmpeq "symplectic" then
    bool1, form1:= SymplecticFormIGLC(H);
    bool2, form2:= SymplecticFormIGLC(K);
  elif type cmpeq "unitary" then
    bool1, form1:= UnitaryFormIGLC(H, d, p);
    bool2, form2:= UnitaryFormIGLC(K, d, p);
  elif (type eq "orth" and IsOdd(d)) or 
        (type in {"orth+", "orth-"} and IsOdd(p) and IsEven(d)) then
    bool1, sort1, form1:= OrthogonalFormIGLC(H, d, p);
    bool2, sort2, form2:= OrthogonalFormIGLC(K, d, p);
  elif (type in {"orth+", "orth-"} and IsEven(p) and IsEven(d)) then
    bool1, form1, sort1:= QuadraticForm(H); 
    bool2, form2, sort2:= QuadraticForm(K);
    if bool1 then
      if sort1 eq "orthogonalminus" then sort1:= "orth-"; 
      elif sort1 eq "orthongalplus" then sort1:= "orth+";
      end if;
    end if;
    if bool2 then
      if sort2 eq "orthogonalminus" then sort2:= "orth-"; 
      elif sort2 eq "orthogonalplus" then sort2:= "orth+";
      end if;
    end if;
  else 
    bool1:= false;
    bool2:= false;  
  end if;

  if not (bool1 eq bool2) then
    return false, _, _, _;
  end if;
  if bool1 then
    if type eq "symplectic" or type eq "unitary" then
      return true, form1, form2, type;
    elif sort1 eq sort2 then
      return true, form1, form2, sort1;
    end if;
  end if;
  return false, _, _, _;
end function;

/************************************************************************
 * WhichForm finds a type of form that is preserved by both H and
 * K, and returns the relevant form matrices. If it discovers
 * that H and K preserve different types of forms it returns
 * false, as H and K are then clearly not conjugate. 
 *
 */

WhichForm:= function(H, K, d, q);

  is_square, p:= IsSquare(q);

  for x in ["orth", "orth+", "orth-", "symplectic", "unitary"] do
    if x eq "unitary" and is_square then
      bool, form1, form2, type:= SameForm(H, K, d, p, x);
    elif not x eq "unitary" then
       bool, form1, form2, type:= SameForm(H, K, d, q, x);
    end if;
    if bool then
      return true, type, form1, form2;
    end if;
  end for;

  //"can't find matching form";
  return false, "unknown", _, _;
end function;
        
/********************************************************************/

//This constructs the maximal subgroup of GL(d, q) to preserve a form
//of type type. 

GetOvergroup:= function(type, d, q)
  z:= PrimitiveElement(GF(q));
  case (type):
  when "symplectic":
    if IsOdd(q) then
      mat:= GL(d, q)!DiagonalMatrix([z : i in [1..(d div 2)]] cat 
                       [1 : i in [((d div 2) + 1)..d]]);
      overgroup:= sub<GL(d, q)|Sp(d, q), mat>;
    else
      overgroup:= sub<GL(d, q)|Sp(d, q)>;
    end if;
    form_over:= GL(d, q)!Matrix(GF(q), d, d, [<i, d-i+1, 1> : i in
          [1..Floor(d/2)]] cat [<i, d-i+1, -1> : i in [Floor(d/2)+1..d]]); 
  when "unitary":
    overgroup:= sub<GL(d, q)|GU(d, Integers()!Round(Sqrt(q)))>;
    form_over:= GL(d, q)!Matrix(GF(q), d, d, [<i, d-i+1, -1>:i in [1..d]]);
  when "orth":
    overgroup:= sub<GL(d, q)|GO(d, q)>;
    a, b, form_over:= OrthogonalFormIGLC(overgroup, d, q);
  when "orth-":
    overgroup:= CGOMinus(d, q);
    if IsEven(q) then
      bool, form_over:= QuadraticForm(GOMinus(d, q));
    else
      a, b, form_over:= OrthogonalFormIGLC(GOMinus(d, q), d, q);
    end if;
  when "orth+":
    overgroup:= CGOPlus(d, q);
    if IsEven(q) then
      bool, form_over:= QuadraticForm(GOPlus(d, q));
    else
      a, b, form_over:= OrthogonalFormIGLC(GOPlus(d, q), d, q);
    end if;
  else:
      "can't identify form";
      return "unknown", _; 
  end case;
  return overgroup, form_over;
end function;



/**********************************************************************
This function seeks to find an element of GL(d, q) which will
conjugate H to K.
We find the matrix of the form that they are preserving, and then
conjugate them so that they preserve the same form. We then look
inside the appropriate classical group for a conjugating element. 
*****************************************************************/

intrinsic IsGLConjugateClassical(H::GrpMat, K::GrpMat: Print:=0) -> BoolElt, GrpMatElt 
{If conjugates of H and K are conjugate inside a classical group, then
returns true and a matrix conjugating H to K. If H and K are shown 
not to be conjugate inside the general linear group then
returns false. Otherwise, returns "unknown" }
  d:= Degree(H);
  require d eq Degree(K): "Groups must have same dimension";
  q:= #BaseRing(H); 
  require q eq #BaseRing(K): "Groups must be over same field";

  require IsAbsolutelyIrreducible(H) : "Groups must be absolutely irreducible";
  require IsAbsolutelyIrreducible(K) : "Groups must be absolutely irreducible";

  //first we find a good form to work with.
  if Print gt 0 then "Determining form"; end if;
  bool, type, form1, form2:= WhichForm(H, K, d, q);
  if not bool then
    if Print gt 0 then "Can't find matching form"; end if;
    if type cmpeq "unknown" then
      return "unknown", _;
    else
      return false, _;
    end if;
  end if;
  if Print gt 0 then "Form type =", type; end if;
  
  //next we make the relevant classical group 
  if Print gt 0 then "making overgroup"; end if;
  overgroup, form_over:= GetOvergroup(type, d, q);
  //hom, ov_hom:= OrbitAction(overgroup, RSpace(overgroup).1);

  //now we conjugate all three groups to preserve the same form.
  conj_over:= GL(d, q)!CorrectForm(form_over, d, q, type);
  conj1:= GL(d, q)!CorrectForm(form1,  d, q, type);
  new_H:= H^(conj1*conj_over^-1);
  conj2:= GL(d, q)!CorrectForm(form2, d, q, type);
  new_K:= K^(conj2*conj_over^-1);

  //now check conjugacy in the overgroup
  if Print gt 0 then "doing final conjugacy check"; end if;
  bool, final_conj:= IsConjugate(overgroup, new_H, new_K);

  if bool then 
    return true,conj1*conj_over^-1*final_conj*conj_over*(conj2)^-1; 
  else      
    return false, _;
  end if;

  //if Print gt 0 then "Not conjugate in overgroup"; end if;
  //return "unknown", _;
end intrinsic;



/* Note that when used as part of IsGLConjugate this function will never find 
     groups containing SL, as they
     are conjugate if and only if they are equal, and so will already have been
     dealt with. However, if used directly then it might. */

intrinsic IsGLConjugateBigClassical(H::GrpMat, K::GrpMat: Print:= 0) -> BoolElt
{If conjugates of H and K both contain a classical group Omega and
 sit inside a classical group Delta, then
returns true and a matrix conjugating H to K. If H and K are shown 
not to be conjugate inside the general linear group then
returns false. Otherwise, returns "unknown" }
   d:= Degree(H);
  require  d eq Degree(K): "Groups must have same dimension";
  q:= #BaseRing(H); 
  require q eq #BaseRing(K): "Groups must be over same field";

  //avoid some irritating small cases.//
  if d eq 2 and q in [2, 3] then return "unknown", _; end if;

  require IsAbsolutelyIrreducible(H): "Groups must be absolutely irreducible";
  require IsAbsolutelyIrreducible(K): "Groups must be absolutely irreducible";

  cl_h:= RecogniseClassical(H : NumberOfElements:= 100); 
  cl_k:= RecogniseClassical(K : NumberOfElements:= 100);

  //RecogniseClassical can be a bit flaky, so this is set not to say they're NOT conjugate
  //if these don't agree.
  if not (cl_h and cl_k) then
    return "unknown", _;
  end if;
  /* so now both H and K definitely contain classical groups in their natural rep */

  type_h:= ClassicalType(H);
  type_k:= ClassicalType(K);

  if not (type_h eq type_k) then
     if Print gt 0 then "Groups contain classical groups of different types"; end if;
     return false, _;
  end if;
  /* so now both H & K contain quasisimple classical groups of the same type */
  if type_h eq "unitary" then bool, r_q:= IsSquare(q); end if;

   /* we eliminate the classical groups whose Omega-group is soluble */
   if (d eq 2) and (type_h in ["orthogonalplus", "orthogonalminus"]) then
        return "unknown", _;
   elif ([d, q] eq [3, 4]) and (type_h eq "unitary") then 
        return "unknown", _;
   elif ([d, q] eq [3, 3]) and (type_h eq "orthogonalcircle") then 
        return "unknown", _;
   elif (d eq 4) and  (q in [2, 3]) and (type_h eq "orthogonalplus") then
        return "unknown", _;
   end if; 


  if type_h eq "linear" then
      if Print gt 0 then "linear : testing equality"; end if;
      if H eq K then
          return true, GL(d, q).0;
      else
          return false, _;
      end if;     
  end if;
  /*After this point, form type is NOT linear*/
   
  /*Now get the form matrix*/
  if type_h eq "unitary" then
     bool_h, form_h:= UnitaryForm(H : Scalars:= true);
     bool_k, form_k:= UnitaryForm(K : Scalars:= true);
 elif type_h eq "symplectic" then
     bool_h, form_h:= SymplecticForm(H : Scalars:= true);
     bool_k, form_k:= SymplecticForm(K : Scalars:= true);
  elif type_h in ["orthogonalplus", "orthogonalminus", "orthogonalcircle"] then
     if IsOdd(q) then 
        bool_h, form_h:= SymmetricBilinearForm(H : Scalars:= true);
        bool_k, form_k:= SymmetricBilinearForm(K : Scalars:= true);
     else
        bool_h, form_h:= QuadraticForm(H : Scalars:= true);
        bool_k, form_k:= QuadraticForm(K : Scalars:= true);
     end if;
  end if;
  if Print gt 0 then "Form type is", type_h; end if;

  //this should never happen but easier for testing
  if not (bool_h eq bool_k) then
    return "unknown", _;
  end if;

 //Conjugate H & K to preserve Magma's standard form.
   conj_1:= TransformForm(form_h, type_h);
   new_h:= H^conj_1;
   conj_2:= TransformForm(form_k, type_k);
   new_k:= K^conj_2;

   //normaliser of quasisimple is cyclic plus scalars, so once they preserve the same form, 
   //groups either equal or not conj in GL
   if type_h in ["unitary", "symplectic", "orthogonalcircle"] or IsEven(q) then
     if new_h eq new_k then
         return true, conj_1*(conj_2^-1);
     else
         return false, _;
     end if;
   end if;

  //more complicated normaliser in GL, so test conjugacy: everything from this point is O+ and O-
  //and q is odd. 
  if type_h eq "orthogonalplus" then 
      overgroup:= CGOPlus(d, q);
  elif type_h eq "orthogonalminus" then
      overgroup:= CGOMinus(d, q);
  end if;

   if Print gt 0 then "Making perm rep"; end if;
   hom, ov_hom:= OrbitAction(overgroup, RSpace(overgroup).1);
 
   //And now test conjugacy in the overgroup for remaining orthogonal cases
   if Print gt 0 then "doing final conjugacy check"; end if;
   bool, final_conj:= IsConjugate(ov_hom, (new_h)@hom, (new_k)@hom);

   if bool then
      return true, conj_1*(final_conj@@hom)*conj_2^(-1);
   else
      return false, _;
   end if;
end intrinsic;










