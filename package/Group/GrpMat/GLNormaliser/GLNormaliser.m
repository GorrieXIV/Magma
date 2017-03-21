freeze;

/*
contains:
GLNormaliser(G : Print) : GrpMat -> GrpMat

GLNormaliser takes a matrix group G and optional parameters Print, Overgroup and der_group.

If Overgroup:= true then the function returns a record in the norm_group format. Otherwise it just returns the normaliser in GL(n,q) of G, where n is the dimension of G and q is the size of the base field of G.

if Print:=a, where a is an integer greater than 0 then the function gives some information about which Aschbacher classes are being used to find an overgroup for G.
*/


import "NormaliserReducible.m":  NormaliserReducible;
import "NormaliserImprimitive.m": NormaliserImprimitive;
import "NormaliserSemilinear.m":  NormaliserSemilinear;
import "NormaliserSubfield.m": NormaliserSubfield;
import "NormaliserExtraspecial.m": NormaliserExtraspecial;
import "DerivedTrick.m": DerivedTrick;
import "NormaliserClassical.m" : NormaliserClassical;
import "GLNormaliser_functions.m" : get_derived_group, IsSolubleClassical;

group_norm:=recformat<overgroup, cob,got_overgroup,full_norm, derived_group>;
  



/**********************************************/

intrinsic GLNormaliser(group::GrpMat[FldFin]: Print:=0, Overgroup:=false, der_group:=0) -> GrpMat
{The normaliser of group in the general linear group}
  D:=der_group;
  got_overgroup:=false;
  n:=Dimension(group);
  q:=#BaseRing(group);
  full_norm:=false;

  if n eq 1 then
    if Print gt 0 then
      "Dimension 1";
    end if;
    N:=rec<group_norm | overgroup:=GL(n,q), cob:=GL(n,q).0, got_overgroup:=true, full_norm:=true, derived_group:=der_group>;
    got_overgroup:=N`got_overgroup;
  end if;
 
   if not got_overgroup and not (false in [IsScalar(g):g in Generators(group)]) then 
    if Print gt 0 then
      "Group is scalar";
    end if;
    N:=rec<group_norm | overgroup:=GL(n,q), cob:=GL(n,q).0, got_overgroup:=true, full_norm:=true, derived_group:=der_group>;
    got_overgroup:=N`got_overgroup;
  end if;

  if not got_overgroup then
    //filter out non abs irred classical gps
    if (not IsSolubleClassical(group,n,q)) and  RecogniseClassical(group) then
      //need group to not be soluble
      if Print gt 0 then
        "Classical, containing quasisimple group";
        "getting overgroup...";
      end if;
      if not (Type(D) eq GrpMat) then
        D:=DerivedGroupMonteCarlo(group);
      end if;
      //don't need to be sure D is the whole derived group. If D is abs irred then G' is abs irred.
      if IsAbsolutelyIrreducible(D) then         
        class_form:=ClassicalForms(group: Scalars:=true);
        N:=NormaliserClassical(group, class_form:contains_QS:=true);
        got_overgroup:=N`got_overgroup;
      end if;
    end if;
  end if;

  if not got_overgroup then
    if not IsIrreducible(group) then
      if Print gt 0 then
       "Reducible";
        "getting overgroup...";
      end if;
      N:=NormaliserReducible(group:Print:=Print);
      got_overgroup:=true; 
      //not really, but want to skip to the end 
    else
      if Print gt 0 then
        "Irreducible";
      end if;
    end if;
  end if;


  if not got_overgroup then
    if (not IsAbsolutelyIrreducible(group)) and (not ([n,q] eq [2,2])) then
      if Print gt 0 then
        "Not absolutely irreducible";
        "getting overgroup...";
      end if;
      N:=NormaliserSemilinear(group:der_group:=D);
      got_overgroup:=N`got_overgroup;
      if got_overgroup then 
        assert IsSemiLinear(N`overgroup);		
        //helps with normaliser calculation
      end if;

    else     
      if Print gt 0 then
        "Absolutely irreducible";
      end if;
    end if;
  end if;

  if not got_overgroup then
    is_subfield,small_field_gp:= IsOverSmallerField(group:Scalars:=false);
    if is_subfield then
      if Print gt 0 then
        "Subfield";
        "getting overgroup...";
      end if;
      N:=NormaliserSubfield(group,small_field_gp:Print:=Print);
      got_overgroup:=N`got_overgroup;
    end if;
  end if;

  //abs irred and not subfield

  if not got_overgroup then
    //see if it could be extraspecial
    fac:=Factorisation(n);
    if #fac eq 1 then
      r:=fac[1][1];
      right_order:=false;
      if IsOdd(r) then
        if not (false in [Order(g) eq r:g in Generators(group)]) then
          right_order:=true;
        end if;
      else
        if not (false in [IsDivisibleBy(4,Order(g)):g in Generators(group)]) then
          right_order:=true;
        end if;
      end if;  
      
      if right_order then
        og:=#group;
        bool, prime, order:= IsPrimePower(og);
        if bool and IsOdd(prime) then
          if (IsExtraSpecial(group) cmpeq true) and Exponent(group) eq prime then
            if not [n,q] in [[2,2],[2,3]] then
              if Print gt 0 then
                "Extraspecial";
                "getting overgroup...";
              end if;
              N:=NormaliserExtraspecial(group,og);
              got_overgroup:=N`got_overgroup;
            end if;
          end if;
        end if;
      end if;
    end if;
  end if;

  if not got_overgroup and IsPrimitive(group) cmpeq false then
    if Print gt 0 then
      "Imprimitive";
      "getting overgroup...";
    end if;
    N:=NormaliserImprimitive(group);
    got_overgroup:=N`got_overgroup;
    //full_norm is true if group preserves 2 block systems
  end if;

  if not got_overgroup and IsSemiLinear(group) cmpeq true then
    if Print gt 0 then
      "Semilinear";
      "getting overgroup...";
    end if;
    D:=der_group;
    N:= NormaliserSemilinear(group:der_group:=D);
    got_overgroup:=N`got_overgroup;
    if got_overgroup then 
      assert IsSemiLinear(N`overgroup); 	    
      //helps with normaliser calculation
    end if;
  end if;
    
  if not got_overgroup then       
    class_form:=ClassicalForms(group);
    form_type:=class_form`formType;
    if not (form_type eq "unknown")  and not (form_type eq "linear") then
      if not ((form_type in ["symplectic", "unitary"]) and (n eq 2)) then  
      //n=2 then conformal group = GL(n,q)
        if Print gt 0 then
          "Preserves", form_type, "form absolutely";
          "getting overgroup...";    
        end if;
        N:=NormaliserClassical(group, class_form: contains_QS:=false);
        got_overgroup:=N`got_overgroup;
      end if;
    end if;
  end if;
    
  if not got_overgroup then      
    if IsPerfect(group) then    //can't do derived trick
      if Print gt 0 then 
        "perfect";
      end if;
      N:=rec<group_norm| overgroup:=GL(n,q), cob:=GL(n,q).0, got_overgroup:=true, full_norm:=false>;
      got_overgroup:=N`got_overgroup;

    elif not Type(der_group) eq GrpMat then     
      D:=get_derived_group(group);
    else
      //check we've got full derived group
      RandomSchreier(group);
      RandomSchreier(D);
      if not IsNormal(group,D) then
        D:=get_derived_group(group);
      else
        quo:=group/D;      //takes long time
        if not IsAbelian(quo) then 
          D:=get_derived_group(group);
        end if;  
      end if;
    end if;

    if not got_overgroup then      
      if Print gt 0 then
        "derived trick";
        "getting overgroup...";
      end if;    
      N:=DerivedTrick(group: der_group:=D,Print:=Print);
    end if;
  end if;
   
  if Overgroup then
    return N;
  end if;

  overgroup:=N`overgroup;    
  cob:=N`cob;
  full_norm:=N`full_norm;
  if full_norm then
    return overgroup^cob^-1 ;
  end if;
  if Print gt 0 then
    "Finding normaliser...";
  end if;
  grp:=group^cob;
  RandomSchreier(grp);
  RandomSchreier(overgroup);
  assert grp subset overgroup;
  return (Normaliser(overgroup,grp))^(cob^-1);

end intrinsic;







