freeze;

/***************************************************************

    Setting up the HackObj type ModelG1

***************************************************************/

declare attributes ModelG1 : 
   Degree,          // = 2,3,4 or 5
   Eltseq,
   Equation,        // for degree 2 or 3, the defining equation
   Equations,       // for degree 4, the defining equation
                    // and for degree 5, the associated equation
   DefiningMatrix,  // for degree 5, the matrix the defines the model
   CoveringCovariants,
   Discriminant;

// IMPORTANT: If the Degree attribute is assigned, then the attribute
//            containing the defining data (for that degree) must also be assigned.

/*****************

     CHANGE LOG 
               
              **** Please record all changes here ****
  
  November 2006, Tom:
     * 'eq' changed to just test coefficients (not polynomial rings)
     * New format for printing of models of degree 2 with the cross terms
           (immitating elliptic curves)
     * Degree 4 models now printed without [ ]. 
  
  TO DO : Make equations indent after first line (as for curves)
                                    
                                         *************/ 


// REQUIRED INTRINSICS:

intrinsic HackobjPrintModelG1(model::ModelG1, level::MonStgElt)
{}
  if not assigned model`Degree then return; end if;
  if model`Degree eq 2 then
    f := model`Equation;
    if VariableWeights(Parent(f)) eq [1,1,2] then
      R<x,z,y> := Parent(f);
      MC := MonomialCoefficient;
      quadric := &+[MC(f,mon*y)*mon : mon in [x^2,x*z,z^2]];
      quartic := -&+[MC(f,mon)*mon : mon in [x^4,x^3*z,x^2*z^2,x*z^3,z^4]];
      if quadric eq 0 then 
        printf "Genus one model of degree 2 defined by %o = %o over %o", y^2, quartic, BaseRing(model);
      else
        printf "Genus one model of degree 2 defined by %o + (%o)*%o = %o over %o", y^2, quadric, y, quartic, BaseRing(model);
      end if;
    else
      printf "Genus one model of degree 2 defined over %o given by \n%o", BaseRing(model), model`Equation;
    end if;
  elif model`Degree eq 3 then
     printf "Genus one model of degree 3 defined over %o given by \n%o", BaseRing(model), model`Equation;
  elif model`Degree eq 4 then
     printf "Genus one model of degree 4 defined over %o given by \n%o\n%o", BaseRing(model), (model`Equations)[1], (model`Equations)[2];
  else 
     printf "Genus one model of degree 5 defined over %o given by the matrix \n%o", BaseRing(model), model`DefiningMatrix;
  end if;
end intrinsic;

/* apparently not required, after all ... and when defined, it causes problems
(the problem is that it gets called and prints $ for the name if the model
ever had a name!)
intrinsic HackobjPrintNamedModelG1(model::ModelG1, level::MonStgElt, 
                                                               name::MonStgElt)
{}
  if not assigned model`Degree then return; end if;
  if model`Degree in {2,3} then
     printf "Genus one model %o of degree %o given by \n%o", 
            name, model`Degree, model`Equation;
  elif model`Degree eq 4 then
     printf "Genus one model %o of degree %o given by \n%o", 
            name, 4, model`Equations;
  else 
     printf "Genus one model %o of degree %o given by the matrix \n%o", 
            name, 5, model`DefiningMatrix;
  end if;
end intrinsic;
*/
 
intrinsic HackobjCoerceModelG1(model::ModelG1, y::.) -> BoolElt, .
{}
  return false;
end intrinsic;

intrinsic HackobjInModelG1(x::., model::ModelG1) -> BoolElt
{}
  return false;
end intrinsic;

intrinsic HackobjIndexedTypeModelG1(model::ModelG1, i::RngIntElt) -> Rng
{}
  return CoefficientRing(model);
end intrinsic;

// OPTIONAL INTRINSICS

intrinsic 'eq'(x::ModelG1, y::ModelG1) -> BoolElt
{True iff the genus one models x and y have the same coefficients}
   if x`Degree ne y`Degree then return false; end if;

   if x`Degree eq 2 then 
     xx := Eltseq(x);
     yy := Eltseq(y);
     if #xx eq 5 and #yy eq 8 then xx := [0,0,0] cat xx; end if;
     if #xx eq 8 and #yy eq 5 then yy := [0,0,0] cat yy; end if;
     return xx cmpeq yy;
   end if;

   return Eltseq(x) cmpeq Eltseq(y);

end intrinsic;
   
   
// precisely the object that used to *be* the genus one model
function OldData(model)
   n := model`Degree;
   if n in {2,3} then return model`Equation; 
   elif n eq 4 then return model`Equations; 
   elif n eq 5 then return model`DefiningMatrix; 
   end if;
end function;
