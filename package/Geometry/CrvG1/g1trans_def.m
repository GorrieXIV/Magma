freeze;

/***************************************************************

    Setting up the HackObj type TransG1

***************************************************************/

declare type TransG1;

declare attributes TransG1 : 
   Degree,          // = 2,3,4 or 5
   Scalar,          // for degrees 2 and 3, re-scaling of equation 
   Shift,           // for degree 2 when there are cross terms
   EquationMatrix,  // for degrees 4 and 5, action on equations 
   Matrix;          // action on variables
//   Determinant;   // e.g. Delta transforms by Det^12

// IMPORTANT: If the Degree attribute is assigned, then the attribute
// containing the defining data (for that degree) must also be assigned.

/*****************

     CHANGE LOG 
               
              **** Please record all changes here ****
                                      
  
                                       *************/ 

// REQUIRED INTRINSICS:

intrinsic Print(trans::TransG1, level::MonStgElt)
{}
  if not assigned trans`Degree then return; end if;
  n := trans`Degree;
  printf "Transformation of genus one models of degree %o given by\n",n;
//  IndentPush();
  if n in {2,3} then 
    printf "Scalar = %o\n",trans`Scalar;
  else
    printf "Change of equations matrix\n%o\n",trans`EquationMatrix;
  end if;
  if trans`Degree eq 2 and assigned trans`Shift then
    printf "Shift = %o\n",trans`Shift;
  end if;
  printf "Change of variables matrix\n%o",trans`Matrix;
//  IndentPop();
end intrinsic;
 
intrinsic IsCoercible(trans::TransG1, y::.) -> BoolElt, .
{}
 return false,_;
end intrinsic;

intrinsic 'in'(x::., trans::TransG1) -> BoolElt
{}
  return false;
end intrinsic;

// OPTIONAL INTRINSICS

// Do we really want to set up a parent object?
// intrinsic HackobjParentModelG1(x::.) -> .

intrinsic 'eq'(tr1::TransG1, tr2::TransG1) -> BoolElt
{True iff the transformations tr1 and tr2 have the same coefficients}
  if tr1`Degree ne tr2`Degree then return false; end if;
  flag := true;
  if tr1`Degree eq 2 then 
    r1 := assigned tr1`Shift select tr1`Shift else [0,0,0];
    r2 := assigned tr2`Shift select tr2`Shift else [0,0,0];
    flag := (r1 cmpeq r2);
  end if;
  if tr1`Degree in {2,3} then 
    flag := flag and (tr1`Scalar cmpeq tr2`Scalar);
  else
    flag := flag and (tr1`EquationMatrix cmpeq tr2`EquationMatrix);
  end if;
  return flag and (tr1`Matrix cmpeq tr2`Matrix);
end intrinsic;
   
/*
// precisely the object that used to *be* the genus one model
function OldData(model)
   n := model`Degree;
   if n in {2,3} then return model`Equation; 
   elif n eq 4 then return model`Equations; 
   elif n eq 5 then return model`DefiningMatrix; 
   end if;
end function;
*/
