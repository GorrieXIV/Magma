freeze;

// need to change so different types can be output by function
// which returns infinity or rationals or something else.

////////////////////////////////////////////////////////////////////
//                                                                //
//                        Arithmetic                              //
//                                                                //
////////////////////////////////////////////////////////////////////

import "coercion.m": init_psl2_elt;

intrinsic '-' (A::GrpPSL2Elt) -> GrpPSL2Elt
   {for elements of PSL_2(Z)}

  return init_psl2_elt(Parent(A), -A`Element);
end intrinsic;


intrinsic '*' (A::GrpPSL2Elt,B::GrpPSL2Elt) -> GrpPSL2Elt
    {"} // "
    GA := Parent(A);
    GB := Parent(B);
    if GA`BaseRing cmpeq GB`BaseRing then
      if assigned GA`IsShimuraGroup and assigned GB`IsShimuraGroup then
        return init_psl2_elt(GA, A`Element*B`Element);
      end if;
       if GA eq GB then
 	    return init_psl2_elt(GA, A`Element*B`Element);
	else
	    P := PSL2(GA`BaseRing);
	    return init_psl2_elt(P, A`Element*B`Element);
	end if;
    end if;		
    error if true, "Incompatible base rings.";
end intrinsic;
    
intrinsic '*' (A::GrpPSL2Elt,z::FldComElt) -> FldComElt
   {"} // "
    // Action on the upper half plane:
    require Imaginary(z) ge 0 : 
    "Argument 2 must be in the upper half plane";
    a,b,c,d := Explode(Eltseq(A`Element));
    // may be an error here! since might coerce in different ways into C!
    if not (Parent(a) cmpeq Integers()
       or Parent(a) cmpeq Rationals()) then       
       a,b,c,d := Explode([Conjugates(x)[1] : x in (Eltseq(A`Element))]);
    end if;
    if (c*z + d) ne 0 then 
       return (a*z+b)/(c*z+d);
    else
       return Infinity();
    end if;
end intrinsic;

intrinsic '*' (A::GrpPSL2Elt,z::RngIntElt) -> FldRatElt
   {"} // "
   // Action on the upper half plane:
   a,b,c,d := Explode(Eltseq(A`Element));
    if (c*z + d) ne 0 then 
       return (a*z+b)/(c*z+d);
    else
       return Infinity();
    end if;
end intrinsic;

/*
// warning, the following does not seem to get caught!!!
intrinsic '*' (A::GrpPSL2Elt,z::Infty) -> FldRatElt
   {"} // "
   // Action on the upper half plane:
   print 4;
   a,b,c,d := Explode(Eltseq(Matrix(A)));
    if c ne 0 then 
       return a/c;
    else
       return Infinity();
    end if;
end intrinsic;
*/

intrinsic '*' (A::GrpPSL2Elt,z::FldRatElt) -> FldRatElt
   {"} // "
   // Action on the upper half plane:
   a,b,c,d := Explode(Eltseq(A`Element));
    if (c*z + d) ne 0 then 
       return (a*z+b)/(c*z+d);
    else
       return Infinity();
    end if;
end intrinsic;


 /*
intrinsic '*' (A::AlgMatElt,z::SetCspElt) -> RngElt
    {"} // "
    // Action on the upper half plane:
    a,b,c,d := Explode(Eltseq(A));
    z1,z2 := Explode(Eltseq(z));
    // following may not always work!
    return (a*z1+b*z2)/(c*z1+d*z2);
end intrinsic;
*/


intrinsic '*' (A::GrpPSL2Elt,z::SpcHypElt) -> SpcHypElt
   {"} // "
   // Action on elements of upper half plane union cusps:
   if assigned Parent(A)`IsShimuraGroup then
     a,b,c,d := Explode(Eltseq(Matrix(A)));
     return Parent(z)!((a*z`complex_value+b)/(c*z`complex_value+d));
   end if;

   a,b,c,d := Explode(Eltseq(A`Element));
   if IsCusp(z) and Type(ExactValue(z)) eq SetCspElt then
      //	require Type(a) in {FldRatElt, RngIntElt}:
      //	"Argument 1 must be defined over the rationals " *
      //	"or integers when argument 2 is a cusp.";
      //      warning : possibly this may not return cusps when
      //      applied to cusps.
      u,v := Explode(Eltseq(z`exact_value));
      if c*u+d*v eq 0 then
	 return Parent(z)!Cusps()![1,0];
      else
	 frac := (a*u + b*v)/(c*u+d*v);
	 return Parent(z)!frac; //frac;	   
      end if;
   // elif z`is_exact and  (Type(a) in [FldRatElt,RngIntElt]) then
   elif z`is_exact then
      // In the exact case, assume either that a,b,c, and d are rationals
      // or integers, or that they are elements of a
      // fixed real quadratic field K, and ze is in 
      // some relative (quadratic) extension of K.       	
      ze := z`exact_value;
      if (c*ze+d) eq 0 then
	 return Parent(z)!Cusps()![1,0];
      else
	 frac := (a*ze+b)/(c*ze+d);
	 return Parent(z)!frac;
      end if;
   else
      // in the none exact case, assume that a,b,c, and d are
      // either elements
      // of the integers or rationals, OR are elements
      // of a real quadratic field.
      // if not, use the following hack:
      if Type(Parent(a)) eq FldRe then
        a,b,c,d := Explode(Eltseq(A`Element));
      elif not (Parent(a) cmpeq Integers()
	 or Parent(a) cmpeq Rationals()) then       
	 a,b,c,d := Explode([Conjugates(x)[1] : x in (Eltseq(A`Element))]);
      end if;
      if (c*z`complex_value+d) eq 0 then
	 return Parent(z)!Infinity();
      else	  
	 return Parent(z)!((a*z`complex_value+b)/
	 (c*z`complex_value+d));
      end if;
   end if;
end intrinsic;


intrinsic '*' (A::GrpPSL2Elt,z::SetCspElt) -> SetCspElt
    {"} // "
    a,b,c,d := Explode(Eltseq(A`Element));
    u,v := Explode(Eltseq(z));
    if c*u+d*v eq 0 then
	return Cusps()![1,0];
    else
	frac := (a*u + b*v)/(c*u+d*v);
	return Cusps()!frac;
    end if;
end intrinsic;


intrinsic '*' (A::GrpPSL2Elt,z::[SpcHypElt]) -> SeqEnum
    {"} // "
    // Action on elements of upper half plane union cusps:
    require Universe(z) eq UpperHalfPlaneWithCusps():
    "The action of congruence subgroups is defined on elements
    of the upper half plane union the cusps,
    and sequences of such elements only";
    // this line was not previously needed, so the fact
    // it is may indicate the presence of a bug somewhere.
    P := Parent(z[1]);
    // also need a futher coercion statement!
    // need to find out why this should be needed
    // there are examples where the parent is wrong
    // if this is not included.
    PP := Parent(z);
    return [P|A*x : x in z];
end intrinsic;

intrinsic '*' (A::GrpPSL2Elt,z::[SetCspElt]) -> SeqEnum
   {"} // "
   // Action on elements of upper half plane union cusps:
   require Universe(z) eq Cusps():
   "The action of congruence subgroups is defined on elements
   of the upper half plane union the cusps,
   and sequences of such elements only";
   P := Parent(z[1]);
   return [P|A*x : x in z];
end intrinsic;


intrinsic '*' (A::GrpPSL2Elt,z::[FldRatElt]) -> SeqEnum
   {"} // "
   // Action on elements of upper half plane union cusps:
   require Universe(z) eq Rationals():
   "The action of congruence subgroups is defined on elements
   of the upper half plane union the cusps,
   and sequences of such elements only";
   P := Parent(z[1]);
   return [P|A*x : x in z];
end intrinsic;



intrinsic '^' (A::GrpPSL2Elt,k::RngIntElt) -> GrpPSL2Elt
   {"} // "
   // note, in finding A^k, we must remember that the element
   // defining A, while invertible projectively, might not be
   // invertible in the MatrixGroup of the Parent of A.

   if assigned Parent(A)`IsShimuraGroup and Parent(A)`IsShimuraGroup then
     return Parent(A)!((A`Element)^k);
   end if;

   e := A`Element;
   if k gt 0 then
      s := Eltseq(e^k);
      return Parent(A)!s;
   elif k lt 0 then
      s := Eltseq(Adjoint(e)^(-k));
      return Parent(A)!s;
   else
      return Parent(A)!1;
   end if;
end intrinsic;
