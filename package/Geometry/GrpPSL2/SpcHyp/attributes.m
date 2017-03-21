freeze;

/////////////////////////////////////////////////////////////
//                                                         //
//         Upper Half Plane                                //
//             Helena Verrill                              //
//    started May 2001                                     //
//                                                         //
//   upper_half_plane.m                                    //
//   This is the upper_half plane, together with the cusps,//
//   Which are the rationals and infinity                  //
//   In future this type could be extended to give other   //
//   hyperbolic spaces                                     //
//                                                         //
/////////////////////////////////////////////////////////////

import "creation.m":  HalfPlaneEltQuad;


/////////////////////////////////////////////////////////////
//                                                         //
//                    Attribute declarations               //
//                                                         //
//                                                         //
/////////////////////////////////////////////////////////////


declare type SpcHyp [SpcHypElt];
declare attributes SpcHyp:
   dimension,        //  currently dimension must be 1
   // the following only make sense for dimension 1
   scalar_field;      // for the case of Shimura curves:
   

declare type SpcHypElt;
declare attributes SpcHypElt:
   is_exact,       //  boolean
   is_cusp,        //  boolean   
   complex_value, //        
   exact_value,   //  field or cusp element
   /*
   D,             //  for is_exact: field = Q(root(D); 
                  //    D = 1 when is_cusp
  		  //    otherwise D=-1.
		  // for shimura curves, this gives second
		  // step of biquadratic extension.
   */
   parent;       

// alternatively could try defining this space as a coproduct   


////////////////////////////////////////////////////////////////
//                                                            //
//                     Printing                               //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic Print(X::SpcHyp, level::MonStgElt)
   {}
   printf "Upper half complex plane union cusps";
end intrinsic;


intrinsic Print(x::SpcHypElt, level::MonStgElt)
   {}
   if not x`is_cusp then       
      if x`is_exact then
	   u, v := Explode(Eltseq(x`exact_value));
	   KL := Parent(x`exact_value);
	   if Type(KL) eq FldQuad then
	      D := SquarefreeFactorization(Discriminant(KL));
	    else
	       f := DefiningPolynomial(KL);
	       D := -Integers()!Coefficient(f,0);
	   end if;
       else
	   u := Real(x`complex_value);
	   v := Imaginary(x`complex_value);
	   D := -1;
       end if;
       if u ne 0 then 
	   printf "%o", u;
	   if v ne 0 then printf " + "; end if;         
       end if;
       if v ne 0 then 
	   if v ne 1 then           
	       printf "(%o)*", v;
	   end if;
	   printf "root(%o)", D;
       end if;
       if v eq 0 and u eq 0 then printf "0";
       end if;
   else
       printf "%o", x`exact_value;
   end if;
end intrinsic;

////////////////////////////////////////////////////////////////
//                                                            //
//      Assign Names for I and Rho                           //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic '.' (H::SpcHyp,i::RngIntElt) -> SpcHypElt
    {}    
    require i eq 1 or i eq 2 : "Invalid index.";
    if i eq 1 then
	H:=UpperHalfPlaneWithCusps();
	K := QuadraticField(-1);
	I := HalfPlaneEltQuad(H,K.1);
	return I;
    else
	H:=UpperHalfPlaneWithCusps();
	L := QuadraticField(-3);
	Rho := HalfPlaneEltQuad(H,(1+L.1)/2);
	return Rho;
    end if;
end intrinsic;


intrinsic AssignNames(~H::SpcHyp, S::[MonStgElt])
    {Assign names to elliptic points.}
    i := #S;
    require  (i eq 0 or i eq 1 or i eq 2):
    "The length of argument 2 must be at most 2.";
end intrinsic;


intrinsic Name(G::SpcHyp,i::RngIntElt) -> GrpPSL2Elt
  {An elliptic point.}
    require  (i eq 0 or i eq 1 or i eq 2):
    "The length of argument 2 must be at most 2.";
  return G.i;
end intrinsic;
