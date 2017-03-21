freeze;

/////////////////////////////////////////////////////////////////////////
//   Short presentation for Omega(d, q)                                   //
//                                                                     //
//   Input two parameters to compute this presentation of Omega(d, q)     //
//     d = dimension                                                   //
//     q = field order                                                 //
// 
//   October 2012
/////////////////////////////////////////////////////////////////////////

import "plus.m": MyOmegaPlusPres;
import "minus.m": MyOmegaMinusPres;
import "circle.m": MyOmegaPres;

intrinsic int_StandardPresentationForOmega (d :: RngIntElt, F :: FldFin: 
     Projective := false, MinGens := true, Type := "Omega+") -> GrpSLP, []
{return standard presentation for Omega(d, F)} 
  
   require d gt 2: "Degree must be at least 3";
   return int_StandardPresentationForOmega(d, #F : Projective := Projective, 
	MinGens := MinGens, Type := Type);
end intrinsic;
 
intrinsic int_StandardPresentationForOmega (d :: RngIntElt, q :: RngIntElt: 
     Projective := false, MinGens := true, Type := "Omega+") -> GrpSLP, []
{return standard presentation for Omega(d, q)} 
  
   require d gt 2: "Degree must be at least 3";
   require IsPrimePower (q): "Field size is not valid";

   if IsOdd (d) then
      require IsOdd (q): "Field size must be odd";
      return MyOmegaPres (d, q: MinGens := MinGens);
   elif Type eq "Omega+" then
      return MyOmegaPlusPres (d, q: Projective := Projective);
   elif Type eq "Omega-" then
      return MyOmegaMinusPres (d, q: Projective := Projective, MinGens := MinGens);
   else 
     error "Must set type";
   end if;
end intrinsic;
