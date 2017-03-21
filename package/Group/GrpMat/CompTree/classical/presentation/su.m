freeze;

/////////////////////////////////////////////////////////////////////////
//   standard presentation for SU(n, q)                                //
//                                                                     //
//   Input two parameters to compute this presentation of SU(n, q)     //
//     n = dimension                                                   //
//     q = field order                                                 //
//                                                                     //
//   July 2010 -- latest revision                                       //
/////////////////////////////////////////////////////////////////////////

import "even-su.m": EvenSU;
import "odd-su.m": OddSU;

intrinsic int_StandardPresentationForSU (n:: RngIntElt, F :: FldFin: 
      Projective := false) -> GrpSLP, [] 
{return standard presentation for SU (n, F); if Projective is true, 
 then return presentation for PSU (n, F)}

   require n gt 2: "Degree must be at least 3"; 
   return int_StandardPresentationForSU(n, #F : Projective := Projective);
end intrinsic;

intrinsic int_StandardPresentationForSU (n:: RngIntElt, q :: RngIntElt: 
      Projective := false) -> GrpSLP, [] 
{return standard presentation for SU (n, q); if Projective is true, 
 then return presentation for PSU (n, q)}
  
   require n gt 2: "Degree must be at least 3"; 
   require IsPrimePower (q): "Field size is not valid";

   //"*** This is the new SU code";

   if IsOdd (n) then
      return OddSU (n, q: Projective := Projective);
   else
      return EvenSU (n, q: Projective := Projective);
   end if;
end intrinsic;

/* 
AttachSpec ("spec");
import "standard.m": SUChosenElements;
for d in [3..20] do
for q in [2,3,4,5,7,8,9,11,13,16, 25,27,32, 49, 64, 81] do
d, q;
G := SU(d, q);
E := SUChosenElements (G);
 Q, W := int_StandardPresentationForSU (d, q);
  X := Evaluate (W, E);
assert #Set (X) eq 1;
end for;
end for;

*/
