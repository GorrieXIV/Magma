freeze;

//$Id:: involution.m 2748 2014-10-08 01:31:02Z eobr007                       $:

import "../../../basics.m": RestrictForm, RecognitionError;
import "../../../order.m": GenerateInvolution;
import "../../../conjugate.m": OrthogonalForm;

import "../../../../../recog/magma/node.m": ERROR_RECOGNITION;

/* identify type of symmetric bilinear form */

TypeOfForm := function (A)
   a := Nrows (A);
   if IsOdd (a) then
      type := "orthogonalcircle";
   else
      type := IsSquare ((-1)^(a div 2) * Determinant (A))
              select "orthogonalplus" else "orthogonalminus";
   end if;
   return type;
end function;

/* identify types for factors in centraliser of involution g; 
   U and W are +1 and -1 eigenspaces for g */

InvolutionType := function (G, g, U, W)

   flag, form := OrthogonalForm (G);
   assert flag;

   Ur := RestrictForm (form, Basis (U), 1);
   Wr := RestrictForm (form, Basis (W), 1);

   return TypeOfForm (Ur), TypeOfForm (Wr);
end function;

/* rewrite G and involution g with respect to basis 
   determined by eigenspaces U and W for g */
 
BasisOfInvolution := function (G, g, U, W)
   B := [Eltseq (u): u in Basis (U)] cat [Eltseq (u): u in Basis (W)];
   B := &cat (B);
   F := BaseRing (G);
   d := Degree (G);
   CB := GL (d, F) ! B;
   b := CB * g * CB^-1;
   gens := UserGenerators (G);
   gens := [CB * g * CB^-1 : g in gens];
   H := sub <GL(d, F) | gens>;
   return b, H, CB;
end function;

/* is g a suitable involution for Omega^- case?
   namely, does centraliser have direct factors of type Omega^+ and Omega^-? 
   if SpecialGroup then we are working with SO^- */ 

IsMinusInvolution := function (G, g, U, W: SpecialGroup := false)

   d := Degree (G);
   F := BaseRing (G);
   q := #F;
   n := d div 2;

   if (SpecialGroup) or (q mod 4 eq 1 and n gt 2) then 
      a, b := InvolutionType (G, g, U, W);
      if a eq "orthogonalminus" and b eq "orthogonalplus" then
         temp := U; U := W; W := temp;
         a, b := InvolutionType (G, g, U, W);
      end if;
      return a eq "orthogonalplus" and b eq "orthogonalminus" 
         and Dimension (W) eq 4, U, W;
   end if;

   assert q mod 4 eq 3;

   if (n gt 3 and IsOdd (n)) then 
      a, b := InvolutionType (G, g, U, W);
      if a eq "orthogonalminus" and b eq "orthogonalplus" then
         temp := U; U := W; W := temp;
         a, b := InvolutionType (G, g, U, W);
      end if;
      return a eq "orthogonalplus" and b eq "orthogonalminus" 
         and Dimension (W) eq 6, U, W;
   end if;

   if (n ge 4 and IsEven (n)) then 
      a, b := InvolutionType (G, g, U, W);
      if (Dimension (U) eq 4 and a eq "orthogonalminus") 
         and b eq "orthogonalplus" then
         temp := U; U := W; W := temp;
         a, b := InvolutionType (G, g, U, W);
      end if;
      return a eq "orthogonalplus"
         and b eq "orthogonalminus" and Dimension (W) eq 4, U, W;
   end if;

   if (d eq 6) then
      a, b := InvolutionType (G, g, U, W);
      if a eq "orthogonalminus" and b eq "orthogonalplus" then
         temp := U; U := W; W := temp;
         a, b := InvolutionType (G, g, U, W);
      end if;
      return a eq "orthogonalplus" and b eq "orthogonalminus" 
         and Dimension (W) eq 2, U, W;
   end if;
      
   error Error (rec<RecognitionError |
         Description := "Constructive recognition for classical group",
         Error := "Problem in IsMinusInvolution">);
end function;

/* is g a suitable involution for Omega^0 case?
   namely, does centraliser have direct factors of type Omega^+ 
   and Omega^0 ? */ 

IsOInvolution := function (G, g, U, W)
   if IsOdd (Dimension (U)) then 
      temp := U; U := W; W := temp;
   end if;
   a, b := InvolutionType (G, g, U, W);
   return a eq "orthogonalplus" and b eq "orthogonalcircle", U, W; 
end function;

/* is g a suitable involution for Omega^+ case?
   namely, does centraliser have direct factors of type Omega^+? */ 

IsPlusInvolution := function (G, g, U, W)
   /* ensure large space is at top */
   if Dimension (W) gt Dimension (U) then 
      tmp := U; U := W; W := tmp;
   end if;
   a, b := InvolutionType (G, g, U, W);
   return a eq "orthogonalplus" and b eq "orthogonalplus", U, W; 
end function;

/* find element y of even order 2n such that y^n has eigenspaces 
   of dimension f, d - f where each lies in prescribed range and 
   resulting centralisers have prescribed type; 
   write matrices wrt resulting eigenbasis */
 
SOSplitSpace := function (G : Limit := Maximum (500, 10 * Degree (G)), 
   type := "orthogonalplus", SpecialGroup := false, 
   Range := [Degree(G) div 3..2 * Degree(G) div 3])

   found := false;
   nmr := 0;
   repeat 
      flag, g, w := GenerateInvolution (G);
      if flag then 
         U := Eigenspace (g, 1);
         W := Eigenspace (g, -1);
         degs := [Dimension (U), Dimension (W)];
         vprint User5: "Characteristic polynomial factors have degree ", degs;
         found := exists (x) {x : x in degs | x in Range};
         if found then 
            if type eq "orthogonalplus" then 
               found, U, W := IsPlusInvolution (G, g, U, W); 
            elif type eq "orthogonalcircle" then 
               found, U, W := IsOInvolution (G, g, U, W); 
            elif type eq "orthogonalminus" then 
               found, U, W := IsMinusInvolution (G, g, U, W : 
                                 SpecialGroup := SpecialGroup); 
            else
               error "Error in type in SOSplitSpace"; 
            end if;
         end if;
      end if;
      nmr +:= 1;
   until (found) or nmr gt Limit;

   if nmr gt Limit then
      error ERROR_RECOGNITION; 
      //error Error (rec<RecognitionError |
      //   Description := "Constructive recognition for classical group",
      //   Error := "Failed to split space in SOSplitSpace">);
   end if;

   vprint User5: "Number of random elements processed to split space is ", nmr;

   b, H, CB := BasisOfInvolution (G, g, U, W);

   return g, w, H, b, CB, Dimension (U), Dimension (W), U, W;

end function;
