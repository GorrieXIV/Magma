freeze;

//$Id:: so-product.m 2748 2014-10-08 01:31:02Z eobr007                       $:

import "../../../section.m": ExtractFactor, ExtractAction;
import "../../../is-classical.m": MyIsSOPlusGroup, MyIsSOGroup, MyIsSOMinusGroup;

/* is G a direct product of two copies of orthogonal groups, 
   where action describes O+; if SpecialGroup
   then require direct product of special orthogonals;
   if Partial, is G direct product of SO+ with C_2 identified? */

IsDirectProductOs := function (G, action: Plus := true, 
                               Partial := false, SpecialGroup := false)

   d := Degree (G);
   
   if Type (action) eq SeqEnum then action := {x : x in action}; end if;

   rest := Sort (SetToSequence ({1..d} diff action));
   action := Sort ([x : x in action]);
   
   G1 := ExtractFactor (G, action);
   G2 := ExtractFactor (G, rest);

   one := MyIsSOPlusGroup (G1);
   if not one then return false; end if;

   Circle := false; Minus := false;

   if IsOdd (#rest) then 
      Circle := true; Plus := false; fct := MyIsSOGroup; 
   elif Plus then 
      fct := MyIsSOPlusGroup; 
   else 
      Minus := true; fct :=  MyIsSOMinusGroup; 
   end if;

   two := fct (G2);
   if not two then return false; end if;
   
   if not Partial and not SpecialGroup then return true; end if;

   if Degree (G1) gt 2 then 
      flag, form1 := SymmetricBilinearForm (G1);
      assert flag;
   end if;
   if Degree (G2) gt 2 then 
      flag, form2 := SymmetricBilinearForm (G2);
      assert flag;
   end if;

   F := BaseRing (G);
   q := #F;
   L := [];
   for i in [1..Ngens (G)] do
      blocks := [* ExtractAction (G.i, action),
                   ExtractAction (G.i, rest) *];
      if Nrows (blocks[1]) eq 2 then
         v := Valuation (q - 1, 2);
         spin1 := Valuation (Order (blocks[1]), 2) eq v select 1 else 0;
      else 
         spin1 := SpinorNorm (blocks[1], form1); 
      end if;

      /* cater for 5-dimensional case where action is 4-dimension */
      if Nrows (blocks[2]) eq 1 then 
        spin2 := 1;
      elif Nrows (blocks[2]) eq 2 then
         if Plus then  
            v := Valuation (q - 1, 2); 
            spin2 := Valuation (Order (blocks[2]), 2) eq v select 1 else 0;
         elif Minus then 
            v := Valuation (q + 1, 2); 
            spin2 := Valuation (Order (blocks[2]), 2) eq v select 1 else 0;
         elif Circle then 
            spin2 := IsEven (Order (blocks[2])) select 1 else 0;
         end if;
      else 
         spin2 := SpinorNorm (blocks[2], form2); 
      end if;
      Append (~L, [spin1, spin2]);
   end for;

   C := CyclicGroup(GrpAb, 2);
   D := DirectSum (C, C);
   I := sub <D | L >;

   vprint User5: "In SODirectProduct I = ", I;
   if Partial then return #I gt 1; end if;
   if SpecialGroup then return #I ge 4; end if;
   return false;
end function;
