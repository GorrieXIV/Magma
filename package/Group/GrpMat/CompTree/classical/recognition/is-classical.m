freeze;

//$Id:: is-classical.m 2003 2010-10-15 02:25:20Z eobr007                     $:

import "../../GrpMat/ClassicalRec/sld2.m": 
OrthogonalForm2, RecognizeSO2, RecognizeOmega2;

MyIsLinearGroup := function (G)
   if IsAbsolutelyIrreducible (G) eq false then return false; end if;
   if Degree (G) gt 1 then
      return IsLinearGroup (G);
   else
      return true;
   end if;
end function;

// MyIsLinearGroup := IsLinearGroup;

MyIsSymplecticGroup := function (G)
   if IsAbsolutelyIrreducible (G) eq false then return false; end if;
   d := Degree (G);
   F := BaseRing (G);
   if Degree (G) gt 4 then
      return IsSymplecticGroup (G);
   elif Degree (G) eq 4 then
      flag, id := SimpleGroupName (G);
      if not flag then return false; end if;
      if id[1] cmpeq <"C", d div 2, #F> then return true; else return false; end if;  
   elif Degree (G) eq 2 then 
      return MyIsLinearGroup (G);
   end if;
end function;

// MyIsSymplecticGroup := IsSymplecticGroup;

MyIsUnitaryGroup := function (G)
   if IsAbsolutelyIrreducible (G) eq false then return false; end if;
   d := Degree (G);
   F := BaseRing (G);
   if Degree (G) eq 2 then
      if #F eq 9 then 
         complete := RandomSchreierBounded (G, 96);
         if complete and IdentifyGroup (G) in [<24, 3>, <96, 67>] 
            then return true; else return false; end if;
      elif #F eq 25 then
         complete := RandomSchreierBounded (G, 720);
         if complete and (#G eq 120 or #G eq 720) then return true; else return false; end if;
      elif #F eq 81 then 
         complete := RandomSchreierBounded (G, 720);
         if not complete or #G ge 720 then return true; else return false; end if;
      else 
         flag, id := SimpleGroupName (G);
         if not flag then return false; end if;
         if id[1] cmpeq <"2A", d - 1, Isqrt(#F)> or id[1] cmpeq <"A", d - 1, Isqrt(#F)> then 
            return true; else return false; 
         end if;  
      end if;
   elif Degree (G) gt 2 then 
      return IsUnitaryGroup (G);
   else
      return true;
   end if;
end function;

// MyIsUnitaryGroup := IsUnitaryGroup;

MyIsSOPlusGroup := function (G: SpecialGroup := false)
   d := Degree (G);
   F := BaseRing (G);

   if d gt 2 then 
      if IsAbsolutelyIrreducible (G) eq true then 
         if Degree (G) eq 4 then n := 250; else n := 50; end if; 
         flag := RecognizeClassical (G: NumberOfElements := n, 
                                     Case := "orthogonalplus");
         if flag cmpeq false then return false; end if;
         if flag cmpeq true then 
            if SpecialGroup eq true then 
               form := ClassicalForms (G)`bilinearForm;
               return exists{x : x in Generators (G) | SpinorNorm (x, form) eq 1};
            end if;
            return true; 
         end if;
      else
         return false;
      end if;
   elif d eq 2 then 
      if SpecialGroup eq true then
         flag := RecognizeSO2 (G);
      else
         flag := RecognizeOmega2 (G);
      end if;
      return flag;
   end if;
   return false;
end function;

MyIsSOMinusGroup := function (G: SpecialGroup := false)
   d := Degree (G);
   F := BaseRing (G);
   if d gt 2 then 
      if IsAbsolutelyIrreducible (G) eq true then 
         flag := RecognizeClassical (G: NumberOfElements := 50, Case := "orthogonalminus");
         if flag cmpeq false then return false; end if;
         if flag cmpeq true then 
            if SpecialGroup eq true then 
               form := ClassicalForms (G)`bilinearForm;
               return exists{x : x in Generators (G) | SpinorNorm (x, form) eq 1};
            end if;
            return true; 
         end if;
      else
         return false;
      end if;
   elif d eq 2 then 
      if SpecialGroup eq true then
         flag := RecognizeSO2 (G);
      else
         flag := RecognizeOmega2 (G);
      end if;
      return flag;
   end if;
   return false;
end function;

MyIsSOGroup := function (G: SpecialGroup := false)
   d := Degree (G);
   F := BaseRing (G);

   if d eq 2 then return false; end if;
   if IsAbsolutelyIrreducible (G) eq true then 
       flag := RecognizeClassical (G: NumberOfElements := 50, 
         Case := "orthogonalcircle");
         if flag cmpeq false then return false; end if;
         if flag cmpeq true then 
            if SpecialGroup eq true then 
               form := ClassicalForms (G)`bilinearForm;
               return exists{x : x in Generators (G) | SpinorNorm (x, form) eq 1};
            end if;
            return true; 
         end if;
      else
         return false;
   end if;

   return false;
end function;

MyFormType := function (G)
   if Degree (G) gt 2 or IsIrreducible (G) then 
      return FormType (G);
   else
      flag, quad, form, type := OrthogonalForm2 (G);
      if flag then return type; else return "unknown"; end if;
   end if;
end function;
