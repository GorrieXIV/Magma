freeze;

   /*--- file contains functions used in sanity checks ---*/

IsStarRing := function (R : Limit := 20)
     isit := true;
     for i in [1..Limit] do
         x := Random (R);
         y := Random (R);
         isit and:= (x + y) @ R`Star eq (x @ R`Star) + (y @ R`Star);
         isit and:= (x * y) @ R`Star eq (y @ R`Star) * (x @ R`Star);
         isit and:= (x @ R`Star) @ R`Star eq x;
     end for;
return isit;
end function;


IsRingHom := function (R, S, phi : Limit := 20)
     isit := true;
     for i in [1..Limit] do
         x := Random (R);
         y := Random (R);
         isit and:= (x + y) @ phi eq (x @ phi) + (y @ phi);
         isit and:= (x * y) @ phi eq (x @ phi) * (y @ phi);
     end for;
return isit;
end function;


IsStarMap := function (R, S, phi : Limit := 20)
     isit := IsRingHom (R, S, phi);
     for i in [1..Limit] do
         x := Random (R);
         isit and:= (x @ phi) @ S`Star eq (x @ R`Star) @ phi;
     end for;
return isit;
end function;


IsUnitaryElement := function (R, u)
return u * (u @ R`Star) eq Identity (R);
end function;


IsAdjointPair := function (F, auto, x, y)
return FrobeniusImage (x, auto) * F eq F * Transpose (y);
end function;


IsIsometry := function (F, auto, x)
return FrobeniusImage (x, auto) * F * Transpose (x) eq F;
end function;


IsSimilarity := function (F, auto, x)
return exists { a : a in BaseRing (Parent (F)) |
       FrobeniusImage (x, auto) * F * Transpose (x) eq a * F };
end function;
