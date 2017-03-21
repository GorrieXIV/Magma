freeze;

/* number of groups of order p^7 */

NumberOfGroupsp7 := function (p)
   if not IsPrime (p) then return false; end if;
   if p eq 2 then 
      return 2328;
   elif p eq 3 then 
      return "unknown";
   elif p eq 5 then
      return "unknown";
   else 
      return 3 * p^5 + 12 * p^4 + 44 * p^3 + 170 * p^2 + 2455 +
      (4 * p^2 + 44 * p + 291) * Gcd (p - 1, 3) +
      (p^2 + 19 * p + 135) * Gcd (p - 1, 4) +
      (3 * p + 31) * Gcd (p - 1, 5) + 
      4 * Gcd (p - 1, 7) + 5 * Gcd (p - 1, 8) + Gcd (p - 1, 9);
   end if;
end function;
