freeze;

/* if G is a finite subgroup of GL(n, F) where F has characteristic 0,
   then G has a normal abelian subgroup of index bounded above by the 
   value returned by JordanIndex (n) */

JordanIndex := function (n)
   assert n gt 1;
   case n:
      when 2: return 60;
      when 3: return 360;
      when 4: return 25920;
      when 5: return 25920;
      when 6: return 6531840;
      when 7: return $$(3) * $$(4);
      when 8: return 2 * $$(4)^2;
      when 9: return $$(3) * $$(6);
      when 10: return $$(4) * $$(6);
      when 11: return 2 * $$(3) * $$(4)^2;
      when 12: return 6 * $$(4)^3;
      when 13: return 6 * $$(4)^3;
      when 14: return Factorial (7) * $$(2)^7;
      when 15: return 6 * $$(3) * $$(4)^3;
      when 16: return 24 * $$(4)^4;
      when 17: return 24 * $$(4)^4;
      when 18: return Factorial (9) * $$(2)^9;
      when 19: return 24 * $$(3) * $$(4)^4;
   end case;
   if n in {20..62} join {64,66,68,70} then
      r := n div 2;
      return Factorial (r) * 60^r;
   else
      return Factorial (n + 1);
   end if;
end function;

/* is index of soluble radical smaller than Jordan index? */

JordanIndexTest := function (H)
   R := LMGSolubleRadical (H);
   rindex := LMGIndex (H, R); 
   jindex := JordanIndex (Degree (H));
   vprint Infinite: "Index of soluble radical and Jordan index are:", rindex, jindex;
   return rindex le jindex;
end function;
