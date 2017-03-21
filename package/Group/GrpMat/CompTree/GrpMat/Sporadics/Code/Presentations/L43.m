freeze;

/* presentation on standard generators for L43 */

FPToSLP := function (F)
  S := SLPGroup (Ngens (F));
  gamma := hom<F -> S | [S.i : i in [1..Ngens (S)]]>;
  Rels := Relations (F);
  Rels := [gamma (LHS (r) * RHS (r)^-1): r in Rels];
  return Rels, gamma;
end function;

PresentationL43 := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;

   F<a,b> := FreeGroup (2);
   Q := quo<
    F |
    a^2 = Id($),
    b^4 = Id($),
    (b * a * b^-1 * a)^4 = Id($),
    b^-1 * a * b^-2 * a * b^-2 * a * b^-2 * a * b^2 * a *
    b^2 * a * b^2 * a * b^2 * a * b^-1 = Id($),
    (a * b^-1)^13 = Id($),
    a * b^-1 * a * b * a * b * a * b^-1 * a * b * a *
    b^-2 * a * b * a * b^-1 * a * b^2 * a * b^-1 * a * b *
    a * b^2 * a * b = Id($),
    (b * a * b * a * b^-1 * a * b^-1 * a)^4 = Id($),
    b^-1 * a * b^-2 * a * b^-2 * a * b^-2 * a * b^-1 * a *
    b^-2 * a * b^-2 * a * b^-2 * a * b * a * b^2 * a * b^2
    * a * b^2 * a * b^-1 * a * b^2 * a * b^2 * a * b^2 * a
    = Id($),
    a * b^-2 * a * b^-1 * a * b^-2 * a * b^-2 * a * b^-2 *
    a * b^-1 * a * b^-2 * a * b^-1 * a * b^-2 * a * b^2 *
    a * b^2 * a * b^-1 * a * b^2 * a * b * a * b^2 * a *
    b^2 * a * b^2 * a * b = Id($),
    b * a * b^-2 * a * b^-2 * a * b * a * b^-2 * a * b *
    a * b^-1 * a * b^-1 * a * b^-1 * a * b^-1 * a * b^-1 *
    a * b * a * b^2 * a * b * a * b^2 * a * b^2 * a * b
    * a * b * a * b^2 * a * b * a = Id($) >
    ;

   R := FPToSLP (Q);
   E := Set (Evaluate (R, UserGenerators));
   if Projective then
      return #E eq 2 and forall{e : e in E | IsCentral (G, e)};
   else 
      return #E eq 1;
   end if;
end function;
