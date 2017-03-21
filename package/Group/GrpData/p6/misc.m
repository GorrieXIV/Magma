freeze;
 
/* return smallest non-qr in GF (p) */

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

/* return a fixed pair used by Easterfield */

EasterfieldPair := function (p)
  lam := 1/NonQuadraticResidue(p);
  for x in GF (p) do
    for y in GF (p) do
      if (x^2 - lam*y^2) eq lam and x ne 0 and y ne 0 then 
        return x,y; 
      end if;
    end for;
  end for;
end function;

