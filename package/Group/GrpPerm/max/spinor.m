freeze;

// Most of this file has moved to Group/GrpMat/Classical

InOmega := function(g,d,q,sign)
  local isf, form;
  if sign eq 1 then
    if d eq 2 then form := Matrix(GF(q),2,2,[0,1,1,0]);
    else isf, form := SymmetricBilinearForm(GOPlus(d,q));
    end if;
  elif sign eq -1 then
    isf, form := SymmetricBilinearForm(GOMinus(d,q));
  else
    isf, form := SymmetricBilinearForm(GO(d,q));
  end if;
  return SpinorNorm(GL(d,q)!g,form) eq 0;
end function;


//This function makes matrix entries that are needed for the
//conformal orthogonal group = normaliser of GO in GL.
function GetAandB(q)
  z:= PrimitiveElement(GF(q));
  for a in GF(q) do
    bool, b:= IsSquare(z - a^2);
    if bool then
      return a, b;
    end if;
  end for;
end function;
