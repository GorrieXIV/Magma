freeze;

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

GLMinusSL := function(d,q)
  //A generating element of GL(d,q) - SL(d,q)
  return GL(d,q)!DiagonalMatrix([w] cat [1:i in [1..d-1]])
                 where w := PrimitiveElement(GF(q));
end function;

GUMinusSU := function(d,q)
  //A generating element of GU(d,q) - SU(d,q)
  local w;
  w := PrimitiveElement(GF(q^2));
  if d eq 1 then return GL(d,q^2)![w^(q-1)]; end if;
  return GL(d,q^2)!DiagonalMatrix([w^-1] cat [1:i in [1..d-2]] cat [w^q])
                 where w := PrimitiveElement(GF(q^2));
end function;

CSpMinusSp := function(d,q)
  //An element of Normaliser(GL(d,q),Sp(d,q)) - Sp(d,q);
  //Determinant = w^(d/2).
  local w, hd;
  assert IsEven(d);
  w := PrimitiveElement(GF(q));
  hd := d div 2;
  return GL(d,q)!DiagonalMatrix(GF(q),d,
             [w:i in [1..hd]] cat [1:i in [1..hd]]);
end function;

SOMinusOmega := function(d,q,eps)
//An element of SO^eps(d,q) - Omega^eps(d,q).
    local  X;
    assert eps in {-1,0,1};
    X := IsOdd(d) select SO(d,q) else
          eps eq 1 select SOPlus(d,q) else SOMinus(d,q);
    for i in [1..Ngens(X)] do
      if not InOmega(X.i,d,q,eps) then
        return X.i;
        break;
      end if;
    end for;
end function;

GOMinusSO := function(d,q,eps)
  //An element of GO^eps(d,q) - SO^eps(d,q); determinant -1.
  local G, h;
  assert IsOdd(q);
  assert eps in {-1,0,1};
  if eps eq 0 then
    return GL(d,q)!ScalarMatrix(GF(q),d,-1);
  end if;
  if eps eq 1 then
    h:=d div 2;
    return GL(d,q)!PermutationMatrix(GF(q),Sym(d)!(h,h+1));
  end if;
  G := GOMinus(d,q);
  for g in [G.i : i in [1..Ngens(G)]] do
    if Determinant(g) ne 1 then return g; end if;
  end for;
end function;

CGOMinusGO := function(d,q,eps)
  //An element of Normaliser(GL(d,q),GO^eps(d,q)) - GO^eps(d,q);
  //Determinant = w^(d/2).

  local w, hd, a, b, g, mat, isit, type, form, AandB;
  function AandB(q,w)
    //find elements of GF(q) with a^2+b^2=w.
    for b in GF(q) do
      bool, a:= IsSquare(w-GF(q)!b^2);
      if bool then return a, b; end if;
    end for;
    error "ERROR: couldn't find a and b in GF(", q, ")";
  end function;

  assert IsEven(d);
  assert IsOdd(q) or eps eq 1;
  assert eps in {-1,1};
  w := PrimitiveElement(GF(q));
  if eps eq 1 then
    hd := d div 2;
    return GL(d,q)!DiagonalMatrix(GF(q),d,
             [w:i in [1..hd]] cat [1:i in [1..hd]]);
  end if;
  a,b := AandB(q,w);
  g := d mod 4 eq 0 or (q-1) mod 4 eq 0 select
      DiagonalJoin( [Matrix(GF(q),2,2,[a,-b,b,a]):i in [1.. d div 2 -1]]
         cat [Matrix(GF(q),2,2,[0,-1,w,0])] ) else
      DiagonalJoin( [Matrix(GF(q),2,2,[a,-b,b,a]):i in [1.. d div 2]]);
  isit, form := SymmetricBilinearForm(GOMinus(d,q));
  mat := CorrectForm(form, d, q, "orth-");
  return GL(d,q)!(mat * g * mat^-1);
end function;
