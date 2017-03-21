freeze;

GOMinusSO := function(d,q,eps)
  //An element of GO^eps(d,q) - SO^eps(d,q); determinant -1.
  local G;
  assert IsOdd(q);
  assert eps in {-1,0,1};
  if eps eq 0 then
    return GL(d,q)!ScalarMatrix(GF(q),d,-1);
  end if;
  G := eps eq 1 select GOPlus(d,q) else GOMinus(d,q);
  for g in [G.i : i in [1..Ngens(G)]] do
    if Determinant(g) ne 1 then return g; end if;
  end for;
end function;

NormGOMinusGO := function(d,q,eps)
  //An element of Normaliser(GL(d,q),GO^eps(d,q)) - GO^eps(d,q);
  //Determinant = z^(d/2).

  local z, hd, a, b, g, mat, isit, type, form, AandB;
  function AandB(q,z)
    //find elements of GF(q) with a^2+b^2=z.
    for b in GF(q) do
      bool, a:= IsSquare(z-GF(q)!b^2);
      if bool then return a, b; end if;
    end for;
    error "ERROR: couldn't find a and b in GF(", q, ")";
  end function;

  assert IsEven(d);
  assert IsOdd(q) or eps eq 1;
  assert eps in {-1,1};
  z := PrimitiveElement(GF(q));
  if eps eq 1 then
    hd := d div 2;
    return GL(d,q)!DiagonalMatrix(GF(q),d,
             [z:i in [1..hd]] cat [1:i in [1..hd]]);
  end if;
  a,b := AandB(q,z);
  g := d mod 4 eq 0 or (q-1) mod 4 eq 0 select
      DiagonalJoin( [Matrix(GF(q),2,2,[a,-b,b,a]):i in [1.. d div 2 -1]]
         cat [Matrix(GF(q),2,2,[0,-1,z,0])] ) else
      DiagonalJoin( [Matrix(GF(q),2,2,[a,-b,b,a]):i in [1.. d div 2]]);
  isit, form := SymmetricBilinearForm(GOMinus(d,q));
  mat := CorrectForm(form, d, q, "orth-");
  return GL(d,q)!(mat * g * mat^-1);
end function;

