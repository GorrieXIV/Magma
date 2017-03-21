freeze;

import "spinor.m": InOmega;

GLMinusSL := function(d,q)
  //A generating element of GL - SL.
  return GL(d,q).1;
end function;

GUMinusSU := function(d,q)
  //A generating element of GU - SU.
  return GU(d,q).1;
end function;

NormSpMinusSp := function(d,q)
  //An element of Normaliser(GL(d,q),Sp(d,q)) - Sp(d,q);
  //Determinant = z^(d/2).
  local z, hd;
  assert IsEven(d);
  z := PrimitiveElement(GF(q));
  hd := d div 2;
  return GL(d,q)!DiagonalMatrix(GF(q),d,
             [z:i in [1..hd]] cat [1:i in [1..hd]]);
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

NormOfSU := function(d,q : general:=false )
//returns the normaliser of SU(d,q) in SL(d,q^2) (or in GL(d,q^2) if general)
  local z, Z, Y, zpow, ypow, mform, trans;
  z := PrimitiveElement(GF(q^2));
  Z := GL(d,q^2)!ScalarMatrix(GF(q^2),d,z);
  if general then
    return sub< GL(d,q^2) | GU(d,q), Z >;
  end if;
  mform := Matrix(GF(q^2),d,d, [<i,d+1-i,1>:i in [1..d]]);
  trans := CorrectForm(mform,d,q^2,"unitary");
  Y := DiagonalMatrix(GF(q^2),[z^(q-1)] cat [1:i in [1..d-1]]);
  Y := trans * Y * trans^-1; //Y is generator of GU/SU
  zpow := (q-1) div GCD(d,q-1);
  ypow := (-d * zpow div (q-1)) mod (q+1);
  return sub< SL(d,q^2) | SU(d,q), Z^zpow * Y^ypow >; 
end function;

NormOfSp := function(d,q : general:=false)
//returns the normaliser of Sp(d,q) in SL(d,q) (or in GL(d,q) if general)
    local z, Z, Y, zpow, ypow, hd, I, x, y;
  if general then
    return sub< GL(d,q) | Sp(d,q), NormSpMinusSp(d,q) >;
  end if;
  z := PrimitiveElement(GF(q));
  Z := ScalarMatrix(GF(q),d,z);
  hd := d div 2;
  if IsEven(q) or GCD(q-1,d) ne GCD(q-1,hd) then
    zpow := (q-1) div GCD(d,q-1);
    return sub< SL(d,q) | Sp(d,q), Z^zpow >;
  else
    Y := NormSpMinusSp(d,q);
    ypow := (q-1) div GCD(hd,q-1);
    return sub< SL(d,q) | Sp(d,q), Y^ypow >;
  end if;
end function;

NormOfO := function(d,q,eps : general:=false)
//returns the normaliser of O^eps(d,q) in SL(d,q) (or in GL(d,q) if general)
//not maximal in SL for q even  - subgroups of Sp if q is even.
//also need d>2 in maximals.
  local z, Z, Y, X,zpow, ypow, hd, form, trans, W, N;

  assert (IsOdd(d) and eps eq 0) or (IsEven(d) and Abs(eps) eq 1);
  if d eq 2 and q eq 3 and eps eq 1 then
    if general then return GL(d,q); end if;
    return SL(d,q);
  end if;

  z := PrimitiveElement(GF(q));
  Z := ScalarMatrix(GF(q),d,z);
  zpow := (q-1) div GCD(d,q-1);
  if IsOdd(d) then
    if general then
      return sub< GL(d,q) | GO(d,q), Z >;
    end if;
    return sub< SL(d,q) | SO(d,q), Z^zpow >;
  end if;
  if IsEven(q) then
    if general then
      if eps eq 1 then return sub< GL(d,q) | GOPlus(d,q), Z >; end if;
      return sub< GL(d,q) | GOMinus(d,q), Z >;
    else
      if eps eq 1 then return sub< SL(d,q) | SOPlus(d,q), Z^zpow >; end if;
      return sub< SL(d,q) | SOMinus(d,q), Z^zpow >;
    end if;
  end if;
  hd := d div 2;
  //get transforming matrix
  if eps eq 1 then
    isit, type, form := OrthogonalForm(GOPlus(d,q));
  else isit, type, form := OrthogonalForm(GOMinus(d,q));
  end if;
  X := GOMinusSO(d,q,eps);
  Y := NormGOMinusGO(d,q,eps);
  //Normaliser in GL = <SO, X, Y, Z > (Z redundant)
  if general then
    if eps eq 1 then return sub< GL(d,q) | SOPlus(d,q), X, Y >; end if;
    return sub< GL(d,q) | SOMinus(d,q), X, Y >;
  end if;
  //Normaliser in SL is generated by SO together with elements
  //X^x Y^y Z^z with x(q-1)/2 + yd/2 + zd = 0 mod q-1
  W := Matrix(Integers(),4,1,[(q-1) div 2, hd, d, q-1]);
  N := Nullspace(W);
  gens := [ X^n[1] * Y^n[2] * Z^n[3] : n in Generators(N) ];
  if eps eq 1 then return sub< SL(d,q) | SOPlus(d,q), gens >;
  else return sub< SL(d,q) | SOMinus(d,q), gens >;
  end if;
    
end function;
