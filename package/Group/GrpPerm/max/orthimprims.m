freeze;

import "spinor.m":  InOmega;
import "orthreds.m": NonDegenStabOmega;
import "classicals.m": SOMinusOmega, GOMinusSO, NormGOMinusGO;

function OrthImprim(d, q, sign, k, sign1 :
                      special:=false, general:=false, normaliser:=false)
/* Construct imprimitive subgroup
 * of type Omega^sign1(k,q) wreath d/k in Omega^sign(d,q),
 */
  local  Omdq, t, sg, type, isf, gp1, gens, gen, newgen, tmat, ex,
         id, gsl1, ggl1, cmat1, cmat2, w, form, form1, formt;
  assert d gt 2;
  assert k lt d and d mod k eq 0;
  assert (IsEven(d) and IsEven(k)) or IsOdd(q);
  assert (IsOdd(d) and sign eq 0) or (IsEven(d) and sign in {-1,1});
  assert (IsOdd(k) and sign1 eq 0) or (IsEven(k) and sign1 in {-1,1});

  t := d div k;
  //Check parameters are compatible.
  if sign in {-1,1} then
    ex := d mod 4 eq 2 and q mod 4 eq 3; //i.e. D non-square
    if (sign1 in {-1,1} and sign1^t ne sign) or
       (sign1 eq 0 and ex and sign eq 1) or
       (sign1 eq 0 and not ex and sign eq -1) then
      error "Incompatible parameters";
    end if;
  end if;

  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  type := sign eq 0 select "orth" else
          sign eq 1 select "orth+" else "orth-";
  
  gp1 :=  k eq 1 select sub<GL(k,q)|[-1]> else
          sign1 eq 0 select GO(k,q) else
          sign1 eq 1 select GOPlus(k,q) else GOMinus(k,q);
  
  //Note that we use GO  (rather than SO, Omega) to calculate the forms
  //to ensure absolute irreducibility of gp1, gp2 in dimension 2.
  if IsEven(q) then
    if q eq 2 and k eq 2 and sign1 eq 1 then
      form1 := Matrix(GF(q),2,2,[0,1,0,0]);
    else isf, form1 := QuadraticForm(gp1);
    end if;
  else
    if q eq 3 and k eq 2 and sign1 eq 1 then
      form1 := Matrix(GF(q),2,2,[0,1,1,0]);
    else isf, form1 := SymmetricBilinearForm(gp1);
    end if;
  end if;

  //We need elements of in sl-omega (k>1) and gl-sl(p odd) 
  if k gt 1 then
    gsl1 := SOMinusOmega(k, q, sign1);
  end if;
  if IsOdd(q) then
    ggl1 := GOMinusSO(k, q, sign1);
  end if;
  
  //now redefine gp1 to include generators of Omega + gsl, ggl 
  
  if k gt 1 then
    gp1 :=  sign1 eq 0 select Omega(k,q) else
            sign1 eq 1 select OmegaPlus(k,q) else OmegaMinus(k,q);
    gp1 := sub < GL(k,q) | gp1, gsl1 >;
    if IsOdd(q) then
      gp1 := sub < GL(k,q) | gp1, ggl1 >;
    end if;
  end if;

  //We will need to transform our generators to fix Magma's quadratic form.
  tmat := TransformForm(DiagonalJoin([form1: i in [1..t]]), type);
  id := GL(k,q)!IdentityMatrix(GF(q),k);

  //Now we can start constructing the generators
  gens := [GL(d,q)|];

  for gen in [gp1.i : i in [1..Ngens(gp1)]] do
    if Determinant(gen) ne 1 then
      //use ggl1 to adjust it and make determinant 1
      if general then
        newgen := GL(d,q)!DiagonalJoin([gen] cat [id: i in [1..t-1]])^tmat;
        Append(~gens,newgen);
      end if;
      newgen := GL(d,q)!DiagonalJoin([gen,ggl1] cat [id: i in [1..t-2]])^tmat;
      if special or InOmega(newgen,d,q,sign) then
        Append(~gens,newgen);
      elif k gt 1 then
        //adjust again using gsl1.
        newgen :=
           GL(d,q)!DiagonalJoin([gen,ggl1*gsl1] cat [id: i in [1..t-2]])^tmat;
        assert InOmega(newgen,d,q,sign);
        Append(~gens,newgen);
      end if;
    else
      newgen := GL(d,q)!DiagonalJoin([gen] cat [id: i in [1..t-1]])^tmat;
      if special or InOmega(newgen,d,q,sign) then
        Append(~gens,newgen);
      elif k gt 1 then
        //adjust using gsl1.
        newgen :=
           GL(d,q)!DiagonalJoin([gen,gsl1] cat [id: i in [1..t-2]])^tmat;
        assert InOmega(newgen,d,q,sign);
        Append(~gens,newgen);
      end if;
    end if;
  end for;

  //Now generators of S_n 
  for gen in [Alt(t).i : i in [1..Ngens(Alt(t))] ] do
    newgen :=
     GL(d,q)!KroneckerProduct( PermutationMatrix(GF(q),gen), id )^tmat;
    assert InOmega(newgen,d,q,sign);
    Append(~gens,newgen);
  end for;

  newgen :=
    GL(d,q)!KroneckerProduct( PermutationMatrix(GF(q),Sym(t)!(1,2)), id )^tmat;
  if Determinant(newgen) ne 1 then
    newgen *:= GL(d,q)!DiagonalJoin([ggl1] cat [id: i in [1..t-1]])^tmat;
  end if;
  if special or InOmega(newgen,d,q,sign) then
    Append(~gens,newgen);
  elif k gt 1 then
    newgen *:= GL(d,q)!DiagonalJoin([gsl1] cat [id: i in [1..t-1]])^tmat;
    assert InOmega(newgen,d,q,sign);
    Append(~gens,newgen);
  end if;

  if normaliser  then
    if IsOdd(q) and IsEven(k) then
      gnl1 := NormGOMinusGO(k, q, sign1);
      newgen := GL(d,q)!DiagonalJoin([gnl1 : i in [1..t]])^tmat;
      Append(~gens,newgen);
    elif q gt 3 then
      Append(~gens, ScalarMatrix(d, PrimitiveElement(GF(q))) );
    end if;
  end if;

  return sub<GL(d,q) | gens>;
  //k=1: t even,q=1,7 mod 8, c=4(so + ngo-go); t even q=3,5 mod 8, c=2 (ngo-go);
  //k=1: t odd,  q=1,7 mod 8, c=2 (so); t odd q=3,5 mod 8, c=1.
  //k>1: k odd, t even, c=2 (ngo-go); else c=1.
end function;

function OrthStabOfHalfTS(d, q :
                      special:=false, general:=false, normaliser:=false)
  //Construct GL_{d/2}(q).2 <= OmegaPlus(d,q)
  assert IsEven(d);

  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  f:= d div 2;
  z:= PrimitiveElement(GF(q));

  DJ := function(mat,f,q)
    local cb;
    cb := GL(f, q)!Matrix(GF(q),f,f,[<i,f+1-i,1>:i in [1..f]]);
    return DiagonalJoin(mat,Transpose(cb*mat^-1*cb));
  end function;

  if special then
    mat1:=DJ(GL(f,q).1,f,q); mat2:=DJ((GL(f,q).2),f,q);
  else
  //want matrices to generate GL(d,q) for q even or GL(d,q)/2
  //for q odd. 
    mat1:= q eq 3 select DJ(SL(f,q).1,f,q) else IsEven(q)
                  select DJ(GL(f,q).1,f,q) else DJ((GL(f,q).1)^2,f,q); 
    mat2:= q eq 3 select DJ(SL(f,q).2,f,q) else DJ((GL(f,q).2),f,q);
  end if;

  if not general and (not special or IsOdd(q)) and IsOdd(f) then
                                          //swapping matrix not in Omega/SO
    return sub<GL(d, q)|mat1, mat2 >;
  end if;

  swapmat := GL(d,q)!Matrix(GF(q),d,d,[<i,d+1-i,1>:i in [1..d]]);
  gens := [GL(d,q) | mat1, mat2, swapmat ];

  if normaliser then
    Append(~gens, NormGOMinusGO(d,q,1) );
  end if;
  return sub< GL(d, q)| gens >;
  //d/2 even, c=2, so (q even), go-so (q odd); o.w. c=1.
end function;

function OrthStabOfHalfND(d, q :
       special:=false, general:=false, normaliser:=false )
  //Construct O_{d/2}(q)^2, d even, d/2 odd
  //This is actually reducible, so we construct it thus.
  //It is classified as imprimitive because the two subspaces fixed are
  //interchanged by an element fixing the orthogonal form mod scalars.
  assert IsOdd(q) and IsEven(d) and IsOdd(d div 2);
  sign := q mod 4 eq 1 select -1 else 1;
  return  NonDegenStabOmega(d, q, sign, d div 2, 0 :
                      special:=special, general:=general, ipn:=normaliser );
  //c=1
end function;

function OrthogonalImprims(d, q, sign)
  assert d gt 2;
  assert (IsOdd(d) and sign eq 0) or (IsEven(d) and sign in {-1,1});
  list:= [];
  divs := Divisors(d);
  Exclude(~divs,1);
  for t in divs do
    k := d div t;
    if IsEven(k) then
      sign1 := 1;
      if sign eq sign1^t then
        Append(~asmax, OrthImprim(d, q, sign, k, sign1) );
      end if;
      sign1 := -1;
      if sign eq sign1^t then
        Append(~asmax, OrthImprim(d, q, sign, k, sign1) );
      end if;
    else //k odd
      if IsEven(q) then continue; end if;
      if IsEven(t) then 
        ex := d mod 4 eq 2 and q mod 4 eq 3; //D non-square
        if (ex and sign eq -1) or (not ex and sign eq 1) then
          Append(~list, OrthImprim(d, q, sign, k, 0) );
        end if;
      else //k, t odd
        Append(~list, OrthImprim(d, q, sign, k, 0) );
      end if;
    end if;
  end for;
    
  if IsEven(d) then
    if sign eq 1 then
      Append(~list, OrthStabOfHalfTS(d, q) );
    end if;
    if IsOdd(q) and d mod 4 eq 2 then
      if (q mod 4 eq 1 and sign eq -1) or (q mod 4 eq 3 and sign eq 1) then
        Append(~list, OrthStabOfHalfND(d, q) );
      end if;
    end if;
  end if;

  return list;
end function;
