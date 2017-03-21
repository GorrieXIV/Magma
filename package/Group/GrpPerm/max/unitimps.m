freeze;

import "classicals.m": GUMinusSU;

ListMatToQ:= function(a, q)
// raise every element of matrix A to q-th power.
  local list;
  list:= Eltseq(a);
  for i in [1..#list] do list[i]:= list[i]^q; end for;
  return list;
end function;

//This makes SU(k, q).(q+1)^(d/k-1).Sym(d/k).
//We create a wreath product which acts on an orthogonal
//sum of k-dimensional unitary spaces, then correct for determinant -1
//in the permutation matrices, then add a single diagonal element
//which has order (q-1) on the first space, and corrects for
//determinant on the second. there's a couple of points where the case
//k=1 is different, as we cannot create a hyperbolic line in a 1-d
//space.
 
function StandardUnitImps(d, q, k : general:=false, normaliser:=false )
  if k gt 1 then 
    assert d mod k eq 0;
  end if;
  assert #Factorisation(q) eq 1;
  t:= d div k;
  z:= PrimitiveElement(GF(q^2)); 
  if normaliser then general:=true; end if;
  if general then
    g:= WreathProduct(GU(k, q), Sym(t));
    bool, form:= UnitaryForm(g);
    mat1:= TransformForm(form, "unitary");
    if normaliser then
      g := sub<GL(d,q^2) | g, ScalarMatrix(d,z) >;
    end if;
    return g^mat1;
  end if;

  //we make the standard wreath product
  g:= WreathProduct(SU(k, q), Sym(t));
  //have to fix determinants, which might be -1 at this point.
  newgens:= [ ];
  for i in [1..Ngens(g)] do
    if not Determinant(g.i) eq 1 then //must be -1, do this for	q even
      if k gt 1 then 
        temp:= 
             g.i*GL(d, q^2)!DiagonalMatrix([z^((q+1) div 2)] cat [1 :
             i in [1..k-2]] cat [-z^(-(q+1) div 2)] cat [1 : i in
             [1..d-k]]);
        assert Determinant(temp) eq 1;
        Append(~newgens, temp); 
      else
        Append(~newgens,
              g.i*GL(d, q^2)!DiagonalMatrix([-1] cat [1:i in [2..d]]));
      end if;
    else
      Append(~newgens, GL(d, q^2)!g.i);
    end if;
  end for;

  if k gt 1 then
    diag:= DiagonalMatrix([z] cat [1 : i in [1..k-2]] cat
      [z^-q, z^-1] cat [1 : i in [1..k-2]] cat [z^q] cat [1 : i in
      [1..d-2*k]]);
    diag:= GL(d, q^2)!diag;
  else
    diag:= GL(d, q^2)!DiagonalMatrix([z^(q-1), z^(1-q)] cat [1 : i in
      [3..d]]);
  end if;
  grp:= sub<GL(d, q^2)|newgens, diag>;
  bool, form:= UnitaryForm(grp);
  if not bool then "error: grp not unitary";
    return grp;
  end if;
  bool, form2:= UnitaryForm(SU(d, q));
  mat1:= CorrectForm(form, d, q^2, "unitary");
  mat2:= CorrectForm(form2, d, q^2, "unitary");
  return grp^(mat1*(mat2^-1));
end function;
 

//idea with this second sort is to act as SL(d/2, q^2) on
//<e_1..e_{d/2}> and correct on <f_{d/2}..f_1>.
function UnitImpHalfDim(d, q  : general:=false, normaliser:=false)
  assert IsEven(d);
  k:= d div 2;
  assert #Factorisation(q) eq 1;
  if normaliser then general:=true; end if;

  swap1:= Matrix(GF(q^2), k, k, [<i, k-i+1, 1> : i in [1..k]]);

  p1:= SL(k, q^2).1;
  p2:= SL(k, q^2).2;

  p1img:= Transpose(GL(k, q^2)!ListMatToQ(Eltseq(p1^-1), q));
  p2img:= Transpose(GL(k, q^2)!ListMatToQ(Eltseq(p2^-1), q));
 
  gen1:= DiagonalJoin(p1, swap1*p1img*swap1);
  gen2:= DiagonalJoin(p2, swap1*p2img*swap1);

  z:= PrimitiveElement(GF(q^2));
  diag:= GL(d, q^2)!DiagonalMatrix([z, z^q] cat [1 : i in [1..d-4]] cat
  [z^-1, z^-q]);

  swapmat:= Matrix(GF(q^2), d, d, [<i, i+k, 1> : i in [1..k]] cat
    [<i, i-k, 1> : i in [k+1..d]]);

  if d mod 4 eq 2 and IsOdd(q) then
     swapmat:= swapmat*(GU(d, q).1)^((q+1) div 2);
  end if;
  gens := [GL(d,q^2) | gen1, gen2, diag, swapmat];
  if general then
    Append(~gens, GUMinusSU(d, q));
  end if;
  if normaliser then
    Append(~gens, ScalarMatrix(d,z));
  end if;

  return sub< GL(d, q^2) | gens >;
end function;
