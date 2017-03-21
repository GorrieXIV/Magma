freeze;
 
//last edited (for tidyness, and to include quad forms) 03/03/04

import "form.m": SymplecticFormIGLC, ListMatToQ, OrthogonalFormIGLC,  UnitaryFormIGLC;
import "correct_orth.m": CorrectQuadForm;

       
/***********************************************************************
 * just a wee matrix function of obvious use.. 
 **********************************************************************/

function IsAntiDiagonal(mat, d)
  for i in [1..d] do
    for j in [1..d] do
      if (not (i eq (d-j+1))) and (not (mat[i][j] eq 0)) then
        return false;
      end if;
    end for;
  end for;
  return true;
end function; 

/***********************************************************************
 * This function takes a diagonal form matrix and finds a change of
 * basis matrix which sends the form to a diagonal one consisting only
 * of 1s and primitives.
 **********************************************************************/

function ConvertTo1sAndPrims(form, d, q)
  z:= PrimitiveElement(GF(q));
  list:= [];
  nonsquares:= [];
  for i in [1..d] do
    a, b:= IsSquare(form[i][i]);
    if a then 
      Append(~list, (b^-1));
    else 
      a, b:= IsSquare(form[i][i]*(z^-1));
      Append(~list, (b^-1));
      Append(~nonsquares, i);
    end if;
  end for;
  return GL(d, q)!DiagonalMatrix(list);
end function;


/************************************************************************
 * ChangeMat returns either Tranpose(Frobenius(mat)) or
 * Transpose(mat), depending on whether we have a form s.t.
 * g*form*Transpose(g) = form or g * form*(Transpose(Frobenius(g))) 
 * = form.
 */

function ChangeMat(mat, type, d, p)
  if type cmpeq "unitary" then
    return Transpose(GL(d, p^2)!ListMatToQ(mat, p));
  else
    return Transpose(mat);
  end if;
end function;


/***********************************************************************
 * 
 */

function NormaliseForm(form, mat, type, d, p)
  if type cmpeq "unitary" then
    q:= p^2;
  else q:= p;
  end if;
  form:= GL(d, q)!form;
  mat2:= GL(d, q)!ChangeMat(mat, type, d, p);
  return mat*form*mat2;
end function;

/**********************************************************************
 * GetCoords returns the column number in which row i of the form must 
 * be nonzero for conjugation.
 */

function GetCoords(i, d, q, type)
  if type cmpeq "symplectic" then
    return d-i+1;
  else
    return i;
  end if;
end function;


/**********************************************************************
 * CorrectDiag takes a (diagonal or antidiagonal) form matrix, and the 
 * type of form that it is supposed to represent, and finds a 
 * conjugating element such that the group will now preserve a 
 * form matrix consisting of all +1s and -1s.
 * In the case of an orthogonal form of type "oplus" it turns
 * everything into 1s and zs, where z is a primitive element of the
 * field. 
 * In the case of "orth", if the form has an odd number of nonsquares
 * then it converts the matrix to all +1s, if it has an odd number of
 * squares then it converts the matrix to all primitives. 
 * q is a prime power.
 */


function CorrectDiag(form, d, q, type)
  if type cmpeq "unitary" then
    bool, p:= IsSquare(q);
    return GL(d, q)!DiagonalMatrix([Root(form[i][i], p+1)^-1 : i in
                                        [1..d]]);
  elif type cmpeq "symplectic"  then 
    list:= [(form[i][d-i+1])^-1 : i in [1..Quotrem(d, 2)]];
    return GL(d, q)!DiagonalMatrix(list cat [GF(q)!1 : i in 
                                         [1..Quotrem(d, 2)]]); 
  end if;
  
  z:= PrimitiveElement(GF(q));
  conj:= ConvertTo1sAndPrims(form, d, q);
  
  //"counting nonsquare entries.";
  nonsquares:= [];
  for i in [1..d] do
    a, b:= IsSquare(form[i][i]);
    if not a then Append(~nonsquares, i); end if;
  end for;
  ns:= #nonsquares;

  /*
   * if all entries are square then conjugation by conj will do.
   */

  if ns eq 0 then
    return conj;
  end if;
    
 /* At this stage in case orth it is necessary to decide whether we
  * are converting nonsquares into squares or vice versa. We pick
  * whichever one has an even number of occurrences.
  */

  redefined:= false;
  if type eq "orth" then
    if ns eq d then 
      return conj;
    end if;
    if IsOdd(ns) then
      redefined:= true;
      temp:= nonsquares;
      nonsquares:= [x: x in [1..d] | not x in temp];
      ns:= #nonsquares;
    end if;
  end if;
 
 /* collecting field element required to turn pairs of nonsquares 
  * into squares, or in case orth maybe vice versa
  */

  x:= false; 
  while not x do
    b:= Random(GF(q));
    if not redefined then
      x, a:= IsSquare(z^-1 - b^2);
    else
      x, a:= IsSquare(z - b^2);       
    end if;
  end while;

  /*
   * we have to change squares into nonsquares in pairs.
   * First we sort out the coordinates that we will fix. These are
   * the "squares".
   */
        
  quot, rem:= Quotrem(ns, 2); 
  list:= [];
  for i in [1..d] do
    if not i in nonsquares then
      Append(~list, <i, i, GF(q)!1>);
    end if;
  end for;
    
  /* now we convert pairs of "nonsquares"
   */

  for i in [1..quot] do
    Append(~list, <nonsquares[2*i-1], nonsquares[2*i-1], a>);
    Append(~list, <nonsquares[2*i-1], nonsquares[2*i], b>);
    Append(~list, <nonsquares[2*i], nonsquares[2*i-1], b>);
    Append(~list, <nonsquares[2*i], nonsquares[2*i], -a>);
  end for;

  if rem eq 1 then 
    final:= nonsquares[ns];
    Append(~list, <nonsquares[ns], nonsquares[ns], 1>);
  end if;
  mat2:= GL(d, q)!Matrix(GF(q), d, d, list);
  conj:= mat2*conj;
 

  //"moving final nonsquare entry (if exists) to (d, d) position";
  mat3:= Identity(GL(d, q));
  if rem eq 1 then
    if not final eq d then
      newlist:= [<i, i, 1> : i in [1..d] | not i eq final and
        	    not i eq d] cat [<final, d, 1>, <d, final, 1>];
      mat3:= GL(d, q)!Matrix(GF(q), d, d, newlist);
    end if;
  end if;
  conj:= mat3*conj;
  newform:= NormaliseForm(form, conj, type, d, q); 
  
   /* So by this stage we should have the matrix being all squares or
    * all nonsquares, and the final entry being the unique one that is
    * different, if such exists. However, because we've been
    * converting it around, we should re-check that it's all 1s or 
    * all primitives
    */

  mat4:= ConvertTo1sAndPrims(newform, d, q);
  return mat4*conj;

end function;

/****************************************************************/

/*
 * This function returns a matrix that is the identity on the
 * first i rows and columns, and a random (invertible) matrix on 
 * the bottom d \times d block.
 * in the symplectic case, or orthogonals over even fields, 
 * it's the first rows and final columns that are zero.
 * note that there's a minor problem with ensuring that the matrix has
 * nonzero determinant. 
 */

function GetRandomConj(i, d, q, type)
  startelt:= Random(GL(d-i, q));
  newelt:= DiagonalMatrix([GF(q)!1 : j in [1..d]]);
  if type cmpeq "unitary" or (not (type cmpeq "symplectic") and IsOdd(q))
       then 
    for j in [1..d-i] do
        for k in [1..d-i] do
            newelt[i+j][i+k]:= startelt[j][k];
        end for;
    end for;
  else
    for j in [1..d-i] do
        for k in [1..d-i] do
              newelt[i+j][k] := startelt[j][k];
        end for;
    end for;
  end if;
  if not Determinant(newelt) eq 0 then
    //"conj_elt =", newelt;
    return newelt;
  else
    return GetRandomConj(i, d, q, type);
  end if;
end function;


/****************************************************************/

function GetConjMat(form, col, d, q, type)
  conjmat:= DiagonalMatrix([GF(q)!1: i in [1..d]]);
  vec:= form[col];
  if type cmpeq "unitary" or (not type cmpeq "symplectic"  and IsOdd(q))
         then
    for i in [(col+1)..d] do
      conjmat[i][col]:= -form[i][col]*(form[col][col]^-1);
    end for;
  elif type cmpeq "symplectic" or IsEven(q) then
    for i in [1..(d-col)]cat[(d-col+2)..d] do
      conjmat[i][d-col+1]:= -form[i][col]*(form[d-col+1][col]^-1);
    end for;
  end if;
  return GL(d, q)!conjmat;
end function;    


/***********************************************************************/
/*
 * finds a matrix that will conjugate a group preserving form1 of type
 * type into a group preserving a standard form. For symplectic groups
 * this is AntiDiag([1..1 -1..-1]), for the remaining
 * groups I have (somewhat lazily) got it to take them to an orthonormal
 * basis. 
 * For orthogonal groups in even characteristic a completely different
 * function is used - note that this MUST have already been checked,
 * and a quadratic form put into it. 
 */

function CorrectForm(form, d, q, type)

  if type cmpeq "unitary" then
    bool, p:= IsSquare(q);
  else
    p:= q;
  end if;

  if (type cmpeq "orth+" or type cmpeq "orth-") and IsEven(q) then
    form, mat:= CorrectQuadForm(form, d, q, type);
    return mat;
  end if;

  conj:= Identity(GL(d, q));

  /* 
   * We go through row by row doing a type of row reduction. Once it's
   * been done d-1 times then the final row is guaranteed to be
   * nonzero in the right place. 
   */

  for i in [1..d-1] do
   
   /* First we have to deal with the problem that the relevant matrix
    * entry (entry [coords][i]) may be zero.
    * In the unitary case this is entry [i][i].
    * In the symplectic case it's entry [d-i+1][i].
    * In orth+ case it's also [d-i+1][i]. We also need [i][i] to be zero.
    */

    temp:= form;
    mat:= Identity(GL(d, q));
    coords:= GetCoords(i, d, q, type);    
    while temp[coords][i] eq 0 do
      mat:= GetRandomConj(i-1, d, q, type);
      temp:= NormaliseForm(form, mat, type, d, p);
      //"temp =", temp;
    end while;     
    //"leaving while";
    form:= temp;
    conj:= mat*conj;
   
    conjmat:= GetConjMat(form, i, d, q, type);
    form:= NormaliseForm(form, conjmat, type, d, p);
    conj:= conjmat*conj;
   
  end for;

  /* By now the matrix should either be diagonal or antidiagonal.
   */

  //"checking that mat is Diagonal or antidiagonal";
  if type cmpeq "symplectic" then
    assert IsAntiDiagonal(form, d);
  else
    assert IsDiagonal(form);
  end if;

  //"finding element to conjugate torus";
  conj_torus:= CorrectDiag(form, d, q, type);
  form:= NormaliseForm(form, conj_torus, type, d, p);
  conj:= conj_torus*conj;

return GL(d, q)!(conj^-1);

end function;




/*
 * And now some tests.

done:= dim = 2, 3, 4, 5, 6, 7, 8, 9
10 except for 128

dimensions:= [11, 12];
fields:= [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 
          23, 32, 64, 128];

dimensions:= [2, 4, 6, 8, 10, 12];
fields:= [2, 4, 8, 16, 32, 64, 128];

for d in dimensions do
  for f in fields do
    "d =", d, "f =", f;
    "unitary";
    bool, overform:= UnitaryFormIGLC(GU(d, f));
    overmat:= CorrectForm(overform, d, f^2, "unitary");
    for i in [1..50] do
      z:= Random(GL(d, f^2));
      bool, uf:= UnitaryFormIGLC(GU(d, f)^z);
      mat:= CorrectForm(uf, d, f^2, "unitary");
      bool, uf2:= UnitaryFormIGLC(GU(d, f)^(z*mat*overmat^-1)); 
      exists(t){l : l in GF(f) | not l eq 0 and 
                              ScalarMatrix(d, l)*uf2 eq overform};
    end for;
    if not IsEven(d) then
      if not IsEven(f) then
        "orthogonal";
        bool, type, overform:= OrthogonalFormIGLC(GO(d, f), d, f);
        overmat:= CorrectForm(overform, d, f, "orth");
        for i in [1..50] do
          z:= Random(GL(d, f));
          bool, type, of:= OrthogonalFormIGLC(GO(d, f)^z, d, f);
          mat:= CorrectForm(of, d, f, "orth");
          bool, type, form2:= OrthogonalFormIGLC(GO(d,f)^(z*mat*overmat^-1), d, f);          
          exists(t){l : l in GF(f) | not l eq 0 and
                     ScalarMatrix(d, l)*form2 eq overform};
        end for;
      end if;
    else //d even
      "symplectic";
      bool, overform:= SymplecticFormIGLC(Sp(d, f));
      overmat:= CorrectForm(overform, d, f, "symplectic");
      for i in [1..50] do
        z:= Random(GL(d, f));
        bool, sf:= SymplecticFormIGLC(Sp(d, f)^z);
        mat:= CorrectForm(sf, d, f, "symplectic");
        bool, sf2:= SymplecticFormIGLC(Sp(d,f)^(z*mat*overmat^-1)); 
        exists(t){l : l in GF(f) | not l eq 0 and
                     ScalarMatrix(d, l)*sf2 eq  overform};
      end for;
      if IsOdd(f) and (d gt 2 or f gt 3) then
        "orth plus/minus : odd characteristic";
        bool, type, overform1:= OrthogonalFormIGLC(GOPlus(d,f), d, f);
        bool, type, overform2:= OrthogonalFormIGLC(GOMinus(d,f), d, f);
        overmat1:= CorrectForm(overform1, d, f, "orth+");
        overmat2:= CorrectForm(overform2, d, f, "orth-");
        for i in [1..50] do
          z:= Random(GL(d, f));
          bool, type, of:= OrthogonalFormIGLC(GOPlus(d, f)^z, d, f);
          mat:= CorrectForm(of, d, f, "orth+");
          bool, type, f2:= OrthogonalFormIGLC(GOPlus(d, f)^(z*mat*(overmat1^-1)),
              d, f);
          exists(t){l : l in GF(f) | not l eq 0 and ScalarMatrix(d, l)*f2 eq
                   overform1};
          bool, type, of:= OrthogonalFormIGLC(GOMinus(d, f)^z, d, f);
          mat:= CorrectForm(of, d, f, "orth-");
          bool, type, f2:= OrthogonalFormIGLC(GOMinus(d, f)^(z*mat*(overmat2^-1)),
              d, f);
          exists(t){l : l in GF(f) | not l eq 0 and ScalarMatrix(d, l)*f2 eq
                   overform2};
        end for;
      elif f gt 4 or d gt 2 then
        "orth p/m: even characteristic";
        for i in [1..50] do
          z:= Random(GL(d, f));
          q1:= QuadraticForm(GOPlus(d, f)^z);
          mat:= CorrectForm(q1, d, f, "orth+");
          QuadraticForm(GOPlus(d, f)^(z*mat)) eq
            QuadraticForm(GOPlus(d, f));
          q2:= QuadraticForm(GOMinus(d, f)^z);
          mat:= CorrectForm(q2, d, f, "orth-");
          QuadraticForm(GOMinus(d, f)^(z*mat)) eq
           QuadraticForm(GOMinus(d, f)); 
        end for;
      end if;
    end if;
  end for;
end for;


*/
