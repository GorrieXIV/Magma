freeze;

/* (DET 2012-01-24)
 - This file has no intrinsics and is not imported anywhere.
 - Its entry has been removed from ClassicalSylow.spec 
 - 
 - See the file correct_form.m in ../Forms for either identical or improved
 - versions of all functions defined here.
*/ 

/* For the form, "type" must be one of "symplectic", "unitary",
 * "orth" (odd dimension), "orth+" or "orth-" (even dimension)
 * 
 * For a group G preserving a form, let C:= ClassicalForms(G), and form:=
 * C`bilinearForm (type symplectic or orthogonal with q odd)
 * C`sesquilinearForm (type unitary)
 * C`quadraticForm (type orthogonal, q,d even)
 * 
 * CorrectFormCS(form,d,q,type)  returns a matrix mat, which
 * satisfies  mat^-1 * form * Transpose(mat) = standard form 
 * or for type "unitary", mat^-1 * form * Transpose(MatToQ(mat)) =
 * standard form where MatToQ(mat) raises each entry of mat to q-th power.
 *
 * But for d even in orthogonal case,
 * we have UT(mat^-1 * form * Transpose(mat)) = standard form
 * where UT transfers entries to upper triangular position
 *
 * NOTE: the standard form is not the same as the form fixed by 
 * SU(d,q), SO(d,q), SOPlus(d,q), etc., so to transform the form to
 * this, you need to call CorrectFormCS twice, once of your group and
 * once on the Magma copy.
 *
 */

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
MatToQ := function(A,q)
// raise every element of matrix A to q-th power
  B := MatrixAlgebra(BaseRing(A),Nrows(A))!0;
  for i in [1..Nrows(A)] do for j in [1..Ncols(A)] do
    B[i][j] := A[i][j]^q;
  end for; end for;
  return B;
end function;

ListMatToQ:= function(a, q)
// raise every element of matrix A to q-th power.
list:= Eltseq(a);
for i in [1..#list] do
    list[i]:= list[i]^q;
end for;
return list;
end function;

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


/*****************************************************************/

/*
 * This takes a quadratic form $F$ and a conjugating matrix $C$ and
 * returns the form that a group preserving $F$ would preserve 
 * after conjugation by $C$.
 */
 
function UT(mat)
 n:=Nrows(mat);
 newform := MatrixAlgebra(BaseRing(mat),n)!0;
 for i in [1..n] do for j in [i..n] do
    if not i eq j then
      newform[i][j]:= mat[i][j] + mat[j][i];
    else
      newform[i][j]:= mat[i][j];
    end if;
  end for; end for;
 return newform;
end function;

function RenormaliseForm(form, conj, n, q)
  return UT(conj^-1*form*Transpose(conj^-1));
end function;

/******************************************************************/
//this returns a matrix which swaps a[i][i] and a[j][j]

function Swapmat(i, j, q, n)
  diag:= [<i,i,1> : i in [1..n]];
  swapmat:= GL(n, q)!Matrix(GF(q), n, n, 
               diag cat [<i,i,0>, <j, j,0>, <i, j, 1>, <j, i, 1>]);  
  return swapmat;
end function;

/******************************************************************/

function Correct2dimQuadForm(form, n, q, type)

  /*
   * The orthogonal groups of minus type in 2 dimensions have 
   * a different form than the central 2 \times 2 block of the form
   * for the orthgonals in > 2 dimensions.
   */
  if n gt 2 and type cmpeq "orth-" then
    form_4:= QuadraticFormCS(GOMinus(4, q));
    goal:= [[form_4[2][2], form_4[2][3]], [0, form_4[3][3]]];
  elif n eq 2 and type cmpeq "orth-" then
    goal:= QuadraticFormCS(GOMinus(2, q));
  end if;

  a:= form[1][1]; b:= form[1][2]; c:= form[2][2];
  p := PolynomialRing(GF(q)); x := p.1;

  if type cmpeq "orth+" then
    if a eq 0 and c eq 0 then
      sqrt:= Root(b, 2);
      return GL(2, q)!DiagonalMatrix([sqrt, sqrt]);
    elif c eq 0 then // so a is not zero, and neither is b.
      mat:= GL(2, q)![0, a*b^-2, b*a^-1, 1];
      return mat^-1;
    elif b eq 0 then // so c is not zero, and neither is b.
      mat:= GL(2, q)![b^-1, 0, b^-1*c, 1];
      return mat^-1;
    else
      //roots exist since form is of plus type.
      roots:= Roots(form[1][1]*x^2 + form[1][2]*x + form[2][2]);
      z:= roots[1][1];
      mat:= GL(2, q)![z, 1, b^-1+z*a*b^-2, a*b^-2]; 
      return mat^-1;
    end if;
  end if;
                 

  /*
   * The remaining code is for orth-. Sadly, I don't know exactly what
   * the form will be, so I've done it for a general form.. 
   */

  //we have matrix [a, b, 0, c] and are aiming for [X, Y, 0,
  //Z]. We will get there by multiplying by [A, B, C, D]. We know 
  //that b and Y are nonzero, and that ax^2+bx+c is irreducible.

  X:= goal[1][1]; Y:= goal[1][2]; Z:= goal[2][2];  

  p := PolynomialRing(GF(q)); x := p.1;

  for A in GF(q) do
    //A;              
    poly:= a*A^2 + x*A*b + x^2*c - X;
    roots:= Roots(poly);
    //roots;
    for root in roots do
      B:= root[1];
      if not (A eq 0 or B eq 0) then
        roots2:= Roots(x^2*B^-2*X + x*B^-1*Y + a*b^-2*B^-2*Y^2 + Z); 
        if #roots2 gt 0 then //it seems that this is always the case
                             //but I can't quite see why.
          D:= roots2[1][1];
          C:= B^-1*(Y*b^-1 + A*D);
          mat:= GL(2, q)![A, B, C, D];
          return mat^-1;
else "AAAAA!";
        end if;
      elif not B eq 0 then //so A = 0.
        C:= Y*B^-1*b^-1;
        roots2:= Roots(x^2*c + x*C*b + C^2*a + Z);
        if #roots2 gt 0 then //again, this is always the case.
          mat:= GL(2, q)![A, B, C, roots2[1][1]];
          return mat^-1;
        end if;
      elif not A eq 0 then //so B eq 0.
        D:= Y*b^-1*A^-1;
        roots2:= Roots(x^2*a + x*D*b + D^2*c + Z);
        if #roots2 gt 0 then //and so is this. 
          mat:= GL(2, q)![A, B, roots2[1][1], D];
          return mat^-1;
        end if;
      end if;
    end for;
  end for;
  "error: form =", form, "goal =", goal;
  return false;
end function;

/*********************************************************************/
      
//this is the main function to standardise a quadratic form.

function CorrectQuadForm(form, n, q, type)
  
  diag:= [<i,i,1> : i in [1..n]];
  s:= 1; f:= n;
  conj:= Identity(GL(n, q));

  while (f - s) gt 1 do

    //if there exists a diagonal entry which is zero
    if exists(t){i : i in [s..f] | form[i][i] eq 0} then

      // move it to row s
      mat:= Swapmat(t, s, q, n);
      form:= RenormaliseForm(form, mat, n, q);
      conj:= conj*mat;

      //if there is an entry in row start which is nonzero
      if exists(t){i : i in [s..f-1] | not form[s][i] eq 0} then  
        mat:= Swapmat(t, f, q, n);
        form:= RenormaliseForm(form, mat, n, q); 
        conj:= conj*mat;
      end if;

      //new x_f -> sum _{j=s,f} form_{s j} old x_j
      mat:= GL(n, q)!Matrix(GF(q), n, n, diag cat
        [<s+j, f, form[s][s+j]> : j in [0..(f-s)]]);
      form:= RenormaliseForm(form, mat, n, q);
      conj:= conj*mat;

      // new x_s = sum _{i=s,f} form_{i f} old x_i
      mat:= GL(n, q)!Matrix(GF(q), n, n, diag cat
          [<s+j, s, form[s+j][f]> : j in [0..(f-s)]]);
      form:= RenormaliseForm(form, mat, n, q);
      conj:= conj*mat;

      s:= s+1; f:= f-1;

    elif exists(t){i : i in [s..f] | exists(u){j: j in [i+1..f] |
                    form[i][j] eq 0}} then
      ri:= Root(form[t][t], 2);
      rj:= Root(form[u][u], 2);
      mat:= GL(n, q)!Matrix(GF(q), n, n, diag cat [<t,t,ri>, <u,t,rj>]);
      form:= RenormaliseForm(form, mat, n, q);
      conj:= conj*mat;

    else
      mat:= GL(n, q)!Matrix(GF(q), n, n, diag cat
         [<s+1, s+1, form[s][s+1]>, <s+2, s+1, form[s][s+2]>]);    
      form:= RenormaliseForm(form, mat, n, q);
      conj:= conj*mat;

    end if;
  end while;

  //the final 2 \times 2 block in the centre.
  h:= n div 2;
  centre:= Submatrix(form, h, h, 2, 2);
  mat:= Correct2dimQuadForm(centre, n, q, type);
  if n gt 2 then
    mat:= GL(n,q)!DiagonalJoin(<Identity(GL(h-1,q)),mat,Identity(GL(h-1,q))>);
  end if;
  form:= RenormaliseForm(form, mat, n, q);

  return form, conj*mat;
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

function CorrectFormCS(form, d, q, type)

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
