freeze; 

import "correct_orth.m": CorrectQuadForm;
// import "form.m": MatToQ;

MatToQ := function(A,q)
// raise every element of matrix A to q-th power
  local B;
  B := MatrixAlgebra(BaseRing(A),Nrows(A))!0;
  for i in [1..Nrows(A)] do for j in [1..Ncols(A)] do
    B[i][j] := A[i][j]^q;
  end for; end for;
  return B;
end function;

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
  F := BaseRing(form); assert #F eq q;
  z:= PrimitiveElement(F);
  list:= [F|];
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
  D := DiagonalMatrix(list); 
  return (d ne 0) select GL(d, F)!D else D;
end function;


/************************************************************************
 * ChangeMat returns either Tranpose(Frobenius(mat)) or
 * Transpose(mat), depending on whether we have a form s.t.
 * g*form*Transpose(g) = form or g * form*(Transpose(Frobenius(g))) 
 * = form.
 */

ListMatToQ:= function(a, q)
// raise every element of matrix A to q-th power.
list:= Eltseq(a);
for i in [1..#list] do list[i]:= list[i]^q;
end for;
return list;
end function;

function ChangeMat(mat, type, d, p)
  F := BaseRing(mat);
  if type cmpeq "unitary" then
    assert #F eq p^2;
    return Transpose(GL(d, F)!ListMatToQ(mat, p));
  else
    return Transpose(mat);
  end if;
end function;


/***********************************************************************
 * 
 */

function NormaliseForm(form, mat, type, d, p)
  F := BaseRing(form);
  if type cmpeq "unitary" then
    assert #F eq p^2;
    q:= p^2;
  else
    assert #F eq p;
    q:= p;
  end if;
  form:= form;
  mat2:= ChangeMat(mat, type, d, p);
  if d ne 0 then return GL(d,F)!(mat*form*mat2); end if;
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
 * In the case of an orthogonal form of type "orth+" it turns
 * everything into 1s and zs, where z is a primitive element of the
 * field. 
 * In the case of "orth", if the form has an odd number of nonsquares
 * then it converts the matrix to all +1s, if it has an odd number of
 * squares then it converts the matrix to all primitives. 
 * q is a prime power.
 */


function CorrectDiag(form, d, q, type)
  F := BaseRing(form); assert #F eq q;
  if type cmpeq "unitary" then
    bool, p:= IsSquare(q);
    if d ne 0 then
       return GL(d, F)!DiagonalMatrix([Root(form[i][i], p+1)^-1 : i in
                                        [1..d]]);
    end if;
    return DiagonalMatrix([Root(form[i][i], p+1)^-1 : i in [1..d]]);
  elif type cmpeq "symplectic"  then 
    list:= [F|(form[i][d-i+1])^-1 : i in [1..Quotrem(d, 2)]];
    if d ne 0 then
      return GL(d, F)!DiagonalMatrix(list cat [F | 1 : i in 
                                         [1..Quotrem(d, 2)]]); 
    end if;
    return DiagonalMatrix(list cat [F | 1 : i in [1..Quotrem(d, 2)]]); 
  end if;
  
  z:= PrimitiveElement(F);
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

  // save random number state, then set to known value for reproducible
  // results; Derek implied this was desirable for more than just
  // debugging purposes.
  s1,s2 := GetSeed();
  SetSeed(0);

  x:= false; 
  while not x do
    b:= Random(F);
    if not redefined then
      x, a:= IsSquare(z^-1 - b^2);
    else
      x, a:= IsSquare(z - b^2);       
    end if;
  end while;

  // restore the random state
  SetSeed(s1,s2);

  /*
   * we have to change squares into nonsquares in pairs.
   * First we sort out the coordinates that we will fix. These are
   * the "squares".
   */
        
  quot, rem:= Quotrem(ns, 2); 
  list:= [];
  for i in [1..d] do
    if not i in nonsquares then
      Append(~list, <i, i, F!1>);
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
  mat2:= GL(d, F)!Matrix(F, d, d, list);
  conj:= mat2*conj;
 

  //"moving final nonsquare entry (if exists) to (d, d) position";
  mat3:= Identity(GL(d, F));
  if rem eq 1 then
    if not final eq d then
      newlist:= [<i, i, 1> : i in [1..d] | not i eq final and
        	    not i eq d] cat [<final, d, 1>, <d, final, 1>];
      mat3:= GL(d, F)!Matrix(F, d, d, newlist);
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

function GetRandomConj(i, d, F, type)
  q := #F;
  startelt:= Random(GL(d-i, F));
  newelt:= DiagonalMatrix([F!1 : j in [1..d]]);
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
    return GetRandomConj(i, d, F, type);
  end if;
end function;


/****************************************************************/

function GetConjMat(form, col, d, q, type)
  F := BaseRing(form); assert #F eq q;
  conjmat:= DiagonalMatrix([F!1: i in [1..d]]);
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
  return GL(d, F)!conjmat;
end function;

function symplectic_std(F)
/* this function is written by Markus Kirschmer (16/10/09)
 * The following should transform a skewsymmetric matrix over any field of
 * char \ne 2  to  the standard one. Is simply constructs pairwise
 * perpendicular 2-dimensional subspaces that yield the forms [[0,1], [0,-1]].
 * Finally it reorders the bases.
 */

  K:= BaseRing(F);
  n:= Nrows(F);

  T:= MatrixRing(K, n) ! 1;
  for i:= 1 to n div 2 do
    b:= T[2*(i-1)+1];
    Fb:= F * Matrix(1, Eltseq(b));
    ok:= exists(j){j : j in [2*i..n] | not IsZero(T[j] * Fb) };
    assert(ok); // otherwise F is singular
    SwapRows(~T, 2*i, j);
    T[2*i]/:= -(T[2*i] * Fb)[1];
    Fc:= F * Matrix(1, Eltseq(T[2*i]));
    for j:= 2*i+1 to n do
      T[j]+:= T[2*i] * (T[j] * Fb)[1] - b * (T[j]*Fc)[1];
    end for;
  end for;
  return Matrix(T[[1..n by 2] cat [n..1 by -2]])^-1;
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

intrinsic CorrectForm(
    form::AlgMatElt, d::RngIntElt, q::RngIntElt, type::MonStgElt:
Restore := false) -> GrpMatElt
{form should be a classical form of type type fixed by a subgroup G of
 GL(d,q). Return a matrix mat such that G^mat fixes our preferred
 standard form.}

  F := BaseRing(form); assert #F eq q;
  if type cmpeq "unitary" then
    bool, p:= IsSquare(q);
  else
    p:= q;
  end if;

  if type cmpeq "orthogonalplus" then type := "orth+"; end if;
  if type cmpeq "orthogonalminus" then type := "orth-"; end if;

// this special version only called for q odd 
  if (type cmpeq "orth+" or type cmpeq "orth-") and IsEven(q) then
    form, mat:= CorrectQuadForm(form, d, q, type);
    return mat;
  end if;

  conj:= IdentityMatrix(F,d);

  /* 
   * We go through row by row doing a type of row reduction. Once it's
   * been done d-1 times then the final row is guaranteed to be
   * nonzero in the right place. 
   */

  // save random number state, then set to known value for reproducible
  // results; Derek implied this was desirable for more than just
  // debugging purposes.
  s1,s2 := GetSeed();
  SetSeed(0);

  for i in [1..d-1] do
   
   /* First we have to deal with the problem that the relevant matrix
    * entry (entry [coords][i]) may be zero.
    * In the unitary case this is entry [i][i].
    * In the symplectic case it's entry [d-i+1][i].
    * In orth+ case it's also [d-i+1][i]. We also need [i][i] to be zero.
    */

    temp:= form;
    mat:= Identity(GL(d, F));
    coords:= GetCoords(i, d, q, type);    
    while temp[coords][i] eq 0 do
      mat:= GetRandomConj(i-1, d, F, type);
      temp:= NormaliseForm(form, mat, type, d, p);
    end while;     
    form:= temp;
    conj:= mat*conj;
   
    conjmat:= GetConjMat(form, i, d, q, type);
    form:= NormaliseForm(form, conjmat, type, d, p);
    conj:= conjmat*conj;
   
  end for;

  // restore the random state
if Restore then 
  SetSeed(s1,s2);
end if;

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

  conj := conj^-1;
  if d ne 0 then  //GL(0,F) doesn't exist
    conj := GL(d,F)!conj;
  end if;
  return conj;
end intrinsic;

intrinsic CorrectForm(
    form::GrpMatElt, d::RngIntElt, q::RngIntElt, type::MonStgElt: Restore := false) -> GrpMatElt
{form should be a classical form of type type fixed by a subgroup G of
 GL(d,q). Return a matrix mat such that G^mat fixes our preferred
 standard form.}
  return CorrectForm(Matrix(form),d,q,type: Restore := Restore);
end intrinsic;

intrinsic TransformForm(
    form::AlgMatElt, type::MonStgElt : field:=0,
Restore := false ) -> GrpMatElt
{form should be a classical form of type "type" fixed by a subgroup G of
 GL(d,q). Return a matrix mat such that G^mat lies in the classical group
 returned by the Magma function  GU, Sp, GO(Plus/Minus).}

/* 16/10/09 Put in Markus Kirschmer's code for sympectic case over
 * infinite field.
 */
 
/* form is assumed to be of type "type" and fixed by  group G <= GL(d,q).
 * where field = GF(q), which defaults to BaseRing(form).
 * For the orthogonal types, form should be as returned by
 * SymmetricBilinearForm, except when q is even, when it should
 * be as returned by QuadraticForm.
 * return g in GL(d,q) such that G^g fixes the Magma form.
 * i.e. G^g <= Sp(d,q), GU(d,sqrt(q)) or GO(Plus/Minus)(d,q).
 *
 * type can be "symplectic", "unitary", "orth", "orthogonal",
 * "orthogonalcircle", "orth+", "orthogonalplus", "oplus",
 *  "orth-", "ominus", "orthogonalminus".
 */
  if not IsFinite(BaseRing(form)) and type eq "symplectic" then
    return symplectic_std(form);
  end if;
   
   UT := function(mat)
    n:=Nrows(mat); assert n eq Ncols(mat);
    K:=BaseRing(mat);
    nmat := MatrixAlgebra(K,n)!mat;
    for i in [2..n] do for j in [1..i-1] do
       nmat[j][i] +:=  nmat[i][j];  nmat[i][j]:=0;
    end for; end for;
    return nmat;
   end function;

   d := NumberOfRows(form);

   if field cmpeq 0 then
     field := BaseRing(form);
   else
     assert BaseRing(form) subset field;
     form := MatrixAlgebra(field,d)!form;
   end if;

   q := #field;

   if type in  { "orth", "orthogonal", "orthogonalcircle" }
      then type := "orth";
   elif type in  { "orth+", "orthogonalplus", "oplus" }
      then type := "orth+";
   elif type in  { "orth-", "orthogonalminus", "ominus" }
      then type := "orth-";
   elif type ne "symplectic" and type ne "unitary" then
     error "illegal form type";
   end if;

   if type eq "orth+" or type eq "orth-" then
   //check that the specified type is correct
     rtype := type eq "orth+" select "orthogonalplus" else "orthogonalminus";
     if IsOdd(q) and rtype ne SymmetricBilinearFormType(form:field:=field)
     or IsEven(q) and rtype ne QuadraticFormType(form:field:=field) then
       error "Orthogonal form type specified is incorrect";
     end if;
   end if;

   g := CorrectForm(form, d, q, type: Restore := Restore);
   if type eq "symplectic" then 
     assert g^-1 * form * Transpose(g^-1) eq Matrix(field,d,d,
  [<i,d+1-i,1>:i in [1..d div 2]] cat [<i,d+1-i,-1>:i in [d div 2 + 1 ..d]]  );
     return g;
   elif type eq "unitary" then 
     f := Factorisation(q);
     if f[1][2] mod 2 eq 1 then
       error "Field size must be a square for unitary type";
     end if;
     rq := f[1][1]^(f[1][2] div 2);
     mform := StandardHermitianForm(d,field);
     g2 := CorrectForm(mform, d, q, type: Restore := Restore);
     g := g*g2^-1;
     assert g^-1 * form * Transpose( MatToQ(g^-1, rq) ) eq mform;
     return g;
   elif type eq "orth" then 
     if d ge 3 then
       mform := SymmetricBilinearForm(d,field);
     else
       mform := (d eq 1) select Matrix( 1,1, [field| 1/2] ) 
         else Matrix(0,0,[field|]);
     end if;
     mform := SymmetricBilinearForm(d,field);
     g2 := CorrectForm(mform, d, q, type: Restore := Restore);
     g := g*g2^-1;
     //in this case, it is possible that form is transposed to a non-square scalar multiple
     cform := g^-1 * form * Transpose(g^-1);
     for i in [1..d] do for j in [1..d] do
       if cform[i][j] ne 0 then
         ffac := cform[i][j]/mform[i][j];
         break i;
       end if;
     end for; end for;
     assert d eq 0 or g^-1 * form * Transpose(g^-1) eq ffac*mform;
     return g;
   elif type eq "orth+" then 
     if d eq 2 and q le 3 then
       mform := IsEven(q) select Matrix(field,2,2,[0,1,0,0])
                            else Matrix(field,2,2,[0,1,1,0]);
     else
       if IsEven(q) then mform := QuadraticFormPlus(d,field);
       else mform := SymmetricBilinearFormPlus(d,field);
       end if;
     end if;
     g2 := CorrectForm(mform, d, q, type: Restore := Restore);
     g := g*g2^-1;
     if IsEven(q) then
       assert UT(g^-1 * form * Transpose(g^-1)) eq mform;
     else
       assert g^-1 * form * Transpose(g^-1) eq mform;
     end if;
     return g;
   elif type eq "orth-" then 
     if IsEven(q) then mform := QuadraticFormMinus(d,field);
     else mform := SymmetricBilinearFormMinus(d,field);
     end if;
     g2 := CorrectForm(mform, d, q, type: Restore := Restore);
     g := g*g2^-1;
     if IsEven(q) then
       assert UT(g^-1 * form * Transpose(g^-1)) eq mform;
     else
       assert g^-1 * form * Transpose(g^-1) eq mform;
     end if;
     return g;
   end if;
end intrinsic;

intrinsic TransformForm(
    form::GrpMatElt, type::MonStgElt : field:=0, Restore := false ) -> GrpMatElt
{A version of TransformForm using GrpMatElt as argument type for form}
   local form2;
   form2 := MatrixAlgebra(BaseRing(form), Nrows(form))!form;
   return TransformForm(form2, type : field:=field, Restore := Restore );
end intrinsic;

intrinsic TransformForm(G::GrpMat : Scalars:=false, Restore := false) -> GrpMatElt
{If the input group G fixes a classical form, then return a matrix mat such
that G^mat lies in the classical group returned by the Magma function
GU, Sp, GO(Plus/Minus). Otherwise return false.}
  local r, type, form, d, q;
  r := ClassicalForms(G : Scalars:=Scalars);
  type := r`formType;
  if type eq "linear" then
    "No fixed form";
    return false;
  end if;
  d := Degree(G);
  q := #BaseRing(G);
  if IsEven(q) and type in {"orthogonalplus", "orthogonalminus"} then 
    form := r`quadraticForm;
  elif type eq "unitary" then
    form := r`sesquilinearForm;
  else form := r`bilinearForm;
  end if;

  return TransformForm(form, type: Restore := Restore);
end intrinsic;
