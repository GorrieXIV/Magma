freeze;

//23/04/03 testing, and some significant tidying up, in particular to
//use the generators for the unitary groups as given in magma rather
//than re-writing them down.

/* 
 * The maximal reducible subgroups of the unitary groups consist of
 * the following: 
 * stabilisers of isotropic k-spaces 1 \leq k \leq Floor(d/2)
 * stabilisers of unitary k-spaces 1 \leq k < Ceiling(d/2)
 * we can't have a unitary k-space of dimension d/2 as this is a
 * subgroup of an imprimitive group.
 */

//in all of the following, p is *not* neccesarily prime - it is simply
//the square root of q.

import "matrixfunctions.m": SquareBlockMatrix, ZeroMatrix;
import "classicals.m": GUMinusSU;

ListMatToQ:= function(a, q)
// raise every element of matrix A to q-th power.
  local list;
  list:= Eltseq(a);
  for i in [1..#list] do list[i]:= list[i]^q; end for;
  return list;
end function;

function ChangeMat(mat, k, p)
  form:= GL(k, p^2)!Matrix(GF(p^2), k, k, [<i, k-i+1, 1>: i in [1..k]]);
  mat:= Eltseq(mat^-1);
  mat:= ListMatToQ(mat, p);
  mat:= Matrix(GF(p^2), k, k, mat);
  return form*Transpose(mat)*form;
end function;

function GetA(p)
  for a in GF(p^2) do
    if a + a^p eq 1 then
      return a;
    end if;
  end for;
  "error: couldn't find element of norm 1";
  return 0;
end function;

function OddBlocks(k, p)
  k2:= Floor(k/2);
  block:= [* *];
  for i in [1, 2] do
    block[1+9*(i-1)]:= Submatrix(SU(k, p).i, 1, 1, k2, k2);
    block[2+9*(i-1)]:= Submatrix(SU(k, p).i, 1, 1+k2, k2, 1);
    block[3+9*(i-1)]:= Submatrix(SU(k, p).i, 1, 2+k2, k2, k2);

    block[4+9*(i-1)]:= Submatrix(SU(k, p).i, 1+k2,1,1,k2);
    block[5+9*(i-1)]:= Submatrix(SU(k, p).i, 1+k2,1+k2,1,1);
    block[6+9*(i-1)]:= Submatrix(SU(k, p).i, 1+k2,2+k2,1,k2);

    block[7+9*(i-1)]:= Submatrix(SU(k, p).i, 2+k2,1,k2,k2);
    block[8+9*(i-1)]:= Submatrix(SU(k, p).i, 2+k2,1+k2,k2,1);
    block[9+9*(i-1)]:= Submatrix(SU(k, p).i, 2+k2,2+k2,k2,k2);
  end for;
  return block;
end function;

function EvenBlocks(k, p)
  k2:= k div 2;
  block:= [];
  for i in [1, 2] do
    block[1+4*(i-1)]:= Submatrix(SU(k, p).i, 1, 1, k2, k2);
    block[2+4*(i-1)]:= Submatrix(SU(k, p).i, 1, 1+k2, k2, k2);
    block[3+4*(i-1)]:= Submatrix(SU(k, p).i, 1+k2, 1, k2, k2);
    block[4+4*(i-1)]:= Submatrix(SU(k, p).i, 1+k2, 1+k2, k2,k2);
  end for;
  return block;
end function;



function IsotropKStab(d, p, k : normaliser:=false, general:=false )

local z;

  if normaliser then general:=true; end if;

  if d eq 3 then //dfh
    assert k eq 1;
    K := GF(p^2);
    z := PrimitiveElement(K);
    D := DiagonalMatrix([K|z^(-p),z^(p-1),z]);
    beta:= -(1+z^(p-1))^(-1);
    assert (beta + beta^p) eq GF(p)!(-1);
    if p eq 2 then
      gens := [ GL(d, p^2) | D, Matrix(K,3,3,[1,0,0,1,1,0,beta,1,1]),
                          Matrix(K,3,3,[1,0,0,beta^2,1,0,beta,beta,1]) ];
    else
      gens := [ GL(d, p^2) | D, Matrix(K,3,3,[1,0,0,-1,1,0,beta,1,1]) ];
    end if;
    if general then
      Append(~gens, GUMinusSU(d, p));
    end if;
    if normaliser then
      Append(~gens, ScalarMatrix(d,z));
    end if;
    return sub< GL(d, p^2) | gens >;
  end if;

  z:= PrimitiveElement(GF(p^2));
  half:= Ceiling(d/2);
  if IsEven(p) then
    nu:= GF(p)!1;
  else
    nu:= z^((p+1) div 2);
  end if;
  assert (nu + nu^p) eq GF(p)!0;

  // Brooksbank asserts that there is an O(log p) algorithm for 
  // solving beta + beta^p eq -1 in GF(p^2) for prime p. need to find
  // it. 
  beta:= -(1+z^(p-1))^(-1);
  assert (beta + beta^p) eq GF(p)!(-1);

  gens:= [GL(d,p^2)|];

 /*
  * First we get the generators for GL(k, p^2) acting on the isotropic
  * {e_1, \ldots, e_k} and make requisite adjustments for {f_k,
  * \ldots, f_1}. 
  * If the space that we are stabilising is half the dimension then we
  * don't get the whole of GL(k, p^2) - We have all matrices whose
  * determinant lies in GF(p), in each block.
  */

  // first we deal with GL.1
  if not (2*k eq d or 2*k eq (d-1)) then
      diag:= DiagonalMatrix([z] cat [1: i in [2..k]] cat [z^-1] cat
                            [1 : i in [k+2..d-k-1]] cat [z^p] cat [1 :
                            i in [d-k+1..d-1]] cat [z^(-p)]);
      Append(~gens, diag);
  elif (2*k eq d-1) then
     diag:= DiagonalMatrix([z] cat [1 : i in [2..half-1]] cat
             [z^(p-1)] cat [1 : i in [half+1..d-1]] cat [z^-p]);
     Append(~gens, diag); 
  else /*k eq half then*/
      Append(~gens, DiagonalMatrix([z, z^-1] cat [1: i in [3..d-2]]
                      cat [z^p, z^(-p)]));
      Append(~gens, DiagonalMatrix([z^(p+1)] cat [1 : i in [2..d-1]]
                      cat [z^(-(p+1))]));
  end if;

  if k gt 1 then
    temp:= SL(k, p^2).2;
    temp2:= ChangeMat(temp, k, p);
    if k lt d/2 then
      Append(~gens,
              DiagonalJoin(<temp, IdentityMatrix(GF(p^2), d-2*k), temp2>));
    else
      Append(~gens, DiagonalJoin(<temp, temp2>));
    end if;
  end if;

 /*
  * Now we need SU(d-2k, p), acting on {e_k+1.. e_{half}, ?w?
  * (depending on odd or even d), f_{d/2}..f_{k+1}}.
  */
   
  if (d - 2*k) gt 1 then
      Append(~gens, DiagonalJoin(<IdentityMatrix(GF(p^2), k), SU(d - 2*k, p).1,
                    IdentityMatrix(GF(p^2), k)>));
      Append(~gens, DiagonalJoin(<IdentityMatrix(GF(p^2), k), SU(d -2*k, p).2,
                    IdentityMatrix(GF(p^2), k)>));
  end if;

/*
 * Finally we need the transvections. We take three: one mapping f_1
 * to f_1 + nu.e_1 and fixing the rest, one mapping f_1 to f_1 +
 * f_k+1, e_k+1 to -e_1+e_k+1 and fixing the rest
 * Because of the irreducibility of the actions of SU(d-2k, p)
 * and GL(k, p^2) this should generate the whole collection of
 * transvections. 
 */

  Append(~gens, Matrix(GF(p^2), d, d,
              [<i,i,1>: i in [1..d]] cat [<d, 1, nu>]));
  if d eq (2*k+1) and IsOdd(p) then
    //x:= Root((GF(p^2)!-2), p+1); - too slow
    lm2 := Log(z,GF(p^2)!-2);
    x := z^(lm2 div (p+1));
    Append(~gens, Matrix(GF(p^2), d, d,
              [<i,i,1>: i in [1..d]] cat [<d, 1, 1>, <half, 1, -(x^p)>,
              <d, half, x>]));
  elif d eq (2*k+1) and IsEven(p) then
    Append(~gens, Matrix(GF(p^2), d, d,
              [<i,i,1>: i in [1..d]] cat [<d, 1, beta>, <half, 1, 1>, <d,
              half, 1>]));
  else 
    Append(~gens, Matrix(GF(p^2), d, d,
              [<i,i,1>: i in [1..d]] cat [<d, d-k,1>, <k+1, 1, -1>]));
  end if; 
  if general then
    Append(~gens, GUMinusSU(d, p));
  end if;
  if normaliser then
    Append(~gens, ScalarMatrix(d,z));
  end if;
  return sub<GL(d, p^2)|gens>; 

end function;




/*****************************************************************/
/*****************************************************************/
/*****************************************************************/

/*
 * The second function that is required is the stabilisers of
 * nonisotropic subspaces. 
 * These groups have the structure: SU(x, q) \times SU(d-x, q).(q+1),
 * which I imagine means that we can have any determinant in \gf(q) on 
 * each part, as long as is balanced by the other part. 
 * So, we need two sets of generators for the SUs, plus one for the 
 * .(q+1) on the outside of determinants.
 * We treat SU(4, 2) as a special case.
 */

function NonisotropKStab(d, p, k : general:=false, normaliser:=false )

  assert d gt 2;
  //if d lt 5 then assert p gt 2; end if; 
 /*
  * We require k < d/2 as otherwise we have a subgroup of an
  * imprimitive group.
  */
  assert k lt d/2;

  if normaliser then general:=true; end if;

  z:= PrimitiveElement(GF(p^2));
  if p eq 2 then
    nu:= 1;
  else
    nu:= z^((p+1) div 2);
  end if;

  gens:= [GL(d,p^2)|];

 /*
  * The structure of the
  * matrices depends on whether k is odd or even, and whether d is odd
  * or even.
  * SU(k, p) is blocks around the edges with the identity in the
  * middle, unless k is odd in which case we have to mess around with
  * either w (if d is odd) or e_d and f_d (d even). SU(d-k, p) is then
  * in the middle, unless d is even and k is odd in which case, once
  * again, the middle two rows and columns are messed up.  
  */
  k2:= Floor(k/2);
  d2:= Floor(d/2);
  r:= Floor((d-k)/2);
  if IsEven(k) then
    // SU(k, p)
    block:= EvenBlocks(k, p);
    for i in [1, 2] do
      Append(~gens, SquareBlockMatrix(
        <block[1+(i-1)*4], 0, block[2+(i-1)*4],
                0, IdentityMatrix(GF(p^2), d-k),  0,
        block[3+(i-1)*4],  0, block[4+(i-1)*4]>, p^2));
    end for;
    
    //SU(d-k, p)
    for i in [1, 2] do
      Append(~gens, DiagonalJoin(<IdentityMatrix(GF(p^2), k2), SU(d-k, p).i,
                                  IdentityMatrix(GF(p^2), k2)>));
    end for;
     
    //extra diagonal matrix
    diag:= DiagonalMatrix([z] cat [1:i in [1..k2-1]] cat [z^-1] cat
    [1:i in [k2+2..d-k2-1]] cat [z^p] cat [1:i in [1..k2-1]] cat
    [z^-p]);
    //"diag =", diag;
    Append(~gens, diag);
    if general then
      Append(~gens, GUMinusSU(d, p));
    end if;
    if normaliser then
      Append(~gens, ScalarMatrix(d,z));
    end if;
    return sub<GL(d, p^2)|gens>;
     
  elif IsOdd(d) and IsOdd(k) then

    if k gt 1 then
      //We take SU(k, p) as semi^2 blocks in the corners, plus small
      //blocks at the obvious junctions in the middle row and middle
      //column.

      block:= OddBlocks(k, p);
      i1:= IdentityMatrix(GF(p^2), (d-k) div 2);

      for i in [0, 9] do
        Append(~gens, SquareBlockMatrix(<
          block[1+i], 0, block[2+i],  0, block[3+i],
          0,        i1,    0,        0,  0,
          block[4+i], 0, block[5+i],0, block[6+i],
          0,         0,    0,       i1,  0,
          block[7+i], 0, block[8+i], 0, block[9+i]>, p^2));
      end for;
 
    else //k eq 1
      Append(~gens, SU(d, p).1);
    end if;
     

    //SU(d-k, p)
    block:= EvenBlocks(d-k, p);
    for i in [0, 1] do
      submatrix:= SquareBlockMatrix(<
        block[1+i*4],   0,     block[2+i*4],
           0,         IdentityMatrix(GF(p^2), 1),  0,
        block[3+i*4],   0,      block[4+i*4]>, p^2);
      if k gt 1 then
        submatrix:= DiagonalJoin(<IdentityMatrix(GF(p^2), k2), submatrix,
                                  IdentityMatrix(GF(p^2), k2)>);
      end if;
      Append(~gens, submatrix);
    end for;

    //extra diagonal matrix
    if d gt 3 then
      if k2 gt 0 then
       Append(~gens, DiagonalMatrix(GF(p^2), [1 : i in [1..k2-1]] cat [z] cat
       [1: i in [1..((d-k)div 2 -1)]] cat [z^-1, 1, z^p] cat
       [1: i in [1..((d-k)div 2 -1)]] cat [z^-p] cat [1 : i in [1..k2-1]]));
      end if;
    end if;

    if general then
      Append(~gens, GUMinusSU(d, p));
    end if;
    if normaliser then
      Append(~gens, ScalarMatrix(d,z));
    end if;
    return sub<GL(d, p^2)|gens>; 
  end if;

  /* d even k odd. Here we have to construct two orthonormal
   * vectors to lie in the k-space and the (d-k)-space respectively.
   */    
  //SU(k, p)    
   k2:= (k-1) div 2;
   r:= (d-k) div 2;
   id:= IdentityMatrix(GF(p^2), r);    
   a:= GetA(p);
   //b:= Root(GF(p^2)!(-1), p+1);  -  too slow!
   b := IsEven(p) select z^(p-1) else z^((p-1) div 2);

   if (k gt 3) or (p gt 2 and k eq 3) then
     //SU(k, p).1
     g1:= DiagonalMatrix([1 : i in [1..k2-1]] cat [z] 
             cat [1 : i in [k2+1..(d2-1)]]);
     g2:= Matrix(GF(p^2), 2, 2, [z^(p-1)*a + a^p, z^(p-1)-1, (z^(p-1)
      - 1)*a^(p+1), z^(p-1)*a^p + a]);
     g3:= DiagonalMatrix([1 : i in [1..(d2 - k2 -1)]]
      cat [z^(-p)] cat [1 : i in [(d2 - k2 + 2)..d2]]);
     mat:= DiagonalJoin(<g1, g2, g3>);
     //mat;
     Append(~gens, mat);      
      
     //SU(k, p).2
     m1:= Submatrix(SU(k, p).2, 1, 1, k2, k2);
     m2:= Matrix(GF(p^2), k2, 2, [<k2, 1, -a>, <k2, 2, -1>]);
     m3:= Submatrix(SU(k, p).2, 1, k2+2, k2, k2);
     m4:= Matrix(GF(p^2), 2, k2, [<1, 1, -1>, <2, 1, -a^p>]);
     m5:= Matrix(GF(p^2), 2, 2, [(a^p-a), -2, -2*a^(p+1), a-a^p]);
     m6:= Submatrix(SU(k, p).2, k2+2, 1, k2, k2);
     m7:= Submatrix(SU(k, p).2, k2+2, k2+2, k2, k2);
     Append(~gens, SquareBlockMatrix(<
         m1, 0, m2, 0, m3,
         0, id, 0, 0, 0,
         m4, 0, m5, 0, 0,
         0, 0, 0, id, 0, 
         m6, 0, 0, 0, m7>, p^2));

    
   elif k eq 3 and p eq 2 then
     i1:= IdentityMatrix(GF(p^2), 1);
     m1:= Matrix(GF(p^2), 1, 2, [z^2, z]);
     m2:= Matrix(GF(p^2), 1, 1, [z]);
     m3:= Matrix(GF(p^2), 2, 2, [1, 0, 0, 1]);
     m4:= Matrix(GF(p^2), 2, 1, [z^2, z]); 
     Append(~gens, SquareBlockMatrix(<
         i1, 0, m1, 0, m2,
         0,  id,0, 0, 0,
         0, 0,  m3, 0, m4,
         0, 0,  0,  id, 0,
         0, 0,   0,  0, i1>, p^2));
      
     i2:= IdentityMatrix(GF(p^2), 2);
     m5:= Matrix(GF(p^2), 2, 1, [1,z^2]);
     m6:= Matrix(GF(p^2), 1, 2, [z, 1]);
     Append(~gens, SquareBlockMatrix(<
         m2, 0, m6, 0, i1,
         0,  id,0,  0,  0,
         m5, 0, i2, 0, 0,
         0,  0, 0, id, 0,
         i1, 0, 0, 0, 0>, p^2));

   elif k eq 1 then
     Append(~gens, DiagonalJoin(<IdentityMatrix(GF(p^2), r),
      Matrix(GF(p^2), 2, 2, [z^(p-1)*a + z^(1-p)*a^p, z^(p-1)-z^(1-p),
              a^(p+1)*(z^(p-1)-z^(1-p)),z^(p-1)*a^p+a*z^(1-p)]),
                                 IdentityMatrix(GF(p^2), r)>));
   end if; 
     
  
  //SU(d-k, q). We may assume wlog that either (d-k) > 3 or (q \neq 2)
  //as (d-k=3, q=2 => k = 1 and SU(4, 2) \cong Sp(4, 3) is a special
  //case.
  //assert ((d-k gt 3) or (d-k eq 3 and p gt 2));
  r:= (d-k)div 2;
  g1:= DiagonalMatrix([1 : i in [1..d2-2]] cat [z]);
  g2:= Matrix(GF(p^2), 2, 2, [a + a^p*z^(p-1), 1-z^(p-1), a^(p+1) -
        (a^(p+1)*z^(p-1)), (a^p +a*z^(p-1))]);
  g3:= DiagonalMatrix([z^(-p)] cat [1 : i in [1..d2-2]]);
  Append(~gens, DiagonalJoin(<g1, g2, g3>));

  id:= IdentityMatrix(GF(p^2), k2);
  m1:= Submatrix(SU(d-k, p).2, 1, 1, r, r);
  m2:= Matrix(GF(p^2), r, 2, [<r, 1, a^p*b>, <r, 2, -b>]);
  m3:= Submatrix(SU(d-k, p).2, 1, r+2, r, r); 
  m4:= Matrix(GF(p^2), 2, r, [<1, 1, b^-1>, <2, 1, -a*b^(-1)>]);  
  m5:= Matrix(GF(p^2), 2, 2, [a - a^p, 2, 2*a^(p+1), (a^p-a)]);
  m7:= Submatrix(SU(d-k,p).2, r+2, 1, r,r);
  m9:= Submatrix(SU(d-k,p).2,r+2,r+2,r, r);

  mat:= SquareBlockMatrix(< m1,m2,m3, m4,m5,0, m7,0,m9 >, p^2);
  if k2 gt 0 then
    mat:= DiagonalJoin(<id, mat, id>);
  end if;
  Append(~gens, mat);
    
  //diagonal matrix: this seems to be misbehaving
  if k gt 1 or IsOdd(d) then
  diag:= DiagonalMatrix([z] cat [1:i in [1..k2-1]] cat [z^-1] cat
      [1:i in [k2+2..d-k2-1]] cat [z^p] cat [1:i in [1..k2-1]] cat
      [z^-p]);
     Append(~gens, diag);
  end if;
  if general then
    Append(~gens, GUMinusSU(d, p));
  end if;
  if normaliser then
    Append(~gens, ScalarMatrix(d,z));
  end if;
  return sub<GL(d, p^2)|gens>;
end function;

function ReduciblesUnit(d, q)
  assert d gt 2;
  if d lt 5 and q eq 2 then
    psu := PSU(d,q);
    phi := hom< SU(d,q)->psu | [psu.1,psu.2] >;
    max := [ m`subgroup @@ phi : m in MaximalSubgroups(psu) ];
    return [ m: m in max | not IsIrreducible(m) ];
  end if;
  list:= [];
  for i in [1.. d div 2] do
    Append(~list, IsotropKStab(d, q, i));
  end for;
  for i in [1.. (d-1) div 2] do
    Append(~list, NonisotropKStab(d, q, i));
  end for;
  return list;
end function;
