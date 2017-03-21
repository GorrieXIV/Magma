freeze;

//23/04/04 testing, tidying up code + changing p to q to emphasise
//that works for prime powers.

/*
 * We use the generators for Sp and GL as described by Don. maximal
 * subgroups are: the point stabiliser (don't forget Sp is
 * transitive), the k-dim isotropic subspace stabiliser (2 \leq k \leq 
 * d/2), the k-dim symplectic subspace stabiliser (k even, 2 \leq k <
 * d/2). Note the "<" at the top of second bound, this is because it is
 * contained in an imprimitive group.
 */

/*
 * The point stabiliser has structure (p^d-1):((p-1) \times Sp(d-2,
 * p)). We stabilise <[1, 0, \ldots, 0]>.
 */

import "matrixfunctions.m": SquareBlockMatrix, ZeroMatrix;
import "classicals.m": NormSpMinusSp;

function PointStabSp(d, q : normaliser:=false)
  assert IsEven(d) and d gt 2;

  z:= PrimitiveElement(GF(q));
  half:= d div 2;  
  diag:= [<i,i,1> : i in [1..d]];
 
  diag1:= DiagonalMatrix([z] cat [1 : i in [2..d-1]] cat [z^-1]);
  
  //Sp(d-2, q) on <e2, e3, \ldots, f3, f2>.
  symp1:= DiagonalJoin(<IdentityMatrix(GF(q), 1), Sp(d-2, q).1,
                        IdentityMatrix(GF(q), 1)>);
  symp2:= DiagonalJoin(<IdentityMatrix(GF(q), 1), Sp(d-2, q).2,
                        IdentityMatrix(GF(q), 1)>); 

  //The transvections around the edge, the "p-gunk".
  trans1:= Matrix(GF(q), d, d, [<d, 1, 1>] cat diag);
  trans2:= GL(d, q)!Matrix(GF(q), d, d,
               [<1, 1, 1>, <d, d, 1>, <d-1, 1, 1>, <d-1, 2, 1>, <d, 1,
               1>, <d, 2, -1>] cat [<i, i, -1>: i in [2..d-1]]);
 
  if normaliser then
    diag2:= NormSpMinusSp(d,q);
    return sub<GL(d, q)|diag1, diag2, symp1, symp2, trans1, trans2>;
  end if;
  return sub<GL(d, q)|diag1, symp1, symp2, trans1, trans2>;
end function;
 

/*
 * Here we stabilise <e_1, \ldots, e_k>, k \leq d/2;
 */

//require 2 gens for GL(k, q).
//require 2 gens for Sp(d - 2k, q)
//require 2 transvecs.

function IsotropicStabSp(d, q, k : normaliser:=false)
  assert IsEven(d) and d gt 2 and k gt 1; //use PointStabSp for k=1
  assert k lt (d/2 + 1);

  z:= PrimitiveElement(GF(q));
  half:= d div 2;
  form:= GL(k, q)!Matrix(GF(q), k, k, [<i, k-i+1, 1> : i in [1..k]]);
  diag:= [<i,i,1>: i in [1..d]];

 
  if k lt half then
    //GL(k, q) on <e_1..e_k>, balanced on <f_k..f_1>.
    gl1:= DiagonalJoin(<GL(k, q).1, IdentityMatrix(GF(q), d-2*k), 
                      form*Transpose(GL(k,q).-1)*form>);
    gl2:= DiagonalJoin(<GL(k, q).2, IdentityMatrix(GF(q), d-2*k), 
                      form*Transpose(GL(k,q).-2)*form>); 
    //the symplectic group acting on a (d-2k) space.
    sp1:= DiagonalJoin(<IdentityMatrix(GF(q), k), Sp(d-2*k, q).1,
                        IdentityMatrix(GF(q), k)>);
    sp2:= DiagonalJoin(<IdentityMatrix(GF(q), k), Sp(d-2*k, q).2,
                        IdentityMatrix(GF(q), k)>);
  
  else  // k = half.
    gl1:= DiagonalJoin(<GL(k, q).1, form*Transpose(GL(k, q).-1)*form>);
    gl2:= DiagonalJoin(<GL(k, q).2, form*Transpose(GL(k, q).-2)*form>); 

  end if;

  trans1:= GL(d, q)!Matrix(GF(q), d, d, [<d, 1, 1>] cat diag);
  if k lt half then
     trans2:= GL(d, q)!Matrix(GF(q), d, d, 
               [<d, d-k, 1>, <k+1, 1, -1>] cat diag);   
  end if;

  if k lt half then
    if normaliser then
      diag2:= NormSpMinusSp(d,q);
      return sub<GL(d, q)|gl1, gl2, sp1, sp2, trans1, trans2, diag2>;
    end if;
    return sub<GL(d, q)|gl1, gl2, sp1, sp2, trans1, trans2>;
  else
    if normaliser then
      diag2:= NormSpMinusSp(d,q);
      return sub<GL(d, q)|gl1, gl2, trans1, diag2>;
    end if;
    return sub<GL(d, q)|gl1, gl2, trans1>;
  end if;

end function;

/*
 * Here we need to make a direct product of Sp(k, q) and Sp(d-k, q),
 * but have to be careful to preserve the correct form.
 * We assume d is at least 6 or this type of group is nonmaximal.
 */

function SymplecticStab(d, q, k : normaliser:=false)
  assert IsEven(k) and k lt d div 2;
  assert d gt 4;
  half:= k div 2;

  mat1:= DiagonalJoin(<IdentityMatrix(GF(q), half), Sp(d-k, q).1,
                       IdentityMatrix(GF(q), half)>);
  mat2:= DiagonalJoin(<IdentityMatrix(GF(q), half), Sp(d-k, q).2,
                       IdentityMatrix(GF(q), half)>);

  gen:= [];

  for i in [1, 2] do
    j:= (i-1)*4;
    gen[1+j]:= Submatrix(Sp(k, q).i, 1, 1, half, half);
    gen[2+j]:= Submatrix(Sp(k, q).i, 1, half+1, half, half);
    gen[3+j]:= Submatrix(Sp(k, q).i, half+1, 1, half, half);
    gen[4+j]:= Submatrix(Sp(k, q).i, half+1, half+1, half, half);
  end for;

  finalmat:= [];

  for i in [0, 1] do
    finalmat[i+1]:= SquareBlockMatrix(<
    gen[1+4*i], ZeroMatrix(q, half, d-k), gen[2+4*i], 
    ZeroMatrix(q, d-k, half), IdentityMatrix(GF(q), d-k),
    ZeroMatrix(q, d-k, half), gen[3+4*i],
    ZeroMatrix(q, half, d-k), gen[4+4*i]>, q); 
  end for;

  if normaliser then
    diag2:= NormSpMinusSp(d,q);
    return sub<GL(d, q)|mat1, mat2, finalmat[1], finalmat[2],diag2>;
  end if;
  return sub<GL(d, q)|mat1, mat2, finalmat[1], finalmat[2]>;
end function;


function ReduciblesSp(d, q: All:=true)
  assert d gt 2 and IsEven(d);
  if d eq 4 and q mod 2 eq 0 and not All then
    return [PointStabSp(d, q)];
  end if;
  list:= [];
  Append(~list, PointStabSp(d, q));
  half:= d div 2;
  for i in [2..half] do 
    Append(~list, IsotropicStabSp(d, q, i));
  end for;
  for i in [2..half-1] do
    if IsEven(i) then
      Append(~list, SymplecticStab(d, q, i));
    end if;
  end for;
  return list;
end function;
