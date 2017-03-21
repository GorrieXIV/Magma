freeze;

/*
 * There is always a group which acts as GL on a maximal totally
 * isotropic subspace, and then is balanced on the other one.
 *
 * This code requires d > 4 as Sp(2, q) is a special case.
 *
 */

import "classicals.m": NormSpMinusSp;
 
function GetStabOfHalf(d, q : normaliser:=false )
  assert IsEven(d);
  //assert not q eq 2;
  f:= d div 2;
  assert f gt 2;
  z:= PrimitiveElement(GF(q));

  mat1:= GL(d, q)!DiagonalMatrix([z] cat [1 : i in [2..d-1]] cat [z^-1]);
  mat2:= GL(d, q)!Matrix(GF(q), d, d,
         [<1, 1, -1>, <1, f, 1>] cat [<i, i-1, -1> : i in [2..f]] cat
         [<d-1, f+1, -1>, <d, f+1, 1>] cat [<i, i+1, -1> : i in
         [f+1..d-1]]);
  swapmat:= GL(d, q)!Matrix(GF(q), d, d,
         [<i, f+i, 1> : i in [1..f]] cat [<i, i-f, -1> : i in
         [f+1..d]]);

  if normaliser then
    return sub<GL(d, q)|mat1, mat2, swapmat, NormSpMinusSp(d,q) >;
  end if;
  return sub<GL(d, q)|mat1, mat2, swapmat>;
end function;


/* 
 * The other function is a wreath product of Sp(d/n, q) and S_n. There
 * seem to be two ways to go here: the easy way is to make the wreath
 * product and conjugate it, as then conjugate it:
 * making wreath: O(d^2). gives 4 gens.
 * conjugating: O(d^3). So O(d^3). But then O(d) groups gives
 * O(d^4)...
 *
 * assumes d gt 4, and that if n eq 2 then q is not 2.
 */

function GetWreathProd(d, q, n : normaliser:=false )
  assert d gt 4;
  //if n gt 2 then assert q gt 2; end if; why? orthogonal?

  s:= d div n;
  f:= d div 2;
  assert IsEven(s);
  
  g:= WreathProduct(Sp(s, q), Sym(n));
  //g:Magma;
  bool, form:= SymplecticForm(g);
  if normaliser then
    elt := DiagonalJoin([NormSpMinusSp(s,q) : i in [1..n]]);
    g := sub< GL(d,q) | g, elt >;
  end if;
  mat:= CorrectForm(form, d, q, "symplectic");   
  return g^mat;
end function;

/*
 * The following function ties it all together.
 * Take GL on maximal isotropic for odd q.
 * Take wreath product of Sp(d/n, Sym(n)) where q > 2 unless n eq 2.
 */

function GetSympImprimsD4(q : normaliser:=false)
    z:= PrimitiveElement(GF(q));

    g:= WreathProduct(Sp(2, q), Sym(2));
    bool, form:= SymplecticForm(g);
    if normaliser then
      elt := DiagonalJoin([NormSpMinusSp(2,q) : i in [1..2]]);
      g := sub< GL(4,q) | g, elt >;
    end if;
    x:= GL(4, q)!CorrectForm(form, 4, q, "symplectic");
    imprim1:= g^x;

    if IsEven(q) then return imprim1; end if;

    newmat1:= GL(4, q)!DiagonalMatrix([z, 1, 1, z^-1]);
    newmat2:= GL(4, q)![-1, 1, 0, 0,
                    -1, 0, 0, 0,
                     0, 0, -1, -1,
                     0, 0, 1, 0];
    newmat3:= GL(4, q)![0, 0, -1, 0,
                        0, 0, 0, -1,
                        1, 0, 0, 0,
                        0, 1, 0, 0];
    imprim2:= normaliser select
              sub<GL(4, q)|newmat1, newmat2, newmat3,NormSpMinusSp(4,q)>
        else  sub<GL(4, q)|newmat1, newmat2, newmat3>;

    return imprim1, imprim2;
end function;


function GetSympImprims(d, q)
 
  assert d gt 4;
  divs:= [x : x in Divisors(d) | x gt 1 and IsEven(d div x)];

  groups:= [];

  for n in divs do
/*
    if q eq 2 and d div n eq 2 then //otherwise orthogonal (KL)
       continue;
    end if;
*/
    Append(~groups, GetWreathProd(d, q, n));
  end for;

//  if IsOdd(q) then //Colva and KL have this - o.w. group is orthogonal
    Append(~groups, GetStabOfHalf(d, q));
//  end if;

  return groups;
end function;
