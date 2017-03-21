freeze;

//we stabilise <(1, 0, 0, 0)> and <(1, 0, 0, 0), (0, 1, 0, 0)>. This is
//essentially unique, as must stabilise point and isotropic 2-space, 
//and since stabilising <(1, 0, 0, 0)> also does stuff to <(0, 0, 0, 1)>
//we might as well have point inside 2-space. 

import "imp_and_gamma.m": GammaL1;

NoveltyReduct:= function(q : normaliser:=false)
  assert IsEven(q);

  z:= PrimitiveElement(GF(q));
  d:= [<i,i,1>: i in [1..4]];

  diag1:= DiagonalMatrix([z, 1, 1, z^-1]);
  diag2:= DiagonalMatrix([1, z, z^-1, 1]);

  trans1:= Matrix(GF(q), 4, 4, [<4, 1, 1>] cat d);
  trans2:= Matrix(GF(q), 4, 4, d cat [<2, 1, 1>, <4, 3, 1>]);
  trans3:= Matrix(GF(q), 4, 4, d cat [<3, 1, 1>, <4, 2, 1>]);
  trans4:= Matrix(GF(q), 4, 4, d cat [<3, 2, 1>]);
  scal := ScalarMatrix(4,z);

  g:= normaliser select
     sub<GL(4, q)|diag1, diag2, trans1, trans2, trans3, trans4, scal>
     else sub<GL(4, q)|diag1, diag2, trans1, trans2, trans3, trans4>;

  return g;
end function;

/****************************************************************/

NoveltySemilin:= function(q : normaliser:=false)
  assert IsEven(q);

  gammal1:= GammaL1(4, q);
  singer:= gammal1.1;
  frob:= gammal1.2;

  grp:= sub<GL(4, q)|singer^(q^2-1), frob>;

  bool, form:= SymplecticForm(grp);
  assert bool;

  if normaliser then
    z:=PrimitiveElement(GF(q)); scal:=ScalarMatrix(4,z);
    grp := sub<GL(4, q)| grp, scal >;
  end if;

  mat:= CorrectForm(form, 4, q, "symplectic");
  return grp^mat;

end function;

/****************************************************************/

NoveltyImprims:= function(q : normaliser:=false)
  assert IsEven(q);

  grp1:= WreathProduct(SOPlus(2, q), Sym(2));
  if q eq 2 then form :=Matrix(GF(2),4,4,[0,1,0,0,1,0,0,0,0,0,0,1,0,0,1,0]);
  else bool, form:= SymplecticForm(grp1);
    assert bool;
  end if;
  mat1:= CorrectForm(form, 4, q, "symplectic");

  grp2:= WreathProduct(SOMinus(2, q), Sym(2));
  bool, form:= SymplecticForm(grp2);
  assert bool;
  mat2:= CorrectForm(form, 4, q, "symplectic");

  if normaliser then
    z:=PrimitiveElement(GF(q)); scal:=ScalarMatrix(4,z);
    grp1 := sub<GL(4, q)| grp1, scal >;
    grp2 := sub<GL(4, q)| grp2, scal >;
  end if;

  return grp1^mat1, grp2^mat2;
end function;
