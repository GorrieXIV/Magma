freeze;

import "spinor.m":InOmega;
import "gl2.m": ModToQ, GL2, GU2;
import "classicals.m": NormSpMinusSp;

OrthogSL2 := function(d,q:special:=false,general:=false,normaliser:=false)
/* construct SL(2,q) in O(d,q) for d odd */
  local w, S, G, M, T, MM, A;
  assert IsOdd(d); assert IsOdd(q);
  /* construct GL(2,q) as SL(2,q) with extra generator */
  w := PrimitiveElement(GF(q));
  G := sub< GL(2,q) | SL(2,q), DiagonalMatrix(GF(q),[w,1]) >;
  M := GModule(G);
  MM := M;
  for i in [3..d] do
    T:=TensorProduct(M,MM);
    MM := [c : c in Constituents(T) | Dimension(c) eq i ][1];
  end for;
  A := ActionGroup(MM);
  S := ScalarMatrix(d, w^((d-1) div 2) );
  A := sub< GL(d,q) | A.1, A.2, A.3*S^-1 >;
  assert Determinant(A.3) eq GF(q)!1;
  assert SymmetricBilinearForm(A);
  A := A^TransformForm(A);
  if normaliser then
    return sub< GL(d,q) | A.1, A.2, A.3, ScalarMatrix(d,w) >;
  elif general then
    return sub< GL(d,q) | A.1, A.2, A.3, ScalarMatrix(d,-1) >;
  elif special or InOmega(A.3,d,q,0)  then
    //InOmega(A.3,d,q,0) seems to happen for d = 1 or 7 mod 8.
    return A;
  else return sub < GL(d,q) | A.1, A.2 >;
  end if;
end function;

SymplecticSL2 := function(d,q:normaliser:=false)
/* construct SL(2,q) in Sp(d,q) for d even */
  local w, S, G, M, T, MM, A, DA, isit, form, tmat;
  assert IsEven(d); assert IsOdd(q);
  /* construct GL(2,q) as SL(2,q) with extra generator */
  w := PrimitiveElement(GF(q));
  G := sub< GL(2,q) | SL(2,q), DiagonalMatrix(GF(q),[w,1]) >;
  M := GModule(G);
  MM := M;
  for i in [3..d] do
    T:=TensorProduct(M,MM);
    MM := [c : c in Constituents(T) | Dimension(c) eq i ][1];
  end for;
  A := ActionGroup(MM);
  S := ScalarMatrix(d, w^((d-2) div 2) );
  A := sub< GL(d,q) | A.1, A.2, A.3*S^-1 >;
  DA := sub< A | A.1, A.2 >;
  isit, form := SymplecticForm(DA); assert isit;
  tmat := TransformForm(form, "symplectic");
  A := A^tmat;
  if normaliser then return A;
  else return  sub< A | A.1, A.2 >;
  end if;
end function;

l3qdim6 := function(q:general:=false)
  local w, S, G, M, T, MM, A;
  assert IsOdd(q);
  w := PrimitiveElement(GF(q));
  G := general select GL(3,q) else SL(3,q);
  M := GModule(G);
  T := TensorProduct(M,M);
  MM := [c : c in Constituents(T) | Dimension(c) eq 6 ][1];
  A := ActionGroup(MM);
  if not general then
    S := ScalarMatrix(6, w^((q-1) div GCD(6,q-1)) );
    return sub< GL(6,q) | A, S >;
  end if;
  return sub< GL(6,q) | A, ScalarMatrix(6,w) >;
end function;

u3qdim6 := function(q:general:=false, normaliser:=false)
  local w, S, G, M, T, MM, A;
  assert IsOdd(q);
  if normaliser then general:=true; end if;
  w := PrimitiveElement(GF(q^2));
  G := general select GU(3,q) else SU(3,q);
  M := GModule(G);
  T := TensorProduct(M,M);
  MM := [c : c in Constituents(T) | Dimension(c) eq 6 ][1];
  A := ActionGroup(MM);
  A := A^TransformForm(A);
  if not general then
    S := ScalarMatrix(6, (w^(q-1))^((q+1) div GCD(6,q+1)) );
    return sub< GL(6,q^2) | A, S >;
  end if;
  if not normaliser then
    return sub< GL(6,q^2) | A, ScalarMatrix(6,w^(q-1)) >;
  end if;
  return sub< GL(6,q^2) | A, ScalarMatrix(6,w) >;
end function;

l2q3dim8 := function(q:normaliser:=false)
  //SL(2,q^3).3 <= Sp(8,q);
  w:=PrimitiveElement(GF(q^3));
  G := sub< GL(2,q^3) | SL(2,q^3), DiagonalMatrix(GF(q^3),[w,1]) >;
  M:=GModule(G); M1:=ModToQ(M,q); M2:=ModToQ(M1,q); 
  T:=TensorProduct(M,TensorProduct(M1,M2)); 
  assert IsIrreducible(T);
  u := GL(8,q^3)!PermutationMatrix(GF(q^3),Sym(8)!(2,3,5)(4,7,6));
  //induces field automorphism
  X := sub< GL(8,q^3) | ActionGroup(T), u >;
  iso, G := IsOverSmallerField(X);
  assert iso;
  G := G^TransformForm(sub<G|G.1,G.2>);
  if normaliser then
    return G;
  end if;
  return( sub<G | G.1,G.2,G.4 >);
end function;

l3qdim8 := function(q:special:=false,general:=false,normaliser:=false)
  //SL(3,q)(.3) <= O+(8,q), q mod 3 = 1 or O-(8,q), q mod 3 = 2
  w := PrimitiveElement(GF(q));
  G := GL2(3,q);
  M := GModule(G);
  T := TensorProduct(M,M);
  C := Constituents(T);
  M8 := [c : c in C | Dimension(c) eq 8][1];
  G8 := ActionGroup(M8);
  G8 := G8^TransformForm(G8);
  if normaliser then
    return sub< GL(8,q) | G8, ScalarMatrix(8,w) >;
  elif general and IsOdd(q) then
    return sub< GL(8,q) | G8, ScalarMatrix(8,-1) >;
  elif (special or general) and IsEven(q) then
    return sub< GL(8,q) | G8 >;
  elif special or q mod 3 eq 1 then
    return sub< GL(8,q) | G8.1, G8.2, ScalarMatrix(8,-1) >;
  else
    return sub< GL(8,q) | G8.1, G8.2 >;
  end if;
end function;

u3qdim8 := function(q:special:=false,general:=false,normaliser:=false)
  //SU(3,q)(.3) <= O+(8,q), q mod 3 = 2 or O-(8,q), q mod 3 = 1
  w := PrimitiveElement(GF(q));
  G := GU2(3,q);
  M := GModule(G);
  T := TensorProduct(M,M);
  C := Constituents(T);
  M8 := [c : c in C | Dimension(c) eq 8][1];
  G8 := ActionGroup(M8);
  isit, G8q := IsOverSmallerField(G8); assert isit;
  G8q := G8q^TransformForm(G8q);
  if normaliser then
    return sub< GL(8,q) | G8q, ScalarMatrix(8,w) >;
  elif general and IsOdd(q) then
    return sub< GL(8,q) | G8q, ScalarMatrix(8,-1) >;
  elif (special or general) and IsEven(q) then
    return sub< GL(8,q) | G8q >;
  elif special or q mod 3 eq 2 then
    return sub< GL(8,q) | G8q.1, G8q.2, ScalarMatrix(8,-1) >;
  else
    return sub< GL(8,q) | G8q.1, G8q.2 >;
  end if;
end function;

l2q2dim9 := function(q:special:=false,general:=false,normaliser:=false)
  //L(2,q^2).2 <= O(9,q);
  w:=PrimitiveElement(GF(q^2)); z:=w^(q+1);
  G := sub< GL(2,q^2) | SL(2,q^2), DiagonalMatrix(GF(q^2),[w,1]) >;
  M:=GModule(G); M1:=ModToQ(M,q);
  T:=TensorProduct(M,M1); 
  assert IsIrreducible(T);
  u := GL(4,q^2)!PermutationMatrix(GF(q^2),Sym(4)!(2,3));
  //induces field automorphism
  X := sub< GL(4,q^2) | ActionGroup(T), u >;
  iso, G := IsOverSmallerField(X);
  assert iso;
  M:=GModule(G);
  T:=TensorProduct(M,M);
  C:= [c: c in Constituents(T) | Dimension(c) eq 9][1];
  G:= ActionGroup(C);
  G := G^TransformForm(sub<G|G.1,G.2>);
  //adjust G.3 to fix form and G.4 to have determinant 1
  isit, form := SymmetricBilinearForm(sub<G|G.1,G.2>); assert isit;
  tform := G.3 * form * Transpose(G.3);
  scal := form[1][9]/tform[1][9];
  isit, rt := IsPower(scal,2); assert isit;
  g3 := G.3 * ScalarMatrix(9, rt);
  g3 := Determinant(g3) eq 1 select g3 else -g3;
  g4 := Determinant(G.4) eq 1 select G.4 else -G.4;
  G := sub< GL(9,q) | G.1,G.2,g3,g4 >;
  if normaliser then
    return sub< GL(9,q) | G, ScalarMatrix(9,z) >;
  elif general then
    return sub< GL(9,q) | G, ScalarMatrix(9,-1) >;
  elif special then
    return G;
  else
    gg := InOmega(g3,9,q,0) select g3
     else InOmega(g4,9,q,0) select g4
     else g3*g4;
    return( sub<GL(9,q) | G.1,G.2 >);
  end if;
end function;

l3q2dim9l := function(q:general:=false)
  //(3.)L(3,q^2)(.3).2 <= L(9,q)
  w:=PrimitiveElement(GF(q^2)); z:=w^(q+1);
  G := sub< GL(3,q^2) | SL(3,q^2), DiagonalMatrix(GF(q^2),[w,1,1]) >;
  M:=GModule(G); M1:=ModToQ(M,q);
  T:=TensorProduct(M,M1); 
  assert IsIrreducible(T);
  u := GL(9,q^2)!PermutationMatrix(GF(q^2),Sym(9)!(2,4)(3,7)(6,8));
  //induces field automorphism
  X := sub< GL(9,q^2) | ActionGroup(T), u >;
  iso, G := IsOverSmallerField(X);
  assert iso;
  //adjust G.4 to have determinant 1
  g4 := Determinant(G.4) eq 1 select G.4 else -G.4;
  G := sub< GL(9,q) | G.1,G.2,G.3,g4 >;
  if general then
    return sub< GL(9,q) | G, ScalarMatrix(9,z) >;
  else
    //get power of G.3 with determinant 1
    return( sub<G | G.1, G.2, G.3^Order(Determinant(G.3)), G.4 >);
  end if;
end function;

l3q2dim9u := function(q:general:=false, normaliser:=false)
  //(3.)L(3,q^2)(.3).2 <= L(9,q)
  w:=PrimitiveElement(GF(q^2)); z:=w^(q-1);
  G := sub< GL(3,q^2) | SL(3,q^2), DiagonalMatrix(GF(q^2),[w,1,1]) >;
  M:=GModule(G); M1:=ModToQ(M,q);
  T:=TensorProduct(Dual(M),M1); 
  assert IsIrreducible(T);
  u := GL(9,q^2)!PermutationMatrix(GF(q^2),Sym(9)!(2,4)(3,7)(6,8));
  //induces field automorphism
  G := sub< GL(9,q^2) | ActionGroup(T), u >;
  G := G^TransformForm(sub<G|G.1,G.2>);
  //adjust G.4 to have determinant 1
  g4 := Determinant(G.4) eq 1 select G.4 else -G.4;
  G := sub< GL(9,q^2) | G.1,G.2,G.3,g4 >;
  if normaliser then
    return sub< GL(9,q^2) | G, ScalarMatrix(9,w) >;
  elif general then
    return sub< GL(9,q^2) | G, ScalarMatrix(9,z) >;
  //get power of G.3 with determinant 1
  else return( sub<G | G.1, G.2, G.3^Order(Determinant(G.3)), G.4 >);
  end if;
end function;

l3qdim10 := function(q:general:=false)
  local w, S, G, M, T, MM, A;
  assert Factorisation(q)[1][1] ge 5;
  w := PrimitiveElement(GF(q));
  G := sub < GL(3,q) | SL(3,q), DiagonalMatrix(GF(q),[w,1,1]) > ;
  M := GModule(G);
  T := TensorPower(M,3);
  MM := [c : c in Constituents(T) | Dimension(c) eq 10 ][1];
  G := ActionGroup(MM);
  if general then return sub< GL(10,q) | G, ScalarMatrix(10,w) >; end if;
  //get intersection with SL
  o := Order(Determinant(G.3));
  tp := 3^Valuation(o,3);
  g3 := G.3^(o div tp);
  isit, rt := IsPower(Determinant(g3),10); assert isit;
  g3 := g3 * ScalarMatrix(10,rt^-1);
  S := ScalarMatrix(10, w^((q-1) div GCD(10,q-1)) );
  return sub< GL(10,q) | G.1, G.2, g3, S >;
end function;

u3qdim10 := function(q:general:=false, normaliser:=false)
  local w, S, G, M, T, MM, A;
  assert Factorisation(q)[1][1] ge 5;
  if normaliser then general:=true; end if;
  w := PrimitiveElement(GF(q^2));
  G := sub < GL(3,q^2) | SU(3,q), GU(3,q).1 > ;
  M := GModule(G);
  T := TensorPower(M,3);
  MM := [c : c in Constituents(T) | Dimension(c) eq 10 ][1];
  A := ActionGroup(MM);
  G := A^TransformForm(A);
  if normaliser then return sub< GL(10,q^2) | G, ScalarMatrix(10,w) >; end if;
  if general then
       return sub< GL(10,q^2) | G, ScalarMatrix(10,w^(q-1)) >;
  end if;
  //get intersection with SU
  o := Order(Determinant(G.3));
  tp := 3^Valuation(o,3);
  g3 := G.3^(o div tp);
  isit, rt := IsPower(Determinant(g3),10*(q-1)); assert isit;
  g3 := g3 * ScalarMatrix(10,rt^-(q-1));
  S := ScalarMatrix(10, (w^(q-1))^((q+1) div GCD(10,q+1)) );
  return sub< GL(10,q^2) | G.1, G.2, g3, S >;
end function;

l4qdim10 := function(q:general:=false)
  local w, S, G, M, T, MM, A;
  assert Factorisation(q)[1][1] ge 3;
  w := PrimitiveElement(GF(q));
  G := sub < GL(4,q) | SL(4,q), DiagonalMatrix(GF(q),[w,1,1,1]) > ;
  M := GModule(G);
  T := TensorPower(M,2);
  MM := [c : c in Constituents(T) | Dimension(c) eq 10 ][1];
  G := ActionGroup(MM);
  if general then return sub< GL(10,q) | G, ScalarMatrix(10,w) >; end if;
  //get intersection with SL
  o := Order(Determinant(G.3));
  tp := 2^Valuation(o,2);
  g3 := G.3^(2*o div tp);
  isit, rt := IsPower(Determinant(g3),10); assert isit;
  g3 := g3 * ScalarMatrix(10,rt^-1);
  S := ScalarMatrix(10, w^((q-1) div GCD(10,q-1)) );
  return sub< GL(10,q) | G.1, G.2, g3, S >;
end function;

u4qdim10 := function(q:general:=false, normaliser:=false)
  local w, S, G, M, T, MM, A;
  assert Factorisation(q)[1][1] ge 3;
  if normaliser then general:=true; end if;
  w := PrimitiveElement(GF(q^2));
  G := sub < GL(4,q^2) | SU(4,q), GU(4,q).1 > ;
  M := GModule(G);
  T := TensorPower(M,2);
  MM := [c : c in Constituents(T) | Dimension(c) eq 10 ][1];
  A := ActionGroup(MM);
  G := A^TransformForm(A);
  if normaliser then return sub< GL(10,q^2) | G, ScalarMatrix(10,w) >; end if;
  if general then
       return sub< GL(10,q^2) | G, ScalarMatrix(10,w^(q-1)) >;
  end if;
  //get intersection with SU
  o := Order(Determinant(G.3));
  tp := 2^Valuation(o,2);
  g3 := G.3^(2*o div tp);
  isit, rt := IsPower(Determinant(g3),10*(q-1)); assert isit;
  g3 := g3 * ScalarMatrix(10,rt^-(q-1));
  S := ScalarMatrix(10, (w^(q-1))^((q+1) div GCD(10,q+1)) );
  return sub< GL(10,q^2) | G.1, G.2, g3, S >;
end function;

l5qdim10 := function(q:general:=false)
  local w, S, G, M, T, MM, A;
  w := PrimitiveElement(GF(q));
  G := general select GL(5,q) else SL(5,q);
  M := GModule(G);
  T := TensorProduct(M,M);
  MM := [c : c in Constituents(T) | Dimension(c) eq 10 ][1];
  A := ActionGroup(MM);
  if not general then
    S := ScalarMatrix(10, w^((q-1) div GCD(10,q-1)) );
    return sub< GL(10,q) | A, S >;
  end if;
  return sub< GL(10,q) | A, ScalarMatrix(10,w) >;
end function;

u5qdim10 := function(q:general:=false, normaliser:=false)
  local w, S, G, M, T, MM, A;
  if normaliser then general:=true; end if;
  w := PrimitiveElement(GF(q^2));
  G := general select GU(5,q) else SU(5,q);
  M := GModule(G);
  T := TensorProduct(M,M);
  MM := [c : c in Constituents(T) | Dimension(c) eq 10 ][1];
  A := ActionGroup(MM);
  A := A^TransformForm(A);
  if not general then
    S := ScalarMatrix(10, (w^(q-1))^((q+1) div GCD(10,q+1)) );
    return sub< GL(10,q^2) | A, S >;
  end if;
  if not normaliser then
    return sub< GL(10,q^2) | A, ScalarMatrix(10,w^(q-1)) >;
  end if;
  return sub< GL(10,q^2) | A, ScalarMatrix(10,w) >;
end function;

sp4qdim10 := function(q:special:=false,general:=false, normaliser:=false)
  //Sp4q <= O^+(10,q) (q=1 mod 4) or O^-(10,q) (q=3 mod 4)
  assert IsOdd(q);
  w := PrimitiveElement(GF(q));
  G := sub< GL(4,q) | Sp(4,q), NormSpMinusSp(4,q) >; 
  M := GModule(G);
  C:=Constituents(TensorProduct(M,M));
  M10 := [c: c in C|Dimension(c) eq 10][1];
  G := ActionGroup(M10);
  G := G^TransformForm(sub<G|G.1,G.2>);
  isit, form := SymmetricBilinearForm(sub<G|G.1,G.2>); assert isit;
  tform := G.3 * form * Transpose(G.3);
  scal := form[1][10]/tform[1][10];
  isit, rt := IsPower(scal,2); assert isit;
  g3 := G.3 * ScalarMatrix(10, rt);
  G := sub<GL(10,q) | G.1, G.2, g3 >;
  sign := q mod 4 eq 1 select 1 else -1;
  assert Determinant(g3) eq 1 and not InOmega(g3,10,q,sign);
  if normaliser then return sub< GL(10,q) | G, ScalarMatrix(10,w) >;
  elif special or general then return sub< GL(10,q) | G, ScalarMatrix(10,-1) >;
  else return sub< GL(10,q) | G.1,G.2,ScalarMatrix(10,-1)>;
  end if;
end function;
