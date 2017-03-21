freeze;

import "ClassicalSylow.m" : sigma;
import "SylowConjClassical.m" : IrredEltConj;

Dim2ConjGL := function(P,S)
// Finds a conjugating element for a Sylow 2 subgroup in dimension 2 for GL - P^g = S

  q := #BaseRing(P);
// First conjugate the subgroup of index 2
  if q mod 4 eq 1 then
// P and S are imprimitive - conjugate them so they fix the same block system
    assert not IsPrimitive(P);
    assert not IsPrimitive(S);
    BlocksP := Blocks(P);
    BlocksS := Blocks(S);
    matP := GL(2,q)!&cat[Eltseq(Blocks(P)[i].1) : i in [1..2] ];
    matS := GL(2,q)!&cat[Eltseq(Blocks(S)[i].1) : i in [1..2] ];
    g1 := matP^-1*matS;
    // Find elts of P^g1 and S that act nontrivially on the blocks
    flag := exists(xP){x : x in Generators(P) | not IsId(ImprimitiveAction(P,x))};
    xP := xP^g1;
    flag := exists(xS){x : x in Generators(S) | not IsId(ImprimitiveAction(S,x))};
  else
// P has order 4(q+1)_2, has an irreducible cyclic subgroup of order 2(q+1)_2
// Also P is semilinear and KP := WriteOverLargerField(P) is the irreducible cyclic subgroup
    assert IsSemiLinear(P);
    assert IsSemiLinear(S);
    KP := WriteOverLargerField(P);
    KS := WriteOverLargerField(S);
    _,x := IsCyclic(KP);
    _,y := IsCyclic(KS);
//  Use Kantor trick to find element in KP that is similar to y
    if IsSimilar(x,y) then
      x2 := x;
    else
      m := MinimalPolynomial(x);
      E := ext <GF(q) | m>;
      mm := MinimalPolynomial(y);
      flag,root := HasRoot(mm,E);
      e := Eltseq(root);
      x2 := ZeroMatrix(GF(q),2,2);
      temp := IdentityMatrix(GF(q),2);
      for i in [1..#e] do
        x2 := x2 + e[i]*temp;
        temp := temp * x;
      end for;
      x2 := Generic(P)!x2;
    end if;
    _,g1 := IsSimilar(y,x2);
    g1 := GL(2,q)!g1;
    // Find an elt of P outside of KP
    flag := exists(xP){t : t in Generators(P) | not IsOne((t,x))};
    xP := xP^g1;
    flag := exists(xS){t : t in Generators(S) | not IsOne((t,y))};
  end if;
//  Use the dihedral trick modulo the normal subgroup
  o := Order(xP*xS); 
  o := o div 2^Valuation(o,2);
  k := (o-1) div 2;
  g2 := (xS*xP)^k;
  return g1*g2;
end function;



Dim2ConjSp := function(P,S)
// Finds a conjugating element for a Sylow 2 subgroup in dimension 2 for Sp = SL - P^g = S



  q := #BaseRing(P);
// First conjugate the subgroup of index 2
  if q mod 4 eq 1 then
// P and S are imprimitive - conjugate them so they fix the same block system
    assert not IsPrimitive(P);
    assert not IsPrimitive(S);
    BlocksP := Blocks(P);
    BlocksS := Blocks(S);
    matP := GL(2,q)!&cat[Eltseq(Blocks(P)[i].1) : i in [1..2] ];
    matS := GL(2,q)!&cat[Eltseq(Blocks(S)[i].1) : i in [1..2] ];
    det := Determinant(matP^-1*matS);
// Use a matrix of the form Diag(det^-1,1) to get into SL
    dmat := GL(2,q)!DiagonalMatrix([det^-1,1]);
    g1 := matP^-1*dmat*matS;
    // Find elts of P^g1 and S that act nontrivially on the blocks
    flag := exists(xP){x : x in Generators(P) | not IsId(ImprimitiveAction(P,x))};
    xP := xP^g1;
    flag := exists(xS){x : x in Generators(S) | not IsId(ImprimitiveAction(S,x))};
  else
// P has order 4(q+1)_2, has an irreducible cyclic subgroup of order 2(q+1)_2
// Also P is semilinear and KP := WriteOverLargerField(P) is the irreducible cyclic subgroup
    assert IsSemiLinear(P);
    assert IsSemiLinear(S);
    KP := WriteOverLargerField(P);
    KS := WriteOverLargerField(S);
    _,x := IsCyclic(KP);
    _,y := IsCyclic(KS);
//  Use Kantor trick to find element in KP that is similar to y
    if IsSimilar(x,y) then
      x2 := x;
    else
      m := MinimalPolynomial(x);
      E := ext <GF(q) | m>;
      mm := MinimalPolynomial(y);
      flag,root := HasRoot(mm,E);
      e := Eltseq(root);
      x2 := ZeroMatrix(GF(q),2,2);
      temp := IdentityMatrix(GF(q),2);
      for i in [1..#e] do
        x2 := x2 + e[i]*temp;
        temp := temp * x;
      end for;
      x2 := Generic(P)!x2;
    end if;
    _,g1 := IrredEltConj(x2,y,"symplectic",GL(2,q)![0,1,-1,0]);
    g1 := GL(2,q)!g1;
    // Find an elt of P outside of KP
    flag := exists(xP){t : t in Generators(P) | not IsOne((t,x))};
    xP := xP^g1;
    flag := exists(xS){t : t in Generators(S) | not IsOne((t,y))};
  end if;
//  Use the dihedral trick modulo the normal subgroup
  o := Order(xP*xS); 
  o := o div 2^Valuation(o,2);
  k := (o-1) div 2;
  g2 := (xS*xP)^k;
  return g1*g2;
end function;

Dim2ConjGOPlus := function(P,S)
// Finds a conjugating element for a Sylow 2 subgroup in dimension 2 for GO+ - P^g = S

  if forall{x : x in Generators(P) | Determinant(x) eq 1} then 
// Are in SO+ which is cyclic!
    return Generic(P)!1;   
  end if;
  q := #BaseRing(P);
// First conjugate the subgroup of index 2
  if q mod 4 eq 1 then
// G is dihedral and imprimitive
// P and S already share a common index 2 subgroup

    o := 2^Valuation(q-1,2);
    repeat
      k := Random(P);
    until Order(k) eq o;
    
    // Find an elt of P and S outside of common subgroup
    
    flag := exists(xP){t : t in Generators(P) |  not IsOne((t,k))};
    flag := exists(xS){t : t in Generators(S) | not IsOne((t,k))};
    g1 := GL(2,q)!1;

  else
// P has order 4
// Find a non scalar element
    flag := exists(xP){x : x in Generators(P) | not IsScalar(x)};
    if not flag then
// G is SO+ of Omega+
      return GL(2,q)!1;
    end if;
    _ := exists(xS){x : x in Generators(S) | not IsScalar(x)};
    g1 := GL(2,q)!1;
  end if;
//  Use the dihedral trick modulo the normal subgroup
  o := Order(xP*xS); 
  o := o div 2^Valuation(o,2);
  k := (o-1) div 2;
  g2 := (xS*xP)^k;
  return g1*g2;
end function;

Dim2ConjGOMinus := function(P,S)
// Finds a conjugating element for a Sylow 2 subgroup in dimension 2 for GO- - P^g = S

 if forall{x : x in Generators(P) | Determinant(x) eq 1} then 
// Are in SO- which is cyclic!
    return Generic(P)!1;   
  end if;


  q := #BaseRing(P);
// First conjugate the subgroup of index 2
  if q mod 4 eq 1 then
// P has order 4
// Find a non scalar element
      flag := exists(xP){x : x in Generators(P) | not IsScalar(x)};
      if not flag then return GL(2,q)!1; end if;
      _ := exists(xS){x : x in Generators(S) | not IsScalar(x)};
      g1 := GL(2,q)!1;
    
  else

// G is dihedral and semilinear
// P and S already share a common index 2 subgroup of order (q+1)_2
    o := 2^Valuation(q+1,2);
    repeat
      k := Random(P);
    until Order(k) eq o;
  
    // Find an elt of P and S outside of common subgroup
    
    flag := exists(xP){t : t in Generators(P) |  not IsOne((t,k))};
    flag := exists(xS){t : t in Generators(S) | not IsOne((t,k))};
    g1 := GL(2,q)!1;
  end if;
//  Use the dihedral trick modulo the normal subgroup
  o := Order(xP*xS); 
  o := o div 2^Valuation(o,2);
  k := (o-1) div 2;
  g2 := (xS*xP)^k;
  return g1*g2;
end function;



Dim2ConjGU := function(G,P,S)
// Finds a conjugating element for a Sylow 2 subgroup in dimension 2 for GU - P^g = S

  q := #BaseRing(P);
  _,p := IsSquare(q);
  _,J := UnitaryForm(G);

  assert IsOverSmallerField(G : Scalars := true);
  cp := (p-1) div 2^Valuation(p-1,2);
  Pims := [SmallerFieldImage(G,P.i)^cp : i in [1..Ngens(P)] ];
  Sims := [SmallerFieldImage(G,S.i)^cp : i in [1..Ngens(S)] ];
  P1 := sub<GL(2,p) | Pims>;
  S1 := sub<GL(2,p) | Sims>;

  cob := SmallerFieldBasis(G);
  g1 := Dim2ConjGL(P1,S1);
  g1 := (GL(2,q)!g1)^(cob^-1);
  z := (g1*J*Transpose(sigma(g1))*J^-1)[1][1];
  _,z1 := NormEquation(GF(q),GF(p)!(z^-1));
  g1 := GL(2,q)!ScalarMatrix(2,z1)*g1;

  return g1;
end function;

Dim2ConjSU := function(P,S,J)
// Finds a conjugating element for a Sylow 2 subgroup in dimension 2 for GU - P^g = S

  q := #BaseRing(P);
  _,p := IsSquare(q);

  G := sub<GL(2,q) | P,S>;  

  assert IsOverSmallerField(G : Scalars := false);
  cob := SmallerFieldBasis(G);
  cp := (p-1) div 2^Valuation(p-1,2);
  Pims := [GL(2,p)!(SmallerFieldImage(G,P.i)^cp) : i in [1..Ngens(P)] ];
  Sims := [GL(2,p)!(SmallerFieldImage(G,S.i)^cp) : i in [1..Ngens(S)] ];
// make into SL
  for i in [1..#Pims] do
    _,z := IsSquare(Determinant(Pims[i])^-1);
    Pims[i] := GL(2,p)!(ScalarMatrix(2,z))*Pims[i];
  end for;
  for i in [1..#Sims] do
    _,z := IsSquare(Determinant(Sims[i])^-1);
    Sims[i] := GL(2,p)!(ScalarMatrix(2,z))*Sims[i];
  end for;
  
  P1 := sub<GL(2,p) | Pims>;
  S1 := sub<GL(2,p) | Sims>;

  g1 := Dim2ConjSp(P1,S1);
  g1 := (GL(2,q)!g1)^(cob^-1);
  z := (g1*J*Transpose(sigma(g1))*J^-1)[1][1];
  _,z1 := NormEquation(GF(q),GF(p)!(z^-1));
  g1 := GL(2,q)!ScalarMatrix(2,z1)*g1;
  assert Determinant(g1) eq 1;

  return g1;
end function;
