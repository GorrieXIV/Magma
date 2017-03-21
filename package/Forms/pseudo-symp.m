freeze;
/**********************************************************************
  Pseudo-symplectic groups over finite fields of characteristic 2.
  
  A bilinear form (in characteristic 2) is pseudo-alternating if it is 
  symmetric but not alternating.  See Hirscheld or Wan Zhexian for the
  terminology and some properties.
 
  If J is the matrix of the form, then X preserves the form (acting on 
  the right) if X*J*Transpose(X) eq J.

  January 2012 Don Taylor

  $Id: pseudo-symp.m 39973 2012-09-12 12:55:34Z don $

  Intrinsics defined in this file:
    PseudoSymplecticGroup
*/

intrinsic PseudoSymplecticGroup(n::RngIntElt, F::FldFin) -> GrpMat
{ The pseudo-symplectic group PsSp(n,F), over the field F of characteristic 2}
  require n gt 0 : "dimension must be at least 1";
  require ISA( Type(F), FldFin ) : "the field must be finite";
  q := #F;
  _, p, e := IsPrimePower(q);
  require p eq 2 : "the field must have characteristic 2";
  if n eq 1 then
    gens := [];
  elif n eq 2 then
    xi := PrimitiveElement(F);
    gens := [Matrix(F,2,2,[1,0,xi^i,1]) : i in [0..e-1]];
    ord := Factorisation(q);
  else
    n0 := IsOdd(n) select n - 1 else n - 2;
    H := SymplecticGroup(n0,F);
    ord := FactoredOrder(H);
    I := IdentityMatrix(F,n-n0);
    gens := [DiagonalJoin(H.i,I) : i in [1..Ngens(H)]];
    if IsEven(n) then
      u := IdentityMatrix(F,n);
      u[n,1] := 1;
      u[n0,n0+1] := 1;
      Append(~gens,u);
      ord *:= Factorisation(q^(n-1));
    end if;
  end if;
  S := sub< GL(n,F) | gens >;
  if n gt 1 then
    S`Order := ord;
  end if;
  return S;
end intrinsic;


intrinsic PseudoSymplecticGroup(n::RngIntElt, q::RngIntElt) -> GrpMat
{ The pseudo-symplectic group PsSp(n,q), over the field GF(q) 
 of characteristic 2}
  require IsEven(q) and IsPrimePower(q) : "second argument must be a power of 2";
  return PseudoSymplecticGroup(n,GF(q));
end intrinsic;


