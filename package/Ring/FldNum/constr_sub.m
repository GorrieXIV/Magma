freeze;
//

intrinsic InternalSubfieldOptimize(a::RngOrdElt, E::RngOrd) -> RngOrdElt, RngOrd
  {}
  /* This is a 2 step approach:
   * 1st compute a module in M * Q containing k
   * 2nd intersect modules
   */

  M := Parent(a);   
  K := FieldOfFractions(M);
  n := Degree(E);
  b := [K|1, a];
  for i in [2..n-1] do
    b[i+1] := b[i]*a;
  end for;

  if CoefficientRing(M) eq Integers() then
    // absolute extensions
    dd := Lcm([Denominator(x) : x in b]);
    d := Discriminant(E)*dd;
    // at this stage we should have that 1/d(Module spanned by b) contains the
    // maximal order
    M1 := RSpace(Integers(), Degree(M));
    M2 := sub<M1 | [d*M1.i : i in [1..Dimension(M1)]]>;
    M3 := RSpaceWithBasis([M1!Eltseq(x*dd) : x in b]);
    M4 := M2 meet M3;
    O := Order(E, Matrix([Coordinates(M3, M4.i) : i in [1..Dimension(M4)]]),
           Integers()!d:Check := false);
    f, m := HasAttribute(M, "Maximal");
    if f and m then
      SetOrderMaximal(O, true);
    end if;
    _, O := OptimizedRepresentation(O);
    assert Type(DefiningPolynomial(E)) eq RngUPolElt;
    O := EquationOrder(O);
    b := FieldOfFractions(E)!O.2;
    b := Polynomial(Eltseq(b));
    b := Parent(a)!Evaluate(b, a);
    return b, O;
  else
    // relatives...
  end if;
end intrinsic; 

