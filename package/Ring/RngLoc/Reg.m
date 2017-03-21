freeze;
//


function MyLog(x)
  yy := x;
  assert not IsWeaklyZero(x);
  x := FieldOfFractions(Parent(x))!x;
  if Valuation(x) ne 0 then
    x *:= UniformizingElement(Parent(x))^-Valuation(x);
  end if;
  assert Valuation(x) eq 0;
  if Valuation(x-1) gt 0 then
    return Parent(yy)!Log(x);
  end if;
  e := 1;
  p := #ResidueClassField(Integers(Parent(x)));

  e := p-1;
  x := x^(p-1);
  while Valuation(x-1) eq 0 do
    x := x^p;
    e *:= p;
  end while;
  return Parent(yy)!Log(x)/e;
end function;

intrinsic Logs(a::[FldAlgElt], R::RngPad: Completions := false) -> .
  {Computes the p-adic logarithms of the elements in a in the completions above R.}

  if Completions cmpeq false then
    O := Universe(a);
    F := SplittingField(DefiningPolynomial(O), R);
    if IsSimple(O) then
      f := Polynomial(F, DefiningPolynomial(O));
      lf := Roots(f);
      em := [hom<NumberField(O) -> F | i[1]> : i in lf];
    else
      lf := [Roots(Polynomial(F, g)) : g in DefiningPolynomial(O)];
      em := [hom<NumberField(O) -> F | [j[1] : j in i]> : i in CartesianProduct(lf)];
    end if;

  else
    em := Completions;
  end if;

  M := Matrix([ [MyLog(m(b)) : m in em] : b in a]);
  return M, em;
end intrinsic;

intrinsic pAdicRegulator(O::RngOrd, R::RngPad) -> RngPadElt
  {After Panayi, chapter 6: Computes (a/the) p-adic regulator}

  U, mU, base := SUnitGroup([PowerIdeal(O)|]:Raw);

  F := FieldOfFractions(R);
  f := Polynomial(F, DefiningPolynomial(O));

  lf, _, C := Factorisation(f:Extensions := true);
  em := [*hom<NumberField(O) -> C[i]`Extension | Degree(lf[i][1]) eq 1 select 
    -ConstantCoefficient(lf[i][1]) else C[i]`Extension.1> : i in [1..#C] *];
 

  /* Note that the p-adic Log is only defined for units and there
   * is no reason that elements in base are units. However since we
   * want only power products over base that are units, we can 
   * change elements in base by a uniformizer - it will cancel at the end.
   * The scaling is done in MyLog....
   */
     
  M := [* Matrix([[MyLog(m(b))] : b in Eltseq(base)]) : m in em*];

  r := Ngens(U)-1;
  lU := [* [ (Matrix(CoefficientRing(m), mU(U.i))*m)[1][1] : i in [2..Ngens(U)]] : m in M *];

  /* lU should have the logs of the units. Now we need pairwise products..
   */
  U := [* [x*y : x,y in Eltseq(z)] : z in lU *];

  z := [ Vector([ Trace(x) : x in y ]) : y in U];
  z := &+ z;
  z := Matrix(R, r, r, Eltseq(z));
  return Sqrt(F!Determinant(z)/Degree(O));

end intrinsic;


/*

x := Polynomial([0,1]);
O := MaximalOrder(x^5-2);

R := pAdicRing(17, 100);
pAdicRegulator(O, R);


*/
