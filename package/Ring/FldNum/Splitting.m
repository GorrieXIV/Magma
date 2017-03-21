freeze;

intrinsic SplittingField(f::RngUPolElt:Opt := false, Abs := true) -> FldNum, []
  {A splitting field for the polynomial f.}
  require Type(CoefficientRing(f)) in {FldRat, RngInt} 
	or ISA(Type(CoefficientRing(f)), FldAlg) 
	or ISA(Type(CoefficientRing(f)), RngOrd) : "Polynomial must be over the rationals or a number field";

  K, ev := SplittingField([f]:Abs := Abs, Opt := Opt);
  return K, ev[1];
end intrinsic;

intrinsic SplittingField(S::{RngUPolElt}:Opt := false, Abs := true) -> FldNum
  {Computes a splitting field for all polynomials in S.}
  require Universe(S) in {FldRat, RngInt} or ISA(Universe(S), FldAlg) or ISA(Universe(S), RngOrd) : "Polynomial must be over the rationals or a number field";
  a := SplittingField([Universe(S)|x : x in S]:Opt := Opt, Abs := Abs);
  return a;
end intrinsic;

intrinsic SplittingField(L::[RngUPolElt]:Opt := false, Abs := true) -> FldNum, []
  {Computes a splitting field for all polynomials in L.}
  P := Universe(L);
  K := CoefficientRing(P);

  if K cmpeq Integers() or ISA(Type(K), RngOrd) then
    K := FieldOfFractions(K);
  end if;

  if #L eq 0 then
    return K, [K|];
  end if;

  require K cmpeq Rationals() or ISA(Type(K), FldAlg) :
    "Polynomial must be  over the rationals or a number field.";

  roots := [* *];
  lroots := [];
  LL := SetToSequence(Set(L));
  LL_start := LL;
  r := 1;
  repeat
    if LL[1] in LL_start then
      if (LL[1] ne LL_start[1]) then
        Append(~roots, lroots);
        lroots := [];
      end if;
    end if;
    lf := Factorisation(Polynomial(K, LL[1]));
    Remove(~LL, 1);
    no_lin := 0;
    for i in lf do
      if Degree(i[1]) eq 1 then
        Append(~lroots, -Eltseq(i[1])[1]);
        no_lin +:= 1;
      else
        LL := [i[1]] cat LL;
      end if;
    end for;
    if no_lin eq #lf then
      continue;
    end if;
    K := NumberField(LL[1] : Check := false);
    AssignNames(~K, [ "r." cat IntegerToString(r)]);
    r +:= 1;
    ChangeUniverse(~lroots, K);
    ChangeUniverse(~LL, PolynomialRing(K));
    LL[1] := LL[1] div Polynomial(K, [-K.1, 1]);
    Append(~lroots, K.1);
  until #LL eq 0;
  Append(~roots, lroots);

  rt := [ Parent([K| ]) | ];
  for i in [1..#L] do
    p := Position(LL_start, L[i]);
    Append(~rt, roots[p]);
  end for;
  roots := rt;
  if Abs then
    if K ne Rationals() then 
      K := AbsoluteField(K);
      if Opt then
        K := OptimizedRepresentation(K);
      end if;
    end if;
    r := [];
    for i in [1..#roots] do
      s := [];
      for j in [1..#roots[i]] do
        Append(~s, K!roots[i][j]);
      end for;
      Append(~r, s);
    end for;
    roots := r;
  end if;
  return K, roots;
end intrinsic;  

