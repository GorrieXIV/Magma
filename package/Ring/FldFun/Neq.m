freeze;


intrinsic NormEquation(F::FldFun, a::FldFunGElt) -> BoolElt, []
  {Tries to solve N(x) = a in the global function field F}

  require IsGlobal(F) : "Function field is not global";
  C, mC := ClassGroup(F);
  S := Support(Divisor(F!a));
  d := 0;
  lp := [];
  i := 1;
  U := sub<C|[x @@ mC : x in S]>;
  while U ne C do
    if i gt #lp then
      d +:= 1;
      lp := Places(F, d);
      i := 1;
    end if;
    c := lp[i]@@mC;
    if not c in U then
      U := sub<C|U, c>;
      Include(~S, lp[i]);
    end if;
    i+:= 1;
  end while;
  T := {};
  for s in S do
    if IsFinite(s) then
      m := Minimum(Ideal(s));
      assert IsPrime(m);
      T join:= {Place(x) : x in Decomposition(Order(Ideal(s)), m)};
    else
      T join:= {x : x in InfinitePlaces(F)};
    end if;
  end for;

  SF, mSF := SUnitGroup(T);
  N := hom<SF -> SF | [(F!Norm(SF.i @ mSF))@@mSF : i in [1..Ngens(SF)]]>;
  r := (F!a)@@mSF;
  if r in Image(N) then
    return true, [(r@@N)@mSF];
  else
    return false, _;
  end if;
end intrinsic;
