freeze;


/* some common binary opeartions for class fields...*/


function make_comparable(A, B)
  /* for FldAb's A and B try to define them using the same
   * (minimal) modulus.
   * returns
   * <m, m0> the common modulus
   * mR the RayClassGroup map for this modulus
   * UA and UB the subgroups (of Domain(mR))
   */

 
  function one_field(C)
    assert Type(C) eq FldAb;

    fl, G := HasAttribute(C, "DefiningGroup");
    assert fl;

    if assigned G`GrpMap then
      return <G`m0, G`m_inf>, G`RcgMap, Kernel(Inverse(G`GrpMap));
    else
      return <G`m0, G`m_inf>, G`RcgMap, sub<Domain(G`RcgMap)|>;
    end if;
  end function;

  mA, mRA, UA := one_field(A);
  mB, mRB, UB := one_field(B);
  R := PowerIdeal(CoefficientRing(A));

  mC := <LCM(mA[1], mB[1]), [x : x in Set(mA[2]) join Set(mB[2])]>;

  if mC eq mA then
    mRC := mRA;
    RC := Domain(mRC);
    assert Domain(mRA) eq RC;
    mCA := hom<RC -> Domain(mRA) | [ RC.i : i in [1..Ngens(RC)]]>;
  else
    RC, mRC := RayClassGroup(mC[1], mC[2]);
    mCA := InducedMap(mRC, mRA, map<R ->R | x:-> x>, Minimum(mC[1]));
  end if;

  mCB := InducedMap(mRC, mRB, map<R ->R | x:-> x>, Minimum(mC[1]));

  return mC, mRC, UA @@ mCA, UB @@ mCB;
end function;

intrinsic 'meet'(A::FldAb, B::FldAb) -> FldAb
  {The intersection of A and B.}
 
  require CoefficientRing(A) eq CoefficientRing(B):
    "Both fields must be defined over the same coefficient ring";
  mC, mRC, UA, UB := make_comparable(A, B);
  q, mq := quo<Domain(mRC) | UA, UB>;
  return AbelianExtension(Inverse(mq)*mRC);
end intrinsic;

intrinsic '*'(A::FldAb, B::FldAb) -> FldAb
  {The smallest field containing both arguments}
  require CoefficientRing(A) eq CoefficientRing(B):
    "Both fields must be defined over the same coefficient ring";

  mC, mRC, UA, UB := make_comparable(A, B);
  q, mq := quo<Domain(mRC) | UA meet UB>;
  return AbelianExtension(Inverse(mq)*mRC);
end intrinsic;

intrinsic 'subset'(A::FldAb, B::FldAb) -> BoolElt
  {Tests if A is contained in B}

  require CoefficientRing(A) eq CoefficientRing(B):
    "Both fields must be defined over the same coefficient ring";
  mC, mRC, UA, UB := make_comparable(A, B);

  return UB subset UA;
end intrinsic;

intrinsic 'eq'(A::FldAb, B::FldAb) -> BoolElt
  {Tests if A and B are the same field}

  require CoefficientRing(A) eq CoefficientRing(B):
    "Both fields must be defined over the same coefficient ring";
  mC, mRC, UA, UB := make_comparable(A, B);
  return UA eq UB;
end intrinsic;


    
