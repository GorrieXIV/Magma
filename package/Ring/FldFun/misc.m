freeze;

//////////////////////////////////////////////////////////////////////////////

intrinsic Numerator(a::FldFunElt, O::RngFunOrd) -> RngFunOrdElt
{
   The numerator of a with respect to the order O.
};

   require FunctionField(O) eq Parent(a) :
     "Arguments are defined for different function fields";

   b, _ := IntegralSplit(a, O);
   return b;

end intrinsic;


//////////////////////////////////////////////////////////////////////////////

intrinsic Denominator(a::FldFunElt, O::RngFunOrd) -> RngElt
{
   The denominator of a with respect to the order O.
};

   require FunctionField(O) eq Parent(a) :
     "Arguments are defined for different function fields";

   _, b := IntegralSplit(a, O);
   return b;

end intrinsic;


//////////////////////////////////////////////////////////////////////////////

intrinsic Zeros(F::FldFun, a::FldFunGElt) -> SeqEnum
{The zeros of a in F};
    require IsCoercible(F, a) : "Argument 2 must lie in argument 1";
    return Zeros(F!a);
end intrinsic;

intrinsic Poles(F::FldFun, a::FldFunGElt) -> SeqEnum
{The poles of a in F};
    require IsCoercible(F, a) : "Argument 2 must lie in argument 1";
    return Poles(F!a);
end intrinsic;

intrinsic CommonZeros(F::FldFunG, L::[FldFunGElt]) -> SeqEnum
{Return the common zeros of the elements of the sequence L};
    c, L := CanChangeUniverse(L, F);
    require c : "Function field must be the universe of the sequence";
    return CommonZeros(L);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////

intrinsic Relations(L::[FldFunElt], R::Rng) -> ModTupRng
{
  The module of R-linear relations between the elements of L
};

  return Relations(L, R, 0);

end intrinsic;

intrinsic Relations(L::[FldFunRatUElt], R::Rng) -> ModTupRng
{
  The module of R-linear relations between the elements of L
};

  return Relations(L, R, 0);

end intrinsic;

intrinsic Relations(L::[DiffFunElt], R::Rng) -> ModTupRng
{
  The module of R-linear relations between the elements of L
};

  return Relations(L, R, 0);

end intrinsic;

//////////////////////////////////////////////////////////////////////////////

intrinsic Support(P::PlcFunElt) -> [], []
{The support of the divisor 1*P}
  return [P], [1];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////

intrinsic PoleDivisor(D::DivFunElt) -> DivFunElt
  {The Pole divisor of D}
  return -GCD(D, 0*D);
end intrinsic;

intrinsic ZeroDivisor(D::DivFunElt) -> DivFunElt
  {The Zero divisor of D}
  return -GCD(-D, 0*D);
end intrinsic;

intrinsic Norm(D::DivFunElt) -> DivFunElt
  {The norm of the divisor D}

    if Type(BaseField(FunctionField(D))) eq FldFunRat then
      return ZeroDivisor(Divisor(Norm(I))) + ZeroDivisor(Divisor(Norm(J)))
        where I, J := Ideals(D);
    else
      return Divisor(Norm(I)) + Divisor(Norm(J)) where I, J is Ideals(D);
    end if;
end intrinsic;

intrinsic Norm(P::PlcFunElt) -> DivFunElt
  {The norm of the place P}

    if Type(BaseField(FunctionField(P))) eq FldFunRat then
      if IsFinite(P) then
        return ZeroDivisor(Divisor(Norm(Ideal(P))));
      else
        return ZeroDivisor(Divisor(Norm(Ideal(P))));
      end if;
    else
      return Divisor(Norm(I)) where I is Ideal(P);
    end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////

intrinsic RiemannRochSpace(P::PlcFunElt) -> ModFld, Map
{The Riemann-Roch space of the divisor 1*P}

    return RiemannRochSpace(1*P);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////

intrinsic FieldMorphism(f::Map) -> Map
{ Converts a map between fields into a field morphism }
    return ImportExternalMorphism(FieldCategory())(f,false);
end intrinsic;

intrinsic RandomPlace(K::FldFunG, d::RngIntElt) -> PlcFunElt
  {}
  require IsGlobal(K) : "Algebraic function field is required to be global";
  f, P := HasRandomPlace(K, d);
  require f: "The function field does not have places of degree", d;

  return P;
end intrinsic;

intrinsic Completion(F::FldFun[FldFun], P::PlcFunElt : Precision := 20) -> RngSerLaur, Map
{The completion of F or O at the place P with infinite precision whose default precision is determined by the parameter Precision.}
    RER := RationalExtensionRepresentation(F);
    C, m := Completion(RER, Places(RER)!P : Precision := Precision);
    return C, Coercion(F, RER)*m;
end intrinsic;

intrinsic Completion(O::RngFunOrd[RngFunOrd], P::PlcFunElt : Precision := 20) -> RngSerLaur, Map
{"} // "
    A := AbsoluteOrder(O);
    C, m := Completion(A, Places(FunctionField(A))!P : Precision := Precision);
    return C, Coercion(O, A)*m;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////

intrinsic '*'(M::PMat, A::RngFunOrdIdl) -> PMat
  {}
  C := CoefficientIdeals(M);
  return PseudoMatrix([x*A : x in C], Matrix(M));
end intrinsic;

intrinsic '*'(A::RngFunOrdIdl, M::PMat) -> PMat
  {}
  C := CoefficientIdeals(M);
  return PseudoMatrix([x*A : x in C], Matrix(M));
end intrinsic;


