
freeze;

declare type SSGalRep;
declare attributes SSGalRep: CoefficientRing, FixedField, Weights, PolList;

intrinsic CoefficientRing(V::SSGalRep) -> Rng
  {Return the coefficient ring of the representation}
  return V`CoefficientRing;
end intrinsic;

intrinsic FixedField(V::SSGalRep) -> Fld
  {Return the fixed field of the absolute Galois group of which V is a representation}
  return V`FixedField;
end intrinsic;

intrinsic Weights(V::SSGalRep) -> SeqEnum
  {Return the tame inertia weights of V}
  return V`Weights;
end intrinsic;

intrinsic Print(V::SSGalRep)
  {Print V}
  printf "Semisimple representation of the absolute Galois group of %o with coefficients in %o and components %o",
  V`FixedField, V`CoefficientRing, V`Weights ;
end intrinsic;

intrinsic SSGaloisRepresentation(CoefficientRing::Rng,FixedField::RngSerLaur,Weights::SeqEnum,PolList::SeqEnum) -> SSGalRep
  {Create a semisimple Galois representation}
  V:=New(SSGalRep);
  V`CoefficientRing:=CoefficientRing;
  V`FixedField:=FixedField;
  V`Weights:=Weights;
  V`PolList:=PolList;
  return V;
end intrinsic;

intrinsic SSGaloisRepresentation(D::PhiMod) -> SSGalRep
  {Compute the semisimple Galois representation attached to a phi-module}
  K:=CoefficientRing(D);
  k:=CoefficientRing(K);
  p:=Characteristic(k);
  s:=D`Frobenius[1];
  b:=D`Frobenius[2];
  if (s ne 0) and ((Degree(k) mod s) ne 0) then
    error "The fixed field of the Frobenius must be a subfield of the coefficient ring";
  end if;
  if (s ne 0) and (b ne p^s) then
    error "The given phi-module does not correspond to a representation";
  end if;
  H,Q,sl,dim:=SemisimpleDecomposition(D);
  return SSGaloisRepresentation(GF(p,s),K,sl,dim);
end intrinsic;
