freeze;

////////////////////////////////////////////////////////////////////////////
  
intrinsic IsWeierstrassPlace(D::DivFunElt, P::PlcFunElt) -> BoolElt
{
  Whether the degree one place P is a Weierstrass place of D.
};

  F := FunctionField(D);

  require FunctionField(P) eq F :
    "Arguments are defined over different function fields";
  require Degree(P) eq 1 :
    "Place must have degree 1";

  return GapNumbers(D, P) ne GapNumbers(D);

end intrinsic;

////////////////////////////////////////////////////////////////////////////
  
intrinsic IsWeierstrassPlace(F::FldFunG, P::PlcFunElt) -> BoolElt
{
  Whether the degree one place P is a Weierstrass place of F.
};

  require FunctionField(P) eq F :
    "Arguments are defined over different function fields";
  require Degree(P) eq 1 :
    "Place must have degree 1";

  return GapNumbers(F, P) ne GapNumbers(F);

end intrinsic;

////////////////////////////////////////////////////////////////////////////
  
intrinsic GapNumbers(P::PlcFunElt) -> BoolElt
{
  The sequence of gap numbers of the function field of P at P where P must be
  a place of degree one
};
   
   require Degree(P) eq 1 :
     "Place must have degree 1";
   
   return GapNumbers(FunctionField(P), P);
   
end intrinsic;

////////////////////////////////////////////////////////////////////////////
  
intrinsic IsWeierstrassPlace(P::PlcFunElt) -> BoolElt
{
  Whether the degree one place P is a Weierstrass place of its function
  field.
};
   
   require Degree(P) eq 1 :
     "Place must have degree 1";
   
   return IsWeierstrassPlace(FunctionField(P), P);
   
end intrinsic;

