freeze;

intrinsic Components(A::FldAb) -> .
{The cyclic components of F as orders};
  _ := EquationOrder(A);
  return [i`ClassField : i in A`Components];
end intrinsic;


