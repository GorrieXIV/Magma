freeze;

//////////////////////////////////////////////////////////////////////////////
  
intrinsic ZetaFunction(F::FldFunG) -> FldFunRatUElt
{
   The Zeta function of the global function field F (with respect to the exact constant field)
};
   require IsGlobal(F) : 
     "Argument 1 must be a global function field";
   
   q := #ConstantField(F)^DegreeOfExactConstantField(F);
   L := LPolynomial(F);
   t := Parent(L).1;
   return L / ((1 - t)*(1 - q*t));  
   
end intrinsic;

  
//////////////////////////////////////////////////////////////////////////////
  
intrinsic ZetaFunction(F::FldFunG, m::RngIntElt) -> FldFunRatUElt
{
   The Zeta function of the constant field extension of degree m of the 
   global function field F (with respect to the exact constant field) 
};

   require IsGlobal(F) : 
     "Argument 1 must be a global function field";
   require 1 le m : 
     "Argument 2 must be >= 1";
  
   qm := #ConstantField(F)^(m * DegreeOfExactConstantField(F));
   L := LPolynomial(F, m);
   t := Parent(L).1;
   return L / ((1 - t)*(1 - qm*t));  
   
end intrinsic;

