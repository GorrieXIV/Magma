freeze;

import "finite.m": MatrixHasFiniteOrder;

intrinsic HasFiniteOrder (g:: GrpMatElt[RngInt]: UseCongruence := false) -> BoolElt
{ return true if invertible matrix over the integers has finite order, else false;
  if UseCongruence, then use congruence homomorphism to decide}

   return MatrixHasFiniteOrder(g: Magma := UseCongruence eq false);
end intrinsic;

intrinsic HasFiniteOrder (g:: GrpMatElt[FldRat]: UseCongruence := false) -> BoolElt
{ return true if invertible matrix over the rationals has finite order, else false;
  if UseCongruence, then use congruence homomorphism to decide}

   return MatrixHasFiniteOrder(g: Magma := UseCongruence eq false);

end intrinsic;

intrinsic HasFiniteOrder (g:: GrpMatElt[FldNum]: UseCongruence := false) -> BoolElt
{ return true if invertible matrix over function field has finite order, else false;
  if UseCongruence, then use congruence homomorphism to decide}

   return MatrixHasFiniteOrder(g: Magma := UseCongruence eq false);

end intrinsic;

intrinsic HasFiniteOrder (g:: GrpMatElt[FldFun]) -> BoolElt
{ return true if invertible matrix over  algebraic function field has finite order, else false}
   return MatrixHasFiniteOrder(g);
end intrinsic;

intrinsic HasFiniteOrder (g:: GrpMatElt[FldFunRat]) -> BoolElt
{ return true if invertible matrix over  rational function field has finite order, else false}

   return MatrixHasFiniteOrder(g);

end intrinsic;

intrinsic Order (G:: GrpMat[FldRat] : Verify := false, UseCongruence := false) -> RngIntElt 
{ return order of G;  if Verify then verify that G is finite;
  if UseCongruence then use congruence machinery to compute order}

   if IsTrivial (G) then G`Order := 1; return 1; end if;
   if assigned G`Order then return G`Order; end if;
   if UseCongruence eq true then
      flag, H := IsomorphicCopy (G: Verify := Verify);
      H`Order := LMGOrder (H); 
      G`Order := H`Order;
      return G`Order;
   else 
      return InternalOrder (G);
   end if;
end intrinsic;

intrinsic Order (G:: GrpMat[FldFun] : Verify := false) -> RngIntElt 
{ return order of G; if Verify then verify that G is finite}

   if IsTrivial (G) then G`Order := 1; return 1; end if;
   if assigned G`Order then return G`Order; end if;
   flag, H := IsomorphicCopy (G: Verify := Verify);
   H`Order := LMGOrder (H); 
   G`Order := H`Order;
   return G`Order;
end intrinsic;

intrinsic Order (G:: GrpMat[FldFunRat] : Verify := false) -> RngIntElt 
{ return order of G; if Verify then verify that G is finite}

   if IsTrivial (G) then G`Order := 1; return 1; end if;
   if assigned G`Order then return G`Order; end if;
   flag, H := IsomorphicCopy (G: Verify := Verify);
   H`Order := LMGOrder (H); 
   G`Order := H`Order;
   return G`Order;
end intrinsic;

intrinsic Order (G:: GrpMat[FldNum] : Verify := false, UseCongruence := false) -> RngIntElt 
{ return order of G;  if Verify then verify that G is finite; 
 if UseCongruence then use congruence machinery to compute order}

   if IsTrivial (G) then G`Order := 1; return 1; end if;
   if assigned G`Order then return G`Order; end if;

   if UseCongruence or AbsoluteDegree(BaseRing(G)) * Degree(G) gt 100 then
      flag, H := IsomorphicCopy (G: Verify := Verify);
      H`Order := LMGOrder (H); 
      G`Order := H`Order;
      return G`Order;
   else 
      return InternalOrder (G);
   end if;
end intrinsic;

intrinsic Order (G:: GrpMat[RngInt] : Verify := false, UseCongruence := false) -> RngIntElt 
{ return order of G;  if Verify then verify that G is finite; 
  if UseCongruence then use congruence machinery to compute order}

   if IsTrivial (G) then G`Order := 1; return 1; end if;
   if assigned G`Order then return G`Order; end if;
   if UseCongruence eq true then 
      flag, H := IsomorphicCopy (G: Verify := Verify);
      H`Order := LMGOrder (H); 
      G`Order := H`Order;
      return G`Order;
   else 
      return InternalOrder (G);
   end if;
end intrinsic;
