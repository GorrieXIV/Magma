freeze;

////////////////////////////////////////////////////////////////////////
//                       Specific Curves                              //
////////////////////////////////////////////////////////////////////////

/*
intrinsic KleinQuartic(K::Fld) -> Crv
   {The Klein quartic over K.}
   P2 := ProjectiveSpace(K,2);
   x := P2.1; y := P2.2; z := P2.3; 
   return Curve(P2, x^3*y + y^3*z + x*z^3);
end intrinsic;
*/

intrinsic KleinQuartic(P2::Prj) -> Crv
   {The Klein Quartic in the projective plane P2.}
   require IsProjective(P2) and Rank(CoordinateRing(P2)) eq 3:
      "Ambient space must be a projective plane";
   x := P2.1; y := P2.2; z := P2.3; 
   return Curve(P2, x^3*y + y^3*z + x*z^3);
end intrinsic;

intrinsic HermitianCurve(P2::Prj[FldFin]) -> Crv
   {Given an projective plane P2 over a finite field of q^2
   elements, return the Hermitian curve x^(q+1)+y^(q+1)+z^(q+1).}

   require IsProjective(P2) and Rank(CoordinateRing(P2)) eq 3:
      "Ambient space must be a projective plane";
   K := BaseRing(P2);
   q2 := #K;
   q := Floor(Sqrt(q2));
   require q^2 eq q2 :
      "Size of the base field of the ambient space must be a square.";
   x := P2.1; y := P2.2; z := P2.3; 
   return Curve(P2,x^(q+1)+y^(q+1)+z^(q+1));
end intrinsic;
