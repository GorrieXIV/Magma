freeze;

/***************************************************************************** 
   hexaeder.m

   Constructs a cubic surface in P^3 which has a Galois invariant double six. 
   The inital data is a polynomial. 
   Its roots are the hexahedral coefficients of the surface.

   Stephan Elsenhans, March 2011
******************************************************************************/

/* This routine computes the trace of arg in the quotient ring mod modul */
my_trace := function(arg, modul)
 local erg, i, r;

 r := Parent(modul);
 erg := 0;
 for i := 0 to Degree(modul) - 1 do
  erg := erg + MonomialCoefficient((arg * r.1^i) mod modul,r.1^i);
 end for;
 return(erg);
end function;


intrinsic CubicSurfaceByHexahedralCoefficients(pol :: RngUPolElt) -> RngMPolElt
{Given a separable polynomial of degree 6, this computes a cubic surface 
 whose hexahedral coefficients are the roots of the given polynomial.
 (These surfaces automatically have a Galois-invariant double-six)}

 require (Degree(pol) eq 6): "Polynomial must have degree 6.";
 
 require IsSquarefree(pol): "Polynomial must be squarefree.";

/* We have to solve the linear system 
        Tr(x) = 0
   Tr(tt * x) = 0 modulo pol.  */

 r := Parent(pol);
 m := Matrix(2,6,[ [my_trace(r.1^i, pol) : i in [0..5]],
                   [my_trace(r.1^(i+1),pol) : i in [0..5]] ]);  
 ker := KernelMatrix(Transpose(m));
 coeff := [ r!0, r!0, r!0, r!0 ];
 for i := 1 to 4 do
  for j := 1 to 6 do
   coeff[i] := coeff[i] + ker[i][j]*r.1^(j-1);
 end for; end for;

 r4 := PolynomialRing(BaseRing(Parent(pol)),4);
 erg := 0; 
 for i := 1 to 4 do
  for j := 1 to 4 do
   for k := 1 to 4 do
    erg := erg + my_trace((coeff[i]*coeff[j]*coeff[k]) mod pol, pol) * r4.i * r4.j * r4.k; 
 end for; end for; end for;
 return(erg);
end intrinsic;

intrinsic CoblesRadicand(pol :: RngUPolElt) -> FldElt
{Evaluates Cobles quartic polynomial. Up to a square this gives the discriminant of the 
 corresponding hexahedral cubic surface. All 27 lines of the cubic surface are defined 
 over the quadratic extension of the splitting field of pol by this radicand.}

 require Degree(pol) eq 6: "Polynomial must have degree 6.";
 
 co := Coefficients(pol);
 
 return(co[5]^2 - 4*co[3] + co[6]*( 2*co[4] - (3/2)*co[6]*co[5]+ (5/16)*co[6]^3  ));
end intrinsic; 

