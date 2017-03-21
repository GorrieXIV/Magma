freeze;

/////////////////////////////////////////////////////////////////////////
// smooth.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 38140 $
// $Date: 2012-04-13 00:18:58 +1000 (Fri, 13 Apr 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Calculates the Ehrhart data for a smooth polytope.
// See: G.Hegedus and A.M.Kasprzyk, "Roots of Ehrhart polynomials of
// smooth Fano polytopes", 	arXiv:1004.3817v1 [math.CO].
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns the value t choose r, where t is an indeterminate of a polynomial
// ring.
function smooth_binomial_contribution(t,r)
    rfac:=Factorial(r);
    return &+[(StirlingFirst(r,i) / rfac) * t^i : i in [0..r]];
end function;

// Calculates the Ehrhart polynomial for a smooth polytope P.
function calculate_smooth_ehrhart_polynomial(P)
    // Collect the data we need
    f:=fVector(P);
    R:=PolynomialRing(Rationals());
    t:=R.1;
    // Create the Ehrhart polynomial
    L:=&+[f[i+1] * smooth_binomial_contribution(t,i) : i in [0..Dimension(P)]];
    // Assign it to P and return it
    P`Ehrhart_qpoly:=[R | L];
    return L;
end function;

// Assignes the data needed to compute the Ehrhart generating function when P
// is a smooth polytope. Returns the rational generating function.
function calculate_smooth_ehrhart_data(P)
    // First we create the Ehrhart polynomial
    L:=calculate_smooth_ehrhart_polynomial(P);
    // Now we calculate the coefficients we'll need
    if not assigned P`Ehrhart_coeffs then
        P`Ehrhart_coeffs:=[Integers()|];
    end if;
    k:=Dimension(P) + 1;
    for i in [1..k - 1] do
        if not IsDefined(P`Ehrhart_coeffs,i) then
            P`Ehrhart_coeffs[i]:=Evaluate(L,i);
        end if;
    end for;
    // Create the rational generating function
    E:=[1] cat P`Ehrhart_coeffs;
    t:=Parent(L).1;
    f:=&+[E[i] * t^(i - 1) : i in [1..k]] * (1 - t)^k;
    coeffs:=[Integers() | Coefficient(f,i) : i in [0..k - 1]];
    P`Ehrhart_gen_func:=&+[coeffs[i] * t^(i - 1) : i in [1..k]] / (1 - t)^k;
    // Return it
    return P`Ehrhart_gen_func;
end function;
