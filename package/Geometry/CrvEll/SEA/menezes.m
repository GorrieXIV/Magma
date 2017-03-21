freeze;

/*

    menezes.m

    Contains code for finding a factor of the l'th division polynomial
    when l is a power of 2.

    RR July 1998
*/


function Menezes(E, c)
// E::CrvEll,		// Our curve of interest
// c::RngIntElt		// l = 2^c
// ) ->
// RngUPolElt		// The factor of the division polynomial
//
// {Computes a factor of the 2^c'th division polynomial.}
//
    // Check curve is in the right form

    assert c ge 1;
    FF := BaseRing(E);
    assert (Characteristic(FF) eq 2);
    P := PolynomialRing(FF);
    x := P.1;
    a6 := aInvariants(E)[5];
    g_list := [ P | ];

    g := x;
    if c eq 1 then return g; end if;

    b := Root(a6, 4);
    g := b + x;
    if c eq 2 then return g; end if;

    g_im1 := g;
    b := Sqrt(b);
    g := g^2 + b*x;
    if c eq 3 then return g; end if;
    g_product := P!1;

    for i in [4..c] do
	b := Sqrt(b);
	g_product *:= g_im1^2;
	g_im1 := g;
	g := g^2 + b*x*g_product;
    end for;

    return g;
end function;
