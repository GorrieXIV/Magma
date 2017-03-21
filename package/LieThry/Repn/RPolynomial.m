freeze;

function computeRPolynomialFP(W, PR, x, y) //->RngUPolElt
	X := PR.1;
	
	assert Type(W) eq GrpFPCox;

	if (not(BruhatLessOrEqual(W, x, y))) then
		return PR!0;
	end if;

	if (x eq y) then
		return PR!1;
	end if;

	lx := CoxeterLength(x);
	ly := CoxeterLength(y);
	
	n := Rank(W);
	i := 1;
	while (i le n) do
		if (CoxeterLength(y*(W.i)) lt ly) then
			break;
		end if;
		i +:= 1;
	end while;

	error if (i gt n), "No simple reflection r found st l(y*r) < l(y).";

	r := W.i; yr := y*r; xr := x*r;
	if (CoxeterLength(xr) lt lx) then
		return computeRPolynomialFP(W, PR, xr, yr);
	else
		return (X-1) * computeRPolynomialFP(W, PR, x, yr) + (X) * computeRPolynomialFP(W, PR, xr, yr);
	end if;

end function;


intrinsic RPolynomial( x::GrpFPCoxElt, y::GrpFPCoxElt : Ring := false) -> RngUPolElt
{ The R-polynomial R_xy. Result will be over the Polynomial ring Ring. }
    W := Parent(x);
    require Parent(y) eq W : "Arguments must be elements of the same Coxeter group.";    
    
	if (Ring cmpeq false) then
		Ring := PolynomialRing(Integers()); X := Ring.1;
	end if;

	return computeRPolynomialFP(W, Ring, x, y);
end intrinsic;


intrinsic RPolynomial( x::GrpPermElt, y::GrpPermElt : Ring := false) -> RngUPolElt
{ The R-polynomial R_xy (only applies to elements of a Coxeter group).
  Result will be over the Polynomial ring Ring. }
    W := Parent(x);
    require Parent(y) eq W : "Arguments must be elements of the same Coxeter group.";    

	Wfp, phi := CoxeterGroup(GrpFPCox, W);
	return RPolynomial(phi(x), phi(y) : Ring := Ring);
end intrinsic;

intrinsic RPolynomial( x::GrpMatElt, y::GrpMatElt : Ring := false) -> RngUPolElt
{ The R-polynomial R_xy (only applies to elements of a Coxeter group).
  Result will be over the Polynomial ring Ring. }
    W := Parent(x);
    require Parent(y) eq W : "Arguments must be elements of the same Coxeter group.";    

	Wfp, phi := CoxeterGroup(GrpFPCox, W);
	return RPolynomial(phi(x), phi(y) : Ring := Ring);
end intrinsic;
