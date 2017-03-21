freeze;

procedure KLPolynomial_SaveResultFP( ~Saved, x, y, Result )
	b, a := IsDefined(Saved, x);
	if not b then
		assert Type(Parent(Result)) eq RngUPol;
		Saved[x] := AssociativeArray(Parent(y));
	end if;
	Saved[x][y] := Result;
end procedure;

function KLPolynomial_HasResultFP( Saved, x, y )
	b, a := IsDefined(Saved, x);
	if not b then 
		return false, _;
	end if;
	b, r := IsDefined(a, y);
	if not b then 
		return false, _;
	end if;
	return true, r;
end function;

procedure computeKLPolynomialFP(W, x, y, PR, ~Saved, ~Result, depth, count_todo)
	vprintf KLPoly : "depth: %3o, todo: %10o\n", depth, count_todo;

	known, r := KLPolynomial_HasResultFP(Saved, x, y);
	if known then Result := r; return; end if;

	assert Type(x) eq GrpFPCoxElt;
	assert Type(y) eq GrpFPCoxElt;
	assert Parent(x) eq W;
	assert Parent(y) eq W;

	X := PR.1;
	lx := CoxeterLength(x);
	ly := CoxeterLength(y);

	/* Base cases */
	if ((not(BruhatLessOrEqual(W, x, y)))) then 
		Result := PR!0;
		KLPolynomial_SaveResultFP(~Saved, x, y, Result);
		return; 
	end if;

	if (x eq y) then 
		Result := PR!1; 
		KLPolynomial_SaveResultFP(~Saved, x, y, Result);
		return; 
	end if;

	/* Check */
	assert lx lt ly;

	/* Find candidates for recursion */
	n := Rank(W);
	cands := [ i : i in [1..n] | CoxeterLength(y*(W.i)) lt ly ];
	error if (#cands eq 0), "No simple reflection r found st l(y*r) < l(y).";

	/* See if we can immediately recurse to a smaller case */
	lensxr := [ CoxeterLength(x*(W.r)) : r in cands ];
	for i in [1..#cands] do
		if (lx lt lensxr[i]) then
			r := cands[i];
			computeKLPolynomialFP(W, x*(W.r), y, PR, ~Saved, ~Result, depth+1, count_todo+1);
			KLPolynomial_SaveResultFP(~Saved, x, y, Result);
			return;
		end if;
	end for;
	for i in [1..#cands] do
		r := cands[i];
		xr := x*(W.r); yr := y*(W.r);
		if (lensxr[i] lt lx) and not(BruhatLessOrEqual(W, x, yr)) and not(BruhatLessOrEqual(W, yr, x)) then
			computeKLPolynomialFP(W, xr, yr, PR, ~Saved, ~Result, depth+1, count_todo+1);
			KLPolynomial_SaveResultFP(~Saved, x, y, Result);
			return;
		end if;
	end for;

	/* try to optimize the choice of r */
	r := false;
	for rcand in cands do
		if KLPolynomial_HasResultFP(Saved, x*W.rcand, y*W.rcand) then
			r := rcand;
			break;
		end if;
	end for;
	if (Type(r) eq BoolElt) then
		for rcand in cands do
			if KLPolynomial_HasResultFP(Saved, x, y*W.rcand) then
				r := rcand;
				break;
			end if;
		end for;
	end if;	  
	if (Type(r) eq BoolElt) then 
		r := Representative(cands);
	end if;

	/* Recurse. */
	assert Type(r) eq RngIntElt;
	r := W.r;
	yr := y*r; xr := x*r;

	/* construct _ALL_ intermediate values */
	bhd := [ z : z in InternalBruhatAllBetween(x, yr) | BruhatLessOrEqual(W, z*r, z) ];
	
	tms := [PR|];
	for i in [1..#bhd] do
		z := bhd[i];
		exp1 := (1/2)*(CoxeterLength(y*r) - CoxeterLength(z) - 1);
		exp2 := (1/2)*(CoxeterLength(y) - CoxeterLength(z));

		assert exp1 ge 0;

		if (exp1 ge 0 and IsIntegral(exp1)) then
			assert IsIntegral(exp2) or (exp2 lt 0);

			Pzy := PR!0; computeKLPolynomialFP(W, z, yr, PR, ~Saved, ~Pzy, depth+1, count_todo+#bhd-i+2);
			mu := Coefficient(Pzy, Integers()!exp1);

			if (mu ne 0) then
				Pxz := PR!0; computeKLPolynomialFP(W, x, z, PR, ~Saved, ~Pxz, depth+1, count_todo+#bhd-i+2);
				Append(~tms, mu*(X^(Integers()!exp2))*Pxz);
			end if;
		end if;
	end for;

	/* The two remaining, boring terms */
	t1 := PR!0; computeKLPolynomialFP(W, xr, yr, PR, ~Saved, ~t1, depth+1, count_todo+2);
	t2 := PR!0; computeKLPolynomialFP(W, x, yr, PR, ~Saved, ~t2, depth+1, count_todo+1);

	/* Combine & return */
	Result := t1 + X*t2 - &+tms;
	KLPolynomial_SaveResultFP(~Saved, x,y, Result);
	return;
end procedure;


intrinsic KLPolynomial(x::GrpFPCoxElt, y::GrpFPCoxElt : Ring := false) -> RngUPolElt
{ The KL-polynomial P_xy. Result will be over the Polynomial ring Ring.
  Method: See du Cloux. }
	W := Parent(x);
	require Parent(y) eq W : "Arguments must be elements of the same Coxeter group.";
	assert Type(W) eq GrpFPCox;
	
	require Ring cmpeq false or Type(Ring) eq RngUPol : "Ring must be a univariate polynomial ring.";

	if (Ring cmpeq false) then 
		Ring := PolynomialRing(Integers()); X := Ring.1;
	end if;

	reslt := Ring!0;
	Saved := AssociativeArray(W);
	
	computeKLPolynomialFP(W, x, y, Ring, ~Saved, ~reslt, 0, 1);

	return reslt;
end intrinsic;

intrinsic KLPolynomial(x::GrpPermElt, y::GrpPermElt : Ring := false) -> RngUPolElt
{ The KL-polynomial P_xy (only applies to elements of a Coxeter group). 
  Result will be over the Polynomial ring Ring. Method: See du Cloux. }
	W := Parent(x);
	Wfp, phi := CoxeterGroup(GrpFPCox, W);
	return KLPolynomial(phi(x), phi(y) : Ring := Ring);
end intrinsic;

intrinsic KLPolynomial(x::GrpMatElt, y::GrpMatElt : Ring := false) -> RngUPolElt
{ The KL-polynomial P_xy (only applies to elements of a Coxeter group). 
  Result will be over the Polynomial ring Ring. Method: See du Cloux. }
	W := Parent(x);
	Wfp, phi := CoxeterGroup(GrpFPCox, W);
	return KLPolynomial(phi(x), phi(y) : Ring := Ring);
end intrinsic;

