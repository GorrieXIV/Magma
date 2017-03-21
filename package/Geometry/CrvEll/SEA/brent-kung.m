freeze;

// Machinery for doing Brent-Kung compositions.
// Main algorithms done by Allan Steel, June 1999.

declare verbose BrentKung, 1;

forward OptimalModularCompositionApply;

intrinsic ModularComposition(f::RngUPolElt,g::RngUPolElt,h::RngUPolElt)
    -> RngUPolElt 
    {Return f(g) mod h}

    if (f eq Parent(f).1) then
	return g; 
    elif (g eq Parent(g).1) then
	return f; 
    elif Degree(g) ge Degree(h)	then
	g := g mod h;
    end if;
    t := Isqrt(Degree(f));
    setup := ModularCompositionSetup(g,h,t);
    return ModularCompositionApply(f,setup,h,t);
end intrinsic;

intrinsic ModularComposition(
    f::RngUPolElt,h::RngUPolElt,r::RngIntElt) -> RngUPolElt 
    {Return the r-th iterate of composition of f with itself modulo h, 
    computed using the Brent-Kung machinery.  Assumes that f defines
    an endomorphism of the quotient by h, so that modular composition
    is well-defined.}

    if r eq 0 then return Parent(f).1; end if;
    if Degree(f) ge Degree(h) then f := f mod h; end if;
    setup := <h, [f], []>;
    f_r := Zero(Parent(f));
    OptimalModularCompositionApply(~setup, r, ~f_r);
    return f_r; 
end intrinsic;

function Optimal_BK_Steps(S, T)
    /*
    Given set S of initial integers, and set T of desired integers return
    sequences of composition steps to optimally construct the elements of
    T from S.
    */

    n := Max(T);
    nsteps := [];
    path := [];
    for i := 1 to n do
	nsteps[i] := -1;
	path[i] := [];
    end for;
    for x in S do
	nsteps[x] := 0;
	path[x] := [];
    end for;

    while T notsubset S do
	vprint BrentKung, 1: "Optimal steps loop";
        for s := 1 to n do
            for x in S do
                y := s - x;
                if y ge x and y in S then
                    ns := 1;
                    if x notin T then
                        ns +:= nsteps[x];
                    end if;
                    if y ne x and y notin T then
                        ns +:= nsteps[y];
                    end if;
                    if s notin S or ns lt nsteps[s] then
                        Include(~S, s);
                        nsteps[s] := ns;
                        if x notin T then
                            p := path[x];
                        else
                            p := [];
                        end if;
                        if y notin T and (y ne x or x in T) then
                            p cat:= path[y];
                        end if;
                        path[s] := p cat [<x, y>];
                    end if;
                end if;
            end for;
        end for;
    end while;
    return [<x, path[x]>: x in T];
end function;

function EqualSplittingDegree(f,x_pow,r_vals) 
    // Given the polynomial f in x over a finite field of q elements 
    // which splits into a product of irreducibles all of the same 
    // degree, the value of x^q mod f, and a sequence of candidates 
    // containing this degree, return the splitting degree.
    /*
    Given sequence r_vals of possible r values, return the first r from
    r_vals such that (x^q^r mod f) = x.  If the second last value of
    r is reached without satisfying the stopping condition, it is assumed
    that the correct value of r is the last value of r_vals.  x_pow
    must be (x^q mod f).
    */

    X := Parent(f).1;
    S := Exclude(r_vals, Max(r_vals));

    // bkt := Ceiling(2 * Sqrt(Degree(f)));
    bkt := Ceiling(1 * Sqrt(Degree(f)));

    // Compute optimal composition steps to go from x_pow to each x^q^i mod f
    steps := Optimal_BK_Steps({1}, S);
    if GetVerbose("BrentKung") gt 0 then
	print "Optimal Brent-Kung steps:";
	print steps;
    end if;

    poly := [x_pow];
    BKS := [];

    step := 1;
    for i in S do
	vprint BrentKung, 1: "Computing power:", i;
	IndentPush();
	// Set poly[i] to (x^q^i mod f).  poly[i] should not be set yet.
	// assert not IsDefined(poly, i);
        if IsDefined(poly, i) then
            print "Failed assertion, but continuing anyway...";
        end if;   
	t := steps[step];
	assert t[1] eq i;
	p := t[2];
	for c in p do
	    // Compose poly[x] with poly[y] to form poly[s]
	    x := c[1];
	    y := c[2];
	    s := x + y;
	    if not IsDefined(poly, s) then
		assert IsDefined(poly, x);
		assert IsDefined(poly, y);
		// Use setup for x if known; i.e., form poly[y](poly[x])
		if IsDefined(BKS, x) then
		    vprintf BrentKung, 1:
   		        "Compose f^(%o)(f^(%o)) -> f^(%o)\n", y, x, s;
		    vtime BrentKung, 1:
		    g := ModularCompositionApply(poly[y], BKS[x], f, bkt);
		// Use setup for y if known; i.e., form poly[x](poly[y])
		elif IsDefined(BKS, y) then
		    vprintf BrentKung, 1:
   		        "Compose f^(%o)(f^(%o)) -> f^(%o)\n", x, y, s;
		    vtime BrentKung, 1:
		    g := ModularCompositionApply(poly[x], BKS[y], f, bkt);
		else
		    // Set up for x and form poly[y](poly[x])
		    vprintf BrentKung, 1: "Brent-Kung setup %o\n", x;
		    vtime BrentKung, 1:
		    BKS[x] := ModularCompositionSetup(poly[x], f, bkt);
		    vprintf BrentKung, 1: 
   		        "Compose f^(%o)(f^(%o)) -> f^(%o)\n", y, x, s;
		    vtime BrentKung, 1:
		    g := ModularCompositionApply(poly[y], BKS[x], f, bkt);
		end if;
		poly[s] := g;
	    end if;
	end for;
	IndentPop();
	if (poly[i] - X) mod f eq 0 then 
	    return i;
	end if;
	step +:= 1;
    end for;
    return Max(r_vals), poly;
end function;

procedure OptimalModularCompositionApply(~setup, r, ~f_r)
    // Given setup information for a polynomial f and modulus m,
    // set g_r to be the r-th self-composition of f modulo m.

    m := setup[1];
    poly := setup[2]; 
    BKS := setup[3];

    if IsDefined(poly, r) then
	f_r := poly[r];
	return;
    end if;   

    //bkt := Ceiling(2 * Sqrt(Degree(m)));
    bkt := Ceiling(1 * Sqrt(Degree(m)));

    // Compute optimal composition steps to go from x_pow to each x^q^i mod f
    steps := Optimal_BK_Steps({i: i in [1 .. #poly] | IsDefined(poly, i)}, {r});
    assert #steps eq 1;
    if GetVerbose("BrentKung") gt 0 then
	print "Optimal Brent-Kung steps:";
	print steps;
	print "Computing power:", r;
    end if;
    IndentPush();
    // Set poly[r] to (x^q^r mod m).

    t := steps[1];
    assert t[1] eq r;
    p := t[2];
    for c in p do
	// Compose poly[x] with poly[y] to form poly[s]
	x := c[1];
	y := c[2];
	s := x + y;
	if not IsDefined(poly, s) then
	    assert IsDefined(poly, x);
	    assert IsDefined(poly, y);
	    // Use setup for x if known; i.e., form poly[y](poly[x])
	    if IsDefined(BKS, x) then
		vprintf BrentKung, 1:
		    "Compose f^(%o)(f^(%o)) -> f^(%o)\n", y, x, s;
		vtime BrentKung, 1:
		g := ModularCompositionApply(poly[y], BKS[x], m, bkt);
	    // Use setup for y if known; i.e., form poly[x](poly[y])
	    elif IsDefined(BKS, y) then
		vprintf BrentKung, 1:
		    "Compose f^(%o)(f^(%o)) -> f^(%o)\n", x, y, s;
		vtime BrentKung, 1:
		g := ModularCompositionApply(poly[x], BKS[y], m, bkt);
	    else
		// Set up for x and form poly[y](poly[x])
		vprintf BrentKung, 1: "Brent-Kung setup %o\n", x;
		vtime BrentKung, 1:
		BKS[x] := ModularCompositionSetup(poly[x], m, bkt);
		vprintf BrentKung, 1:
		    "Compose f^(%o)(f^(%o)) -> f^(%o)\n", y, x, s;
		vtime BrentKung, 1:
		g := ModularCompositionApply(poly[y], BKS[x], m, bkt);
	    end if;
	    poly[s] := g;
	end if;
    end for;
    IndentPop();
    setup := <m, poly, BKS>;
    f_r := poly[r];
end procedure;
