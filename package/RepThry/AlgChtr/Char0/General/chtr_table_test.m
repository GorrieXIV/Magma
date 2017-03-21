freeze;

intrinsic CheckCharacterTable (irreds::SeqEnum[AlgChtrElt], level::RngIntElt : Print := true) -> BoolElt
{Perform tests that the sequence irreds will pass if it is the character table
of a group. The parameter level controls how much testing is done, from 0 to 7.}

    if level le 0 then return true; end if;

    /* level 1: Check degrees */
    Z := Integers();
    CR := Universe(irreds);
    cl := ClassesData(CR);

    if Print then
	printf "Starting character degree checks\n";
	zeit := Cputime();
    end if;
    sos := 0;
    if #cl ne #irreds then
	if Print then printf "WRONG - incorrect number of characters"; end if;
	return false;
    end if;
    Gord := &+[c[2]: c in cl];
    N := Gord div #[c: c in cl | c[2] eq 1];
    for x in irreds do
	flag, deg := IsCoercible(Z, Degree(x));
	if not flag then
	    if Print then printf "WRONG - degree is not an integer\n"; end if;
	    return false;
	end if;
	if deg le 0  or N mod deg ne 0 then
	    if Print then printf "WRONG - degree %o is impossible\n", deg; end if;
	    return false;
	end if;
	sos +:= deg^2;
    end for;
    if sos ne Gord then
	if Print then printf "WRONG - Sum of degree squares is not group order\n"; end if;
	return false;
    end if;
    if Print then
	printf "Finished character degree checks in %o secs\n", Cputime(zeit);
    end if;
    if level le 1 then return true; end if;

    /* level 2: Check Frob-Schur indicators */
    if Print then
	printf "Starting Schur indicator checks\n";
	zeit := Cputime();
    end if;
    sos := 0;
    for x in irreds do
	s := Schur(x, 2);
	flag, s_Z := IsCoercible(Z, s);
	if not flag then 
	    if Print then printf "WRONG - Schur indicator not an integer\n";  end if;
	    return false;
	end if;
	if s_Z notin {0,1,-1} then 
	    if Print then printf "WRONG - Schur indicator %o\n", s_Z; end if;
	    return false;
	end if;
	if s_Z eq -1 and Z!Degree(x) mod 2 ne 0 then
	    if Print then printf "WRONG - Schur indicator %o, degree %o\n", s_Z, Z!Degree(x); end if;
	    return false;
	end if;
	sos +:= s_Z * Degree(x);
    end for;
    if sos ne &+[c[2]:c in cl|c[1] le 2] then
	if Print then printf "WRONG - Count of involutions is incorrect\n"; end if;
	return false;
    end if;
    if Print then
	printf "Finished Schur indicator checks in %o secs\n", Cputime(zeit);
    end if;
    if level le 2 then return true; end if;

    /* Level 3: Check norms - have to compute from scratch */
    if Print then
	printf "Starting character norm checks\n";
	zeit := Cputime();
    end if;
    pm := PowerMap(CR);
    invs := [pm(i, -1):i in [1..#cl]];
    for x in irreds do
	y := Eltseq(x);
	K := Universe(y);
	sum := 0;
	for i := 1 to #cl do
	    sum +:= cl[i,2]*y[i]*y[invs[i]];
	end for;
	flag, sum := IsCoercible(Z, sum);
	if not flag then 
	    if Print then printf "WRONG - Norm not an integer\n";  end if;
	    return false;
	end if;
	if sum ne Gord then 
	    if Print then printf "WRONG - Norm not 1 (%o)\n", sum; end if;
	    return false;
	end if;
    end for;
    if Print then
	printf "Finished norm checks in %o secs\n", Cputime(zeit);
    end if;
    if level le 3 then return true; end if;

    if Print then
	printf "Starting checks of integrality and mod p congruences\n";
	zeit := Cputime();
    end if;
    /* Compute p-parts & p'-parts for future use */
    G_ord := Factorization(Gord);
    pc := []; /* p part classes */
    ppc := []; /* p' part classes */
    for t in G_ord do
	p := t[1];
	pp := [];
	ppp := [];
	for i := 1 to #cl do
	    v, r := Valuation(cl[i,1], p);
	    pv := p^v;
	    _,a,b:= Xgcd(pv, r);
	    pp[i] := pm(i, b*r);
	    ppp[i] := pm(i, a*pv);
	end for;
	Append(~pc, pp);
	Append(~ppc, ppp);
    end for;

    /* Level 4: Number theoretic congruences */
    for x in irreds do
	y := [x[i]:i in [1..#cl]];
	K := Universe(y);
	R := IntegerRing(K);
	fl, y := CanChangeUniverse(y, R);
	if not fl then 
	    if Print then printf "WRONG - Non-integral character values\n"; end if;
	    return false;
	end if;
	for i := 1 to #G_ord do
	    ppp := ppc[i];
	    p := G_ord[i,1];
	    for j := 1 to #cl do
		pppj := ppp[j];
		if pppj eq j then continue j; end if;
		if not IsZero(Modexp(y[j]-y[pppj], cl[j,1] div cl[pppj,1], p)) 
		then
		    if Print then 
			printf "WRONG - congruence with p'-part\n";
			printf "Prime: %o, Class: %o, p' class: %o\n",p,j,pppj;
			printf "Values: %o, %o\n", K!y[j], K!y[pppj];
		    end if;
		    return false;
		end if;
	    end for;
	end for;
    end for;
    if Print then
	printf "Finished checks of integrality and congruences in %o secs\n", Cputime(zeit);
    end if;
    if level le 4 then return true; end if;

    /* Level 5: Row orthogonality */
    if Print then
	printf "Starting checks of row orthogonality\n";
	zeit := Cputime();
    end if;
    for i := 2 to #cl do
	for j := 1 to i-1 do
	    ip := InnerProduct(irreds[i], irreds[j]);
	    if not IsZero(ip) then
		if Print then 
		    printf "WRONG - Inner product (%o,%o) not zero (%o)\n",
			i,j,ip;
		end if;
		return false;
	    end if;
	end for;
    end for;
    if Print then
	printf "Finished checks of orthogonality in %o secs\n", Cputime(zeit);
    end if;
    if level le 5 then return true; end if;

    /* Level 6: Block column orthogonality */
    if Print then
	printf "Starting checks of block column orthogonality\n";
	zeit := Cputime();
    end if;
    blocks := Blocks(irreds);
    for i := 1 to #blocks do
	blks := blocks[i,2];
	pp := pc[i];
	for j := 1 to #cl-1 do
	    ppj := pp[j];
	    j_inv := invs[j];
	    for k := j+1 to #cl do
		if pp[k] eq ppj then continue k; end if;
		for b in blks do
		    if not IsZero(&+[irreds[c, j_inv]*irreds[c, k] : c in b])
		    then
			if Print then printf "WRONG - block column orthogonality failed\n"; end if;
			return false;
		    end if;
		end for;
	    end for;
	end for;
    end for;
    if Print then
	printf "Finished checks of block orthogonality in %o secs\n", Cputime(zeit);
    end if;
    if level le 6 then return true; end if;

    /* Level 7: Decompose symmetrized powers */
    if Print then
	printf "Starting checks of symmetrized powers\n";
	zeit := Cputime();
    end if;
    for x in irreds do
	s := SymmetricComponents(x, 3);
	for y in s do
	    c, res := Decomposition(irreds, y);
	    if not IsZero(res) then
		if Print then printf "WRONG - Symmetric component does not fully decompose\n"; end if;
		return false;
	    end if;
	    fl, c := CanChangeUniverse(c, Z);
	    if not fl or exists{i: i in c | i lt 0} then
		if Print then printf "WRONG - Symmetric component does not decompose well\n"; end if;
		return false;
	    end if;
	end for;
    end for;
    if Print then
	printf "Finished checks of symmetrized powers in %o secs\n", Cputime(zeit);
    end if;

    return true;

end intrinsic;
