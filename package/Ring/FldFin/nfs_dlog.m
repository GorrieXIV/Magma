freeze;

DEBUG_NFS_DLOG := false;

function xoverPH()   /* return cross over to Pohlig Hellman */

    return 2^48;
    
end function;

function special_q_power(n)   /* consecutive bounds go down for special q as ^special_q_power */

    if (n eq 3) then
	return 0.9;
    end if;
    
    return 0.75;
    
end function;

function smooth_combo_power(n)  /* start of descent allows for primes up to sieve^smooth_combo_power() */

    if (n eq 3) then
	return 2.5;
    end if;

    return 2.5;

end function;


function sub_exp(q, a, b)  /* computes L_q(a,b) */
    
    return Exp(b*(Log(q))^(a)*(Log(Log(q)))^(1-a));
    
end function;

function select_nfs_bounds(p, n)
    
    q := p^n;
    Ab := 0;
    mF := 0;
    mG := 0;
    L := sub_exp(q, 1/3, (8/9)^(1/3));
    mc := 0;
    ac := 0;
    
    if (n eq 1) then

	mc := 0.1;
	ac := 3;

	if (p lt 2^150) then
	    mc := 0.2;
	    ac := 5;
	end if;
	
    end if;
    
    if (n eq 2) then  /* basic case for complexity */
	mc := 0.5;
	ac := 10;
	
	if (p lt 2^70) then
	    mc := 0.5;
	    ac := 10;
	end if;

	if (p lt 2^60) then
	    mc := 0.35;
	    ac := 10;
	end if;
	
    end if;

    if (n eq 3) then  /* basic case for complexity */

	mc := 0.15;
	ac := 60;
	
	if (p lt 2^45) then
	    mc := 0.25;
	    ac := 50;
	end if;
	
	if (p lt 2^35) then
	    mc := 0.4;
	    ac := 50;
	end if;
	
    end if;
    
    mF := Round(mc*L);
    mG := mF;
    Ab := ac*mF;	
    
    return Ab, mF, mG;
    
end function;

function approx_size_of_FB(fmon, mF, gmon, mG)

    p := 2;
    tot_size := 0;
    
    while (p lt Maximum([mF, mG])) do
	Fpx := PolynomialRing(GF(p));
	if (p lt mF) then
	    tot_size +:= #Roots(Fpx ! fmon);
	end if;
	if (p lt mG) then
	    tot_size +:= #Roots(Fpx ! gmon);
	end if;
	p := NextPrime(p);
    end while;

    return tot_size;
    
end function;

function BSGS_dlog(g, h, pi)  /* order of g is prime pi */

    B := Ceiling(Sqrt(pi));

    babies := [ Parent(g) ! 1 : i in [0..B-1] ];
    for i := 2 to #babies do
	babies[i] := babies[i-1]*g;
    end for;

    ggiant := g^(-B);
    current := h;

    baby_index := 0;
    giant_index := 0;
    
    for i := 0 to B-1 do
	baby_index := Index(babies, current);
	if (baby_index ne 0) then
	    baby_index -:= 1;
	    giant_index := i;
	    break;
	else
	    current *:= ggiant;
	end if;
    end for;

    dlog := (baby_index + giant_index*B) mod pi;

    if (g^dlog ne h) then
	error "DLOG computation in BSGS made error";
    end if;

    return dlog;
    
end function;

function PohligHellman(g, h)  /* assumes order of g consists of powers of small primes */

    Order_g := Order(g);
    Order_h := Order(h);

    if ((Order_g mod Order_h) ne 0) then
	return -1;
    end if;
    
    Fs := Factorisation(Order_g);

    dlogs := [];
    exponents := [];
    
    for i := 1 to #Fs do

	pi := Fs[i][1];
	exppi := Fs[i][2];
	gproj := g^(Order_g div pi^exppi);
	hproj := h^(Order_g div pi^exppi);
	
	if (hproj eq 1) then
	    dlogpi := 0;
	else
	    pow_gproj := [gproj];
	    pow_hproj := [hproj];
	    
	    for k := 2 to exppi do
		Append(~pow_gproj, pow_gproj[k-1]^pi);
		Append(~pow_hproj, pow_hproj[k-1]^pi); 
	    end for;
	    
	    dlogpi := 0;
	    for k := exppi to 1 by -1 do
		logk := BSGS_dlog(pow_gproj[exppi], pow_hproj[k]/pow_gproj[k]^dlogpi, pi);
		dlogpi := dlogpi + pi^(exppi - k)*logk;
	    end for;
	end if;
	
	Append(~dlogs, dlogpi);
	Append(~exponents, pi^exppi);
	
    end for;
       
    return CRT(dlogs, exponents) mod Order_g; 

end function;

function find_cyclic_poly_general(p, n, d)
    
    /* constructs irreducible polynomial of degree n */
    /* that splits into degree d polynomials mod p and has */
    /* cyclic Galois group */
    
    if ((n mod d) ne 0) then
	"d has to be multiple of n";
	return 0;
    end if;
    
    m := NextPrime(n);
    Res := 0;
    Zx := PolynomialRing(Integers()); X := Zx.1;
    Fp := FiniteField(p);
    Fpx := PolynomialRing(Fp); x := Fpx.1;
    
    while (Res eq 0) do
	
	if ((m mod n) eq 1) then  /* can do the cyclotomic construction */
	    
	    Zm := FiniteField(m);
	    gen := 0;
	    for k := 2 to m-1 do
                if (Order(Zm ! k) eq (m-1)) then
		    gen := k;
		    break;
		end if;
	    end for;
	    
	    K := NumberField(CyclotomicPolynomial(m));
	    root := K.1;

	    ind := (m-1) div n;
	    
	    for k := 1 to ind-1 do
                root := root + K.1^(gen^(n*k));
	    end for;
	    
	    Res := Zx ! MinimalPolynomial(root);
	    
            F := Factorisation(Fpx ! Res);
	    for i := 1 to #F do
                if (Res ne 0) and (Degree(F[i][1]) ne d) then 
                    Res := 0;
                end if;
            end for;
        end if;

        m := NextPrime(m);
       
    end while;
    
    return Res;
    
end function;

function construct_mod_p_multiple(p, f, d)
    
    /* constructs a polynomial of degree d that is a multiple */
    /* of the polynomial f modulo p */
    
    if (Degree(f) gt d) then
        "d should be at least degree of f";
        return 0;
    end if;
    
    f0 := f;
    found := false;
    W := Round(p^(1/(d+1)));
    ZX := Parent(f);
    X := ZX.1;
    
    while (not found) do
        f1 := Evaluate(f0, X + W);
        numcols := d+1;
        numrows := 2*d - Degree(f) + 2;
        M := ZeroMatrix(Integers(), numrows, numcols);
        
        for i := 0 to d-Degree(f) do
            fi := f1*X^i;
            for j := 0 to Degree(fi) do
                M[i+1][j+1] := Coefficient(fi,j);
            end for;
        end for;

        j := 1;
        for i := d-Degree(f)+2 to numrows do
            M[i][j] := p;
            j +:= 1;
        end for;
        
        L := LLL(M);
        
        f2 := ZX ! 0;
        for i := 1 to numcols do
            f2 +:= L[1][i]*X^(i-1);
        end for;
	
	/* final test */
        
        found := (f2 mod f1) ne 0;
        
        W := Round(1.1*W);
    end while;
    
    return f1, f2;

end function;

function construct_minimum_poly_mod_p(p, f, alpha, d)
    
    /* constructs a polynomial of degree d such that alpha is zero modulo p */
    
    M := DiagonalMatrix(Integers(), d+1, [1 : i in [1..(d+1)]]);
    M[1][1] := p;
    for i := 2 to (d+1) do
	M[i][1] := (-(alpha^(i-1))) mod p;
    end for;
    
    L := LLL(M);
    
    ZX := Parent(f);
    X := ZX.1;
    
    f2 := ZX ! 0;
    for i := 1 to (d+1) do
	f2 +:= L[1][i]*X^(i-1);
    end for;
    
    return f2;
    
end function;

function construct_polys(p, n)

    /* constructs two polynomials f and g such that f | g mod p and irreducible over integers */

    f := 0;
    g := 0;

    if (n eq 1) then  /* doing reverse construction */
	
	f := find_cyclic_poly_general(p, 3, 1);
	R := Roots(f, GF(p));
	alpha := Integers() ! R[1][1];
	g := construct_minimum_poly_mod_p(p, f, alpha, 2);
	
    end if;
    
    if (n eq 2) then  /* constructing degree 2 and 3 */
	
	ft := find_cyclic_poly_general(p, 2, 2);
	f, g := construct_mod_p_multiple(p, ft, 3);
	
    end if;

    if (n gt 2) then
	f := find_cyclic_poly_general(p, n, n);
	g := f + p;
    end if;
    
    if (LeadingCoefficient(g) lt 0) then
	g := -g;
    end if;
    
    return f, g;
 
end function;

function schirokauer_exponent(f, ell)

    fmodell := PolynomialRing(FiniteField(ell))!Coefficients(f);
    fcts := Factorization(fmodell);
    
    /* Do we ramify ? */
    if Max([x[2] : x in fcts]) gt 1 then
	"ARGHHH, ", f, "is not square-free mod ", ell, "I give up...";
	return 0;
    end if;
    
    epsilonf := LCM([Degree(x[1]) : x in fcts]);
    return epsilonf;
    
end function;

function get_hard_part_data(p, n, f, g)

    /* computes large non-smooth factor of group order */
    /* also computes schirokauer exponents */
    
    Facs := Factorisation(p^n-1);
    
    ell := 1;
    big_prime_bound := 2^25;
    schirokexp1 := 1;
    schirokexp2 := 1;
    
    for i := 1 to #Facs do
	if (Facs[i][1] gt big_prime_bound) then
	    ell := ell*Facs[i][1]^Facs[i][2];

	    /* compute Schirokauer exponent for F */
	    
	    s1 := schirokauer_exponent(f, Facs[i][1]);
	    schirokexp1 *:= Facs[i][1]^(Facs[i][2]*s1) - 1;
	    
	    /* compute Schirokauer exponent for G */
	    
	    s2 := schirokauer_exponent(g, Facs[i][1]);
	    schirokexp2 *:= Facs[i][1]^(Facs[i][2]*s2) - 1;
	end if;
    end for;

    return ell, schirokexp1, schirokexp2;
    
end function;

function get_bad_primes(I, Pr)
    
    /* gives index of bad primes, not primes themselves */
    
    b_primes := [];
    
    for i := 1 to #Pr do
	if ((I mod Pr[i]) eq 0) then /* bad prime */
	    Append(~b_primes, i);
	end if;
    end for;
    
    return b_primes;
    
end function;

procedure add_lc_cols(~M, cF, cG)

     Nrows := NumberOfRows(M);
     Ncols := NumberOfColumns(M);

     if ((cF ne 1) and (cG ne 1)) then
	 for i := 1 to Nrows do
	     SetEntry(~M, i, Ncols+1, 1);
	     SetEntry(~M, i, Ncols+2, -1);
	 end for;
     end if;

     if ((cF eq 1) and (cG ne 1)) then
	 for i := 1 to Nrows do
	     SetEntry(~M, i, Ncols+1, -1);
	 end for;
     end if;

     if ((cF ne 1) and (cG eq 1)) then
	 for i := 1 to Nrows do
	     SetEntry(~M, i, Ncols+1, 1);
	 end for;
     end if;

end procedure;

procedure fix_up_index_lc_divisors(~M, FB, FI, nr, ~bad_ideals, ~bad_ideals_index)

    /* FI contains field info */
    /* number field F */
    /* maximal order OF */
    /* index of OFE in OF */
    
    Ncols := NumberOfColumns(M);
    F := FI[1];
    OF := FI[2];
    Ind := FI[3];
    cf := FI[4];
    
    Pind := 1;
    Iind := 2*nr;
    
    offset := (nr-1)*#FB[2];  /* gives offset in variable array */

    /* getting bad primes in FB */
    
    bad_primes := get_bad_primes(Ind*cf, FB[1]);
    New_nr_cols := Ncols;

    for i := 1 to #bad_primes do

	/* getting true prime ideal factors of p*OF */
	
	Facs := Factorisation((FB[1][bad_primes[i]])*OF);
	num_id := #Facs;
	for j := 1 to num_id do
	    Append(~bad_ideals, Facs[j][1]);
	    Append(~bad_ideals_index, 0);
	end for;
	
	/* getting start index for section that starts at bad primes */
	
	start_ind := Index(FB[Iind], bad_primes[i]);
	
	/* writing column indices in bad_ideals_index */ 
	
	if (start_ind ne -1) then
	    k := start_ind;
	    while (FB[Iind][k] eq bad_primes[i]) do
		bad_ideals_index[#bad_ideals_index - num_id + k - start_ind + 1] := k + offset;
		k +:= 1;
	    end while;
	else
	    start_ind := 0;
	    k := 0;
	end if;
	
	/* if not all ideals have been assigned index then need to add columns */

	for j := #bad_ideals_index - num_id + k - start_ind + 1 to #bad_ideals_index do
	    New_nr_cols +:= 1;
	    bad_ideals_index[j] := New_nr_cols;
	end for;
    end for;

    /* getting bad primes not in FB */
    
    Find := Factorisation(Ind*cf);
    
    for i := 1 to #Find do
	pi := Find[i][1];
	if (pi gt FB[1][#FB[1]]) then /* not taken care of yet */
	    Facs := Factorisation(pi*OF);
	    num_id := #Facs;
	    for j := 1 to num_id do
		Append(~bad_ideals, Facs[j][1]);
		New_nr_cols +:= 1;
		Append(~bad_ideals_index, New_nr_cols);
	    end for;
	end if;
    end for;
    
    /* Computing valuation at bad prime ideals for each relation */
    
    Nrows := NumberOfRows(M);
    for i := 1 to Nrows do
	el_ideal := (cf*FB[6][i] - FB[7][i]*F.1)*OF;
	for j := 1 to #bad_ideals do
	    val_prime := Valuation(el_ideal, bad_ideals[j]);
	    SetEntry(~M, i, bad_ideals_index[j], (-1)^(nr - 1)*val_prime);
	end for;
    end for;
end procedure;

procedure clean_matrix(~M, ~FB)
    
    /* cleans up sparse matrix M */
    /* cols of weight zero and one are removed */
    /* then done again and again */
    
    Stop := false;
    
    while not (Stop) do
	Stop := true;
	
	CW := ColumnWeights(M);
	Nros := NumberOfRows(M);
	
	RowsToDelete := {@ @};
	for i := 1 to #CW do
	    if (CW[i] eq 1) then
		Stop := false;
		for j := 1 to Nros do
		    if not (M[j][i] eq 0) then
			Include(~RowsToDelete, j);
		    end if;
		end for;
	    end if;
	end for;
	
	RowsToDelete := Sort(SetToSequence(RowsToDelete));
	for i := 1 to #RowsToDelete do
	    RemoveRow(~M, RowsToDelete[i] - i + 1);
	    Remove(~FB[6], RowsToDelete[i] - i + 1);
	    Remove(~FB[7], RowsToDelete[i] - i + 1);
	end for;
    end while;
    
end procedure;

procedure fix_up_fb_dlogs(~V, ell, Rem_EQ)
    
    /* only doing two passes, we should have most of them after this */
    
    Nros := NumberOfRows(Rem_EQ);
    for m := 1 to 3 do
	for i := 1 to Nros do
	    S := Support(Rem_EQ, i);
	    tot_k := 0;
	    one_ind := 0;
	    for k := 1 to #S do
		if (V[S[k]] eq 0) then
		    tot_k +:= 1;
		    one_ind := S[k];
		end if;
	    end for;
	    
	    if (tot_k eq 1) then  /* now we are sure we can fix things up correctly */
		correct_log := 0;
		for k := 1 to #S do
		    correct_log +:= V[S[k]]*Rem_EQ[i][S[k]];
		end for;
		Zell := Integers(ell);
		inv_coeff := Integers() ! ((Zell ! Rem_EQ[i][one_ind])^(-1));
		V[one_ind] := (-inv_coeff*correct_log) mod ell;
	    end if;
	end for;
    end for;

end procedure;

function find_root(Id, pi, F)
    Fpi := FiniteField(pi);
    Fpix := PolynomialRing(Fpi);
    R := Roots(Fpix ! DefiningPolynomial(F));
    
    for i := 1 to #R do
	r := Integers() ! R[i][1];
	if ((r - F.1) in Id) then
	    break;
	end if;
    end for;
    
    return Integers() ! r;
end function;

function find_index_in_V(FB, p, r, nr, lc)

    /* Finds the correct index for the ideal (p, lc*r - theta) */
    /* Only for ideals that do not divide the index and are not projective! */
    
    ip := Index(FB[1], p);
    field_ind := 2 + 2*(nr-1);
    offset := (nr-1)*#FB[2];
    d, invlc, _ := XGCD(lc, p);
    radjust := (r*invlc) mod p;
    
    ipind := Index(FB[field_ind], ip);

    k := ipind;
    ind := 0;
    while (p eq FB[1][ FB[field_ind][k] ]) do  /* in the same prime, looking for correct root */
	if (FB[field_ind+1][k] eq radjust) then
	    ind := k;
	    break;
	end if;
	k := k+1;
    end while;
    
    return offset + ind;
    
end function;

function check_relations(ell, M, FB, num_field_info, bad_ideal_info, pars)

    new_M := SparseMatrix();
    
    As := FB[6];
    Bs := FB[7];
    
    F := num_field_info[1];
    OF := num_field_info[2];
    IF := num_field_info[3];
    cF := num_field_info[4];
    
    G := num_field_info[5];
    OG := num_field_info[6];
    IG := num_field_info[7];
    cG := num_field_info[8];
    
    bad_ideals_F := bad_ideal_info[1];
    bad_ideals_index_F := bad_ideal_info[2];
    
    bad_ideals_G := bad_ideal_info[3];
    bad_ideals_index_G := bad_ideal_info[4];
    
    index_schirokF := pars[1];
    nr_schirokF := pars[2];
    schirokexpF := pars[3];
    
    index_schirokG := pars[4];
    nr_schirokG := pars[5];
    schirokexpG := pars[6];
    
    Zell2 := PolynomialRing(Integers(ell^2));
    Zell2zF<zF> := quo<Zell2 | Zell2 ! DefiningPolynomial(F)>;
    Zell2zG<zG> := quo<Zell2 | Zell2 ! DefiningPolynomial(G)>;
        
    for i := 1 to #As do
	
	a := As[i];
	b := Bs[i];
	
	FacsF := Factorisation((cF*a - b*F.1)*OF);
	FacsG := Factorisation((cG*a - b*G.1)*OG);
	
	for j := 1 to #FacsF do
	    
	    Idj := FacsF[j][1];
	    Idexp := FacsF[j][2];
	    
	    pj := Factorisation(Integers() ! Norm(Idj))[1][1];

	    if (((IF*cF) mod pj) eq 0) then
		ind_pi := Index(bad_ideals_F, Idj);
		ind_ideal := bad_ideals_index_F[ind_pi];
	    else
		rj := find_root(Idj, pj, F);
		ind_ideal := find_index_in_V(FB, pj, rj, 1, cF);
	    end if;
	    
	    SetEntry(~new_M, i, ind_ideal, Idexp);
	    
	    if (M[i][ind_ideal] ne Idexp) then
		print "ERROR !!!!!!!!!";
		print "F";
		print Idj;
		print M[i][ind_ideal], Idexp;
	    end if;
	end for;
	
	rs := (cF*a - b*zF)^schirokexpF - 1;
	maps := [Integers() ! (x div ell) : x in Coefficients(rs)];
	for j := 1 to Minimum(#maps, nr_schirokF) do
	    SetEntry(~new_M, i, index_schirokF + j - 1, maps[j]);
	    if (M[i][index_schirokF + j - 1] ne maps[j]) then
		print "ERROR in schirokauer maps F";
	    end if;
	end for;

	for j := 1 to #FacsG do
	    
	    Idj := FacsG[j][1];
	    Idexp := FacsG[j][2];
	    
	    pj := Factorisation(Integers() ! Norm(Idj))[1][1];
	    
	    if (((IG*cG) mod pj) eq 0) then
		ind_pi := Index(bad_ideals_G, Idj);
		ind_ideal := bad_ideals_index_G[ind_pi];
	    else
		rj := find_root(Idj, pj, G);
		ind_ideal := find_index_in_V(FB, pj, rj, 2, cG);
	    end if;
	    
	    SetEntry(~new_M, i, ind_ideal, -Idexp);
	    
	    if (M[i][ind_ideal] ne -Idexp) then
		print "ERROR !!!!!!!!!";
		print "G";
		print Idj;
		print M[i][ind_ideal], Idexp;
	    end if;
	end for;

	rs := (cG*a - b*zG)^schirokexpG - 1;
	maps := [Integers() ! (x div ell) : x in Coefficients(rs)];
	for j := 1 to Minimum(#maps, nr_schirokG) do
	    SetEntry(~new_M, i, index_schirokG + j - 1, -maps[j]);
	    if (M[i][index_schirokG + j - 1] ne -maps[j]) then
		print "ERROR in schirokauer maps G";
	    end if;
	end for;
    end for;
    
    return new_M;
end function;

function check_results(ell, FB, F, G, Rq, V, pars)

    p := Characteristic(Rq);
    n := Degree(Rq);
    
    Pol := DefiningPolynomial(Rq);
    Polring := Parent(Pol);
    
    Fell := Integers(ell);
    Ps := FB[1];
    I1 := FB[2];
    r1 := FB[3];
    I2 := FB[4];
    r2 := FB[5];

    index_schirokF := pars[1];
    nr_schirokF := pars[2];
    schirokexpF := pars[3];
    
    index_schirokG := pars[4];
    nr_schirokG := pars[5];
    schirokexpG := pars[6];
    
    OF := MaximalOrder(F);
    OG := MaximalOrder(G);
    
    hF := ClassNumber(F);
    /* hG := ClassNumber(G); */

    print "ClassNumber F =",  hF;
    /* print "ClassNumber G =",  hG; */

    OK_index := 1;
    
    while (GCD(V[OK_index], ell) gt 1) do
	OK_index +:= 1;
    end while;
    
    Zell2 := PolynomialRing(Integers(ell^2));
    Zell2zF<zF> := quo<Zell2 | Zell2 ! DefiningPolynomial(F)>;
    Zell2zG<zG> := quo<Zell2 | Zell2 ! DefiningPolynomial(G)>;
    
    Id1 := ideal<OF | Ps[I1[OK_index]], (r1[OK_index] - F.1)>;
    _, g1 := IsPrincipal(Id1^hF);
    rs := (Zell2zF ! Eltseq(g1))^schirokexpF - 1;
    maps := [x div ell : x in Coefficients(rs)];
    scalar := hF*V[OK_index];
    for j := 1 to Minimum(#maps, nr_schirokF) do
	scalar +:= V[index_schirokF + j - 1]*maps[j];
    end for;
    invscalar := (Fell ! scalar)^(-1);
    g1l := (Rq ! [Integers() ! c : c in Eltseq(g1)])^((p^n - 1) div ell);
    
    for i := 1 to #I1 do
	Ii := ideal<OF | Ps[I1[i]], (r1[i] - F.1)>;
	_, gi := IsPrincipal(Ii);
	rs := (Zell2zF ! Eltseq(gi))^schirokexpF - 1;
	maps := [x div ell : x in Coefficients(rs)];
	scalari := hF*V[i];
	for j := 1 to Minimum(#maps, nr_schirokF) do
	    scalari +:= V[index_schirokF + j - 1]*maps[j];
	end for;
	
	coeffs := [Integers() ! c : c in Eltseq(gi)];
	
	gil := (Rq ! coeffs)^((p^n - 1) div ell);
	
	dlog := Integers() ! ((Fell ! scalari)*invscalar);
	
	if not(gil eq g1l^(dlog)) then
	    print "F", i, V[i];
	end if;
	
    end for;

    /*
    for i := 1 to #I2 do
	Ii := ideal<OG | Ps[I2[i]], (r2[i] - G.1)>;
	b, gi := IsPrincipal(Ii^hG);
	
	if (b) then
            rs := (Zell2zG ! Eltseq(gi))^schirokexpG - 1;
	    maps := [x div ell : x in Coefficients(rs)];
	    scalari := hG*V[i + #I1];
	    for j := 1 to Minimum(#maps, nr_schirokG) do
		scalari +:= V[index_schirokG + j - 1]*maps[j];
	    end for;
	    
	    coeffs := [Integers() ! c : c in Eltseq(gi)];
	    
	    gil := (Rq ! Eltseq((Polring ! coeffs) mod Pol))^((p^n - 1) div ell);
	    
	    dlog := Integers() ! ((Fell ! scalari)*invscalar);

	    if not(gil eq g1l^(dlog)) then
		print "G", i, V[i + #I1];
	    else
		print "G CORRECT ===========================================================";
	    end if;
	end if;

    end for;
    */
    
    return 0;
    
end function;

function dlog_smooth_el(a, b, data_DLOGS)

    /* need to rebuild relation belonging to cF*a - b*OF.1 */
    /* then derive log if all entries in V we need are non-zero */
    
    F := data_DLOGS[3][5];
    OF := data_DLOGS[3][6];
    IF := data_DLOGS[3][8];
    cF := data_DLOGS[3][3];

    cG := data_DLOGS[4][3];

    bad_ideals_F := data_DLOGS[3][12];
    bad_ideals_index_F := data_DLOGS[3][13];
    
    index_schirokF := data_DLOGS[3][9];
    nr_schirokF := data_DLOGS[3][10];
    schirokexpF := data_DLOGS[3][11];

    FB := data_DLOGS[1];
    V := data_DLOGS[2];

    CW := data_DLOGS[6];
    
    ell := data_DLOGS[5][5];
    
    Zell2 := PolynomialRing(Integers(ell^2));
    Zell2zF<zF> := quo<Zell2 | Zell2 ! DefiningPolynomial(F)>;
            
    FacsF := Factorisation((cF*a - b*F.1)*OF);

    LogOK := true;
    LogEl := 0;
    
    for j := 1 to #FacsF do
	
	Idj := FacsF[j][1];
	Idexp := FacsF[j][2];
	
	pj := Factorisation(Integers() ! Norm(Idj))[1][1];
	
	if (((IF*cF) mod pj) eq 0) then
	    ind_pi := Index(bad_ideals_F, Idj);
	    ind_ideal := bad_ideals_index_F[ind_pi];
	else
	    rj := find_root(Idj, pj, F);
	    ind_ideal := find_index_in_V(FB, pj, rj, 1, cF);
	end if;

	if (V[ind_ideal] ne 0) then
	    LogEl +:= Idexp*V[ind_ideal];
	else
	    if (CW[ind_ideal] lt 5) then /* otherwise dlog is really zero */
		LogOK := false;
	    end if;
	end if;
	
    end for;

    if (cF ne 1) then /* need to also take log of leading coeff into account */
	ind_ideal := #V;
	if (cG ne 1) then
	    ind_ideal -:= 1;
	end if;
	LogEl +:= V[ind_ideal];
    end if;
    
    rs := (cF*a - b*zF)^schirokexpF - 1;
    maps := [Integers() ! (x div ell) : x in Coefficients(rs)];
    for j := 1 to Minimum(#maps, nr_schirokF) do
	LogEl +:= maps[j]*V[index_schirokF + j - 1];
    end for;

    if not (LogOK) then
	LogEl := -1;
    else
	LogEl := LogEl mod ell;
    end if;
    
    return LogEl;
    
end function;

function dlog_smooth_el_minus_ideal(Id, a, b, data_DLOGS)

    /* need to rebuild relation belonging to cF*a - b*OF.1 */
    /* then derive log if all entries in V we need are non-zero */
    
    F := data_DLOGS[3][5];
    OF := data_DLOGS[3][6];
    IF := data_DLOGS[3][8];
    cF := data_DLOGS[3][3];

    cG := data_DLOGS[4][3];

    bad_ideals_F := data_DLOGS[3][12];
    bad_ideals_index_F := data_DLOGS[3][13];
    
    index_schirokF := data_DLOGS[3][9];
    nr_schirokF := data_DLOGS[3][10];
    schirokexpF := data_DLOGS[3][11];

    FB := data_DLOGS[1];
    V := data_DLOGS[2];

    CW := data_DLOGS[6];
    
    ell := data_DLOGS[5][5];
    
    Zell2 := PolynomialRing(Integers(ell^2));
    Zell2zF<zF> := quo<Zell2 | Zell2 ! DefiningPolynomial(F)>;
            
    FacsF := Factorisation((cF*a - b*F.1)*OF);

    LogOK := true;
    LogEl := 0;
    
    for j := 1 to #FacsF do
		
	Idj := FacsF[j][1];
	Idexp := FacsF[j][2];

	if (Idj ne Id) then
	    
	    pj := Factorisation(Integers() ! Norm(Idj))[1][1];
	    
	    if (((IF*cF) mod pj) eq 0) then
		ind_pi := Index(bad_ideals_F, Idj);
		ind_ideal := bad_ideals_index_F[ind_pi];
	    else
		rj := find_root(Idj, pj, F);
		ind_ideal := find_index_in_V(FB, pj, rj, 1, cF);
	    end if;
	    
	    if (V[ind_ideal] ne 0) then
		LogEl +:= Idexp*V[ind_ideal];
	    else
		if (CW[ind_ideal] lt 5) then /* otherwise dlog is really zero */
		    LogOK := false;
		end if;
	    end if;
	end if;
	
    end for;

    if (cF ne 1) then /* need to also take log of leading coeff into account */
	ind_ideal := #V;
	if (cG ne 1) then
	    ind_ideal -:= 1;
	end if;
	LogEl +:= V[ind_ideal];
    end if;
    
    rs := (cF*a - b*zF)^schirokexpF - 1;
    maps := [Integers() ! (x div ell) : x in Coefficients(rs)];
    for j := 1 to Minimum(#maps, nr_schirokF) do
	LogEl +:= maps[j]*V[index_schirokF + j - 1];
    end for;

    if not (LogOK) then
	LogEl := -1;
	print "Cannot verify relation due to unknown log in FB";
    else
	LogEl := LogEl mod ell;
    end if;

    return LogEl;
    
end function;

function select_smooth_gen(data_DLOGS)

    As := data_DLOGS[1][6];
    Bs := data_DLOGS[1][7];
    cf := data_DLOGS[3][3];
    Fpn := data_DLOGS[5][3];
    modulus := data_DLOGS[5][4];
    z := Parent(modulus).1;
    ell := data_DLOGS[5][5];
    
    for i := 1 to #As do
	map_el := (Fpn ! ((cf*As[i] - Bs[i]*z) mod modulus))/cf;
	if ((Order (map_el) mod ell) eq 0) then /* ok we can map this into a generator modulo ell */ 
	    dlog_map_el := dlog_smooth_el(As[i], Bs[i], data_DLOGS);
	    if (dlog_map_el ne -1) then
		return As[i], Bs[i], dlog_map_el;
	    end if;
	end if;
    end for;
    
    return 0, 0, -1;
    
end function;


function check_results_simple(data_DLOGS)

    As := data_DLOGS[1][6];
    Bs := data_DLOGS[1][7];
    cf := data_DLOGS[3][3];
    Fpn := data_DLOGS[5][3];
    modulus := data_DLOGS[5][4];
    z := Parent(modulus).1;
    ell := data_DLOGS[5][5];
    
    Elns := [];
    Logs := [];
    for i := 1 to #As do
	map_el := (Fpn ! ((cf*As[i] - Bs[i]*z) mod modulus))/cf;
	dlog_map_el := dlog_smooth_el(As[i], Bs[i], data_DLOGS);
	if (dlog_map_el ne -1) then
	    Append(~Elns, map_el^((#Fpn - 1) div ell));
	    Append(~Logs, dlog_map_el);
	end if;
    end for;

    for i := 1 to #Elns do
	if (GCD(Logs[i], ell) eq 1) then
	    Logs[1] := Logs[i];
	    Elns[1] := Elns[i];
	    break;
	end if;
    end for;

    Zell := Integers(ell);
    LogInv := (Zell ! Logs[1])^(-1); 
    Logs := [Integers() ! (Logs[i]*LogInv) : i in [1..#Logs]];
    
    ElnsCheck := [Elns[i] - Elns[1]^Logs[i] : i in [1..#Logs]];

    return ElnsCheck eq [0 : i in [1..#ElnsCheck]];
    
end function;

function check_dlog_one_ideal(Id, a, b, dlog_check, data_DLOGS)

    /* given one relation a - b*theta divisible by Id, check if virtual dlog of Id is correct */
    
    As := data_DLOGS[1][6];
    Bs := data_DLOGS[1][7];
    cf := data_DLOGS[3][3];
    Fpn := data_DLOGS[5][3];
    modulus := data_DLOGS[5][4];
    z := Parent(modulus).1;
    ell := data_DLOGS[5][5];
    
    base_el := 0;
    base_log := 0;
    for i := 1 to #As do
	map_el := (Fpn ! ((cf*As[i] - Bs[i]*z) mod modulus))/cf;
	dlog_map_el := dlog_smooth_el(As[i], Bs[i], data_DLOGS);
	if (dlog_map_el ne -1) then
	    if (GCD(dlog_map_el, ell) eq 1) then
		base_el := map_el;
		base_log := dlog_map_el;
		break;
	    end if;
	end if;
    end for;

    map_el := (Fpn ! ((cf*a - b*z) mod modulus))/cf;
    dlog_el := dlog_smooth_el_minus_ideal(Id, a, b, data_DLOGS) + dlog_check;

    Zell := Integers(ell);
    LogInv := (Zell ! base_log)^(-1); 
    final_log := Integers() ! (dlog_el*LogInv);

    el1 := map_el^((#Fpn-1) div ell);
    el2 := base_el^((#Fpn-1) div ell);

    print "g", el1, "h", el2, "log", final_log;
    
    return el1 eq el2^final_log;

end function;


function iso_image_gen(Fq, Fpn)

     R := Roots(DefiningPolynomial(Fq), Fpn);
     return R[1][1];

end function;

function iso_rep_apply(g, iso_root)

     C := Eltseq(g);
     return &+[iso_root^(i-1)*C[i] : i in [1..#C]];

end function;

function is_smooth_FB_bound(N, FB_primes, B, n)  /* N should smooth and squarefree  */

     Res := AbsoluteValue(N);
     ind := 1;
     pow := 0;

     while (Res gt 1) and (ind le #FB_primes) do
	 while ((Res mod FB_primes[ind]) eq 0) do
	     pow +:= 1;
	     if (pow eq 2) then
		 return false;
	     end if;
	     Res := Res div FB_primes[ind];
	 end while;
	 pow := 0;
	 ind +:= 1;
     end while;

     is_smooth := false;

     if (n gt  2) then
	 /* we only want one large prime factor to limit special-q sieving */
	 if (Res lt B) then
	     if (Res eq 1 or IsPrime(Res)) then
		 is_smooth := true;
	     end if;
	 end if;
     else
	 if (Res gt 1) and (Res lt B) then
	     facs := Factorisation(Res);
	     is_smooth := Maximum([facs[i][2] : i in [1..#facs]]) lt 2;
	 end if;
	 
	 if (Res gt B) and (Res lt B^1.5) and not IsPrime(Res) then
	     facs := Factorisation(Res);
	     is_smooth := Maximum([facs[i][2] : i in [1..#facs]]) lt 2;
	     if (is_smooth) then
		 is_smooth := Maximum([facs[i][1] : i in [1..#facs]]) lt B;
	     end if;
	 end if;
     end if;
     
     return is_smooth;

end function;

function find_smooth_combo_Fp(el, smooth_gen, FBprimes, B, F, modulus)

    /* special routine for the Fp case since degree(F) != 1 */
    
    Fq := Parent(el);
    p := Characteristic(Fq);
    n := Degree(F);
    z := Parent(modulus).1;
    
    mu := Integers() ! ConstantCoefficient(z mod modulus);
     
    pow_el := 0;
    pow_sm := 0;
    
    M := ZeroMatrix(Integers(), 2*n, n^2 + n);
    
    /* fiddling in p's */
    
    for i := 1 to n do
	M[i][n^2 + i] := p;
    end for;
    
    found := false;
    
    while (not found) do

	pow_el := pow_el + 1;
	if (pow_el eq 50) then
	    pow_el := 1;
	    pow_sm +:= 1;
	end if;
	
	Mnew := M;
	c_pow := smooth_gen^pow_sm*el^pow_el;
	
	for i := 1 to n do
	    for j := 1 to n do
		Mnew[i][(i-1)*n + j] := c_pow*mu^(j-1);
		
		powmu := F.1^(j-1 + i-1);
		coeffsmu := Eltseq(powmu);
		
		for k := 1 to #coeffsmu do
		    Mnew[n+k][(i-1)*n + j] := coeffsmu[k];
		end for;
	    end for;
	end for;
	
	BB := Basis(LLL(Lattice(Transpose(Mnew))));
	
	for i := 1 to #BB do
	    num := &+[BB[i][k]*F.1^(k-1) : k in [1..n]];
	    denom := &+[BB[i][n + k]*F.1^(k-1) : k in [1..n]];
	    
	    Nnum := Integers() ! Norm(num);
	    Ndenom := Integers() ! Norm(denom);
	    
	    is_smooth_num := is_smooth_FB_bound(Nnum, FBprimes, B, 1);
	    
	    if (is_smooth_num) then
		if (is_smooth_FB_bound(Ndenom, FBprimes, B, 1)) then
		    found := true;
		    break;
		end if;
	    end if;
	end for;
	
    end while;
    
    return pow_el, pow_sm, num, denom;
    
end function;

function find_smooth_combo(el, smooth_gen, FBprimes, B, F, modulus)

    Fq := Parent(el);
    p := Characteristic(Fq);
    n := Degree(Fq);
    
    if (n eq 1) then
	return find_smooth_combo_Fp(el, smooth_gen, FBprimes, B, F, modulus);
    end if;

    if (Degree(F) ne Degree(Fq)) then
	error "Error: degree of number field is not equal to degree of finite field";
    end if;
    
    pow_el := 0;
    pow_sm := 0;
    
    M := Matrix(Integers(), 2*n, 2*n, [0 : i in [1..4*n^2]]);
    
    for i := n+1 to 2*n do
	M[i][i-n] := 1;
    end for;
    for i := n+1 to 2*n do
	M[i-n][i] := p;
    end for;

    found := false;
    
    while (not found) do

	pow_el := pow_el + 1;
	if (pow_el eq 50) then
	    pow_el := 1;
	    pow_sm +:= 1;
	end if;

	Mnew := M;
	c_pow := smooth_gen^pow_sm*el^pow_el;

	for j := 0 to n-1 do  
	    coeffs := Eltseq(Fq.1^j*c_pow);
	    for k := 1 to #coeffs do
		Mnew[k][j+1] := Integers() ! coeffs[k];
	    end for;
	end for;
		
	BB := Basis(LLL(Lattice(Transpose(Mnew))));
	
	for i := 1 to #BB do
	    num := &+[BB[i][k]*F.1^(k-1) : k in [1..n]];
	    denom := &+[BB[i][n + k]*F.1^(k-1) : k in [1..n]];
	    
	    Nnum := Integers() ! Norm(num);
	    Ndenom := Integers() ! Norm(denom);
	    
	    is_smooth_num := is_smooth_FB_bound(Nnum, FBprimes, B, n);
	    
	    if (is_smooth_num) then
		if (is_smooth_FB_bound(Ndenom, FBprimes, B, n)) then
		    found := true;
		    break;
		end if;
	    end if;
	end for;
	
    end while;
    
    return pow_el, pow_sm, num, denom;
    
end function;

function special_q_lattice_sieve(Id, pi, r, new_B, data_DLOGS, nr)

    F := data_DLOGS[3][5];
    OF := data_DLOGS[3][6];
    IF := data_DLOGS[3][8];
    cf := data_DLOGS[3][3];

    bad_idealsF := data_DLOGS[3][12];
    bad_ideals_indexF := data_DLOGS[3][13];
    
    G := data_DLOGS[4][5];
    OG := data_DLOGS[4][6];
    IG := data_DLOGS[4][8];
    cg := data_DLOGS[4][3];
    
    bad_idealsG := data_DLOGS[4][12];
    bad_ideals_indexG := data_DLOGS[4][13];

    ell := data_DLOGS[5][5];
    FB := data_DLOGS[1];
    V := data_DLOGS[2];
    CW := data_DLOGS[6];

    p := data_DLOGS[5][1];
    n := data_DLOGS[5][2];
    
    /* transforming polys back to original sieve polys, so not necessarily monic */
    
    /* need to transform ideal first */
    
    lc := 1;
    if (nr eq 1) then
	lc := cf;
	ind := IF;
    end if;
    if (nr eq 2) then
	lc := cg;
	ind := IG;
    end if;
    
    /* quick sanity check */
    
    if (GCD(Norm(Id), lc*ind) gt 1) then
	"Bad ideal given by ", Id;
	error "special_q_lattice_sieve can only handle degree 1 prime ideals or divisors of index/leading coefficient";
    end if;
        
    d, invlc, _ := XGCD(lc, pi);
    radjust := (r*invlc) mod pi;
    
    d, radjustinv, _ := XGCD(radjust, pi);
    L := GaussReduce(Matrix(Integers(), 2, 2, [1, radjustinv, 0, pi]));
    
    v0 := L[1][1]; v1 := L[1][2];
    w0 := L[2][1]; w1 := L[2][2];
    
    /* all pairs (x*v0 + y*w0, x*v1 + y*w1) are divisible by prime ideal (p, r - X) */
    
    f := DefiningPolynomial(F);
    g := DefiningPolynomial(G);
    
    Zxy<x,y> := PolynomialRing(Integers(),2);
    FPol := &+[ (((Integers() ! Coefficient(f,i))*(cf^i)) div cf^(Degree(f)-1))*x^i*y^(Degree(f)-i) : i in [0..Degree(f)]];
    GPol := &+[ (((Integers() ! Coefficient(g,i))*(cg^i)) div cg^(Degree(g)-1))*x^i*y^(Degree(g)-i) : i in [0..Degree(g)]];
    
    Fpolq := Evaluate(FPol, [x*v0 + y*w0, x*v1 + y*w1]);
    Gpolq := Evaluate(GPol, [x*v0 + y*w0, x*v1 + y*w1]);
    
    if (nr eq 1) then
	Fpolq := Fpolq div pi;
    end if;
    
    if (nr eq 2) then
	Gpolq := Gpolq div pi;
    end if;
    
    Ab, mF, mG := select_nfs_bounds(p, n);
    
    /* need to check that the pair is a good pair, i.e. only degree 1 ideals on both sides */
    
    num_pairs := 2;
    good_pair_found := false;

    a := 0;
    b := 0;
    
    while not (good_pair_found) do

	ps := [mF, mG, Ab, 0, 0, mF+1, mG+1, 13, 13, 0, num_pairs, ell, new_B];
	pairs := InternalSieveDLOGSpecialq(Fpolq, Gpolq, ps);	
	
	for k := 1 to num_pairs do
	    
	    i := pairs[1][k];
	    j := pairs[2][k];

	    a := i*v0 + j*w0;
	    b := i*v1 + j*w1;
	    
	    FFab := Factorisation((a*cf-b*F.1)*OF);
	    FGab := Factorisation((a*cg-b*G.1)*OG);
	    
	    deg_F := [Degree(Id[1]) : Id in FFab];
	    deg_G := [Degree(Id[1]) : Id in FGab];
	    
	    norms_F := [(Integers() ! Norm(Id[1])) : Id in FFab];
	    norms_G := [(Integers() ! Norm(Id[1])) : Id in FGab];
	    
	    if (nr eq 1) then
		ind_no := Index(norms_F, pi);
		if (ind_no gt 0) then
		    norms_F[ind_no] := 0;
		end if;
	    end if;
	    
	    if (nr eq 2) then
		ind_no := Index(norms_G, pi);
		if (ind_no gt 0) then
		    norms_G[ind_no] := 0;
		end if;
	    end if;
	    
	    /* Processing bad ideals in factorisation */
	    
	    for i := 1 to #deg_F do
		if (GCD(norms_F[i], IF*cf) gt 1) then /* bad ideal */
		    norms_F[i] := 0;
		    deg_F[i] := 0;
		end if;
	    end for;
	    
	    for i := 1 to #deg_G do
		if (GCD(norms_G[i], IG*cg) gt 1) then /* bad ideal */
		    norms_G[i] := 0;
		    deg_G[i] := 0;
		end if;
	    end for;
	    
	    /* Final processing to see if this is good pair (a,b) */
	    
	    max_deg_F := Maximum(deg_F);
	    max_deg_G := Maximum(deg_G);
	    
	    max_pi_F := Maximum(norms_F);
	    max_pi_G := Maximum(norms_G);
	    
	    delete(deg_F);
	    delete(deg_G);
	    delete(norms_F);
	    delete(norms_G);
	    
	    if (max_deg_F eq 1) and (max_deg_G eq 1) then /* found pair contains degree one ideals only */
		if (max_pi_F lt new_B) and (max_pi_G lt new_B) then
		    if (pi lt FB[1][#FB[1]]) then  /* unknown log in FB, so need to avoid loops */

			check_known := true;
			
			for i := 1 to #FFab do
			    if not ((nr eq 1) and (Id eq (FFab[i][1]))) then
				pj := Integers() ! Norm(FFab[i][1]);
				if (GCD(pj, cf*IF) eq 1) then  /* otherwise ideal is bad and we know it */
				    rj := find_root(FFab[i][1], pj, F);
				    ind_ideal := find_index_in_V(FB, pj, rj, 1, cf);
				    if not ((V[ind_ideal] ne 0) or (CW[ind_ideal] gt 4)) then /* otherwise dlog is really zero */
					check_known := false;
					break;
				    end if;
				end if;
			    end if;
			end for;
			
			for i := 1 to #FGab do
			    if not ((nr eq 2) and (Id eq (FGab[i][1]))) then
				pj := Integers() ! Norm(FGab[i][1]);
				if (GCD(pj, cg*IG) eq 1) then  /* otherwise ideal is bad and we know it */
				    rj := find_root(FGab[i][1], pj, G);
				    ind_ideal := find_index_in_V(FB, pj, rj, 2, cg);
				    if not ((V[ind_ideal] ne 0) or (CW[ind_ideal] gt 4)) then /* otherwise dlog is really zero */
					check_known := false;
					break;
				    end if;
				end if;
			    end if;
			end for;
			
			if (check_known) then
			    good_pair_found := true;
			    break;
			end if;
			
		    else
			
			good_pair_found := true;
			break;
			
		    end if;
		end if;
	    end if;
	    
	end for;
	
	num_pairs +:= 2;
	
    end while;
    
    delete(FPol);
    delete(GPol);
    delete(Fpolq);
    delete(Gpolq);
    
    return a, b;
    
end function;

function special_q_descent_log(Id, data_DLOGS, nr)
    
    /* special-q descent of ideal Id of degree one */
    
    normId := Integers() ! Norm(Id);
    
    FB := data_DLOGS[1];
    V := data_DLOGS[2];
    ell := data_DLOGS[5][5];
    modulus := data_DLOGS[5][4];
    
    if (nr eq 1) then
	num_field := data_DLOGS[3][5];
	max_ord := data_DLOGS[3][6];
	I := data_DLOGS[3][8];
	this_c := data_DLOGS[3][3];
	
	other_field := data_DLOGS[4][5];
	other_ord := data_DLOGS[4][6];
	other_c := data_DLOGS[4][3];
	
	bad_ideals := data_DLOGS[3][12];
	bad_ideals_index := data_DLOGS[3][13];
	
	offset := 0;
	
	this_index_schirok := data_DLOGS[3][9];
	this_nrschirok := data_DLOGS[3][10];
	this_schirokexp := data_DLOGS[3][11];
	
	other_index_schirok := data_DLOGS[4][9];
	other_nrschirok := data_DLOGS[4][10];
	other_schirokexp := data_DLOGS[4][11];
	
	this_log_c := 0;
	other_log_c := 0;
	
	if ((this_c ne 1) and (other_c ne 1)) then
	    this_log_c := V[#V-1];
	    other_log_c := V[#V];
	end if;
	
	if ((this_c eq 1) and (other_c ne 1)) then
	    other_log_c := V[#V];
	end if;
	
	if ((this_c ne 1) and (other_c eq 1)) then
	    this_log_c := V[#V];
	end if;
	
	other_nr := 2;
	this_nr := 1;
	
    end if;
    
    if (nr eq 2) then
	num_field := data_DLOGS[4][5];
	max_ord := data_DLOGS[4][6];
	I := data_DLOGS[4][8];
	this_c := data_DLOGS[4][3];
	
	other_field := data_DLOGS[3][5];
	other_ord := data_DLOGS[3][6];
	other_c := data_DLOGS[3][3];
	
	bad_ideals := data_DLOGS[4][12];
	bad_ideals_index := data_DLOGS[4][13];
	
	offset := #FB[2];
	
	this_index_schirok := data_DLOGS[4][9];
	this_nrschirok := data_DLOGS[4][10];
	this_schirokexp := data_DLOGS[4][11];
	
	other_index_schirok := data_DLOGS[3][9];
	other_nrschirok := data_DLOGS[3][10];
	other_schirokexp := data_DLOGS[3][11];
	
	this_log_c := 0;
	other_log_c := 0;
	
	if ((this_c ne 1) and (other_c ne 1)) then
	    this_log_c := V[#V];
	    other_log_c := V[#V-1];
	end if;
	
	if ((this_c eq 1) and (other_c ne 1)) then
	    other_log_c := V[#V];
	end if;
	
	if ((this_c ne 1) and (other_c eq 1)) then
	    this_log_c := V[#V];
	end if;
	
	other_nr := 1;
	this_nr := 2;
	
    end if;

    if (Degree(Id) gt 1) or (GCD(normId, I*this_c) gt 1) then 
	
	/* only possible for bad ideals, see if this is the case */
	
	if (GCD(normId, I*this_c) gt 1) then /* bad ideal found */ 
	    ind_pi := Index(bad_ideals, Id);
	    ind_log := V[bad_ideals_index[ind_pi]];
	    return ind_log;
	else
	    "Bad ideal given by ", Id;
	    error "special_q_descent_log can only handle degree 1 prime ideals or divisors of index/leading coefficient";
	end if;
	
    else  /* here we know ideal has degree 1 and is not bad ideal */

	/* first easy case, if log of ideal is already known */
	 
	pi := normId;
	ind_log := 0;
	
	if (pi le FB[1][#FB[1]]) then
	    r := find_root(Id, pi, num_field);
	    ind_ideal := find_index_in_V(FB, pi, r, nr, this_c);
	    
	    if (V[ind_ideal] ne 0) then
		return V[ind_ideal];
	    else
		if (data_DLOGS[6][ind_ideal] gt 4) then  /* it seems that this entry really is zero */
		    return 0;
		end if;
	    end if;
	end if;
	
	mul_id_inv := 1;

	if (ind_log eq 0) then  /* really need to find new relation now */

	    /* getting ideal in the normal representation (p, r - F.1) */

	    Zell2 := PolynomialRing(Integers(ell^2));
	    r := find_root(Id, pi, num_field);
	    
	    /* doing special-q lattice sieve to find good pair (a,b) */
	    
	    if (pi le FB[1][#FB[1]]) then  /* in special case that log of FB element is not known */
		
		vprintf FFLog, 2: "\nUnknown log of factorbase ideal (%o, %o - x%o)", pi, r, nr;
		new_B := FB[1][#FB[1]];
		
	    else
		nu := special_q_power(Degree(modulus));
		new_B := Round(pi^nu);
		new_B := Maximum(new_B, FB[1][#FB[1]]);
	    end if;

	    t_start := Cputime();
	    vprintf FFLog, 1: "\nStarted special-q lattice sieve for ideal (%o, %o - x%o) with bound %o\n", pi, r, nr, new_B;
	    a, b := special_q_lattice_sieve(Id, pi, r, new_B, data_DLOGS, nr);
	    vprintf FFLog, 1: "Finished special-q lattice sieve for ideal (%o, %o - x%o) with bound %o in time %o\n", pi, r, nr, new_B, Cputime(t_start);

	    /* log(Id) equals sum of logs other field ids + schirok maps  */
	    /* - logs this field ids - schirok maps - log this_c + log other_c */
	    
	    /* other field */
	    
	    /* Schirokauer maps */
	    
	    if (other_nrschirok gt 0) then
		Zell2zother<zother> := quo<Zell2 | Zell2 ! DefiningPolynomial(other_field)>;
		rs := (other_c*a - b*zother)^other_schirokexp - 1;
		maps := [Integers() ! (x div ell) : x in Coefficients(rs)];
		for i := 1 to Minimum(other_nrschirok, #maps) do
		    ind_log +:= maps[i]*V[other_index_schirok+i-1];
		end for;
	    end if;
	     
	    /* other ideals in factorisation of other field get a + */
	    
	    facs_2 := Factorisation((a*other_c - b*other_field.1)*other_ord);
	    
	    for i := 1 to #facs_2 do
		id_log := special_q_descent_log(facs_2[i][1], data_DLOGS, other_nr);
		ind_log +:= facs_2[i][2]*id_log;
	    end for;
	    
	    delete(facs_2);
	    
	    /* taking care of lc */
	    
	    ind_log +:= other_log_c;
	    
	    /* this field */
	    
	    /* Schirokauer maps */

	    if (this_nrschirok gt 0) then
		Zell2zother<zthis> := quo<Zell2 | Zell2 ! DefiningPolynomial(num_field)>;
		rs := (this_c*a - b*zthis)^this_schirokexp - 1;
		maps := [Integers() ! (x div ell) : x in Coefficients(rs)];
		for i := 1 to Minimum(this_nrschirok, #maps) do
		    ind_log -:= maps[i]*V[this_index_schirok+i-1];
		end for;
	    end if;

	    /* other ideals in this field, except for the ideal Id */
	    
	    mul_id := 0;
	    
	    facs_1 := Factorisation((a*this_c - b*num_field.1)*max_ord);
	    
	    for i := 1 to #facs_1 do
		if (facs_1[i][1] ne Id) then
		    id_log := special_q_descent_log(facs_1[i][1], data_DLOGS, this_nr);
		    ind_log -:= facs_1[i][2]*id_log;
		else
		    mul_id := facs_1[i][2];
		end if;
	    end for;

	    delete(facs_1);
	    
	    /* taking care of lc */
	    
	    ind_log -:= this_log_c;

	    Zell := Integers(ell);
	    mul_id_inv := (Zell ! mul_id)^(-1);

	    dlog_check := (Integers() ! (ind_log*mul_id_inv)) mod ell;

	    return (Integers() ! (ind_log*mul_id_inv)) mod ell;
	    
	end if;
    end if;
    
    return -1;
    
end function;

function indiv_dlog(gg, smooth_gen, dlog_gen, data_DLOGS)

    Fpn := Parent(gg);
    p := Characteristic(Fpn);
    n := Degree(Fpn);

    modulus := data_DLOGS[5][4];
    Fpz := Parent(modulus);
    
    F := data_DLOGS[3][5];
    OF := data_DLOGS[3][6];
    IF := data_DLOGS[3][8];
    cF := data_DLOGS[3][3];

    cG := data_DLOGS[4][3];
    
    bad_ideals_F := data_DLOGS[3][12];
    bad_ideals_index_F := data_DLOGS[3][13];
    
    index_schirokF := data_DLOGS[3][9];
    nr_schirokF := data_DLOGS[3][10];
    schirokexpF := data_DLOGS[3][11];

    FB := data_DLOGS[1];
    V := data_DLOGS[2];
    
    ell := data_DLOGS[5][5];
    
    Zell2 := PolynomialRing(Integers(ell^2));
    Zell2zF<zF> := quo<Zell2 | Zell2 ! DefiningPolynomial(F)>;

    Ab, mF, mG := select_nfs_bounds(p, n);
    
    /* choosing starting bound for the descent */
    
    B := Round(mF^smooth_combo_power(n));
    
    /* First finding good combination of smooth_gen^j*gg^i */
    
    t_start := Cputime();
    vprintf FFLog, 1: "\nStarted finding %o-smooth power of element\n", B;
    pow_gg, pow_smooth, num, denom := find_smooth_combo(gg, smooth_gen, FB[1], B, F, modulus);
    vprintf FFLog, 1: "Finished finding %o-smooth power of element in time %o\n", B, Cputime(t_start);
        
    /* Log of numerator */
    
    log_num := 0;

    /* Doing Schirokauer maps first */

    if (nr_schirokF gt 0) then
	rs := (Zell2zF ! Eltseq(num))^schirokexpF - 1;
	maps := [Integers() ! (x div ell) : x in Coefficients(rs)];
	for j := 1 to Minimum(#maps, nr_schirokF) do
	    log_num +:= maps[j]*V[index_schirokF + j - 1];
	end for;
    end if;

    vprintf FFLog, 2: "\nNumerator = %o\n", num;
    vprintf FFLog, 2: "Factorisation of norm of numerator = %o\n", Factorisation(Integers() ! Norm(num));
    fac_num := Factorisation(num*OF);
    for i := 1 to #fac_num do
	log_num +:= fac_num[i][2]*special_q_descent_log(fac_num[i][1], data_DLOGS, 1);
    end for;

    /* Log of denominator */
        
    log_denom := 0;
    
    /* Doing Schirokauer maps first */
    
    if (nr_schirokF gt 0) then
	rs := (Zell2zF ! Eltseq(denom))^schirokexpF - 1;
	maps := [Integers() ! (x div ell) : x in Coefficients(rs)];
	for j := 1 to Minimum(#maps, nr_schirokF) do
	    log_denom +:= maps[j]*V[index_schirokF + j - 1];
	end for;
    end if;

    vprintf FFLog, 2: "\nDenominator = %o\n", denom;
    vprintf FFLog, 2: "Factorisation of norm of denominator = %o\n", Factorisation(Integers() ! Norm(denom));
    fac_denom := Factorisation(denom*OF);
    for i := 1 to #fac_denom do
	log_denom +:= fac_denom[i][2]*special_q_descent_log(fac_denom[i][1], data_DLOGS, 1);
    end for;

    /* Final combination of all parts involved */
    
    Zell := Integers(ell);
    ind_log := (log_num - log_denom);  
    final_log := Integers() ! ((ind_log - pow_smooth*dlog_gen)*(Zell ! pow_gg)^(-1)); 
    
    return final_log;

end function;

procedure set_dlog_data(~Fq)
    
    p := Characteristic(Fq);
    n := Degree(Fq);
    q := p^n;
    
    if (n gt 4) then
	error "Higher degree sieving not yet implemented";
    end if;
    
    /* Find polynomials here */
    
    f, g := construct_polys(p,n);
    Zxy<x,y> := PolynomialRing(Integers(),2);
    FPol := &+[ Coefficient(f,i)*x^i*y^(Degree(f)-i) : i in [0..Degree(f)]];
    GPol := &+[ Coefficient(g,i)*x^i*y^(Degree(g)-i) : i in [0..Degree(g)]];
    
    /* making monic versions of f and g to get transformed number fields */
    
    cf := LeadingCoefficient(f);
    cg := LeadingCoefficient(g);
    
    fmon := cf^(Degree(f)-1)*f;
    gmon := cg^(Degree(g)-1)*g;
    
    fmon := Parent(f) ! [ (Coefficient(fmon, i) div cf^i) : i in [0..Degree(fmon)] ];
    gmon := Parent(g) ! [ (Coefficient(gmon, i) div cg^i) : i in [0..Degree(gmon)] ];
    
    /* f is always monic due to the construction */
    /* set f_fac to be one of factors of precise degree n */
    
    Fpz := PolynomialRing(GF(p)); z := Fpz.1;
    Facs := Factorisation(GCD(Fpz ! f, Fpz ! g));
    modulus := Fpz ! 0;
    
    for i := 1 to #Facs do
	modulus := Facs[i][1];
	if (Degree(modulus) eq n) then
	    break;
	end if;
    end for;
    
    Fpn := ext<GF(p) | modulus>;
    
    vprintf FFLog, 1: "Modulus equals %o\n", modulus;
    
    /* The number fields */
    
    F<v> := NumberField(fmon);
    OF := MaximalOrder(F);
    OFE := EquationOrder(F);
    IF := Index(OF,OFE);
    rl, cp := Signature(F);
    nrschirokF := rl+cp-1;
    
    G<w> := NumberField(gmon);
    OG := MaximalOrder(G);
    OGE := EquationOrder(G);
    IG := Index(OG,OGE);
    rl, cp := Signature(G);
    nrschirokG := rl+cp-1;
    
    vprintf FFLog, 1: "Sieve polynomial side 1 = %o\n", FPol;
    vprintf FFLog, 1: "Number field F defined by = %o\n", fmon;
    vprintf FFLog, 1: "Number of Schirokauer maps for F = %o\n", nrschirokF;
    vprintf FFLog, 2: "Index of equation order in max order for F = %o\n", IF;
    
    if (IF gt 1) then
	vprintf FFLog, 2: "Will need to fix up index divisors in side 1\n";
    end if;
    if (cf ne 1) then
	vprintf FFLog, 2: "Will need to fix up lc divisors in side 1\n";
    end if;
    
    vprintf FFLog, 1: "\nSieve polynomial side 2 = %o\n", GPol;
    vprintf FFLog, 1: "Number field G = %o\n", gmon;
    vprintf FFLog, 1: "Number of Schirokauer maps for G = %o\n", nrschirokG;
    vprintf FFLog, 2: "Index of equation order in max order for G = %o\n", IG;
    
    if (IG gt 1) then
	vprintf FFLog, 2: "Will need to fix up index divisors in side 2\n";
    end if;
    if (cg gt 1) then
	vprintf FFLog, 2: "Will need to fix up lc divisors in side 2\n";
    end if;
    
    /* Selecting good bounds */
    
    Ab, mF, mG := select_nfs_bounds(p, n);
    
    /* seeing how many variables we will have approx */

    tot_vars := approx_size_of_FB(fmon, mF, gmon, mG);
    
    /* Getting hard part of DLOG out */
    
    ell, schirokexpF, schirokexpG := get_hard_part_data(p, n, fmon, gmon);
    
    vprintf FFLog, 1: "\nComputing modulo large factor of p^n-1 = %o\n", ell;
    
    /* Precomputing logs of FB elements */

    num_rel := Round(1.3*tot_vars);
    if (n eq 3) then
	num_rel := Round(1.7*tot_vars);
    end if;
    
    sieve_ps := [mF, mG, Ab, 0, 0, mF+1, mG+1, 13, 13, 0, num_rel, ell, nrschirokF, schirokexpF, nrschirokG, schirokexpG];
    t_start := Cputime();
    vprintf FFLog, 1: "\nStarted sieving ... \n";
    M, FB := InternalSieveDLOG(FPol, GPol, sieve_ps);	
    vprintf FFLog, 1: "Finished sieving in time %o \n", Cputime(t_start);
    vprintf FFLog, 1: "Collected %o relations amongst %o unknowns\n", NumberOfRows(M), NumberOfColumns(M);
    
    /* Remembering which columns refer to schirokauer maps */
    
    index_schirokF := NumberOfColumns(M) - nrschirokF - nrschirokG + 1;
    index_schirokG := index_schirokF + nrschirokF;
    
    bad_ideals_F := [];
    bad_ideals_F_index := [];
    if ((IF gt 1) or (cf ne 1)) then
	t_start := Cputime();
	vprintf FFLog, 2: "\nStarted fixing up index/lc divisors in F\n";
	fix_up_index_lc_divisors(~M, FB, [* F, OF, IF, cf *], 1, ~bad_ideals_F, ~bad_ideals_F_index);
	vprintf FFLog, 2: "Finished fixing up index/lc divisors in F in time %o \n", Cputime(t_start);
    end if;
    
    bad_ideals_G := [];
    bad_ideals_G_index := [];
    if ((IG gt 1) or (cg ne 1)) then
	t_start := Cputime();
	vprintf FFLog, 2: "\nStarted fixing up index/lc divisors in G\n";
	fix_up_index_lc_divisors(~M, FB, [* G, OG, IG, cg *], 2, ~bad_ideals_G, ~bad_ideals_G_index);
	vprintf FFLog, 2: "Finished fixing up index/lc divisors in G in time %o \n", Cputime(t_start);
    end if;
    
    /*  Checking if all relations are OK */
    
    if (DEBUG_NFS_DLOG) then
	pars := [index_schirokF, nrschirokF, schirokexpF, index_schirokG, nrschirokG, schirokexpG];
	num_field_info := [* F, OF, IF, cf, G, OG, IG, cg *];
	bad_ideal_info := [* bad_ideals_F, bad_ideals_F_index, bad_ideals_G, bad_ideals_G_index *];
	print "Going in check relations";
	MM := check_relations(ell, M, FB, num_field_info, bad_ideal_info, pars);
	if (M eq MM) then
	    print "Check relations passed without problems";
	end if;
    end if;
    
    /* adding columns for the leading coefficients of f and g if necessary */
    
    add_lc_cols(~M, cf, cg);
    
    /* removing all columns that have weight one, necessary to restrict null space */
    t_start := Cputime();
    vprintf FFLog, 1: "\nStarted cleaning up matrix \n";
    clean_matrix(~M, ~FB);
    vprintf FFLog, 1: "Finished cleaning up matrix in time %o \n", Cputime(t_start);
    
    t_start := Cputime();
    vprintf FFLog, 1: "\nStarted finding element in kernel ... \n";
    V := Eltseq(ModularSolution(M, ell));
    vprintf FFLog, 1: "Finished computing element in kernel in time %o \n", Cputime(t_start);
    // vprintf FFLog, 2: "Virtual dlogs are given by (zero element means undetermined) \n %o \n\n", V;
    
    CW := ColumnWeights(M);
    nbr_dlogs_unknown := &+[ ((V[i] eq 0) and (CW[i] lt 2)) select 1 else 0 : i in [1..#V]];
    vprintf FFLog, 1: "Number of dlogs not determined = %o \n", nbr_dlogs_unknown;
    
    delete(M);
    
    /* Building data structure with info to compute indiv dlogs */
    /* Saving this datastructure will allow more indiv dlogs to be computed */
    /* without redoing all the sieving and linear algebra */
    
    data_F := [* f, FPol, cf, fmon, F, OF, OFE, IF, index_schirokF, nrschirokF, schirokexpF, bad_ideals_F, bad_ideals_F_index *];
    data_G := [* g, GPol, cg, gmon, G, OG, OGE, IG, index_schirokG, nrschirokG, schirokexpG, bad_ideals_G, bad_ideals_G_index *];
    data_fin := [* p, n, Fpn, modulus, ell *];
    data_DLOGS := [* FB, V, data_F, data_G, data_fin, CW *]; 
    
    /* Checking the results, i.e. verifying dlogs of reduced elements */
    
    if (DEBUG_NFS_DLOG) then
	print "Check results gives = ", check_results_simple(data_DLOGS);
    end if;
    
    Fq`NFS_dlog_data := data_DLOGS;
    
end procedure;


function NFS_dlog(gel, hel)   /* computes log(g,h) */

    vprintf FFLog, 1: "\nIn NFS discrete log routine\n";
    
    /* quick test */

    ord_gel := Order(gel);
    
    if ((ord_gel mod Order(hel)) ne 0) then
	return -1;
    end if;

    if (Parent(gel) ne Parent(hel)) then
	error "Both input elements should be part of same finite field!";
    end if;
    
    Facs := Factorisation (ord_gel);
    if (Maximum( [Facs[i][1] : i in [1..#Facs]] ) lt xoverPH()) then
	return Log(gel, hel);
    else

	Fq := Parent(gel);
	
	AddAttribute(FldFin, "NFS_dlog_data");
	if (not (assigned  Fq`NFS_dlog_data)) then
	    set_dlog_data(~Fq);
	end if;
	data_DLOGS := Fq`NFS_dlog_data;

	/* unpacking some of the data in data_DLOGS */

	Fpn := data_DLOGS[5][3];
	p := Characteristic(Fpn);
	n := Degree(Fpn);
	modulus := data_DLOGS[5][4];
	ell := data_DLOGS[5][5];
	z := Parent(modulus).1;
	cf := data_DLOGS[3][3];
	
	/* Starting to do individual dlogs */
	
	/* Search for a smooth generator, first looking for an easy match from relations */
	/* if none found, which is unlikely, then generate one explicitly */
	
	a, b, dlog_gen := select_smooth_gen(data_DLOGS);
	smooth_gen := (Fpn ! ((cf*a - b*z) mod modulus))/cf;
	
	/* mapping elements g and h over to representation we use */
	
	iso_root := iso_image_gen(Fq, Fpn);
	
	gg := iso_rep_apply(gel, iso_root);
	hh := iso_rep_apply(hel, iso_root);
	
	/* Computing individual logs of gg and hh wrt smooth_gen */
	
	t_start := Cputime();
	vprintf FFLog, 1: "\nStarted computing dlog of g ... \n";
	gg_log := indiv_dlog(gg, smooth_gen, dlog_gen, data_DLOGS);
	vprintf FFLog, 1: "\nFinished computing dlog of g in time %o \n", Cputime(t_start);
	
	t_start := Cputime();
	vprintf FFLog, 1: "\nStarted computing dlog of h ... \n";
	hh_log := indiv_dlog(hh, smooth_gen, dlog_gen, data_DLOGS);
	vprintf FFLog, 1: "\nFinished computing dlog of h in time %o \n", Cputime(t_start);
	
	Zell := Integers(ell);
	gg_log_inv := (Zell ! gg_log)^(-1);
	log_mod_ell := (Integers() ! (gg_log_inv*hh_log)) mod ell;

	/* Test to see if this is correct */
	
	if ( (gel^(log_mod_ell)/hel)^((p^n - 1) div ell) eq 1 ) then
	    vprintf FFLog, 1: "\nModulo l information of dlog is correct \n";
	end if;
	
	/* Getting easy part of DLOG via Pohlig-Hellman */
	
	t_start := Cputime();
	vprintf FFLog, 1: "\nStarted Pohlig-Hellman to get easy part out ... \n";
	
	g_perp_ell := gel^(ell);
	h_perp_ell := hel^(ell);
	
	log_perp_ell := PohligHellman(g_perp_ell, h_perp_ell);
	
	if (log_perp_ell eq -1) then
	    return -1;
	end if;
	
	/* Combining both using CRT */
	
	final_log := 0;
	if (ell gt 1) then
	    final_log := CRT([log_mod_ell, log_perp_ell], [ell, (p^n-1) div ell]) mod (p^n - 1); 
	else
	    final_log := log_perp_ell;
	end if;
	
	vprintf FFLog, 1: "\nFinished Pohlig-Hellman in time %o \n", Cputime(t_start);

	if (gel^final_log ne hel) then
	    error "NFS_dlog computation made error: final dlog incorrect";
	end if;
	
	return final_log mod ord_gel;
    end if;

    return -1;
    
end function;
