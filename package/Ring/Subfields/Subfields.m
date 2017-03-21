freeze;

forward NextSubfields, SUBSET, SubfieldFromBlock;

import "GalSubfield.m" : GetBlock, BlockComposite, FindPrime, BlockFromPrimitiveElement, PossibleBlockSizes;
import "../GaloisGrp/GalRelRest.m" : RealBasis;

declare attributes FldAlg : SubfieldLattice;
declare attributes FldFun : SubfieldLattice;

Debug := false;
SubGraphLimit := 100;

/*
OptAlg is used to select this method only if it is the optimal algorithm
for computing Subfields. If OptAlg is true then after the degrees of factors
have been checked and found to be too large then the function will return 
so that the old Subfields algorithm can be used. OptAlg should be false to use
this algorithm regardless, e.g. when GeneratingSubfields only are required
OptAlg := true will only have effect when the coefficient field of F is the
rational field (the only case there is a reliable possibly faster algorithm)
*/
/*
Proof levels are 
0 : cheapest checks only (1 and 2)
1 : More checks (3, 4 also)
2 : All Checks (5 also)
*/
function GeneratingSubfieldsFunc(F, l : OptAlg := false, Proof := 1)
/*
This function implements the computation of the fields L_i as in 
van Hoeij and Klueners "Generating Subfields" Theorem 2.1
There are two "methods" implemented.
The second uses F as F_tilde and the computations are somewhat straightforward
The first uses local methods (see van Hoej and Klueners, Novocin ISSAC 2011)
*/
    if Debug then
        "GeneratingSubfieldsFunc";
    end if;

    vprint Subfields,1:"Start GeneratingSubfieldsFunc";
    // Get generating subfields already stored in the lattice
    S := InternalSubfieldLatticeGetGeneratingSubfields(l);

    n := Degree(F);
    if n eq 1 then
	return [];
    end if;

    if l`GeneratingComplete then 
	return S;
    end if;


    if n lt 50 and Proof ne 2 then
	//Proof := 2;
    end if;
//Proof := 2;
    f := DefiningPolynomial(F);

    PF := PolynomialRing(F);
    if CoefficientField(F) cmpeq RationalField() then 
//"IN p-ADIC FACTORIZATION BIT\n\n";

        if OptAlg and (Degree(f) le 30) then
          vprint Subfields,1:"Degree <= 30. Not using this algorithm.";
          return false, _;
        end if;

// collect cycle type information for later use.
        cycle_data := [];
        p := Degree(F)^2;
        p_lim := Degree(F);
	primes := [* *];
	att_primes := 0;
	min_length := 2*n;
	min_98_length := 2*n;
        repeat 
           p_lim := p_lim + Degree(F);
           repeat
             // p := NextPrime(p);
	    FindPrime(p, l : full := false);
	    p := l`Prime[1];
	    att_primes +:= 1;
              if IsCoercible(PolynomialRing(GF(p)), f) then
                 red := PolynomialRing(GF(p))!f;
                 if Degree(red) eq Degree(f) then
                    fac := Factorization(red);
                    if {a[2] : a in fac} eq {1} then
		       degs := [Degree(a[1]) : a in fac];
                       Append(~cycle_data,<p,degs>);
		       if 1 in degs then
			   Append(~primes, <p, fac>);
			   if #fac lt min_length then
			    min_length := #fac;
			    end if;
			end if;
			if #fac lt min_98_length then
			    min_98_length := #fac;
			end if;
		    else
			assert false;
                    end if;
		 else 
		    assert false;
                 end if;
              end if;
           until #cycle_data gt p_lim;
           poss_bl_s := PossibleBlockSizes({a[2] : a in cycle_data});
           if #poss_bl_s eq 0 then
             vprint Subfields,1:"No subfields by shape test";
             return S;
           end if;

        until #primes gt 0;
 
        vprint Subfields,3:"Cycle types found",{a[2] : a in cycle_data};
        vprint Subfields,1:"Shape test forces blocks to be of size",poss_bl_s;
        gal_lower_bound := InternalDivisorOfGroupOrder({a[2] : a in cycle_data}); 
        vprint Subfields,2:"Order of Galois group is multiple of",gal_lower_bound;

	cput := Cputime();
	d := func<|LCM([Denominator(c) : c in Coefficients(f)])>();
	lc := LeadingCoefficient(f);
	f *:= d;

	cycle_sizes := {LCM(x[2]) : x in cycle_data};
//"Cycle sizes after Stephan's cycle checks", cycle_sizes;
 
	// some estimate from size of polynomial coeffs
	a := Integers()!Norm(Vector(Coefficients(f)));
	blocks := {};

	really_really_large := 10^(n);
	really_large := 10^(n/2);
	fairly_large := 10^(n/4);
	large := 10^Ceiling(Sqrt(n));
	medium := 10^Ceiling(Root(n, 4));

	cycle_sub := 3;

	function use_this_alg(min_length, min_98_length, cycle_sizes, a)
//min_length, min_98_length, Maximum(cycle_sizes), a;
	    cycle_size := Maximum(cycle_sizes);
	    // min_length initialised to 2n and might not be really set yet
	    if min_length ge n and min_98_length gt 5 then
	    // Probable Galois extension : best to stay here
	    // or haven't tried enough primes to reduce
		return true;
	    elif min_length/min_98_length ge 3 then
	    // lengths are not close, short for K compared to KvH
		// unless cycle_size or coeffs are particularly small
		//cycle_size will be a degree of a p-adic splitting field K would use
		// limit it
		if cycle_size lt 60 and cycle_size ge n/10 and (cycle_size gt n/2 or a gt n^(3/2)) then
		    return false;
		end if;
	    elif cycle_size*a/min_98_length gt n^(n/2) then 
		return false;
	    end if;
	    return true;
	end function;

	poss_gal_ext := true;
/*
rep_loop := Cputime();
	repeat
	//"Need another prime";
	    // Want a prime with a short factorization
	    // If the degrees of the factorizations are all the same then the 
	    // field is Galois and the factorization with one linear factor
	    // will contain only linear factors
	    // It can take a while to find a prime, is it worth searching for
	    // another?
	    // We look at the degrees of the factors. If they are not "small"
	    // then if OptAlg is true we exit this function and use the
	    // old subfields code
	    FindPrime(p, l : full := false, with_linear := not OptAlg);
	    p := l`Prime[1];
	    FF := GF(p);//l`Prime[3];
	    att_primes +:= 1;

	    ff := Polynomial(FF, f);
	    fact := Factorization(ff);
	    // If there are large degrees then there are long cycles in the
	    // Galois group. Therefore the Galois group has fewer subgroups and
	    // by the Galois correspondence the field has fewer subfields
	    // in which case the older algorithm is more efficient.
	    // If the degrees are small than there are short cycles in the 
	    // Galois group so it has more subgroups and the field has more
	    // subfields and the GeneratingSubfields algorithm is more 
	    // efficient
	    Include(~cycle_sizes, LCM([Degree(g[1]) : g in fact]));
	    vprint Subfields, 2 : p, LCM([Degree(g[1]) : g in fact]);
	    if false and OptAlg then
//Ceiling(&*[Degree(g[1]) : g in fact]/n);
		if Maximum([Degree(g[1]) : g in fact]) in [Floor(n/5) + 1 .. Ceiling(n/3)] then //and &*[Degree(g[1]) : g in fact] lt n^3 then
//"OLD";
		    //return false;
		end if;
	    end if;
	    has_linear := exists(g){g : g in fact | Degree(g[1]) eq 1};
	    // squarefree, has a linear factor, separable, 
//p, has_linear;
	    if has_linear and &and[ff[2] eq 1 : ff in fact] and &and[Derivative(ff[1]) ne 0 : ff in fact] then 
		Append(~primes, <p, fact>);
		if #fact lt min_length then
		    min_length := #fact;
		end if;
	    end if;
	    if #fact lt min_98_length then
		min_98_length := #fact;
	    end if;
	    poss_gal_ext and:= #{Degree(ff[1]) : ff in fact} eq 1;
	// enough primes considered OR a splitting which means we have a
	// Galois extension and won't get a better prime
	// A splitting doesn't always mean a Galois extension
	// Need to make sure there is at least one prime!

	// If we are looking for the optimal algorithm and we haven't got a prime
	// after ? attempts we should check which algorithm we might want to use
	// since if it is not this one we should give up sooner
	    if not false and OptAlg and att_primes ge 3 then
//"Cycle sizes after 3 attempted primes", cycle_sizes;
		new_cycle_size := Maximum(cycle_sizes);
		if not assigned cycle_size then
		    cycle_size := new_cycle_size;
		end if;
		if new_cycle_size gt cycle_size then
		    cycle_sub := att_primes - 1;
		    cycle_size := new_cycle_size;
		end if;
		at := a^(1/((att_primes - cycle_sub)/20 + 1));
		if not use_this_alg(min_length, min_98_length, cycle_sizes, a) then
		    // need a prime with full info for the lattice stuff 
		    // at the end
		    FindPrime(p - 1, l);
                    vprint Subfields,1:"GeneratingSufieldsFunc: Not using this algorithm!";
		    return false;
		end if;
//OptAlg, #primes, att_primes, at, cycle_sub, cycle_size;
	    end if;
	until (#primes gt n div 10 + 1 and att_primes ge 5);
"Cycle sizes after prime loop", cycle_sizes;
//Cputime(rep_loop);
//att_primes;

//#primes, att_primes;
*/

	if OptAlg then
	    if not use_this_alg(min_length, min_98_length, cycle_sizes, a) then
		// need a prime with full info for the lattice stuff 
		// at the end
		FindPrime(p - 1, l);
		return false;
	    end if;
/*
	    //min_length, n;
	    if true or not poss_gal_ext then

		elif false and min_98_length lt 8 then
		// Klueners algorithm unless cycle_size is particularly small
		    if cycle_size gt n/10 then
			return false;
		    end if;
		elif false and min_98_length gt 12 then
		// Klueners van Hoeij algorithm unless cycle_size is particularly
		// large or coefficients are particularly large.
		    if cycle_size*a gt n*10^(Sqrt(n)) then
			return false;
		    end if;
*/
/*
//cycle_size, n, a;
		//cycle_size, a, cycle_size*a, n, n^2;
		//a, cycle_size*n, a*cycle_size*n;
//		cycle_size le n/5; a gt really_large;
//		if cycle_size lt n/10 then use KvH
//[Ceiling(n/10) .. Ceiling(n/5)-1], [Ceiling(n/5) .. Ceiling(n/2)-1], [Ceiling(n/2) .. n-1];
//cycle_size in [Ceiling(n/2) .. n-1], a gt large;
		at := a/min_98_length;
		if (cycle_size in [Ceiling(n/10) .. Ceiling(n/5)-1] and a gt really_large) or
		    (cycle_size in [Ceiling(n/5) .. Ceiling(n/2)-1] and a gt fairly_large)  or
		    (cycle_size in [Ceiling(n/2) .. n-1] and a gt large) or
		    (cycle_size in [n .. 2*n-1] and a gt medium) or
		    cycle_size gt 2*n then
		//if cycle_size*a gt n^(2.5) and cycle_size gt n/5 then
		//if min_length gt 1/3*n then
		    return false;
		end if;
	    end if;
*/
//"New";

	end if;
	a_sq := a;
	a := Sqrt(a);
	a *:= n^2;
	a_sq *:= n^4;

//primes;
	p, fact := Explode([* t : t in primes | #t[2] eq min_length *][1]);
	FindPrime(p-1, l : with_linear := true);
	FF := GF(p);//l`Prime[3];
	Fact := func<|[ff[1] : ff in fact]>();
	//C, m := Completion(F, P);
	//fact := HenselLift(Polynomial(C, [m(c) : c in Coefficients(f)]), fact);
	mm := n div Minimum(PrimeDivisors(n));
	// where we are up to in the factorization - don't need to start again

        vprintf Subfields,1:"Choosing p = %o of type %o\n",p,[Degree(a) : a in Fact]; 

	fact_complete := 1;
	HP := HenselProcess(PolynomialRing(Integers())!f, Fact, 10);
	increase_precision_factor := 1;
	for i in [1 .. #Fact] do
	    if Degree(Fact[i]) eq 1 then
		II := i;
		break;
	    end if;
	end for;
	assert assigned II;
	f := Polynomial(CoefficientField(F), f);
	PFf := PF!f;
	fd := Derivative(f);
	fd_int := PolynomialRing(Integers())!fd;
	_, inv := XGCD(fd, f);
	// Get the \alpha^i/f'(\alpha) basis here once
	bas := func<|[(Parent(inv).1)^i * inv mod f : i in [0..n-1]]>();
	Fbas := func<|[Evaluate(x, F.1) : x in bas]>();

	function gcd_attempt_at_g_t(M)
	    r_tries := 0;
	    HH := func<|[F!Eltseq(M[k])[1 .. n] : k in [1 .. Nrows(M)]]>();
	    repeat
		x := &+[Random(-10, 10)*H : H in HH];
		if x in CoefficientField(F) then
		    continue;
		end if;
		assert Denominator(x) eq 1;
		xf := Polynomial(Parent(x), Eltseq(Numerator(x)));
		//g := gcd(f,  h(alpha) * f'(x) - h(x) * f'(alpha) ).
		df := Polynomial(Parent(x), Derivative(f));
		_g := Gcd(f, x*df - xf*Evaluate(df, F.1));
		r_tries +:= 1;
//Degree(_g), Nrows(M), n;
	    until (x notin CoefficientField(F) and (r_tries ge 5 or Degree(_g)*Nrows(M) eq n));
	    return Degree(_g)*Nrows(M) eq n select _g else false;
	end function;

	function check4(g_t)
	    return PFf mod g_t eq 0;
	end function;

	function check5(g_t, H)
	    //if &and[H[k] mod g_t ne H[k] mod Polynomial([-F.1, 1]) : k in [1 .. #h]] then
	    for hk in H do
	    // by checking on the elements from the basis of the 
	    // original LLLed lattice with large norm vectors removed
		hk_mod_f1 := PF!hk mod Polynomial(F, [-F.1, 1]);
		//if not func<|&and[Evaluate(PF!hk mod g_t, F!Eltseq(x)[1 .. n]) eq hk_mod_f1 : x in Rows(M_orig)]>() then
		// This won't make things much faster usually since we expect
		// all these to succeed so will have to test all evaluations
		// anyway!
		hk_mod_g_t := func<|PF!hk mod g_t>();
		//function check5()
		if hk_mod_g_t ne hk_mod_f1 then
		//for x in Rows(M_orig) do 
		    //if Evaluate(hk_mod_g_t, F!Eltseq(x)[1 .. n]) ne hk_mod_f1 then
		    return false;
		    //end if;
		//end for;
		end if;
		//return true;
		//end function;
		// This is cheaper without check5 as a function but with 
		// check5 as a function it shows how expensive this check
		// currently is
		//if not check5() then
		    //break i;
		//end if;
	    end for;
	    return true;
	end function;

	fda := 1/Evaluate(fd, F.1);
	//"Setup time", Cputime(cput);
	proof := Proof;
	while fact_complete le #Fact do
            if Debug or (GetVerbose("Subfields") ge 2) then
              "Hensel Lifting";
            end if;
	    for i in [fact_complete .. #Fact] do
		if i eq II then
		    fact_complete +:= 1;
		    continue;
		end if;

		fi := Fact[i];
                if (1 + Degree(fi)) gt Max(poss_bl_s) then
                    vprintf Subfields,2:"Factor %o of degree %o skiped by shape test.\n",i,Degree(fi);  
                    fact_complete +:= 1;
		    continue;
                end if; 


                vprintf Subfields,2:"Doing factor %o of degree %o\n",i,Degree(fi);
		d := Degree(fi);
		// g_cand must contain FI and fi as factors so will have
		// degree at least d + 1. If d + 1 is larger than the 
		// largest divisor of n the
		// subfield has to be the coefficient field
		if d + 1 gt mm then
		    fact_complete +:= 1;
		    continue;
		end if;

		/*
		If we have found a subfield L of prime index (so maximal)
		for which f_j | f_L, we also have f_1 | f_L so f_1 f_j | f_L
		L will have a block containing 1 and j, the subfield we are
		about to compute will also have a block containing 1 and j.
		If we intersect the blocks we get a field with a block 
		containing 1 and j which contains L but CANNOT contain F
		(since j is in the same block as 1), but L is maximal
		so we have a contradication. So the subfield we are about to 
		compute must be L again so we don't bother recomputing.
		See Klueners Pohst, Remark 2.4
		*/

		bl:=[x: x in blocks | i in x];
		bl:=[&+[Degree(Fact[j]): j in x]: x in bl | #x lt #Fact];  // Exclude trivial block system with only 1 block
 //		bl:=[x:x in bl |IsPrime(x)];
                bl := [x : x in bl | #[a : a in Divisors(x) | a in poss_bl_s] le 1]; 

	        if #bl gt 0 then
                    vprint Subfields,2:"Factor in minimal block. It will reproduce a known field.";  
		    //bl;
		    fact_complete +:= 1;
		    continue;
		end if;
		cput := Cputime();
		aa := increase_precision_factor*Ceiling(n/d*Log(p, 2^d*a*2^n));
//a, aa, p;
		fact := HenselLift(HP, aa);
		pa := p^aa;
vprint Subfields,2:"Working with p-adic precision", aa;
		P := PolynomialRing(Integers(pa));
		ChangeUniverse(~fact, P);
//fact;
		FI := fact[II];
		fi := fact[i];

		alpha_1 := -TrailingCoefficient(FI);
		Pbas := [P!x : x in bas];

		fP_der := P!fd;

		fi_int := PolynomialRing(Integers())!fi;
		Pfi_int := P!fi_int;
		PFI := P!FI;

//"using", P!fi_int, "and", P!FI;

		B := func<|[Eltseq(P1mod) cat [0 : i in [Degree(P1mod) + 2 .. d]] where 
			P1mod := Pbas[j] mod Pfi_int - Pbas[j] mod PFI
							: j in [1 .. n ]]>();
		M := Matrix(Integers(), n, d, B);
//"Bi:", M;
//M;
//a;
//"LLL", i;
		ll := Ceiling(Log(10, a));
		function LLL_with_removals(M, _a)
		    //return LLL(M, [pa : i in [1 .. d]], RealField()!_a);
		    M := func<|LLL(M)>();
		    N := Orthogonalize(Matrix(RealField(100 + n + ll), M));
		    len := Nrows(N);
		    while Norm(N[len]) gt _a do
			len -:= 1;
		    end while;
		    M := RowSubmatrix(M, len);
//"M, L : ", M, L;
//[Floor(Norm(x)) : x in Rows(Orthogonalize(Matrix(RealField(100 + n + ll), M)))];
//[Floor(Norm(x)) : x in Rows(Orthogonalize(Matrix(RealField(100 + n + ll), L)))], _a;
//M - L;
		    return M;
		end function;

		if true then
		    // MvH new ScalingProgram GradualLLLmodq code
//time 
                  vprint Subfields,2: "Calling LLL";
                  vtime Subfields,2: M := LLL(M, p, aa, a_sq);
		elif true then
		    // One coeff at a time
		    A := IdentityMatrix(Integers(), n);
		    for j in [1 .. d] do
			z := Vector([0 : i in [1 .. Ncols(A)]]);
			A1 := VerticalJoin(A, z);
			cs := ColumnSubmatrix(A, n)*ColumnSubmatrix(M, d - j + 1, 1);
			cs := Matrix([[x mod pa : x in Eltseq(r)] : r in Eltseq(cs)]);
			A := HorizontalJoin(A1, VerticalJoin(cs, Vector([pa])));
			time A := LLL_with_removals(A, a_sq);
		    end for;
		    M := A;
		else
		    // simple LLL all coeffs together
		    M := VerticalJoin(M, ScalarMatrix(d, pa));
//	    "M = ", M;
		    I := IdentityMatrix(Integers(), n);
		    I := VerticalJoin(I, ZeroMatrix(Integers(), d, n));
		    M := HorizontalJoin(I, M);
		    time M, L := LLL_with_removals(M, a_sq);
		end if;
		m := Nrows(M);
		C := 100000000;
		// Multiply last d columns
		D := DiagonalMatrix([1 : i in [1 .. n]] cat [C : i in [1 .. d]]);
		while not func<|&and[IsZero(M[i][j]) : i in [1 .. m], j in [n + 1 .. Ncols(M)]]>() do
		    M := M*D;
//"M :", M;
		    M := LLL_with_removals(M, a_sq);
		    m := Nrows(M);
//m;
		end while; 
		M_orig := M;
		if n mod m ne 0 then
		    break;
		end if;

		vprint Subfields,2: "Have L, time was", Cputime(cput);
		cput := Cputime();


		//h := func<|[&+[M[k, j]*Pbas[j] : j in [1..n]] : k in [1..m]]>();
		//H := func<|[&+[M[k, j]*bas[j] : j in [1..n]] : k in [1..m]]>();
		//function h_and_H()
		//H := [Universe(bas)|];
		h := func<|[P!(Polynomial(Eltseq(M[k])[1 .. n]) * inv) : k in [1 .. m]]>();
		H := func<|[F!Eltseq(M[k])[1 .. n] * fda : k in [1 .. m]]>();
		//h := func<|[P | Denominator(x)*Polynomial(Eltseq(x)) : x in H]>();
		//h;
		if false then 
		    h := [Universe(Pbas)|]; 
		    H := [Universe(Fbas)|]; 
		    for k := 1 to m do
			h[k] := 0; H[k] := 0;
			for j := 1 to n do
			    h[k] := func<|h[k] + M[k, j]*Pbas[j]>();
			    H[k] := func<|H[k] + M[k, j]*Fbas[j]>();
			end for;
		    end for;
		    h;
		end if;
		_H := H;
		//return h, H;
		//end function;
		//h, H := h_and_H();


		g := Universe(fact)!lc;
		gS := {};
		// T[k] could be incomplete, especially for larger k because of 
		// the continue
		T := [{Integers() | } : k in [1 .. #h]];
		T_lim := [1 : j in [1 .. #fact]]; //largest k for which j tested
		for j := 1 to #fact do
		//    if func<|&and[h[k] mod fact[j] eq h[k] mod FI : k in [1 .. #h]]>() then
		    for k := 1 to #h do
			if func<|h[k] mod fact[j] ne h[k] mod FI>() then
			    T_lim[j] := k;
			    continue j;
			end if;
			Include(~(T[k]), j);
		    end for;
		    g *:= fact[j];
//j;
		    Include(~gS, j);
		end for;
//gS;
		Include(~blocks, gS);
		
		//assert (n div m) eq (&+[Degree(fact[j]): j in gS]);
		if Degree(g) eq n then
                    vprint Subfields,2:"Factor results in trivial subfield";
		    fact_complete +:= 1;
		    continue;
		end if;
		vprint Subfields,2:"First block identified. Have g, time was", Cputime(cput);

//"g = ", g;
//Parent(g);
		//
		if proof ge 1 then

		if false then 
		    _g := gcd_attempt_at_g_t(M);
		end if;

		cput := Cputime();
//"M (acutually L):", M;
		M := Submatrix(M, 1, 1, m, n);
		Z := Integers();
		fd_alpha_eval := Evaluate(fd_int, alpha_1);
		one_over_fd_alpha_eval := 1/fd_alpha_eval;
		c := func<|[Evaluate(h[j], alpha_1) : j in [1 .. m]]>();
		//c := func<|[&+[M[j][i+1]*alpha_1^i*one_over_fd_alpha_eval : i in [0 .. n-1]] : j in [1 .. m]]>();
		M := HorizontalJoin(M, Matrix(Integers(), 1, func<|[C*(Z!cj) : cj in c]>()));
		M := VerticalJoin(M, Vector([0 : i in [1 .. n]] cat [C*pa]));
//"final new M", M, "DONE";

		M := func<|LLL(M)>();

		g_t := 0;
		gk := Coefficients(-g);
		M := HorizontalJoin(M, Matrix(m+1, 1, [0 : i in [1 .. m + 1]]));
		for k in [0 .. Degree(g)] do
		    Mk := VerticalJoin(M, Vector(Integers(), [0 : i in [1 .. n]] cat [C*(Z!gk[k+1]), 1]));
//"before LLL", Mk, "done";
		    //"g_t LLL time";
		    Mk := func<|LLL(Mk)>();
		    //Check 3
		    C_increase := 0;
//Mk;
		    V := func<|[v : v in Rows(Mk) | v[n+1] eq 0]>();
//Mk;
//V;
		    while not exists(v){v : v in V | Abs(v[n+2]) eq 1} and C_increase lt 4 do
			if false and exists(v){v : v in V | &and[IsCoercible(CoefficientRing(v), v[i]/v[n+2]) : i in [1 .. n]]} then
"SHOULD WE NEED TO NORMALIZE ANYMORE?";
			    v := v/v[n+2];
			    break;
			end if;
			MultiplyColumn(~M, C, n+1);
			MultiplyColumn(~Mk, C, n+1);
			//"More g_t LLL";
			Mk := func<|LLL(Mk)>();
//"new Mk", Mk;
			C_increase +:= 1;
			C *:= C;
			V := func<|[v : v in Rows(Mk) | v[n+1] eq 0]>();
		    end while;
		    if not assigned v then
			if not IsExport() then
			"ne FAIL CHECK 3", C_increase, increase_precision_factor;
			end if;

			if not false then
			_g := func< | gcd_attempt_at_g_t(M_orig)>();

			if _g cmpne false and Degree(_g)*Nrows(M_orig) eq n then
			    g_t := _g;
			    break k;
			else
			    Exclude(~blocks, gS);
			    if increase_precision_factor gt 1 then
				proof := 0;
			    end if;
			    delete g_t;
			    break k;
			end if;
			end if;
		    else 
			if v[n+2] eq -1 then
			    v *:= -1;
			end if;
			g_t +:= func<|&+[v[i]*Fbas[i] : i in [1 .. n]]*PF.1^k>();
		    end if;
		end for;
		//end if;

		//"Have g_t, time was", Cputime(cput);
		//Check 4
		if assigned g_t and not check4(g_t) then
		if not IsExport() then 
		"ne FAIL CHECK 4";
		end if;
		    Exclude(~blocks, gS);
		    break i;
		end if;

		//Check 5
		if proof ge 2 and assigned g_t then
		    if not check5(g_t, H) then
		    "FAIL CHECK 5";
			Exclude(~blocks, gS);
		    error "";
			    //return false;
			    break i;
		    end if;

		end if; //proof ge 2

		end if; //proof ge 1

		/*
		I think the "subfield polynomial" _g should be further up,
		just inside proof eq 1. This is an alternative way of computing 
		g_t?
		*/

		FII := Fact[II];
		//"Time for sub";
		//time L := func<|sub<F | Coefficients(g_t)>>();
		
		// If I have a g_t should I use it in preference to H?

		// Try to find a primitive element - a coeff of g_t should be one!
		// Compute a block from each coeff until find one that is 
		// primitive
		// Consider sums of coeffs if a primitive element has not been
		// found

		while not assigned elt do
		    if assigned g_t then
			H := Coefficients(g_t);
			for x in H/*Coefficients(g_t)*/ do
			    xf := Polynomial(FF, Eltseq(Numerator(x)));
			    B := {i : i in [1 .. #Fact] | xf mod FII eq xf mod Fact[i]};
			    if B eq gS then
				elt := x;
			//"Single coeff";
				break;
			    end if;
			end for;
		    else
			// something clever with T?
			// complete the T then compare to gS
			for k := 1 to #h do
			    for j := 1 to #Fact do
				hkFII := h[k] mod FI;
				// if not succeeded and not failed and tested ok
				if j notin T[k] and k gt T_lim[j] and func<|h[k] mod fact[j] eq hkFII>() then
				    Include(~(T[k]), j);
				end if;
			    end for;
			    if T[k] eq gS then
				elt := Numerator(H[k]);
				elt := H[k];
//"Primitive element by T comparison", k;
				break;
			    end if;
			end for;
		    end if;

		    if assigned elt then
			if true or assigned g_t then
			    break;
			else
			    delete elt;
			end if;
		    end if;

		    if not assigned g_t then
			// intersect some T_k to get gS
			t := T[1];
			k := 1;
			ind := [1];
			while k lt #h and t ne gS do 
			    tt := t meet T[k];
			    if tt ne t then
				Append(~ind, k);
				t := tt;
			    end if;
			    k +:= 1;
			end while;
			assert gS eq t;
			HH := H[ind];
			x := &+HH;
			xf := Polynomial(FF, Eltseq(Numerator(x)));
			B := {i : i in [1 .. #Fact] | xf mod FII eq xf mod Fact[i]};
			r_tries := 0;
			while B ne gS and r_tries lt 5 do
			    x := &+[Random(1, 10)*hh : hh in HH];
			    xf := Polynomial(FF, Eltseq(Numerator(x)));
			    B := {i : i in [1 .. #Fact] | xf mod FII eq xf mod Fact[i]};
			    r_tries +:= 1;
			end while;
			if B eq gS then
//"Primitive element by T comparison", ind;
			    elt := Numerator(x);
			    elt := x;
			    if true or assigned g_t then
				break;
			    else
				delete elt;
			    end if;
			end if;
		    end if;

		    x := &+H;//Coefficients(g_t);
		    xf := Polynomial(FF, Eltseq(Numerator(x)));
		    B := {i : i in [1 .. #Fact] | xf mod FII eq xf mod Fact[i]};
		    // Unused !! Is this correct? I only have 1 counter example
		    // I need it for above but I end up with a correct answer 
		    // without it here
		    //assert B eq gS;
		    r_tries := 0;
		    while r_tries lt 10 and B ne gS or x in CoefficientField(F) do
			x := &+H[Setseq(s)] where s is {Random(1, #H) : i in [1 .. Random(1, #H)]};
			//x := &+[Random(-100, 100)*HH : HH in H];
			r_tries +:= 1;
			if x in CoefficientField(F) then continue; end if;
			xf := Polynomial(FF, Eltseq(Numerator(x)));
			B := {i : i in [1 .. #Fact] | xf mod FII eq xf mod Fact[i]};
//x;
		    end while;

		    if B eq gS and x notin CoefficientField(F) and (true or assigned g_t) then
			elt := x;
		//"Sum of coeffs";
		    elif assigned g_t then 
			// no point trying again
			elt := H;
		    else
			g_t := gcd_attempt_at_g_t(M_orig);
//"Use GCD to get subfield poly";
			if g_t cmpeq false then
			    delete g_t;
			    elt := H;
			// could still get through the check after the subfield
			// is constructed but don't want to use this g_t if it
			// is dodgy : do we want to do anything?
			elif (Proof ge 1 and not check4(g_t)) or 
			    (Proof ge 2 and not check5(g_t, H)) then
			    delete g_t;
			    elt := H;
			    "Checks failed";
			    // break i; ?????
			end if;
		    end if;

		end while;
//g_t, L;
		// Had an infinite example in here, works without!
		//B := BlockFromPrimitiveElement(l, elt, n/Degree(g));
		//#B, n/Degree(g);
		//[x[2] : x in l`Fields];
		//B;
		/* 
		WHY DOES InternalGaloisSubfieldLatticeAddField compute a 
		different block? IF B is wrong!!!
		*/

function MinPoly(b,deg)
//returns a monic minimal polynomial over the rationals

ll:=[b^i: i in [0..deg]];
ll:=[Eltseq(x):x in ll];
M:=Matrix(Rationals(),ll);
ker:=Kernel(M);
assert Dimension(ker) eq 1;
d:=ker.1;
d:=Eltseq(d);
Qx := PolynomialRing(Rationals()); x := Qx.1;
g:=Qx ! d;
g:=g/LeadingCoefficient(g);

return g;

end function;

		assert n mod Degree(g) eq 0;
		assert not assigned g_t or Degree(g) eq Degree(g_t);
		if false and B cmpne false and exists{x : x in l`Fields | x[2] eq B} then
//"ALREADY GOT IT?";
		    L := CoefficientRing(F);
		else
		    //time L := SubfieldFromBlock(F, B, l : Opt := false);
		    if true then
		        //"Subfiel", Degree(F) / #H, #H, #Sprint(elt), elt;
			if Type(elt) eq SeqEnum then
			    L := func<|sub<F | elt>>();
			else
			    if not true then
				L := func<|sub<F | elt>>();
			    else 
				//min_pol := MinPoly(elt, n div Degree(g));
				min_pol := MinimalPolynomialByTraces(elt);
				L := ext<CoefficientField(F) | min_pol>;
				Embed(L, F, elt);
			    end if;
			end if;
		    else 
			min_pol := MinimalPolynomial(elt);
			L := ext<CoefficientField(F) | min_pol>;
			Embed(L, F, elt);
		    end if;
		    if Type(elt) ne SeqEnum then
		    assert Evaluate(DefiningPolynomial(L), elt) eq 0;
		    assert F!L.1 eq elt;
		    end if;
		    assert Evaluate(DefiningPolynomial(L), F!L.1) eq 0;
		end if;
		//assert Degree(L)*Nrows(M_orig) eq n;
		assert Degree(L)*Degree(g) eq n;

		if Proof ge 1 and (not assigned g_t or Type(elt) eq SeqEnum) then
		    xf := Polynomial(FF, Eltseq(Numerator(F!L.1)));
		    if xf mod FII ne xf mod Fact[i] then
//"New break";
			Exclude(~blocks, gS);
			delete elt;
			break i;//for more precision
		    end if;
//"Did it the 98 way?", Proof, proof;
		end if;

		// need to make it unassigned for the next loop!
		delete elt;
//L;
                vprint Subfields,2:"Time for remaining steps:",Cputime(cput);
                vprint Subfields,1:"Found subfield given by",DefiningPolynomial(L);
		if L ne CoefficientRing(F) then
		    // L is set to the coeff ring when we have already computed it
		    // which will be incompatible with these assertions so hide 
		    // them in here
		    //assert Degree(L) eq m;
		    assert n mod Degree(L) eq 0;
		    bool, bs := InternalGaloisSubfieldLatticeAddField(l, L);// : B := B);
//"Added", bool;
		    if bool then
			Append(~S, L);
		    end if;

		    // assertions to check the coercion
		    if Debug then
		      assert Evaluate(DefiningPolynomial(L), F!L.1) eq 0;
		    end if;
		end if;
		fact_complete +:= 1;
		proof := Proof;
		increase_precision_factor := 1;
                vprint Subfields,3:"Current block list is:",blocks; 
            
                if #blocks gt 0 then
                   bll := {a[2] : a in l`Fields};
                   all_block_systems := [[SetToSequence(b) : b in a] : a in bll | #Representative(a) gt 1];
                   gal_approx := IntersectionOfWreathProducts(all_block_systems);
                   assert #gal_approx mod gal_lower_bound eq 0;  
                   principal_part := {MinimalPartition(gal_approx: Block := {1,i}) : i in [2..Degree(gal_approx)]};
                   pp_new := [a : a in principal_part | not a in bll and #a gt 1];
                   if GetVerbose("Subfields") gt 0 then
                     printf"Order of Galois starting group: %o\n",
                         #gal_approx;  
                     printf"Group forces %o additional principal partitions\n", #pp_new;
                     if #pp_new gt 0 then printf"Adding these fields to the lattice.\n"; end if;
                   end if;
                   p0 := l`Prime[1];
                   for part in pp_new do
                    subf := SubfieldFromBlock(F, Set(part), l);
                    Append(~S,subf);
                    bool, bs := InternalGaloisSubfieldLatticeAddField(l,subf:B := Set(part));
                    assert bs eq part;  
                    emb := Polynomial(ElementToSequence(F!subf.1)); // Embedding
                    first_block := {i : i in [1 .. #Fact] | emb mod FII eq emb mod Fact[i]};
                    if #Representative(part) ne &+[Degree(Fact[i]) : i in first_block] then
// More precision needed to reconstruct first block
                     first_block := {i : i in [1 .. #fact] | Parent(fi)!emb mod fi eq Parent(fi)!emb mod fact[i]};
                     assert  #Representative(part) eq &+[Degree(Fact[i]) : i in first_block];
                    end if;
                    vprintf Subfields,2: "First block %o\n",first_block;
                    Include(~blocks,first_block);  
                   end for;                    
                   if Order(gal_approx) eq gal_lower_bound then                    
                      vprint Subfields,1:"Group reached lower bound. Early return from generating subfields.";
                      l`GeneratingComplete := true;
                      return S;
                   end if; 
                end if;
	    end for;
	    // if this gets too large then want to use the block system proof
	    increase_precision_factor *:= 2;


	end while;
//blocks;
    else
        vprint Subfields, 1:"Coefficient field is not Q. Use factorization approach.";
	f := PolynomialRing(F)!f;
	f div:= Polynomial(F, [-F.1, 1]);

        fact, lc := Factorization(f);
        vprint Subfields, 1: "Have factorization";
	if false or Debug then
	    assert lc * &* [x[1] : x in fact] eq f;
	end if;

//"Have factorization";
	BF := Basis(F);
	for f in fact do
//f;
	    if ISA(Type(F), FldNum) then 
		Fi := NumberField(f[1] : DoLinearExtension := true, Check := false);
	    elif ISA(Type(F), FldFun) then
		Fi := FunctionField(f[1] : Check := false);
	    end if;
	    phi := hom<F -> Fi | Fi.1>;
	    B := [&cat[Eltseq(r) : r in Eltseq(b)] : b in [phi(bb) - bb : bb in BF]];
	    M := Matrix(B);
	    K := KernelMatrix(M);
	    // Need to find a block system to get better input to sub<>
	    df := DefiningPolynomial(F);

            vprint Subfields, 1: "Building subfield of degree", Nrows(K);
	    if assigned l`UseGalois and Characteristic(F) ne 0 then
//"HERE HERE HERE";
		blocks := {};
		for i in [1 .. Nrows(K)] do
		    bg := GetBlock(l`UseGalois, F!Eltseq(K[i]));
		    Include(~blocks, bg);
		end for;
		B := BlockComposite(blocks);
                if Debug then
                  L2 := sub< F | [F!Eltseq(K[i]) : i in [1 .. Nrows(K)]]>;
                  "Degree L2", Degree(L2);
                  assert (L2 eq CoefficientRing(F) and Nrows(K) eq 1) or Degree(L2) eq Nrows(K);
                end if;
                assert #B eq Nrows(K);

//B;
		if #B eq Degree(F) then
		    L := F;
		    assert Nrows(K) eq Degree(F);
		elif #B eq 1 then
		    L := CoefficientRing(F);
		    assert Nrows(K) eq 1;
		else
//"FromBlock CALL FROM GeneratingSubfields";
		    L := SubfieldFromBlock(F, B, l : Opt := true);
		    assert Degree(L) eq Nrows(K);
		end if;
	    else
		H := [F!Eltseq(K[i]) : i in [1 .. Nrows(K)]];
		L := sub< F | H>;
                assert Nrows(K) eq 1 or Degree(L) eq Nrows(K);
		B := false;
	    end if;
	    if L ne CoefficientRing(F) then
		bool, bs := InternalGaloisSubfieldLatticeAddField(l, L);// : B := B);
		if B cmpne false and assigned bs then
		    assert bs eq B;
		end if;
		if bool then
                    vprint Subfields,1:"Generating subfield",L,"found.";
		    Append(~S, L);
		end if;

		// assertions to check the coercion
                if Debug then
                  assert Evaluate(DefiningPolynomial(L), F!L.1) eq 0;
                end if;
	    end if;
	end for;
    end if;
    vprint Subfields,1:"Have generating subfields";
    l`GeneratingComplete := true;
    return S;

end function;

function SubfieldsOfAll(F : OptAlg := false, Proof := 1)
/*
This function implements the Algorithm "AllSubfields" of van Hoeij and Klueners
It finds a generating set for the subfields of F and sets up the array e
Additionally, it also puts the generating subfields into a subfield lattice
*/
    // Get generating set
    l := InternalGaloisSubfieldLatticeCreate(F);
    S := GeneratingSubfieldsFunc(F, l : OptAlg := OptAlg, Proof := Proof);
    if OptAlg and S cmpeq false then 
        vprint Subfields,1:"Using combinatorial algorithm";
//"Back to old";
	S := InternalSubfields(F);
	for s in S do 
	    _ := InternalGaloisSubfieldLatticeAddField(l, s[1]);
	end for;
	l`Complete := true;
	l`GeneratingComplete := true;
	return [<x[1], Coercion(x[1], F)> : x in l`Fields], l;
	return S, l;
    end if;
    // Take intersections
    e := [];
//"Got lattice";
    for i in S do
	if i eq F then
	    Append(~e, 1);
	else 
	    Append(~e, 0);
	end if;
    end for;
    //S is a copy of l`Fields but the first elements of the tuples are
    //fields rather than maps from the fields into F
    S := [<x, y> where _, y := InternalGaloisSubfieldLatticeFindField(l, x) : x in S];
//"Have S";
    //L is a copy of the top of the subfield lattice
    L := <F, y> where _, y := InternalGaloisSubfieldLatticeFindField(l, F);
    NextSubfields(F, S, L, e, 0, l);
    l`Complete := true;
    if false and Type(F) eq FldFun then
	return [<Domain(x[1]), x[1]> : x in l`Fields], l;
    else 
	return [<x[1], Coercion(x[1], F)> : x in l`Fields], l;
    end if;
end function;

function IntersectionFunc(F, K, FK)
// F is a subfield of FK, K is a principal subfield of FK (from the generating 
// set)
// FK is the top field which we are computing Subfields of
// return a subfield of F

    if CoefficientField(F) ne CoefficientField(K) then
    B := Basis(F);
    BF := ChangeUniverse(B, FK);
    BK := ChangeUniverse(Basis(K), FK);
    M := ZeroMatrix(CoefficientRing(FK), #BF + #BK, Degree(FK));
    for i := 1 to #BF do 
	M[i] := Vector(Eltseq(BF[i]));
    end for;
    for i := 1 to #BK do
	M[i + #BF] := Vector(Eltseq(BK[i]));
    end for;
    //S, null := Solution(M, ZeroMatrix(CoefficientRing(FK), Ncols(M), Ncols(M)));
    vtime Subfields : S := KernelMatrix(M);
    //null := Rank(null);
    S := Submatrix(S, 1, 1, Nrows(S), #BF);
    S := Matrix(F, S);
    M := Matrix(Degree(F), 1, B);
    M := S*M;
    // Need to find a block system to get better input to sub<>
    vtime Subfields : return sub<F | Eltseq(M)>;
    end if;

    //Rewritten using SubfieldFromBlock
    //Lattice may be stored and populated - it may not be constructed empty here
    //so cannot make assumptions when fields are already in the lattice
    L := InternalGaloisSubfieldLatticeCreate(FK);
    _, BK := InternalGaloisSubfieldLatticeAddField(L, K);
    _, BF := InternalGaloisSubfieldLatticeAddField(L, F);
    B := InternalGaloisSubfieldLatticeMeet(BK, BF);
    if #B eq 1 then 
	return CoefficientRing(FK);
    end if;
    if #B eq Degree(FK) then
	return FK;
    end if;
    return SubfieldFromBlock(FK, B, L : NumSub := #L`Fields);

end function;


// For F defined by monic integral poly only
function SubfieldFromBlockANF(F, B, L : Opt := false)

    // Splitting field containing the roots of the defining polynomial of f
    split := L`Prime[5];
    // Roots of defining polynomial of f in a residue field
    r := L`Prime[4];
    // Roots of the defining polynomial of the subfield in residue field
    theta_k := [&*[r[i] : i in b] : b in B];
    // Tschirnhausen transformation to ensure uniqueness
    tschirni := PolynomialRing(Integers()).1;
    // Check whether the roots of the defining polynomial of the subfield are 
    // unique in the residue field and transform until they are
    for i in [1 .. Degree(F)] do
	if #Set(theta_k) eq #B then
	    break;
	end if;
	tschirni +:= 1; 
	theta_k := [&*[Evaluate(tschirni, r[i]): i in b] : b in B];
    end for;
    no_tschirni := Degree(F);
    while #Set(theta_k) ne #B do
	tschirni := Parent(tschirni)!([Random(3) : i in [1 .. Maximum(2, no_tschirni div 5)]] cat [1]);
	theta_k := [&*[Evaluate(tschirni, r[i]): i in b] : b in B];
	no_tschirni +:= 1;
    end while;
    // prime
    p := L`Prime[1];
    f := DefiningPolynomial(F);

    // compute a bound on the complex absolute value (size) of the roots of the
    // defining polynomial of F
    if not assigned L`max_comp then
	comp_roots := Roots(f, ComplexField());
	max_comp := Ceiling(Maximum([Abs(x[1]) : x in comp_roots]));
    else
	L`max_comp := max_comp;
    end if;
    // bound the coefficients of the defining polynomial of the subfield
    // which will be sums of products of the roots of the defining polynomial
    // of F which we bounded with max_comp
    // Take transformation into account in the bound too
    C := Evaluate(tschirni, max_comp)^#Rep(B);
    bound := Maximum([Binomial(#B, i)*C^i : i in [1 .. #B]]);

    // Get precision to use with this bound
    prec := Ceiling(Log(L`Prime[1], 2*bound)) + 1;
    assert L`Prime[1]^(prec) gt 2*bound;
    if prec gt split`DefaultPrecision then
	SetPrecision(split, prec);
    end if;
    split`DefaultPrecision := prec;

    // Get roots of defining polynomial of F to large enough precision
    if not assigned L`Roots then
	L`Roots := [HenselLift(Polynomial(split, f), split!x) : x in r];
    end if;
    R := L`Roots;

    // Construct map to map back from the splitting field to the integers
    // and reconstruct
    _B := L`Prime[1]^(split`DefaultPrecision);
    back_map := Coercion(split, Integers(CoefficientRing(F)));
    _B2 := _B div 2;
    back_map := function(x, b)
	x := back_map(x);
	return (x gt _B2 select x - _B else x);
    end function;
    from_residue_field_map := Coercion(Codomain(L`Prime[2]), Integers(CoefficientRing(F)));

    // R contains the roots of the defining polynomial of F in the completion
    // product of roots in a block is a root of the defining polynomial of the
    // subfield (in theta)
    // theta contains elements of the completion which are the roots of split_g
    theta := [&*[Evaluate(tschirni, R[i]): i in b] : b in B];
    split_g := &* [Polynomial([-x, 1]) : x in theta];

    // essentially the defining polynomial of the subfield, roots are the 
    // elements of theta
    // split_g is monic and integral so g will be too
    g := Polynomial(Integers(CoefficientRing(F)), [back_map(x, true) : x in Coefficients(split_g)]);

    // All the roots of the defining polynomial of F in blocks
    rcat := &cat [ [FieldOfFractions(split) | R[i] : i in b] : b in B];
    // All the roots of the defining polynomial of the subfield (contains
    // duplicates)
    thetacat := &cat [ [FieldOfFractions(split) | theta[j] : i in [1 .. #Rep(B)]] : j in [1..#B]];

    // Map roots of defining polynomial of F to roots of defining polynomial
    // of subfield, which are products of such roots
    // Map each root to the product of roots which contains it
    // This is still over the completion
    I := Interpolation(rcat, thetacat);
    J := I;

    // map back from the splitting field
    I := Polynomial([back_map(c, false) : c in Coefficients(I)]);
    JJ := I;

    /*
    We are using the lifting

        b_{i+1} = b_i - w_i g(b_i) mod p^{2^i} (or so)
        w_{i+1} = w_i(2 - w_i g'(b_{i+1})) mod p^{2^i+1}

    in Klueners

    where we start with an approximation b_0 such that g(b_0) = 0 mod p and
    w_0 is the inverse of g'(b_0) mod p

    We are here trying to get our approximations b_0 (z) and w_0 (w)
    */

    dg := Derivative(split_g);
    // Ie maps roots in rcat (rcat[i]) to 1/g'(thetacat[i])
    // This will compute w = 1/g'(z) where z = I(F.1)
    // and I maps rcat[i] to thetacat[i]
    Ie := Interpolation(rcat, [1/Evaluate(dg, t) :t in thetacat]);

    Ie := Polynomial([back_map(c, false) : c in Coefficients(Ie)]);
    w := Evaluate(Ie,F.1);

    if not assigned L`EquationOrder then
//	m := Evaluate(Derivative(f), F.1);
	L`EquationOrder := Order([(F.1)^i : i in [0..Degree(F)-1]] : Order, Verify := false);
    end if;
    E := L`EquationOrder;

    den := Denominator(FieldOfFractions(E)!w);
    w *:= den;
    den, iden := XGCD(den, p^prec);
    w *:= iden;
    assert den eq 1;

    z := Evaluate(I, F.1);
    pp := p;
    zz := z;
    w := w;
    pE := p*E;
    pm := p;
    p_val := 1;

    fpa := Evaluate(Derivative(f), F.1);
    e := E!Evaluate(g, zz);
    e2 := E!(Evaluate(Derivative(g), zz)*w - den);
    while (e ne 0 and e mod (pm*pE) eq 0) and (e2 mod (pm*pE) eq 0) do
	pE *:= pm;
	pp *:= p;
	p_val +:= 1;
    end while;
    pE := pp*E;

    while Evaluate(g, zz) ne 0 do
p_val;
	pp *:= pp;
	p_val *:= 2;
	pE := pp*E;

	zz := (E!(zz*fpa) mod pE)/fpa;
	w := (E!(w*fpa) mod pE)/fpa;
	nz := Evaluate(g, zz)*w;
	// Really wanted to multiply by w/den, so do the /den bit
	dnz := Denominator(nz);
	nz := E![(Numerator(x) div den) : x in Eltseq(E!Numerator(nz))];
	nz := (E!nz mod pE)/dnz;
	zz := zz - nz;
	nz := w*Evaluate(Derivative(g), zz);
	// Again really wanted to multiply by w/den so do the /den bit
	w := w*(2 - E![Numerator(x) div den : x in Eltseq(FieldOfFractions(E)!nz)]);
	w := (E!(w*fpa) mod (den*pE))/fpa;
    end while;
    subF := ext<CoefficientField(F) | g>;
    Embed(subF, F, F!zz);
		    assert F!subF.1 eq F!zz;
		    assert Evaluate(DefiningPolynomial(subF), F!zz) eq 0;
		    assert Evaluate(DefiningPolynomial(subF), F!subF.1) eq 0;
    return subF;
end function;


/* A more p-adic version of lifting embeddings of subfields:

  g  : Subfield polynomial
  zz : Approximation of embedding
  L  : p-adic structure of roots 
  F  : Number Field
  E  : Order of F
  f  : Defining polynomial of F
  zz : p-adic appoximation of embedding in E 
*/
function my_eval(f,x, modul)
 n := Degree(f);
 res := Coefficient(f,n);
 while n gt 0 do
  n := n - 1;
  res := (x*res + Coefficient(f,n)) mod modul;
 end while;
 return res;
end function;

function LiftEmbeddingANF(zz,L,E, g_not_scaled, _df)

 dg := Derivative(g_not_scaled);
 p := L`Prime[1];
 if Valuation(Norm(_df),p) ne 0 then
  vprint Subfields,2:"_df not coprime";
  return false, zz;
 end if;
 if (Discriminant(PolynomialRing(GF(p))!g_not_scaled) eq 0) then
  vprint Subfields,2:"discriminant not coprime";
  return false, zz;
 end if;

 qu,pi := quo<E | p * E>;
 z_ns := (zz * (1/pi(_df)) @@ pi) mod (p*E);
 gsi_e := (1/pi(my_eval(dg, z_ns, p * E))) @@ pi;
 
 modul := p^2;
 g_e := my_eval(g_not_scaled, z_ns, modul * E);
 prec := 2; 
 suc := false;
 repeat
  z_ns := (z_ns - g_e * gsi_e) mod  (modul * E);
  assert2 my_eval(g_not_scaled,z_ns,(modul * E)) eq 0;
  zz_seq := [Integers()!a mod modul : a in ElementToSequence(E!(z_ns * _df))];
  zz_seq := [2*a gt modul select a - modul else a : a in zz_seq];
  mm := Max([AbsoluteValue(a) : a in zz_seq]);
  zz := E!zz_seq;
//  z_ns := zz / _df;
  if mm * 10^6 lt modul then
// The aproximation may be good...check!
   vprint Subfields,3:"Doing full check";
   vtime Subfields,3: suc :=  Evaluate(g_not_scaled,zz / _df) eq 0;
  end if;  
  if not suc then
   vprintf Subfields,3:"Lifting embedding to precision %o^%o\n",p,2*prec;
   gsi_e := (gsi_e - ((my_eval(dg, z_ns, modul * E) * gsi_e) mod (modul * E)- 1) 
                      * gsi_e) mod (modul * E);
   modul := modul^2;
   prec := 2 * prec; 
   g_e := my_eval(g_not_scaled, z_ns, modul * E);
  end if;
 until suc;

 return true, zz;
end function;


// g gets too large : how to make it smaller? (rewrite!)
// there is C code to do this for number fields.
function SubfieldFromBlock(F, B, L : Opt := false, NumSub := 0)

    vprintf Subfields,1:"Computing subfield to block %o\n", [a : a in B | 1 in a][1];
    tt_sfb := Cputime();
 
    if Type(F) eq FldNum and IsMonic(DefiningPolynomial(F)) and IsCoercible(PolynomialRing(Integers()), DefiningPolynomial(F)) then
	//return SubfieldFromBlockANF(F, B, L : Opt := Opt);
    end if;
//F, B;
    // Get the roots of the subfield as a product of roots of F
    // need a splitting field and roots to high precision
    if Debug then
      "SubfieldFromBlock";
    end if;

    split := L`Prime[5];	// splitting field
    if assigned L`UseGalois then	// use roots in correct order
	r := L`UseGalois`Roots;
	_, rfm := ResidueClassField(L`UseGalois`Ring);
	r := [rfm(rr) : rr in r];
    else
	r := L`Prime[4];		// roots in residue field
    end if;
    tschirni := PolynomialRing(Integers()).1;
    rel := false;
    p := L`Prime[1];
    f := DefiningPolynomial(F);
    if Type(F) eq FldFun then
//tschirni;
//(L`UseGalois)`max_comp;
	SL := SLPolynomialRing(Integers(), Degree(F));
	theta_inv := [&*[SL.i : i in b] : b in B];
	g := &* [Polynomial([-x, 1]) : x in theta_inv];
	cg := Eltseq(g);
	for i in [1 .. Degree(g)+1] do
	    cg[i]`GalInvType := "Other";
	end for;
	scale := L`UseGalois`Scale;
	// Recompute the tschirni now that we have the scaling factor
	// Here the scaling factor matters since we are not using GaloisRoot
	scale_rf := L`Prime[2](scale);
	theta_k := [&*[Evaluate(tschirni, scale_rf*r[i]): i in b] : b in B];
	for i in [1 .. Degree(F)] do
	  if #Set(theta_k) eq #B then
	    break;
	  end if;
	  tschirni +:= 1; //CF: wrong in char p - guaranteed to work for number 
			  //fields, see Klueners' thesis
	  theta_k := [&*[Evaluate(tschirni, scale_rf*r[i]): i in b] : b in B];
	end for;
	no_tschirni := Degree(F);
	while #Set(theta_k) ne #B do
	  //CF: probably too restrictive in general for function fields in char p
	  tschirni := Parent(tschirni)!([Random(3) : i in [1 .. Maximum(2, no_tschirni div 5)]] cat [1]);
	  theta_k := [&*[Evaluate(tschirni, scale_rf*r[i]): i in b] : b in B];
	  no_tschirni +:= 1;
	end while;
	bounds := [L`UseGalois`Bound(tschirni, inv, 1) : inv in cg[1 .. #cg - 1]];
        //CF: too slow for large examples, do it directly.

	if Characteristic(F) eq 0 then
	    bound := &+bounds;
	    bound := ChangePrecision(bound, 2*AbsolutePrecision(bound));
	    bound *:= bound;
	    prec := L`UseGalois`GetPrec(bound, L`UseGalois);
	    prec +:= prec;
	    split`DefaultPrecision := prec[1];
	    csplit := CoefficientRing(split);
	    csplit`DefaultPrecision := prec[2];
	    R := L`UseGalois`Roots;
	    if not assigned L`Roots or Precision(L`Roots[1]) lt prec then
		L`Roots := [GaloisRoot(i, L`UseGalois:Prec := prec) : i in [1 .. Degree(F)]];
	    end if;
	    R := L`Roots;
	    char := Characteristic(L`Prime[3]);
	    half_char := Ceiling(char / 2);
	    back_map := function(x, b)
	        if false and Debug then 
                  "before", x, bound;
                end if;
		bool, x := (L`UseGalois)`IsInt(x, bound, (L`UseGalois) : full);
		if b then
                  assert bool;
		end if;
		return x;
		if x ne 0 then
		  x := Parent(x)!Polynomial(
                    [c gt half_char select c - char else c 
                      : c in Coefficients(Numerator(x))]) 
                        /Polynomial(
                    [c gt half_char select c - char else c 
                      : c in Coefficients(Denominator(x))]);
		end if;
	        if Debug then
                  "after", x;  
                end if;
		return x;
	    end function;
	else
	    bound := Maximum(bounds);
	    prec := L`UseGalois`GetPrec(bound, L`UseGalois);
	    if not assigned L`Roots or Precision(L`Roots[1]) lt prec then
		L`Roots := [GaloisRoot(i, L`UseGalois:Prec := prec) : i in [1 .. Degree(F)]];
	    end if;
	    R := L`Roots;
	    back_map := function(x, b)
		bool, x := (L`UseGalois)`IsInt(x, bound, (L`UseGalois));
		if b then
		  if not bool then
		  F;
		  end if;
                  assert bool;
		end if;
		return x;
	    end function;
	end if;
	from_residue_field_map := Inverse(L`Prime[2]);
    else 
	rel := ISA(Type(CoefficientRing(F)), FldAlg);
	scale := LCM([Denominator(CoefficientRing(F)!x) : x in 
		    Eltseq(Polynomial(CoefficientRing(F), f)/LeadingCoefficient(f))]);
	if not assigned L`max_comp then
	    if rel then
		comp_roots := [];
		assert not ISA(Type(CoefficientRing(CoefficientRing(f))), FldAlg);
		for ip in InfinitePlaces(CoefficientRing(f)) do
		    _if := Polynomial([Evaluate(c, ip) : c in Coefficients(f)]);
		    comp_roots cat:= Roots(_if, ComplexField());
		end for;
	    else
/*
From Galois.m : get a bound without getting the roots
  if Maximum([Abs(x) : x in Eltseq(f)]) lt 2^400 then
    vtime GaloisGroup, 3: comp_roots:=Roots(f,ComplexField());
    if (not IsMonic(f)) or LCM([Denominator(x) : x in Eltseq(f)]) ne 1 then
      S`Scale := LCM([Denominator(x) :
	     x in Eltseq(Polynomial(Rationals(), f)/LeadingCoefficient(f))]);
      comp_roots := [ <x[1]*S`Scale, x[2]> : x in comp_roots];
    end if;
    vprint GaloisGroup, 3: "done\n";
    max_comp:=Ceiling(Maximum([Abs(x[1]):x in comp_roots]));
  else
    c := Eltseq(f);_n := #c;
    max_comp := Maximum([Abs(c[_n-i]/c[_n])^(1/i) : i in [1.._n-2]]);
    max_comp := 2*Maximum(max_comp, Abs(c[1]/2/c[_n])^(1/(_n-1)));
    max_comp := Ceiling(max_comp); //Fujiwara bound
    if (not IsMonic(f)) or LCM([Denominator(x) : x in Eltseq(f)]) ne 1 then
      S`Scale := LCM([Denominator(x) :
	     x in Eltseq(Polynomial(Rationals(), f)/LeadingCoefficient(f))]);
      max_comp *:= S`Scale;
    end if;
  end if;
*/
		if false and Maximum([Abs(x) : x in Eltseq(f)]) lt 2^5 then
                    vprintf Subfields,3:"Calculating Complex Roots...";
		    comp_roots := Roots(f, ComplexField());
                    vprintf Subfields,3:"done\n";
		else 
		    max_comp := FujiwaraBound(f);
		end if;
	    end if;
	    if assigned comp_roots then
		comp_roots := [x[1]*scale : x in comp_roots];
		max_comp := Ceiling(Maximum([Abs(x) : x in comp_roots]));
	    else
		max_comp *:= scale;
	    end if;
	    L`max_comp := max_comp;
	else
	    max_comp := L`max_comp;
	end if;

	// Recompute the tschirni now that we have the scaling factor
	// Here the scaling factor matters since we are not using GaloisRoot
	theta_k := [&*[Evaluate(tschirni, scale*r[i]): i in b] : b in B];
	for i in [1 .. Degree(F)] do
	  if #Set(theta_k) eq #B then
	    break;
	  end if;
	  tschirni +:= 1; //CF: wrong in char p - guaranteed to work for number 
			  //fields, see Klueners' thesis
	  theta_k := [&*[Evaluate(tschirni, scale*r[i]): i in b] : b in B];
	end for;

        vprintf Subfields,3 : "Tschirni is %o\n",tschirni;  

	C := Evaluate(tschirni, max_comp)^#Rep(B);
	bound := Maximum([Binomial(#B, i)*C^i : i in [1 .. #B]]);
	if rel then
	    /*
	    prec := Ceiling(Log(Minimum(L`Prime[1]), 2*bound)) + 1;
	    assert Minimum(L`Prime[1])^(prec) gt 2*bound;
	    // for the reconstruction - precision gets shared among coeffs
	    prec *:= Degree(Order(p)) div Degree(p);
	    */

	    Z_k := MaximalOrder(CoefficientField(F));
	    RB := Transpose(RealBasis(Z_k));
	    a,b := SpectralRadius(RB);
	    n := Degree(Z_k);
	    C := 1/b*bound*Sqrt(n);
	    prec := Ceiling(n*Log(C* 2 * 3^(n-1))/Log(Norm(p)));
	else
	    prec := Ceiling(Log(L`Prime[1], 2*bound)) + 1;
	    assert L`Prime[1]^(prec) gt 2*bound;
	end if;

	if prec gt split`DefaultPrecision then
	SetPrecision(split, prec);
	end if;
	split`DefaultPrecision := prec;

	if rel then
	    // Use L`Prime[6] to map into split
	    ms := L`Prime[6];
	    f := Polynomial(split, [ms(x) : x in Eltseq(f)]);
	end if;
	if not assigned L`Roots or Precision(L`Roots[1]) lt prec then
	    L`Roots := [scale*HenselLift(Polynomial(split, f), split!x) : x in r];
	end if;
 
        vprintf Subfields,3 : "Ring of roots is: %o.\n",Parent(L`Roots[1]) ;   

	R := L`Roots;
	if rel then
	    k := CoefficientRing(F);
	    Z_k := MaximalOrder(k);
	    Z := Integers();
	    l_k := Degree(p);
	    back_map := function(x, b) 
		prec := AbsolutePrecision(x);
		x := BaseRing(split)!x;

		M := VerticalJoin(Matrix(Z, [Eltseq(
		    BaseRing(split)!ms(x))
		 : x in Basis(Z_k, k)]), Minimum(p)^prec*IdentityMatrix(Z, l_k));
		f, I := IsConsistent(M, IdentityMatrix(Z, l_k));
		assert f;
		I := Submatrix(I, 1, 1, l_k, Degree(k));
		Zk := Z_k;
		kk := k;
		assert forall{x : x in [1..l_k] |
		    Valuation(ms(Z_k!Eltseq(I[x]))
		  - BaseRing(split)!Eltseq(IdentityMatrix(Z, l_k)[x])) gt 0};

		RE := ReconstructionEnvironment(p, prec);
		x := Matrix(Z, [Eltseq(x)]) * I;
		x := Z_k!Eltseq(x);

		x := Reconstruct(Order(p)!(x), RE : UseDenominator := false);
		return x;
	    end function;
	else
	    _B := L`Prime[1]^(split`DefaultPrecision);
	    back_map := Coercion(split, Integers(CoefficientRing(F)));
	    _B2 := _B div 2;
	    back_map := function(x, b) 
	    //x;
		x := back_map(x); 
		return (x gt _B2 select x - _B else x); 
	    end function;
	end if;
	from_residue_field_map := Coercion(Codomain(L`Prime[2]), Integers(CoefficientRing(F)));
    end if;
    // R contains the roots of the defining polynomial of F in the completion
    // product of roots in a block is a root of the defining polynomial of the 
    // subfield (in theta)
    // theta contains elements of the completion which are the roots of split_g
//"tschirni : ", tschirni;
    theta := [&*[Evaluate(tschirni, R[i]): i in b] : b in B];
    split_g := &* [Polynomial([-x, 1]) : x in theta];
    if not assigned L`UseGalois then
    // not when UseGalois since then we use different roots so don't expect it
    // to match since we have not updated theta_k
    rf, mrf := ResidueClassField(Universe(theta));
    assert rf eq Universe(theta_k);
    assert theta_k eq [mrf(th) : th in theta];
    end if;
//g;
    // essentially the defining polynomial of the subfield, roots are the elements
    // of theta
    if Type(CoefficientRing(F)) eq FldFun then
	g := Polynomial(MaximalOrderFinite(CoefficientRing(F)), [back_map(x, true) : x in Coefficients(split_g)]);
    else
	g := Polynomial(Integers(CoefficientRing(F)), [back_map(x, true) : x in Coefficients(split_g)]);
    end if;

    g_not_scaled := g; // Don't confuse me with scaling!
    vprintf Subfields,3: "Subfield polynomial: %o\n",g;

    if false or Debug then
    while #Roots(g, F) eq 0 do
	prec *:= 2;
	if prec gt split`DefaultPrecision then
	ChangePrecision(~split, prec);
	end if;
	split`DefaultPrecision := prec;
	if assigned L`UseGalois then
	    L`Roots := [GaloisRoot(i, L`UseGalois:Prec := prec) : i in [1 .. Degree(F)]];
	    R := L`Roots;
	else
	    R := [scale*HenselLift(Polynomial(split, f), split!x) : x in r];
	end if;
R[1];
	theta := [&*[Evaluate(tschirni, R[i]): i in b] : b in B];
	split_g := &* [Polynomial([-x, 1]) : x in theta];
split_g;
Discriminant(split_g);
//g;
	g := Polynomial(Integers(CoefficientRing(F)), [back_map(x, true) : x in Coefficients(split_g)]);
//scale;
//[MinimalPolynomial(x[1]) : x in Roots(g, F)];
prec;
//g;
    end while;
    end if;
    _dg := Discriminant(g);
//Factorization(_dg);

    // split_g and g are always monic here, are they integral? Depends on whether
    // roots in R are, I think they are because we use GaloisRoot for R rather
    // than `Roots

    // check there is a root of g with block system B
    if false or Debug then 
	gg := Polynomial(split, [L`Prime[6](x) : x in Eltseq(g)]);
	gg - split_g;
	_rt :=  Roots(g, F);
	assert #_rt ge 1;
	if assigned L`UseGalois then
	    _brt := [GetBlock(L`UseGalois, x[1]) : x in _rt];
	    assert exists(x){x : x in [1..#_rt] | _brt[x] eq B};
	    "found block system!!!", _brt[x], _rt[x];
	end if;
    end if;

    GFp := L`Prime[2]; 
    // All the roots of the defining polynomial of F in blocks
    rcat := &cat [ [FieldOfFractions(split) | R[i] : i in b] : b in B];
    // All the roots of the defining polynomial of the subfield (contains duplicates)
    thetacat := &cat [ [FieldOfFractions(split) | theta[j] : i in [1 .. #Rep(B)]] : j in [1..#B]];
    // Map roots of defining polynomial of F to roots of defining polynomial 
    // of subfield, which are products of such roots
    // Map each root to the product of roots which contains it
    // This is still over the completion
    I := Interpolation(rcat, thetacat);
    if Debug then
      assert &and[IsWeaklyZero(Evaluate(I, rcat[i]) - thetacat[i]): i in [1 .. #rcat]];
    end if;

    J := I;
    //integral element * discriminant \in equation order
    // Want a polynomial with roots integral_element * discriminant?
    // Want a polynomial over SOME equation order? 
    _f := DefiningPolynomial(F);
    _f := Polynomial([x/l : x in Eltseq(_f)]) where l := LeadingCoefficient(_f);
    _df := Discriminant(_f);
    if Type(CoefficientRing(F)) eq FldFun then
	_d := Lcm([Denominator(x, MaximalOrderFinite(CoefficientRing(F))) : x in Eltseq(_f)]);
    else 
	_d := Lcm([Denominator(CoefficientField(F)!x) : x in Eltseq(_f)]);
    end if;
    if Type(F) eq FldFun then
	_df := Denominator(1/Evaluate(Derivative(_f), F.1), MaximalOrderFinite(F));
    else 
	_df := func< | Denominator(1/Evaluate(Derivative(_f), F.1))>();
    end if;

if not ISA(Type(p), RngElt) then
assert Valuation(Order(p)!_df, p) eq 0;
else
assert Valuation(Parent(p)!_df, p) eq 0;
end if;
//    _df *:= scale^(n*(n - 1)) where n is Degree(F);
   _df *:= scale^(n) where n is Degree(F);
if not ISA(Type(p), RngElt) then
assert Valuation(Order(p)!_df, p) eq 0;
else
assert Valuation(Parent(p)!_df, p) eq 0;
end if;
    //_df *:= _d^(n*(n - 1) div 2) where n is Degree(F);
    //disc = prod_(i ne j) x_i - x_j
    //so, if we replace x_i by x_i*d, then disc changes by (n choose 2)^2
    //(each pair x_i -x_j occurs twice as x_j-x_i as well. There are (n choose
    //2) pairs and (n choose 2) is n*(n-1) div 2....

    //experiment
    //_df *:= _df;

    // _d eq scale!!!!!!!
    //CF: we need to adjust twice: 1st by the denominator - we made the 
    // polynomial monic, but non-integral and then 2nd, by scale
    // since that is what we scale the roots by

    if Type(CoefficientRing(_f)) eq FldFun then
	//assert Denominator(_df, MaximalOrderFinite(CoefficientRing(_f))) eq 1;
	//_df := Numerator(_df, MaximalOrderFinite(CoefficientRing(_f))); // to change type to poly
    else
	assert Denominator(_df) eq 1;
	_df := Numerator(_df); // to change type??? 
    end if;
    if assigned L`UseGalois then
	_ddf :=  L`UseGalois`BaseMap(_df, prec);
    elif rel then
	_ddf :=  ms(_df);
    else
	_ddf :=  split!_df;
    end if;
    // need to make sure coeffs of I are integral so the back_map will succeed
    // now maps rcat[i] to _ddf*thetacat[i]
    I *:= _ddf;
    I := Polynomial(F, [back_map(c, false) : c in Coefficients(I)]);
    JJ := I;

    // the roots of the reversed polynomial are the inverses of the roots 
    // of the polynomial
    // reverse g (invert roots), eval at x*_df, then reverse back
    // same as evaluating g at x/_df??
    // Roots of g are now r*_df where r was a root of g?
    // Should be given the division of zz by _df at the end!@!@
    // This matches the multiplication of I by _ddf
    rf := func<x|Polynomial(Reverse(Eltseq(x)))>;
    ng := rf(Evaluate(rf(g), Parent(g).1*CoefficientRing(g)!_df));
    if false or Debug then
     "old g", g;
     _og := g;
     end if;
    real_g := g;
    g := Parent(g)!ng; 

    if Debug then
      "new g", g;
    end if;
    split_g := Parent(split_g)!rf(Evaluate(rf(split_g), Parent(split_g).1*CoefficientRing(split_g)!_ddf));

    if false or Debug and assigned L`UseGalois then 
	"Root check";
	time assert exists{x : x in Roots(g, F) | GetBlock(L`UseGalois, x[1]) eq B};
    end if;

    /*
    We are using the lifting 
    
	b_{i+1} = b_i - w_i g(b_i) mod p^{2^i} (or so)
	w_{i+1} = w_i(2 - w_i g'(b_{i+1})) mod p^{2^i+1}

    in Klueners

    where we start with an approximation b_0 such that g(b_0) = 0 mod p and
    w_0 is the inverse of g'(b_0) mod p

    We are here trying to get our approximations b_0 (z) and w_0 (w)
    */

    // I maps the roots of the defining polynomial of F to roots of the defining
    // polynomial of the subfield
    // So z should be (an approximation to) a root of the defining polynomial
    // of the subfield (a primitive element)
    z := Evaluate(I, F.1*scale);

    if Type(F) eq FldFun then
	E := CoefficientRing(EquationOrderFinite(F));
	if Type(E) eq RngFunOrd then
	    E := MaximalOrder(E);
	end if;
	if not assigned L`EquationOrder then
	    L`EquationOrder := Order(E, [(F.1*scale)^i : i in [0..Degree(F)-1]] : Order, Verify := false);
	end if;
	E := L`EquationOrder;
	//assert Basis(E, F) eq Basis(EquationOrderFinite(F), F);
	//E := EquationOrderFinite(F);
    else
	if not assigned L`EquationOrder then
	    L`EquationOrder := Order([(F.1*scale)^i : i in [0..Degree(F)-1]] : Order, Verify := false);
	end if;
	E := L`EquationOrder;
    end if;

  tt_emb := Cputime();
// z is an appoximation of the embedding. 
  suc := false; 
  if (not rel) and (CoefficientField(F) cmpeq Rationals()) then
//    g eq g_not_scaled;
    suc, zz :=  LiftEmbeddingANF(E!z,L,E, g_not_scaled, _df);
  end if;
  if not suc then // Use old code
    zz := E!z;
    vtime Subfields,4: eval_g_z := Evaluate(g, z);
    // Check for exact root
    if not true or eval_g_z ne 0 then
        vprintf Subfields,3: "Further lifting for embedding needed.\n"; 

	// Need to lift
	dg := Derivative(split_g);
	if false and assigned L`UseGalois then
	    dg := Polynomial([L`UseGalois`BaseMap(c, prec) : c in Eltseq(Derivative(g))]);
	end if;

	// Ie maps roots in rcat (rcat[i]) to 1/g'(_ddf*thetacat[i])???
	// This will compute w = 1/g'(z) where z = I(F.1*scale)
	// and I maps rcat[i] to _ddf*thetacat[i]
        Ie := Interpolation(rcat, [1/Evaluate(dg, t*_ddf) :t in thetacat]);

	//_dg := Discriminant(g);
	deg_g := Degree(g);
	_dg *:= (_df)^(deg_g*(deg_g - 1));
	if false and assigned L`UseGalois then
	    Ie *:= L`UseGalois`BaseMap(_dg, prec);
	else 
	    Ie *:= Discriminant(split_g);
	end if;
	// Ie now maps rcat[i] to _dg/(g'(_ddf*thetacat[i]))
	Ie := Polynomial([back_map(c, false) : c in Coefficients(Ie)]);
	//Ie;
	//Parent(Ie);
	//Polynomial(Integers(),Ie);

	// Unused! and this is the only use of GFp
	//J := Polynomial([GFp(c) : c in Coefficients(I)] cat [Codomain(GFp)!0]);

if not ISA(Type(p), RngElt) then
assert Valuation(Order(p)!_dg, p) eq 0;
else
assert Valuation(Parent(p)!_dg, p) eq 0;
end if;
	// Want w to be the inverse of g'(zz) for use in lifting
        w := Evaluate(Ie,F.1*scale);
if not ISA(Type(p), RngElt) then
assert &and[Valuation(FieldOfFractions(Order(p))!x, p) ge 0 : x in Eltseq(w)];
else
assert &and[Valuation(FieldOfFractions(Parent(p))!x, p) ge 0 : x in Eltseq(w)];
end if;
	// remove discriminant scaling so w is now 1/g'(I()) = 1/g'(z)
	w := w/_dg;

	den := Denominator(FieldOfFractions(E)!w);
//den;
//Factorization(den);
den_change := false;
 if not ISA(Type(p), RngElt) and Valuation(Order(p)!den, p) gt 0 then
  den_change := true;
  if not IsExport() then
    "Recomputing denominator", den;
  end if;
  val := Valuation(Order(p)!den, p);
  id1 := ideal<Order(p) | den>;
  id1 := id1 / ideal<Order(p) | p>^val;
  den := CRT(ideal<Order(p) | p>, id1, Order(p)!1, Order(p)!0);
  assert w*den in E;
end if;


if not ISA(Type(p), RngElt) then
/*
fd := Factorization(den);
dden := &cat[[<__d[1], __d[2]*x[2]> : __d in _d] where _d := Decomposition(Order(p), x[1]) : x in fd];
dden_nop := [x : x in dden | Valuation(x[1], p) eq 0];
den2 := &*[b^x[2] where _, b := TwoElement(x[1]) : x in dden_nop];
den2;
_w := w*den;
w*den2 in E;
*/
assert Valuation(Order(p)!den, p) eq 0;
else
assert Valuation(den, p) eq 0;
end if;

	// make w integral in the order we are using
	w *:= den;
	if Type(prec) ne RngIntElt then
	    prec := prec[1];
	end if;

if den_change then
 iden := InverseMod(den, p^prec);
 den := 1;
else
	if not ISA(Type(p), RngElt) then
	    den, iden := XGCD(den, Minimum(p)^prec);
	else
	    den, iden := XGCD(den, p^prec);
	end if;
	// divide by denominator mod p
end if;
	w *:= iden; 

	pp := p;
	w := E!w;
	if not ISA(Type(p), RngElt) then
	    pE := E!!p;
	    pm := pE;
	else
	    pE := p*E;
	    pm := p;
	end if;

	p_val := 1;
	dg := Derivative(g);
    //pE;
	// Find to what precision we know the root of the defining polynomial
	// of the subfield
	vprint Subfields,4: "Computing larges modul p^e with g(zz) = 0 mod p^e for initial embedding zz.";
        vtime Subfields,4: e := E!Evaluate(g, zz);
	vtime Subfields,4: e2 := Evaluate(dg, zz)*w - den;
        pEm := pE*pm;
        vtime Subfields,4:
	while func<|(e ne 0 and e mod (pEm) eq 0) and (e2 mod (pEm) eq 0) >() do
//"before", pp;
	  pp *:= p;
	  p_val +:= 1;
	  pE := pEm;
          pEm *:= pm;
//pp;
	end while;
        vprint Subfields,4:"Initial precision",p_val;
//p_val;
	if not ISA(Type(p), RngElt) then
	    vtime Subfields,4: pE := E!!pp;
	else
	    pE := pp*E;
	end if;

	if false or Debug then
	  "Starting at ", Valuation(pp, p);
	  if assigned L`UseGalois then
	      [GetBlock(L`UseGalois, x[1]) : x in Roots(g, F)], B;
	      time assert exists{x : x in Roots(g, F) | GetBlock(L`UseGalois, x[1]) eq B};
	  else
	    assert #Roots(g, F) ge 1;
	  end if;
	end if;

/*
"z evaluations";
z; zz;
z - Roots(g, F)[2][1];
zz - Roots(g, F)[2][1];
Evaluate(g, Roots(g, F)[2][1]);
[Valuation(x, p) : x in Eltseq(Evaluate(g, z))];
[Valuation(x, p) : x in Eltseq(Evaluate(g, zz))];
*/
	// We do this coercion because we can get some strange random covering
	// structures for which it is really hard to find where they are coming
	// from so we just coerce here instead
	//g := PolynomialRing(E)!g;
	if  Debug then
	    "Before SubfieldFromBlock lifting loop";
	    Evaluate(g, zz);
	end if;
	zz_pow := [1, zz];
        vprint Subfields,4:"Building power list:";
        vtime Subfields,4: 
	for i := 2 to deg_g do
	    Append(~zz_pow, zz*zz_pow[i]);
	end for;
	cg := Coefficients(g);
	cdg := Coefficients(dg) cat [0 : i in [Degree(dg) .. deg_g - 1]];
	vtime Subfields,4: egzz := &+[cg[i]*zz_pow[i] : i in [1 .. deg_g + 1]];
	//egzz := Evaluate(g, zz);
	//assert egzz eq Evaluate(g, zz);
	while egzz ne 0 do
            vprint Subfields,4: "Next egzz iteration"; 
	    // check we still have the correct setup
	    if (assigned L`UseGalois and assigned L`UseGalois`Scale and not IsOne(L`UseGalois`Scale)) or Debug then
	      //"Loop", pp;
	      // [ Valuation(x, p) : x in Eltseq(E!Evaluate(g, zz))];
	      //[ Valuation(x, p) : x in Eltseq(w*E!Evaluate(Derivative(g), zz)-den)];
	      // [ Valuation(x, CoefficientRing(E)!!p) : x in Eltseq(E!Evaluate(g, zz))];
	      // [ Valuation(x, CoefficientRing(E)!!p) : x in Eltseq(w*E!Evaluate(Derivative(g), zz)-den)];
              vprint Subfields,4: "Eval 4";
	      vtime Subfields,4: assert E!Evaluate(g, zz) mod pE eq 0;
	      // w/den is the inverse of g'(z) mod pE
	      vtime Subfields,4: assert E!(Evaluate(Derivative(g), zz)*w) mod pE eq den;
	    end if;
	    if false then
	      assert E!Evaluate(g, zz) mod pE eq 0;
	      // w/den is the inverse of g'(z) mod pE
	      assert E!(Evaluate(Derivative(g), zz)*w) mod pE eq den;
    "passed assertions";
	    end if;
	    if not false and not IsExport() then
		if p_val gt 5000 then
		    "too much looping in SubfieldFromBlock", p_val, F;
		end if;
		if false and ISA(Type(pp), RngUPolElt) and Degree(pp) gt 1000 then 
		    error "too much in SubfieldFromBlock"; 
		end if;
	    end if;

	    // square the modulus
	    // but why do we divide by den 3 times??
	    pp *:= pp;
	    p_val *:= 2;
	    if not ISA(Type(pp), RngElt) then
		pp /:= den;
		pp /:= den;
		pp /:= den;
		pE := E!!pp;
	    else
		pp div:= den;
		pp div:= den;
		pp div:= den;
		pE := pp*E;
	    end if;
	    zz := func<|E!zz>();
	    //Content(pE);
	    zz := func<|zz mod pE>();
	    w := func<|E!w mod pE>();
	    nz := egzz*w;
	    if (assigned L`UseGalois and assigned L`UseGalois`Scale and not IsOne(L`UseGalois`Scale)) or false or Debug then
		if Type(CoefficientRing(F)) eq FldFun then
		  //assert forall{x : x in Eltseq(E!nz) | Numerator(x, CoefficientRing(E)) mod den eq 0};
		else
		  assert forall{x : x in Eltseq(E!nz) | Numerator(x) mod den eq 0};
		end if;
	    end if;
	    // Really wanted to multiply by w/den, so do the /den bit
	    if Type(CoefficientRing(F)) eq FldFun then
		nz := E![Numerator(x, CoefficientRing(E)) div den : x in Eltseq(E!nz)];
	    elif rel then
		nz := E![Numerator(x) / den : x in Eltseq(E!nz)];
	    else
		nz := E![Numerator(x) div den : x in Eltseq(E!nz)];
	    end if;
            nz := func<|E!nz mod pE>();
	    zz := zz - nz;
	    if Type(CoefficientRing(F)) eq FldFun then
		time R := ReconstructionEnvironment(p, p_val);
		zz := E![Reconstruct(CoefficientRing(E)!x, R) : x in Eltseq(zz)];
	    elif rel then
		R := ReconstructionEnvironment(p, p_val);
		zz := E![Reconstruct(CoefficientRing(E)!x, R : UseDenominator := false) : x in Eltseq(zz)];
	    end if;
	    zz_pow := [1, zz];
            vprint Subfields,4:"Comuting new power list";
            vtime Subfields,4: 
	    for i := 2 to deg_g do
        	Append(~zz_pow, zz*zz_pow[i]);
	    end for;
            vprint Subfields,4:"Evaluating cdg polynomial";
	    vtime Subfields,4: nz := w*&+[cdg[i]*zz_pow[i] : i in [1 .. deg_g]];
	    // Again really wanted to multiply by w/den so do the /den bit
	    if ((assigned L`UseGalois and assigned L`UseGalois`Scale and not IsOne(L`UseGalois`Scale)) or false or Debug) and Type(CoefficientRing(F)) ne FldFun then
	      assert forall{x : x in Eltseq(E!nz) | Numerator(x) mod den eq 0};
	    end if;
	    if Type(CoefficientRing(F)) eq FldFun then
		w := w*(2 - E![Numerator(x, CoefficientRing(E)) div den : x in Eltseq(nz)]);
	    elif rel then 
		w := w*(2 - E![Numerator(x) / den : x in Eltseq(nz)]);
	    else
		w := w*(2 - E![Numerator(x) div den : x in Eltseq(nz)]);
	    end if;
	    denpE := func<|(den*pE)>();
	    //Content(denpE);
	    w := func<|w mod denpE>();
            vprint Subfields,4:"Evaluating cg polynomial";
	    vtime Subfields,4: egzz := &+[cg[i]*zz_pow[i] : i in [1 .. deg_g + 1]];
	    //egzz := Evaluate(g, zz);

	end while;
    end if;
  end if;
 
    if Debug  then
      "SubfieldFromBlock almost out";
    end if;
    // We have the minimal polynomial of the primitive element
    // so we should use it in ext rather than recomputing it in sub
    if not true then
	subF := func<|sub<F | zz/_df>>();
    else
	if CoefficientField(F) cmpeq Rationals() then
	    g := Polynomial(CoefficientField(F), g);
            g := Evaluate(g, Parent(g).1*_df);
	    g := g/LeadingCoefficient(g);
	    g *:= LCM([Denominator(xx) : xx in Coefficients(g)]);
//real_g ne g;
	end if;
	//gn := LeadingCoefficient(g);
	//g := gn^(deg_g - 1)*Evaluate(g, Parent(g).1/gn);
	subF := ext<CoefficientField(F) | real_g : Global := false>;
	proc<|Embed(subF, F, zz/_df)>();
// if not IsExport() then "non export printing"; TES(F); TES(subF); "end ne"; end if;
    end if;

    vprintf Subfields,2: "Time for embedding: %o\n", Cputime(tt_emb); 
//    vprintf Subfields,4: "Embedding: %o\n", F!subF.1;

    if true or NumSub lt SubGraphLimit then
	assert Evaluate(DefiningPolynomial(subF), F!zz/_df) eq 0;
	assert Evaluate(DefiningPolynomial(subF), F!subF.1) eq 0;
	assert F!subF.1 eq F!zz/_df;
    else 
"NumSub = ", NumSub;
    end if;
//MinimalPolynomial(zz/_df); g;
//subF, _subF;
    if Opt and Degree(F) eq AbsoluteDegree(F) and Degree(subF) lt 5 then
	O, mp := OptimizedRepresentation(subF);
//"subF : ", subF;
//"O : ", O;
	O := sub<F | mp(O.1)>;
	if Valuation(Discriminant(DefiningPolynomial(O)), p) eq 0 then
	    subF := O;
	end if;
    end if;
    vprintf Subfields,1: "Time for SubfieldFromBlock: %o\n",Cputime(tt_sfb);
    return subF;
end function;

intrinsic OptimizedRepresentation(K::FldFun[FldFunRat]) -> FldFun, Map
  {}
  M := MaximalOrderFinite(K);
  require   IsAbsoluteOrder(M) : "Field must be an absolute extension";

  b:= ShortBasis(Divisor(1*M));

  i := 1;
  mf := false;
  e := false;
  fe := false;
  repeat
    if i le Degree(K) then
      n := b[i];
    else
      n := Random(b) + Random(b);
    end if;
    f := MinimalPolynomial(n);
    if Degree(f) eq Degree(K) then
      if mf cmpeq false then
        e := n;
        fe := f;
        mf := &+([ Degree(x) : x in Eltseq(f)]);
      else
        nf := &+([ Degree(x) : x in Eltseq(f)]);
        if nf lt mf then
          e := n;
          fe := f;
          mf := nf;
        end if;
      end if;
    end if;
    i +:=1;
  until i gt Degree(K)^2 and mf cmpne false;


  L := FunctionField(fe);
  mp := hom<L -> K | e>;

  return L, mp;
end intrinsic;

/*
intrinsic SFB(a,b,c) -> .
  {}
  return SubfieldFromBlock(a, b, c);
end intrinsic;
*/

procedure NextSubfields(F, S, L, e, s, subfields)
/*
This procedure implements the algorithm NextSubfields of van Hoeij and Klueners
F is the field we are computing subfields of
S is a sequence of tuples <gen_subf, B> where B is a set (block system)
which is the second 
entry of the tuples in the subfield lattice, holding a generating set for the 
subfields
L is a tuple of the top of the subfield lattice <LL, B> where LL is a subfield 
of F
e is as described in van Hoeij and Klueners (pg 3)
s is as described in van Hoeij and Klueners (pg 3)
subfields is the subfield lattice which we are adding subfields to
*/

//"NextSubfields In";
//F;
//S;
//L;
//e;
//s;
//subfields;
    for i := s + 1 to #S do
	if e[i] ne 0 then
	    continue;
	end if;
	//Step 1 : take intersection
	M := InternalGaloisSubfieldLatticeMeet(S[i][2], L[2]);
	et := [];
	append := true;

	if #M eq 1 then
	  continue;
	end if;

//"NextSubfields", i;
	// Step 2 : find the e tuple for M
	// and check the condition on the e[j] as in step 3
	for j := 1 to i - 1 do
	    // assign et[j]
	    if InternalGaloisSubfieldLatticeSubset(M, S[j][2]) then
		Append(~et, 1);
		if et[j] gt e[j] then
		    append := false;
		end if;
	    else 
		Append(~et, 0);
	    end if;
	end for;
	for j := i to #S do 
	    // assign et[j]
	    if InternalGaloisSubfieldLatticeSubset(M, S[j][2]) then
		Append(~et, 1);
	    else 
		Append(~et, 0);
	    end if;
	end for;
	// Step 3 : If condition on e[j] was satisfied then keep M
	// (intersect the actual fields rather than lattice stuff)
	// and recurse
	if append then
	    df := DefiningPolynomial(F);
	    //if not false and IsMonic(df) and LCM([Denominator(c) : c in Coefficients(df)]) eq 1 then
	    if M eq S[i][2] then
		LL := S[i][1];
	    elif exists(j){j: j in [1 .. #subfields`Fields] | M eq subfields`Fields[j][2]} then
		LL := subfields`Fields[j][1];
	    else
		if true or assigned subfields`UseGalois then
		    LL := SubfieldFromBlock(F, M, subfields : NumSub := #subfields`Fields);
		else
		    vtime Subfields : LL := IntersectionFunc(L[1], S[i][1], F);
		end if;
		f := InternalGaloisSubfieldLatticeAddField(subfields, LL: B := M);
		assert f;
	    end if;
	    NextSubfields(F, S, <LL, M>, et, i, subfields);
	end if;
    end for;
//"NextSubfields Out";
end procedure;

function SUBSET(K, F1, F2)
// Return whether F2 is a subset of F1 where F1 and F2 are subfields of K
    A1, m1 := Algebra(K, F1);
    A2, m2 := Algebra(K, F2);

    f1 := MinimalPolynomial(m1(K.1));
    f2 := MinimalPolynomial(m2(K.1));

    d1 := Discriminant(F1);
    d2 := Discriminant(F2);
    dk := Discriminant(K);

    p := RandomPrime(7);

    repeat
	while true do 
	    if Gcd(p, d1) eq 1 and Gcd(p, d2) eq 1 and Gcd(p, dk) eq 1 then
		/* 
		check p doesn't divide denominators of coefficients
		of f1 and f2
		*/
		d := &*[Denominator(c) : c in Coefficients(f1)];
		if d mod p ne 0 then
		    d := &*[Denominator(c) : c in Coefficients(f2)];
		    if d mod p ne 0 then
			break;
		    end if;
		end if;
	    end if;
	    p := NextPrime(p + 1);
	end while;

	// p;
	D := Decomposition(K, p);
	// D;
	// [Degree(P[1]) : P in D];
	p := NextPrime(p + 1);
    until exists(P){P : P in D | Degree(P[1]) eq 1};

    P := P[1];
    F := ResidueClassField(P);

    f1 := Polynomial(F, [Evaluate(c, P) : c in Coefficients(f1)]);
    f2 := Polynomial(F, [Evaluate(c, P) : c in Coefficients(f2)]);

    if f1 mod f2 eq 0 then
	return true;
    else
	return false;
    end if;
end function;

intrinsic Subfields(F::FldAlg : Current := false, Al := "Default", Proof := 1) -> SeqEnum
{Return the subfields of the algebraic field F};
    require IsSimple(F) : "Field must be a simple extension";
    if Current or (assigned F`SubfieldLattice and F`SubfieldLattice`Complete) then
	if assigned F`SubfieldLattice then
	    l := F`SubfieldLattice;
	    return [<x[1], Coercion(x[1], F)> : x in l`Fields], l;
	else
	    l := InternalGaloisSubfieldLatticeCreate(F);
	    return [], l;
	end if;
    end if;
    if Al eq "Klueners" and CoefficientField(F) eq Rationals() then 
	// Could improve this to put the subfield lattice into the internal stuff?
	l := InternalGaloisSubfieldLatticeCreate(F);
	if not l`Complete then
	    S := InternalSubfields(F);
	    for s in S do 
		_ := InternalGaloisSubfieldLatticeAddField(l, s[1]);
	    end for;
	    l`Complete := true;
	    l`GeneratingComplete := true;
	end if;
	return [<x[1], Coercion(x[1], F)> : x in l`Fields], l;
	return S, l;
    end if;
    // Can't store the subfields of relatives yet - not internally anyway
    if Al in {"KvH", "KluenersvanHoeij"} or CoefficientField(F) ne Rationals() then
	return SubfieldsOfAll(F : Proof := Proof);
    end if;
    assert CoefficientField(F) eq Rationals();
    require Al eq "Default" : "Parameter Al must be one of \"Default\", \"Klueners\", \"KluenersvanHoeij\"";
    return SubfieldsOfAll(F : OptAlg := true, Proof := Proof);
end intrinsic;

function triple_relative_subfields(F : Current := false)
    if Type(F) eq FldFun then
	A := RationalExtensionRepresentation(CoefficientField(F));
	AF := ext<A | DefiningPolynomial(F)>;
	subfields := Subfields(AF);
    else 
	A := AbsoluteField(CoefficientField(F));
	AF := ext<A | DefiningPolynomial(F)>;
	subfields := Subfields(AF : Current := Current);
    end if;
    //return [<x[1], Coercion(x[1], F)> : x in l`Fields], l;
    S := [CartesianProduct(PowerStructure(Type(F)), PowerStructure(Map))|];
    for x in subfields do
	subf := sub<F | F!Eltseq(AF!x[1].1)>;
	Append(~S, <subf, Coercion(subf, F)>);
    end for;
    return S;
end function;

intrinsic Subfields(F::FldFun[FldFun[FldFun]]) -> SeqEnum
{Return the subfields of the function field F};
    require IsSimple(F) : "Field must be a simple extension";
    return triple_relative_subfields(F);
end intrinsic;

intrinsic Subfields(F::FldAlg[FldAlg[FldAlg]] : Current := false) -> SeqEnum
{Return the subfields of the algebraic field F};
    require IsSimple(F) : "Field must be a simple extension";
    return triple_relative_subfields(F : Current := Current);
end intrinsic;

intrinsic Subfields(F::FldFun[FldFunRat[FldFin]]) -> SeqEnum
{Return the subfields of the global function field F};
    require IsSimple(F) : "Field must be a simple extension";
    return SubfieldsOfAll(F);
end intrinsic;

intrinsic Subfields(F::FldFun[FldFun]) -> SeqEnum
{Return the subfields of the function field F represented relatively};
    require IsSimple(F) : "Field must be a simple extension";
    return SubfieldsOfAll(F);
end intrinsic;

// Use FldAlg[FldAlg[FldRat]] for any higher towers as per Subfields
intrinsic GeneratingSubfields(F::FldAlg : Proof := 1) -> SeqEnum
{Return the generating subfields of the algebraic field F};
    l := InternalGaloisSubfieldLatticeCreate(F);
    g := GeneratingSubfieldsFunc(F, l : Proof := Proof, OptAlg := true);
    if g cmpeq false then
	assert CoefficientField(F) eq Rationals();
	_, l := Subfields(F : Al := "Klueners");
    end if;
    g := InternalSubfieldLatticeGetGeneratingSubfields(l);
    return g;
end intrinsic;

function triple_relative_generating_subfields(F)
    if Type(F) eq FldFun then
	A := RationalExtensionRepresentation(CoefficientField(F));
	AF := ext<A | DefiningPolynomial(F)>;
    else 
	A := AbsoluteField(CoefficientField(F));
	AF := ext<A | DefiningPolynomial(F)>;
    end if;
    subfields := GeneratingSubfields(AF);
    //return [<x[1], Coercion(x[1], F)> : x in l`Fields], l;
    S := [];
    for x in subfields do
	subf := sub<F | F!Eltseq(AF!x.1)>;
	Append(~S, subf);
    end for;
    return S;
end function;

intrinsic GeneratingSubfields(F::FldAlg[FldAlg[FldAlg]]) -> SeqEnum
{Return the generating subfields of the algebraic field F};
    return triple_relative_generating_subfields(F);
end intrinsic;

// Use FldFun[FldFun[FldFunRat]] for any higher towers as per Subfields
intrinsic GeneratingSubfields(F::FldFun) -> SeqEnum
{Return the generating subfields of the function field F};
    l := InternalGaloisSubfieldLatticeCreate(F);
    g := GeneratingSubfieldsFunc(F, l);
    g := InternalSubfieldLatticeGetGeneratingSubfields(l);
    return g;
end intrinsic;

intrinsic GeneratingSubfields(F::FldFun[FldFun[FldFun]]) -> SeqEnum
{Return the generating subfields of the function field F};
    return triple_relative_generating_subfields(F);
end intrinsic;

function generating_subfields_as_lattice(F, l : Proof := 1)
    S := GeneratingSubfieldsFunc(F, l : Proof := Proof);
    S := InternalSubfieldLatticeGetGeneratingSubfields(l);
    return l, [<s, Coercion(s, F)> : s in S];
end function;

intrinsic GeneratingSubfieldsLattice(F::FldAlg : Proof := 1) -> Any, SeqEnum
{Return the generating subfields of F in a subfield lattice};
    require CoefficientField(F) cmpeq Rationals() or CoefficientField(CoefficientField(F)) cmpeq Rationals() : "Extension must be absolute or simple relative";
    l := InternalGaloisSubfieldLatticeCreate(F);
    return generating_subfields_as_lattice(F, l : Proof := Proof);
end intrinsic;

intrinsic GeneratingSubfieldsLattice(F::FldFun) -> Any, SeqEnum
{Return the generating subfields of F in a subfield lattice};
    require Type(CoefficientField(F)) ne FldFun or Type(CoefficientField(CoefficientField(F))) ne FldFun : "Extension must be absolute or simple relative";
    l := InternalGaloisSubfieldLatticeCreate(F);
    return generating_subfields_as_lattice(F, l);
end intrinsic;

intrinsic GeneratingSubfieldsLattice(F::FldFun, S::GaloisData) -> Any, SeqEnum
{Return the generating subfields of F in a subfield lattice};
    require Type(CoefficientField(F)) ne FldFun or Type(CoefficientField(CoefficientField(F))) ne FldFun : "Extension must be absolute or simple relative";
    l := InternalGaloisSubfieldLatticeCreate(F, S);
    return generating_subfields_as_lattice(F, l);
end intrinsic;

intrinsic 'meet'(F::FldAlg, K::FldAlg) -> FldAlg
{Return the intersection of F and K if they have a covering structure};

    has, FK := ExistsCoveringStructure(F, K);
    require has : "Fields must have a covering structure";
    return IntersectionFunc(F, K, FK);

end intrinsic;

