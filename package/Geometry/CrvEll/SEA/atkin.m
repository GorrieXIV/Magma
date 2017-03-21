freeze;

import "brent-kung.m": EqualSplittingDegree;
import "schoof.m": SignedTrace;

procedure TorsionModuleTraceAtkin(~T)
    // "La methode d'Atkin". 
    // Finds candidates for the trace of E mod a power of the prime 
    // in this prime_block.  The power is incremented by one (to 1) 
    // each time this function is called.  Assumes prime type is Atkin.

    error if (assigned T`trace), "Trace already found.";
    error if (not assigned T`prime_type), "Unknown type for this prime.";
    TIME := Cputime();


    error if (T`prime_exponent ne 0), 
        "Can't handle prime powers as Atkin primes.";
    T`prime_exponent +:= 1;
    ell := T`prime;
    j := jInvariant(T`E);
    FF := BaseRing(T`E);
    q := #FF;
    PPF := PolynomialRing(FF);
    PPFJ<F,J> := PolynomialRing(FF,2);
    modular_poly := PPF!UnivariatePolynomial(
        Evaluate(PPFJ!T`modular_eqn,2,j) );

    if (T`prime_type eq "Atkin") then
	// Find possible values of r.
	jac_sym := JacobiSymbol(q,ell);
	deg_poly := Degree(modular_poly);
	r_vals := [ Integers() | ];
	for r in [rr : rr in Divisors(deg_poly) | rr ge 2] do
	    if not (ell gt 2 and jac_sym ne (-1)^(deg_poly div r)) then
		Append(~r_vals, r);
	    end if;
	end for;

	vprint SEA, 4: "Modular_eqn degree:", Degree(modular_poly);
	vprint SEA, 4: "Possible r values:", r_vals;

	if #r_vals eq 1 then
	   r := r_vals[1];
	elif true then
	    vprint SEA, 4: "Performing Brent-Kung evaluations";
	    x_pow := T`x_pow;
	    x := Parent(x_pow).1; 
	    // assert x_pow eq Modexp(x,q,modular_poly);
	    r_max_test := Max(Exclude(r_vals,Max(r_vals)));
	    BK_Time := Cputime();
	    if true then
		IndentPush();
		r := EqualSplittingDegree(modular_poly, x_pow, r_vals);
		IndentPop();
	    else
		// The original Brent-Kung:
		vtime SEA, 4: 
		    BKExp := ModularCompositions(x_pow,modular_poly,r_max_test);
		for i in [1..#r_vals] do 
		    r := r_vals[i]; 
		    if i eq #r_vals then 
			break; 
		    end if; 
		    if (BKExp[r] mod modular_poly) eq x then 
			// assert BKExp[r] eq Modexp(x,q^r,pl); 
			break; 
		    end if; 
		end for; 
	    end if;
	    vprint SEA, 4: 
                "Total Brent-Kung time:", Cputime(BK_Time);
	else 
	   // e.g. No Brent-Kung implementation.
	   vprint SEA, 4: "Doing complete factorization...";
	   vtime  SEA, 4: r := Degree(Factorization(modular_poly)[1][1]);
	end if;
	vprint SEA, 4: "Found splitting degree r =", r;

	// Use the multiplicative relations in GF(ell^2) for the 
	// eigenvalues of Frobenius: 
	//    (1) Log(a2) = ell*Log(a1) mod (ell^2 - 1);
	//    (2) a (ell+1) = Log(q) = Log(a1*a2); 
	//    (3) r = Order(a1/a2);
	// Then decompose: 
	//    Z/(ell^2-1)Z ---> Z/(ell-1)Z x Z/(ell+1)Z ---> Z/2Z.
	//    t = Log(a1)  |-->        ( a , b )             
	// where a is fixed by (2) and b runs over the elements s*(Z/rZ)^* 
	// for s = (ell+1) div r in the same mod 2 congruence class as a.
	// 
	K := FiniteField(ell^2);
	w := PrimitiveElement(K);
	a := Log(K!q) div (ell+1);
	s := (ell + 1) div r; 
	b_vals := { s*u : u in [1..r-1] | GCD(u,r) eq 1 };
	eigen_logs := { a + i*(ell-1) : i in [0..ell] 
	    | (a + i*(ell-1)) mod (ell+1) in b_vals };
	trace_list := SetToSequence(
	   { Integers()!Trace(w^t) : t in eigen_logs } );
	vprintf SEA, 4:
	  "Possible values for t mod %o are %o\n", ell, trace_list;
	if #trace_list eq 1 then
	    T`trace := trace_list[1];
	    T`entropy := -(T`prime_exponent)*Log(T`prime); 
	else
	    T`trace := trace_list;
	    T`entropy := Log(#trace_list) - 
		(T`prime_exponent)*Log(T`prime); 
	end if;
    else
        error if (T`prime_type ne "Elkies"), 
            "Inappropriate non-Atkin, non-Elkies prime in Atkin.";  

        FF := GF(ell); 
        if (JacobiSymbol(q,ell) eq -1) then  
            r_vals := [ r : r in Divisors(ell-1) |   
                (r ne 1) and (r mod 2) eq 0 ];  
        else  
            r_vals := [ r : r in Divisors(ell-1) |   
                (r ne 1) and ((ell-1) div r) mod 2 eq 0 ];  
        end if; 
        if #r_vals eq 1 then
           r := r_vals[1];
        else 
            r_max_test := Max(Exclude(r_vals,Max(r_vals)));
            x_pow := T`x_pow;
            x := Parent(x_pow).1; 
            vprint SEA, 4: "Removing Elkies factors in Atkin:"; 
            vtime SEA, 4:  
            modular_fact := modular_poly div GCD(modular_poly,x_pow-x);
            BK_Time := Cputime();
            vprint SEA, 4: "Performing Brent-Kung evaluations";
            IndentPush();
            r := EqualSplittingDegree(modular_poly, x_pow, r_vals);
            IndentPop();
            vprint SEA, 4: "Brent-Kung time:", Cputime(BK_Time);
        end if;

        trace_list := SetToSequence( { Integers()!(a + q/a) 
            : a in FF | (a ne 0) and Order(a^2/q) eq r } ); 
        vprintf SEA, 4:
            "Possible values for t mod %o are %o\n", ell, trace_list;
        if #trace_list eq 1 then
            T`trace := trace_list[1];
            T`entropy := -(T`prime_exponent)*Log(T`prime); 
        else
            T`trace := trace_list;
            T`entropy := Log(#trace_list) - 
                 (T`prime_exponent)*Log(T`prime); 
        end if;
    end if; // end of Atkin v. Elkies if statement.
    return;
end procedure;

procedure TorsionModuleTraceRamified(~T)
    // Finds candidates for the trace of E mod the prime 
    // power of the torsion module.

    assert not assigned T`trace;

    T`prime_exponent := 1;
    FF := BaseRing(T`E);
    q := #FF;
    ell := T`prime;
    a := Sqrt(GF(ell)!q);
    trace_vals := SetToSequence({Integers() | 2*a, -2*a});
    if #trace_vals eq 1 then
        T`trace := trace_vals[1];
        vprint SEA, 5: "Trace = ", T`trace, "mod", ell; 
    elif ell eq 3 then
        lambda := Integers()!a;
        T`kernel_poly := 
            Factorization(DivisionPolynomial(T`E,3))[1][1];
        SignedTrace(~T,lambda);
    else
        vprintf SEA, 5: 
             "Possible values for t mod %o are %o\n", ell, trace_vals;
	T`trace := trace_vals;
    end if;
end procedure;

procedure TorsionModuleTraceNonmaximal(~T)
    // Finds candidates for the trace of E mod the prime 
    // power of the torsion module.  

    assert (not assigned T`trace);

    T`prime_exponent := 2;
    FF := BaseRing(T`E);
    K := ResidueClassRing(T`prime);
    R := ResidueClassRing(T`prime^2);
    a := R!(Sqrt(K!#FF));
    s := R!(a + (R!#FF)*(a^(-1)));
    trace_list := SetToSequence({Integers() | s, -s});
    vprint SEA, 4:
	"Possible values of t mod", (T`prime)^2, "are", trace_list;
    if #trace_list eq 1 then
        T`trace := trace_list[1];
        T`entropy := -2*Log(T`prime); 
    else
	T`trace := trace_list;
        T`entropy := Log(2) - 2*Log(T`prime); 
    end if;
end procedure;
