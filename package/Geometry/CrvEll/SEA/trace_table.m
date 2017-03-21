freeze; 

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           TRACE TABLES                             //
//            (Collecting data of various 'torsion modules')          //
//                  Based on code of Richard Rannard                  //
//                      Rewritten by David Kohel                      //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "shanks.m": MakeResidues, ListPartition, TraceTableBSGS; 
import "torsion_module.m": TorsionModule, TorsionModuleType,
       TorsionModuleTrace, TorsionModuleTracePower;

// Bound beyond which no modular equations are available for
// the current FULL modular database.
MaxModularLimit := 828;
Infty := 2^31;

RR := RealField();
R8 := RealField(8);

////////////////////////////////////////////////////////////////////////
//                Definition of Trace Table Record                    //
////////////////////////////////////////////////////////////////////////

SymModTors := recformat< 
    E              : CrvEll,    // The elliptic curve.
    log_weil_bound : FldReElt,  // The logarithmic length of the trace range.
    multi_places   : SeqEnum,   // TorsionModules with multiple trace residues.
    unique_places  : SeqEnum,   // TorsionModules with a unique trace defined.
    unique_modulus : RngIntElt, // Product of the primes in unique_trace
    unique_trace   : RngIntElt, // Trace modulo unique_modulus.
    R1             : SeqEnum,   // First subset of multi_places.
    R2             : SeqEnum,   // Second subset of multi_places.
    multi_modulus_1 : RngIntElt, // The product of prime powers in R1.
    multi_modulus_2 : RngIntElt, // The product of prime powers in R2.
    smooth_abort    : BoolElt, 
    // Parameters for use in deciding whether to type a new prime, 
    // process an Atkin prime, or go to a power of an Elkies prime.
    PrimeFactor    : RngIntElt, // Relative time to type a prime.
    AtkinFactor    : RngIntElt, // Relative time to process Atkin prime.
    PowerFactor    : RngIntElt  // Relative time for Elkies prime power.
>;

////////////////////////////////////////////////////////////////////////
//                      Trace Table Constructor                       //
////////////////////////////////////////////////////////////////////////

function TraceTable(E)
    // Trace table constructor.

    FF := BaseRing(E);
    return rec< SymModTors | 
                E := E, 
                unique_places := [  ], 
                unique_modulus := 1, 
                unique_trace := 0, 
                multi_places := [  ],
                smooth_abort := false,
                log_weil_bound := RR!Log(10,4*Sqrt(#FF))
             >;
end function;

////////////////////////////////////////////////////////////////////////
//                  Member functions for TraceTable                   //
////////////////////////////////////////////////////////////////////////

procedure InsertTorsionModule(~TT,T)
    // (Re)insert a torsion module in the table.

    // Check first if we are updating power of prime.
    multi_primes := [ T`prime : T in TT`multi_places ];
    unique_primes := [ T`prime : T in TT`unique_places ];
    // Remove first: may have changed entropy or moved between 
    // unique and multiply defined trace lists.
    if T`prime in multi_primes then 
        i := Index(multi_primes,T`prime);
        Remove(~(TT`multi_places),i);
    elif T`prime in unique_primes then
        i := Index(unique_primes,T`prime);
        Remove(~(TT`unique_places),i);
    end if;

    // Now insert.
    if (Type(T`trace) eq RngIntElt) then
        T`entropy := -T`prime_exponent * Log(10,T`prime);
        Append(~(TT`unique_places),T);
    else 
        assert #(T`trace) gt 1;
        T`entropy := Log(10,#T`trace) - T`prime_exponent * Log(10,T`prime);
        i := 1;
        while i le #(TT`multi_places) and 
           T`entropy gt (TT`multi_places[i])`entropy do
           i +:= 1;
        end while;
        Insert(~(TT`multi_places),i,T);
    end if;
end procedure;

procedure TraceTableProcessUTPrimes(~TT)
    // Process those primes for which we know an exact residue 
    // of the trace. 
    if #TT`unique_places eq 0 then
        TT`unique_modulus := 1;
        TT`unique_trace := 0;
    else
        residue_list := [ T`trace : T in TT`unique_places ];
        modulus_list := [ T`prime^T`prime_exponent 
           : T in TT`unique_places ];
        TT`unique_modulus := &*(modulus_list); 
        TT`unique_trace := CRT(residue_list,modulus_list);
    end if;
end procedure;

procedure TraceTableProcessMTPrimes(~TT)
    // Process the primes for which we know several values of the trace
    // modulo that prime.

    ProcessTyme := Cputime();

    res_list_1, moduli_1, res_list_2, moduli_2 := ListPartition(TT);

    m0 := TT`unique_modulus; 
    t0 := TT`unique_trace;
    m1 := &* moduli_1; 
    m2 := &* moduli_2; 
    TT`multi_modulus_1 := m1;
    TT`multi_modulus_2 := m2;

    vprint SEA, 4: "Constructing first residue list.";

    max_bound := m1 div 2;  
    vtime SEA, 4:
    TT`R1 := MakeResidues(
        res_list_1, moduli_1, m2, m0, t0, max_bound); 

    vprint SEA, 4: "Constructing second residue list.";

    max_bound := m2;  

    vtime SEA, 4:
    if #moduli_2 eq 0 then
        TT`R2 := [ 0 ];
    else
        TT`R2 := MakeResidues(
            res_list_2, moduli_2, m1, m0, t0, max_bound);
    end if;
    vprint SEA, 3:
        "Total residue construction time:", Cputime(ProcessTyme);
end procedure;

////////////////////////////////////////////////////////////////////////
//          FUNCTIONS FOR THE TOP-LEVEL CONTROL OF ALGORITHM          //
////////////////////////////////////////////////////////////////////////

function GetModularLimit()

    // First 2 Atkin modular databases should always exist!
    // Try now and let the error be thrown to the user
    // to get the basic library files/correct library path.
    ok := ExistsModularCurveDatabase("Atkin",1);
    ok := ExistsModularCurveDatabase("Atkin",2);
    i := 2; ok := true;
    while ok do
	i +:=1;
	try
	  ok := ExistsModularCurveDatabase("Atkin",i);
	catch e
	  ok := false;
	end try;
    end while;

    i -:= 1; // max index of Atkin files available.
    mod_lim := Min(200*i,MaxModularLimit);
    if mod_lim lt MaxModularLimit then
	// extra optional modular databases available
        // set mod_lim to first prime missing.
        mod_lim := NextPrime(mod_lim : Proof := false);
    end if;
    return mod_lim;

end function;

// These functions deal with the decisions about what primes are
// processed.  The algorithm is based in Lercier's dynamic strategy in
// his thesis.

// The timings are based on the assumption that the time taken 
// to find x^(q^r) mod g is proportional to r and deg(g)^2.

function TimeForNextPrime(TT,prime, ModularLimit);
    // Returns an integer corresponding to the time to type the next prime

    ell := NextPrime(prime : Proof := false);
    if ell gt ModularLimit then
        return Infty;
    elif ell eq ModularLimit then
	print "\n***************************************************";
	print "***************************************************\n";
	printf "Warning! There is no Modular data for auxiliary prime %o.\n",ell;
	print "Magma can continue processing but SEA will be much more";
	print "efficient for this elliptic curve if you install the";
	print "additional Modular Equation library. This is available";
	print "on the Magma website as ModEqA.tar.gz. If you do not have";
	print "permission to download this file but are still interested in";
	print "extending the modular database, please contact us at";
	print "magma@maths.usyd.edu.au\n";
	print "***************************************************";
	print "***************************************************\n";
        return Infty;
    else 
        return (ell + 1)^2 * TT`PrimeFactor;
    end if;
end function;

function TimeForPower(TT)
    // Returns an integer corresponding to the time to find the trace
    // mod a power of an existing trace'd Elkies prime.
    // Returns the prime_block to process.

    tyme := Infty;
    min_time := Infty;
    min_index := 0;
    for index in [1..#(TT`unique_places)] do
        T := TT`unique_places[index];
        ell := T`prime;
        n := T`prime_exponent + 1;
        if (ell eq 2) and (T`char_type eq 0) or 
            (T`prime_type eq "Elkies" and 
                Characteristic(BaseRing(TT`E)) gt (2*T`prime+1)) then
            // Sum recursively over all tymes [sic] to account 
            // for the cumulative time-to-date for this prime.
            tyme := ((ell^n - ell^(n-1)) div 2)^2;
            if ell eq 2 then tyme := (3*tyme) div 2; end if; 
            if tyme lt min_time then
                min_index := index;
                min_time := tyme;
            end if;
        end if;
    end for;
    return min_time * TT`PowerFactor, min_index;
end function;

procedure TraceTableGetPrimeData(~TT :
    MaxSmooth := Infinity(), AbortLevel := 0)
    // Get data on the primes.

    VerboseLevel := GetVerbose("SEA");

    FF := BaseRing(TT`E);
    p := Characteristic(FF);
    smooth0 := 1;
    smooth1 := 1;
    log_modulus := RR!0;
    log_good_modulus := RR!0;
    total_entropy := RR!0;
    // Settign entropy bounds to determine exit to Shanks step.
    log2ff := Log(2,#FF);
    entropy_diff := RR!( 1.5 );
    if 2 lt p and p lt 60 then
	// If the characteristic is small then there may be 
	// no or few Elkies primes to work with.
	max_entropy := RR! (14.6 + log2ff/10 )/Log(10);
	entropy_diff +:= RR! (3*log2ff/40)/Log(10);
    elif log2ff lt 200 then
        max_entropy := RR! (9.6 + log2ff/20)/Log(10);
    else
        max_entropy := RR! (14.6 + log2ff/40 )/Log(10);
    end if;
    max_entropy := Min(max_entropy,10.5);
    low_entropy := RR!(max_entropy - entropy_diff);
    
    vprintf SEA, 3: "Computing torsion data for\n%o\n", TT`E;
    if VerboseLevel ge 3 then 
        printf "Setting low_entropy to %o\n", R8!low_entropy;
        printf "Setting max_entropy to %o\n", R8!max_entropy;
    end if;

    ell := 2;
    // Process prime 2 separately.
    T := TorsionModule(TT`E,2);
    if Characteristic(FF) eq 2 then
        T`prime_type := "Elkies";
        TorsionModuleTrace(~T);
        InsertTorsionModule(~TT,T); 
        log_modulus +:= T`prime_exponent * Log(10,2);
        // Curve is not supersingular, so order is even:
        smooth0 *:= 2; 
        smooth1 *:= 2; 
    else
        TorsionModuleType(~T);
        if T`prime_type eq "Atkin" then
            T`trace := 1;
        else
            T`trace := 0;
            smooth0 *:= 2; 
            smooth1 *:= 2; 
        end if;
        T`prime_exponent := 1;
        T`entropy := -Log(10,2);
        InsertTorsionModule(~TT,T); 
        log_modulus +:= Log(10,2);
    end if;
    vprint SEA, 3: "-----------------------------------------";
    if VerboseLevel ge 2 then
        "Computing trace mod 2.";
        "Prime 2 is", T`prime_type;
        printf "Trace is %o mod 2.\n", T`trace;
    end if;
    vprint SEA, 3: "-----------------------------------------";
    if AbortLevel eq 0 then
        if smooth0 gt MaxSmooth then
            TT`smooth_abort := true;
            return;
        end if;
    elif AbortLevel eq 1 then
        if smooth0 gt MaxSmooth and smooth1 gt MaxSmooth then
            TT`smooth_abort := true;
            return;
        end if;
    else // (AbortLevel eq 2)
        if smooth0 gt MaxSmooth or smooth1 gt MaxSmooth then
            TT`smooth_abort := true;
            return;
        end if;
    end if;

    // ENTERING TRACE COLLECTION ROUTINE.
    // We really have two algorithms here.  If the characteristic
    // is large or has char 2, we use all the machinery, but if we
    // are working over any other field we just use the Atkin primes.
    // In the latter case the "time" variables are used to ensure
    // only Atkin primes get processed.
    // BEGIN:
    RunningTyme := Cputime();
    ModularLimit := GetModularLimit();
    bRML := false;        // ReachedModularLimit?
    repeat
        PrimeTyme := Cputime();
	if bRML then
	    next_prime_time := Infty;
	else
            next_prime_time := TimeForNextPrime(TT,ell,ModularLimit);
	    if next_prime_time eq Infty then 
		bRML := true;
	    end if;
	end if;
        elkies_power_time, power_index := TimeForPower(TT);
	/*
	if VerboseLevel ge 3 then 
            printf "Cost for typing next prime  %o\n", next_prime_time;
            printf "Cost for Elkies prime power %o\n", elkies_power_time;
            "-----------------------------------------";
	end if;
	*/
        if next_prime_time le elkies_power_time then
            TypingTyme := Cputime();
            ell := NextPrime(ell : Proof := false);
            if ell eq Characteristic(FF) then
                // Skip the characteristic of the base ring.
                ell := NextPrime(ell : Proof := false);
            end if;
            if VerboseLevel ge 1 then 
                print "Computing trace mod", ell;
            end if;
            // Check we can actually get the mod eqn for this prime
            T := TorsionModule(TT`E, ell);
            TorsionModuleType(~T);
            if (T`prime_type eq "Ramified") then
                TorsionModuleTrace(~T);
                InsertTorsionModule(~TT,T);
                if Type(T`trace) eq RngIntElt then
                    if (#FF - T`trace + 1) mod ell eq 0 then
                        smooth0 *:= ell;
                    elif (#FF + T`trace + 1) mod ell eq 0 then
                        smooth1 *:= ell;
                    end if;
                end if;
                log_modulus +:= Log(10,ell);
            end if;
            if VerboseLevel ge 2 then
                printf "Prime %o is %o.\n", ell, T`prime_type;
                printf "Characterization time: %o\n", Cputime(TypingTyme);
	    end if;
            if T`prime_type in {"Atkin","Elkies"} then
                TraceTyme := Cputime();
                if VerboseLevel ge 2 then
                    if T`prime_type eq "Atkin" then
                        if log_modulus lt TT`log_weil_bound then
                            "Processing Atkin prime", ell;
                        end if;
                    elif T`prime_type eq "Elkies" then
			if (p gt 2 and p le (2*ell+1)) or 
                            ell gt ModularLimit then
                            "Processing as Atkin prime", ell;
                        else
                            "Processing Elkies prime", ell;
                        end if;
                    end if;
                end if;
                if T`prime_type eq "Elkies" or
                    log_modulus lt TT`log_weil_bound then
                    TorsionModuleTrace(~T);
                    InsertTorsionModule(~TT,T);
		    if T`prime_type ne "Pathological" then /*may have changed!*/
                      if Type(T`trace) eq RngIntElt then
                        if (#FF - T`trace + 1) mod ell eq 0 then
                            smooth0 *:= ell;
                        elif (#FF + T`trace + 1) mod ell eq 0 then
                            smooth1 *:= ell;
                        end if;
                      end if;
                      log_modulus +:= Log(10,ell);
		    end if;
                end if;
                if VerboseLevel ge 2 then
		    if T`prime_type eq "Ramified" then
                        print "Number of trace candidates:", 2;
		    elif (not assigned T`trace) or (T`prime_type eq "Pathological") then
			n := (ell-1) div 2;
			print "Number of trace candidates:", n;
		    elif Type(T`trace) eq RngIntElt then
                        printf "Trace %o mod %o.\n", T`trace, ell;
		    else 
			print "Number of trace candidates:", #T`trace;
                    end if;
                    print "Trace computation time:", Cputime(TraceTyme);
                end if;
            end if;
        elif elkies_power_time le next_prime_time then
            PowerTyme := Cputime();
            T := TT`unique_places[power_index];
            exp := T`prime_exponent;
            if VerboseLevel ge 2 then 
                printf "Processing prime power %o^%o\n", T`prime, exp+1;
            end if; 
            TorsionModuleTracePower(~T);
            InsertTorsionModule(~TT,T); 
            assert T`prime_exponent eq exp+1;
            if Type(T`trace) eq RngIntElt then
                if (#FF - T`trace + 1) mod T`prime^(exp+1) eq 0 then
                    smooth0 *:= T`prime;
                elif (#FF - T`trace + 1) mod T`prime^(exp+1) eq 0 then
                    smooth1 *:= T`prime;
                end if;
            end if;
            log_modulus +:= Log(10,T`prime);
            if VerboseLevel ge 2 then 
                print "Trace computation time:", Cputime(PowerTyme);
             end if;
        end if;
	log_good_modulus :=
	    &+[ RR | T`prime_exponent *
	        Log(10,T`prime) : T in TT`unique_places ];
        total_entropy := &+[ RR | T`entropy : T in TT`unique_places ];
        k := 0;
        while k lt #(TT`multi_places) and 
            log_good_modulus lt Min(TT`log_weil_bound,log_modulus) do
            k +:= 1;
            T := TT`multi_places[k];
            total_entropy +:= T`entropy;
            log_good_modulus +:= Log(10,T`prime);
        end while;
        if AbortLevel eq 0 then
            if smooth0 gt MaxSmooth then
                TT`smooth_abort := true;
                return;
            end if;
        elif AbortLevel eq 1 then
            if smooth0 gt MaxSmooth and smooth1 gt MaxSmooth then
                TT`smooth_abort := true;
                return;
            end if;
        else // (AbortLevel eq 2)
            if smooth0 gt MaxSmooth or smooth1 gt MaxSmooth then
                TT`smooth_abort := true;
                return;
            end if;
        end if;
        if VerboseLevel ge 2 then
            "Total prime time =", Cputime(PrimeTyme);
            "-----------------------------------------";
        end if;
	if VerboseLevel ge 2 then
	    printf "Current run time = %o\n", Cputime(RunningTyme);
	    "-----------------------------------------";
	end if;
        if VerboseLevel ge 3 then 
	    "CRT Moduli:";
	    "    Log(Elkies) = ",
                &+[ R8 | T`prime_exponent *
                    Log(10,T`prime) : T in TT`unique_places ];
            "    Log(Atkin)  = ",
                &+[ R8 | T`prime_exponent *
                    Log(10,T`prime) : T in TT`multi_places ];
            if log_modulus gt TT`log_weil_bound then 
            "    Log(Good)   = ", R8!log_good_modulus;
            end if;
            "    Log(Total)  = ", R8!log_modulus;
            "    Log(Weil)   = ", R8!TT`log_weil_bound;
	    "Entropy:";
            relative_entropy := total_entropy + log_good_modulus;
            "    Absolute    =" , R8!total_entropy;
            "    Relative    = ", R8!relative_entropy;
            "    Low exit    = ", R8!low_entropy;
            "    Max exit    = ", R8!max_entropy;
            if MaxSmooth ne Infinity() then
	    "Known smoothness:";
            "    Curve       = ", smooth0;
            "    Twist       = ", smooth1;
            "    Abort bound = ", MaxSmooth;
	    end if;
	    "-----------------------------------------";
	end if;
        if (log_modulus lt TT`log_weil_bound) and 
           (total_entropy + TT`log_weil_bound lt low_entropy) then 
            if VerboseLevel ge 2 then print
                "Filling in dummy trace data for early exit to Shanks.";
            end if; 
            ell := NextPrime(ell : Proof := false);
            log_extra := Log(10,ell);
            while log_modulus + log_extra lt TT`log_weil_bound do 
                vprint SEA, 3: "Adding filler prime", ell;
                log_modulus +:= log_extra;
                T := TorsionModule(TT`E,ell : Initialize := false); 
                InsertTorsionModule(~TT,T); 
                ell := NextPrime(ell : Proof := false);
                extra_entropy := Log(10,ell);
            end while;          
            // Top up last bit with the prime 2.
            multi_primes := [ T`prime : T in TT`multi_places ];
            unique_primes := [ T`prime : T in TT`unique_places ];
            two := Min(multi_primes cat unique_primes);
            e := Ceiling( Log(10)/Log(two)
                   * (TT`log_weil_bound - log_modulus) );
            if VerboseLevel ge 2 then 
                printf "Adding filler prime power 2^%o\n", e;
                "-----------------------------------------";
            end if;
            log_modulus +:= e * Log(10,two);
            if two in multi_primes then
                T := TT`multi_places[Index(multi_primes,2)];
                n := T`prime_exponent;
                T`prime_exponent := n + e;
                T`trace := [ t + k * two^n : k in [0..two^e-1], t in T`trace ];
            else 
                T := TT`unique_places[Index(unique_primes,2)];
                n := T`prime_exponent;
                T`prime_exponent := n + e;
                T`prime_type := "Atkin"; 
                T`trace := [ T`trace + k * 2^n : k in [0..2^e-1] ]; 
            end if;   
            InsertTorsionModule(~TT,T); 

            log_good_modulus := 
	        &+[ RR | T`prime_exponent * Log(10,T`prime)
  	            : T in TT`unique_places ];
	    total_entropy := &+[ RR | T`entropy : T in TT`unique_places ];
            k := 0;
            while (log_good_modulus lt TT`log_weil_bound) 
                and (k lt #(TT`multi_places)) do 
                k +:= 1;
                T := TT`multi_places[k];
                total_entropy +:= T`entropy;
                log_good_modulus +:= T`prime_exponent * Log(10,T`prime);
            end while;
	end if;  
    until log_modulus gt TT`log_weil_bound and 
          (total_entropy + log_good_modulus) lt max_entropy;
    if VerboseLevel ge 1 then
        printf "Total trace collection time = %o\n", Cputime(RunningTyme);
	"-----------------------------------------";
    end if;
    if VerboseLevel ge 2 then
        print "Discarding unused Atkin primes:";
        print [ T`prime^T`prime_exponent :
            T in [ TT`multi_places[i] : i in [k+1..#(TT`multi_places)] ] ];
    end if;
    // Do the actual discarding:
    TT`multi_places := [ TT`multi_places[i] : i in [1..k] ];
end procedure;

function TraceTableTrace(E, prime_factor, atkin_factor, power_factor :
    MaxSmooth := Infinity(), AbortLevel := 0 )
    // Returns the trace of E.

    VerboseLevel := GetVerbose("SEA");

    TT := TraceTable(E);
    TT`PrimeFactor := prime_factor;
    TT`AtkinFactor := atkin_factor;
    TT`PowerFactor := power_factor;

    TraceTableGetPrimeData(~TT :
        MaxSmooth := MaxSmooth, AbortLevel := AbortLevel );
    if TT`smooth_abort then
        return #BaseRing(E)+1;
    end if;

    TraceTableProcessUTPrimes(~TT);

    // Begin verbose printing.
    if VerboseLevel ge 1 then
        print "Elkies prime powers are: ";
        print [ T`prime^T`prime_exponent : T in TT`unique_places ];
        print "Corresponding traces are:";
        print [ T`trace : T in TT`unique_places ];
        print "Atkin prime powers are: ";
        print [ T`prime^T`prime_exponent : T in TT`multi_places ];
	if VerboseLevel le 3 then 
	    print "Corresponding number of trace candidates are:";
	    print [ #T`trace : T in TT`multi_places ];
	else
	    print "Corresponding traces candidates are:";
	    print [ T`trace : T in TT`multi_places ];
	end if;
    end if;
    // End verbose printing.

    if VerboseLevel ge 1 then BSGStyme := Cputime(); end if;
    if #TT`multi_places ne 0 then
        TraceTableProcessMTPrimes(~TT);
        trace := TraceTableBSGS(TT);
    else
        trace := TT`unique_trace;
        if trace ge TT`unique_modulus div 2 then
            trace := trace - TT`unique_modulus;
        end if;
    end if;
    if VerboseLevel ge 1 then
        print "Total BSGS time:", Cputime(BSGStyme);
    end if;
    return trace;
end function;
