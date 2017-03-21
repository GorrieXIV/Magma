freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                SHANKS BABY-STEP GIANT-STEP ALGORITHM               //
//                                                                    //
////////////////////////////////////////////////////////////////////////

/*
Constant by which to scale all logs (so that rounding a scaled log 
to the nearest integer preserves enough precision).
*/

LOG_SCALE := 1000;
GOOD_LIMIT := 1.1;
FRAC := 1.0;

////////////////////////////////////////////////////////////////////////
//      FUNCTIONS TO SPLIT THE MULTIPLE-MOD PRIMES INTO TWO LISTS     //
////////////////////////////////////////////////////////////////////////

function BasicSequencePartition(Q, frac)
   /*
   Use the lattice machinery to pick out a subset of Q whose sum
   is 1/frac times the sum of all the elements of Q.
   Much improved version: Allan Steel, June 1999.
   */

   TIME := Cputime();
   n := #Q;
   vprintf SEA, 5:
      "Constructing lattice of dimension %o " *
      "for near-optimal partition.\n", n + 1;

   Q_scale := 1;
   if false then
      Q_scale := Ceiling(Min(Q) / 100);
      vprintf SEA, 4: "Sequence scale: %o\n", Q_scale;
      Q := [Round(x / Q_scale): x in Q];
   end if;

   s := Round((&+Q - Log(frac)*LOG_SCALE/Q_scale) / 2);
   X := RMatrixSpace(Integers(), n + 1, n + 2) ! 0;

   if GetVerbose("SEA") ge 5 then
       "Q:", Q;
       "frac:", frac;
       "s:", s;
   end if;
   
   oscale := (n * s)^2;

   for i := 1 to n do
      X[i][i] := 2 * oscale;
      X[i][n + 1] := n * Q[i];
      X[n + 1][i] := 1 * oscale;
   end for;
   X[n + 1][n + 1] := n * s;
   X[n + 1][n + 2] := 1 * oscale;

   L := LatticeWithBasis(X);
   last_M := 1;
   M := Minimum(L);
   vprint SEA, 5: "Lattice minimum:", M;
   if true then
      best_good := false;
      while true do
	 T := Cputime();
	 vprintf SEA, 5: "Enumerate up to %o\n", M;
	 P := ShortVectorsProcess(L, last_M, M);
	 best_norm := M + 1;
	 c := 1;
	 while true do
	    v, norm := NextVector(P);
	    if norm lt 0 then
	       break;
	    end if;
	    if forall {i: i in [1 .. n] cat [n + 2] | Abs(v[i]) eq oscale}
		then
		if norm lt best_norm then
		    d := v[n + 1] div n;
		    if GetVerbose("SEA") ge 5 then
			printf
			"    Solution found after %o vector %o (time: %o)\n",
			c, c eq 1 select "" else "s", Cputime(T);
			"        Difference from optimum:", d;
			"       ", [ i: i in [1 .. n] | v[i] ne v[n + 2] ];
		    end if;
		    best_norm := norm;
		    best_v := v;
		    if d eq 0 then
			break;
		    end if;
		    ratio := Exp((d) / LOG_SCALE) + 0.0;
		    best_good := ratio ge 1 and ratio le GOOD_LIMIT or 
		    ratio le 1 and ratio ge 1/GOOD_LIMIT;
		    vprint SEA, 5: "        Ratio:  ", ratio;
		    vprint SEA, 5: "        1/Ratio:", 1/ratio;
		end if;
	    end if;
	    c +:= 1;
	    if c ge 50000 and best_good then
		break;
	    end if;
         end while;

	 vprintf SEA, 5: "%o vector%o (time: %o)\n",
	    c, c eq 1 select "" else "s", Cputime(T);

  	 if best_norm lt M + 1 then
	    v := best_v;
	    sol := [i: i in [1 .. n] | v[i] ne v[n + 2]];
	    vprint SEA, 5: "Indices selected:", sol;
	    vprint SEA, 5: "Lattice computation time:", Cputime(TIME);
	    return sol, v;
	 end if;

	 last_M := M + 1;
	 M := Ceiling(1.2 * M);
      end while;
   else
      while true do
         T := Cputime();
	 S := ShortVectors(L, last_M, M);
	 vprintf SEA, 5:
   	    "Enumerate up to %o: %o vector%o (time: %o)\n",
	    M, #S, #S eq 1 select "" else "s", Cputime(T);
	 for t in S do
	    v := t[1];
	    if forall{i: i in [1 .. n] cat [n + 2] | Abs(v[i]) eq oscale}
	       then
	       sol := [i: i in [1 .. n] | v[i] ne v[n + 2]];
	       if GetVerbose("SEA") ge 5 then
		   "Difference from optimum:", v[n + 1] div n;
		   "Indices selected:", sol;
		   "Lattice computation time:", Cputime(TIME);
	       end if;
	       return sol;
	    end if;
	 end for;
	 last_M := M + 1;
	 M := 2 * M;
      end while;
   end if;
end function;

function SequencePartition(Q,frac)
    // Since BasicSequencePartition takes too long when #Q > 30, 
    // we handle such sequences by splitting them in two, processing 
    // each part, and recombining them.

    TIME := Cputime();
    if #Q le 16 then
	soln := BasicSequencePartition(Q,frac);
    else
        vprint SEA, 5: "Constructing recursive partition";
    	d := #Q div 2;
    	Q1 := [ Q[i] : i in [1..d]];
    	Q2 := [ Q[i] : i in [d+1..#Q]];
    	soln1 := $$(Q1, Sqrt(frac));
    	soln2 := $$(Q2, Sqrt(frac));
	soln := soln1 cat [ i+d : i in soln2];
    end if;
    vprint SEA, 4: "Sequence partitioning time:", Cputime(TIME);
    return soln;
end function;

function ListPartition(tt)
    // We split the multiple-mod primes (Atkin and Easy) into two
    // lists, such that &*C1_mod_list is close to 1/3 &*C2_mod_list.

    Z := Integers();

    Atkin_prime_list := [ (T`prime)^(T`prime_exponent) 
       : T in tt`multi_places ];
    Atkin_mod_list := [ T`trace : T in tt`multi_places ];

    C1_mod_list   := [];
    C1_prime_list := [Z |];
    C2_mod_list   := [];
    C2_prime_list := [Z |];

    if #Atkin_mod_list eq 2 then
	C2_mod_list := [ Atkin_mod_list[2] ];
	C2_prime_list := [ Atkin_prime_list[2] ];
    end if;

    if #Atkin_mod_list le 2 then
	C1_mod_list := [ Atkin_mod_list[1] ];
	C1_prime_list := [ Atkin_prime_list[1] ];
	return C1_mod_list,  C1_prime_list, C2_mod_list, C2_prime_list;
    end if;

    Q := [ Round(Log(#q)*LOG_SCALE) : q in Atkin_mod_list];
    soln := SequencePartition(Q, FRAC); // Make lists in ratio FRAC:1.0

    C1_mod_list   := [Atkin_mod_list[i]   : i in [1..#Q] | i in soln];
    C1_prime_list := [Z | Atkin_prime_list[i] : i in [1..#Q] | i in soln];
    C2_mod_list   := [Atkin_mod_list[i]   : i in [1..#Q] | i notin soln];
    C2_prime_list := [Z | Atkin_prime_list[i] : i in [1..#Q] | i notin soln];

    return C1_mod_list, C1_prime_list, C2_mod_list, C2_prime_list;
end function;

////////////////////////////////////////////////////////////////////////
//                  FUNCTIONS TO MAKE THE BSGS TABLE                  //
////////////////////////////////////////////////////////////////////////

function MakeResiduesOLD(res_list,moduli,m2,m0,t0,abs_bound)
    Z := Integers();
    R := [ Z | ];
    m1 := &*moduli;
    Zm1 := ResidueClassRing(m1);
    m2m0_inv := ( Zm1!(m2*m0) )^-1;
    index_bound := &*[ #res_list[i] : i in [1..#res_list] ];
    moduli_compls := [ mc * Z!((ResidueClassRing(m)!mc)^-1) 
        where mc is m1 div m : m in moduli ];
    for i in [1..index_bound] do
	index := i;
	c1 := Zm1!0;
	for j in [1..#res_list] do
	    jth_res := res_list[j];
	    sub_index := (index mod #jth_res) + 1;
	    index := index div #jth_res;
	    t := jth_res[sub_index];
	    c1 +:= t * moduli_compls[j];
	end for;
	r1 := Z!( (c1 - t0) * m2m0_inv );
	if r1 le abs_bound then
	    Append(~R,r1);
	else
	    Append(~R,r1-m1);
	end if;
    end for;
    return R;
end function;

function MakeResidues(res_list,moduli,m2,m0,t0,abs_bound)
    TIME := Cputime();
    //if IsIntrinsic("MakeResiduesSEA") then
	R := MakeResiduesSEA(res_list,moduli,m2,m0,t0,abs_bound);
    /*
    else
	R := MakeResiduesOLD(res_list,moduli,m2,m0,t0,abs_bound);
    end if;
    */
    vprint SEA, 4: "MakeResidues time:", Cputime(TIME);
    return R;
end function;

function BSGS_by_Parts(E,m1,m2,m0,t0,R1,R2)
   // Use a modified baby step, giant step algorithm to find the trace.

   vprint SEA, 4: "Begin BSGS_by_Parts";
   ZEIT := Cputime();

   P := Random(E);

   if GetVerbose("SEA") ge 4 then
       "Shanks initialized with the following values:";
       // This point can be quite big to print...
       //vprint SEA, 5: "    P =", P;
       // Exact trace modulus and known value.
       "    m0 =", m0;
       "    t0 =", t0;
       // Moduli for partitions of Atkin primes:
       "    m1 =", m1;  
       "    m2 =", m2;
       // Residue partitions:
       "    #R1 =", #R1;
       "    #R2 =", #R2;
       "    Ratio #R2/#R1 =", RealField(8)!(#R2/#R1);
       //"    Seed:", GetSeed();
   end if;
   
   F := BaseRing(E);
   q := #F;
   E_0 := E!0;
   Q0 := (q+1-t0)*P;
   Q1 := m2*m0*P;
   Q2 := m1*m0*P;
   Q3 := m1*m2*m0*P;

   ZEIT1 := Cputime();

   res := ECPCShanks([Q0,Q1,Q2,Q3],[m1,m2,m0,t0],R1,R2);

   vprint SEA, 4: "ECPCShanks time:", Cputime(ZEIT1);
   vprint SEA, 4: "Total BSGS_by_Parts time:", Cputime(ZEIT);

   return res;
end function;

function TraceTableBSGS(tt)
   // Find the trace of the curve associated to the trace table tt
   // using the BSGS algorithm.

   /*
   Since the initial BSGS_by_Parts may not return the correct trace
   (e.g. if it used a random point whose order is smaller than the
   Hasse interval).  We must verify the answer by choosing other
   points at random and checking their order is the putative order
   of the curve, working simultaneously with the quadratic twist.
   */

   TIME := Cputime();
   E := tt`E;
   q := #BaseRing(E);
   weil_bound := 2 * (Isqrt(q) + 1);

   /*
   Repeat Shanks until number of traces is reasonably small (an unluckly
   random element could produce a large number of possible traces).
   */

   repeat
      traces := BSGS_by_Parts(
      tt`E, tt`multi_modulus_1, tt`multi_modulus_2, 
      tt`unique_modulus, tt`unique_trace, tt`R1, tt`R2
      );
   until #traces le 10^6;

   vprint SEA, 4: "Number of possible traces found:", #traces;
   ZEIT := Cputime();

   /*
   Eliminate bad traces which are out of range or cannot give
   correct order; there should be one left over.
   */

   traces := [ t : t in Set(traces) | Abs(t) le weil_bound ];
   F := QuadraticTwist(E);
   for t in traces do
       order := q + 1 - t;
       twist := q + 1 + t;
       vprint SEA, 4: "Possible trace:", t;
       vprint SEA, 4: "Possible order:", order;
       for j in [1 .. 8] do
	   P := Random(E);
	   Q := Random(F);
	   if not IsIdentity(order * P) or not IsIdentity(twist * Q) then
	       vprint SEA, 4: "Candidate is not correct order, eliminating.";
	       Exclude(~traces, t);
	       break j;
	   end if;
       end for;
   end for;

   vprint SEA, 4: "Traces check time:", Cputime(ZEIT);

   /*
   By working with the twist of the curve we are unlikely to
   get here, but now we consider the exponent of the group.

   If E(k) = Z/mZ x Z/nZ then frob-1 == 0 mod m, so that its
   trace, t-2, is divisible by m.  The group order will then
   be m*n | n^2, where n is the exponent.  
   */

   exp := GCD([ Integers() | q+1-t : t in traces ]);
   vprint SEA, 4 : "Remaining trace candidates:", traces;
   vprint SEA, 4 : "Group exponent multiple:", exp;

   // Assume that the GCD, exp, of the remaining orders is a 
   // multiple of the exponent. 
   traces1 := traces;
   for t in traces do
       n := q - t + 1;
       if exp^2 mod n ne 0 then
	   vprint SEA, 4 : "Removing trace candidate", t;
	   Exclude(~traces,t);
       end if;
   end for;
   error if #traces gt 1, "Failed to eliminate trace candidates.";
   error if #traces eq 0, "Failed to find valid trace candidate.";
   vprint SEA, 4: "Correct order found";
   vprint SEA, 4: "Total Shanks time:", Cputime(TIME);
   return traces[1];
end function;
