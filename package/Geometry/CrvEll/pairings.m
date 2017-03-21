freeze;

/*
  Pairings on elliptic curves:

  The following were implemented in Magma C, see pairings.c

     - Weil pairing: using points only as described in Miller: The Weil pairing and its efficient calculation
     - Tate pairing giving a random representative as result
   
  The following are implemented in Magma simply calling the Miller function:
       - Reduced Tate pairing, i.e. which includes final powering and thus gives unique result
       - Eta pairing with multiplier T=t-1 (supersingular curves only)
       - Reduced Eta pairing with multiplier T=t-1 (supersingular curves only)
       - Eta pairing with multiplier q (no final powering/small powering necessary)
       - Ate pairing with multiplier T=t-1
       - Reduced Ate pairing with multiplier T=t-1
       - Ate pairing with multiplier q (no final powering/small powering necessary)

  All of these are a simple application of Miller's algorithm to compute evaluations
  of functions f_{n,P}(Q) with (f_{n,P}) = n[P] - [n*P] - (n-1)[O]

  Frederik Vercauteren November 2006

*/

/* Mar 2016, MW: Bill Allombert reports a bug with k=6 q=5, so Fre says
   the fix is to always have k be 1 in InternalFinalExponentiation */


function InternalFinalExponentiation(b, Fq, k, n)

    /* computes b^((q^k-1) / n) where it is known that n only divides \Phi_k(q) */

    res := Parent(b) ! 1;
    q := #Fq;

    if (k lt 0) then
	error "InternalFinalExponentiation: k should be > 0";
    end if;
    
    if (k eq 1) then
	res := b^((q-1) div n);
    else
        Zx := PolynomialRing(Integers()); x:=Zx.1;
	divs := Divisors(k);
	nd := #divs;
	ld := divs[nd-1];  /* largest divisor of k different from k */

	res := Frobenius(b, Fq, ld)*b^(-1);  /* res := b^(q^(k/d)-1)  with d largest divisor */
	
	Middlex := Eltseq((x^k - 1) div ((x^ld - 1)*CyclotomicPolynomial(k)));
	if ( &and[c gt 0 : c in Middlex]) then
	    resinv := 1;
	else
	    resinv := res^(-1);
	end if;
	
	prev := #Middlex;
	prod := res^Middlex[prev];
	
	for i := #Middlex-1 to 1 by -1 do
	    /* search for next non-zero coefficient */
	    
	    if (Middlex[i] ne 0) then
		prod := Frobenius(prod, Fq, prev - i);
		if (Middlex[i] lt 0) then
		    prod *:= resinv^(-Middlex[i]);
		else
		    prod *:= res^(Middlex[i]);
		end if;
		prev := i;
	    end if;
	    
	end for;
	res := Frobenius(prod, Fq, prev - 1);
	
	rempow := Evaluate(CyclotomicPolynomial(k),q);
	if ((rempow mod n) ne 0) then
	    error "InternalFinalExponentiation: n sould divide \Phi_k(q)";
	end if;
	rempow := rempow div n;
	
	res := res^rempow;
    end if;
    
    return res;
    
end function;

function InternalTatePairingNumerator(P, Q, m)

    /* computes Tate pairing using InternalMillerNumerator when denominator elimination applies */

    res := Parent(P[1]) ! 1;
    
    if not (IsZero(P) or IsZero(Q)) then
	if (P eq Q) then /* points are the same, so fiddle a bit */
	    P2 := 2*P;
	    P3 := P2 + P;
	    
	    if ((not IsZero(P2)) and (not IsZero(P3))) then
		b, res_n1 := InternalMillerNumerator(P, P2, m);
		if (b ne 0) then
		    error "P must be in m-torsion, i.e. m*P = 0";
		else
		    b, res_n2 := InternalMillerNumerator(P, P3, m);
		    res := res_n2/res_n1;
		end if;
	    else
		if (IsZero(P3)) then /* P is 3-torsion */
		    b, res_n := InternalMillerNumerator(P, P2, m);
		    if (b ne 0) then
			error "P must be in m-torsion, i.e. m*P = 0";
		    else
			res := res_n^(-1);
		    end if;
		else /* P is 2-torsion */
		    if ((m mod 2) ne 0) then
			error "P must be in m-torsion, i.e. m*P = 0";
		    else
			// mch - 03/12 - No! This is not to compute the
			// reduced Tate pairing and the present thing is wrong
			// anyway! If 2P=0 then T(P,P,m) = T(P,P,2)^(m/2) in k*/k*^m
			// so the result is 1 (mod k*^m) if T(P,P,2)=1 mod k*^2 and
			// a^(m/2) mod k*^m where a is a generator of k* say, if T(P,P,2)
			// != 1 mod k*^m. Can compute T(P,P,2) using the 2-division poly
			// but don't bother here as this clause has now been bypassed!  
			// Need to do properly for internal TatePairing, though.
			if IsDivisibleBy(P,2) then
			    res := Parent(P[1]) ! 1;
			else
			    res := PrimitiveElement(Parent(P[1]))^(m div 2);
			end if;
		    end if;
		end if;
	    end if;
	else  
	    b, res_n := InternalMillerNumerator(P, Q, m);
	    if (b ne 0) then
		error "P must be in m-torsion, i.e. m*P = 0";
	    else
		res := res_n;
	    end if;
	end if;
    end if;
    
    return res;
    
end function;
    
intrinsic ReducedTatePairing(P :: PtEll, Q :: PtEll, m :: RngIntElt) -> RngElt
    { The reduced Tate Pairing e_m(P,Q) = t_m(P,Q)^((q^k-1) div m) where P is in E[m]. }

    if (Parent(P) ne Parent(Q)) then
	error "Points P and Q must lie in the same pointset";
    end if;
    
    FF := Parent(P[1]);
    qk := #FF;
    p := Characteristic(FF);
    k := Degree(FF);  /* note that this could be a multiple of k, but that does not matter */
    bF := BaseField(FF);
    rd := Degree(FF, bF);

    if (((qk - 1) mod m) ne 0) then
	error "F_q^k must contain m-th roots of unity, i.e. m | q^k - 1";
    end if;

    /* P=Q of order 2 not correctly handled in the old version. Bypass calling the
       non-reduced version here by handling directly - mch - 03/12 */
    if (IsZero(P) or IsZero(Q)) then
	return FF!1;
    end if;
    if (P eq Q) and IsZero(2*P) then
	error if not IsDivisibleBy(m,2), "P must be an m-torsion point";
	val := Evaluate(Derivative(DivisionPolynomial(Curve(P),2)),P[1]);
	boo := IsSquare(val);
	return ((boo) select FF!1 else -FF!1);
    end if;                
    
    /* Test if denominator elimination applies */

    if (rd gt 1) and (Degree(MinimalPolynomial(P[1])) lt rd) and (Degree(MinimalPolynomial(Q[1])) lt rd) then /* OK, denominator elimination applies */
	res := InternalTatePairingNumerator(P, Q, m);
    else
	res := TatePairing(P, Q, m);
    end if;
    
    return InternalFinalExponentiation(res, FF, 1, m); // MW
//    return InternalFinalExponentiation(res, PrimeField(FF), k, m);
      
end intrinsic

function InternalAteEtaPairing(P, Q, n, q, CheckPoints, CheckCurve, Tversion, bAte) 

    res :=  Parent(P[1]) ! 1; 
      
    if (Parent(P) ne Parent(Q)) then
	error "Points P and Q must lie in the same pointset";
    end if;

    qk := #Parent(P[1]);

    if (((qk - 1) mod n) ne 0) then
	error "F_q^k must contain m-th roots of unity, i.e. m | q^k - 1";
    end if;
    
    if (CheckCurve and not bAte) then
	if not (IsSupersingular(Curve(Parent(P)))) then
	    error "Curve must be supersingular for Eta-T pairing to apply";
	end if;
    end if;
    
    if (CheckPoints and not bAte) then  /* check for Eta case if requested */
	if not ((P[1]^q eq P[1]) and (P[2]^q eq P[2]) and (P[3]^q eq P[3])) then
	    error "P must satisfy Frob_q(P) = P";
	end if;
	
	if not (IsZero(n*P)) then
	    error "P must be n-torsion";
	end if;
	
	qQ := q*Q;
	if not ((Q[1]^q eq qQ[1]) and (Q[2]^q eq qQ[2]) and (Q[3]^q eq qQ[3])) then
	    error "Q must satisfy Frob_q(Q) = q*Q";
	end if;
	
	if not (IsZero(n*Q)) then
	    error "Q must be n-torsion";
	end if;
    end if;

    if (CheckPoints and bAte) then /* check for Ate case if requested */

	qP := q*P;
	if not ((P[1]^q eq qP[1]) and (P[2]^q eq qP[2]) and (P[3]^q eq qP[3])) then
	    error "Q must satisfy Frob_q(Q) = q*Q";
	end if;
	
	if not (IsZero(n*P)) then
	    error "Q must be n-torsion";
	end if;

	if not ((Q[1]^q eq Q[1]) and (Q[2]^q eq Q[2]) and (Q[3]^q eq Q[3])) then
	    error "P must satisfy Frob_q(P) = P";
	end if;
	
	if not (IsZero(n*Q)) then
	    error "P must be n-torsion";
	end if;
    end if;

    E := Curve(Parent(P));
    C := #BaseRing(E);
    if ((q mod C) eq 0) then /* E is defined over subfield of F_q which is good */
	if (Tversion) then
	    d := q div C;
	    t := TraceOfFrobenius(E,d);
	    T := t-1;
	else
	    T := q;
	    order_found := false;
	    i := 1;
	    k := 0;
	    qi := q mod n;
	    while ((not order_found) and (i lt 1000)) do
		if (qi eq 1) then
		    order_found := true;
		    k := i;
		else
		    i := i+1;
		    qi := qi*q mod n;
		end if;
	    end while;
	    
	    if (not order_found) then
		Zn := Integers(n);
		k := Order(Zn ! q);
	    end if;
	end if;
	
	if (IsZero(P) or IsZero(Q) or (T eq 1) or (T eq -1)) then
	    res := Parent(P[1]) ! 1;
	else
	    if (P eq Q) then /* points are the same, so fiddle a bit */
		P2 := 2*P;
		P3 := P2 + P;
		
		if ((not IsZero(P2)) and (not IsZero(P3))) then
		    b, res_n1, res_d1 := InternalMiller(P, P2, T);
		    b, res_n2, res_d2 := InternalMiller(P, P3, T);
		    
		    res := (res_n2*res_d1)/(res_n1*res_d2);
		else
		    if (IsZero(P3)) then /* P is 3-torsion */
			b, res_n, res_d := InternalMiller(P, P2, T);
			res := res_d/res_n;
		    else /* P is 2-torsion */
			if ((n mod 2) ne 0) then
			    error "P must be in m-torsion, i.e. m*P = 0";
			else
			    if ((n mod 4) eq 0) then
				res := Parent(P[1]) ! 1;
			    else
				res := Parent(P[1]) ! -1;
			    end if;
			end if;
		    end if;
		end if;
	    else  
		b, res_n, res_d := InternalMiller(P, Q, T);
		res := res_n/res_d;
	    end if;
	end if;
    else
	error "The elliptic curve E must be defined over a subfield of F_q";
    end if;

    if (not Tversion and not bAte) then
	Zk := Integers(k);
	qk := (Zk ! q)^k;
	d := GCD(k, (Integers() ! qk) - 1);
	res := res^d;
    end if;
    
    return res;
    
end function;

function InternalAteEtaPairingNumerator(P, Q, n, q, CheckPoints, CheckCurve, bAte) 

    res :=  Parent(P[1]) ! 1; 
      
    if (CheckCurve and not bAte) then
	if not (IsSupersingular(Curve(Parent(P)))) then
	    error "Curve must be supersingular for Eta-T pairing to apply";
	end if;
    end if;

    if (CheckPoints and not bAte) then  /* check for Eta case if requested */
	if not ((P[1]^q eq P[1]) and (P[2]^q eq P[2]) and (P[3]^q eq P[3])) then
	    error "P must satisfy Frob_q(P) = P";
	end if;
	
	if not (IsZero(n*P)) then
	    error "P must be n-torsion";
	end if;
	
	qQ := q*Q;
	if not ((Q[1]^q eq qQ[1]) and (Q[2]^q eq qQ[2]) and (Q[3]^q eq qQ[3])) then
	    error "Q must satisfy Frob_q(Q) = q*Q";
	end if;
	
	if not (IsZero(n*Q)) then
	    error "Q must be n-torsion";
	end if;
    end if;

    if (CheckPoints and bAte) then /* check for Ate case if requested */

	qP := q*P;
	if not ((P[1]^q eq qP[1]) and (P[2]^q eq qP[2]) and (P[3]^q eq qP[3])) then
	    error "Q must satisfy Frob_q(Q) = q*Q";
	end if;
	
	if not (IsZero(n*P)) then
	    error "Q must be n-torsion";
	end if;

	if not ((Q[1]^q eq Q[1]) and (Q[2]^q eq Q[2]) and (Q[3]^q eq Q[3])) then
	    error "P must satisfy Frob_q(P) = P";
	end if;
	
	if not (IsZero(n*Q)) then
	    error "P must be n-torsion";
	end if;
    end if;
    
    E := Curve(Parent(P));
    C := #BaseRing(E);
    if ((q mod C) eq 0) then /* E is defined over subfield of F_q which is good */
	d := q div C;
	t := TraceOfFrobenius(E,d);
	T := t-1;

	if (IsZero(P) or IsZero(Q) or (T eq 1) or (T eq -1)) then
	    res := Parent(P[1]) ! 1;
	else
	    if (P eq Q) then /* points are the same, so fiddle a bit */
		P2 := 2*P;
		P3 := P2 + P;
		
		if ((not IsZero(P2)) and (not IsZero(P3))) then
		    b, res_n1 := InternalMillerNumerator(P, P2, T);
		    b, res_n2 := InternalMillerNumerator(P, P3, T);
		    
		    res := res_n2/res_n1;
		else
		    if (IsZero(P3)) then /* P is 3-torsion */
			b, res_n := InternalMillerNumerator(P, P2, T);
			res := res_n^(-1);
		    else /* P is 2-torsion */
			if ((n mod 2) ne 0) then
			    error "P must be in m-torsion, i.e. m*P = 0";
			else
			    if ((n mod 4) eq 0) then
				res := Parent(P[1]) ! 1;
			    else
				res := Parent(P[1]) ! -1;
			    end if;
			end if;
		    end if;
		end if;
	    else  
		b, res_n  := InternalMillerNumerator(P, Q, T);
		res := res_n;
	    end if;
	end if;
    else
	error "The elliptic curve E must be defined over a subfield of F_q";
    end if;

    return res;
    
end function;
	
intrinsic EtaTPairing(P :: PtEll, Q :: PtEll, m :: RngIntElt, q :: RngIntElt : CheckPoints:=false, CheckCurve:=false) -> RngElt
    { Computes Eta-T pairing with T = t-1, with E(F_q) = q + 1 - t, curve needs to be supersingular, (t-1)^k != 1 else
    pairing is trivial, P = Frob(P) and q*Q = Frob(Q) with Frob the q-power Frobenius, m*P = 0 and m*Q = 0 }
    
    return InternalAteEtaPairing(P, Q, m, q, CheckPoints, CheckCurve, true, false);
    
end intrinsic
    
intrinsic EtaqPairing(P :: PtEll, Q :: PtEll, m :: RngIntElt, q :: RngIntElt : CheckPoints:=false, CheckCurve:=false) -> RngElt
    { Computes Eta-q pairing, curve needs to be supersingular, P = Frob(P) and q*Q = Frob(Q) with Frob the q-power
    Frobenius, m*P = 0 and m*Q = 0, maps directly into m-th roots of unity }
    
    return InternalAteEtaPairing(P, Q, m, q, CheckPoints, CheckCurve, false, false);
    
end intrinsic
    
intrinsic ReducedEtaTPairing(P :: PtEll, Q :: PtEll, m :: RngIntElt, q :: RngIntElt : CheckPoints:=false, CheckCurve:=false) -> RngElt
    { Computes reduced Eta-T pairing with T = t-1, with E(F_q) = q + 1 - t, curve needs to be supersingular, 
    (t-1)^k != 1 else pairing is trivial, P = Frob(P) and q*Q = Frob(Q) with Frob the q-power Frobenius, m*P = 0
    and m*Q = 0 }

    if (Parent(P) ne Parent(Q)) then
	error "Points P and Q must lie in the same pointset";
    end if;
    
    FF := Parent(P[1]);
    qk := #FF;
    p := Characteristic(FF);
    k := Degree(FF);  /* note that this could be a multiple of k, but that does not matter */
    bF := BaseField(FF);
    rd := Degree(FF, bF);

    if (((qk - 1) mod m) ne 0) then
	error "F_q^k must contain m-th roots of unity, i.e. m | q^k - 1";
    end if;
        
    /* Test if denominator elimination applies */

    if (rd gt 1) and (Degree(MinimalPolynomial(P[1])) lt rd) and (Degree(MinimalPolynomial(Q[1])) lt rd) then
	/* OK, denominator elimination applies */
	res := InternalAteEtaPairingNumerator(P, Q, m, q, CheckPoints, CheckCurve, false);
    else
	res := EtaTPairing(P, Q, m, q : CheckPoints, CheckCurve);
    end if;

    return InternalFinalExponentiation(res, FF, 1, m); // MW
//    return InternalFinalExponentiation(res, PrimeField(FF), k, m);
    
end intrinsic

intrinsic AteTPairing(Q :: PtEll, P :: PtEll, m :: RngIntElt, q :: RngIntElt : CheckPoints:=false) -> RngElt
    { Computes Ate-T pairing with T = t-1, with E(F_q) = q + 1 - t, (t-1)^k != 1 else pairing is trivial, 
      q*Q = Frob(Q) and P = Frob(P) with Frob the q-power Frobenius, m*P = 0 and m*Q = 0 }
    
    return InternalAteEtaPairing(Q, P, m, q, CheckPoints, false, true, true);
    
end intrinsic
    
intrinsic AteqPairing(Q :: PtEll, P :: PtEll, m :: RngIntElt, q :: RngIntElt : CheckPoints:=false) -> RngElt
    { Computes Ate-q pairing, q*Q = Frob(Q) and P = Frob(P) with Frob the q-power Frobenius, 
      m*P = 0 and m*Q = 0, maps directly into m-th roots of unity }
    
    return InternalAteEtaPairing(Q, P, m, q, CheckPoints, false, false, true);
    
end intrinsic
    
intrinsic ReducedAteTPairing(Q :: PtEll, P :: PtEll, m :: RngIntElt, q :: RngIntElt : CheckPoints:=false) -> RngElt
    { Computes reduced Ate-T pairing with T = t-1, with E(F_q) = q + 1 - t, (t-1)^k != 1 else pairing is trivial, 
    q*Q = Frob(Q) and P = Frob(P) with Frob the q-power Frobenius, m*P = 0 and m*Q = 0 }

    if (Parent(P) ne Parent(Q)) then
	error "Points P and Q must lie in the same pointset";
    end if;
    
    FF := Parent(P[1]);
    qk := #FF;
    p := Characteristic(FF);
    k := Degree(FF);  /* note that this could be a multiple of k, but that does not matter */
    bF := BaseField(FF);
    rd := Degree(FF, bF);

    if (((qk - 1) mod m) ne 0) then
	error "F_q^k must contain m-th roots of unity, i.e. m | q^k - 1";
    end if;
        
    /* Test if denominator elimination applies */

    if (rd gt 1) and (Degree(MinimalPolynomial(P[1])) lt rd) and (Degree(MinimalPolynomial(Q[1])) lt rd) then
	/* OK, denominator elimination applies */
	res := InternalAteEtaPairingNumerator(Q, P, m, q, CheckPoints, false, true);
    else
	res := AteTPairing(Q, P, m, q : CheckPoints);
    end if;

    return InternalFinalExponentiation(res, FF, 1, m); // MW
//    return InternalFinalExponentiation(res, PrimeField(FF), k, m);
    
end intrinsic
