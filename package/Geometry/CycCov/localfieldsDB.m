freeze;
//
//
// Lists of defining polynomials of extensions of
// Q_2, Q_3, Q_5 and Q_3(zeta_3), Q_5(zeta_5) of given degree 

// Source for absolute extensions of Q_p: 
//    http://math.la.asu.edu/~jj/localfields/

/*
==========================
extensions of Q_2
==========================
n  | #	
2  | 7								
3  | 2		TAME		
4  | 59					
5  | 2		TAME
6  | 47	
7  | 2		TAME
...........
8  | 1823
9  | 3		TAME
10 | ?
11 | 2		TAME
//////////////////////////

==========================
extensions of Q_3
==========================
n  | #
2  | 3          TAME
3  | 10
4  | 5          TAME
5  | 2          TAME 
6  | 75
7  | 2          TAME
...........
8  | 8
9  | lots
//////////////////////////

==========================
extensions of Q_5
==========================
n  | #
2  | 3
3  | 2
4  | 7
5  | 26
6  | 7
//////////////////////////

==========================
extensions of Q_3(zeta_3) 
==========================
n | #extensions
2 | 2
3 | 31
4 | 4
5 | 2
6 | lots
7 | 2
//////////////////////////


==========================
extensions of Q_5(zeta_5)
==========================
n | #extensions
1 | 1
2 | 2
3 | 2
4 | 4
5 | too many
//////////////////////////
*/	


AbsoluteExtensionsOfQ_2 := function(kpol);

  x := kpol.1;
  return [
  //Degree 2
  x^2+x+1, x^2+2*x+2, x^2+2*x-2, x^2-2, x^2+2, x^2-6, x^2+6, 
  //Degree 3
  x^3-2, x^3+x+1,
  //Degree 4
  x^4-x+ 1, x^4+ 8*x^2+ 4, x^4-x^2+ 5,
  x^4+ 2*x^2+ 4*x+ 4, x^4- 5, x^4+ 2*x + 2, x^4- 6*x^2+ 4,
  x^4- 2*x^2+ 4, x^4+ 2*x^2+ 20, x^4- 2*x^2+ 20,
  x^4+ 2*x^2- 4, x^4- 20, x^4+ 2*x^3+ 2*x^2+ 2,
  x^4+ 2*x^3+ 2, x^4+ 2*x^3+ 6,	x^4+ 2*x^2+ 4*x+ 10,
  x^4+ 6*x^2+ 1, x^4+ 6*x^2+ 4*x+ 14, x^4+ 6*x^2+ 4*x+ 6,
  x^4+ 2*x^2+ 4*x+ 6, x^4+ 6*x^2+ 4*x+ 2, x^4+ 4*x^2+ 4*x+ 2,
  x^4+ 4*x+ 2,x^4+ 6*x^2+ 2, x^4- 2*x^2+ 2,
  x^4+ 6*x^2+ 10, x^4+ 2*x^2+ 10, x^4+ 2*x^2- 2,
  x^4- 2*x^2- 2, x^4+ 2*x^2+ 6, x^4- 2*x^2+ 6, x^4+ 2*x^2- 9,
  x^4+ 2*x^2- 1, x^4+ 6*x^2- 9, x^4+ 6*x^2- 1, x^4- 6*x^2+ 3,
  x^4+ 6*x^2+ 3, x^4- 2*x^2+ 3, x^4+ 2*x^2+ 3, x^4+ 12*x^2+ 2,
  x^4+ 8*x+ 14, x^4+ 4*x^2+ 18, x^4+ 12*x^2+ 18,
  x^4+ 2, x^4+ 18, x^4+ 8*x^2+ 8*x+ 22, x^4+ 4*x^2+ 10,
  x^4+ 12*x^2+ 10, x^4+ 8*x+ 6, x^4+ 10,
  x^4+ 26, x^4+ 4*x^2+ 14, x^4+ 8*x+ 10,
  x^4+ 30, x^4+ 14, x^4+ 4*x^2+ 6,
  x^4+ 12*x^2+ 6, x^4+ 22, x^4+ 6,
  // Degree 5:
  x^5+x^2+1, x^5-2,
  // Degree 6:
  x^6-x+ 1, x^6+ 3*x^5+ 6*x^4+ 3*x^3+ 9*x+ 9,
  x^6- 2*x^3+ 4, x^6+x^2- 1, x^6-x^4- 5,
  x^6+ 2*x^4+x^2- 7, x^6+x^2+ 1, x^6+ 2*x+ 2,
  x^6- 2*x^4+x^2- 3, x^6- 13*x^4+ 7*x^2- 3,
  x^6+ 2*x^2+ 2*x+ 2, x^6+ 2*x^3+ 2,
  x^6+ 2*x^3+ 2*x^2+ 6, x^6+ 2*x^3+ 6,
  x^6+ 2*x^3+ 2*x^2+ 2, x^6+ 4*x^4+ 4*x^2- 8,
  x^6+ 4*x^2- 8, x^6- 4*x^4+ 4*x^2+ 24, x^6+ 4*x^2+ 24,
  x^6- 4*x^4+ 4*x^2+ 8, x^6+ 4*x^2+ 8, x^6+ 4*x^4+ 4*x^2- 24,
  x^6+ 4*x^2- 24, x^6+ 2*x^5+ 2*x^4+ 2, x^6+ 2*x^5+ 2*x^4+ 2*x^2+ 2,
  x^6+ 2*x^5+ 4*x+ 2, x^6+ 2*x^5+ 2*x^4+ 6, x^6+ 2*x^5+ 6,
  x^6+ 2*x^5+ 4*x^3+ 6, x^6+ 2*x^5+ 4*x^3+ 2, x^6+ 2*x^5+ 2,
  x^6+ 14, x^6+ 6*x^4+ 14, x^6+ 2*x^2+ 14,
  x^6+ 6*x^4+ 4*x^2+ 4*x+ 14, x^6+ 6, x^6+ 6*x^4+ 6,
  x^6+ 2*x^2+ 6, x^6+ 4*x^4+ 2*x^2+ 6, x^6+ 6*x^4+ 2,
  x^6+ 2*x^4+ 2, x^6+ 2*x^4+ 2*x^2+ 2, x^6+ 2*x^2+ 2,
  x^6+ 10, x^6+ 2*x^4+ 10, x^6+ 2*x^4+ 2*x^2+ 10, x^6+ 2*x^2+ 10,
  // Degree 7:
  x^7-x+1, x^7-2
];
end function;

AbsoluteExtensionsOfQ_3 := function(k0);

x := PolynomialRing(k0).1;

exts := [
  //Degree 2
  x^2-3, x^2-x+2,
    // contain zeta_3:
    x^2+3,
  //Degree 3
  x^3-x+ 1,x^3+ 6*x+ 3, x^3- 3*x^2+ 21, x^3- 3*x^2+ 3, x^3- 3*x^2+ 12, x^3+ 3*x^2+ 3, 
    // contain zeta_3:
    x^3+ 3*x+ 3, x^3+3, x^3+21, x^3+12,
  //Degree 4
  x^4-x+2, x^4-3*x^2+18,x^4-3, 
    // contain zeta_3:
    x^4 + 3, x^4 + 9*x^2 + 36,
  //Degree 5
  x^5-x+1,x^5-3,
  //Degree 6
  x^6 + 3*x^3 + 6, x^6 + 6*x^5 + 36, x^6 + 6*x^4 + 3*x^3 + 6,
  x^6 + 6*x^5 + 9, x^6 + 6*x^3 + 6*x^2 + 6, x^6 + 6*x^3 + 15,
  x^6 + 6, x^6 + 6*x^4 + 6, x^6 + 3*x^5 + 24,
  x^6 + 6*x^5 + 6*x^3 + 72, x^6 + 3*x^4 + 24, x^6 - 6*x^4 + 9*x^2 - 27,
  x^6 + 3*x^5 - 2, x^6 - 18, x^6 + 6*x^2 + 6,
  x^6 + 6*x^3 + 45, x^6 + 6*x^4 + 6*x^3 + 18,x^6 + 15,
  x^6 + 3*x^4 + 6*x^3 + 6, x^6 + 36, x^6 + 9, x^6 + 3*x^5 + 63,
  x^6 + 6*x^5 + 3*x^4 + 15, x^6 + 18*x^2 + 63,
  x^6 + 3*x^3 + 18, x^6 + 6*x^5 + 18*x^2 + 9,
  x^6 + 3*x^2 + 6, x^6 + 18*x + 24,
  x^6 + 6*x^5 + 9*x^2 + 9, x^6 + 3*x^5 + 6, x^6 + 3*x^4 + 6,
  x^6 + 6*x^3 + 9*x^2 + 9, x^6 + 3*x^3 + 72,
  x^6 + 3*x^4 + 3*x^3 + 15, x^6 + 24, x^6 - x + 2,
  x^6 + 3*x + 6, x^6 + 3*x^5 + 15, x^6 + 3*x^4 + 15, x^6 + 18*x^2 + 36,
  x^6 + 18*x^2 + 9, x^6 + 3*x^4 + 9,
  x^6 + 9*x^2 + 9, x^6 + 3*x^4 + 6*x^3 + 9*x^2 + 63*x + 9,
    // containing zeta_3
    x^6 - 9*x^2+ 27, x^6+ 3*x+ 3, x^6+ 3*x^2+ 3, x^6+ 6*x^2+ 3, x^6+ 3*x^3+ 3*x^2+ 3, 
    x^6+ 6*x^4+ 21, x^6+ 6*x^4+ 3, x^6+ 6*x^4+ 12, x^6+ 3*x^4+ 3, x^6+ 6*x^5+ 6*x^4+ 21,
    x^6+ 6*x^5+ 6*x^4+ 12, x^6+ 6*x^4+ 6*x^3+ 12, x^6+ 3*x^4+ 6*x^3+ 3, x^6+ 3*x^5+ 12,
    x^6+ 6*x^5+ 21, x^6+ 3*x^5+ 3, x^6+ 21, x^6+ 12, x^6+ 3, x^6+ 18*x^3+ 12,
    x^6+ 9*x^3+ 21, x^6+ 18*x^3+ 3, x^6+ 6*x^3+ 3, x^6+ 12*x^3+ 18*x^2+ 3, x^6+ 3*x^3+ 3,
    x^6+ 3*x^3+ 12, x^6+ 18*x+ 12, x^6+ 21*x^3+ 12, x^6+ 15*x^3+ 3, 
    x^6+ 24*x^3+ 21, x^6+ 9*x+ 21,
  //Degree 7:
  x^7+x^2-x+1, x^7-3
];		
  
  return exts;
end function;


RelativeExtensionsOfQ_3zeta_3 := function(kpol, zeta_3);

// zeta_3 in k is a cube root of unity
T := kpol.1;
return [
  // Degree 2
  T^2 + 2*zeta_3+1,
  T^2 + zeta_3,
  // Degree 3
  T^3 + 2*T + 1,
  T^3 + 3*T+ 3,
  T^3 + 6*T+ 3,
  T^3 - 3*T^2+ 21,
  T^3 - 3*T^2+ 3,
  T^3 - 3*T^2+ 12,
  T^3 + 3*T^2+ 3,
  T^3 + 21,
  T^3 + 3*T - 3*zeta_3,
  T^3 + (-3*zeta_3 + 3)*T - 3,
  T^3 + (-3*zeta_3 + 3)*T - 3*zeta_3 - 3,
  T^3 - 3*T^2 - 3*zeta_3,
  T^3 - 3*T^2 - 3*zeta_3 - 3,
  T^3 - 3*T^2 + (-3*zeta_3 + 3)*T + 3,
  T^3 - 3*T^2 + (-3*zeta_3 + 3)*T - 3*zeta_3 - 3,
  T^3 + (-3*zeta_3 + 3)*T^2 - 3*zeta_3,
  T^3 + (-3*zeta_3 + 3)*T^2 + (-3*zeta_3 + 3)*T - 3,
  T^3 - 12*zeta_3,
  T^3 - 12*zeta_3 + 6,
  T^3 - 12*zeta_3 - 3,
  T^3 + 3*zeta_3 + 12,
  T^3 + 6*zeta_3,
  T^3 + 6*zeta_3 - 12,
  T^3 + 6*zeta_3 - 3,
  T^3 + 9*zeta_3 - 12,
  T^3 + 9*zeta_3 + 3,
  T^3 - 2*zeta_3 - 1,
  T^3 + 3*zeta_3*T^2 + (-3*zeta_3 - 3)*T - 4*zeta_3 - 1,
  T^3 + (-zeta_3 + 1)*T + 1,
  T^3 - zeta_3 + 1,
  T^3 - zeta_3 + 4,
  // Degree 4
  T^4 - zeta_3 + 1, 
  T^4 + 2*zeta_3*T^2 + 1, 
  T^4 + 2*T^3 + 2, 
  T^4 - 2*zeta_3*T^3 - zeta_3*T^2 + 2*T + 1,
  // Degree 5
  T^5 + 2*zeta_3 + 1,
  T^5 + 2*T + 1
];
end function;


AbsoluteExtensionsOfQ_5 := function(k0);

x := PolynomialRing(k0).1;

exts := [
  //Degree 2
  x^2-x+2, x^2-5, x^2+10,
  //Degree 3
  x^3-x+2, x^3-5,
  //Degree 4
  x^4+x^2-2*x+2, x^4+15*x^2+100, x^4-5*x^2+50,
  x^4-5, x^4-20, x^4+10, x^4+40,
  //Degree 5
  x^5-x+ 2, x^5+ 20*x+ 5, x^5+ 5*x+ 5,
  x^5+ 15*x+ 5, x^5+ 10*x+ 5, x^5+ 10*x^2+ 5,
  x^5+ 15*x^2+ 5, x^5+ 5*x^2+ 5, x^5+ 20*x^2+ 5,
  x^5+ 15*x^3+ 5, x^5+ 10*x^3+ 5, x^5+ 20*x^3+ 5,
  x^5+ 5*x^3+ 5, x^5- 5*x^4+ 105, x^5- 5*x^4+ 5,
  x^5- 5*x^4+ 30, x^5- 5*x^4+ 55, x^5- 5*x^4+ 80,
  x^5+ 5*x^4+ 5, x^5+ 10*x^4+ 5, x^5+ 15*x^4+ 5,
  x^5+ 5, x^5+ 55, x^5+ 80, x^5+ 30, x^5+ 105,
  //Degree 6
  x^6-x+2, x^6-10*x^4+25*x^2-500, x^6-25*x^2+250,
  x^6+25*x^3+200, x^6-5*x^3+50, x^6-5, x^6+10
];

return exts;
end function;

/* Those which contain 5-th roots of unity...
 x^4-20, //cyclotomic extension
 x^8-20, x^8 - 5*x^4 + 400, // totally ramified and unramified
 x^12- 10*x^8 + 25*x^4 - 500, x^12-20, // totally ramified and unramified
 x^16- 20, x^16+ 30*x^12+ 825*x^8+ 5000*x^4+ 10000 , x^16+ 155*x^8+ 6400, x^16- 5*x^8+ 400 ];
*/

RelativeExtensionsOfQ_5zeta_5 := function(kpol,zeta_5);

Z := kpol.1;
return [
  //Degree 2
  Z^2+(1-zeta_5), // ramified
  Z^2+(1+zeta_5), //unramified
  //Degree 3
  Z^3 + Z + zeta_5, //unramified
  Z^3+(1-zeta_5), //ramified
  //Degree 4
  Z^4 +(1+zeta_5), //unramified
  Z^4 +(1-zeta_5), //totally ramified 
  Z^4 + 4*Z^2 + 4*zeta_5, //contains both degree 2 extensions above
  Z^4 + (2*zeta_5 + 2)*Z^2 + (-4*zeta_5^3 + 4)*Z - 
    2*zeta_5^3 - zeta_5^2 + 2*zeta_5 // contains the unramified degree 2 extension above
  //Degree 5: maybe some day... (there are a lot)
  ];
end function;


RelativeExtensionsOfQ_pzeta_p := function(kpol,zeta_q);
  if zeta_q^2 eq 1 then
    return AbsoluteExtensionsOfQ_2(kpol);
  end if;

  if zeta_q^3 eq 1 then
    return RelativeExtensionsOfQ_3zeta_3(kpol,zeta_q);
  end if;

  if zeta_q^5 eq 1 then
    return RelativeExtensionsOfQ_5zeta_5(kpol,zeta_q);
  end if;
  return [];
end function;









	CompareRelandAbsolute := function(relpolys,abspolys,p);
	// check that a list of relative polynomials define
	// the same extension as a list of absolute polynomials.
	relcheck := [];
	abscheck := [];
	k := BaseRing(Parent(relpolys[1]));

	for g in relpolys do
		printf "\n\ng = %o defines the absolute extension \n", g;
		K := ext<k | g>;
		K := AbsoluteField(K);
		printf "%o.\n", K;
		v := Decomposition(K,p);
		printf " %o has decomposition type %o.\n",p, [ <Degree(pid[1]),pid[2]> : pid in v ];
		Kv := Completion(K,v[1][1]);
		Kv`DefaultPrecision *:= p;
		printf " comparing with absolute polynomials....\n";
		for h in abspolys do
			printf "  Checking h = %o.\n",h;
			if #Roots(h,Kv) gt 0 then	
				printf "     found %o roots of h in extension defined by g.\n", #Roots(h,Kv);
				L := ext<Rationals()|h>;
				w := Decomposition(L,p);
				printf " %o has decomposition type %o in L = Q[x]/h.\n",p, [ <Degree(pid[1]),pid[2]> : pid in w ];
				relcheck cat:= [g];
				abscheck cat:= [h];	
			end if;
		end for;
	end for;

	return relcheck, abscheck;
	end function;


	GetLucky := function(k,polys);
	// give a list of absolute polys 
	// check which have roots in k, then compute the relative extension

	d := Degree(k);
	f := DefiningPolynomial(k);
	relpolys := [];
	lucky := [];

	for g in polys do
		K := ext<Rationals() | g >;
		K := OptimisedRepresentation(K);
		sfd := [ sf[1] : sf in Subfields(K) | Degree(sf[1]) eq d ];
		for L in sfd do
			rts := Roots(f,L);
			if #rts gt 0 then
				// we found one
				lucky cat:= [g];
				Embed(k,K,rts[1][1]);
				Koverk := RelativeField(k,K);
				relpolys cat:= [DefiningPolynomial(Koverk)];
			end if;
		end for;
	end for;

	return relpolys, lucky;

	end function;

	
	BlindSearch := function( cfs, k, polys, p );
	
		found := <>;

		d := Degree(k);
		D := Degree(Random(polys));
		rd := D div d; // relative degree
		R := PolynomialRing(k); T := R.1;	

		checkagainst := polys;	
		ii := (#cfs)^(d*rd);	
		
		for a in CartesianProduct([  cfs : i in [1..d*rd] ]) do
			ii -:= 1;
			poly := R ! T^rd;
			for i in [1..rd] do
				poly +:= &+[ a[(i-1)*d + j ]*k.1^(j-1) : j in [1..d]]*T^(i-1);
			end for;
			if IsIrreducible(poly) then
				L := ext< k | poly >;
				L := AbsoluteField(L);
				L;
				dp := Decomposition(L,p);
				if #dp eq 1 then
					printf " # remaining %o.\n",ii;
					L_w := Completion(L,dp[1][1]);
					L_w`DefaultPrecision *:= 3;
					for g in polys do
						if #Roots(g,L_w) gt 0 then
							printf "\n\nfound one.\n";
							poly;
							g;
							checkagainst := checkagainst diff {g};
							found := Append(found, <g,poly>);
							if #checkagainst eq 0 then break; end if;
						end if;	
					end for;
				end if;
			end if;
		end for;

		return found;
	end function;



/*
//Construct tamely ramified extensions of completions of k(zeta_q).
//k  should be cyclotomic field
//O_k := Integers(k)
//O_v := Completion(O_k,v);

	k := CyclotomicField(q);
	kpol := PolynomialRing(k);
	v := Decomposition(k,p)[1][1];
	v := Ideal(v);
	k_v, ktok_v := Completion(k,v);
	O_k := Integers(k);
	O_k := Integers(k);
	O_v , O_ktoO_v := Completion(O_k,v);
	O_vtoO_k := Inverse(O_ktoO_v);
	O_vpol := PolynomialRing(O_v);
	Polytok_v := func< h | h ne 0 select Polynomial([ O_ktoO_v(c) : c in Coefficients(h)]) else O_vpol!0>;
	Polytok := func< h | Polynomial([ O_vtoO_k(c) : c in Coefficients(h)])>;
	F_v,modv := ResidueClassField(O_v);
	FF := PolynomialRing(F_v); xbar := FF.1;
	// functions for coercing polynomials around
	Polytok_v := func< h | h ne 0 select Polynomial([ O_ktoO_v(c) : c in Coefficients(h)]) else O_vpol!0>;
	Polytok := func< h | Polynomial([ O_vtoO_k(c) : c in Coefficients(h)])>;
	PolytoF_v := func< h | Polynomial([ modv(O_ktoO_v(c)) : c in Coefficients(h)])>;
	Polymodvtok := func< h | h ne 0 select Polynomial([ O_vtoO_k(c @@ modv)  : c in Coefficients(h)]) else kpol!0>;


	TamelyRamifiedPolys := function(d);
	
		//Computes polynomials (over k) which define all (at worst) tamely 
		//ramified extensions of k_v of degree d.
		//These will be plugged into TraceOfxminusT above
		
		// currently only for k_v = Q_p (though k may be of arbitrary degree),
		// or for d prime and k_v/Q_p unramified.
		
		polys := [  ];
		p := Characteristic(F_v);
		id := Ilog(p,#F_v);
		
		error if e_v gt 1, "Computation of tamely ramified extensions of k_v not implemented in this case: k_v/Q_p is ramified.\n";
		
		if id eq 1 then
			// k_v = Q_p
			Z_p := pAdicQuotientRing(p,2);
			for m in Divisors(d) do
				n := d div m;
				if n mod p ne 0 then
					// we construct extensions with ramification degree d/m = n
					R := ext< Z_p | m >;
					fR := Polynomial([ Rationals()! c : c in Coefficients(DefiningPolynomial(R))]);
					
					
					
					F_R,modw := ResidueClassField(R);
					zeta := PrimitiveElement(F_R)@@ modw;
					
					S := PolynomialRing(Rationals()); T := S.1;
					SS := PolynomialRing(S); TT := SS.1;
					
					exps := GCD(n,p^m -1);
					for s in [1..exps] do
						a_r := (zeta^s*p);
						a_rpol := &+[ Rationals()!(Eltseq(a_r)[i])*T^(i-1) : i in [1..#Eltseq(a_r)] ];
						polys cat:= [Resultant(Evaluate(fR,TT),(S.1-TT)^n+Evaluate(a_rpol,TT))];
					end for;
				end if;
			end for;
			return polys;
			
		else
			
			error if not IsPrime(d), "Computation of tamely ramified extensions of k_v not implemented in this case: k_v/Q_p nontrivial and d composite.";
			
			// this leaves totally ramified and totally unramified cases
			unr := Polymodvtok(IrreduciblePolynomial(F_v,d));
			unr := Polynomial([ c mod v : c in Coefficients(unr) ]);
			polys cat:= [ unr ];
			// this takes care of the unramified case.
			if d mod p ne 0 then 
				//we have some tamely ramified extensions to compute
				zeta := PrimitiveElement(F_v)@@ modv;
				zeta := O_vtoO_k(zeta) mod v; // we only need it to precision 1 
				exps := GCD(d,p^d -1);
				for s in [1..exps] do
					polys cat:= [ kpol.1^d - zeta^s*p ];
				end for;
			end if;
			return polys;
			
		end if; // id eq 1
		
	end function; // TamelyRamifiedPolys
*/












