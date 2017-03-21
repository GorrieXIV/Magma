freeze;

random_MAX_SUM_LEN := 5;
random_MAX_PROD_LEN := 5;

import "big.m"    : projection,  big, compute_q, almost_little, rep,
          get_beta_bar, myeval, first_little, next_little, make_generic,
	  expand_phi, scalar_matrix;

import "matfunc.m" : pows_of, radical_power;

import "rand.m" : random_word, random_element, random_field_element;

//*********************************************************************

function cyclic_K_star(beta, beta_bar, d, q)

	beta_bars := pows_of(beta_bar, q-1);
	U := Generic(Parent(beta_bars[1]));
	map_bar := {@ U | beta_bar : beta_bar in beta_bars @};
	pow_bar := func< m | Index(map_bar, m) >;
	inverse_bar := func< m | 
		i eq q-1 select i else (q-1)-i where i := pow_bar(m) >;

	K_star := recformat
        <
                betas, beta_bars,
                pow_bar, inverse_bar
        >;

	return rec< K_star | 
		betas := pows_of(beta, q-1), 
		beta_bars := beta_bars,
		pow_bar := pow_bar,
		inverse_bar := inverse_bar>;
	
end function;

//**********************************************************************

is_non_zero_idempotent := func< x | x ne 0 and IsIdempotent(x) >;

//**********************************************************************

is_mut_orth := func< s |
                &and[is_non_zero_idempotent(x) : x in s] and
                &and[IsZero(s[i]*s[j]) and IsZero(s[j]*s[i]):
                                                i, j in [1..#s] | i ne j]>;

//**********************************************************************

function make_result(A, L, n_i, d_i, q_i, tau, tau_bar, 
		beta, beta_bar, g, g_bar, f_i, id, h_prime, s_g, s_g_bar)

       PerModInfo := recformat
        <
                PowersOfFieldGenerators,        // L
                Permutation,
                PermutationOnQuotient,         //tau, tau_bar,
                FieldGenerator,
                FieldGeneratorOnQuotient,          // beta, beta_bar,
                PrimitiveIdempotent,
                PrimitiveIdempotentOnQuotient,           //g, g_bar,
                GeneratingPolForCenter           //h_prime
        >;

	res := rec< PerModInfo | 
		PowersOfFieldGenerators := L, 
		Permutation := tau, 
                PermutationOnQuotient := tau_bar,
		FieldGenerator := beta, 
                FieldGeneratorOnQuotient := beta_bar,
		PrimitiveIdempotent := g, 
                PrimitiveIdempotentOnQuotient := g_bar, 
		GeneratingPolForCenter := h_prime
        >;

	return res;

end function;

//************************************************************************

function SS_generators_i(Lambda, phi, 
		phi_i, RI, n_i, d_i, q_i, invmat,invmat_i)

	A := Codomain(phi);
	A_i := Codomain(phi_i);
	GA_i := Generic(A_i);
	p := Characteristic(CoefficientRing(A));
	phi := expand_phi(phi);

        f_i :=  RI`AlgebraIdempotent;   
        g_1 :=  RI`PrimitiveIdempotent;    
        g_1_bar :=  RI`PrimitiveIdempotentOnQuotient;
        beta :=  RI`FieldGenerator; 
        beta_bar :=  RI`FieldGeneratorOnQuotient;
        h_prime :=   RI`GeneratingPolForCenter;

	// compute g_1, g_1_bar, beta, beta_bar, and h_prime

		vprint Presentation: "Little 1";

	L := cyclic_K_star(beta, beta_bar, d_i, q_i);

	//	initialise for the loop ahead

	/* AKS: */
	s_g := [make_generic(g_1)];
	s_g_bar := [make_generic(g_1_bar)];

	// if n_i = 1 we can bail out now

	if n_i eq 1 then
		return make_result(A, L, n_i, d_i, q_i, 
			g_1, g_1_bar, beta, beta_bar, g_1, g_1_bar, f_i, 
			GA_i!1, h_prime, s_g, s_g_bar);
	end if;	

	e := f_i - g_1;
	e_bar := GA_i!1 - g_1_bar;
	
	prod := f_i;
	prod_bar := GA_i!1;
	/*
	tau := A!0;
	tau_bar := GA_i!0;
	*/
OA := RI`OriginalAlgebra;
	tau := scalar_matrix(OA, 0);
//"NOW tau:", tau;
	tau_bar := scalar_matrix(GA_i, 0);

	pre := g_1;
	pre_bar := g_1_bar;
		
	//	compute g_2 through g_n, and g_2_bar through g_n_bar
	//	compute all the z_j and z_j bar except z_n and z_n_bar

	for j := 2 to n_i do
			vprint Presentation: "Little", j;

		//	compute g_j and g_j_bar

		if j eq n_i then
			
			g_j := e;
			g_j_bar := e_bar; 
		else

		  g_j, g_j_bar := next_little(Lambda, phi, phi_i, n_i, d_i, 
			 e, e_bar, s_g[#s_g], s_g_bar[#s_g], invmat, invmat_i);
		end if;

		Append(~s_g, g_j);
		Append(~s_g_bar, g_j_bar);

		e -:= g_j;
		e_bar -:= g_j_bar;
				
		//   compute z_j_bar in (g_(j-1)_bar A_i g_j_bar) and lift to 
		//	z_j in g_(j-1) A g_j

		w, z_j_bar := 
        	   random_element(Lambda, phi_i, pre_bar, g_j_bar);
		z_j := pre * phi(w) * g_j;

		tau +:= z_j;
		prod *:= z_j;
		tau_bar +:= z_j_bar;
		prod_bar *:= z_j_bar;
	
		//	roll pre and pre_bar over to g_j and g_j_bar

		pre := g_j;
		pre_bar := g_j_bar;
	
	end for;

	// construct z_n_bar as a 1 in the (n,1)-th spot
	
	g_n_bar := pre_bar;
	w, z_n_bar := 
		random_element(Lambda, phi_i, g_n_bar, g_1_bar);
	invpow := L`inverse_bar(prod_bar * z_n_bar);
	z_n_bar := z_n_bar * L`beta_bars[invpow];
		
	//	lift z_n_bar to z_n

	g_n := pre;
	z_n_prime := g_n * phi(w) * g_1;
	z_n_prime := z_n_prime * L`betas[invpow];
	prod_z_n_prime := prod * z_n_prime;

	l := radical_power(prod_z_n_prime - g_1);
	z_n := z_n_prime * (prod_z_n_prime)^(p^l-1);

	//	update tau and tau_bar

	tau +:= z_n;
	tau_bar +:= z_n_bar;
	return make_result(A, L, n_i, d_i, q_i, tau, tau_bar, 
				beta, beta_bar, g_1, g_1_bar, f_i, 
				GA_i!1, h_prime, s_g, s_g_bar);
	
end function;

//*******************************************************************

function SS_generators(RR, phi, s_phi, n, d, q)

	X := Domain(phi);
	A := Codomain(phi);
	r := #s_phi;
	ss_I := [];
	Lambda := [X.j : j in [1..Rank(X)]];
	invlst := [];
	inv_mat := [];
	ophi := phi;
	phi := expand_phi(phi);
	for j := 1 to #Lambda do
	   a,b := IsInvertible(phi(Lambda[j]));
	   if a then 
	       Append(~invlst, j);
	       Append(~inv_mat, [phi(Lambda[j]), b]);
	   end if;
	end for;
	for i := 1 to r do
           inv_mat_i := [[s_phi[i](Lambda[x]), s_phi[i](Lambda[x])^-1]:
			x in invlst];
	   vprint Presentation: "SS_generators Big",
	       i, "n_i, d_i, q_i =", n[i], d[i], q[i];
	   Append(~ss_I, SS_generators_i(Lambda, ophi, 
			s_phi[i], RR[i], n[i], d[i], q[i], inv_mat,inv_mat_i));
	end for;
		
	             return ss_I;

end function;

//**********************************************************************

intrinsic SemisimpleGeneratorData(A::AlgMat) -> SeqEnum
{The data on the semisimple generators of the algebra A.}

if assigned A`SemisimpleGeneratorData then
   return A`SemisimpleGeneratorData;
end if;
ff := CoefficientRing(A);
R1 := SimpleQuotientAlgebras(A);
R2 := PrimitiveIdempotentData(A);
phi := NaturalFreeAlgebraCover(A);
phii := R1`SimpleQuotients;
n := R1`DegreesOverCenters;
d := R1`DegreesOfCenters;
q := R1`OrdersOfCenters;

PP := FreeAlgebra(ff, Ngens(A));
SS := SS_generators(R2, phi, phii, n, d, q);
A`SemisimpleGeneratorData := SS;

return SS;

end intrinsic;
