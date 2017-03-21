freeze;

import     "rand.m" : random_element1, random_element1_m, random_element,
  random_element_m, random_element2;

import     "matfunc.m": prod_pols,inverting_polynomial,power_to_idempotent,
  lift_p,radical_power,pows_of,all_degree,degree_M,flatten,map,make_idempotent;

//**********************************************************************

function make_generic(X)
    if ISA(Type(X), Mtrx) then
        X := Generic(Parent(X))!X;
    end if;
    return X;
end function;

function scalar_matrix(A, x)
    if assigned A`DiagonalBlockStructure then
        B := A`DiagonalBlockStructure;
	return BlockDiagScalarMat(B, x);
    else
        return Generic(A)!x;
    end if;
end function;

function expand_phi(phi)
    if assigned phi`DiagMap then
	return phi`DiagMap;
    end if;
    return phi;
end function;

//**********************************************************************

function projection_m(Lambda, i, s_phi, notdone, lim1, lim2)

	repeat
		w, m := random_element1_m(Lambda, s_phi[i], lim1, lim2);
		F := [MinimalPolynomial(s_phi[j](w)) : j in notdone];
		a_i_bar := prod_pols(F, m);
	until not IsZero(a_i_bar);

	return w, F, a_i_bar;

end function;

//***********************************************************************

function big_m(Lambda, phi, i, s_phi, e, nddd, lim1, lim2)

	A_i := Codomain(s_phi[i]);
	rank := Degree(Codomain(s_phi[i]));
	sum_a_i_bar := A_i!0;
	wlist := [];
	plist := [];

	while true do

		w, F, a_i_bar := projection_m(Lambda, i, s_phi, nddd, 
                           lim1, lim2);

		if Rank(a_i_bar) eq rank then
			g := inverting_polynomial(a_i_bar);
			m := prod_pols(F, phi(w));
			a := e * (m * Evaluate(g, m)) * e;
			f := lift_p(a);
			return f;
		else 
			Append(~wlist, w);
			Append(~plist, F);
			sum_a_i_bar +:= a_i_bar;
			if Rank(sum_a_i_bar) eq rank then
			    g := inverting_polynomial(sum_a_i_bar);
			    sum_m := &+[prod_pols(plist[j], phi(wlist[j])) : 
					       j in [1 .. #wlist]];
			    a := e * sum_m * Evaluate(g, sum_m) * e;
			    f := lift_p(a);
			    return f;
			end if;
		end if;
	end while;

end function;

//*********************************************************************

function compute_q(q, j)

	q_to_the_k := q;
	while q_to_the_k lt j do
		q_to_the_k *:= q;
	end while;
	return q_to_the_k;

end function;

//***********************************************************************

function almost_little_m(Lambda, phi_i, n_i, d_i, e, lim1, lim2)

	P := PolynomialRing(CoefficientRing(Domain(phi_i))); x := P.1;

	if n_i eq 1 then
		w, a := random_element_m(Lambda, phi_i, e, e, lim1, lim2);
		return w, x, a;
	else

		while true do
		  w, m := random_element_m(Lambda, phi_i, e, e, lim1, lim2);
		  g := MinimalPolynomial(m);
		  for fac in Factorization(g) do
	             f := fac[1];
		     if Degree(f) eq d_i then
			 F := g div f;
			 a := e* Evaluate(F, m);
			 if Rank(a) eq d_i then
			    ff := P!MinimalPolynomial(a);
			    if not IsDivisibleBy(ff, x^2) then 
			       return w, F, a, ff;
			    end if;
			 end if;
		      end if;
		   end for;
		end while;

	end if;

end function;

//**********************************************************************

function get_beta_bar_m(Lambda, phi, phi_i, n_i, d_i, q_i, lim1, lim2)

	id := Generic(Codomain(phi_i))!1;

	repeat
	   w, F, beta_bar := 
	          almost_little_m(Lambda, phi_i, n_i, d_i, id, lim1, lim2);
	until #Seqset(pows_of(beta_bar, q_i-1)) eq q_i-1;

	return w, F, beta_bar;

end function;

//*********************************************************************

function almost_little2_m(Lambda, phi_i, n_i, d_i, e, f, inv_lst, lim1, lim2)

        P := PolynomialRing(CoefficientRing(Domain(phi_i))); x := P.1;

        if n_i eq 1 then
                w, a := random_element_m(Lambda, phi_i, e, e, lim1, lim2);
                return w, x, a;
        else
	    if #inv_lst ge 1 then 
	      for i := 1 to #inv_lst do				// new stuff
		a := e*inv_lst[i][1]*f*inv_lst[i][2]*e;
		if Rank(a) eq d_i then
                   ff := P!MinimalPolynomial(a);
                   if not IsDivisibleBy(ff, x^2) then
                        return i, i, a, ff, 1;
                   end if;
                end if;
   	      end for;
	    end if;					// end new stuff
		
            while true do
                  w, m := random_element_m(Lambda, phi_i, e, e, lim1, lim2);
                  g := MinimalPolynomial(m);
                  for fac in Factorization(g) do
                     f := fac[1];
                     if Degree(f) eq d_i then
                         F := g div f;
                         a := e* Evaluate(F, m);
                         if Rank(a) eq d_i then
                           ff := P!MinimalPolynomial(a);
                            if not IsDivisibleBy(ff, x^2) then
                               return w, F, a, ff, 2;
                            end if;
                         end if;
                      end if;
                   end for;
            end while;

        end if;

end function;

//***********************************************************************

myeval := func<F, X | Evaluate(F, make_generic(X))>;

//***********************************************************************

is_non_zero_idempotent := func< x | not IsZero(x) and IsIdempotent(x) >;

//**********************************************************************

function first_little_m(Lambda, phi, phi_i, f_i, n_i, d_i, q_i, lim1, lim2)

	w, F, beta_bar := 
		get_beta_bar_m(Lambda, phi, phi_i, n_i, d_i, q_i, lim1, lim2);
	g_bar := beta_bar^(q_i-1);

 	gamma := f_i * myeval(F, phi(w)) * f_i;
	g := gamma^(q_i-1);
	while not is_non_zero_idempotent(g) do
		g ^:= q_i;
		gamma ^:= q_i;
	end while;

	f := MinimalPolynomial(beta_bar);
	h_prime := n_i eq 1 select Parent(f).1 * f else f;

	k := radical_power(myeval(h_prime, gamma));
	j := compute_q(q_i, k);
	beta := gamma^j;

	return g, g_bar, beta, beta_bar, h_prime;

end function;

//**********************************************************************

function next_little_m(Lambda, phi, phi_i, n_i, d_i, e_i, e_i_bar, 
		f, f_bar, invlst, invlst_i, lim1, lim2)

        w, F, g_bar, mp, tt :=
           almost_little2_m(Lambda, phi_i, 
               n_i, d_i, e_i_bar, f_bar, invlst_i, lim1, lim2);

	if tt eq 1 then 
	   g_prime := e_i * invlst[w][1] * f * invlst[w][2] * e_i;
	end if;
	if tt eq 2 then 
           g_prime := e_i * Evaluate(F, e_i * phi(w) * e_i) * e_i;
	end if;

           g_bar, j := make_idempotent(g_bar,mp);
           g := power_to_idempotent(Evaluate(j,g_prime));

        return g, g_bar;

end function;

//**********************************************************************

function projection(A, i, s_phi, notdone)

   repeat
      w, m := random_element1(A, s_phi[i]);
      F := [MinimalPolynomial(s_phi[j](w)) : j in notdone];
      a_i_bar := prod_pols(F, m);
   until not IsZero(a_i_bar);

	return w, F, a_i_bar;

end function;

//***********************************************************************

function big(A, phi, i, s_phi, e, nddd)

   A_i := Codomain(s_phi[i]);
   rank := Degree(Codomain(s_phi[i]));
   sum_a_i_bar := A_i!0;
   wlist := [];
   plist := [];
   while true do

      w, F, a_i_bar := 
                projection(A, i, s_phi, nddd);

      if Rank(a_i_bar) eq rank then
		g := inverting_polynomial(a_i_bar);
		m := prod_pols(F, phi(w));
		a := e * (m * Evaluate(g, m)) * e;
		f := lift_p(a);

		   return f;
	else 
		Append(~wlist, w);
		Append(~plist, F);
		sum_a_i_bar +:= a_i_bar;
		if Rank(sum_a_i_bar) eq rank then
		   g := inverting_polynomial(sum_a_i_bar);
		   sum_m := &+[prod_pols(plist[j], phi(wlist[j])) : 
					       j in [1 .. #wlist]];
		   a := e * sum_m * Evaluate(g, sum_m) * e;
		   f := lift_p(a);

		    return f;
		end if;
	end if;
   end while;

end function;

//*********************************************************************

function almost_little(A, phi_i, n_i, d_i, e)

	P := PolynomialRing(CoefficientRing(Domain(phi_i))); x := P.1;

	if n_i eq 1 then
	   w, a := random_element(A, phi_i, e, e);
	   return w, x, a;
	else
		while true do
		  w, m := 
                     random_element(A, phi_i, e, e);
		  g := MinimalPolynomial(m);
		  for fac in Factorization(g) do
	             f := fac[1];
		     if Degree(f) eq d_i then
			 F := g div f;
			 a := e* Evaluate(F, m);
			 if Rank(a) eq d_i then
			    ff := P!MinimalPolynomial(a);
			    if not IsDivisibleBy(ff, x^2) then 
			       return w, F, a;
			    end if;
			 end if;
		      end if;
		   end for;
		end while;

	end if;

end function;

//**********************************************************************

function get_beta_bar(A, phi, phi_i, n_i, d_i, q_i)

	id := Generic(Codomain(phi_i))!1;
	repeat
	   w, F, beta_bar := 
		almost_little(A, phi_i, n_i, d_i, id);
	until #Seqset(pows_of(beta_bar, q_i-1)) eq q_i-1;
	return w, F, beta_bar;

end function;

//*********************************************************************

function almost_little2(A, phi_i, n_i, d_i, e, f, inv_lst)

        P := PolynomialRing(CoefficientRing(Domain(phi_i))); x := P.1;
   	spin := A`SpinMatrices;
   	boo := A`SpinDone;
   	mons := A`SpinMonomials;
   	V := A`SpinVectors;
	m := mons[1];
	a := e;
        if n_i eq 1 then
            random_element2(A,~spin, ~mons, ~V, ~boo, phi_i, e, e, ~w, ~a);
                return w, x, a, P!1, 0;
        else
	    if #inv_lst ge 1 then 
	      for i := 1 to #inv_lst do				// new stuff
		a := e*inv_lst[i][1]*f*inv_lst[i][2]*e;
		if Rank(a) eq d_i then
                   ff := P!MinimalPolynomial(a);
                   if not IsDivisibleBy(ff, x^2) then
                        return i, i, a, ff, 1;
                   end if;
                end if;
   	      end for;
	    end if;					// end new stuff
            while true do
                  w := mons[1];
                  m := e;
                  random_element2(A,~spin, ~mons, ~V, ~boo, phi_i, e, e, ~w, ~m);
                  g := MinimalPolynomial(m);
                  for fac in Factorization(g) do
                     f := fac[1];
                     if Degree(f) eq d_i then
                         F := g div f;
                         a := e* Evaluate(F, m);
                         if Rank(a) eq d_i then
                           ff := P!MinimalPolynomial(a);
                            if not IsDivisibleBy(ff, x^2) then
                               return w, F, a, ff, 2;
                            end if;
                         end if;
                      end if;
                   end for;
            end while;

        end if;

end function;

//***********************************************************************

is_non_zero_idempotent := func< x | not IsZero(x) and IsIdempotent(x) >;

//**********************************************************************

function first_little(A, phi, phi_i, f_i, n_i, d_i, q_i)

	w, F, beta_bar := 
		get_beta_bar(A, phi, phi_i, n_i, d_i, q_i);
	g_bar := beta_bar^(q_i-1);

 	gamma := f_i * myeval(F, phi(w)) * f_i;
	g := gamma^(q_i-1);
	while not is_non_zero_idempotent(g) do
		g ^:= q_i;
		gamma ^:= q_i;
	end while;

	f := MinimalPolynomial(beta_bar);
	h_prime := n_i eq 1 select Parent(f).1 * f else f;

	k := radical_power(myeval(h_prime, gamma));
	j := compute_q(q_i, k);
	beta := gamma^j;
	return g, g_bar, beta, beta_bar, h_prime;

end function;

//**********************************************************************

function next_little(A, phi, phi_i, n_i, d_i, e_i, e_i_bar, 
		f, f_bar, invlst, invlst_i)

        w, F, g_bar, mp, tt :=
           almost_little2(A, phi_i, n_i, d_i, e_i_bar, f_bar, invlst_i);

	if tt eq 1 then 
	   g_prime := e_i * invlst[w][1] * f * invlst[w][2] * e_i;
	end if;
	if tt eq 2 then 
           g_prime := e_i * Evaluate(F, e_i * phi(w) * e_i) * e_i;
	end if;

           g_bar, j := make_idempotent(g_bar,mp);
           g := power_to_idempotent(Evaluate(j,g_prime));

        return g, g_bar;

end function;

//*********************************************************************

intrinsic PrimitiveIdempotentData(A::AlgMat : Rand := "PartSpin", 
	  limprod := 7, limsum := 8)  ->  SeqEnum 

{The initial data for a decomposition of the matrix algebra A. The output
is a sequence of records, one for each simple quotient algrbra of A, each
consisting of an  idempotent which is the identity on the simple quotient,
primitive idempotents for the algebra and the quotient, field generators
for the algebra and the quotient and defining polynomial for the center
of the quotient.

The user has two choices of randomization. The default is "PartSpin", which
begins a spin and takes random linear combinations as the rendom elements.
This should work for all algebra. The second is "Meataxe", which evaluated
small polynomials on the generators. The user can choose the maximum degree
of the monomals in the polynomial ("limprod") and the maximum number of 
terms in the polynomial ("limsum"). The defaults are 7 and 8 respectively.
The "Meataxe" method is faster for many algebras such as actions of groups
on modules, but it may fail completely in other cases. 
}

	require Rand in {"PartSpin", "Meataxe"} : 
   "\n   *** Error in parameter: Unknown algorithm specified.\n";
        require IsFinite(BaseRing(A)) : 
    "\n Coefficient ring is not finite. \n";

    if assigned A`PrimitiveIdempotentData then 
	    return A`PrimitiveIdempotentData;
    end if;
    RS := SimpleQuotientAlgebras(A);
    n := RS`DegreesOverCenters;
    d := RS`DegreesOfCenters;
    q := RS`OrdersOfCenters;

    ff := CoefficientRing(A);
    p := Characteristic(ff);
    phi := NaturalFreeAlgebraCover(A);
    philst := RS`SimpleQuotients;
    X := Domain(phi);
    phi := expand_phi(phi);

    vprint Presentation: "PrimitiveIdempotentData A:", A;

    GA := Generic(A);
    e := scalar_matrix(A, 1);

    RR := []; 

    if Rand eq "PartSpin" then 
       gens := [A.i: i in [1 .. Ngens(A)]];
       A`SpinGenerators := gens;
       A`SpinMatrices := [GA!x:x in gens];
       A`SpinMonomials := [X.j : j in [1..Rank(X)]];
       VG := KMatrixSpace(ff, Degree(A), Degree(A));
       A`SpinVectors := sub< VG| [VG!x: x in gens]>;
       A`SpinDone := false;
    else 
       random_MAX_SUM_LEN := limsum;
       random_MAX_PROD_LEN := limprod;
       Lambda := [X.j : j in [1..Rank(X)]];
    end if;

    PrimIdData := recformat<AlgebraIdempotent,
			    PrimitiveIdempotent,
			    PrimitiveIdempotentOnQuotient,
			    FieldGenerator,
			    FieldGeneratorOnQuotient,
			    GeneratingPolForCenter:RngUPolElt,
			    OriginalAlgebra:AlgMat>;

    r := #n;

    nn := n;
    reclst := [];


    for i := 1 to r do
	aa, bb := Maximum(nn);
	Append(~reclst,bb);
        vprint Presentation: "Big", bb, "n_i, d_i, q_i =", n[bb], d[bb], q[bb];

	if i eq r then
     		f_i := e;
      	else 
                nnn := nn;
                nnn[bb] := 0;
                nddd := [i: i in [1 .. #nnn]| nnn[i] ne 0];
                if Rand eq "PartSpin" then 
                   f_i := big(A, phi, bb, philst, e, nddd);
                else
                   f_i := big_m(Lambda, phi, bb, philst, e, nddd, 
				limprod, limsum);
                end if;
       	end if;
       	e -:= f_i;
        if Rand eq "PartSpin" then 
            g_1, g_1_bar, beta, beta_bar, h_prime :=
                first_little(A, phi, philst[bb], f_i, n[bb], d[bb], q[bb]);
        else
            g_1, g_1_bar, beta, beta_bar, h_prime :=
                first_little_m(Lambda, phi, philst[bb], f_i, 
                      n[bb], d[bb], q[bb], limprod, limsum);
	end if;
        Ri := rec<PrimIdData |AlgebraIdempotent        := make_generic(f_i),
		        PrimitiveIdempotent            := g_1,
			PrimitiveIdempotentOnQuotient  := g_1_bar,
			FieldGenerator                 := beta,
			FieldGeneratorOnQuotient       := beta_bar,
			GeneratingPolForCenter         := h_prime,
			OriginalAlgebra		       := A>;
        Append(~RR,Ri);
        nn[bb] := 0;
    end for;
    RRR := [];
    for i := 1 to r do
         RRR[i] := RR[Index(reclst,i)];
    end for;

        A`PrimitiveIdempotentData := RRR;

              return RRR;


end intrinsic;

//*********************************************************************

intrinsic PrimitiveIdempotents(A::AlgMat :  Rand := "PartSpin",
          limprod := 7, limsum := 8) -> SeqEnum
{A list of primitive idempotent for the matrix algebra A, one idempotent
for each irreducible module.

The user has two choices of randomization. The default is "PartSpin", which
begins a spin and takes random linear combinations as the rendom elements.
This should work for all algebra. The second is "Meataxe", which evaluated
small polynomials on the generators. The user can choose the maximum degree
of the monomals in the polynomial ("limprod") and the maximum number of 
terms in the polynomial ("limsum"). The defaults are 7 and 8 respectively.
The "Meataxe" method is faster for many algebras such as actions of groups
on modules, but it may fail completely in other cases. 
}

        require Rand in {"PartSpin", "Meataxe"} :
   "\n   *** Error in parameter: Unknown algorithm specified.\n";

if Rand eq "PartSpin" then 
   RR := PrimitiveIdempotentData(A : Rand := "PartSpin");
else 
   a := limprod; 
   b := limsum;
   RR := PrimitiveIdempotentData(A : Rand := "Meataxe", limprod := a, 
         limsum := b);
end if;
ss := [RR[i]`PrimitiveIdempotent: i in 
            [1 .. #SimpleQuotientAlgebras(A)`DegreesOverCenters]];

               return ss;

end intrinsic;

//*********************************************************************

intrinsic RanksOfPrimitiveIdempotents(A::AlgMat :  Rand := "PartSpin",
          limprod := 7, limsum := 8) -> SeqEnum
{The sequence of ranks of the primitive idempotents for the matrix
algebra A.

The user has two choices of randomization. The default is "PartSpin", which
begins a spin and takes random linear combinations as the rendom elements.
This should work for all algebra. The second is "Meataxe", which evaluated
small polynomials on the generators. The user can choose the maximum degree
of the monomals in the polynomial ("limprod") and the maximum number of 
terms in the polynomial ("limsum"). The defaults are 7 and 8 respectively.
The "Meataxe" method is faster for many algebras such as actions of groups
on modules, but it may fail completely in other cases. 
}

        require Rand in {"PartSpin", "Meataxe"} :
   "\n   *** Error in parameter: Unknown algorithm specified.\n";

if assigned A`RanksOfPrimitiveIdempotents then 
   return A`RanksOfPrimitiveIdempotents;
end if;
if Rand eq "PartSpin" then
   pi := PrimitiveIdempotents(A : Rand := "PartSpin");
else
   a := limprod;
   b := limsum;
   pi := PrimitiveIdempotents(A : Rand := "Meataxe", limprod := a, 
        limsum := b);
end if;

dd := [Rank(x):x in pi];
A`RanksOfPrimitiveIdempotents := dd;

        return dd;

end intrinsic;
