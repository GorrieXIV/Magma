freeze;

import     "rand.m" : random_element1, random_word, random_field_element,
  random_element;

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

function projection(Lambda, i, s_phi, notdone)

	repeat
		w, m := random_element1(Lambda, s_phi[i]);
		F := [MinimalPolynomial(s_phi[j](w)) : j in notdone];
		a_i_bar := prod_pols(F, m);
	until not IsZero(a_i_bar);

	return w, F, a_i_bar;

end function;

//***********************************************************************

function big(Lambda, phi, i, s_phi, e, nddd)

	A_i := Codomain(s_phi[i]);
	rank := Degree(Codomain(s_phi[i]));
	sum_a_i_bar := A_i!0;
	wlist := [];
	plist := [];

	while true do

		w, F, a_i_bar := projection(Lambda, i, s_phi, nddd);

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
//"e:", e; "sum_m:", sum_m;
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

function almost_little(Lambda, phi_i, n_i, d_i, e)

	P := PolynomialRing(CoefficientRing(Domain(phi_i))); x := P.1;

	if n_i eq 1 then
		w, a := random_element(Lambda, phi_i, e, e);
		return w, x, a;
	else

		while true do
		  w, m := random_element(Lambda, phi_i, e, e);
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

function get_beta_bar(Lambda, phi, phi_i, n_i, d_i, q_i)

	id := Generic(Codomain(phi_i))!1;

	repeat
	   w, F, beta_bar := 
			almost_little(Lambda, phi_i, n_i, d_i, id);
	until #Seqset(pows_of(beta_bar, q_i-1)) eq q_i-1;

	return w, F, beta_bar;

end function;

//*********************************************************************

function almost_little2(Lambda, phi_i, n_i, d_i, e, f, inv_lst)

        P := PolynomialRing(CoefficientRing(Domain(phi_i))); x := P.1;

        if n_i eq 1 then
                w, a := random_element(Lambda, phi_i, e, e);
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
                  w, m := random_element(Lambda, phi_i, e, e);
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

function first_little(Lambda, phi, phi_i, f_i, n_i, d_i, q_i)

	w, F, beta_bar := 
		get_beta_bar(Lambda, phi, phi_i, n_i, d_i, q_i);
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
/*
function next_little(Lambda, phi, phi_i, n_i, d_i, e_i, e_i_bar)

	w, F, g_bar, mp := 
		almost_little(Lambda, phi_i, n_i, d_i, e_i_bar);
	g_prime := e_i * Evaluate(F, e_i * phi(w) * e_i) * e_i;
//	g_bar, j := make_idempotent(g_bar,mp);
			g_bar, j := power_to_idempotent(g_bar);
//	g := power_to_idempotent(Evaluate(j,g_prime));
			g := power_to_idempotent(g_prime^j);	

	return g, g_bar;

end function;
*/

function next_little(Lambda, phi, phi_i, n_i, d_i, e_i, e_i_bar, 
		f, f_bar, invlst, invlst_i)

        w, F, g_bar, mp, tt :=
           almost_little2(Lambda, phi_i, n_i, d_i, e_i_bar, f_bar, invlst_i);

	if tt eq 1 then 
//"e_i:", e_i; "invlst[w][1]:", invlst[w][1];
	   g_prime := e_i * invlst[w][1] * f * invlst[w][2] * e_i;
	end if;
	if tt eq 2 then 
           g_prime := e_i * Evaluate(F, e_i * phi(w) * e_i) * e_i;
	end if;

           g_bar, j := make_idempotent(g_bar,mp);
                      //  g_bar, j := power_to_idempotent(g_bar);
           g := power_to_idempotent(Evaluate(j,g_prime));
                      //  g := power_to_idempotent(g_prime^j);

        return g, g_bar;

end function;

//*********************************************************************

intrinsic PrimitiveIdempotentData(A::AlgMat)  ->  SeqEnum 
{The initial data for a decomposition of the matrix algebra A. The output
is a sequence of records, one for each simple quotient algrbra of A, each
consisting of an  idempotent which is the identity on the simple quotient,
primitive idempotents for the algebra and the quotient, field generators
for the algebra and the quotient and defining polynomial for the center
of the quotient.}

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
    Lambda := [X.j : j in [1..Rank(X)]];

    /*
    PrimIdData := recformat<AlgebraIdempotent:AlgMatElt,
			    PrimitiveIdempotent:AlgMatElt,
			    PrimitiveIdempotentOnQuotient:AlgMatElt,
			    FieldGenerator:AlgMatElt,
			    FieldGeneratorOnQuotient:AlgMatElt,
			    GeneratingPolForCenter:RngUPolElt>;
    */

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
//print aa, bb, nn;
	Append(~reclst,bb);
        vprint Presentation: "Big", bb, "n_i, d_i, q_i =", n[bb], d[bb], q[bb];

//	vprint Presentation: "Big", i, "n_i, d_i, q_i =", n[i], d[i], q[i];
//"e DiagonalBlocksStructure:", DiagonalBlocksStructure(e);

	if i eq r then
     		f_i := e;
      	else 
                nnn := nn;
                nnn[bb] := 0;
                nddd := [i: i in [1 .. #nnn]| nnn[i] ne 0];
                f_i := big(Lambda, phi, bb, philst, e, nddd);
//       	        f_i := big(Lambda, phi, i, philst, e);
       	end if;
       	e -:= f_i;
        g_1, g_1_bar, beta, beta_bar, h_prime :=
                first_little(Lambda, phi, philst[bb], f_i, n[bb], d[bb], q[bb]);

//                first_little(Lambda, phi, philst[i], f_i, n[i], d[i], q[i]);

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

//    A`PrimitiveIdempotentData := RR;

//    return RR;

              return RRR;


end intrinsic;

//*********************************************************************

intrinsic PrimitiveIdempotents(A::AlgMat) -> SeqEnum
{A list of primitive idempotent for the matrix algebra A, one idempotent
for each irreducible module.}

RR := PrimitiveIdempotentData(A);
ss := [RR[i]`PrimitiveIdempotent: i in [1 .. #RR]];

               return ss;

end intrinsic;

//*********************************************************************

intrinsic RanksOfPrimitiveIdempotents(A::AlgMat) -> SeqEnum
{The sequence of ranks of the primitive idempotents for the matrix
algebra A}

if assigned A`RanksOfPrimitiveIdempotents then 
   return A`RanksOfPrimitiveIdempotents;
end if;
dd := [Rank(x):x in PrimitiveIdempotents(A)];
A`RanksOfPrimitiveIdempotents := dd;

        return dd;

end intrinsic;
