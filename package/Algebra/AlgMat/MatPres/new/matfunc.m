freeze;

function isomorphism_classes(mods)

	isos := [mods[1]];
	for i := 2 to #mods do
		for j := 1 to #isos do
			if IsIsomorphic(mods[i], isos[j]) then
				continue i;
			end if;
		end for;
		Append(~isos, mods[i]);
	end for;

	return isos;

end function;

rep := func< X, A | hom< X -> A | [A.i : i in [1 .. Ngens(A)]] >>;

function inverting_polynomial(m)

	P := PolynomialRing(CoefficientRing(m)); x := P.1;
	h := P ! MinimalPolynomial(m);
	c := Coefficient(h, 0);
	return (c-h) div (c*x);

end function;

prod_pols := func< pols, m | Evaluate(&*pols, m) >;

prod_pols := function(pols, m)
    if ISA(Type(m), Mtrx) then
	m := Generic(Parent(m))!m;
    end if;
    return Evaluate(&*pols, m);
end function;

function make_idempotent(m, p)

	// p is the minimal polynomial of m. The function requires
	// that the variable x divide p to exactly the first power.

	P := Parent(p);
	h := p div P.1;
	a := -Evaluate(h,CoefficientRing(P)!0);
	g := a^-1*(h+a*P!1);
	return Evaluate(g,m), g;

end function;
	
//**********************************************************************

function power_to_idempotent(m)

	j := 1;
	res := m;
	while not IsIdempotent(res) do
		res *:= m;
		j +:= 1;
	end while;

//"power_to_idempotent j:", j;
	return res, j;

end function;

function lift_p(m)

	p := Characteristic(CoefficientRing(m));
	j := 1;
	while not IsIdempotent(m) do
		m ^:= p;
		j +:= 1;
	end while;
			
//"lift_p j:", j;
	return m, j;
		
end function;

function radical_power(m)

	isNP, c := IsNilpotent(m);
	assert isNP;
	return c;

end function;

function pows_of(m, n)

/*
"****";
m;
"pows_of", Parent(m), n;
Density(m);
// time FactoredMinimalPolynomial(m);
F := PrimaryInvariantFactors(m);
{* t: t in F *};
P<x> := Parent(F[1,1]);
[Order(CompanionMatrix(t[1])): t in F | t[1] ne x];
*/

	res := [m];
	temp := m;
	for i := 2 to n do
		temp := temp*m;
		Append(~res, temp);
	end for;
	return res;

end function;

all_degree := func< C, n | [ x : x in C | Dimension(x) eq n]>;

degree := func< C, n | all_degree(C, n)[1] >;

function all_degree_M(M, n)
	CF := CompositionFactors(M);
	C := isomorphism_classes(CF);
	return all_degree(C, n);
end function;

function degree_M(M, n)
	CF := CompositionFactors(M);
	C := isomorphism_classes(CF);
	return degree(C, n);
end function;

flatten := func<J, f | [f(x) : x in J[i][j], i, j in [1 ..#J]]>;

function map(J, f)

	r := #J;
	T := Seqlist([Seqlist([[] : i in [1..r]]) : j in [1..r]]);
	for i := 1 to r do
		for j := 1 to r do
			T[i][j] := [f(x) : x in J[i][j]];
		end for;
	end for;

	return T;
end function;

