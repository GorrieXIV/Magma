freeze;

/*
**   Dan Roozemond (dan.roozemond@sydney.edu.au)
**   
**   July 2010
**   
**   Melikian Lie Algebras.
**
*/

import "AlgCarTyp.m":aux, wittprodbrkt;

forward auxO, vectoquad;
forward divti, divtup, addtups, divadd;
forward Df;
forward mpol_to_melikian;

intrinsic MelikianLieAlgebra(F::Rng, n1::RngIntElt, n2::RngIntElt : Check := false) -> AlgLie
{ The Melikian Lie algebra M(n1, n2), over F }

	require Characteristic(F) eq 5 : "Characteristic of F should be 5";
	
	//Set up W(2), Witt multiplication
	p := Characteristic(F);
	W := WittLieAlgebra(F, 2, [n1,n2]);
	_,tau, n2pW, p2nW, ndszO := aux( Characteristic(F), 2, [n1, n2] );
	wittprod,wittbrkt := wittprodbrkt(F, 2, [n1,n2], tau, n2pW, p2nW);
	dimW := Dimension(W);
	
	//Set up O(2)
	dimO := p^(n1 + n2);
	O := VectorSpace(F, dimO);
	n2pO, p2nO := auxO(ndszO);
	
	//Set up vector spaces that will form the Melikian algebra
	dimM := p^(n1 + n2 + 1);
	assert dimM eq dimW + dimO + dimW;

	VS := VectorSpace(F, dimM);
	VSO := VectorSpace(F, dimO);
	VSW := VectorSpace(F, dimW);

	//Set up injections from W and O into M
	idxWtoMW1 := func<i | i>;
	idxOtoMO := func<i | dimW + i>;
	idxWtoMW2 := func<i | dimW + dimO + i>;
	
	//Compute multiplication table
	MT := [];
	
	tstart := Cputime();
	//[W1, W1]
	//Inherit multiplication from W
	//printf "[W1,W1] (dimW = %o, dimO = %o)\n", dimW, dimO;
	for i in [1..dimW] do for j in [(i+1)..dimW] do
		w := wittbrkt(i, j);
		for q in w do 
			Append(~MT, <idxWtoMW1(q[1]), idxWtoMW1(q[2]), idxWtoMW1(q[3]), q[4]>);
		end for;
	end for; end for;
	
	//[W1, W2]
	//[D, \~E] = \~([D, E]) + 2 div(D) \~E
	//printf "[W1,W2] %o %o\n", #MT, Cputime() - tstart;
	for i in [1..dimW] do for j in [1..dimW] do
		//Compute [D,E]
		v := Vector(W.i*W.j);
		
		//Compute  2 div(D) E
		t1 := p2nW(i); t2 := p2nW(j);
		c, t := divadd(F, tau, t1[2], t1[1], t2);
		if not IsZero(c) then 
			pos := n2pW(t); assert not IsZero(pos);
			v[pos] +:= 2*c;
		end if;
		
		vectoquad(idxWtoMW1(i), idxWtoMW2(j), v, idxWtoMW2, ~MT);
	end for; end for;
	
	//[W1, O]
	//[D, f] = D(f) - 2 div(D) f
	//printf "[W1,O] %o %o\n", #MT, Cputime() - tstart;
	for i in [1..dimW] do for j in [1..dimO] do
		t1 := p2nW(i); t2 := p2nO(j);
		
		c, t := Df(F, tau, t1, t2);
		p1 := 0;
		if not IsZero(c) then
			p1 := n2pO(t); assert not IsZero(p1); v1 := c;
		end if;

		t := divtup(t1);
		p2 := 0;
		if t cmpne 0 then
			c, tt := addtups(F, tau, t, t2);
			if not IsZero(c) then
				p2 := n2pO(tt); assert not IsZero(p2); v2 := -2*c;
			end if;
		end if;

		ii := idxWtoMW1(i); jj := idxOtoMO(j);
		if p1 ne 0 and p1 eq p2 then
			if v1+v2 ne 0 then
				MT cat:= [ <ii, jj, idxOtoMO(p1), v1+v2>, <jj, ii, idxOtoMO(p1), -(v1+v2)> ];
			end if;
		else
			if p1 ne 0 then MT cat:= [<ii,jj,idxOtoMO(p1),v1>, <jj,ii,idxOtoMO(p1),-v1>]; end if;
			if p2 ne 0 then MT cat:= [<ii,jj,idxOtoMO(p2),v2>, <jj,ii,idxOtoMO(p2),-v2>]; end if;
		end if;
	end for; end for;

	//[O, W2]
	//[f, \~E] := fE
	//printf "[O,W2] %o %o\n", #MT, Cputime() - tstart;
	for i in [1..dimO] do for j in [1..dimW] do
		t1 := p2nO(i); t2 := p2nW(j);
		
		c, t := addtups(F, tau, t1, t2);
		if not IsZero(c) then
			pos := n2pW(t); assert not IsZero(pos);
			Append(~MT, <idxOtoMO(i), idxWtoMW2(j), idxWtoMW1(pos), c>);
			Append(~MT, <idxWtoMW2(j), idxOtoMO(i), idxWtoMW1(pos), -c>);
		end if;
	end for; end for;
	
	//[O, O]
	//[f,g] = 2(g d2(f) - f d2(g)) \~d1 + 2( f d1(g) - gd1(f)) \~d2
	//printf "[O,O] %o %o\n", #MT, Cputime() - tstart;
	for i in [1..dimO] do for j in [(i+1)..dimO] do
		f := p2nO(i); g := p2nO(j);
		chgd := false; v := VSW!0;
		
		c, t := addtups(F, tau, g, divti(f, 2)); if not IsZero(c) then chgd := true; v[n2pW(<t,1>)] +:=  2*c; end if;
		c, t := addtups(F, tau, f, divti(g, 2)); if not IsZero(c) then chgd := true; v[n2pW(<t,1>)] +:= -2*c; end if;
		c, t := addtups(F, tau, f, divti(g, 1)); if not IsZero(c) then chgd := true; v[n2pW(<t,2>)] +:=  2*c; end if;
		c, t := addtups(F, tau, g, divti(f, 1)); if not IsZero(c) then chgd := true; v[n2pW(<t,2>)] +:= -2*c; end if;
		
		vectoquad(idxOtoMO(i), idxOtoMO(j), v, idxWtoMW2, ~MT);
	end for; end for;

	//[W2, W2]
	//[f1 ~d1 + f2 ~d2, g1 ~d1, g2 ~d2] = f1 g2 - f2 g1.
	//printf "[W2,W2] %o %o\n", #MT, Cputime() - tstart;
	for i in [1..dimO] do for j in [1..dimO] do 
		for d in [1..2] do
			f1 := < p2nO(i), d >; g2 := < p2nO(j), 3-d >;
			c,t := addtups(F, tau, f1[1], g2[1]);
			if not IsZero(c) then 
				Append(~MT, <idxWtoMW2(n2pW(f1)),idxWtoMW2(n2pW(g2)),idxOtoMO(n2pO(t)), (d eq 1 select 1 else -1)*c>);
			end if;
		end for;
	end for; end for; 
	
	//Construct Lie algebra
	//printf "MT... %o\n", Cputime() - tstart;
	M := LieAlgebra<F, dimM | MT : Check := Check>;

	return M, mpol_to_melikian(M, [n1,n2], dimW, dimO, idxWtoMW1, idxOtoMO, idxWtoMW2, n2pW, p2nW, n2pO, p2nO);
end intrinsic;


//
function auxO(ndszO)
	local i;
	
	P := [ t : t in ndszO ];
	return func<t | Position(P, t)>, func<i | P[i]>;
end function;




//div(t, i)
divti := function(t, i)
	local j;
	
	assert Type(t) eq Tup; assert Type(t[1]) eq RngIntElt;
	if t[i] eq 0 then 
		return 0;
	else
		t[i] -:= 1;
		return t;
	end if;
end function;

//div(f d_i) := d_i f (so that <<a,b>,1> --> <a-1,b> and <<a,b>,2> --> <a, b-1>)
divtup := function(t)
	local i;
	assert Type(t) eq Tup;
	assert #t eq 2;
	assert Type(t[1]) eq Tup;
	assert #t[1] eq 2;
	assert Type(t[2]) eq RngIntElt;
	
	return divti(t[1], t[2]);
end function;

//(d_i f) * g
divadd := function(F, tau, i, t1, t2)
	return addtups(F, tau, divti(t1, i), t2);
end function;

//addtups(p, <a,b>, <c,d>) = x^{[a,b]}*x^{[c,d]}
//addtups(p, <<a,b>,i>, <c,d>) = x^{[a,b]}*x^{[c,d]} delta_i
addtups := function(F, tau, t1, t2)
	local t, c, di, j, isw1, isw2, u1, u2, u;
	
	if t1 cmpeq 0 then return F!0,_; end if;
	if t2 cmpeq 0 then return F!0,_; end if;
	
	isw1 := Type(t1[1]) eq Tup;
	isw2 := Type(t2[1]) eq Tup;
	if isw1 and isw2 then error "addtups: Cannot BOTH be elts of W"; 
	elif isw1 then u1 := t1[1]; di := t1[2]; u2 := t2; 
	elif isw2 then u1 := t1; u2 := t2[1]; di := t2[2]; 
	else u1 := t1; u2 := t2; di := 0;
	end if;
	
	u := u1 + u2;
	if exists{j : j in [1..#tau] | u[j] gt tau[j]} then
		return F!0, _;
	end if;
	
	c := F!1;
	for j in [1..#tau] do
		c *:= Binomial(u[j], u1[j]);
		if IsZero(c) then return c, _; end if;
	end for;
	
	if di eq 0 then
		return c, u;
	else
		return c, <u, di>; 
	end if;
end function;

//D(f) : X... d_i (...)
// so that Df(F, tau, <<a,b>,1>, <c,d>) = <a+c-1, b+d>
Df := function(F, tau, t1, t2)
	local i, j, t;
	assert Type(t1) eq Tup; assert #t1 eq 2; assert Type(t1[1]) eq Tup;
	assert #t1[1] eq 2; assert Type(t1[2]) eq RngIntElt;
	
	assert Type(t2) eq Tup; assert #t2 eq 2; 
	assert Type(t2[1]) eq RngIntElt; assert Type(t2[2]) eq RngIntElt;
	
	return addtups(F, tau, divti(t2, t1[2]), t1[1]);
end function;

vectoquad := procedure(i, j, v, idxmp, ~MT : sym := true)
	local l;
	for l in [1..NumberOfColumns(v)] do
		if not IsZero(v[l]) then
			Append(~MT, <i, j, idxmp(l), v[l]>);
			if sym then Append(~MT, <j, i, idxmp(l), -v[l]>); end if;
		end if;
	end for;
end procedure;


/*
** A map assisting the end user in identifying the basis elements of a Witt lie algebra
*/
function mpol_to_melikian(M, n, dimW, dimO, idxWtoMW1, idxOtoMO, idxWtoMW2, n2pW, p2nW, n2pO, p2nO)
	local p, P, trmtoW, PtoW, bastoP, WtoP;
	
	m := 2; assert #n eq m;
	
	F := BaseRing(M);
	P := PolynomialRing(F, 3*m);
	AssignNames(~P, [ Sprintf("x%o",i) : i in [1..m] ] cat [ Sprintf("d%o",i) : i in [1..m]] cat [ Sprintf("dp%o",i) : i in [1..m]]);
	p := Characteristic(F);
	
	//Set up inverses of idx* (this may be overdoing things, but it's better than hardcoding positions here)
	posW1 := [ idxWtoMW1(i) : i in [1..dimW] ]; idxMW1toW := func<i | Position(posW1, i)>;
	posW2 := [ idxWtoMW2(i) : i in [1..dimW] ]; idxMW2toW := func<i | Position(posW2, i)>;
	posO := [ idxOtoMO(i) : i in [1..dimO] ]; idxMOtoO := func<i | Position(posO, i)>;
	
	trmtoM := function(trm)
		local i, dd, t, dok;
		
		t := <0 : i in [1..m]>;
		for i in [1..m] do
			if Degree(trm, P.i) gt p^(n[i])-1 then error Sprintf("trmtoM: Degree of x%o must be between 0 and %o", i, p^(n[i]) -1); end if;
			t[i] := Degree(trm, P.i);
		end for;
		
		dd := 0; dok := true;
		for i in [m+1..3*m] do
			if Degree(trm, P.i) eq 0 then continue; end if;
			if Degree(trm, P.i) ne 1 then dok := false; break; end if;
			if dd ne 0 then dok := false; break; end if;
			dd := i;
		end for;
		if not dok then error Sprintf("trmtoM: At most one of the d's and dp's must occur with degree one"); end if;
		
		if dd eq 0 then i := idxOtoMO(n2pO(t));
		elif dd in [m+1..2*m] then i := idxWtoMW1(n2pW(<t,dd-m>));
		elif dd in [2*m+1..3*m] then i := idxWtoMW2(n2pW(<t,dd-2*m>));
		else error Sprintf("trmtoM: dd = %o not expected.", dd); end if;
		
		return LeadingCoefficient(trm)*M.i;
	end function;
	PtoM := function(p)
		return &+[ trmtoM(t) : t in Terms(p) ];
	end function;
	
	bastoP := function(i)
		local t, r;
		assert i ge 1 and i le Dimension(M);
		if idxMW1toW(i) ne 0 then
			t := p2nW(idxMW1toW(i));
			return &*[ (P.j)^(t[1][j]) : j in [1..m] ]*P.(m+t[2]);
		elif idxMW2toW(i) ne 0 then
			t := p2nW(idxMW2toW(i));
			return &*[ (P.j)^(t[1][j]) : j in [1..m] ]*P.(2*m+t[2]);
		elif idxMOtoO(i) ne 0 then
			t := p2nO(idxMOtoO(i));
			return &*[ (P.j)^(t[j]) : j in [1..m] ];
		else
			error "Unexpected case in bastoP for Melikian Lie algebras";
		end if;
	end function;
	MtoP := function(m)
		return &+[ m[i]*bastoP(i) : i in [1..Dimension(M) ] ];
	end function;

	return map<P -> M | p :-> PtoM(p), m :-> MtoP(m) >;
end function;


