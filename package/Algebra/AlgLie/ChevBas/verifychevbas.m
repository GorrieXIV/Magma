freeze;

/* 
 * Dan Roozemond, 2010. 
 */

/* This file is self-contained to improve robustness of the checks */

findeigenv := function(h, x)
	local exh, ex, xh, i, t, nzp;

	if IsZero(x) then return 0; end if;

	ex := Eltseq(x);
	xh := x*h;
	exh := Eltseq(xh);
	nzp := exists(i){ i : i in [1..#ex] | ex[i] ne 0};
	if nzp then
		t := exh[i]/ex[i];
		if ( t*x eq xh ) then return t; end if;
	end if;
	return false;
end function;

ismultof := function(a, b)
	//returns i st i*a = b
	local N, nzp, t;
	N := NumberOfColumns(a);
	nzp := exists(i){ i : i in [1..N] | a[i] ne 0};
	if nzp then
		//a is nonzero
		t := b[i]/a[i];
		if ( t*a eq b ) then 
			return t; 
		else
			return false;
		end if;
	elif IsZero(b) then
		//a and b both zero
		return One(BaseRing(a));
	else
		//a is zero, b is not
		return false;
	end if;
end function;


findp := function(Rts, r, s)
	//r and s are root indices in R
	//Finds p largest p such that -pr+s is still a root.

	local p, rr, ss;
	rr := Rts[r]; ss := Rts[s];

	t := -rr+ss; p := 1;
	while Position(Rts, t) ne 0 do
		p +:= 1; t -:= rr;
	end while;

	return p-1;
end function;

Nrsopts := function(ps,r,s)
	return { ps[r][s]+1, -(ps[r][s]+1) };
end function;

pairing_e_f := func<R,i,j | (i eq j) select 1 else 0 >;
pairing_e_alphast := func<R,i,j | Coroot(R,j)[i] >;
pairing_alpha_f := func<R,i,j | Root(R,i)[j] >;
pairing_alpha_alphast := func<R,i,j | CartanInteger(R,i,j) >;

intrinsic IsChevalleyBasis(L::AlgLie, R::RootDtm, epos::SeqEnum, eneg::SeqEnum, h::SeqEnum : EarlyOut := true) -> BoolElt, SeqEnum
{ Checks whether epos, eneg, h is a correct Chevalley basis for L wrt the root datum R. If so, second return value is the sequence of corresponding extraspecial signs}
	local e,i,j,a,b,bv,c, n, sgn, ess, espR,
		Np, rnk, ri, ris,
		verbok, theb, oldverbose;

	//check whether it is a basis
	if Type(L) eq AlgLie then
		if Rank(Matrix(epos cat eneg cat h)) ne Dimension(L) then
			vprintf ChevBas, 4: "!! Basis vectors do not linearly span Lie algebra\n";
			return false,_;
		end if;
	else
		vprintf ChevBas, 4: "!! Cannot check linear span with L not of type AlgLie\n";
	end if;
	
	//Pull epos,eneg, h into L -- strange stuff happens otherwise
	epos := [ L!Vector(v) : v in epos ];
	eneg := [ L!Vector(v) : v in eneg ];
	h := [ L!Vector(v) : v in h ];
	
	//some precomputations etc
	Np := NumPosRoots(R);
	rnk := #h;
	ri := func<i | ( i le Np ) select i else -(i-Np) >;
	ris := func<i | IntegerToString( ri(i) ) >;
	verbok := func<b | b select "OK" else "!!" >;
	theb := true;
	Rts := Roots(R);
	psA := Matrix([ [ findp(Rts, r, s) : s in [1..Np] ] : r in [1..Np] ]);
	psB := Matrix([ [ findp(Rts, r, s+Np) : s in [1..Np] ] : r in [1..Np] ]);
	ps := BlockMatrix([[ psA, psB], [psB, psA]]);

	//Check number of Cartan elements
	theb := #h eq Dimension(R);
	vprintf ChevBas, 4: "%o #h = Dimension(R) (%o = %o)\n",verbok(theb), #h, Dimension(R);
	if EarlyOut and not theb then return false, _; end if;
	
	e := epos cat eneg;
	//the actual checks
	vprintf ChevBas, 4 : "Property (1) : [h_i, h_j] = 0\n";
	IndentPush();
	for i in [1..rnk] do for j in [(i+1)..rnk] do
		b := IsZero(h[i]*h[j]);
		theb and:= b;
		vprintf ChevBas, 4: "%o [h_%o, h_%o] = %o\n", verbok(b), i, j, h[i]*h[j];
		if EarlyOut and not theb then IndentPop(); return false, _; end if;
	end for; end for;
	IndentPop();

	vprintf ChevBas, 4 : "Property (2) : [e_a, h_i] = < a, f_i > e_a\n";
	IndentPush();
	for a in [1..2*Np] do for i in [1..rnk] do
		b := e[a]*h[i] eq pairing_alpha_f(R,a,i)*e[a];
		theb and:= b;
		vprintf ChevBas, 4 : "%o [e_%o, h_%o] = %o; <a_%o, f_%o> = %o; e_%o = %o (--> %o)\n", verbok(b), ris(a), i, e[a]*h[i], ris(a), i, pairing_alpha_f(R,a,i), ris(a), e[a], findeigenv(h[i], e[a]);
		if EarlyOut and not theb then IndentPop(); return false, _; end if;
	end for; end for;
	IndentPop();

	vprintf ChevBas, 4 : "Property (3): [e_-a, e_a] = sum < e_i, a* > h_i \n";
	IndentPush();
	for a in [1..Np] do 
		b := e[a+Np]*e[a] eq &+[ pairing_e_alphast(R,i,a)*h[i] : i in [1..rnk] ];
		theb and:= b;
		vprintf ChevBas, 4 : "%o [e_-%o, e_%o] = %o, sum <e_i, a*>h_i = %o\n", verbok(b), a, a, e[a+Np]*e[a], &+[ pairing_e_alphast(R,i,a)*h[i] : i in [1..rnk] ];
		if EarlyOut and not theb then IndentPop(); return false, _; end if;
	end for;
	IndentPop();

	vprintf ChevBas, 4 : "Property (4): [e_a, e_b] = N_ab e_{a+b}, or 0\n";
	ess := []; espR := ExtraspecialPairs(R);
	IndentPush();
	for a in [1..2*Np] do for b in [(a+1)..2*Np] do
		if b - a eq Np then continue; end if;
		c := Position(Rts, Rts[a]+Rts[b]);

		if c eq 0 then
			bv := IsZero(e[a]*e[b]);
			theb and:= bv;
			vprintf ChevBas, 4 : "%o [e_%o, e_%o] -> a + b not a root\n", 
				verbok(bv), ris(a), ris(b);
			if EarlyOut and not theb then IndentPop(); return false, _; end if;
		else
			n := Nrsopts(ps, a, b);
			sgn := { i : i in n | i*e[c] eq e[a]*e[b] };
			bv := #sgn gt 0;
			theb and:= bv;
		
			vprintf ChevBas, 4 : "%o [e_%o, e_%o] ", verbok(bv), ris(a), ris(b);

			if bv then
				if #sgn eq 1 then
					sgn := (Setseq(sgn))[1] lt 0 select -1 else 1;
					vprintf ChevBas, 4 : "-> sign = %o", sgn;
				else
					sgn := 0;
					vprintf ChevBas, 4 : "-> sign = both (!!)";
				end if;
				if (<a,b> in espR) then
					Append(~ess, <a,b,sgn>);
				end if;
			else
				vprintf ChevBas, 4 : "-> [ mult : %o ]", ismultof(e[c], e[a]*e[b]);
			end if;
			if EarlyOut and not theb then IndentPop(); return false, _; end if;
			vprintf ChevBas, 4 : "\n  N_{ab} e_{a+b} = %o * %o\n", n, e[c];
		end if;
	end for; end for;
	IndentPop();
	
	if theb then return theb, ess; else return theb, _; end if;
end intrinsic;

intrinsic IsChevalleyBasis(CBD::Rec) -> BoolElt, SeqEnum
{Checks whether CBD contains a Chevalley basis}
	return IsChevalleyBasis(CBD`L, CBD`R, CBD`BasisPos, CBD`BasisNeg, CBD`BasisCart);
end intrinsic;

