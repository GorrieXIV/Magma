freeze;

/*
Interface to MiniSat.
AKS, 2009.
*/

function make_input(B, exclude: Cut := 0)

    if Cut eq 0 then
	Cut := 4;
	Cut := 5;
    end if;

    P := Universe(B);
    n := Rank(P);

    if Type(P) ne RngMPolBool then
	FP := [P.i^2 + P.i: i in [1 .. n]];
	B := [NormalForm(f, FP): f in B];
	delete FP;
    end if;

    one := n + 1;

    out := "";
    nc := 0;

    out cat:= Sprintf("c one monomial is %o\n", one);
    out cat:= Sprintf("%o 0\n", one);
    nc +:= 1;

    M := {@ @};
    mon_base := n + 2;

    M := {@ P.i: i in [1 .. n] @};
    Include(~M, P!1);
    mon_base := 0;
    // M;

    for S in exclude do
	assert #S eq n;
	out cat:= Sprintf("c exclude solution\n");
	for i := 1 to n do
	    j := mon_base + i;
	    if i gt 1 then
		out cat:= " ";
	    end if;
	    if S[i] eq 1 then
		out cat:= Sprintf("%o", -j);
	    else
		out cat:= Sprintf("%o", j);
	    end if;
	end for;
	out cat:= " 0\n";
    end for;

    neg_trick := 0 eq 1;

    L := [];
    for f in B do
	if f eq 0 then
	    continue;
	end if;
	m := Monomials(f)[1];
	v := Min([i: i in [1 .. n] | Degree(m, i) gt 0]);
	if f eq P.v^2 + P.v then
	    continue;
	end if;

	if neg_trick then

	    linears := {};
	    for m in Monomials(f) do
		s := Support(m);
		if #s eq 1 then
		    Include(~linears, s[1]);
		end if;
	    end for;
//"f:", f; "linears:", linears;
	end if;

	killed := {};

	A := [];
	for fm in Monomials(f) do

	    m := fm;
	    if m in killed then
		continue;
	    end if;

	    if IsOne(m) then
		Append(~A, one);
		continue;
	    end if;

	    neg := 0;
	    if neg_trick then

		/*
		a*b + b = (a + 1)*b = (~a)*b where ~a means complement of ~a.
		*/

		s := Support(m);
		if #s eq 2 then
		    v1, v2 := Explode(s);
		    if v1 in linears and P.v1 notin killed then
			// b = v1, a = v2
			m +:= P.v1;
			neg := v2;
			Include(~killed, P.v1);
		    elif v2 in linears and P.v2 notin killed then
			// b = v2, a = v1
			m +:= P.v2;
			neg := v1;
			Include(~killed, P.v2);
		    end if;
		end if;
	    end if;

	    MC := #M;
	    Include(~M, m);
	    ind := mon_base + Index(M, m);

	    Append(~A, ind);

	    if #M gt MC then

		out cat:= Sprintf("c mon %o = %o\n", m, ind);
		mi := [i: i in [1 .. n] | Degree(m, i) ge 1];

		if neg gt 0 then
		    i := Index(mi, neg);
		    assert i gt 0;
		    mi[i] := -neg;
		end if;

		// m | ~x | ~y
		out cat:= Sprintf("%o", ind);
		for i in mi do
		    out cat:= Sprintf(" %o", -i);
		end for;
		out cat:= " 0\n";
		nc +:= 1;

		// ~m | x  for each x

		for i in mi do
		    out cat:= Sprintf("%o %o 0\n", -ind, i);
		    nc +:= 1;
		end for;
	    end if;
	end for;
//"A:", A;
	Append(~L, A);
    end for;

    next := mon_base + #M + 1;
    for f in L do
	if #f eq 1 then
	    a := f[1];
	    out cat:= Sprintf("c (%o[%o] = 0)\n", a, M[a]);
	    out cat:= Sprintf("%o 0\n", -a);
	    nc +:= 1;
	elif #f eq 2 then
	    // (~a | b) & (a | ~b): whether a + b = 0
	    a, b := Explode(f);
	    out cat:= Sprintf("c (%o[%o] + %o[%o])\n", a, M[a], b, M[b]);
	    out cat:= Sprintf("%o %o 0\n", -a, b);
	    out cat:= Sprintf("%o %o 0\n", a, -b);
	    nc +:= 2;
	elif #f eq 3 then
	    // (~a | ~b | ~c) & (~a | b | c) & (a | ~b | c) & (a | b | ~c)
	    // whether a + b + c = 0
	    a, b, c := Explode(f);
	    if c eq one then
		// a + b + 1 = 0, so b = negation of a.
		// (a | b) & (~a | ~b): whether a + b = 1
		a, b := Explode(f);
		out cat:= Sprintf("c (%o[%o] + %o[%o] + 1)\n", a,M[a], b,M[b]);
		out cat:= Sprintf("%o %o 0\n", a, b);
		out cat:= Sprintf("%o %o 0\n", -a, -b);
		nc +:= 2;
	    else
		out cat:= Sprintf(
		    "c (%o[%o] + %o[%o] + %o[%o])\n", a, M[a], b, M[b], c, M[c]
		);
		out cat:= Sprintf("%o %o %o 0\n", -a, -b, -c);
		out cat:= Sprintf("%o %o %o 0\n", -a, b, c);
		out cat:= Sprintf("%o %o %o 0\n", a, -b, c);
		out cat:= Sprintf("%o %o %o 0\n", a, b, -c);
		nc +:= 4;
	    end if;
	else
	    T := [];
	    if #f eq 4 then
		Append(~T, [f[1], f[2], f[3], f[4]]);
	    elif #f eq 5 and Cut eq 5 then
		Append(~T, [f[1], f[2], f[3], f[4], f[5]]);
	    elif Cut eq 5 then // and f long enough?
		yb := next; next +:= 1;
		Append(~T, [f[1], f[2], f[3], f[4], yb]);
		i := 5;
		while i + 3 lt #f do
		    ye := next; next +:= 1;
		    Append(~T, [yb, f[i], f[i + 1], f[i + 2], ye]);
		    yb := ye;
		    i +:= 3;
		end while;
		Append(~T, [yb] cat [f[j]: j in [i .. #f]]);
	    else
		yb := next; next +:= 1;
		Append(~T, [f[1], f[2], f[3], yb]);
		i := 4;
		while i + 2 lt #f do
		    ye := next; next +:= 1;
		    Append(~T, [yb, f[i], f[i + 1], ye]);
		    yb := ye;
		    i +:= 2;
		end while;
		Append(~T, [yb] cat [f[j]: j in [i .. #f]]);
	    end if;

	    MM := func<i | i le #M select M[i] else Sprintf("T%o", i - #M)>;

	    for t in T do
		if #t eq 5 then
		    /*
		    Odd number of tildes.

		    1 tilde:

			(~a|b|c|d|e)
			(a|~b|c|d|e)
			(a|b|~c|d|e)
			(a|b|c|~d|e)
			(a|b|c|d|~e)

		    3 tildes:
			(~a|~b|~c|d|e)
			(~a|~b|c|~d|e)
			(~a|~b|c|d|~e)
			(~a|b|~c|~d|e)
			(~a|b|~c|d|~e)
			(~a|b|c|~d|~e)
			(a|~b|~c|~d|e)
			(a|~b|~c|d|~e)
			(a|~b|c|~d|~e)
			(a|b|~c|~d|~e)

		    5 tildes:

			(~a|~b|~c|~d|~e)
		    */

		    a, b, c, d, e := Explode(t);
		    out cat:= Sprintf(
			"c (%o[%o] + %o[%o] + %o[%o] + %o[%o] + %o[%o])\n",
			a, MM(a), b, MM(b), c, MM(c), d, MM(d), e, MM(e)
		    );
		    out cat:= Sprintf("%o %o %o %o %o 0\n", -a, b, c, d, e);
		    out cat:= Sprintf("%o %o %o %o %o 0\n", a, -b, c, d, e);
		    out cat:= Sprintf("%o %o %o %o %o 0\n", a, b, -c, d, e);
		    out cat:= Sprintf("%o %o %o %o %o 0\n", a, b, c, -d, e);
		    out cat:= Sprintf("%o %o %o %o %o 0\n", a, b, c, d, -e);

		    out cat:= Sprintf("%o %o %o %o %o 0\n", -a, -b, -c, d, e);
		    out cat:= Sprintf("%o %o %o %o %o 0\n", -a, -b, c, -d, e);
		    out cat:= Sprintf("%o %o %o %o %o 0\n", -a, -b, c, d, -e);
		    out cat:= Sprintf("%o %o %o %o %o 0\n", -a, b, -c, -d, e);
		    out cat:= Sprintf("%o %o %o %o %o 0\n", -a, b, -c, d, -e);
		    out cat:= Sprintf("%o %o %o %o %o 0\n", -a, b, c, -d, -e);
		    out cat:= Sprintf("%o %o %o %o %o 0\n", a, -b, -c, -d, e);
		    out cat:= Sprintf("%o %o %o %o %o 0\n", a, -b, -c, d, -e);
		    out cat:= Sprintf("%o %o %o %o %o 0\n", a, -b, c, -d, -e);
		    out cat:= Sprintf("%o %o %o %o %o 0\n", a, b, -c, -d, -e);

		    out cat:= Sprintf("%o %o %o %o %o 0\n", -a, -b, -c, -d, -e);

		    nc +:= 16;
		elif #t eq 4 then
		    // (~a|b|c|d) (a|~b|c|d) (a|b|~c|d) (a|b|c|~d)
		    // (~a|~b|~c|d) (~a|~b|c|~d) (~a|b|~c|~d) (a|~b|~c|~d)

		    a, b, c, d := Explode(t);
		    out cat:= Sprintf(
			"c (%o[%o] + %o[%o] + %o[%o] + %o[%o])\n",
			a, MM(a), b, MM(b), c, MM(c), d, MM(d)
		    );
		    out cat:= Sprintf("%o %o %o %o 0\n", -a, b, c, d);
		    out cat:= Sprintf("%o %o %o %o 0\n", a, -b, c, d);
		    out cat:= Sprintf("%o %o %o %o 0\n", a, b, -c, d);
		    out cat:= Sprintf("%o %o %o %o 0\n", a, b, c, -d);
		    out cat:= Sprintf("%o %o %o %o 0\n", -a, -b, -c, d);
		    out cat:= Sprintf("%o %o %o %o 0\n", -a, -b, c, -d);
		    out cat:= Sprintf("%o %o %o %o 0\n", -a, b, -c, -d);
		    out cat:= Sprintf("%o %o %o %o 0\n", a, -b, -c, -d);
		    nc +:= 8;
		else
		    assert #t eq 3;
		//(~a | ~b | ~c) & (~a | ~b | c) & (~a | b | ~c) & (a | ~b | ~c)
		    a, b, c := Explode(t);
		    out cat:= Sprintf(
			"c (%o[%o] + %o[%o] + %o[%o])\n",
			a, MM(a), b, MM(b), c, MM(c)
		    );
		    out cat:= Sprintf("%o %o %o 0\n", -a, -b, -c);
		    out cat:= Sprintf("%o %o %o 0\n", -a, b, c);
		    out cat:= Sprintf("%o %o %o 0\n", a, -b, c);
		    out cat:= Sprintf("%o %o %o 0\n", a, b, -c);
		    nc +:= 4;
		end if;
	    end for;
	end if;
    end for;

    //"L:", L;

    out := Sprintf("p cnf %o %o\n", next - 1, nc) cat out;

    return out;
end function;

function do_sat(B, Exclude, Verbose)

    root := Sprintf("%o/msat.%o.", GetTempDir(), Getpid());
    in_file := root cat "in";
    out_file := root cat "out";

    cols := GetColumns();
    SetColumns(0);
    S := make_input(B, Exclude);
    PrintFile(in_file, S: Overwrite);
    delete S;
    SetColumns(cols);

    cmd := Sprintf("minisat %o %o", in_file, out_file);
    if not Verbose then
	cmd cat:= " >/dev/null 2>&1";
    end if;
    System(cmd);
    cmd := Sprintf("#rm -f %o", in_file);
    System(cmd);

    S := Read(out_file);
    cmd := Sprintf("rm -f %o", out_file);
    System(cmd);

    if Regexp("UNSAT", S) then
	return false, _;
    end if;

    n := Rank(Universe(B));
    t, U, M := Regexp("SAT(.*)", S);
    if not (t and #M eq 1) then
	error "Interrupted or failed";
    end if;

    S := M[1];
    Q := [eval x: x in Split(S, " ")];
    assert forall{i: i in [1 .. #Q - 1] | Abs(Q[i]) eq i};

    return true, [GF(2) | Q[i] lt 0 select 0 else 1: i in [1 .. n]];

end function;

intrinsic SAT(B::[RngMPolElt]: Exclude := [], Verbose := false)
    -> BoolElt, SeqEnum
{Apply the SAT solver to the binary poly system B: return true and a
solution if the system is solvable, false otherwise}

    require BaseRing(Universe(B)) cmpeq GF(2): "Base ring must be GF(2)";

    return do_sat(B, Exclude, Verbose);

end intrinsic;

intrinsic SAT(B::[RngMPolBoolElt]: Exclude := [], Verbose := false)
    -> BoolElt, SeqEnum
{Apply the SAT solver to the binary poly system B: return true and a solution
if the system is solvable, false otherwise}

    return do_sat(B, Exclude, Verbose);

end intrinsic;
