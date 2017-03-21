freeze;
 
////////////////////////////////////////////////////////////////////////////////
// Making the baskets of Fano 3-folds of Fano index f with 'bound' n
//
// Idea: first make a big collection of baskets satisfying the weaker
// conditions: N <= 15 and sum(r-1) < 24, where N = #singular points.
// NB n == 24 here.
// Then test the real conditions
//	N <= 15 and (3/2)N <= sum(r - (1/r)) < 24
// on each of these.
// When f = 2 the parameter g also plays a role: it appears in formulas
// for A^3 and for the Hilbert coefficients.
//
// The easy one-off way to construct baskets is simply
//	> B := FanoBaskets(20,8);
// as before (or with argument 'g' when f eq 2).
// But now you can also make the raw isolated list first, and then
// try imposing the conditions on it in different orders.
//	> SetVerbose("User1",true);
//	> B0 := FanoIsolatedBaskets(20,8);
//	> B1 := FanoBaskets(B0,8);
//	> B2 := FanoBaskets(B0,8: Order:="kas");
// The last version does the Kawamata bound 'k' first, then checks 'a' that
// A^3 > 0, and finally checks 's' that some of the negative coefficients
// (by which it means t^-1 and t^-2) are zero.
//
////////////////////////////////////////////////////////////////////////////////

import "../Fano/fanohilb.m": fano_Ac, fano_degree, fano_degree_g, contribution;

/////////////////////////////////////////////////////////////////////
// This is the main intrinsic.
// Conditions are imposed separately by procedures written below.
/////////////////////////////////////////////////////////////////////

intrinsic FanoBaskets(n::RngIntElt,f::RngIntElt: Order:="default") -> SeqEnum
{}
    B := FanoIsolatedBaskets(n,f);
    return FanoBaskets(B,f: Order:=Order);
end intrinsic;

forward cond_A3pos,cond_allnegcoeffs,cond_somenegcoeffs,cond_kawamata,
base_genus, max_genus,func_cond_allnegcoeffs;

intrinsic FanoBaskets(B::SeqEnum,f::RngIntElt:Order:="default") -> SeqEnum
{All baskets of singularities appearing on Fano 3-folds with Fano index f
and genus g (either from among those of B or with Kawamata index sum at
most n)}
    tt := Cputime();
if f in {1,2} then
    // Step 1:  for each b in B find the values of g = g_min..g_kawamata
    // for which A^3 > 0 and Kawamata condition is satisfied.
    g_mins := [ base_genus(f,b) : b in B ];
    g_kawas := [ max_genus(f,B[i],g_mins[i]) : i in [1..#B] ];

    // Step 2: for each b,g pair, check the negative coefficients.
    newB := [];
    G := [ Parent([1,2,3]) | ];
    for i in [1..#B] do
        b := B[i];
        gg := [ Integers() | ];
        g_min := g_mins[i];
        g_max := g_kawas[i];
        for g in [g_min..g_max] do
            if func_cond_allnegcoeffs(b,f,g) then
                Append(~gg, g);
            end if;
        end for;
        if #gg gt 0 then
            Append(~newB,b);
            Append(~G,gg);
        end if;
    end for;

    if #B ne 1 then
        vprintf User1: "Finished with %o baskets\n",#B;
    else
        vprintf User1: "Finished with 1 basket\n",#B;
    end if;
    return newB,G;
else
    if Order eq "default" then
	// The parameter 'Order' determines the order in which the conditions
	// are applied.
	Order := "akn";
    end if;
    // THINK: haven't tested that the index of things in B is f.

    // Do the tests.
// THINK: remove g from this section
g := 0;
    for i in [1..#Order] do
	if Order[i] eq "a" then
	    cond_A3pos(~B,f);
	elif Order[i] eq "k" then
	    cond_kawamata(~B,f);
	elif Order[i] eq "n" then
	    cond_allnegcoeffs(~B,f,g);
	elif Order[i] eq "s" then
	    cond_somenegcoeffs(~B,f,g);
	end if;
	vprintf User1: "\tTime: %o\n",Cputime(tt);
    end for;

    if #B ne 1 then
	vprintf User1: "Finished with %o baskets\n",#B;
    else
	vprintf User1: "Finished with 1 basket\n",#B;
    end if;
    return B;
end if;
end intrinsic;

// The minimum value of the Fano genus g for which the triple (f,B,g)
// determine a positive Fano degree.
function base_genus(f,B)
    if not f in {1,2} then
        return 0;       // this value is irrelevant
    end if;
    // I could be smarter about this since the degree is linear in g.
    g := 0;
    if fano_degree_g(g,f,B) le 0 then
        repeat
            g +:= 1;
        until fano_degree_g(g,f,B) gt 0;
    else
        repeat
            g -:= 1;
        until fano_degree_g(g,f,B) le 0;
        g +:= 1;
    end if;
    return g;
end function;

function max_genus(f,B,g_min)
    if not f in {1,2} then
        return 0;       // irrelevant
    end if;
    g := g_min;
    Ac := 3/8*fano_Ac(f,B);
    while Ac ge fano_degree_g(g,f,B) do
        g +:= 1;
    end while;
    return g;
end function;


//////////////////////////////////////////////////////////////////////////////

procedure cond_A3pos(~BB,f)
    vprintf User1: "Imposing A^3 > 0 ...\n";
    nBB := #BB;
    BB := [ B : B in BB | fano_degree(f,B) gt 0 ];
    vprintf User1: "\treduced from %o to %o baskets\t",nBB,#BB;
end procedure;

procedure cond_kawamata(~BB,f)
    vprintf User1: "Imposing Kawamata bound ...\n";
    nBB := #BB;
    if f in {1,2} then
// THINK
g := 0;
	BB := [ B : B in BB | 3/8*fano_Ac(f,B) ge fano_degree_g(g,f,B)];
// THINK 28 Aug 2003 changed 'gt' in line above to 'ge'.
    else
	BB := [ B : B in BB | 48*fano_Ac(f,B) ge  (4*f - 3)*fano_degree(f,B)];
    end if;
    vprintf User1: "\treduced from %o to %o baskets\t",nBB,#BB;
end procedure;

forward coefficient, coefficient_g;
procedure cond_somenegcoeffs(~BB,f,g)
    Qorder := [-2,-1];	// the coefficients checked by this test.
    vprintf User1: "Imposing coefficients of all t^%o  are 0 ...\n",Qorder;
    nBB := #BB;
    BB := [ B : B in BB |
	&and[ coefficient_g(g,f,B,i) eq 0 : i in Qorder ] ];
    vprintf User1: "\treduced from %o to %o baskets\t",nBB,#BB;
end procedure;

procedure cond_allnegcoeffs(~BB,f,g)
    vprintf User1: "Ensuring all negative coefficients are 0 ...\n";
    for n in [-Round(f-1)..-3] do
	nBB := #BB;
	BB := [ B : B in BB | &and[ coefficient_g(g,f,B,n) eq 0 ] ];
	vprintf User1: "\tt^%o: reduced from %o to %o baskets\n",n,nBB,#BB;
    end for;
end procedure;

function func_cond_allnegcoeffs(b,f,g)
    return &and [ coefficient_g(g,f,b,n) eq 0 : n in [-Round(f-1)..-3] ];
end function;


// The n-th coefficient of the Hilbert series of Fano with Fano index f and
// basket B.
//    require f ge 3: "Include arguments (g,f,B) when f <= 2";
/*
function coefficient(f,B,n)
    return 1 + (1/12) * fano_degree(f,B) * n*(n+f)*(2*n+f)
        + n * fano_Ac(f,B)
        + &+[Rationals()| contributions(f,p)[n mod Index(p)] :
                                p in Points(B) ];
end function;
*/

function coefficient_g(g,f,B,n)
    return 1 + (1/12) * fano_degree_g(g,f,B) * n*(n+f)*(2*n+f)
                                // this g the only difference
        + n * fano_Ac(f,B)
        + &+[Rationals()| contribution(f,p,(n mod Index(p))) :
                                p in Points(B) ];
end function;



///////////////////////////////////////////////////////////////////////
//  Making the raw list of isolated singularities with given index f
///////////////////////////////////////////////////////////////////////

forward indices, small_coprimes, round_up;
intrinsic FanoIsolatedBaskets(n::RngIntElt,f::RngIntElt) -> SeqEnum
{Large list of possible baskets of isolated singularities appearing
on Fano 3-folds with Fano index f and Kawamata index sum at most n}

    // Idea: first make a big collection of baskets satisfying the weaker
    // conditions: N <= 15 and sum(r-1) < 24, where N = #singular points.
    // NB n == 24 here.

    tt := Cputime();

    vprintf User1: "Building collections of singularities...\n";
    // Precompute all sequences of singularity types [r,a] that might be needed.
    // The result is called 'sing_combs'.
    max_num_sings_per_r := [ round_up(n/(r-1)) - 1 : r in [2..n] ];
    A := [ small_coprimes(i) : i in [2..n] ];
    // Entry 'poss_as_per_r[r-1][j]' is a sequence containing sequences of
    // 'a's (in notation [r,a]) that could appear in a collection of j sings
    // of index r.
    poss_as_per_r := [];
    for r in [2..n]  do
	poss_a := [];
	for j in [1..max_num_sings_per_r[r-1]] do
	    poss_a[j] := Sort(SetToSequence({ Sort(S) :
				S in Subsequences(A[r-1],j) }));
	end for;
	poss_as_per_r[r-1] := poss_a;
    end for;
    // Add the index 'r' to each of the elements of 'poss_as_per_r' to make
    // baskets.
    sing_combs := [];
    for r in [2..n] do
	poss_comb := [];
	for j in [1..max_num_sings_per_r[r-1]] do
	    papj := poss_as_per_r[r-1][j];
	    baskets := [];
	    for k in [1..#papj] do
		Append(~baskets,[ [r,i] : i in papj[k]]);
	    end for;
	    Append(~poss_comb,baskets);
	end for;
	sing_combs[r-1] := poss_comb;
    end for;

    // Compute prima facie allowable collections of indices according to the
    // coarse formula \sum (ri - 1) < n. Redescribe collections like
    // [ 2,2,2,2,2,3,4,4 ] as [ [2,5],[3,1],[4,2] ].
    // Result is called 'Ifactors'.
    I0 := indices(n);
    I := [ R : R in I0 |
			#R le 15 and
			(3/2)*#R le fanosum and fanosum lt 31
		where fanosum is &+[Rationals()| r - 1/r : r in R ] ];
    Ifactors := [];
    for i in I do
	new_term := [];
	for r in [2..n] do
	    k := #[ z : z in i | z eq r ];
	    if k gt 0 then
		Append(~new_term,[r,k]);
	    end if;
	end for;
	Append(~Ifactors,new_term);
    end for;

    // Translate the result into sequences of baskets.
    result := [];
    for X in Ifactors do
	Xbaskets := [ [] ];
	for inds in X do
	    poss_sings := sing_combs[inds[1]-1,inds[2]];
	    Xbaskets_temp := [];
	    for S in poss_sings do
		for B in Xbaskets do
		    Append(~Xbaskets_temp,B cat S);
		end for;
	    end for;
	    Xbaskets := Xbaskets_temp;
	end for;
	result cat:= Xbaskets;
    end for;
    vprintf User1: "Made %o raw baskets\t",#result;
    vprintf User1: "\tTime: %o\n",Cputime(tt);

    // don't include nonisolated sings: f must be coprime to index p[1]
    vprintf User1: "Assembling only those with isolated singularities...\n";
    result1 := [ B : B in result | &and[ GCD(p[1],f) eq 1 : p in B ] ];

    // Turn this raw result into singularities before making subtle tests.
    BB := [ Basket([Point(p[1],[p[2],p[1]-p[2],f]): p in B ]): B in result1 ];
    vprintf User1: "Now have %o baskets\t",#BB;

    return BB;
end intrinsic;

///////////////////////////////////////////////////////////////////////

forward add_term, sub_sum;
function indices(n)
    // return sequences of indices [ r1,r2,... ] so that \sum (ri - 1) < n.
    I := [ [ Integers() | ] ];
    Itemp := I;
    repeat
	S := &cat [add_term(B,n) : B in Itemp ];
	I cat:= S;
	Itemp := [ B : B in S | sub_sum(B) lt n ];
    until #Itemp eq 0;
    return I;
end function;

function add_term(B,n)
    new := [];
    if #B eq 0 then
	m0 := 2;
	m1 := n;
    else
	m0 := B[#B];
	m1 := n - sub_sum(B);
    end if;
    for i in [m0..m1] do
	C := B;
	Append(~C,i);
	Append(~new,C);
    end for;
    return new;
end function;

function sub_sum(B)
    return &+ [ b - 1 : b in B ];
end function;

function small_coprimes(r)
    n := IsEven(r) select Integers() ! (r/2) else Integers() ! ((r-1)/2);
    return { a : a in [1..n] | GCD(r,a) eq 1 };
end function;

function round_up(q)
    n := Round(q);
    if n - q ge 0 then
	return n;
    else
	return n + 1;
    end if;
end function;














////////////////////////////////////////////////////////////////////////////////
//		Old stuff
////////////////////////////////////////////////////////////////////////////////

/*
    vprintf User1: "Building collections of singularities...\n";
    // Precompute all sequences of singularity types [r,a] that might be needed.
    // The result is called 'sing_combs'.
    max_num_sings_per_r := [ round_up(n/(r-1)) - 1 : r in [2..n] ];
    A := [ small_coprimes(i) : i in [2..n] ];
    // Entry 'poss_as_per_r[r-1][j]' is a sequence containing sequences of
    // 'a's (in notation [r,a]) that could appear in a collection of j sings
    // of index r.
    poss_as_per_r := [];
    for r in [2..n]  do
	poss_a := [];
	for j in [1..max_num_sings_per_r[r-1]] do
	    poss_a[j] := Sort(SetToSequence({ Sort(S) :
				S in Subsequences(A[r-1],j) }));
	end for;
	poss_as_per_r[r-1] := poss_a;
    end for;
    // Add the index 'r' to each of the elements of 'poss_as_per_r' to make
    // baskets.
    sing_combs := [];
    for r in [2..n] do
	poss_comb := [];
	for j in [1..max_num_sings_per_r[r-1]] do
	    papj := poss_as_per_r[r-1][j];
	    baskets := [];
	    for k in [1..#papj] do
		Append(~baskets,[ [r,i] : i in papj[k]]);
	    end for;
	    Append(~poss_comb,baskets);
	end for;
	sing_combs[r-1] := poss_comb;
    end for;
    // Compute prima facie allowable collections of indices according to the
    // coarse formula \sum (ri - 1) < n. Redescribe collections like
    // [ 2,2,2,2,2,3,4,4 ] as [ [2,5],[3,1],[4,2] ].
    // Result is called 'Ifactors'.
    I0 := indices(n);
    I := [ R : R in I0 |
			#R le 15 and
			(3/2)*#R le fanosum and fanosum lt 31
		where fanosum is &+[Rationals()| r - 1/r : r in R ] ];
    Ifactors := [];
    for i in I do
	new_term := [];
	for r in [2..n] do
	    k := #[ z : z in i | z eq r ];
	    if k gt 0 then
		Append(~new_term,[r,k]);
	    end if;
	end for;
	Append(~Ifactors,new_term);
    end for;
    // Translate the result into sequences of baskets.
    result := [];
    for X in Ifactors do
	Xbaskets := [ [] ];
	for inds in X do
	    poss_sings := sing_combs[inds[1]-1,inds[2]];
	    Xbaskets_temp := [];
	    for S in poss_sings do
		for B in Xbaskets do
		    Append(~Xbaskets_temp,B cat S);
		end for;
	    end for;
	    Xbaskets := Xbaskets_temp;
	end for;
	result cat:= Xbaskets;
    end for;
    vprintf User1: "Made %o raw baskets\t",#result;
    vprintf User1: "\tTime: %o\n",Cputime(tt);
    // don't include nonisolated sings: f must be coprime to index p[1]
    vprintf User1: "Assembling only those with isolated singularities...\n";
    result1 := [ B : B in result | &and[ GCD(p[1],f) eq 1 : p in B ] ];
    // Turn this raw result into singularities before making subtle tests.
    BB := [ [Point(p[1],[p[2],p[1]-p[2],f]): p in B ]: B in result1 ];
    vprintf User1: "Now have %o baskets\t",#BB;
*/

/*
    if f eq 2 then
	B3 := [ B : B in B2 | 3/8*fano_Ac(f,B) gt fano_degree_g(g,f,B)];
	// Oguiso's correction:  here too?
	// B3 := [ B : B in B2 | 4*fano_Ac(f,B) ge  (4*f - 3)*fano_degree_g(g,f,B)];
        Bfinal := [ B : B in B3 | &and[FanoCoefficient(g,f,B,-1) eq 0]];
    else
	// it seems to be quicker to check a couple of coeffs first
	// before doing the Ac > A3 calculation.
	vprintf User1: "Imposing coefficients of t^-1, t^-2 are 0...\n";
	B3 := [ B : B in B2 |
		&and[ FanoCoefficient(g,f,B,n) eq 0 : n in [-2..-1]] ];
	vprintf User1: "Imposing Kawamata bound...\n";
	// B4 := [ B : B in B3 | 3*fano_Ac(f,B) gt  fano_degree(f,B)/f^3];
	// correction:
	B4 := [ B : B in B3 | 48*fano_Ac(f,B) ge  (4*f - 3)*fano_degree(f,B)];
	vprintf User1: "Ensuring remaing negative coefficients are 0...\n";
        Bfinal := [ B : B in B4 | &and[ FanoCoefficient(g,f,B,n) eq 0 :
                                       n in [-Round(f-1)..-3]]];
	vprintf User1: "Now have %o baskets and am finished\t",#Bfinal;
	vprintf User1: "\tTime: %o\n",Cputime(tt);
    end if;
*/
