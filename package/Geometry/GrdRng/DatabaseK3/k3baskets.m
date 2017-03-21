freeze;
 
/////////////////////////////////////////////////////////////////////
//		Computing all baskets for K3 surfaces
/////////////////////////////////////////////////////////////////////

import "../K3/k3.m": k3_degree, k3_hilbert_series;

forward indices,small_coprimes,round_up;
intrinsic K3Baskets(n::RngIntElt: Proof:=true)
		 -> SeqEnum,SeqEnum,SeqEnum,SeqEnum
{The first return sequence contains baskets of singularities for virtual K3
surfaces polarised by a divisor with a g-dimensional linear system (or bigger)
and at most n curves in the resolution of its singularities where g is the
corresponding entry of the second sequence. The third sequence is the
corresponding degree, while (if Proof is true) the fourth contains elements
which had positive degree but negative coefficients for the indicated value
of g}
    // If 'Proof' is true then the relatively expensive check that each
    // basket produces only power series with positive coefficients is done.
    // If n is 20 then there are three cases from 7000ish that fail this test
    // and that need their corresponding g to be increased by 1.
    // Timing: Baskets(20) takes 66s

    // Precompute all sequences of singularity types [r,a] that might be needed.
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

    // Compute a priori allowable collections of indices according to the
    // coarse formula \sum (ri - 1) < n. Redescribe collections like
    // [ 2,2,2,2,2,3,4,4 ] as [ [2,5],[3,1],[4,2] ].
    I := indices(n);
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

    // Compute the expected number as a test.
    SC := [ small_coprimes(i) : i in [1..n] ];
//    print "Expected number:",1 + &+[ &*[ Binomial(#SC[b[1]]+b[2]-1,b[2])
//	    where b is <x,#[y: y in ind | y eq x ]> : x in SequenceToSet(ind) ]
//			: ind in I[2..#I] ];

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
//    print "Actual number:",#result;

// !! change from the old version
// remove a bunch of baskets that could not possibly live on a K3:
//	those having at least 17 singularities in them
//	those having 16 sings including a 1/4 or 1/5
//	those having 15 sings incl 1/6
// each of these includes at least 17 disjoint -2 curves, which is illegal,
// but would otherwise have singular rank <= 19.
// THINK: is this still true if the sings are not exactly the basket?

old_result := result;
result := [ B : B in old_result | 
	#B le 14 or
	(#B eq 15 and 6 notin {p[1]:p in B}) or
	(#B eq 16 and 4 notin {p[1]:p in B} and 5 notin {p[1]:p in B})
			];

    // Compute the minimum genus in each case which produces positive degree.
    // If 'Proof' is true, then also check the first few coefficients of the
    // power series expansion to make sure that they are positive.
    check_coeffs := Type(Proof) eq BoolElt and Proof cmpeq true;
    if check_coeffs then
	S := PowerSeriesRing(Rationals());
//	print "Checking degrees ...";
    end if;
    genuses := [ Integers() | ];
    degrees := [ Rationals() | ];
    errors := [];
    for b in result do
	g := -2;
	repeat
	    g +:= 1;
	    d := k3_degree(g,b);
	until d gt 0;
	if check_coeffs then
	    done := false;
	    repeat
		h := k3_hilbert_series(g,b);
		if &or[ a lt 0 : a in Coefficients(S!h) ] then
		    Append(~errors,<b,g>);
		    g +:= 1;
		else
		    done := true;
		end if;
	    until done;
	    d := k3_degree(g,b);
	end if;
	Append(~genuses,g);
	Append(~degrees,d);
    end for;
    return result,genuses,degrees,errors;
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

///////////////////////////////////////////////////////////////////////

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

