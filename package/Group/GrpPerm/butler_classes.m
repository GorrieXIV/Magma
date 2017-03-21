freeze;

/*
Routines to compute conjugacy classes of elements in permutation groups
by using homomorphisms, quotients of centralizers of elements of order p,
and whatever else is necessary.

This version works with rational classes of elements.

It attempts to be more polished in treating fusion of the classes of the
Sylow p-subgroup in G, and is certainly more proficient at handling the
classes of composite order - due to more theory.

This library is used in conjunction with:
    cladt	- which implements the data structure for class table entries
    clutilities	- utility routines
    clcomposite	- which computes the classes of composite order
    clprime	- which computes the classes of prime power order
The data structure stores one entry per rational class.
*/

forward AbGpAnalyse, AnalysePrimes, BigHomClass, CheckOrder, ClCnts;
forward ClConcatenate, ClCycs, ClFusPows, ClFusgen, ClLength, ClLths, ClOrds;
forward ClPMaps, ClPows, ClPrime, ClPrint, ClPrmRoot, ClReps, ClRoots, ClSets;
forward ClTotLth, Close, Convert, CycLift, CycPos, ExpSort, Expnt;
forward Filter, FusSetup, GetExp, GetpClasses, GetpSylow, HomClass, Imset;
forward IsClassSmall, IsNewRational, IsRatConjugate, IspGroup;
forward LiftFPows, LiftRatCl, NewCl, OSetRep, PossFusion, PowFuse, PrimRoot;
forward RootClose, Sets, SmallHomClass, SylAnalyse, AddpClass, check, cladd;
forward cntsor, pPSqFilter, pPowSequence, pSetup, pcpClasses, qPSqFilter;
forward qPowSequence, qSetup, rHomClass;
forward SylAnalyseU;


HomClass := function(gp, N, clN, prnt, dbug)
/*
Given a group gp it returns a data structure cl containing information
on the rational conjugacy classes.
prnt is a flag to switch on printing.
dbug is a flag to switch on debug printing.
This is driver routine, mainly to record statistics
*/
    zeit := Cputime();
    lookat := AnalysePrimes(gp);
    if prnt cmpeq true then prnt := 1; end if;
    cl := rHomClass(gp, N, clN, lookat, prnt, dbug);
    zeit := Cputime(zeit);
    if prnt gt 0 then
	print "HomClass took ", zeit, " seconds";
    end if;
    return cl;
end function;

rHomClass := function(gp, N, clN, psq, prnt, dbug)
/*
Recursive routine using homomorphisms to compute conjugacy classes.
Given a group gp it returns a class table cl for the rational conjugacy classes.
It returns complete information on those classes of elements whose order
involves only the primes in psq.
prnt is a flag to switch on printing.
dbug is a flag to switch on debug printing.
*/
// "Entering rHomClass", gp, Labelling(gp);
    zeit := Cputime();
    if #N eq 1 and IsClassSmall(gp) then
	cl := SmallHomClass(gp, N, clN, psq);
    else
	cl := BigHomClass(gp, N, clN, psq, prnt, dbug);
    end if;
    zeit := Cputime(zeit);
    if prnt gt 0 then
	print "rHomClass took ", zeit, " seconds";
    end if;
    return cl;
end function;

IsClassSmall := function(gp)
/*
Return whether the group is small enough to compute classes directly.
*/
    /*
    // fudge for testing purposes
    small := false;
    */
    small :=
	#gp le 5000 or
	#gp le 20000 and Degree(gp) le 50 or
	#gp le 2000000 and Degree(gp) le 12;
    return small;
end function;

SmallHomClass := function(gp, N, clN, psq)
/*
Use other techniques to compute the classes of a small group.
Set up class table entries in cl for those rational classes
whose elements have orders only involving the primes in psq.
*/
    if #gp le 5000 then al := "Action"; else al := "Random"; end if;
    return ClConcatenate(clN, Convert(gp, N, Classes(gp:Al := al), psq));
end function;

ExtractpCls := function(cl, p)
    ords := ClOrds(cl);
    keep := [i: i in [1..#ords]|o mod p eq 0 and IsPrimePower(o)
		    where o := ords[i]];

    return [*    [cl[1,i]: i in keep],
		[cl[2,i]: i in keep],
		[cl[3,i]: i in keep],
		[cl[4,i]: i in keep],
		[cl[5,i]: i in keep],
		[cl[6,i]: i in keep],
		[cl[7,i]: i in keep],
		[], [], [] *];
		/*
		[cl[9,i]: i in keep],
		[cl[10,i]: i in keep] *];
		*/

end function;

ExtractNonNCls := function(cl, N)
    reps := ClReps(cl);
    keep := [i: i in [1..#reps]|reps[i] notin N];

    return [*    [cl[1,i]: i in keep],
		[cl[2,i]: i in keep],
		[cl[3,i]: i in keep],
		[cl[4,i]: i in keep],
		[cl[5,i]: i in keep],
		[cl[6,i]: i in keep],
		[cl[7,i]: i in keep],
		[],[],[] *];
		/*
		[cl[9,i]: i in keep],
		[cl[10,i]: i in keep] *];
		*/

end function;

BigHomClass := function(gp, N, clN, psq, prnt, dbug)
/*
Given a group gp return a class table cl.
Only consider elements whose order involves only primes in psq. The sequence psq
gives the suggested order in which to treat the primes---hardest primes last.)
This routine recursively handles cases which are too big to compute directly.
*/
    cl := clN;
    for i := 1 to #psq do
	p := psq[i];
	if prnt gt 0 then
	    printf "BigHomClass handling the prime %o (degree %o)\n", p, Degree(gp);
	end if;
	totlth := ClTotLth(cl);
	limit := #gp - totlth;
	if Index(gp, N) mod p eq 0 then
	    pcl := ClPrime(gp, N, p, limit, prnt, dbug);
	    if prnt gt 1 then
		print "In BigHomClass, the p-classes for this prime are ";
		ClPrint(gp, pcl, prnt gt 2);
	    end if;
	    cl := ClConcatenate(cl, pcl);
	else
	    pcl := NewCl(gp);
	end if;
	pcl := ClConcatenate(pcl, ExtractpCls(clN, p));
	if i lt #psq then
	    // other primes for composite orders

	    rest := psq[i + 1 .. #psq];
	    qcl := NewCl(gp);
	    plth := ClLength(pcl);
	    for j := 1 to plth do
		rcl := ClRoots(gp, N, rest, pcl, j, prnt, dbug);
		qcl := ClConcatenate(qcl, rcl);
	    end for;
	    if prnt  gt 1 then
	      print "In BigHomClass, the composite classes for this prime are ";
	      ClPrint(gp, qcl, prnt gt 2);
	    end if;
	    cl := ClConcatenate(cl, qcl);
	end if;
    end for;
    return cl;
end function;

/*
Create an empty class table for the group gp.
*/
NewCl := func<gp | [*[gp|], [], [], [], [], [], [], [], [], []*]>;

/*
Return a sequence of generators of the fusion subgroup
*/
ClFusgen := procedure(gp, ~cl, i, ~gen)
    if IsDefined(cl[9],i) then gen := cl[9][i]; return; end if;
    FusSetup(gp, i, cl[1], cl[2], cl[4], cl[5], ~fgens, ~fpws);
    cl[9, i] := fgens;
    cl[10, i] := fpws;
    gen := fgens;
end procedure;

/*
Return the appropriate primitive root of fusion subgroup
(only for cyclic fusion subgroups).
*/
ClPrmRoot := procedure(gp, ~cl, i, ~root)
    if IsDefined(cl[10], i) then root := cl[10][i][1,1]; return; end if;
    FusSetup(gp, i, cl[1], cl[2], cl[4], cl[5], ~fgens, ~fpws);
    cl[9, i] := fgens;
    cl[10, i] := fpws;
    root := fpws[1,1];
end procedure;

/*
Return the sequence of powers corresponding to the generators of
the fusion subgroup.
*/
ClFusPows := procedure(gp, ~cl, i, ~pows)
    if IsDefined(cl[10], i) then pows := cl[10][i][2]; return; end if;
    FusSetup(gp, i, cl[1], cl[2], cl[4], cl[5], ~fgens, ~fpws);
    cl[9,i] := fgens;
    cl[10, i] := fpws;
    pows := fpws[2];
end procedure;

ClReps := func<cl | cl[1]>;
ClOrds := func<cl | cl[2]>;
ClCycs := func<cl | cl[3]>;
ClPows := func<cl | cl[4]>;
ClSets := func<cl | cl[5]>;
ClLths := func<cl | cl[6]>;
ClCnts := func<cl | cl[7]>;
ClPMaps := func<cl | cl[8]>; // Return the power maps.

ClLength := func<cl |
/*
Return the length of the class table, that is, the number of rational
classes (excluding identity) which it contains.
*/
    #cl[1]
>;

ClTotLth := function(cl)
/*
Return the total number of elements accounted for in the rational classes of cl.
Count the identity element as well.
*/
    lths := ClLths(cl);
    pows := ClPows(cl);
    return 1 + &+[Integers() | lths[i] * #pows[i] : i in [1 .. ClLength(cl)]];
end function;

ClConcatenate := func<cl1, cl2 |
/*
Return the concatenation of two class tables
*/
    [*
	cl1[1] cat cl2[1],
	cl1[2] cat cl2[2],
	cl1[3] cat cl2[3],
	cl1[4] cat cl2[4],
	cl1[5] cat cl2[5],
	cl1[6] cat cl2[6],
	cl1[7] cat cl2[7],
	cl1[8] cat cl2[8],
	cl1[9] cat cl2[9],
	cl1[10] cat cl2[10]
    *]
>;

ClPrint := procedure(gp, cl, prntbase)
/*
Print the class table cl.
Just record the base image and the order of the element.
*/
    b := Base(gp);
    reps := cl[1];
    ords := cl[2];
    cycs := cl[3];
    ClPows := cl[4];
    ClSets := cl[5];
    lths := cl[6];
    cnts := cl[7];

    print "\n\n Class table for a group";
    print "   of order: ", FactoredOrder( gp );
    if prntbase then
	print "   and with base: ", b;
    end if;

    totelt := 1;	// for identity

    cllth := #reps;
    for i := 1 to cllth do
	print "\n";
	if i mod 10 eq 1 and i ne 11 then
	    print i, "-ST rational class:";
	elif i mod 10 eq 2 and i ne 12 then
	    print i, "-ND rational class:";
	elif i mod 10 eq 3 and i ne 13 then
	    print i, "-RD rational class:";
	else
	    print i, "-TH rational class:";
	end if;
	pws := ClPows[i];
	l := #pws;
	if l eq 1 then
	    print "   containing precisely 1 class";
	else
	    print "   containing ", #pws, " classes via powers: ", pws;
	end if;
	print "   elements have order: ", ords[i];
	print "   classes have length: ", lths[i];
	if prntbase then
	    print "   representative has base image: ", b^reps[i];
	end if;
	print "   cycle structure is: ", cycs[i];
	if l ne 1 then
	    print "   fusion within rational class is: ", ClSets[i];
	end if;
	print "   order of centralizer is: ", FactoredOrder(cnts[i]);
	totelt := totelt + l * lths[i];
    end for;

    print "\nNumber of elements in the classes (including identity) = ", totelt;
end procedure;

check := function(gp, cl)
/*
Check whether the supplied sequence of class reps (excluding identity)
    have class lengths summing to group order.
*/
    num := ClTotLth(cl);
    flag := num eq #gp;
    if not flag then
	print "check is short by ", #gp - num;
    end if;
    return flag;
end function;

cladd := function(clin, x, ord, cyc, pws, Sets, lth, cnt, pthpow, fusgp, w, fuspws )
/*
Add a new entry as the last one of the class table clin.
For some class tables also want to store the P-th power map entry PTHPOW
*/
    // assert forall{x: x in clin[5] | #x ge 1};
    // assert #Sets ge 1;
    res := [*
	clin[1] cat [x],
	clin[2] cat [ord],
	clin[3] cat [cyc],
	clin[4] cat [pws],
	clin[5] cat [Sets],
	clin[6] cat [lth],
	clin[7] cat [cnt],
	clin[8] cat [pthpow],
	clin[9] cat [fusgp],
	clin[10] cat [[[w], fuspws]]
    *];
    // chk := { #x : x in res};
    // assert #chk eq 1;
    return res;
end function;

Convert := function(gp, N, oldcl, psq)
/*
Convert from existing Cayley class table to a table of rational classes
of elements whose orders only involve the primes in psq.
The identity class is not stored.
For permutation groups we store the cycle structures of elements.
*/
    zeit := Cputime();
    reps := [];
    ords := [];
    cycs := [];
    ClPows := [];
    ClSets := [];
    lths := [];
    cnts := [];
    numrat := 0;
    oldlth := #oldcl;
    done := {};
	// classes wrt oldcl which are already in class table or not required

    m := [0: i in [1 .. oldlth]]; // map from index in oldcl to index in cl
    minv := [];			  // map from index in cl to index in oldcl

    // identity class is not explicitly stored and we are not interested in
    // elements whose order involves a prime not in psq or classes in N
    pset := Seqset(psq);
    for i := 1 to oldlth do
	if oldcl[i][1] eq 1 or Seqset(PrimeBasis(oldcl[i][1])) notsubset pset
		or oldcl[i][3] in N then
	    Include(~done, i);
	end if;
    end for;
    vprintf Classes, 3:"Convert: initialisation after %o secs\n", Cputime(zeit);

    // run through classes, take a new rational class rep and
    // process that rational class
    for i := 1 to oldlth do
	if i notin done then
	    numrat +:= 1;
	    Include(~done, i);
	    x := oldcl[i][3];
	    reps[numrat] := x;
	    eltord := oldcl[i][1];
	    ords[numrat] := eltord;
	    cllth := oldcl[i][2];
	    lths[numrat] := cllth;
	    cycsq := CycleStructure(x);
	    cycs[numrat] := cycsq;
	    cnt := Centralizer(gp, x);
	    cnts[numrat] := cnt;
	    m[i] := numrat;
	    minv[numrat] := i;

	    // Now find the classes in the rational class
	    // Form set of all possible powers for this element order that
	    //   could give class representatives
	    allpow := {pw:pw in [1..eltord - 1]| GCD(pw, eltord) eq 1};
	    possib := {}; // set of possible classes in the rational class*/
	    for j := 1 to oldlth  do
		if j notin done then
		    if oldcl[j][1] eq eltord then
			if oldcl[j][2] eq cllth then
			    if CycleStructure(oldcl[j][3]) eq cycsq then
				possib := possib join {j};
			    end if;
			end if;
		    end if;
		end if;
	    end for;

	    if IsEmpty(possib) then
		pows := \[1];
		Sets := [allpow];
	    else
		numcl := 1;
		pows := \[1];
		oneset := {1};		// powers conjugate to ELT
		accfor := { 1 };	// powers accounted for
		numpos := #possib;
		for pw in allpow do
		    if pw notin accfor then
			newelt := x^pw;
			// check conjugate to ELT
			is_conj := IsConjugate(gp, newelt, x:
			    LeftSubgroup:=cnt, RightSubgroup:=cnt,
			    Centralizer := "None");
			if is_conj then
			    oneset := oneset join {pw};
			    oneset := Close(oneset, eltord);
			    // under consequences
			    accfor := accfor join oneset;
			    for nj := 2 to numcl do
				s := Imset(oneset, pows[nj], eltord);
				accfor := accfor join s;
			    end for;
			else
			    // check conjugate to a possible class rep
			    for j in possib diff done do
				is_conj := IsConjugate(gp, 
				    newelt, oldcl[j][3]: LeftSubgroup:=cnt,
				    Centralizer := "None");
				if is_conj then
				    numcl +:= 1;
				    pows[numcl] := pw;
				    s := Imset(oneset, pw, eltord);
				    accfor := accfor join s;
				    done := done join {j};
				    m[j] := numrat;
				    break;
				end if;
			    end for;
			end if;
		    end if;
		end for;
		Sets := [oneset];
		for nj := 2 to numcl do
		    s := Imset(oneset, pows[nj], eltord);
		    Sets[nj] := s;
		end for;
	    end if;
	    ClPows[numrat] := pows;
	    ClSets[numrat] := Sets;
	end if;
    end for;
    vprintf Classes, 3:"Convert: processed %o rational classes after %o secs\n", numrat, Cputime(zeit);

	cl := [*
	    reps, ords, cycs, ClPows, ClSets, lths, cnts, [], [], []
	*];

    vprintf Classes, 2:"Convert ended: %o secs\n", Cputime(zeit);
    return cl;
end function;

FusSetup := procedure(gp, nr, reps, ords, ClPows, ClSets, ~fgens, ~fpws:cents:=0)
/*
Set up info about fusion subgroup of NR-th rational class
*/
    x := reps[nr];
    eltord := ords[nr];
    oneset := ClSets[nr][1];
    fgens := [];
    w := PrimitiveRoot(eltord);
    pws := [];
    if cents cmpeq 0 then
	x_cent := 0;
    else
	x_cent := cents[nr];
    end if;
    if oneset ne {1} then
	// must calculate non trivial fusion subgroup
	// treat cases separately---
	//    p-element, p>2; 2-element; composite element
	eltfac := Factorisation(eltord);
	pelt := #eltfac eq 1;
	twoelt := pelt and eltfac[1][1] eq 2;
	if pelt and (not twoelt) then
	    // fusion group is cyclic
	    p := eltfac[1][1];
	    m := eltfac[1][2];
	    fusord := p - 1;
	    if m ge 2 then
		fusord := fusord * p^(m-1);
	    end if;
	    for wexp := 1 to fusord - 1 do
		pw := (w^wexp) mod eltord;
		if pw in oneset then
		    // have found generator of fusion subgroup
		    break;
		end if;
	    end for;
	    pws := [pw];
	    if x_cent cmpeq 0 then
		flg, cnjelt := IsConjugate(gp, x, x^pw);
	    else
		flg, cnjelt := IsConjugate(gp, x, x^pw:LeftSubgroup:=x_cent,
		    RightSubgroup:=x_cent, Centralizer:="None");
	    end if;
	    assert flg;
	    fgens := [cnjelt];
	else
	    if twoelt then
		p := 2;
		m := eltfac[1][2];
		if m gt 2 then
		    fusord := p^(m - 2);
		end if;
		mone := eltord - 1;	// generator of Z2 component
		w := 5 mod eltord;	// generator of other cyclic component

		if mone in oneset then	// just find subgroup of other component
		    pws := [mone];
		    if x_cent cmpeq 0 then
			flg, cnjelt := IsConjugate(gp, x, x^-1);
		    else
			flg, cnjelt := IsConjugate(gp, x, x^-1:
			    LeftSubgroup:=x_cent,
			    RightSubgroup:=x_cent, Centralizer:="None");
		    end if;
		    fgens := [cnjelt];
		    if m gt 2 and oneset ne {1, mone} then
			for wexp := 1 to fusord-1  do
			    pw := w^wexp mod eltord;
			    if pw in oneset then
				break;
			    end if;
			end for;
			pws := pws cat [pw];
			if x_cent cmpeq 0 then
			    flg, cnjelt := IsConjugate(gp, x, x^pw);
			else
			    flg, cnjelt := IsConjugate(gp, x, x^pw:
				LeftSubgroup:=x_cent,
				RightSubgroup:=x_cent, Centralizer:="None");
			end if;
			fgens := fgens cat [cnjelt];
		    end if;
		else
		    /* must also consider smashed cyclic subgroups */ 
		    for wexp := 1 to fusord - 1 do
			pw := (w^wexp) mod eltord;
			if pw in oneset then
			    break;
			end if;
			pw := mone * pw mod eltord;
			if pw in oneset then
			    break;
			end if;
		    end for;
		    pws := [pw];
		    if x_cent cmpeq 0 then
			flg, cnjelt := IsConjugate(gp, x, x^pw);
		    else
			flg, cnjelt := IsConjugate(gp, x, x^pw:
			    LeftSubgroup:=x_cent,
			    RightSubgroup:=x_cent, Centralizer:="None");
		    end if;
		    fgens := [cnjelt];
		end if;
	    else
		// composite element
		AbGpAnalyse(eltord, oneset, ~pws, ~ordsq);
		for pw in pws do
		    if x_cent cmpeq 0 then
			flg, cnjelt := IsConjugate(gp, x, x^pw);
		    else
			flg, cnjelt := IsConjugate(gp, x, x^pw:
			    LeftSubgroup:=x_cent,
			    RightSubgroup:=x_cent, Centralizer:="None");
		    end if;
		    fgens := fgens cat [cnjelt];
		end for;
	    end if;
	end if;
    end if;	// if oneset ne {1}
    fpws := [[w], pws];
end procedure;

AbGpAnalyse := procedure(eltord, oneset, ~powsq, ~ordsq)
/*
Analyse the abelian subgroup oneset of integers mod eltord
*/
    subord := #oneset;
    sfac := Factorisation(subord);
    onesq := Setseq(oneset);
    ords := [1: i in [1 .. subord]];
    powset := [{1}: i in [1 .. subord]];
    for pr := 1 to subord  do
	pw := onesq[pr];
	s := {1};
	num := pw;
	for i := 1 to subord  do
	    if num eq 1 then
		ords[pr] := i;
		powset[pr] := s;
		break;
	    else
		s := s join { num };
		num := num * pw mod eltord;
	    end if;
	end for;
    end for;

    powsq := [];
    ordsq := [];
    done := {1};
    ksub := {1};
    for i := 1 to #sfac do
	p := sfac[i][1];
	m := sfac[i][2];
	for n := m to 1 by -1 do
	    // find cyclic components of order p^n
	    for pr := 1 to subord  do
		pw := onesq[pr];
		ord := ords[pr];
		pows := powset[pr];
		if pw notin done and ord eq p^n and ksub meet pows eq {1} then
		    powsq := powsq cat [pw];
		    ordsq := ordsq cat [ord];
		    ksub := Close(ksub join pows, eltord);
		    done := done join ksub;
		end if;
	    end for;
	end for;
    end for;
end procedure;

Close := function(s1_orig, ord)
/*
In the cyclic group of order ord, we know that the generators
(given as integers representing a power) are conjugate.
Assume 1 is in s1_orig.
Form S2---the closure of all consequences of the conjugacy in S1.
*/
    s2 := s1_orig;
    repeat
	s1 := s2;
	for s in s1 do
	    pow := s;
	    while pow ne 1 do
		for n in s1 do
		    s2 := s2 join {n * pow mod ord};
		end for;
		pow := s * pow mod ord;
	    end while;
	end for;
    until s1 eq s2;
    return s2;
end function;

Imset := func<s1, pw, ord |
/*
Form the image under power pw mod ord of the set of integers s1
*/
    {x * pw mod ord: x in s1}
>;

AnalysePrimes := function(gp)
/*
Produce the primes in the sequence to be investigated
They should be in order from easiest to hardest in terms of
determining the elements of prime power order, and their fusion
in GP, as well as the sizes of their centralizers.
This is not very sophisticated---just listing them from
largest to smallest, and by increasing order of exponents.

Make 2 the last prime always.
*/
    gps := PrimeBasis(#gp);
    lth := #gps;
    psq := ExpSort(Reverse(gps), FactoredOrder(gp));
    pos := Position(psq, 2);
    if pos eq 0 or pos eq lth then
	return psq;
    end if;
    Remove(~psq, pos);
    Append(~psq, 2);
    return psq;
end function;

ExpSort := function(sq, expsq)
/*
Sort the entries of sq, a sequence of primes in increasing order of their
exponents in expsq, a pfactorisation sequence.
For equal exponents, preserve the order of the primes in the original sequence.
*/
    lth := #sq;
    expnts := [];
    for i := 1 to lth do
	p := sq[i];
	for pos := 1 to #expsq do
	    if p eq expsq[pos][1] then
		expnts[i] := expsq[pos][2];
		break;
	    end if;
	end for;
    end for;
    outsq := sq;
    for j := 1 to lth - 1  do
	for i := 1 to lth - j do
	    if expnts[i] gt expnts[i + 1] then
		// swap entries i and i + 1
		ts := outsq[i];
		te := expnts[i];
		outsq[i] := outsq[i + 1];
		expnts[i] := expnts[i + 1];
		outsq[i + 1] := ts;
		expnts[i + 1] := te;
	    end if;
	end for;
    end for;
    return outsq;
end function;

CheckOrder := function(psq, p, ord)
/*
Return true if ord is not divisible by p or a larger prime
or does not involve a prime in psq
*/
    if ord eq 1 then
	return false;
    end if;
    pset := Seqset(psq);
    for q in PrimeBasis(ord) do
	if q ge p or q notin pset then
	    return false;
	end if;
    end for;
    return true;
end function;

IspGroup := function(gp, p)
/*
Return true if gp is a p-group (including the identity)
*/
    f := FactoredOrder(gp);
    return #f eq 0 or #f eq 1 and f[1][1] eq p;
end function;

Expnt := function(g, p)
/*
Determine the exponent of p in the group order.
*/
    pairs := FactoredOrder(g);
    pexp := 0;
    for i := 1 to #pairs do
	if pairs[i][1] eq p then
	    return pairs[i][2];
	end if;
    end for;
    return 0;
end function;

CycleAction := function(G, x)
/*
x in centre G, return action of G on cycles of x 
*/
    forw := [];
    back := [];
    im := 0;
    _, f := StandardGroup(G);
    x_st := x@f;
    done := [false:i in [1..Degree(G)]];
    pt := 1;
    repeat
	im +:= 1;
	back[im] := pt;
	cyc := Cycle(x_st, pt);
	for c in cyc do
	    forw[c] := im;
	    done[c] := true;
	end for;
	pt := Position(done, false, pt+1);
    until pt eq 0;
    d := #back;
    S := Sym(d);
    f := hom<G->S|[ [forw[back[i]^g]:i in [1..d]] : j in [1..Ngens(G)] | true 
			    where g := G.j@f ] >;
    return f, Image(f), Kernel(f);
end function;

Filter := function(psq, gpord)
/*
Filter the sequence of primes so that only those involved in the group order
are listed.  (This routine could actually analyse the primes and change their
order of listing.)
*/
    gps := Seqset(PrimeBasis(gpord));
    return [p : p in psq | p in gps ];
end function;

ClRoots := function(gp, N, psq, pcl, pno, prnt, dbug)
/*
Determine the GP-classes of elements which are roots of the rational
class pcl[pno] of elements of order p^n.  The orders of the roots should
only involve p^n, and primes in psq.
PRNT is a flag that switches on printing.
DBUG is a flag to switch on debug printing.
*/
    zeit := Cputime();
    preps := ClReps(pcl);
    x := preps[pno];
    pords := ClOrds(pcl);
    p := PrimeBasis(pords[pno])[1];
    pcntlz := ClCnts(pcl);
    cnt := pcntlz[pno];
    cl := NewCl(gp);

    // no more to do if order of the centralizer does not involve a prime
    // in the set psq or the centralizer is contained in N
    if IsEmpty(Seqset(PrimeBasis(Order(cnt))) meet Seqset(psq)) or 
	cnt subset N
    then
	return cl;
    end if;

    if prnt  gt 1 then
	print "In ClRoots, the centralizer has order ", FactoredOrder(cnt);
    end if;
    f1, quot1, ker1 := CycleAction(cnt, x);
    if prnt  gt 1 then
	print "Blocks restriction to order ", FactoredOrder(quot1),
	      " degree ", Degree(quot1);
    end if;
    rest := Filter(psq, Order(quot1));
    clq := rHomClass(quot1, sub<quot1|>, NewCl(quot1), rest, prnt, dbug);
    qlth := ClLength(clq);
    if prnt gt 1 then
	print "In ClRoots, the quotient has ", qlth, " classes";
    end if;

    // allow for fusion of quotient classes under the action of the normalizer
    fused := {};
    for i := 1 to qlth  do
	if i notin fused then
	    LiftRatCl( gp, N, clq, i, f1, pcl, pno, fused, cl, ~cl, ~cnjset );
	    fused := fused join cnjset;
	end if;
    end for;

    cllth := ClLength(cl);
    if (cllth ne qlth) and prnt gt 1 then
	print "(which fuse to ", cllth, " classes under the normalizer)";
    end if;

    zeit := Cputime(zeit);
    if prnt gt 0 then
	print "ClRoots: ", cllth, " classes, took ", zeit, " seconds";
    end if;
    return cl;
end function;

LiftRatCl := procedure(gp, N, qcl, qno, f, gcl, gno, fused, incl, ~cl, ~cnjset)
/*
Given an element qelt = qcl[qno] of the image of the homomorphism f from
the centralizer in gp of kelt = gcl[gno] to its action on the cycles of kelt,
determine the gp-class representative of the unique rational class of elements
in the preimage of qelt which are r-th roots of kelt (where r is the order
of qelt).  This actually lifts the rational class qcl[qno] of the image.
Should have cl the same as incl and just append one new rational class.
Also consider fusion under the normalizer.
cnjset returns a set of indices of the qcl classes fusing to qno-th class.
*/
    greps := ClReps(gcl);
    kelt := greps[gno];
    gords := ClOrds(gcl);
    kord := gords[gno];
    p := PrimeBasis(kord)[1];

    qreps := ClReps(qcl);
    qelt := qreps[qno];
    qords := ClOrds(qcl);
    qord := qords[qno];
    y := qelt @@ f;
    yord := Order(y);
    r := yord;
    while r mod p eq 0 do
	r := r div p;
    end while;
    y := y^(yord div r);
    // an element of order coprime to P
    // make sure this Y is truly a preimage of QELT
    one, a, b := XGCD(r, kord);

    x := y * (kelt^a);
    assert x^qord eq kelt;
    assert x@f eq qelt^(yord div r);
    // is the representative of the unique rational class

    if x in N then
	cnjset := {qno};
	return;
    end if;

    gpows := ClPows(gcl);
    kpow := gpows[gno];
    gsets := ClSets(gcl);
    kset := gsets[gno];
    nqord := #kset[1];	// order of normaliser quotient
    ClFusPows(gp, ~gcl, gno, ~kfpows);
    ClFusgen(gp, ~gcl, gno, ~kfgens);

    qpows := ClPows(qcl);
    qpow := qpows[qno];
    qsets := ClSets(qcl);
    qset := qsets[qno];
    qcntlz := ClCnts(qcl);
    qcnt := qcntlz[qno];
    qgp := Image(f);
    ClFusPows(qgp, ~qcl, qno, ~qfpows);

    eltord := qord * kord;
    cycs := CycleStructure(x);

    // determine if the normalizer could fuse other QCL classes
    // set up the fusion subgroup as an abstract group, but not explicit
    // generators from GP
    efgens := [];
    ew := -1;
    // in general no primitive root exists
    if nqord eq 1 then
	// know everything already (God??)
	efuspo := LiftFPows(eltord, qord, kord, qfpows);
	Sets(eltord, efuspo, ~epows, ~esets);
	FusSetup := { qno };
    else
	posset := PossFusion(gp, y, f, qcl, qno, fused);
	if posset eq {qno} and #qpow eq 1 then
	    // no choice but to have direct product of the two fusion subgroups
	    fpsq1 := LiftFPows(eltord, kord, qord, kfpows);
	    fpsq2 := LiftFPows(eltord, qord, kord, qfpows);
	    efuspo := fpsq1 cat fpsq2;
	    Sets(eltord, efuspo, ~epows, ~esets);
	    FusSetup := {qno};
	else
	    /*separate cyclic and abelian but not cyclic cases*/
	    if #kfpows eq 1 then
		// cyclic case
		assert #kfgens eq 1; // must match ...
		assert kelt^(kfpows[1]) eq kelt^kfgens[1];
		CycLift(
		    gp, f, kfpows[1], kfgens[1], eltord, kord, qord, qcl,
		    qno, posset, ~fpow, ~FusSetup
		);
		fpsq2 := LiftFPows(eltord, qord, kord, qfpows);
		if fpow eq 1 then
		    // no more fusion found
		    efuspo := fpsq2;
		else
		    efuspo := [fpow] cat fpsq2;
		end if;
		Sets(eltord, efuspo, ~epows, ~esets);
	    else
		// abelian but not cyclic case
		print "should not come here---as 2 is last prime treated";
		// fudge
		efuspo := [];
		esets := [];
		epows := [];
		FusSetup := {qno};
	    end if;
	end if;
    end if;
    cntlzr := Centralizer(qcnt @@ f, x); // could be improved
    lth := Order(gp) div Order(cntlzr);
    cl := cladd(
	incl, x, eltord, cycs, epows, esets, lth, cntlzr, 0, efgens, ew, efuspo
    );
    cnjset := FusSetup;
    // which contains at least QNO
end procedure;

PossFusion := function(gp, y, f, qcl, qno, fused)
/*
Determine which rational classes in QCL could fuse to QCL[QNO] under the action
of an automorphism group which lies in GP.  The element Y of GP is the preimage
of QCL[QNO] and of the same order, so its cycle structure could be relevant.
FUSED is a set of classes already accounted for, so they cannot be in the
resulting set POSSET.
*/
    qlth := ClLength(qcl);
    qreps := ClReps(qcl);
    qords := ClOrds(qcl);
    qsets := ClSets(qcl);
    qlths := ClLths(qcl);
    qcycs := ClCycs(qcl);
    cycs := qcycs[qno];

    posset := { qno };
    for i := 1 to qlth  do
	if i notin (fused join {qno}) then
	    if qords[i] eq qords[qno] then
		if qlths[i] eq qlths[qno] then
		    if qsets[i][1] eq qsets[qno][1] then
			if qcycs[i] eq cycs then
			    posset := posset join { i };
			end if;
		    end if;
		end if;
	    end if;
	end if;
    end for;
    return posset;
end function;

LiftFPows := function(eltord, qord, kord, qfpows)
/*
Lift the generators QFPOWS of fusion subgroup (as integers mod QORD)
to those mod ELTORD = QORD*KORD, which are coprime.
Assume they centralize the KORD component.
*/
    efuspo := [];
    for i := 1 to #qfpows do
	qi := qfpows[i];
	for enum := 1 to eltord - 1 by kord do
	    // number must be 1 mod KORD
	    if enum mod qord eq qi then
		efuspo[i] := enum;
		break;
	    end if;
	end for;
    end for;
    return efuspo;
end function;

Sets := procedure(eltord, efuspo, ~epows, ~esets)
/*
Given the generators of the fusion subgroup, set up the fusion information.
*/
    oneset := Close({1} join Seqset(efuspo), eltord);
    esets := [oneset];
    epows := \[1];
    num := 1;
    done := oneset;
    for pw := 2 to eltord - 1 do
	if GCD(pw, eltord) eq 1 and pw notin done then
	    s := Imset(oneset, pw, eltord);
	    num +:= 1;
	    esets[num] := s;
	    epows[num] := pw;
	    done := done join s;
	end if;
    end for;
end procedure;

CycLift := procedure(gp, f, gfpw, gfgen, eltord, kord, qord, qcl, qno, posset, ~fpow, ~FusSetup)
/*
We have a cyclic fusion subgroup of the element of order KORD in GP.  It is
generated by the element GFGEN, which corresponds to the power GFPW mod KORD.
The quotient class QCL[QNO] lifts to an element of order ELTORD = KORD*QORD,
and may fuse under the normaliser to quotient classes in POSSET. Determine
the actual fusion.  Return the set FUSSET of quotient classes actually fused.
Return a generator FPOW mod ELTORD for the cyclic subgroup (of <GFPW>)
which normalizes QCL[QNO].
*/
    q := Image(f);
    qreps := ClReps(qcl);
    qelt := qreps[qno];
    qpows := ClPows(qcl);
    qepow := qpows[qno];
    qsets := ClSets(qcl);
    qeset := qsets[qno];

    // determine order of cyclic group
    num := gfpw;
    for i := 2 to kord - 1  do
	num := num * gfpw mod kord;
	if num eq 1 then
	    cycord := i;
	    break;
	end if;
    end for;

    // Try fusion, stopping once answer is known
    // Need to know which rational classes fuse under normalizer,
    //   and which classes within QCL[QNO] fuse

    // Get an elt in gp which maps to qelt. Doesn't matter which
    // gp class it is in? 
    gelt := qelt @@ f;

    FusSetup := { qno };
    nrmpw := cycord;
    for i := 1 to cycord - 1 do
	imelt := (gelt^(gfgen^i)) @ f;
	found := false;
	for qi in (posset diff FusSetup) do
	    IsRatConjugate(q, qcl, qi, imelt, ~cnjflg, ~pw);
	    if cnjflg then
		found := true;
		FusSetup := FusSetup join { qi };
		break;
	    end if;
	end for;
	if not found then
	    // I-th power must normalize QCL[QNO]
	    nrmpw := i;
	    break;
	end if;
    end for;

    if (nrmpw eq cycord) then
	impw := 1;
    else
	imelt := (gelt^(gfgen^nrmpw)) @ f;
	IsRatConjugate(q, qcl, qno, imelt, ~cnjflg, ~impw);
	assert cnjflg;
    end if;

    // so the NRMPW-th power of GFGEN normalizes QCL[QNO], and
    //   IMPW gives the fusion within the rational class QCL[QNO].

    // we need FPOW congruent to GFPW ^ NRMPW mod KORD and
    //   congruent to IMPW mod QORD
    knum := Modexp(gfpw, nrmpw, kord);
    // knum := (gfpw^nrmpw) mod kord;
    qnum := impw mod qord;
    if assigned fpow then delete fpow; end if;
    for fpw := 1 to eltord - 1  do
	if GCD(fpw, eltord) eq 1 and fpw mod kord eq knum and
		fpw mod qord eq qnum then
	    fpow := fpw;
	    break;
	end if;
    end for;
    assert assigned fpow;
end procedure;

IsRatConjugate := procedure(q, qcl, qi, imelt, ~cnjflg, ~pw)
/*
Determine whether IMELT is in the rational class QCL[QI],
and return the power which represents the class.
We know the invariants of the classes match.
*/
    qreps := ClReps(qcl);
    qelt := qreps[qi];
    qpows := ClPows(qcl);
    qepow := qpows[qi];
    pw := 0;
    for pow in qepow do
	cnjflg := IsConjugate(q, imelt, qelt^pow);
	if cnjflg then
	    pw := pow;
	    break;
	end if;
    end for;
end procedure;

ClPrime := func<gp, N, p, limit, prnt, dbug |
/*
Given a group GP, a prime P, determine the rational classes of GP of
elements of P-power order.
LIMIT is the number of elements required to complete the classes of GP.
PRNT is a flag that switches on printing.
DBUG is a flag to switch on debug printing.
*/
    GetpClasses(gp, N, GetpSylow(gp, p, prnt), p, limit, prnt, dbug)
>;

GetpSylow := function(gp, p, prnt)
/*
Form the sylow P-subgroup of GP.
*/
    zeit := Cputime();
    syl := SylowSubgroup(gp, p);
    zeit := Cputime(zeit);
    if prnt gt 0 then
	print "Sylow ", p, " subgroup took ", zeit, " seconds";
    end if;
    return syl;
end function;

pcpClasses := function(gp, N, p)
/*
Given a p-group by a pcp determine a class table for it.
NB also need power maps for these groups - place it in QCL
*/
    zeit := Cputime();
    oldcl := Classes(gp);
    reps := [];
    ords := [];
    cycs := [];
    ClPows := [];
    ClSets := [];
    lths := [];
    cnts := [];
    numrat := 0;
    oldlth := #oldcl;
    done := {1};
	// classes wrt oldcl which are already in class table or not required

    m := [0: i in [1 .. oldlth]]; // map from index in oldcl to index in cl
    minv := [];			  // map from index in cl to index in oldcl

    // identity class is not explicitly stored 
    powmap := PowerMap(gp);
    vprintf Classes, 3:"Convert: PowerMap after %o secs\n", Cputime(zeit);

    // run through classes, take a new rational class rep and
    // process that rational class
    for i := 1 to oldlth do
	if i in done then continue; end if;
	Include(~done, i);
	x := oldcl[i, 3];
	if x in N then continue; end if;
	numrat +:= 1;
	reps[numrat] := x;
	eltord := oldcl[i, 1];
	ords[numrat] := eltord;
	cllth := oldcl[i, 2];
	lths[numrat] := cllth;
	cnt := Centralizer(gp, x);
	cnts[numrat] := cnt;
	m[i] := numrat;
	minv[numrat] := i;

	// Now find the classes in the rational class
	// Form set of all possible powers for this element order that
	//   could give class representatives
	allpow := {pw:pw in [1..eltord - 1]| GCD(pw, eltord) eq 1};
	oneset := {pw:pw in allpow | powmap(i, pw) eq i};

	pows := \[1];
	Sets := [oneset];
	pows_to_do := allpow diff oneset;
	while #pows_to_do gt 0 do
	    pw := Rep(pows_to_do);
	    j := powmap(i, pw);
	    assert j notin done;
	    Include(~done, j);
	    Append(~pows, pw);
	    m[j] := numrat;
	    s := {pw:pw in pows_to_do | powmap(i, pw) eq j};
	    // assert s eq Imset(oneset, pw, eltord);
	    Append(~Sets, s);
	    pows_to_do diff:= s;
	end while;
	ClPows[numrat] := pows;
	ClSets[numrat] := Sets;
    end for;
    vprintf Classes, 3:"Convert: processed %o rational classes after %o secs\n", numrat, Cputime(zeit);

    // now set up fusion subgroup
    fusgen := [];
    fuspws := [];
/*
    for nr := 1 to numrat  do
	FusSetup(gp, nr, reps, ords, ClPows, ClSets, ~fgens, ~fpws);
	fusgen[nr] := fgens;
	fuspws[nr] := fpws;
    end for;
    vprintf Classes, 3:"Convert: fusion subgroups after %o secs\n", Cputime(zeit);
*/
    // now set up p power map
    pmap := [0: i in [1 .. numrat]];
    for nr := 1 to numrat  do
	pmap[nr] := m[powmap(minv[nr], p)];
    end for;
    cl := [*
	reps, ords, cycs, ClPows, ClSets, lths, cnts, pmap, fusgen, fuspws
    *];
    vprintf Classes, 2:"Convert ended: %o secs\n", Cputime(zeit);
    return cl, m, minv;
end function;

GetpClasses := function(gp, N, syl, p, limit, prnt, dbug)
/*
Given a group GP, a prime P, and a Sylow P-subgroup SYL of GP,
determine the GP-classes of elements of P-power order.
LIMIT is the number of elements required to complete the classes of GP.
PRNT is a flag that switches on printing.
DBUG is a flag to switch on debug printing.
*/
    zeit := Cputime();
    cnjcnt := 0;	// number of conjugacy tests in GP
    q, f := PCGroup(syl);
    N_image := IntersectionWithNormalSubgroup(syl, N)@f;
    qcl := pcpClasses(q, N_image, p);
    if dbug then
	print qcl;
    end if;
    qcllth := ClLength(qcl);
    qords := ClOrds(qcl);
    pcl := NewCl(gp);
    nogood := {};	// QCL classes that we know fuse in GP
    fusmap := [0: i in [1 .. qcllth]];	// PCL index of a Q-class, or 0
    over := false;
    totlth := 0;
    SylAnalyseU(gp, syl, p, q, f, qcl, dbug, ~list, ~outset);
    if dbug then
	print list, outset, q;
    end if;
    li := 1;
    while (li le qcllth) and (not over) do
	i := list[li];
	if i notin nogood then
	    IsNewRational(gp, pcl, q, f, qcl, i, fusmap, prnt, ~new, ~cnt, ~cent);
	    cnjcnt := cnjcnt + cnt;
	    if new then
		// add new rational class - must determine fusion within class
		if prnt  gt 1 then
		    zz := Cputime(zeit);
		    print "getpclasses---new class found at time: ", zz;
		end if;
		AddpClass(
		    gp, pcl, q, f, qcl, i, fusmap, prnt, cent, ~pcl, ~cnt, ~newlth
		);
		cnjcnt := cnjcnt + cnt;
		pos := ClLength(pcl);
		fusmap[i] := pos;
		totlth := totlth + newlth;
		over := totlth ge limit; // ge rather than eq to help catch bugs
	    else
		// whole rational class fuses
		nogood := nogood join outset[li];
	    end if;
	end if;
	li +:= 1;
    end while;

    assert totlth le limit;
    assert not(over and totlth lt limit);

    if over and GetVerbose("Classes") gt 1 then
	printf "getpclasses terminating: limit %o, have %o\n",
	    limit, totlth;
    end if;
    pcllth := ClLength(pcl);
    zeit := Cputime(zeit);
    if prnt  gt 0 then
	print "getpclasses took ", zeit, " seconds";
	print "   did ", cnjcnt, " conjugacy tests in GP";
	print "   and fused ", qcllth, " SYLP-classes into ", pcllth, " GP-classes";
    end if;
    return pcl;
end function;

centsig := func<C|[#C] cat [t[1]:t in OrbitRepresentatives(C)]>;

IsNewRational := procedure(gp, pcl, q, f, qcl, i, fusmap, prnt, ~new, ~cnt, ~xcent)
/*
Q is a P-subgroup of GP via homomorphism F.
PCL is the class table of known p-elements of GP.
QCL is the class table of Q.
PRNT is a flag that switches on printing.
Determine whether QCL[I] belongs to a new rational class of p-elements in GP.
Return the boolean result NEW, and a count CNT of the conjugacy tests in GP.
*/
    old := false;
    cnt := 0;

    qreps := ClReps(qcl);
    x := qreps[i] @@ f;
    qords := ClOrds(qcl);
    eltord := qords[i];
    eltcyc := CycleStructure(x);
    qpows := ClPows(qcl);
    qepows := qpows[i];
    qsets := ClSets(qcl);
    qesets := qsets[i];
    eltone := qesets[1];
    qpowma := ClPMaps(qcl);
    qcents := ClCnts(qcl);
    xcentsub := qcents[i] @@ f;

    preps := ClReps(pcl);
    pords := ClOrds(pcl);
    pcycs := ClCycs(pcl);
    ppows := ClPows(pcl);
    psets := ClSets(pcl);
    ppowma := ClPMaps(pcl);
    pcents := ClCnts(pcl);

    pcllth := ClLength(pcl);
    for j := 1 to pcllth do
	// are rational classes compatible - order, cycle structure, fusion
	if eltord ne pords[j] then
	    continue;
	end if;
	if eltcyc ne pcycs[j] then
	    continue;
	end if;
	if eltone notsubset psets[j][1] then
	    continue;
	end if;
	ok := PowFuse(i, qpowma, j, ppowma, fusmap);
	// if not OK then continue; end if;

	gelt := preps[j];
	gcent := pcents[j];
	// they are compatible so must test conjugacy
	for pw in ppows[j] do
	    cnt +:= 1;
	    ct := Cputime();
	    flg := IsConjugate(gp, x, gelt^pw : LeftSubgroup := xcentsub,
		    RightSubgroup := gcent, Centralizer := "None");
	    if prnt  gt 1 then
		print "isnewrat - conjugacy test took: ", Cputime(ct), " secs";
	    end if;
	    if flg then
		old := true;
		pos := j;
		break;
	    end if;
	end for;
	if old then
	    break;
	end if;
    end for;
    new := not old;
    if new then
	ct := Cputime();
	xcent := Centralizer(gp, x :Subgroup := xcentsub);
	if prnt  gt 1 then
	    print "isnewrat - centralizer took: ", Cputime(ct), " secs";
	end if;
    end if;
end procedure;

PowFuse := function(i, qmap, j, pmap, fusmap)
/*
(Should also test fusion of P-th powers)
If elements are of order P^N, N > 1, then must have the class of P-th powers
of PCL[I] being the same as the class of the P-th powers of ELT (mapped into
PCL locations, of course).  The Q-class of the P-th powers of ELT must have
given rise to a new rational class.
*/
    if pmap[j] ne 0 and qmap[i] ne 0 then
	return pmap[j] eq fusmap[qmap[i]];
    end if;
    return true;
end function;

AddpClass := procedure(
    gp, pcl, q, f, qcl, i, fusmap, prnt, cntlzr, ~pclout, ~cnt, ~totlth
)
/*
Q is a P-subgroup of GP via homomorphism F.
PCL is the class table of known p-elements of GP
QCL is the class table of Q
PRNT is a flag that switches on printing.
We know QCL[I] represents a new rational class of p-elements of GP,
we must add that class to PCL and determine any fusion within the class in GP.
PCLOUT is the updated version of PCL.
CNT records the number of conjugacy tests in GP.
TOTLTH is the total number of elements in the rational class.
*/
    cnt := 0;

    qreps := ClReps(qcl);
    x := qreps[i] @@ f;
    // assert IsCentral(cntlzr, sub<gp|x>);
    // assert cntlzr eq Centralizer(gp, x:Subgroup := cntlzr);
    qords := ClOrds(qcl);
    eltord := qords[i];
    qpows := ClPows(qcl);
    qepows := qpows[i];
    qsets := ClSets(qcl);
    qesets := qsets[i];
    ClFusgen(q, ~qcl, i, ~qfgens);
    ClFusPows(q, ~qcl, i, ~qfpows);
    ClPrmRoot(q, ~qcl, i, ~qw);
    qpowma := ClPMaps(qcl);

    p := PrimeBasis(eltord)[1];
    n := GetExp(eltord, p);

    if n eq 1 or qpowma[i] eq 0 then
	pthpow := 0;	// P-th power is the identity class
    else
	pthpow := fusmap[qpowma[i]];
    end if;
    if pthpow ne 0 then
	pesets := ClSets(pcl);
	pthfor := #pesets[pthpow][1]; // order of fusion subgroup of P-th power
    else
	pthfor := 0;	// unknown or the identity
    end if;

    if p eq 2 then
	// easy case - we know fusion
	epows := qepows;
	esets := qesets;
	fgens := [fx @@ f: fx in qfgens];
	w := qw;
	fpows := qfpows;
    else
	if n eq 1 then
	    // handle prime case
	    // in this case there is no information from the Sylow subgroup
	    // Aut(n) is Z(p-1), & we find the generator of the cyclic subgroup
	    pPowSequence(p, ~sq, ~wlogs);
	    sq := pPSqFilter(p, sq, wlogs, Order(gp) div eltord);
	    flg := false;
	    for pw in sq do
		cnt := cnt+1;
		ct := Cputime();
		flg, cnjelt := IsConjugate(gp, x, x^pw: LeftSubgroup := cntlzr,
			RightSubgroup := cntlzr, Centralizer:="None");
		if prnt  gt 1 then
		    zz := Cputime(ct);
		    print "addpclass---conjugacy test took: ", zz, " secs";
		end if;
		if flg then
		    cnjpw := pw;
		    break;
		end if;
	    end for;

	    if flg then
		// have a Z(p-1) component
		// result is just Z(p-1) component
		w := qw;
		fgens := [cnjelt];
		fpows := [cnjpw];
		pSetup(p, {cnjpw}, ~epows, ~esets);
	    else
		// Z(p-1) component is trivial
		// result is trivial
		w := qw;
		fgens := [];
		fpows := [];
		pSetup(p, {1}, ~epows, ~esets);
	    end if;
	else
	    // Handle prime power case - autgrp is cyclic
	    // In this case, the Sylow subgroup tells use the p-part of the
	    // fusion subgroup, while we must calculate the Z(p-1) component
	    // Both components and the result are cyclic
	    qPowSequence(p, n, ~sq, ~wlogs);
	    sq := qPSqFilter(p, n, sq, wlogs, pthfor, Order(gp) div eltord);
	    flg := false;
	    for pw in sq do
		cnt +:= 1;
		ct := Cputime();
		flg, cnjelt := IsConjugate(gp, x, x^pw: LeftSubgroup := cntlzr,
			RightSubgroup := cntlzr, Centralizer:="None");
		if prnt gt 2 then
		    zz := Cputime(ct);
		    print "addpclass---conjugacy test took: ", zz, " secs";
		end if;
		if flg then
		    cnjpw := pw;
		    break;
		end if;
	    end for;
	    if flg then
		// have a Z(p-1) component
		// combine p-part and Z(p-1) component
		w := qw;
		if qfgens eq [] then
		    fgens := [cnjelt];
		    fpows := [cnjpw];
		    qSetup(p^n, {cnjpw}, ~epows, ~esets);
		else
		    fgens := [cnjelt * (qfgens[1] @@ f)];
		    fpows := [cnjpw * qfpows[1] mod (p^n)];
		    qSetup(p^n, qesets[1] join {cnjpw}, ~epows, ~esets);
		end if;
	    else
		// Z(p-1) component is trivial
		// result is just p-part lifted from QCL
		epows := qepows;
		esets := qesets;
		if qfgens eq [] then
		    fgens := [];
		else
		    fgens := [qfgens[1] @@ f];
		end if;
		w := qw;
		fpows := qfpows;
	    end if;
	end if;
    end if;
    // Separate treatment of prime and prime power case
    // Now set up new entry in class table
    lth := Order(gp) div Order(cntlzr);
    cycs := CycleStructure(x);
    totlth := #epows * lth;

    if prnt gt 1 then
	print "addpclass adding new rational class";
	print "elements have order: ", eltord;
	print "there are ", #epows, " classes";
	print "each of length: ", lth;
    end if;

    pclout := cladd(
	pcl, x, eltord, cycs, epows, esets, lth, cntlzr, pthpow, fgens, w, fpows
    );
end procedure;

pPowSequence := procedure(p, ~sq, ~pows)
/*
Set up an ordered list of powers to try in conjugacy test to determine
the fusion of an element of prime order P where we are working down
the subgroup lattice.  Hence the first power we find which is conjugate to the
element generates the cyclic subgroup of the fusion pattern.
POWS is the corresponding sequence of logarithms wrt primitive root.
*/
    if p eq 2 then
	sq := [];
	pows := [];
	return;
    end if;

    fusord := p - 1;
    n := 1;
    w := PrimitiveRoot(p);
    qs := PrimeBasis(fusord);
    sq := [w];
    sqlth := 1;
    pows := \[1];
    i := 1;
    while i le sqlth do
	pw := pows[i];
	ord := fusord div pw; // order of this cyclic subgroup
	if not IsPrime(ord) then
	    // take its maximals which are not already in the list
	    for q in PrimeBasis(ord) do
		newpw := pw * q;
		if Position(pows, newpw) eq 0 then
		    sqlth := sqlth + 1;
		    pows[sqlth] := newpw;
		    sq[sqlth] := (w^newpw) mod (p^n);
		end if;
	    end for;
	end if;
	i +:= 1;
    end while;
end procedure;

pPSqFilter := function(p, sq, wlogs, gord)
    /*
    Filter the sequence produced by ppowsequence.
    The order of the fusion subgroup must divide GORD.
    */

    fusord := p - 1;	// order of largest fusion subgroup

    // delete those not compatible with GORD
    sqout := [];
    lth := 0;
    for j := 1 to #sq do
	if gord mod (fusord div wlogs[j]) eq 0 then
	    lth := lth+1;
	    sqout[lth] := sq[j];
	end if;
    end for;
    return sqout;
end function;

pSetup := procedure(p, cnjset, ~epows, ~esets)
/*
Given that the power(s) CNJSET generate the cyclic group of the fusion of
our element of prime order P, set up the sequence of powers for the class reps,
and the sets of powers in each class.
*/
    if cnjset eq {1} or IsEmpty(cnjset) then
	// no fusion at all in rational class
	epows := \[1];
	esets := [{1}];
	w := PrimitiveRoot( p );
	for pw := 1 to p - 2  do
	    s := (w ^ pw) mod p;
	    epows[pw + 1] := s;
	    esets[pw + 1] := {s};
	end for;
    else
	oneset := Close(cnjset join {1}, p);
	done := oneset;
	epows := \[1];
	numcl := 1;
	esets := [oneset];
	for pw := 2 to p - 1 do
	    if pw notin done then
		numcl +:= 1;
		epows[numcl] := pw;
		s := Imset(oneset, pw, p);
		esets[numcl] := s;
		done := done join s;
	    end if;
	end for;
    end if;
end procedure;

qPowSequence := procedure(p, n, ~sq, ~pows)
/*
Set up an ordered list of powers to try in conjugacy test to determine the
fusion of an element of order P ^ N, N ge 2, P ne 2 where we are working down
the subgroup lattice.  We are only interested in the Z(p-1) component.
Hence the first power we find which is conjugate to the
element generates the cyclic subgroup of the Z(p-1) component.
POWS is the corresponding sequence of logarithms wrt primitive root.
*/
    fusord := p^(n - 1) * (p - 1);
    ppart := p^(n-1);
    w := PrimRoot(p, n, fusord);

    qs := PrimeBasis(fusord);

    sq := [w^ppart mod (p^n)];
    sqlth := 1;
    pows := [ppart];
    i := 1;
    while i le sqlth do
	pw := pows[i];
	ord := fusord div pw; // order of this cyclic subgroup
	if not IsPrime(ord) then
	    // take its maximals which are not already in the list
	    for q in PrimeBasis(ord) do
		newpw := pw * q;
		if Position(pows, newpw) eq 0 then
		    sqlth := sqlth + 1;
		    pows[sqlth] := newpw;
		    sq[sqlth] := w ^ newpw mod (p^n);
		end if;
	    end for;
	end if;
	i +:= 1;
    end while;
end procedure;

PrimRoot := func<p, n, fusord | PrimitiveRoot(p^n)>;

qPSqFilter := function(p, n, sq, wlogs, pthfor, gord)
/*
Filter the sequence produced by qpowsequence to account for the order of
the fusion subgroup of the P-th power.
The order of the fusion subgroup must also divide GORD.
*/
    fusord := p^(n - 1) * (p - 1); // order of largest fusion subgroup

    // delete those not compatible with both PTHFORD and GORD
    sqout := [];
    lth := 0;
    for j := 1 to #( sq )  do
	if pthfor mod (fusord div wlogs[j]) eq 0 and
		gord mod (fusord div wlogs[j]) eq 0 then
	    lth := lth+1;
	    sqout[lth] := sq[j];
	end if;
    end for;
    return sqout;
end function;

qSetup := procedure(eltord, cnjset, ~epows, ~esets)
/*
Given that the power(s) CNJSET generate the group of the fusion of our element
of order ELTORD, set up the sequence of powers for the class reps,
and the sets of powers in each class.
*/
    if cnjset eq {1} or IsEmpty(cnjset) then
	// no fusion at all in rational class
	epows := \[1];
	esets := [{1}];
	lth := 1;
	for pw := 2 to eltord - 1  do
	    if GCD(pw, eltord) eq 1 then
		lth +:= 1;
		epows[lth] := pw;
		esets[lth] := {pw};
	    end if;
	end for;
    else
	oneset := Close(cnjset join {1}, eltord);
	done := oneset;
	epows := \[1];
	numcl := 1;
	esets := [oneset];
	for pw := 2 to eltord - 1  do
	    if pw notin done and GCD(pw, eltord) eq 1 then
		numcl +:= 1;
		epows[numcl] := pw;
		s := Imset(oneset, pw, eltord);
		esets[numcl] := s;
		done := done join s;
	    end if;
	end for;
    end if;
end procedure;

SylAnalyse := procedure(gp, syl, p, q, f, qcl, dbug, ~list, ~outset)
/*
Analyse the classes of the sylow P-subgroup of GP.
Produce
LIST - a list of the class indexes in QCL in the order in which they
    should be processed for fusion in GP
OUTSET - a corresponding sequence of Sets of QCL indexes such that
    if the class LIST[J] fuses to an earlier (in LIST) class
    then we can deduce that all the classes in OUTSETS[J] fuse as well.
DBUG is a flag to switch on debug printing.

Set up information about the rational classes of Q.
Viz,
PTHS[I]    the set of classes of elements of order P^I
RTS[I]     the set of classes which are P-th roots of class I
CYCSTR[I]  the I-th distinct cycle structure in GP encountered
CYCSETS[I] the set of classes whose elements (lifted) have cycle str CYCSTR[I]

We will eliminate all roots of a class if it fuses in GP, but for this to be
correct we must process the classes (within a given category) in order of
decreasing centralizer order in Q.

For fusion within a class to be correct when lifted, we need the classes within
a given category and centralizer order to be order in decreasing order of their
normalizer.
*/
    zeit := Cputime();
    qlth := ClLength(qcl);
    reps := ClReps(qcl);
    ords := ClOrds(qcl);
    qPowSequence := ClSets(qcl);
    powmap := ClPMaps(qcl);
    cnts := ClCnts(qcl);

    qexp := GetExp(Order(q), p);

    pths := [{0}: i in [1 .. qexp]];
    rts := [{0}: i in [1 .. qlth]];
    // 0 entry is a fudge as cayley doesnot like null

    numcyc := 0;
    cycstr := [];
    cycset := [];
    for i := 1 to qlth  do
	eltord := ords[i];
	eltexp := GetExp(eltord, p);
	pths[eltexp] := pths[eltexp] join { i };
	pow := powmap[i];
	if pow ne 0 then
	    rts[pow] := rts[pow] join { i };
	end if;
	x := reps[i] @@ f;
	cycsq := CycleStructure(x);
	pos := Position(cycstr, cycsq);
	if pos eq 0 then
	    numcyc +:= 1;
	    cycstr[numcyc] := cycsq;
	    cycset[numcyc] := {i};
	else
	    cycset[pos] := cycset[pos] join {i};
	end if;
    end for;

    // find order of largest element
    for j := qexp to 1 by -1 do
	if pths[j] ne {0} then
	    nmax := j;
	    break;
	end if;
    end for;

    // get centralizer orders - for use in sorting classes
    cntexp := [];
    for i := 1 to qlth  do
	ce := GetExp(Order(cnts[i]), p);
	cntexp[i] := ce;
    end for;

    // get order of fusion subgroup - for use in sorting
    nrmexp := [];
    for i := 1 to qlth  do
	nexp := GetExp(#qPowSequence[i][1], p);
	nrmexp[i] := nexp;
    end for;

    // Now implement some strategy to order the classes for processing.
    list := [];
    outset := [];
    listlt := 0;
    done := {};	// record which classes have been added to the list

    // Choose Q-classes that by virtue of the cycle structures we know
    // will not fuse in GP. Cover each cycle structure.
    cycdon := {};	// record cycle structures which have been included
    picks := [[] : i in [1 .. nmax]]; // choices of classes for each order
    // we want to sort them from low to high in list
    for n := nmax to 1 by -1 do
	// run through cycle structures for elements of order P^N
	for cj := 1 to numcyc  do
	    if (cycstr[cj][1][1] eq (p^n)) and cj notin cycdon then
		qi := OSetRep(cycset[cj], cntexp, nrmexp);
		picks[n] := picks[n] cat [qi];
		cycdon := cycdon join { cj };
		done := done join { qi };

		// now look at powers of this class
		pi := qi;
		for nn := n-1 to 1 by -1 do
		    pi := powmap[pi];
		    pos := CycPos(cycset, pi);
		    if pos in cycdon then
			break;
		    else
			picks[nn] := picks[nn] cat [pi];
			cycdon := cycdon join { pos };
			done := done join { pi };
		    end if;
		end for;
	    end if;
	end for;
    end for;

    // now place the PICKS in LIST in order of increasing element order
    for n := 1 to nmax do
	sq := picks[n];
	for j := 1 to #sq do
	    listlt +:= 1;
	    list[listlt] := sq[j];
	    outset[listlt] := { sq[j] };
	end for;
    end for;

    // Now add the remaining classes
    // Use a depth first traversal of the root tree
    // Order classes at a given depth by decreasing centralizer order
    //   and then by decreasing normalizer order*

    pels1 := cntsor(Setseq(pths[1] diff {0}), nrmexp);
    pelsq := cntsor(pels1, cntexp);

    for qi in pelsq do
	// determine its roots - as a sequence in depth first order
	rtsq := RootClose(rts, qi, cntexp, nrmexp);
	if qi notin done then
	    listlt +:= 1;
	    list[listlt] := qi;
	    done := done join { qi };
	    outset[listlt] := Seqset(rtsq) join { qi };
	end if;
	for pi in rtsq do
	    if pi notin done then
		listlt +:= 1;
		list[listlt] := pi;
		pisq := RootClose(rts, pi, cntexp, nrmexp);
		outset[listlt] := Seqset(pisq) join { pi };
		done := done join { pi };
	    end if;
	end for;
    end for;

    if dbug then
	print "classes of order P^I are ", pths;
	print "Sets of P-th roots are ", rts;
	print "distinct cycle structures are ", cycstr;
	print "Sets sorted by cycle structure are ", cycset;
    end if;

    if listlt ne qlth then
	print "error in sylow analyse";
	print pths, rts, cycstr, cycset, list, outset;
    end if;
    vprintf Classes, 2:"SylAnalyse ended: %o secs\n", Cputime(zeit);
end procedure;

GetExp := func<q, p |
/*
Return the  positive integer EXPNT such that Q = P^EXPNT, for prime P.
*/
    q eq 1 select 0 else Factorisation(q)[1][2]
>;

OSetRep := func<s, exps1, exps2 |
/*
Choose a setrep of S such that it has maximum value in EXPS1,
and then a maximum within EXPS2.
*/
    cntsor(cntsor(Setseq(s), exps2), exps1)[1]
>;

CycPos := function(sq, i)
/*
SQ is a sequence of disjoint Sets.  Find the position of the set containing I.
*/
    for j := 1 to #sq do
	if i in sq[j] then
	    return j;
	end if;
    end for;
end function;

RootClose := function(rts, qi, cntexp, nrmexp)
/*
RTS is a sequence of P-th roots of the classes.  QI is a class.
Return a sequence of all roots of QI ordered in a depth first fashion.
*/
    qrts := rts[qi] diff {0};
    if qrts eq {} then
	outsq := [];
    else
	// must sort roots in terms of centralizer orders
	//   and then normalizer orders*/
	qrts1 := cntsor(Setseq(qrts), nrmexp);
	qrtsq := cntsor(qrts1, cntexp);
	outs := [];
	for i in qrtsq do
	    outs := outs cat [i];
	    outs := outs cat $$(rts, i, cntexp, nrmexp);
	end for;
	outsq := outs;
    end if;
    return outsq;
end function;

cntsor := function(sq, expsq)
/*
Sort the entries of SQ, a sequence of class indexes in decreasing order of
their exponents in EXPSQ.  For equal exponents, preserve the order
in the original sequence.
*/
    lth := #sq;
    outsq := sq;
    for j := 1 to lth - 1 do
	for i := 1 to lth - j do
	    if expsq[outsq[i]] lt expsq[outsq[i+1]] then
		// swap entries I and I+1
		ts := outsq[i];
		outsq[i] := outsq[i+1];
		outsq[i+1] := ts;
	    end if;
	end for;
    end for;
    return outsq;
end function;

SylAnalyseU := procedure(gp, syl, p, q, f, qcl, dbug, ~list, ~outset)
/*
Analyse the classes of the sylow P-subgroup of GP.
Produce
LIST - a list of the class indexes in QCL in the order in which they
    should be processed for fusion in GP
OUTSET - a corresponding sequence of Sets of QCL indexes such that
    if the class LIST[J] fuses to an earlier (in LIST) class
    then we can deduce that all the classes in OUTSETS[J] fuse as well.
DBUG is a flag to switch on debug printing.

Set up information about the rational classes of Q.
Viz,
PTHS[I]    the set of classes of elements of order P^I
RTS[I]     the set of classes which are P-th roots of class I
CYCSTR[I]  the I-th distinct cycle structure in GP encountered
CYCSETS[I] the set of classes whose elements (lifted) have cycle str CYCSTR[I]

We will eliminate all roots of a class if it fuses in GP, but for this to be
correct we must process the classes (within a given category) in order of
decreasing centralizer order in Q.

For fusion within a class to be correct when lifted, we need the classes within
a given category and centralizer order to be order in decreasing order of their
normalizer.

Bill Unger's version
*/
    zeit := Cputime();
    qlth := ClLength(qcl);
    reps := ClReps(qcl);
    ords := ClOrds(qcl);
    qPowSequence := ClSets(qcl);
    powmap := ClPMaps(qcl);
    cnts := ClCnts(qcl);


    // get element orders - for use in sorting classes
    eltexp := [];
    for i := 1 to qlth  do
	ee := GetExp(ords[i], p);
	eltexp[i] := -ee;
    end for;

    // get centralizer orders - for use in sorting classes
    cntexp := [];
    for i := 1 to qlth  do
	ce := GetExp(Order(cnts[i]), p);
	cntexp[i] := ce;
    end for;

    // get order of fusion subgroup - for use in sorting
    nrmexp := [];
    for i := 1 to qlth  do
	nexp := GetExp(#qPowSequence[i][1], p);
	nrmexp[i] := nexp;
    end for;

    // Now implement some strategy to order the classes for processing.

    cmp_func := function(i,j)
	res := eltexp[j] - eltexp[i];
	if res ne 0 then return res; end if;
	res := cntexp[j] - cntexp[i];
	if res ne 0 then return res; end if;
	return nrmexp[j] - nrmexp[i];
    end function;
    list := [1..qlth];
    Sort(~list, cmp_func);

    // list is in incr. elt order, decr. cent order, decr. norm order

    // set up outset's of roots
    listinv := []; // inverse permutation for list
    for i := 1 to #list do
	listinv[list[i]] := i;
    end for;
    outset := [{i}:i in list];
    for i := #list to 1 by -1 do
	j := powmap[list[i]];
	if j gt 0 then
	    outset[listinv[j]] join:= outset[i];
	end if;
    end for;

    if #list ne qlth then
	print "error in sylow analyse";
	print eltexp, cntexp, nrmexp, list, outset;
    end if;
    vprintf Classes, 2:"SylAnalyse ended: %o secs\n", Cputime(zeit);
end procedure;

intrinsic ClassesInductive(G::GrpPerm, N::GrpPerm, C::SeqEnum[Tup]) -> SeqEnum
{Implementation of G. Butler's inductive algorithm for conjugacy classes of a 
permutation group};
    fl, stored_cls := HasAttribute(G, "Classes");
    if fl then return stored_cls; end if;
    if N eq G then
	G`Classes := C;
	return Classes(G);
    end if;
    Ncls := Convert(G, sub<N|>, C, [t[1]:t in FactoredOrder(G)]);
    cls := HomClass(G, N, Ncls, GetVerbose("Classes"), false);

    /* Classes is a write-once attribute. So we can't reset them anyway. */
    fl, stored_cls := HasAttribute(G, "Classes");
    if fl then return stored_cls; end if;

    reps := [ <1,1,G!1> ];
    for i := 1 to #cls[1] do
        x := cls[1][i];
	x_ord := Order(x);
        pows := cls[4][i];
        len_cls := cls[6][i];
        // len_cls;
        for j := 1 to #pows do
            Append( ~reps, <x_ord, len_cls, x^pows[j]> );
        end for;
    end for;
    G`Classes:= reps;
    return Classes(G);
end intrinsic;

intrinsic ClassesInductiveSetup(G::GrpPerm, N::GrpPerm, C::SeqEnum[Tup])
{Implementation of G. Butler's inductive algorithm for conjugacy classes of a 
permutation group. This version stores the class table with the group};
    fl := HasAttribute(G, "Classes");
    if fl then return; end if;
    if N eq G then
	G`Classes := C;
	return;
    end if;
    Ncls := Convert(G, sub<N|>, C, [t[1]:t in FactoredOrder(G)]);
    cls := HomClass(G, N, Ncls, GetVerbose("Classes"), false);
    fl := HasAttribute(G, "Classes");
    if fl then return; end if;
// TES(G);
    reps := [ <1, 1, G!1, sub<G|G>, [[1,1]]> ];
    Z := Integers();
    for i := 1 to #cls[1] do
        x := cls[1][i];
        pows := cls[4][i];
        len_cls := cls[6][i];
	cent := cls[7][i];
	x_ord := Order(x);
        base := #reps+1;
        for j := 1 to #pows do
	    if #pows eq 1 then
// "A";
		U,f := UnitGroup(Integers(x_ord));
		powmap := [ [Z|u@f,base]:u in Generators(U)];
	    else
// "B";
		powmap := [ [Z|Modinv(pows[j], x_ord), base] ];
	    end if;
/*
reps;
Universe(reps);
<x_ord, len_cls, x^pows[j], cent, powmap>;
Parent(<x_ord, len_cls, x^pows[j], cent, powmap>);
*/
            Append( ~reps, <x_ord, len_cls, x^pows[j], cent, powmap> );
        end for;
	if #pows gt 1 then
	    powmap := [[j,base]:j in cls[5,i,1]|j ne 1];
	    reps[base, 5] := powmap;
	end if;

    end for;
    G`Classes:= reps;
end intrinsic;

intrinsic ClassesInductive(G::GrpPerm) -> SeqEnum
{Implementation of G. Butler's inductive algorithm for conjugacy classes of a 
permutation group};
    return ClassesInductive(G, sub<G|>, [<1,1,G!1>]);
end intrinsic;

intrinsic ClassesInductiveSetup(G::GrpPerm)
{Implementation of G. Butler's inductive algorithm for conjugacy classes of a 
permutation group. This version stores the class table with the group};
    ClassesInductiveSetup(G, sub<G|>, [<1,1,G!1>]);
end intrinsic;


