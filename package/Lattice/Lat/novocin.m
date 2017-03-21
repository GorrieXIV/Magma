freeze;

ReduceLat:=function(A,bound)
    if true then
	N := Orthogonalize(Matrix(RealField(100), A));
	len := Nrows(N);
	while Norm(N[len]) gt bound do
	    len -:= 1;
	end while;
	A := RowSubmatrix(A, len);
    else
 Gr:=GramLength(A);
 len:=#Gr;
 while Gr[len] gt bound do
   len-:=1;
 end while;
 //"reduced to dimension", len;
 //"Gram length", [Round(Log(x)/Log(10)):x in Gr];
 A:=RowSubmatrix(A,len);
 end if;
 return A, len;
end function;

//Code from Damien
intrinsic GramLength(L::Mtrx) -> SeqEnum
{Gram-Schmid length}

 G:=GramMatrix (L);
 return GramLengthFromGram(G);
end intrinsic;

intrinsic GramLengthFromGram(G::Mtrx) -> SeqEnum
{Gram-Schmid length}

 d:=NumberOfRows (G);
 R:=RealField(Ceiling(53+1.6*d):Bits:=true);
// precision sufficient for guaranteeing a few correct bits
// of results, starting from (0.99,0.51)-LLL-reduced bases
 T:=Cholesky(ChangeRing(G, R));
 m:=Minimum(NumberOfRows(T),NumberOfColumns(T));
 return [T[i][i]: i in [1..m]];
end intrinsic;


intrinsic LLL(A::Mtrx, P::[RngIntElt], B::FldReElt : Alpha := 1.2) -> Mtrx
{Implement a variant of the LLL algorithm as described by Novocin (LATIN 2010), Algorithm 3};

    r := Nrows(A);
    N := Ncols(A);

    require N lt r : "I am not going to implement the non-trivial bit of Step 1, if you want it you do it";

    c := r + N;

    s := r;
    M := IdentityMatrix(Integers(), r);

    for j in [1 .. N] do
	yj := ColumnSubmatrix(M, r)*ColumnSubmatrix(A, j, 1);
	l := Floor(Log(2, Max([Abs(P[j]), Max([Abs(y) : y in Eltseq(yj)]), 2])));
	require P[j] ne 0 : "What do I do about 0 P[j], continue or re-LLL?";
	z := Matrix(Rationals(), 1, Ncols(M) + 1, [0 : i in [1 .. Ncols(M)]] cat [P[j]/2^l]);
	M := HorizontalJoin(Matrix(Rationals(), M), Matrix(Rationals(), yj)/2^l);
	M := VerticalJoin(z, M);
	s +:= 1;
	while l ne 0 do
	    yj := 2^l*ColumnSubmatrix(M, Ncols(M), 1);
	    ll := Max([Abs(y) : y in Eltseq(yj)])/(Alpha^(2*c)*B^2);
	    if ll le 1 then
		l := 0;
	    else
		l := Ceiling(Log(2, ll));
	    end if;
	    M := ColumnSubmatrix(M, r + j - 1);
	    M := HorizontalJoin(M, yj/2^l);
	    M := LLL(M : Proof := false, InitialSort := false);
	    M, s := ReduceLat(M, B);		
	end while;
	M := Matrix(Integers(), M);
    end for;

    return M;
end intrinsic;

/*
# A version of vH+N that uses rounding, for inputs determined mod a prime power.
#
#            Mark van Hoeij,  June 2012.


# Let q be a prime-power, say q = p^a.
#
# Let  v_1, v_2, .., v_r   be vectors, each with N entries,  and each entry
# determined by a computation modulo q.
# Let B be a positive integer, and let V_1  be the vector (1 0 0 ... 0 v_1)
# (I'm using row-notation in this file since that's easier to type).

# Likewise, let V_2 be the vector (0 1 0 .. 0 v_2), etc.
# up to V_r = (0 0 0 ... 1 v_r).

# So each V_i is a vector with r+N entries.   Now let
# Q_1 = (0 0 0 ... 0   q 0 ... 0)
# ...
# Q_N = (0 0 0 ... 0   0 0 ... q)
#
# So Q_i has a q in the (r+i)'th entry, and 0's elsewhere.

# Now consider the vectors  Q_1, Q_2,.., Q_N, V_1, V_2, ..., V_r  in Z^{r+N}.
# Notice that large entries occur only in the last N entries of each vector.
# The first r entries are 0's for the Q_i and 0's and a 1 for each V_i.

# Let L be the Z-SPAN of those N+r vectors inside Z^{r+N}.
# The goal is to compute vectors W_1, .., W_d inside L such that:
#  a) W_1 .. W_d are LLL-reduced.
#  b) Every element of L with SquareLength <= B is an element of the Z-SPAN of W_1 .. W_d.
#  c) If W_1^* .. W_d^* are the Gram-Schmidt vectors of W_1 .. W_d,  then the SquareLength of W_d^*
#     is <= B (if using exact arithmetic), or, <= (1+eps)*B  (if using floating point
#     arithmetic, where eps is a bound for the relative precision of W_d^*).
*/

intrinsic LLL(A::Mtrx, p::RngIntElt, a::RngIntElt, B::RngIntElt)->Mtrx
{Mark van Hoeij's Gradual LLL (Novocin LATIN 2010) mod p^a using rounding}
    r := Nrows(A);
    N := Ncols(A);

/*
#  Step  := the smallest p-power that is >= 2^(C1*r) and also >= 2^(C2*r) * B^2.
# So
#  Step := p^lStep,  with lStep as in the program below.
#
#  numSt := an integer for which q / Step^numSt  is in the range [Step, Step^2).
#  (see the program below for details).
*/
    C1 := 10;
    C2 := 2;
    lStep := Maximum(Ceiling(C1*r*Log(2)/Log(p)), Ceiling((C2*r*Log(2) + 2*Log(B))/Log(p)));

    Step := p^lStep;
    numSt := Floor(a/lStep) - 1;
    q := p^a;
    if numSt le 0 then
//"numSt :", numSt;
	L := HorizontalJoin(IdentityMatrix(Integers(), r), A);
	z := HorizontalJoin(ZeroMatrix(Integers(), N, r), ScalarMatrix(N, q));
	L := VerticalJoin(z, L);
	L := LLL(L : Proof := false, InitialSort := false);
	return ReduceLat(L, B);
    end if;

/*
# Denote:
#  q_0 := Step^numSt
#  q_1 := Step^(numSt - 1)
#  q_2 := Step^(numSt - 2)
#  ...
#  q_numSt := 1
#
#  Note that q / q_0 is the range [Step, Step^2), this number is denoted as qFirst
*/
    q_0 := Step^numSt;
    qFirst := p^(a - lStep*numSt);
    Br := Ceiling(B + B*r/4);
    Br2 := #IntegerToString(2^r*Br); //Number of decimal digits

    IsAlreadyZero := function(L, v, q)
	r := Nrows(v);
	for i := Nrows(L) to 1 by -1 do
	    if &+[L[i][j]*v[j][1] : j in [1..r]] mod q ne 0 then
		return false;
	    end if;
	end for;
	return true;
    end function;

/*
# Now denote  v_{i,j} := round(v_i / q_j).
# Now we can write
#
#	v_{i, j+1} = Step * v_{i,j} + R_{i,j}   (1)
#
# where R_{i,j} is a vector with N entries, all of which have abs value <= Step/2.
# This formula (1) is implemented in the program Formula1 below  (note: this
# implementation treats just one entry of the vectors v_{i,j} and R_{i,j}).
#
# We have to compute:  v_{i, 0}  for each i=1..r
# and compute R_{i,j} for each i=1..r and j = 0..numSt-1.  For one entry of v_{i,0}, this
# is done in the procedure CutV below.
# Once we have v_{i, 0} and R_{i,j} (for j=0,1,2,..), then the values of v_{i,j} (for j=1,2,...)
# are not needed anymore because those will be recursively obtained from formula (1)
# as done in the program Formula1 below.
*/

    //# Returns v_0 as output.  The R values are written in table R.
    CutV := function(v, q_0, Step, numSt, R, j)
	v_i := v[1];
	for i := numSt to 1 by -1 do
	    q, r := Quotrem(v_i, Step);
	    if 2*r gt Step then
		r := r - Step;
		q := q+1;
	    end if;
	    v_i := q;
	    R[i][j] := r;
	end for;
	return v_i, R;
    end function;

    AddEntries := function(L, r, v0, qFirst, znum)
	/*
	# This inserts a new vector (0 ... 0 qFirst) at the front,
	# and for all remaining vectors, one entry is added.
	*/
	//[[0$nops(L[1]),qFirst],
	if znum gt 0 then
	    z := Matrix(Integers(), znum, Ncols(L) + 1, [0 : i in [1 .. Ncols(L)]] cat [qFirst]);
	end if;
	//seq([op(v),mods(add(v[i]*v0[i],i=1..r), qFirst)],v=L)]
	w := Matrix(Nrows(L), 1, [&+[L[j][i]*v0[i] : i in [1 .. r]] mod qFirst : j in [1 .. Nrows(L)]]);
	L := HorizontalJoin(L, w);
	if znum gt 0 then
	    L := VerticalJoin(z, L);
	end if;
	return L;
    end function;

    Formula1 := function(v, R, j, Step, r)
	//# subsop(-1 = a, v) replaces the last entry of v by a.
	nc := Ncols(v);
	for k in [1 .. Nrows(v)] do
	    //subsop(-1 = Step * v[-1] + add(v[i] * R[j,i], i=1..r), v)
	    v[k][nc] := Step * v[k][nc] + &+[v[k][i] * R[j,i] : i in [1..r]];
	end for;
	return v;
    end function;

    L := IdentityMatrix(Integers(), r);
//"A : ", A;
    for i in [1 .. N] do
	/*
	# The input was a list of vectors, but v_1, v_2, .. , v_r
	# but we treat only one entry of those vectors at a time, here
	# we take the i'th entry:
	*/
	w := ColumnSubmatrix(A, i, 1);
	if i lt N and IsAlreadyZero(L, w, q) then
	    //L := AddEntries(L, r, &cat[Eltseq(x) : x in Eltseq(w)], qFirst, 0);
//"CONTINUE";
	    continue;
	end if;

	R := [[] : ii in [1 .. numSt]];
	v0 := [];
	for j in [1 .. r] do
	    /*
	    # Compute v_{i,0} as well as the R_{i,j} mentioned in formula (1).
	    # Note: the "i" in (1) is denoted "j" here:
	    */
	    v0[j], R := CutV(w[j], q_0, Step, numSt, R, j);
	end for;
	/*
	# Now insert the v_{i,0} into the lattice. Those entries are determined 
	# mod qFirst
	# so we also add the vector (0 ... 0 qFirst).
	*/
	L := AddEntries(L, r, v0, qFirst, 1);
	L := LLL(L : Proof := false, InitialSort := false);
	L := ReduceLat(L, Br);

	for j in [1 .. numSt] do
	    //# Update the last entry of each vector using formula (1).
	    L := Formula1(L, R, j, Step, r);
	    //# Only call LLL if something became large.
	    if Maximum([#IntegerToString(L[ii][Ncols(L)]) : ii in [1 .. Nrows(L)]]) gt Br2 then
		/*
		# In the last step, if j = numSt-1, there is no rounding 
		# anymore,
		# so in that case use the original cut-off bound B. Otherwise 
		# use Br.
		*/
		L := LLL(L : Proof := false);
		L := ReduceLat(L, j eq numSt select B else Br);
	    end if;
	end for;
    end for;

    return L;
end intrinsic;

/*
GradualLLLmodq := proc(v::list, p::posint, a::posint, B::posint)
	local r,N,CONST1, CONST2,lStep,Step,numSt,q,i,q_0,qFirst,L,Br,Br2,w,j,v0,R,l,Ln;
	r := nops(v);
	N := nops(v[1]);
	CONST1 := 10;  # Experiment a bit with CONST1 and CONST2 to see what gives the best
	CONST2 := 2;   # CPU times (note: CONST1 dominates for small B, while CONST2 for large B).
	lStep := ceil(CONST1*r*log(2)/log(p)),  ceil( CONST2*(r*log(2) + log(B))/log(p) );
	lprint(lStep);
	lStep := max(lStep);
	Step := p^lStep;
	numSt := floor(a / lStep) - 1;
	q := p^a;
	if numSt <= 0 or _Env_Use_Standard_LLL = true then
		# Input entries are small, do a regular LLL-with-removals:
		return LLLInteger([
		 seq([0$(r+i-1),q,0$(N-i)], i = 1..N),  # vectors Q_1 .. Q_N
		 seq([0$(i-1),1,0$(r-i),op(v[i])], i=1..r) # vectors V_1 .. V_r
		], 'cut_away', B)
	fi;
	q_0 := Step^numSt;
	qFirst := p^(a - lStep*numSt);
	L := [seq([0$(i-1),1,0$(r-i)], i=1..r)]; # Standard basis (i.e. identity matrix)
	Br := ceil(B + B*r/4);  # Rounding increases the cut-off bound.
	Br2 := length( 2^r * Br );
	for i to N do
		# The input was a list of vectors, but v_1, v_2, .. , v_r
		# but we treat only one entry of those vectors at a time, here
		# we take the i'th entry:
		w := [seq(j[i],j=v)];

		if IsAlreadyZero(L, w, q) then
			lprint(cat("Entry #", convert(i,string)," is already zero"));
			next
		fi;
		for j to r do
			# Compute v_{i,0} as well as the R_{i,j} mentioned in formula (1).
			# Note: the "i" in (1) is denoted "j" here:
			v0[j] := CutV(w[j], q_0, Step, numSt, R, j)
		od;

		# Now insert the v_{i,0} into the lattice. Those entries are determined mod qFirst
		# so we also add the vector (0 ... 0 qFirst).
		L := AddEntries(L, r, v0, qFirst);
		lprint("LLLStart", time());
		L := LLLInteger(L, 'cut_away', Br);
		lprint("LLLStop", time());

		for j from 0 to numSt-1 do
			# Update the last entry of each vector using formula (1).
			L := [seq(Formula1(l, R, j, Step, r), l=L)];
			# Only call LLL if something became large.
			if max(seq(length(l[-1]),l=L)) > Br2 then
				lprint("LLLStart", time());
				# In the last step, if j = numSt-1, there is no rounding anymore,
				# so in that case use the original cut-off bound B. Otherwise use Br.
				L := LLLInteger(L, 'cut_away', `if`(j = numSt-1, B, Br) );
				lprint("LLLStop", time());
			else
				lprint("Last entry is small", time());
			fi
		od
	od;
	L
end:

Formula1 := proc(v, R, j, Step, r)
	local i;
	# subsop(-1 = a, v) replaces the last entry of v by a.
	subsop(-1 = Step * v[-1] + add(v[i] * R[j,i], i=1..r), v)
end:

AddEntries := proc(L, r, v0, qFirst)
	local v,i;
	# This inserts a new vector (0 ... 0 qFirst) at the front,
	# and for all remaining vectors, one entry is added.
	[[0$nops(L[1]),qFirst],
	seq([op(v),mods(add(v[i]*v0[i],i=1..r), qFirst)],v=L)]
end:

# Returns v_0 as output.  The R values are written in table R.
CutV := proc(v::integer, q_0, Step, numSt, R, j)
	local i, v_i, r, q;
	v_i := v;
	for i from numSt-1 to 0 by -1 do
		r := irem(v_i, Step, 'q');
		if 2*r > Step then
			r := r - Step;
			q := q+1
		fi;
		v_i := eval(q);
		R[i,j] := r
	od;
	v_i
end:

IsAlreadyZero := proc(L::list, v::list, q)
	local r,i,j;
	r := nops(v);
	for i from nops(L) to 1 by -1 do
		if add(L[i][j]*v[j],j=1..r) mod q <> 0 then
			return false
		fi
	od;
	true
end:
*/
