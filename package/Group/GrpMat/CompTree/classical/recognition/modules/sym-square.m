freeze;

/* code to decompose symmetric power representation of Class(d, q); 
   Kay Magaard, Eamonn O'Brien, and Akos Seress; October 2008 
   
   Additions for non-SL cases added by Brian Corr and Eamonn O'Brien; July 2013
*/

import "basics.m": getExtensionDegree, ChooseSingerElt, ScaleMatrix2, ScaleMatrices, 
    FindScalarMultipleOverSubfield, fixSigns, IdentifyForm;

/* find position of <i, j> in the list defs */
IndexPosition := function (defs, i, j)
	pair := i lt j select <i, j> else <j, i>;
	return Position (defs, pair);
end function;

/* return the value of formula (viii) (equal to (c_ij / c_jk)*a_ik*a_ii) */
viii := function (T, i, j, k, defs)
	ii := IndexPosition (defs,i,i);
	ij := IndexPosition (defs,i,j);
	jj := IndexPosition (defs,j,j);
	jk := IndexPosition (defs,j,k);
	if T[jj][jj]*T[ii][jj]*T[ii][ij]*T[ij][jj] eq 0 then return false; end if;
	return T[ii][ij]*T[ij][jj] / (2* T[jj][jj]*T[ii][jj]) * (T[ij][jk] - T[ij][jj]*T[jj][jk]/(2*T[jj][jj]));
end function;

/* is n = d (d + 1) / 2 or close enough? */
DetermineDegree := function (n)
	flag := exists (d){d : d in [1..n] | d * (d + 1)/2 eq n or d * (d + 1)/2 eq n + 1 or d * (d + 1)/2 eq n + 2};
	if flag then return true, d; else return false, _; end if;
end function;

/* labels eigenvalues and finds eigenspaces of s */
FindEigenspaces := function (s, ev, ones, G, TypeString)
	n := #Rows (s);
	q := #BaseRing (G);
	f, d := DetermineDegree (n);
	e := getExtensionDegree (d, TypeString);
	E := GF(q^e);
        // the indices of the orbits of length d (candidates for the orbit containing ell_11)
	index := [i : i in [1..#ev] | #ev[i] eq d]; 

        /* possible orderings of basis vectors using the rule "ell_11 * ell_jj = ell_1j^2" */
	good := []; 
	for k in index do 
		X := ev[k]; 
		list := [j : j in [1..#ev] | j ne k]; 
		for i in [1..#X] do 
			for j in [i + 1..#X] do 
				val := X[i] * X[j];
				if not IsSquare (val) then break k; end if;
				root := Sqrt (val);
				if not exists {l: l in list | -root in ev[l] or root in ev[l]} then 
					continue k;
				end if;
			end for;
		end for;
		Append (~good, k);
	end for;
	
	vprint SmallDegree: "Possible choices for basis are ", good;
	if #good eq 0 then return false, _,_,_; end if;
	
	/* select ordering */
	for m in [1..#good] do 
		onescount := 0;
		k := good[m];
		list := [j : j in [1..#ev] | j ne k];
		X := ev[k];
		e := X[1];

		eigs := &join(ev);
		X := [e^(q^i): i in [0..d - 1]];
		L := X;

		defs := [<i, i> : i in [1..d]]; 
		for i in [1..d] do
			for j in [i + 1..d] do
				val := X[i] * X[j];
				if (val eq 1) then 
					onescount +:= 1;
					if (onescount le ones) then 
						Append (~L,1);
						Append (~defs, <i, j>);
					end if;
				else
					root := Sqrt(val);
					if exists (l) {l: l in list | root in eigs} then
						pos := Position (eigs, root);
					elif exists (l) {l: l in list | -root in eigs} then
						pos := Position (eigs, -root);
					else 
						vprint SmallDegree: "Problem for ordering ", m, i ,j;
						break m;
					end if;
					Append (~L, eigs[pos]);
					Append (~defs, <i, j>);
				end if;
			end for;
		end for;
	end for;

	// need to find an eigenvector for each eigenvalue. 
        // most eigenspaces are 1-dimensional but the 1-eigenspace requires care.
	ES := [[]: i in [1..#L]];
	for j in [1..d] do
		ES[IndexPosition (defs,1,j)] := Eltseq (Eigenspace (s, L[IndexPosition (defs,1,j)]).1);
	end for;

	e := getExtensionDegree (d, TypeString);
	for i in [2..e] do
		for j in [i..e] do
			if (<i,j> in defs) then 
                           ES[IndexPosition (defs,i,j)] := [x^q: x in ES[IndexPosition (defs,i-1,j-1)]]; 
                        end if;
		end for;
	end for;

	try
		onescount := 1;
		for i in [1..#L] do
			if (L[i] eq 1 and onescount le ones) then
				ES[i] := Eltseq (Eigenspace (s, L[i]).onescount);
				onescount := onescount+1;
			end if;
		end for;
	
		/* construct change-of-basis matrix */
		CB := MatrixAlgebra(E,n) ! &cat (ES);
		if IsInvertible (CB) eq false then return false, _,_,_; end if;
		return true, CB, CB^(-1), defs;
	catch e;
		return false, _,_,_;
	end try;
end function;

/* label eigenvalues and find eigenspaces of s in the case d'=d-1 */
FindEigenspacesSOOdd := function (s, ev, ones, G, TypeString)
	n := #Rows (s);
	q := #BaseRing (G);
	f,d := DetermineDegree (n);
	e := getExtensionDegree (d, TypeString);
	E := GF(q^e);
	index := [i : i in [1..#ev] | #ev[i] eq e]; 
        // the indices of the orbits of length d (candidates for the orbit containing ell_11)

	/* one of the orbits contains L1. Using LiLj=Lij we identify it */
	good := []; 
	for k in index do 
		X := ev[k]; 
		list := [j : j in [1..#ev] | j ne k]; 
		for i in [1..#X] do 
			for j in [i + 1..#X] do 
				val := X[i] * X[j];
				if not exists {l: l in list | -val in ev[l] or val in ev[l]} then 
					continue k;
				end if;
			end for;
		end for;
		Append (~good, k);
	end for;
	     		
	if #good eq 0 then return false, _,_,_; end if;
	vprint SmallDegree: "Possible choices for basis are ", good;
	
	/* select ordering */
	for m in [1..#good] do 
		onescount := 0;
		k := good[m];
		list := [j : j in [1..#ev] | j ne k];
		X := ev[k];
		eig := X[1];

		eigs := &join(ev);
		X := [eig^(q^i): i in [0..e - 1]];
		Append (~X,1);
		L := [];
		defs := [];
		for i in [1..d] do
			for j in [i..d] do
				val := X[i] * X[j];
				if (val eq 1) then 
					onescount +:= 1;
					if (onescount le ones) then
						Append (~L, 1);
						Append (~defs, <i, j>);
					end if;
				else
					if exists (l) {l: l in list | val in eigs} then
						pos := Position (eigs, val);
					else 
						vprint SmallDegree: "Problem in ordering ", m, i, j;
						break m;
					end if;
					Append (~L, eigs[pos]);
					Append (~defs, <i, j>);
				end if;
			end for;
		end for;
	end for;

	// need to find an eigenvector for each eigenvalue. 
        // most eigenspaces are 1-dimensional but the 1-eigenspace requires care.
	ES := [[]: i in [1..#L]];
	for j in [1..d] do
		ES[IndexPosition (defs,1,j)] := Eltseq(Eigenspace (s, L[IndexPosition (defs,1,j)]).1);
	end for;

	for i in [2..e] do
		for j in [i..e] do
			if (<i, j> in defs) then 
                            ES[IndexPosition (defs,i,j)] := [x^q: x in ES[IndexPosition (defs,i-1,j-1)]]; 
                        end if;
		end for;
		if (<i,d> in defs) then 
                    ES[IndexPosition (defs,i,d)] := [x^q: x in ES[IndexPosition (defs,i-1,d)]];  
                end if;
	end for;

	onescount := 1;
	try
		for i in [1..#L] do
			if (L[i] eq 1 and onescount le ones) then
				ES[i] := Eltseq (Eigenspace (s, L[i]).onescount);
				onescount := onescount+1;
			end if;
		end for;

                /* construct change-of-basis matrix */
		CB := MatrixAlgebra(E,n) ! &cat (ES);
		if IsInvertible (CB) eq false then return false, _,_,_; end if;
		return true, CB, CB^(-1), defs;
	catch e;
		return false,_,_,_;
	end try;
end function;

/* label eigenvalues and find eigenspaces of s in the case d'=d-2 */
FindEigenspacesSOPlus := function (s, ev, ones, G, TypeString);
	n := #Rows(s);
	q := #BaseRing(G);
	f, d := DetermineDegree (n);
	e := getExtensionDegree (d, TypeString);
	E := GF(q^e);
	
	eigs := &join(ev);
	index := [i: i in [1..#ev] | #ev[i] eq e]; // the indices of the orbits of length d 
	
	// choose m1^2 from the orbit of length 2
	m1squared := [orb[1] : orb in ev | #orb eq 2 ][1];
	//compute m2/m1 as a power of m1^2
	m2overm1 := m1squared^((q-1) div 2);
	
	// identify l1m1 and l1m2
	candidates := [ev[i][1]: i in index | ev[i][1]*m2overm1 in eigs];
	if (#candidates ge 1) then 
		l1m1 := candidates[1];
		l1m2 := l1m1*m2overm1;
	else
		candidates := [ev[i][1]: i in index | ev[i][1]/m2overm1 in eigs];
		if #candidates eq 0 then return false, _,_,_; end if;
		l1m1 := candidates[1];
		l1m2 := l1m1/m2overm1;
	end if;

	/* select ordering */
	onescount := 1;

	L := [];
	defs := [];

	//power up to compute LiMj
	for i in [1..e] do
		Append (~L, l1m1^(q^(i-1)));
		Append (~defs, <i, d - (i mod 2)>);
		Append (~L, l1m2^(q^(i-1)));
		Append (~defs, <i, d - 1 + (i mod 2)>);
	end for;

	//compute L1^2 and get Lij from this
	l1squared := l1m1*l1m2;
	for i in [1..e] do
		for j in [i..e] do
			val := l1squared^((q^(i-1) + q^(j-1)) div 2);
			if (val eq 1) then 
				onescount +:= 1;
				if (onescount le ones) then 			
					Append (~L, 1);
					Append (~defs, <i, j>);
				end if;
			else
				Append (~L, val);
				Append (~defs, <i, j>);
			end if;
		end for;
	end for;

	//last couple of values
	Append (~L, m1squared);
	Append (~defs, <d-1, d-1>);

	Append (~L, m1squared^q);
	Append (~defs, <d, d>);

	Append (~L, 1);
	Append (~defs, <d-1, d>);

	// need to find an eigenvector for each eigenvalue. 
        // most eigenspaces are 1-dimensional but the 1-eigenspace requires care.
	ES := [[]: i in [1..#L]];
	for j in [1..d] do
		space := Eigenspace(s,L[IndexPosition (defs,1,j)]);
		if #space eq 1 then return false, _,_,_; end if;
		ES[IndexPosition (defs,1,j)] := Eltseq(space.1);
	end for;

	for i in [2..e] do
		for j in [i..e] do
			if (<i,j> in defs) then ES[IndexPosition (defs,i,j)] := [x^q: x in ES[IndexPosition (defs,i-1,j-1)] ]; end if;
		end for;
		if (<i,d> in defs) then ES[IndexPosition (defs,i,d)] := [x^q: x in ES[IndexPosition (defs,i-1,d-1)] ]; end if;
		if (<i,d-1> in defs) then ES[IndexPosition (defs,i,d-1)] := [x^q: x in ES[IndexPosition (defs,i-1,d)] ]; end if;
	end for;

	if (<d-1,d-1> in defs) then ES[IndexPosition (defs,d-1,d-1)] := Eltseq(Eigenspace (s, m1squared).1); end if;
	if (<d,d> in defs) then ES[IndexPosition (defs,d,d)] := [x^q: x in ES[IndexPosition (defs,d-1,d-1)] ]; end if;	
	
	onescount := 1;
	try
		for i in [1..#L] do
			if (L[i] eq 1 and onescount le ones) then
				ES[i] := Eltseq (Eigenspace (s, L[i]).onescount);
				onescount := onescount+1;
			end if;
		end for;

	        /* construct change-of-basis matrix */
		CB := MatrixAlgebra(E,n) ! &cat (ES);
		if IsInvertible(CB) eq false then return false, _,_,_; end if;
		return true, CB, CB^(-1), defs;
	catch e;
		return false, _,_,_;
	end try;
end function;

// Find Cij when all eigenvalues are distinct
DetermineConstantsSL := function (G, CB, CBinv, defs, TypeString, NumberRandom)
	F := BaseRing (G);
	q := #F;

	n := Degree (G);
	flag, d := DetermineDegree (n);
	e := getExtensionDegree (d, TypeString);
	E := GF (q^e);
	M := MatrixAlgebra (E, n);

	for count in [1..NumberRandom] do
		g := Random (G);

		/* write wrt to the new basis */
		T := CB * M!g * CBinv;
		MA := MatrixAlgebra (E, d);
		A := Zero (MA);

		C := Identity (MA);

		/* compute c1ell for odd ell  */ 
		i := 1;
		for j in [2..((e+1) div 2)] do
			ii := IndexPosition (defs,i,i);
			ij := IndexPosition (defs,i,j);
			jj := IndexPosition (defs,j,j);
			ell := 2*j-1;
			int := viii (T, i, j, ell, defs);

			if int cmpeq false then continue count; end if;

			if T[jj][jj]*T[ii][jj]*T[ij][jj] eq 0 then continue count; end if;
			int := int * ((T[ij][jj]^2) / (4*T[jj][jj]*T[ii][jj]))^((q^(j - 1) - 1) div 2);
		
			iell := IndexPosition (defs,i,ell);

			if T[ii][iell] eq 0 then continue count; end if;
			int := int / T[ii][iell];

			if int eq 0 then continue count; end if;
			C[1][ell] := int;
		end for;

		/* compute c_12 as a square root. Ignore sign ambiguity */
		i := 1;
		j := 2;
		ii := IndexPosition (defs,i,i);
		ij := IndexPosition (defs,i,j);
		jj := IndexPosition (defs,j,j);
		if T[jj][jj]*T[ii][jj]*T[ij][jj] eq 0 then continue count; end if;
		int := T[ij][jj]^2 / (4*T[jj][jj]*T[ii][jj]);
		if not IsSquare (int) then continue count; end if;
		C[1][2] := Sqrt (int);

		/* compute c_1ell for even ell */
		for ell in [2*t : t in [1..Floor(e/2)]] do
			iell := IndexPosition (defs,i,ell);
			int := viii (T, i, j, ell, defs);
			if int cmpeq false then continue count; end if;

			int := int * (C[1][ell-1])^q / C[1][2];
			if T[ii][iell] eq 0 then continue count; end if;
			int := int / T[ii][iell];

			if int eq 0 then continue count; end if;
			
			C[1][ell] := int;
		end for;

		/* power up to find the other cij */	
		for i in [2..e] do
			for j in [2..e] do
				C[i][j] := C[(i - 1)][(j - 1)]^q;
			end for;
		end for;
		return true, C;
	end for;
	return false, _;
end function;

// Finds the constants Cij in cases with eigenvalues 1
DetermineConstantsNonSL := function (G, CB, CBinv, defs, TypeString, NumberRandom)
	F := BaseRing (G);
	q := #F;

	n := Degree (G);
	flag, d := DetermineDegree (n);
	e := getExtensionDegree (d, TypeString);
	E := GF (q^e);
	M := MatrixAlgebra (E, n);

	for count in [1..NumberRandom] do
		/* choose random g to determine constants */
		g := Random (G);

		/* write wrt to the new basis */
		T := CB * M!g * CBinv;
		MA := MatrixAlgebra (E, d);
		A := Zero (MA);

		C := Identity (MA);

		/* compute c1ell for odd ell except the forbidden value ell=e/2+1 */ 
		i := 1;
		for j in [2..(e+1) div 2] do
			ii := IndexPosition (defs,i,i);
			ij := IndexPosition (defs,i,j);
			jj := IndexPosition (defs,j,j);
			ell := 2*j-1;
			int := viii (T, i, j, ell, defs);
			if int cmpeq false then continue count; end if;

			if T[jj][jj]*T[ii][jj] eq 0 then continue count; end if;
			int := int * ((T[ij][jj]^2) / (4*T[jj][jj]*T[ii][jj]))^((q^(j - 1) - 1) div 2);
		
			iell := IndexPosition (defs,i,ell);
			if T[ii][iell] eq 0 then continue count; end if;
			int := int / T[ii][iell];
			if (ell ne e/2+1) then
			    C[1][ell] := int;
			end if;
		end for;

		/* compute c_12 as a square root. ignore sign ambiguity */
		i := 1;
		j := 2;
		ii := IndexPosition (defs, i, i);
		ij := IndexPosition (defs, i, j);
		jj := IndexPosition (defs, j, j);

		if T[jj][jj]*T[ii][jj] eq 0 then continue count; end if;
		int := T[ij][jj]^2 / (4*T[jj][jj]*T[ii][jj]);
		if (not IsSquare (int)) then continue count; end if;
		C[1][2] := Sqrt (int);

		/* compute c_1ell for even ell (except the forbidden value) */
		for ell in [2*t : t in [1..e div 2]] do
			iell := IndexPosition (defs,i,ell);
			int := viii (T, i, j, ell, defs);
			if int cmpeq false then continue count; end if;

			int := int * (C[1][ell-1])^q / C[1][2];

			if T[ii][iell] eq 0 then continue count; end if;
			int := int / T[ii][iell];
			if (ell ne e/2+1 and ell ne e/2+2) then C[1][ell] := int; end if;		
		end for;

                /* if e/2 is even, we missed a spot */
		if IsEven (e div 2) then
			k := e div 2+2;
			ik := IndexPosition (defs, i, k);
			int := viii (T, 1, 3, k, defs);
			if int cmpeq false then continue count; end if;

			int := int * (C[1][k - 2])^(q^2) / C[1][3];
			if T[ii][ik] eq 0 then continue count; end if;
			int := int / T[ii][ik];
			C[1][k] := int;
		end if;

		/* power up to find the other cij */
		for i in [2..e] do
		     for j in [2..e] do
				C[i][j] := C[(i-1)][(j-1)]^q;
			end for;
		end for;
		return true, C;
	end for;
	return false, _;
end function;

/* given matrix g in symmetric square repn of GL(d, q),
   reconstruct it as d x d matrix over GF(q^d') */

Reconstruct := function (G, g, C, CB, CBinv, defs, TypeString)
	F := BaseRing (G);
	q := #F;

	n := Degree (G);
	flag, d := DetermineDegree (n);
	e := getExtensionDegree (d, TypeString);
	E := GF (q^e);
	M := MatrixAlgebra (E, n);

        /* write wrt to the new basis */
	T := CB * M!g * CBinv;

	MA := MatrixAlgebra (E, d);
	A := Zero (MA);

	/* choose sign A(1, 1) */
	roots := AllRoots (T[IndexPosition (defs,1,1)][IndexPosition (defs,1,1)],2);
	if #roots eq 0 then return false, _; end if;
	A[1][1] := roots[1];
	if A[1][1] eq 0 then return false, _; end if;
	rootm1 := roots[1]^-1;

	// Deal with linear case 
	if (TypeString eq "A") then
	    //first row and column
	    for j in [2..e] do
	       if C[1][j] eq 0 then return false, _; end if;
	       A[1][j] := T[IndexPosition (defs,1,1)][IndexPosition (defs,1,j)] * C[1][j]/(C[1][1] * A[1][1]);
	       A[j][1] := T[IndexPosition (defs,1,j)][IndexPosition (defs,1,1)] * C[1][1]/(C[1][j] *2* A[1][1]);
	    end for;
	
	    /* fill in the rest of A */
	    for i in [2..e] do
	       for j in [i..e] do
    		  A[i][j] := 1/A[1][1] * (C[1][j]/C[1][i] * T[IndexPosition (defs,1,i)][IndexPosition (defs,1,j)] - A[1][j]*A[i][1]);
    		  A[j][i] := 1/A[1][1] * (C[1][i]/C[1][j] * T[IndexPosition (defs,1,j)][IndexPosition (defs,1,i)] - A[1][i]*A[j][1]);
	       end for;
            end for;
            return true, A;
	end if;

	//non SL cases
        // find the first row and column of A except for certain 'hard' values
	for j in [2..e] do
	   if j ne e/2+1 then
	      if C[1][j] eq 0 then return false, _; end if;
	      A[1][j] := T[IndexPosition (defs,1,1)][IndexPosition (defs,1,j)] * C[1][j]/(C[1][1] * A[1][1]);
	      A[j][1] := T[IndexPosition (defs,1,j)][IndexPosition (defs,1,1)] * C[1][1]/(C[1][j] *2* A[1][1]);
	   end if;
	end for;
	
	/* fill in 'most' of A */
	for i in [2..e] do
	   for j in [i..e] do
	      if (j ne e/2 + 1 and i ne e/2+1) then
                 A[i][j] := 1/A[1][1] * (C[1][j]/C[1][i] * T[IndexPosition (defs,1,i)][IndexPosition (defs,1,j)] - A[1][j]*A[i][1]);
    		 A[j][i] := 1/A[1][1] * (C[1][i]/C[1][j] * T[IndexPosition (defs,1,j)][IndexPosition (defs,1,i)] - A[1][i]*A[j][1]);
              end if;
	   end for;
	end for;
	if (A[2][2] eq 0) then return false, _; end if;

	/* fill in the last parts */
	k := e div 2+1;
	A[2][k] := C[2][k] / C[2][2]* T[IndexPosition (defs,2,2)][IndexPosition (defs,2,k)]/A[2][2];
	A[k][2] := C[2][2] / C[2][k]* T[IndexPosition (defs,2,k)][IndexPosition (defs,2,2)]/(2*A[2][2]); 

	for i in [3..e] do
	   if (i ne e div 2+2) then 
	      A[i][k] := 1/A[2][2] * (C[2][k]/C[2][i] * T[IndexPosition (defs,2,i)][IndexPosition (defs,2,k)] - A[2][k] * A[i][2]);
	      A[k][i] := 1/A[2][2] * (C[2][i]/C[2][k] * T[IndexPosition (defs,2,k)][IndexPosition (defs,2,i)] - A[2][i] * A[k][2]);
	   end if;
	end for;

	A[1][k] := 1/A[2][2] * (C[1][k-1]^q / C[1][2] * T[IndexPosition (defs,1,2)][IndexPosition (defs,2,k)] - A[1][2]*A[2][k]);
	A[k][1] := 1/A[2][2] * (C[1][2] / C[1][k-1]^q * T[IndexPosition (defs,2,k)][IndexPosition (defs,1,2)] - A[2][1]*A[k][2]);

	if A[k][2] eq 0 then return false, _; end if;
	A[k][k] := C[2][k] / C[k][k] * T[IndexPosition (defs,k,k)][IndexPosition (defs,2,k)]/A[k][2];

	if A[k][k] eq 0 then return false, _; end if;
	A[k][k+1] := C[k][k+1] / C[k][k] * T[IndexPosition (defs,k,k)][IndexPosition (defs,k,k+1)]/A[k][k];
	A[k+1][k] := C[k][k] / C[k][k+1] * T[IndexPosition (defs,k,k+1)][IndexPosition (defs,k,k)]/(2*A[k][k]);
	
	if (e eq d-1) then
	   for i in [1..e] do
	      if (A[i][1] eq 0) then return false, _; end if;
	      if (A[1][i] eq 0) then return false, _; end if;
	      A[i][d] := T[IndexPosition (defs,i,i)][IndexPosition (defs,1,d)]/(C[i][i] * A[i][1]);
              A[d][i] := T[IndexPosition (defs,1,d)][IndexPosition (defs,i,i)]*C[i][i] /(2* A[1][i]);
	   end for;
           A[d][d] := 1/A[1][1] * (T[IndexPosition (defs,1,d)][IndexPosition (defs,1,d)] - A[1][d]*A[d][1]);
	elif (e eq d-2) then
	   for i in [1..e] do
	      if (A[i][1] eq 0) then return false, _; end if;
	      if (A[1][i] eq 0) then return false, _; end if;
	      for t in [d-1,d] do
		 A[i][t] := T[IndexPosition (defs,i,i)][IndexPosition (defs,1,t)]/(C[i][i] * A[i][1]);
		 A[t][i] := T[IndexPosition (defs,1,t)][IndexPosition (defs,i,i)]*C[i][i] /(2* A[1][i]);
	      end for;
           end for;
           A[d][d] := 1/A[1][1] * (T[IndexPosition (defs,1,d)][IndexPosition (defs,1,d)] - A[1][d]*A[d][1]);
	   A[d-1][d-1] := 1/A[1][1] * (T[IndexPosition (defs,1,d-1)][IndexPosition (defs,1,d-1)] - A[1][d-1]*A[d-1][1]);
           A[d-1][d] := 1/A[1][1] * (T[IndexPosition (defs,1,d-1)][IndexPosition (defs,1,d)] - A[1][d]*A[d-1][1]);
	   A[d][d-1] := 1/A[1][1] * (T[IndexPosition (defs,1,d)][IndexPosition (defs,1,d-1)] - A[1][d-1]*A[d][1]);
	end if;

	return true, A;
end function;

/* Run the Reconstruct function: if it fails, try again with a random element to 'go around' */
TryReconstruct := function  (G, g, C, CB, CBinv, defs, TypeString, trials, tryWithoutRandomElt)
	if tryWithoutRandomElt then
		flag, A := Reconstruct (G, g, C, CB, CBinv, defs, TypeString);
		if flag then return true, A; end if;
	end if;

	for i in [1..trials] do
		h := Random (G);
		flag1, A1 := Reconstruct (G, g*h^(-1), C, CB, CBinv, defs, TypeString);
		if flag1 eq false then continue; end if;
		flag2, A2 := Reconstruct (G, h, C, CB, CBinv, defs, TypeString);
		if flag2 eq false then continue; end if;
		return true, A1*A2;
	end for;
	return false, _;
end function;

// Recognise G in the symmetric square case
RecogniseSymmetricSquare := function (GG, TypeString, q: NumberRandom := 100)
	vprint SmallDegree: "Trying to recognise G in the symmetric square case";

        G := GG;
	n := Degree (G);
	flag, d := DetermineDegree (n);
	e := getExtensionDegree (d, TypeString);
	if flag eq false then 
		vprint SmallDegree: "Representation is not symmetric square"; 
		return false, _;
	end if;

	if (#BaseRing(G) ne q) then
		if (#BaseRing(G) lt q) then 
                        G := sub<GL(n, q) | [G.i : i in [1..Ngens(G)]]>; 
		else 
			flag, K := IsOverSmallerField (G);
			if flag then 
                            G := K;
			else	
			    vprint SmallDegree: 
				   "Recognition for Symmetric-square failed: "
				   cat "This is not the right field size.";
			    return false, _;
			end if;
		end if;
	end if;

	for count in [1..NumberRandom] do
                counter := count;
                vprint SmallDegree: "\nSelect special element ", counter;
		found, s, ev, ones := ChooseSingerElt (G, TypeString, d);
		if found eq false then
			vprint SmallDegree: 
			"Could not find a special element: Representation is probably not symmetric square of" , TypeString;
			return false, _;
		else
			vprint SmallDegree: "Special element found.";
		end if;

		if (TypeString eq "B" or (TypeString eq "2A" and IsEven (d))) then
			found, CB, CBinv, defs := FindEigenspacesSOOdd (s, ev, ones, G, TypeString);
		elif (TypeString eq "D") then 
			found, CB, CBinv, defs := FindEigenspacesSOPlus (s, ev, ones, G, TypeString);
		else 
			found, CB, CBinv, defs := FindEigenspaces (s, ev, ones, G, TypeString);
		end if;

		if found eq false then
			continue count;
		else 
			vprint SmallDegree: "Eigenspaces have been computed.";
		end if;

		// find the constants Cij	
		if (TypeString in ["A", "2A"]) then 
			found, C := DetermineConstantsSL (G, CB, CBinv, defs, TypeString, NumberRandom);
		else
			found, C := DetermineConstantsNonSL (G, CB, CBinv, defs, TypeString, NumberRandom);
		end if;
	
		if found eq false then
			vprint SmallDegree: 
			"Could not find the constants Cij: Representation is probably not symmetric square of" , TypeString;
			return false, _;
		else 
			vprint SmallDegree: "Constants Cij have been computed.";
		end if;

                X := [];
                for i in [1..Ngens(G)] do
		     flag, MyGen := TryReconstruct (G, G.i, C, CB, CBinv, defs, TypeString, NumberRandom, true);
		     if not flag then 	
			 vprint SmallDegree: "Could not find preimages of generators"; 
			return false, _;
                     end if;
                     Append (~X, MyGen);
                end for;
          	vprint SmallDegree: "Preimages of generators have been computed.";

		H := sub<GL(d, q^e) | X>;

		// fix problems with minus signs in the generators.
		flag, H := fixSigns (H, G);
		if not flag then continue; end if;

		flag, A := IsOverSmallerField (H);
		if flag then break; end if;
	end for;
    
        vprint SmallDegree: "Number of random elements selected is ", counter;
        if counter ge NumberRandom or not flag then return false, _; end if;
	
	vprint SmallDegree: "Change-of-basis matrix has been computed.";

	//find and store a form defining our group (for testing preimage)
        found, form := IdentifyForm (A, TypeString);

        if TypeString ne "A" and not found then
           vprint SmallDegree:
            "Construction of preimage failed. Input group is probably not symmetric square representation of ", TypeString;
           return false, _;
        end if;

	
	SCB := H`SmallerFieldChangeOfBasis;
	GG`SmallDegree := <"SymSquare", CB, CBinv, defs, C, SCB, SCB^(-1), TypeString, form, q, A>;
	return true, A;
end function;

// Find the preimage of g in the symmetric square case
SymmetricSquarePreimage := function(G, g, limit: NumberRandom := 100)
	vprint SmallDegree: "Computing preimage (symmetric square case)";
	R := G`SmallDegree; 
	CB := R[2]; CBinv := R[3]; defs := R[4]; C := R[5]; SCB := R[6];
        SCBinv := R[7]; TypeString := R[8]; form := R[9]; A := R[11];

	for count in [1..limit] do
		flag, h := TryReconstruct (G, g, C, CB, CBinv, defs, TypeString, NumberRandom, count eq 1);

		if not flag then return false, _; end if;
		if Determinant (h) eq 0 then continue count; end if;

		// write the matrix over the subfield		
		im := SCBinv*(GL(Degree(SCB), BaseRing(SCB))!h)*SCB;

		im := FindScalarMultipleOverSubfield (im, BaseRing(G));
		if (im cmpeq false) then continue count; end if;
		im := ScaleMatrix2 (im);
		if (im cmpeq false) then continue count; end if;

		im := GL(#Rows(im), BaseRing(im))!im;

		if TypeString eq "A" then 
                   return true, im;
		elif TypeString eq "2A" then 	 
		   F := BaseRing (G); deg := Degree (F) div 2;
		   if form cmpeq false or (IsScalar (form^(-1) * im * form * Transpose (FrobeniusImage (im, deg)))) then 
                      return true, im;
                   end if;		
		elif TypeString in ["B", "D", "2D", "C"] and (form cmpeq false or IsScalar (form^(-1) * im * form * Transpose(im))) then 
                   return true, im;
		end if;
		break;
	end for;
        vprint SmallDegree: "Construction of preimage failed.";
	return false, _;
end function;
