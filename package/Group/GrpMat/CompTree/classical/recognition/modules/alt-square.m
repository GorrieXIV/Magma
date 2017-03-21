freeze;

/* code to decompose symmetric power representation of Class(d, q); 
   Kay Magaard, Eamonn O'Brien, and Akos Seress; October 2008 

   Additions for non-SL cases added by Brian Corr and Eamonn O'Brien; July 2013
*/

import "basics.m": getExtensionDegree, ChooseSingerElt, fixSigns, IdentifyForm,
                   ScaleMatrix2, FindScalarMultipleOverSubfield;

/* find position of <i, j> in the list defs */
IndexPosition := function (defs, i, j)
	pair := i lt j select <i, j> else <j, i>;
	return Position (defs, pair);
end function;

//computation of B_{ijk} helper matrix. 
//if A11 is known, scales without taking a square root, otherwise choose sqrt 
Bijk := function (kap, i,j,k, defs, A11)
	ij := IndexPosition (defs, i, j);
	ik := IndexPosition (defs, i, k);
	jk := IndexPosition (defs, j, k);

	//first find C_ijk
	Cijk := ZeroMatrix (BaseRing (kap), 3, 3);
	Cijk[1][1] := kap[jk][jk];
	Cijk[1][2] := -kap[ik][jk];
	Cijk[1][3] := kap[ij][jk];
	Cijk[2][1] := -kap[jk][ik];
	Cijk[2][2] := kap[ik][ik];
	Cijk[2][3] := -kap[ij][ik];
	Cijk[3][1] := kap[jk][ij];
	Cijk[3][2] := -kap[ik][ij];
	Cijk[3][3] := kap[ij][ij];

	det := Determinant (Cijk);
	if det eq 0 then return false, _; end if;
	
	ScaledBijk := Cijk^(-1);

	if (A11 ne 0) then 
		if ScaledBijk[1][1] eq 0 then 
			return false, _;
		else	
			return true, ScaledBijk * A11 / ScaledBijk[1][1]; 
		end if;
	else	
		roots := AllRoots (det,2);
		if #roots eq 0 then 
                        return false, _;
		else
			det := roots[1];
			return true, ScaledBijk * det;		 	
		end if;
	end if;
end function;

/* is n = d (d + 1) / 2 or close enough? if so, return true and d*/
DetermineDegree := function (n)
	flag := exists (d){d : d in [1..n] | d * (d - 1)/2 eq n or d * (d - 1)/2 eq n + 1 or d * (d - 1)/2 eq n + 2};
	if flag then return true, d; else return false, _; end if;
end function;

/* label eigenvalues and find eigenspaces of s */
FindEigenspaces := function (s, ev, ones, G, TypeString)
	n := #Rows (s);
	q := #BaseRing (G);
	f, d := DetermineDegree (n);
	e := getExtensionDegree (d, TypeString);
	E := GF(q^e);

        // the indices of the orbits of length d (candidates for the orbit containing ell_11)
	index := [i : i in [1..#ev] | #ev[i] eq d]; 

	eigs := &join(ev);
        vprint SmallDegree: "Length of orbits ", [#o : o in ev];

        /* long orbit */
        for m in index do 
		orbit := ev[m];

                /* construct l_1 * l_2i for i <= n / 2 */
		l12 := orbit[1];
		l23 := orbit[2];
		l34 := orbit[3];
		assert l34 eq l12^(q^2);
		a := orbit[1]; assert a^(q^2) eq orbit[3];
		l14 := l12 * l34 / l23;

		if IsOdd (d) then 
			if d le 3 then 
				S := [l12];
			else 
				S := [l12, l14];
                                /* we now generate l_{1, 2k} using S_n S_n^(q^2) / S_{n - 1}^(q^2) */
				for k in [3..d div 2] do
					a := S[k - 1]; b := a^(q^2); c := S[k - 2]^(q^2);
					S[k] := a * b / c;
				end for;
			end if;
	       
			/* l_1 * l_2k where 2k + 1 = d */
			a := S[#S]; 
	                /* a^(q^2) = l_3 * l_1 */
			b := a^(q^2);
			/* now evaluate w^2 = (l_1 * l_3) / (l_1 l_2)^(q - 1) */
			w2 := b / S[1]^(q - 1);
			w := SquareRoot (w2);
			X := [];
			defs := [];
			onescount := 1;
			for i in [1..d] do
				for j in [i+1..d] do
					y := w^((q^(i-1)) + (q^(j-1)));
					if y eq 1 then 
						if (onescount le ones) then 
							onescount +:= 1;
							Append (~defs, <i,j>);
							Append (~X, 1);
						end if;
					else
						Append (~defs, <i,j>);
						Append (~X, y);
					end if;
				end for;
			end for;
			if Set (X) eq Set (eigs) then 
				vprint SmallDegree: m, "is good orbit"; 
				index := [Position (eigs, X[i]): i in [1..#X]]; break m; 
			end if;
		end if;

		if IsEven (d) then 
			/* a = l_1 l_2 * l_3 l_4  = (l_1 l_3)^(q + 1) */
			a := orbit[1] * orbit[3]; 
			if d eq 4 then short := 2; else short := d; end if;
			Other := [k : k in [1..#ev] | #ev[k] eq short and k ne m];
			if #Other eq 0 then return false, _, _, _; end if;
			for k in Other do 
				for x in ev[k] do
					if x^(q + 1) eq a then
						w2 := x / (orbit[1])^(q - 1);
						w := SquareRoot (w2);
						X := [];
						defs := [];
						onescount := 1;
						for i in [1..d-1] do
							for j in [i+1..d] do
								y := w^Floor((q^(i-1) + q^(j-1)));
								if y eq 1 then 
									if (onescount le ones) then 
										onescount +:= 1;
										Append (~defs, <i,j>);
										Append (~X, 1);
									end if;
								else
									Append (~defs, <i,j>);
									Append (~X, y);
								end if;
							end for;
						end for;

						if Set (X) eq Set (eigs) then 
							index := [Position (eigs, X[i]): i in [1..#X]]; 
							//m, k, "is good orbit"; 
							break m; 
						end if;
					end if;
				end for;
			end for;
		end if;
	end for;

	L := X;
	// need to find an eigenvector for each eigenvalue. 
        // most eigenspaces are 1-dimensional but the 1-eigenspace requires care.
	ES := [[]: i in [1..#L]];
	for j in [2..d] do
		ES[IndexPosition(defs,1,j)] := Eltseq (Eigenspace (s, L[IndexPosition(defs,1,j)]).1);
	end for;

	for i in [2..d-1] do
		for j in [i+1..d] do
			if (<i,j> in defs) then 
                           ES[IndexPosition(defs,i,j)] := [x^q: x in ES[IndexPosition(defs,i-1,j-1)]];     
                        end if;
		end for;
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
		CB := GL (n, E) ! &cat (ES);
		return true, CB, CB^(-1), defs;
	catch e; 
		return false, _,_,_;
	end try;
end function;
   
/* labels eigenvalues and finds eigenspaces of s in the case d'=d-1 */
FindEigenspacesSOOdd := function (s, ev, ones, G, TypeString)
	n := #Rows (s);
	q := #BaseRing (G);
	f, d := DetermineDegree (n);
	e := getExtensionDegree (d, TypeString);
	E := GF(q^e);

        // the indices of the orbits of length d (candidates for the orbit containing ell_11)
	index := [i : i in [1..#ev] | #ev[i] eq e]; 

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
	     		
	vprint SmallDegree: "Possible choices for basis are ", good;
        if #good eq 0 then return false, _,_,_; end if;

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
		for i in [1..d-1] do
			for j in [i+1..d] do
				val := X[i] * X[j];
				if (val eq 1) then 
					onescount +:= 1;
					if (onescount le ones) then 			
						Append (~L,1);
						Append (~defs, <i, j>);
					end if;
				else
					if exists (l) {l: l in list | val in eigs} then
						pos := Position (eigs, val);
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
	for j in [2..d] do
		ES[IndexPosition(defs,1,j)] := Eltseq (Eigenspace (s, L[IndexPosition(defs,1,j)]).1);
	end for;

	for i in [2..e-1] do
		for j in [i+1..e] do
			if (<i, j> in defs) then ES[IndexPosition(defs,i,j)] := [x^q: x in ES[IndexPosition(defs,i-1,j-1)]]; end if;
		end for;

		if (<i, d> in defs) then ES[IndexPosition(defs,i,d)] := [x^q: x in ES[IndexPosition(defs,i-1,d)]]; end if;
	end for;

	if (<e, d> in defs) then ES[IndexPosition(defs,e,d)] := [x^q: x in ES[IndexPosition(defs,e-1,d)]]; end if;
	onescount := 1;
	for i in [1..#L] do
		if (L[i] eq 1 and onescount le ones) then
			ES[i] := Eltseq (Eigenspace (s, L[i]).onescount);
			onescount := onescount+1;
		end if;
	end for;
	
	/* construct change-of-basis matrix */
	try
		CB := GL (n, E) ! &cat (ES);
		return true, CB, CB^(-1), defs;
	catch e
		return false, _,_,_;
	end try;
end function;

/* labels eigenvalues and finds eigenspaces of s in the case d'=d-2 */
FindEigenspacesSOPlus := function (s, ev, ones, G, TypeString)
	n := #Rows(s);
	q := #BaseRing (G);
	f, d := DetermineDegree (n);
	e := getExtensionDegree (d, TypeString);
	E := GF(q^e);
	
	eigs := &join(ev);
	index := [i : i in [1..#ev] | #ev[i] eq e]; // the indices of the orbits of length d 

	// test quotients of eigenvalues until we find m2/m1 = (Lim2)/(Lim1)...
	quotientsList := [[eig/ev[i][1]:  eig in eigs ] : i in [1..#ev]];
	enoughQuotients := [#[x^(q+1) ne 1: x in list | x^(q+1) eq 1] ge 2 : list in quotientsList];
	
	if not true in enoughQuotients then return false,_,_,_; end if;
	l1m1 := ev[Position (enoughQuotients, true)][1];
	enoughQuotients[Position (enoughQuotients, true)] := false;

	if not true in enoughQuotients then return false,_,_,_; end if;
	MyList := [x : x in ev[Position (enoughQuotients, true)] | (x/l1m1)^(q+1) eq 1];
	if #MyList eq 0 then return false, _, _, _; end if;
	l1m2 := MyList[1];	
	
	/* select ordering */
	onescount := 0;

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
	root := Sqrt (l1squared);
	for i in [1..e-1] do
		for j in [i+1..e] do
			val := root^(q^(i-1) + q^(j-1));
			if (val eq 1) then 
				onescount +:= 1;
                                // we `leave out' a 1-dimensional eigenspace since L(d-1)(d) is coming up
				if (onescount le ones-1) then 	
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
	Append (~L, 1);
	Append (~defs, <d-1, d>);
	
	// need to find an eigenvector for each eigenvalue. 
        // most eigenspaces are 1-dimensional but the 1-eigenspace requires care.
	ES := [[]: i in [1..#L]];
	for j in [2..d] do
		EigSpace := Eigenspace(s,L[IndexPosition (defs,1,j)]);
		if #EigSpace eq 1 then return false, _, _, _; end if;
		ES[IndexPosition(defs,1,j)] := Eltseq (EigSpace.1);
	end for;

	for i in [2..e-1] do
		for j in [i+1..e] do
			if (<i,j> in defs) then ES[IndexPosition(defs,i,j)] := [x^q: x in ES[IndexPosition(defs,i-1,j-1)] ]; end if;
		end for;

		if (<i,d> in defs) then ES[IndexPosition(defs,i,d)] := [x^q: x in ES[IndexPosition(defs,i-1,d-1)] ]; end if;
		if (<i,d-1> in defs) then ES[IndexPosition(defs,i,d-1)] := [x^q: x in ES[IndexPosition(defs,i-1,d)] ]; end if;
	end for;
	if (<e,d-1> in defs) then ES[IndexPosition(defs,e,d-1)] := [x^q: x in ES[IndexPosition(defs,e-1,d)] ]; end if;
	if (<e,d> in defs) then ES[IndexPosition(defs,e,d)] := [x^q: x in ES[IndexPosition(defs,e-1,d-1)] ]; end if;
	
	onescount := 1;
	for i in [1..#L] do
		if (L[i] eq 1 and onescount le ones) then
			ES[i] := Eltseq (Eigenspace (s, L[i]).onescount);
			onescount := onescount+1;
		end if;
	end for;

        // construct change-of-basis matrix 
	try 
		CB := GL (n, E) ! &cat (ES);
		return true, CB, CB^(-1), defs;
	catch e;
		return false,_,_,_;
	end try;
end function;

/* Find the constants Cij when all eigenvalues are distinct */
DetermineConstantsSL := function (G, CB, CBinv, defs, TypeString, NumberRandom)
	F := BaseRing (G);
	q := #F;

	n := Degree (G);
	flag, d := DetermineDegree (n);
	e := getExtensionDegree (d, TypeString);
	E := GF (q^e);
	M := MatrixAlgebra (E, n);

	/* choose random g to determine constants */
	for count in [1..NumberRandom] do
		g := Random (G);

                /* write wrt to the new basis */
		T := CB * M!g * CBinv;
		MA := MatrixAlgebra (E, d);
		A := Zero (MA);

		//initialise C and xexp, yexp (which track the unknowns x, y)
		C := Zero (MA);
		xexp := [[0: i in [1..d]]: j in [1..d]];
		yexp := [[0: i in [1..d]]: j in [1..d]];
	
		C[1][2] := 1;
		xexp[1][2] := 1;
		yexp[1][2] := 0;
		C[1][3] := 1;
		xexp[1][3] := 0;
		yexp[1][3] := 1;

		// find C1k for even k
		flag, B123 := Bijk (T, 1, 2, 3, defs, 0);
		if not flag then continue count; end if;

		for k in [4..e] do
			if (IsEven(k)) then 
				flag, B13k := Bijk (T, 1, 3, k, defs, B123[1][1]);
				if not flag then continue count; end if;
				if B13k[2][1] eq 0 then continue count; end if;
				C[1][k] := B123[3][1]/B13k[2][1]*C[1][k-2]^(q^2);
				if C[1][k] eq 0 then continue count; end if;
				xexp[1][k] := xexp[1][k-2]*q^2 + 1 - q;
				yexp[1][k] := yexp[1][k-2]*q^2;			
			end if;
		end for;

		//compute powerofy := y* := y^(q+1)
		flag, B124 := Bijk (T, 1, 2, 4, defs, B123[1][1]);
		if not flag then continue count; end if;
		flag, B134 := Bijk (T, 1, 3, 4, defs, B123[1][1]);
		if not flag then continue count; end if;

		if B134[2][1]*B123[2][1] eq 0 then continue count; end if;
		powerofy := B123[3][1]*B124[2][1]/(B134[2][1]*B123[2][1]);
		if powerofy eq 0 then continue count; end if;

		for k in [5..e] do
			if (IsOdd(k)) then
				flag, B12k := Bijk (T, 1, 2, k, defs, B123[1][1]);
				if not flag then continue count; end if;

				if B12k[2][1] eq 0 then continue count; end if;
				C[1][k] := (C[1][k-1]^q)*B123[2][1]/B12k[2][1];
				if C[1][k] eq 0 then continue count; end if;

				xexp[1][k] := q*xexp[1][k-1] - q;
				yexp[1][k] := q*yexp[1][k-1] + 1;
			end if;
		end for;

		//power up to find other values of Cij, and correct using y*
		for i in [2..e-1] do
			for j in [i+1..e] do
				C[i][j] := (C[i-1][j-1]^q);
				xexp[i][j] := q*xexp[i-1][j-1];
				yexp[i][j] := q*yexp[i-1][j-1];
				if yexp[i][j] eq q then 
					C[i][j] := C[i][j]*powerofy;
					yexp[i][j] := yexp[i][j] - (q+1);
					xexp[i][j] := xexp[i][j] + (q^2+1);
				end if;
				if yexp[i][j] eq -q then 
					C[i][j] := C[i][j]/powerofy;
					yexp[i][j] := yexp[i][j] + (q+1);
					xexp[i][j] := xexp[i][j] - (q^2+1);
				end if;
			end for;
		end for;

		return true, C, powerofy, xexp, yexp;
	end for;
	return false, _, _, _, _;
end function;

/* Find the constants Cij when all eigenvalues are not distinct */
DetermineConstantsNonSL := function (G, CB, CBinv, defs, TypeString, NumberRandom)
	F := BaseRing (G);
	q := #F;

	n := Degree (G);
	flag, d := DetermineDegree (n);
	e := getExtensionDegree (d, TypeString);
	E := GF (q^e);
	M := MatrixAlgebra (E, n);

        /* choose random g to determine constants */
	for count in [1..NumberRandom] do
		g := Random (G);

		/* write wrt to the new basis */
		T := CB * M!g * CBinv;
		MA := MatrixAlgebra (E, d);
		A := Zero (MA);

		// initialise C and xexp, yexp (which track the unknowns x, y)
		C := Zero (MA);
		xexp := [[0: i in [1..d]]: j in [1..d]];
		yexp := [[0: i in [1..d]]: j in [1..d]];
	
		C[1][2] := 1;
		xexp[1][2] := 1;
		yexp[1][2] := 0;
		C[1][3] := 1;
		xexp[1][3] := 0;
		yexp[1][3] := 1;

		//compute powerofy := y* := y^(q+1)
		flag, B123 := Bijk (T, 1, 2, 3, defs, 0);
		if not flag then continue count; end if;
		flag, B124 := Bijk (T, 1, 2, 4, defs, B123[1][1]);
		if not flag then continue count; end if;
		flag, B134 := Bijk (T, 1, 3, 4, defs, B123[1][1]);
		if not flag then continue count; end if;

		if B134[2][1]*B123[2][1] eq 0 then continue count; end if;
		powerofy := B123[3][1]*B124[2][1]/(B134[2][1]*B123[2][1]);

		// code must change if e/2 is even or odd...
		if IsEven (e div 2) then
			for k in [4..e] do
				if (IsEven(k)) then 
					flag, B13k := Bijk (T, 1, 3, k, defs, B123[1][1]);
					if not flag then continue count; end if;
					C[1][k] := B123[3][1]/B13k[2][1]*C[1][k-2]^(q^2);
					if C[1][k] eq 0 then continue count; end if;
					xexp[1][k] := xexp[1][k-2]*q^2 + 1-q;
					yexp[1][k] := yexp[1][k-2]*q^2;			
				end if;
			end for;

			//gap at C[1][e/2+1]
			for k in [5..e] do
				if (IsOdd(k) and k ne e/2+1) then
					flag, B12k := Bijk (T, 1, 2, k, defs, B123[1][1]);
					if not flag then continue count; end if;
					C[1][k] := (C[1][k-1]^q)*B123[2][1]/B12k[2][1];
					if C[1][k] eq 0 then continue count; end if;
					xexp[1][k] := q*xexp[1][k-1] - q;
					yexp[1][k] := q*yexp[1][k-1] + 1;
				end if;
			end for;
		else
			for k in [4..e/2-1] do
				if (IsEven(k)) then
					flag, B13k := Bijk (T, 1, 3, k, defs, B123[1][1]);
					if not flag then continue count; end if;
					C[1][k] := B123[3][1]/B13k[2][1]*C[1][k-2]^(q^2);
					if C[1][k] eq 0 then continue count; end if;
					xexp[1][k] := xexp[1][k-2]*q^2 + 1 - q;
					yexp[1][k] := yexp[1][k-2]*q^2;
				end if;
			end for;
		
			//gap at e/2+1 we must 'jump' over...
			k := Floor(e/2+3);
			flag, B145 := Bijk (T, 1, 4, 5, defs, B123[1][1]);
			if not flag then continue count; end if;
			flag, B15k := Bijk (T, 1, 5, k, defs, B123[1][1]);
			if not flag then continue count; end if;
	
			if B15k[2][1] eq 0 then continue count; end if;
			C[1][k] := B145[3][1]/B15k[2][1] * C[1][k-4]^(q^4) * C[1][4];
			if C[1][k] eq 0 then continue count; end if;
			xexp[1][k] := xexp[1][k-4]*q^4 + xexp[1][4] - q^3;
			yexp[1][k] := yexp[1][k-4]*q^4 + yexp[1][4];

			//now find the remaining even k

			for k in [e/2+5..e] do
				if (IsEven(k)) then
					flag, B13k := Bijk (T, 1, 3, k, defs, B123[1][1]);
					if not flag then continue count; end if;
	
					if B13k[2][1] eq 0 then continue count; end if;
					C[1][k] := B123[3][1]/B13k[2][1]*C[1][k-2]^(q^2);
					if C[1][k] eq 0 then continue count; end if;
					xexp[1][k] := xexp[1][k-2]*q^2 + 1 - q;
					yexp[1][k] := yexp[1][k-2]*q^2;
				end if;
			end for;
		

			//odd k: don't have access to C[1][e/2+1] so we have to come back for C[1][e/2+2]...
			for k in [5..e] do
				if (IsOdd(k) and k ne e/2+2) then
					flag, B12k := Bijk (T, 1, 2, k, defs, B123[1][1]);
					if not flag then continue count; end if;
					if B12k[2][1] eq 0 then continue count; end if;
					C[1][k] := (C[1][k-1]^q)*B123[2][1]/B12k[2][1];
					if C[1][k] eq 0 then continue count; end if;
					xexp[1][k] := q*xexp[1][k-1] - q;
					yexp[1][k] := q*yexp[1][k-1] + 1;
				end if;
			end for;

			//last entry 
			k := Floor(e/2+2);
			flag, B15k := Bijk (T, 1, 5, k, defs, B123[1][1]);
			if not flag then continue count; end if;
	
			if B15k[2][1] eq 0 then continue count; end if;
			C[1][k] := B145[3][1]/B15k[2][1] * C[1][k-4]^(q^4) * C[1][4];
			if C[1][k] eq 0 then continue count; end if;
			xexp[1][k] := xexp[1][k-4]*q^4 + xexp[1][4]-q^3;
			yexp[1][k] := yexp[1][k-4]*q^4 + yexp[1][4];
		
			C[1][k] := C[1][k]*(powerofy)^(q^3-q^2+q-1);
			if C[1][k] eq 0 then continue count; end if;
			yexp[1][k] := yexp[1][k] - (q+1)*(q^3-q^2+q-1);
			xexp[1][k] := xexp[1][k] + (q^2+1)*(q^3-q^2+q-1);
		end if;

		//power up to find other values of Cij, and correct using y*
		for i in [2..e-1] do
			for j in [i+1..e] do
				C[i][j] := (C[i-1][j-1]^q);
				xexp[i][j] := q*xexp[i-1][j-1];
				yexp[i][j] := q*yexp[i-1][j-1];
				if yexp[i][j] eq q then 
					C[i][j] := C[i][j]*powerofy;
					yexp[i][j] := yexp[i][j] - (q+1);
					xexp[i][j] := xexp[i][j] + (q^2+1);
				end if;
				if yexp[i][j] eq -q then 
					C[i][j] := C[i][j]/powerofy;
					yexp[i][j] := yexp[i][j] + (q+1);
					xexp[i][j] := xexp[i][j] - (q^2+1);
				end if;
			end for;
		end for;
		return true, C, powerofy, xexp, yexp;
	end for;
	return false, _, _, _, _;
end function;

/* given matrix g in alternating square repn of GL(d, q),
   reconstruct it as d x d matrix over GF(q^d') */
ReconstructSL := function (G, g, C, xexp, yexp, CB, CBinv, defs, powerofy, TypeString)
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
	x := [[0: i in [1..d]]: j in [1..d]];
	y := [[0: i in [1..d]]: j in [1..d]];

	//few initial values
	flag, B123 := Bijk (T, 1, 2, 3, defs, 0);
	if (flag eq false) then return false, _,_,_; end if;
	A[1][1] := B123[1][1];
	A[2][2] := B123[2][2];
	A[3][3] := B123[3][3];
	A[1][2] := B123[1][2]*C[2][3]/C[1][3];
	x[1][2] := q;
	y[1][2] := -1;

	A[2][1] := B123[2][1]*C[1][3]/C[2][3];
	x[2][1] := -q;
	y[2][1] := 1;

	if A[1][1] eq 0 then return false,_,_,_; end if;
	//first row and column of A
	for j in [3..e] do
		flag, B12j := Bijk (T, 1, 2, j, defs, B123[1][1]);
		if (flag eq false) then return false, _,_,_; end if;
		A[1][j] := B12j[1][3] * C[2][j]/C[1][2];
		x[1][j] := xexp[2][j] - xexp[1][2];
		y[1][j] := yexp[2][j] - yexp[1][2];

		A[j][1] := B12j[3][1] * C[1][2]/C[2][j];
		x[j][1] := xexp[1][2] - xexp[2][j];
		y[j][1] := yexp[1][2] - yexp[2][j];
	end for;

	//power up and keep track
	for i in [2..e] do
		for j in [2..e] do
			A[i][j] := A[i-1][j-1]^q;
			x[i][j] := x[i-1][j-1]*q;
			y[i][j] := y[i-1][j-1]*q;

			if y[i][j] eq q then 
				A[i][j] := A[i][j]*powerofy;
				y[i][j] := y[i][j] - (q+1);
				x[i][j] := x[i][j] + (q^2+1);
			end if;

			if y[i][j] eq -q then 
				A[i][j] := A[i][j]/powerofy;
				y[i][j] := y[i][j] + (q+1);
				x[i][j] := x[i][j] - (q^2+1);
			end if;
		end for;
	end for;

	//compute last row and column in the unitary case for even d
	if (e le d-1) then
		for t in [e+1..d] do 
			flag, B12d := Bijk (T, 1, 2, t, defs, B123[1][1]);
			if (flag eq false) then return false, _,_,_; end if;
			A[2][t] := B12d[2][3]/C[1][2];
			x[2][t] := -xexp[1][2];
			y[2][t] := -yexp[1][2];

			A[t][2] := B12d[3][2]*C[1][2];
			x[t][2] := xexp[1][2];
			y[t][2] := yexp[1][2];

			A[t][t] := B12d[3][3];

			if (A[2][1] eq 0) then return false, _,_,_; end if;
			if (A[1][2] eq 0) then return false, _,_,_; end if;

			A[1][t] := (A[1][1]*A[2][t] - T[IndexPosition(defs,1,2)][IndexPosition(defs,1,t)])/A[2][1];
			x[1][t] := x[1][1]+ x[2][t] - x[2][1];
			y[1][t] := y[1][1]+ y[2][t] - y[2][1];

			A[t][1] := (A[1][1]*A[t][2] - T[IndexPosition(defs,1,t)][IndexPosition(defs,1,2)])/A[1][2];
			x[t][1] := x[1][1]+ x[t][2] - x[1][2];
			y[t][1] := y[1][1]+ y[t][2] - y[1][2];

			for i in [2..e] do
				if (A[i-1][1] eq 0) then return false, _,_,_; end if;
				A[i][t] := 1/A[i-1][1] * (A[i-1][t]*A[i][1] + T[IndexPosition(defs,i-1,i)][IndexPosition(defs,1,t)])/C[i-1][i];
				x[i][t] := -xexp[i-1][i] -x[i-1][1];
				y[i][t] := -yexp[i-1][i] -y[i-1][1];

				if (A[1][i-1] eq 0) then return false, _,_,_; end if;
				A[t][i] := 1/A[1][i-1] * (A[t][i-1]*A[1][i] + T[IndexPosition(defs,1,t)][IndexPosition(defs,i-1,i)])*C[i-1][i];
				x[t][i] := xexp[i][i-1] -x[1][i-1];
				y[t][i] := yexp[i][i-1] -y[1][i-1];
			end for;
		end for;
	end if;
	return true, A, x, y;
end function;

//reconstruct, and if a division by zero is attempted, work around
TryReconstructSL := function (G, g, C, xexp, yexp, CB, CBinv, defs, powerofy, TypeString, trials, tryWithoutRandomElt)

	if tryWithoutRandomElt then
		flag, A, x, y := ReconstructSL (G, g, C, xexp, yexp, CB, CBinv, defs, powerofy, TypeString);
		if flag then flag := Determinant(A) ne 0; end if;
		if flag then return true, A; end if;
	end if;

	for i in [1..trials] do
		h := Random(G);
		flag1, A1, x1, y1 := ReconstructSL (G, g*h^(-1), C, xexp, yexp, CB, CBinv, defs, powerofy, TypeString);
		if (flag1 eq false) then continue; end if;
		flag2, A2, x2, y2 := ReconstructSL (G, h, C, xexp, yexp, CB, CBinv, defs, powerofy, TypeString);
		if (flag2 eq false) then continue; end if;
		if (Determinant (g) ne 0 and Determinant (A1) * Determinant (A2) eq 0) then continue; end if;
		return true, A1*A2;
	end for;
	return false,_;
end function;

// Reconstruct in the harder cases
ReconstructNonSL := function (G, g, C, xexp, yexp, CB, CBinv, defs, powerofy, TypeString)
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
	x := [[0: i in [1..d]]: j in [1..d]];
	y := [[0: i in [1..d]]: j in [1..d]];

	//few initial values
	flag, B123 := Bijk (T, 1, 2, 3, defs, 0);
	if (flag eq false) then return false, _,_,_; end if;

	A[1][1] := B123[1][1];
	A[2][2] := B123[2][2];
	A[3][3] := B123[3][3];
	A[1][2] := B123[1][2]*C[2][3]/C[1][3];
	x[1][2] := q;
	y[1][2] := -1;

	A[2][1] := B123[2][1]*C[1][3]/C[2][3];
	x[2][1] := -q;
	y[2][1] := 1;

	if A[1][1] eq 0 then return false, _,_,_; end if;

	//first row and column of A
	for j in [3..e] do
		if not j in [e/2+1, e/2+2] then
			flag, B12j := Bijk (T, 1, 2, j, defs, B123[1][1]);
			if (flag eq false) then return false, _,_,_; end if;

			A[1][j] := B12j[1][3]*C[2][j]/C[1][2];
			x[1][j] := xexp[2][j] - xexp[1][2];
			y[1][j] := yexp[2][j] - yexp[1][2];

			A[j][1] := B12j[3][1]*C[1][2]/C[2][j];
			x[j][1] := xexp[1][2] - xexp[2][j];
			y[j][1] := yexp[1][2] - yexp[2][j];
		end if;
	end for;

	//power up and keep track
	for i in [2..e] do
		for j in [2..e] do
			A[i][j] := A[i-1][j-1]^q;
			x[i][j] := x[i-1][j-1]*q;
			y[i][j] := y[i-1][j-1]*q;

			if y[i][j] eq q then 
				A[i][j] := A[i][j] * powerofy;
				y[i][j] := y[i][j] - (q+1);
				x[i][j] := x[i][j] + (q^2+1);
			end if;

			if y[i][j] eq -q then 
				A[i][j] := A[i][j] / powerofy;
				y[i][j] := y[i][j] + (q+1);
				x[i][j] := x[i][j] - (q^2+1);
			end if;
		end for;
	end for;

	//still missing some rows/columns...
	for j in [Floor(e/2+1), Floor(e/2+2)] do
		if (A[3][3] eq 0) then return false, _,_,_; end if;

		A[1][j] := 1/A[3][3] * (A[1][3] * A[3][j] - C[3][j]/C[1][3]*T[IndexPosition(defs,1,3)][IndexPosition(defs,3,j)]);
		x[1][j] := x[1][3]+x[3][j]-x[3][3];
		y[1][j] := y[1][3]+y[3][j]-y[3][3];

		A[j][1] := 1/A[3][3] * (A[3][1] * A[j][3] - C[1][3]/C[3][j]*T[IndexPosition(defs,3,j)][IndexPosition(defs,1,3)]);
		x[j][1] := x[3][1]+x[j][3]-x[3][3];
		y[j][1] := y[3][1]+y[j][3]-y[3][3];
	end for;

	for i in [2..(e div 2)] do
		for j in [e div 2+i, e div 2+i+1] do
			if j le d then
				A[i][j] := A[i-1][j-1]^q;
				x[i][j] := x[i-1][j-1]*q;
				y[i][j] := y[i-1][j-1]*q;

				if y[i][j] eq q then 
					A[i][j] := A[i][j] * powerofy;
					y[i][j] := y[i][j] - (q+1);
					x[i][j] := x[i][j] + (q^2+1);
				end if;

				if y[i][j] eq -q then 
					A[i][j] := A[i][j] / powerofy;
					y[i][j] := y[i][j] + (q+1);
					x[i][j] := x[i][j] - (q^2+1);
				end if;
			end if;
		end for;
	end for;

	for j in [2..(e div 2)] do
		for i in [e div 2+j, e div 2+j+1] do
			if i le e then
				A[i][j] := A[i-1][j-1]^q;
				x[i][j] := x[i-1][j-1]*q;
				y[i][j] := y[i-1][j-1]*q;

				if y[i][j] eq q then 
					A[i][j] := A[i][j] * powerofy;
					y[i][j] := y[i][j] - (q+1);
					x[i][j] := x[i][j] + (q^2+1);
				end if;

				if y[i][j] eq -q then 
					A[i][j] := A[i][j] / powerofy;
					y[i][j] := y[i][j] + (q+1);
					x[i][j] := x[i][j] - (q^2+1);
				end if;
			end if;
		end for;
	end for;

	if (e le d-1) then
		for t in [e+1..d] do 
			flag, B12d := Bijk (T, 1, 2, t, defs, B123[1][1]);
			if (flag eq false) then return false, _,_,_; end if;

			A[2][t] := B12d[2][3]/C[1][2];
			x[2][t] := -xexp[1][2];
			y[2][t] := -yexp[1][2];

			A[t][2] := B12d[3][2]*C[1][2];
			x[t][2] := xexp[1][2];
			y[t][2] := yexp[1][2];

			A[t][t] := B12d[3][3];

			if (A[2][1] eq 0 or A[1][2] eq 0) then return false, _,_,_; end if;
			A[1][t] := (A[1][1]*A[2][t] - T[IndexPosition (defs,1,2)][IndexPosition (defs,1,t)])/A[2][1];
			x[1][t] := x[1][1]+ x[2][t] - x[2][1];
			y[1][t] := y[1][1]+ y[2][t] - y[2][1];

			A[t][1] := (A[1][1]*A[t][2] - T[IndexPosition (defs,1,t)][IndexPosition (defs,1,2)])/A[1][2];
			x[t][1] := x[1][1]+ x[t][2] - x[1][2];
			y[t][1] := y[1][1]+ y[t][2] - y[1][2];

			for i in [2..e] do			
				if (A[i-1][1] eq 0 or A[1][i-1] eq 0) then return  false, _,_,_; end if;

				A[i][t] := 1/A[i-1][1] * (A[i-1][t]*A[i][1] + T[IndexPosition (defs,i-1,i)][IndexPosition(defs,1,t)])/C[i-1][i];
				x[i][t] := -xexp[i-1][i] -x[i-1][1];
				y[i][t] := -yexp[i-1][i] -y[i-1][1];
				A[t][i] := 1/A[1][i-1] * (A[t][i-1]*A[1][i] + T[IndexPosition (defs,1,t)][IndexPosition(defs,i-1,i)])*C[i-1][i];
				x[t][i] := xexp[i][i-1] -x[1][i-1];
				y[t][i] := yexp[i][i-1] -y[1][i-1];
			end for;
		end for;
		if (e eq d-2) then 			
			if (A[2][1] eq 0 or A[1][2] eq 0) then return false, _,_,_; end if;
			A[d-1][d] := (T[IndexPosition (defs,1,d-1)][IndexPosition (defs,1,d)]+A[1][d] * A[d-1][1])/A[1][1];
			x[d-1][d] := x[1][d]+x[d-1][1] - x[1][1];
			y[d-1][d] := y[1][d]+y[d-1][1] - y[1][1];

			A[d][d-1] := (T[IndexPosition (defs,1,d)][IndexPosition (defs,1,d-1)]+A[1][d-1] * A[d][1])/A[1][1];
			x[d][d-1] := x[1][d-1]+x[d][1] - x[1][1];
			y[d][d-1] := y[1][d-1]+y[d][1] - y[1][1];
		end if;
	end if;

	return true, A, x, y;
end function;

//reconstruct, and if a division by zero is attempted, work around
TryReconstructNonSL := function (G, g, C, xexp, yexp, CB, CBinv, defs, powerofy, TypeString, trials, tryWithoutRandomElt)
	if tryWithoutRandomElt then
		flag, A, x, y := ReconstructNonSL (G, g, C, xexp, yexp, CB, CBinv, defs, powerofy, TypeString);
		if flag then return true, A; end if;
	end if;
	for i in [1..trials] do
		h := Random(G);
		flag1, A1, x1, y1 := ReconstructNonSL (G, g*h^(-1), C, xexp, yexp, CB, CBinv, defs, powerofy, TypeString);
		if (flag1 eq false) then continue; end if;
		flag2, A2, x2, y2 := ReconstructNonSL (G, h, C, xexp, yexp, CB, CBinv, defs, powerofy, TypeString);
		if flag2 eq false then continue; end if;

		return true, A1*A2;
	end for;
	return false, _;
end function;

// Recognise G in the alternating square Case
RecogniseAlternatingSquare := function (GG, TypeString, q: NumberRandom := 100)
	if not TypeString in ["A", "2A", "B", "C", "D", "2D"] then
		vprint SmallDegree: "TypeString must be one of A, 2A, B, C, D, 2D."; 
		return false, _;
	end if;

	vprint SmallDegree: "Trying to recognise G as the alternating square";

        G := GG;
	n := Degree (G);
	flag, d := DetermineDegree (n);
	e := getExtensionDegree (d, TypeString);
	if flag eq false then 
		vprint SmallDegree: "Representation is not alternating square"; 
		return false, _;
	end if;

	if (#BaseRing(G) ne q) then
		if (#BaseRing(G) lt q) then 
                        G := sub<GL(n,q) | [G.i : i in [1..Ngens(G)]]>; 
		else 
			flag, K := IsOverSmallerField (G);
			if flag 
			   then G := K;
			else
			    vprint SmallDegree:
				   "Recognition for Alternating-square failed: "
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
			"Could not find a special element: Representation is probably not alternating square of" , TypeString;
			return false, _;
		else
			vprint SmallDegree : "Special element found.";
		end if;

		if (TypeString eq "B" or (TypeString eq "2A" and IsEven(d))) then
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

		if (TypeString eq "A" or TypeString eq "2A") then
			found, C, powerofy, xexp, yexp := DetermineConstantsSL (G, CB, CBinv, defs, TypeString, NumberRandom);
			if found eq false then
				vprint SmallDegree: 
				"Could not find the constants Cij: Representation is probably not alternating square of type" , TypeString;
				return false, _;
			else 
				vprint SmallDegree: "Constants Cij have been computed.";
			end if;
	
			X := [];
			for i in [1..Ngens(G)] do
				flag, MyGen := TryReconstructSL (G, G.i, C, xexp, yexp, CB, CBinv, defs, powerofy, TypeString, NumberRandom, true);
			
				if (Determinant(MyGen) eq 0) then continue count; end if;
				Append (~X, MyGen);
			end for;
		else
			found, C, powerofy, xexp, yexp := DetermineConstantsNonSL (G, CB, CBinv, defs, TypeString, 100);
			if found eq false then
				vprint SmallDegree: 
				"Could not find the constants Cij: Representation is probably not alternating square of type" , TypeString;
				return false, _;
			else 
				vprint SmallDegree: "Constants Cij have been computed.";
			end if;
			X := [];
			for i in [1..Ngens(G)] do
				flag, MyGen := TryReconstructNonSL (G, G.i, C, xexp, yexp, CB, CBinv, defs, powerofy, TypeString, NumberRandom, true);
			
				if (Determinant(MyGen) eq 0) then continue count; end if;
				Append (~X, MyGen);
			end for;
			vprint SmallDegree: "Preimages of generators have been computed.";
		end if;	
	
		//fix problems with minus signs in the generators.
                vprint SmallDegree: "Fixing minus signs...";
		H := sub <GL(d, q^e) | X >;
		flag, H := fixSigns (H, G);
		if not flag then continue; end if;

                vprint SmallDegree: "Rewriting over the original field...";
		flag, A := IsOverSmallerField (H);
		if not flag then continue; end if;

		break;
	end for;

	if counter ge NumberRandom or not flag then return false, _; end if;

	vprint SmallDegree: "Change-of-basis matrix has been computed.";

	//find and store a form defining our group (for testing preimage)
        found, form := IdentifyForm (A, TypeString);

        if TypeString ne "A" and not found then
           vprint SmallDegree:
            "Construction of preimage failed. Input group is probably not alternating square representation of ", TypeString;
           return false, _;
        end if;

	SCB := H`SmallerFieldChangeOfBasis;
	GG`SmallDegree := <"AltSquare", CB, CBinv, defs, C, xexp, yexp, powerofy, SCB, SCB^(-1), TypeString, form, q, A>;
	return true, A;
end function;

/* Preimage of g in the alternating case */
AlternatingSquarePreimage := function(G, g, limit: NumberRandom := 100) 
	vprint SmallDegree: "Computing preimage (alternating square case)";
	R := G`SmallDegree; 
	CB := R[2]; CBinv := R[3]; defs := R[4]; C := R[5]; xexp := R[6]; yexp := R[7]; 
	powerofy := R[8]; SCB := R[9]; SCBinv := R[10]; TypeString := R[11]; form := R[12]; A := R[14];

	for count in [1..limit] do
		flag := false;
		if (TypeString eq "A" or TypeString eq "2A") then
			flag, h := TryReconstructSL (G, g, C, xexp, yexp, CB, CBinv, defs, powerofy, TypeString, NumberRandom, count eq 1);
		else
			flag, h := TryReconstructNonSL (G, g, C, xexp, yexp, CB, CBinv, defs, powerofy, TypeString, NumberRandom, count eq 1);
		end if;

		if not flag then return false, _; end if;
		if Determinant (h) eq 0 then continue count; end if;

		// write the matrix over the subfield
		im := SCBinv*h*SCB;
		im := ScaleMatrix2 (im);
		if im cmpeq false then continue count; end if;

		im := FindScalarMultipleOverSubfield (im, BaseRing (G));
		if im cmpeq false then continue count; end if;

		im := GL(#Rows(im), BaseRing(im))!im;

		if TypeString eq "A" then 
                        return true, im;
		elif TypeString eq "2A" then 	
			F := BaseRing(G); deg := Degree (F) div 2;
			if form cmpeq false or IsScalar (form^(-1) * im * form * Transpose (FrobeniusImage (im, deg))) then return true, im; end if;
		elif TypeString in ["B", "D", "2D", "C"] and (form cmpeq false or IsScalar (form^(-1) * im * form * Transpose(im)))  then   
                        return true, im;
		end if;
		break;
	end for;
	vprint SmallDegree: "Construction of preimage failed."; 
	return false, _;
end function;
