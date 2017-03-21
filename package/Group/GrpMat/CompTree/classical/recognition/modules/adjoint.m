freeze;

/* code to decompose adjoint representation of H where SL(d, q) <= H <= GL(d, q);
   Kay Magaard, Eamonn O'Brien, and Akos Seress;
   this July 2009 version corrects errors in the algorithm described in our paper 

   Addition for unitary groups in even dimension: 
   added July 2013 by Brian Corr and Eamonn O'Brien
*/

import "basics.m": getExtensionDegree, ChooseSingerElt, IdentifyForm,
       ScaleMatrix, FindScalarMultipleOverSubfield, fixSigns, FixForm;

forward TryReconstruct;

DetermineDegree := function (n)
	flag, d := IsSquare (n + 1);
	if not flag then 
		flag, d := IsSquare (n + 2); 
		def := 2;
	else 
		def := 1;
	end if;
	if not flag then 
		return false, _, _; 
	else 
		return true, d, def; 
	end if;
end function;

FindIndex := function (i, j, d)
	if (j le i) then 
		return (i - 1) * (d - 1) + j;
	else 
		return (i - 1) * (d - 1) + (j - 1);
	end if;
end function;

FindEigenspacesSL := function (s, ev, ones, G, TypeString) 

	flag, d, def := DetermineDegree (Degree (G));

	n := Degree (G);
	F := BaseRing (G);
	q := #F;
	p := Characteristic (F);
	E := BaseRing(s);
	MA := MatrixAlgebra (E, n); 
   
        /* diagonalise s */
	EV := &join(ev);

	MA := MatrixAlgebra (E, d);

	CBs := [];

	for o in [1..#ev] do 
		L := Zero (MA);
		first := ev[o];
		if #first eq 1 then continue o; end if;

		//guess that L12 is in the orbit o. Label the whole orbit
		for i in [1..d - 1] do
			L[i][i+1] := first[i];
		end for;
		L[d][1] := first[d];

		//label L1,k+1 := L1k Lk,k+1 = L1/Lk*Lk/Lk+1
		for k in [2..d - 1] do
			v := L[1][k] * L[1][2]^(q^(k - 1));
			if v in EV and not (v in first) then 
				L[1][k + 1] := v;
				for j in [2..d - k] do
					L[j][j + k] := L[j - 1][j + k - 1]^q;
				end for;
				L[d + 1 - k][1] := L[d - k][d]^q;
				for j in [d + 2 - k..d] do
					L[j][j -(d - k)] := L[j - 1][j - (d - k) - 1]^q;
				end for;
			else 
				continue o;
			end if;
		end for;

		// check that everything worked and construct the change of basis matrix CB and its inverse.
		fine := true;
		try
			MA := MatrixAlgebra (E, n); 
			l := Eltseq (L);
			l := [x : x in l | x ne 1 and x ne 0];

			OneEigenspace := Eigenspace (s, 1);
			ES := [Eigenspace (s, e).1: e in l] cat 
			      [OneEigenspace.i : i in [1..ones]];

			CB := GL(n, E) ! &cat ([Eltseq (x): x in ES]);
		catch e;
			fine := false;
		end try;
		if (not fine) then continue o; end if;

		return true, CB, CB^(-1);

	end for;
	return false, _,_,_;
end function;

FindEigenspacesSUEven := function (s, ev, ones, G, TypeString) 
	flag, d, def := DetermineDegree (Degree (G));
	n := Degree (G);
	F := BaseRing (G);
	q := #F;
	p := Characteristic (F);
	E := BaseRing(s);
	MA := MatrixAlgebra (E, n); 
   	dprime := d-1;
	EV := &join(ev);
	MA := MatrixAlgebra (E, d);

	// candidates for the orbits Lid, Ldi
	MyOrbs := [x: x in ev | #x ge 2  and x[1]/x[2] in EV and x[1]/x[3] in EV and x[1]/x[3] in EV];

	for o in MyOrbs do
		l1 := o[1];

		L := Identity (MA);
		L[1][d] := l1;
		L[d][1] := 1/l1;

		if not L[d][1] in EV then continue o; end if;

		// guess that L1d=L1 is in the orbit o. Label the whole orbit
		for i in [2..d - 1] do
			L[i][d] := L[i-1][d]^q;
			L[d][i] := L[d][i-1]^q;
		end for;

		for i in [1..dprime] do
			for j in [1..dprime] do
				val := L[i][d]*L[d][j];
				if (not val in EV) then continue o; end if;
				L[i][j] := val;
			end for;
		end for;

		fine := true;
		try
			MA := MatrixAlgebra (E, n); 
			l := Eltseq (L);
			l := [x : x in l | x ne 1];

			OneEigenspace := Eigenspace (s, 1);

			ES := [Eigenspace (s, e).1: e in l] cat 
			      [OneEigenspace.i : i in [1..ones]];
			CB := MA ! &cat ([Eltseq (x): x in ES]);	
		catch e;
			fine := false;
		end try;
		if (not fine) then continue o; end if;
		return true, CB, CB^(-1);
	end for;

	vprint SmallDegree: "Tried everything.";
	return false, _,_,_;
end function;

/* construct the matrix of constants C */
DetermineConstants := function (G, CB, CBinv, TypeString, s: Hard := true)
	flag, d, def := DetermineDegree (Degree (G));
	dprime := getExtensionDegree (d, TypeString);
	P := Parent (CB);
	E := BaseRing (P);
	n := Degree (G);

	F := BaseRing (G);
	q := #F;

	M := MatrixAlgebra (E, n);
	repeat
	    vprint SmallDegree: "Choosing a random element and writing in the new basis...";
	    h := Random (G);
	    K := CB * M!h * CBinv;
	until K[d + 1][d + 1] * K[2][2] ne 0 and 
           forall{j: j in [4..d] | K[FindIndex (1, j - 1, d)][FindIndex (1, j, d)] ne 0};

	A11A22 := K[FindIndex(1,3,d)][FindIndex(1,3,d)]/K[FindIndex(2,3,d)][FindIndex(2,3,d)];

	MA := MatrixAlgebra (E, d);
	w := PrimitiveElement(E);

	//compute order of s and a random conjugate for testing later
	Ord := Order (s);
	sss := M ! Eltseq (s);
	sss := GL(n, q^dprime) ! sss;
	sss := sss^(GL(n, q^dprime) ! Random(G));
        sss := GL(n, q) ! sss;

	// determine by brute-force the values of C12, C13 
        // in reality we can assume C12=1 so kk will never reach 1
        MaxNumber := q - 1;
        // FieldSizeLimit := 2^8;
        // if (Hard eq false and q gt FieldSizeLimit) then MaxNumber := FieldSizeLimit; else MaxNumber := q - 1; end if;
	// for kk in [0..q-1] do
	for kk in [0] do
           for kkk in [0..MaxNumber] do
		vprint SmallDegree: "Trying with C_12 = w^", kk, "C_13 = w^", kkk;
		C := Zero (MA);
            	// if d ge 3 then C[1][3] := 1; end if;
		C[1][2] := w^kk;
		C[1][3] := w^kkk;
		for j in [4..dprime] do 
                   C[1][j] := (C[1][j-1])^(q+1)* A11A22 * 
                       K[FindIndex (2,j-1,d)][FindIndex (2,j,d)]/((C[1][j-2])^q * K[FindIndex (1,j-1,d)][FindIndex (1,j,d)]);
		end for;
                for j in [2..dprime] do
		    for k in [1..dprime] do
		       if k eq 1 then 
			  C[j][k] := C[j- 1][dprime]^q;
		       else 
			  C[j][k] := C[j- 1][k - 1]^q; 
		       end if;
		    end for;
		end for;

		//case SU even dimension.
		if (TypeString eq "2A" and IsEven(d)) then
			a22a33st := K[FindIndex (1,2,d)][FindIndex (1,2,d)]/K[FindIndex (1,3,d)][FindIndex (1,3,d)];
			mypower := (K[FindIndex (d,3,d)][FindIndex (1,3,d)]/K[FindIndex (d,2,d)][FindIndex (1,2,d)]) * (a22a33st);
			mypower := mypower * C[1][3]/C[1][2];

			// CASE 2A for even d: we have computed C_d2^(q-1). 
			// if what we compute is a q-1st power, then find the root. if not, try again.
			if mypower^(((q^dprime -1) div (q-1))) ne 1 then continue kkk; end if;

			vprint SmallDegree: "Looking for (q-1)-th root...";
			root := Root (mypower, q-1);
			C[d][2] := root;
			C[d][1] := C[d][2]^(q^(dprime-1));
	        end if;

         	//test the array C. first test that the preimage of a random conjugate of s has the correct order.
                f2, ss := TryReconstruct (G, sss, C, CB, CBinv, TypeString, 10, true);
                if (not IsScalar (ss^Ord)) then continue kkk; end if;

         	// confirm correctness with a trial of random elements. this should only run once.
		g := Random (G);
		f1, a := TryReconstruct(G, g, C, CB, CBinv, TypeString, 10, true);
		if not f1 then continue kkk; end if;

		f2, c := TryReconstruct(G, h, C, CB, CBinv, TypeString, 10, true);
		if not f2 then continue kk; end if;
		f3, u := TryReconstruct(G, g * h, C, CB, CBinv, TypeString, 10, true);
		if not f3 then continue kk; end if;

		if (f1 and f2 and f3) and Determinant (u) ne 0 and IsScalar (a*c*u^(-1)) then 
                   return true, C;
      		end if;
           end for;
	end for;

	vprint SmallDegree: "No choice worked in ChooseConstants";
	return false, _;
end function;

Reconstruct := function (G, g, C, CB, CBinv, TypeString)
	flag, d, def := DetermineDegree (Degree (G));
   
	F := BaseRing (G);
	n := Degree (G);

	P := Parent (CB);
	K := CB * (P ! g) * CBinv;

	E := BaseRing (P);
	M := MatrixAlgebra (E, d);
	A := Zero (M);

	MA := MatrixAlgebra (E, d);

	a := FindIndex (3, 1, d); b := FindIndex (3, 2, d);
	if d ge 4 then 
		ell := FindIndex (4, 1, d); m := FindIndex (4, 2, d); 
	end if;
	if K[b][b] * K[a][a] ne 0 then
		A11A22st := K[a][a]/ K[b][b];
	elif d ge 4 and K[m][m] * K[ell][ell] ne 0 then 
		A11A22st := K[ell][ell] / K[m][m];
	else 
		return false, _;
	end if;

	i := FindIndex (2, 3, d); 
	if d ge 4 then j := FindIndex (4, 3, d); end if;
	if K[i][i] ne 0 then
		ell := FindIndex (2, 1, d);
		A11A33st := K[ell][ell]/ K[i][i];
	elif d ge 4 and K[j][j] ne 0 then
		m := FindIndex (4, 1, d);
		A11A33st := K[m][m]/ K[j][j];
	else 
		return false, _;
	end if;

	for i in [2..d] do
		for j in [2..d] do
			A[i][j] := K[FindIndex (i,1,d)][FindIndex (j,1,d)]*C[j][1]/C[i][1];
		end for;
	end for;

	for j in [1] cat [3..d] do
		A[1][j] := K[FindIndex (1,2,d)][FindIndex (j,2,d)]*C[j][2]*A11A22st/C[1][2];
		A[j][1] := K[FindIndex (j,2,d)][FindIndex (1,2,d)]*C[1][2]*A11A22st/C[j][2];
	end for;

	a := FindIndex (1, 3, d);
	b := FindIndex (2, 3, d);
	A[1][2] := K[a][b]*C[2][3]*A11A33st/C[1][3];
	A[2][1] := K[b][a]*C[1][3]*A11A33st/C[2][3];

	return true, A;
end function;

/* Run Reconstruct: if a division by zero is attempted then works around with a random element */
TryReconstruct := function (G, g, C, CB, CBinv, TypeString, trials, tryWithoutRandomElt)
	if tryWithoutRandomElt then
		flag, A := Reconstruct (G, g, C, CB, CBinv, TypeString);
		if flag then return true, A; end if;
	end if;

	for i in [1..trials] do
		h := Random (G);
		flag1, A1 := Reconstruct (G, g*h^(-1), C, CB, CBinv, TypeString);
		
		if (flag1 eq false) then continue; end if;
		flag2, A2 := Reconstruct (G, h, C, CB, CBinv, TypeString);
		
		if (flag2 eq false) then continue; end if;
		return true, A1*A2;
	end for;
	return false,_;
end function;

/* Recognise G in the adjoint case */
RecogniseAdjoint := function (GG, TypeString, q: NumberRandom := 1000, Hard := true)
        vprint SmallDegree: "Trying to recognise G in the adjoint case";

        G := GG;
	n := Degree (G);
	flag, d := DetermineDegree (n);
	e := getExtensionDegree (d, TypeString);

	if (#BaseRing(G) ne q) then
		if (#BaseRing(G) lt q) then 
			G := sub<GL(n, q) | [G.i : i in [1..Ngens(G)]]>; 
		else 
			flag, K := IsOverSmallerField (G);
			if flag then 
			    G := K;
			else	
			    vprint SmallDegree: "Recognition for adjoint "
				   cat "This is not the correct field size.";
			    return false, _;
			end if;
		end if;
	end if;

        FormTrial := Hard eq true select 10^7 else 10^4;
	for count in [1..NumberRandom] do
                counter := count;
                vprint SmallDegree: "\nSelect special element ", counter;
		found, s, ev, ones := ChooseSingerElt (G, TypeString, d);

		if found eq false then
			vprint SmallDegree: 
			"Could not find a special element: Representation is probably not the adjoint of " , TypeString;
			return false, _;
		else
			vprint SmallDegree: "Special element found.";		
		end if;

		if TypeString eq "2A" and IsEven (d) then
			found, CB, CBinv := FindEigenspacesSUEven (s, ev, ones, G, TypeString);
		else 
			found, CB, CBinv := FindEigenspacesSL (s, ev, ones, G, TypeString);
		end if;

		if found eq false then
			vprint SmallDegree: "Could not label eigenspaces: trying again.";
			continue count;
		else 
			vprint SmallDegree: "Eigenspaces have been computed.";
		end if;

		//find the constants Cij	
		found, C := DetermineConstants (G, CB, CBinv, TypeString, s: Hard := Hard);
	
		if found eq false then
			continue count;
		else 
			vprint SmallDegree: "Constants Cij have been computed.";
		end if;

		X := [];
		for i in [1..Ngens (G)] do
			flag, MyGen := TryReconstruct (G, G.i, C, CB, CBinv, TypeString, NumberRandom, true);
			if not flag then 	
				vprint SmallDegree: "Could not find preimages of generators"; 
				continue count;
			end if;
			if (Determinant(MyGen) eq 0) then continue count; end if;
			Append (~X, MyGen);
		end for;

	        vprint SmallDegree: "Rewriting over the original field...";
		H := sub <GL(d, q^e) | X>;
		flag, A := IsOverSmallerField (H, Degree (BaseRing (G)): Scalars := true);
		if not flag then continue count; end if;

		vprint SmallDegree: "Scaling the generators....";
                gens := [Generic (A) | ];
		for i in [1..Ngens (A)] do
                   a := ScaleMatrix (A.i);
                   if a cmpeq false then 
		      vprint SmallDegree: "Scaling problem. Retrying.", TypeString;
		      continue count;
                   else
                      Append (~gens, a);
                   end if;
                end for;
        	A := sub<Generic (A) | gens>;

        	//fix for nontrivial scalars stuff in unitary case
                if TypeString eq "2A" then 
                   found, A, form := FixForm (A, TypeString: FormTrial := FormTrial);
                   if not found then error "RecogniseAdjoint: Form not fixed"; end if;
        	   gens := [ScaleMatrix (A.i) : i in [1..Ngens(A)] ];
             	   A := sub<Generic (A) | gens>;
                end if;
	        break;
        end for;

	//find and store a form defining our group (for testing preimage)
        // if TypeString ne "2A" then 
           found, form := IdentifyForm (A, TypeString);
        // end if;

	if TypeString ne "A" and not found then 
           vprint SmallDegree:
            "Construction of preimage failed. Input group is probably not adjoint representation of ", TypeString;
           return false, _;
        end if;

	SCB := H`SmallerFieldChangeOfBasis;

	GG`SmallDegree := <"Adjoint", CB, CBinv, C, SCB, SCB^(-1), TypeString, form, q, A>;
	return true, A;
end function;

/* Find the preimage of g in the adjoint case */
AdjointPreimage := function (G, g, limit: NumberRandom := 100)
	R := G`SmallDegree; 
        CB := R[2]; CBinv := R[3]; C := R[4]; SCB := R[5];
        SCBinv := R[6]; TypeString := R[7]; A := R[10]; form := R[8];

	for count in [1..limit] do
		flag, h := TryReconstruct (G, g, C, CB, CBinv, TypeString, NumberRandom, count eq 1);
		if not flag then return false, _; end if;
		if Determinant (h) eq 0 then continue count; end if;

		im := ScaleMatrix (h);
		if (im cmpeq false) then continue count; end if;

		//write the matrix over the subfield
		im := SCBinv*im*SCB;
		im := FindScalarMultipleOverSubfield (im, BaseRing (A));
		if (im cmpeq false) then continue count; end if;

		im := GL(#Rows(im), BaseRing(im))!im;

		if TypeString eq "A" then
		    return true, im;
		elif TypeString eq "2A" then			
			F := BaseRing (A); deg := Degree (F) div 2;
			if form cmpeq false or form eq im * form * Transpose (FrobeniusImage (im, deg)) then 
                            return true, im;
                        else
                            myRootsOfUnity := AllRoots (One(BaseRing(im)), #Rows(im));
                            for myRoot in myRootsOfUnity do
                                mat := im * ScalarMatrix (#Rows(im), myRoot);
                                if form eq mat * form * Transpose (FrobeniusImage (mat, deg)) then 
	                           return true, GL(#Rows(im), BaseRing(im)) ! mat;
                                end if;
     			    end for;
                            return true, im;
                        end if;
                end if;
	end for;
        vprint SmallDegree: "Construction of preimage failed.";
	return false, _;
end function;
