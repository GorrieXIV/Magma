freeze;

////////////////////////////////////////////////////////////////////
//    Functions for computing multi-variate Hilbert Series        //
//       (using Bayer-Stillman algorithm)                         //
//     Added by Mike Harrison - 4/11/2004                         //
////////////////////////////////////////////////////////////////////


function HilbertMonomial(mon,P,M)

    col := Matrix(#seq,1,seq) where seq is 
                    [Degree(mon,i) : i in [1..NumberOfColumns(M)]];
    return &*[(P.i)^N[i,1] : i in [1..Rank(P)]] where
                   N is M*col;

end function;

function hnumer(A,M,P)

    r := #A;
    if r eq 0 then
	return P ! 1;
    end if;

    h := 1 - HilbertMonomial(A[1],P,M);
    R := Parent(A[1]);

    for i := 2 to r do
	B := [A[j] div GCD(A[j], A[i]): j in [1 .. i - 1]];
	
	// Reduce B by removing monomials divisible by others
	j := 1;
	while j le #B do 
	    rems := Reverse(
               [k : k in [1..#B] | (k ne j) and IsDivisibleBy(B[k],B[j])]);
	    j -:= #[0: k in rems | k lt j] - 1;
	    for k in rems do Remove(~B,k); end for;
	end while;

        // Separate out linear entries in B	    	
	lins := [];
	for j := #B to 1 by -1 do
	    mon := B[j];
	    if TotalDegree(mon) eq 1 then
		Remove(~B,j);
		lins cat:= [k : k in [1..Rank(R)] | Degree(mon,k) eq 1];
	    end if;
	end for;

        // Recurse
	if #B eq 0 then
	    N := P!1;
	else
	    N := hnumer(B,M,P);
	end if;

	N := (#lins eq 0) select N else N *
               &*[1-HilbertMonomial(R.j,P,M) : j in lins];

	h := h - HilbertMonomial(A[i],P,M) * N;
    end for;

    return h;
end function;

intrinsic HilbertSeries(I::RngMPol,weight_mat::Mtrx[RngInt]) -> RngIntElt
  { Returns the multi-variate Hilbert series of the homogeneous
    ideal I of a multi-graded polynomial ring with gradings given
    by weight matrix weight_mat (with integer entries >= 0)
  }
    require ISA(ModMatRngElt,Type(weight_mat)) or 
	ISA(AlgMatElt,Type(weight_mat)) : "Invalid weight matrix";
    require (BaseRing(weight_mat) eq Integers()) and
	&and[m ge 0 : m in Eltseq(weight_mat)] : "Invalid weight matrix";
    // Should really also check that I is (weight_mat)-homogeneous !!	
	
    gens := [LeadingMonomial(F) : F in GroebnerBasis(EasyIdeal(I))];
    P := PolynomialRing(Rationals(),NumberOfRows(weight_mat));
    return hnumer(gens,weight_mat,P) /
	    &*[1 - &*[(P.j)^weight_mat[j,i] : j in [1..Rank(P)]] : 
		i in [1..NumberOfColumns(weight_mat)]];

end intrinsic;

/* 
   Computes the arithmetic genus of projective variety X whose
   ambient space is product projective.
*/
function MultiGradArithGenus(X)

    I := DefiningIdeal(X);
    grades := Gradings(X);
    P := PolynomialRing(Rationals(),#grades);
    I1 := EasyIdeal(I);
    gens := [LeadingMonomial(F) : F in GroebnerBasis(I1)];
    h_num := hnumer(gens,Matrix(grades),P);
    dimX := Dimension(I1) - #grades;
    
    // reduce hnum mod the powers (x_i-1)^n_i in the denominator
    // of the Hilbert Series
    ns := [ &+g : g in grades];
    h1 := Evaluate(h_num,[(P.i)+1 : i in [1..Rank(P)]]);
    h1_red := &+[t : t in Terms(h1) |
    			&and[Degree(t,i) lt ns[i] : i in [1..Rank(P)]] ];
    return
	(IntegerRing()!Evaluate(h1_red,[-1 : i in [1..Rank(P)]]) -1) * ((-1)^dimX);

end function;
