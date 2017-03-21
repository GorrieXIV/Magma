freeze;
////////////////////////////////////////////////////////////////////////
//                                                                    //  
//                       Basis Reduction Extensions                   // 
//                            by David Kohel                          //
//                                                                    // 
////////////////////////////////////////////////////////////////////////

declare verbose Minkowski, 2;

forward SignNormalization, PermutationReduction, NeighborReduction;
forward NormEchelon, CompareGram;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                     MINKOWSKI BASIS REDUCTION                      //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic MinkowskiGramReduction(M::Mtrx : Canonical := false)
    -> Mtrx, Mtrx
{}

    require Type(BaseRing(Parent(M))) in {RngInt,FldRat} : 
        "Argument must be a matrix over the integers or rationals.";
    require IsSymmetric(M) and IsPositiveDefinite(M) : 
       "Argument must be a symmetric positive definite matrix.";
    require not Canonical or Rank(M) le 4 : 
       "Parameter \"Canonical\" is only valid for rank at most 4.";

	   
    deg := Degree(Parent(M));
    ZMat := MatrixAlgebra(Integers(),deg);
    I := Identity(ZMat);
    if Type(BaseRing(Parent(M))) eq RngInt then
	coeffs := Eltseq(M);
	c := GCD(coeffs);
	M0 := ZMat ! [ 1/c * x : x in coeffs ];
    else
	coeffs := Eltseq(M);
	den := LCM([ Denominator(x) : x in coeffs ]);
	num := GCD([ Numerator(den*x) : x in coeffs ]);
	c := num/den;
	M0 := ZMat![ 1/c * x : x in coeffs ];
    end if;
    // Treat some special cases here?
    if Eltseq(M0) eq [2,1,1,0,1,2,1,1,1,1,2,1,0,1,1,2] then
	return M, I;
    end if;
    D, B := SuccessiveMinima(LatticeWithGram(M0));
    // Treat some special cases here.
    if deg eq 4 and &and[ D[i] eq D[1] : i in [2..4] ] then
	if D[1] le 2 then
	    MS := [
	            Matrix(4,4,[1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1]),
   		    Matrix(4,4,[2,1,1,0,1,2,1,1,1,1,2,1,0,1,1,2]),
		    Matrix(4,4,[2,1,0,0,1,2,0,0,0,0,2,1,0,0,1,2])
		  ];
	    for M1 in MS do
		L1 := LatticeWithGram(M1);
		bool, T1 := IsIsometric(LatticeWithGram(M0),L1);
		if bool then
		    return Parent(M) ! (c * M1), T1;
		end if;
	    end for;
	end if;
    elif deg eq 4 and D[1] eq D[2] then
	if D[1] le 2 then
	    MS := [
	            Matrix(4,4,[2,0,1,1,0,2,1,1,1,1,4,1,1,1,1,4]),
		    Matrix(4,4,[2,1,0,0,1,2,0,0,0,0,4,2,0,0,2,4]),
	            Matrix(4,4,[2,1,1,0,1,2,1,1,1,1,10,5,0,1,5,10])
		  ];
	    for M1 in MS do
		L1 := LatticeWithGram(M1);
		bool, T1 := IsIsometric(LatticeWithGram(M0),L1);
		if bool then
		    return Parent(M) ! (c * M1), T1;
		end if;
	    end for;
	end if;
    end if;
    if &or[ D[i] lt M0[i,i] : i in [1..deg] ] then
	T := ZMat! &cat [ Eltseq(v) : v in B ];
	M0 := T*M0*Transpose(T); 
    else // don't change if already there
	T := I;
    end if;
    repeat
	M0, T1 := PermutationReduction(M0);
	if Canonical then
	    M0, T2 := SignNormalization(M0);
	    M0, T3 := NeighborReduction(M0);
	    T1 := T3*T2*T1; 
	end if;
	T := T1*T;
    until T1 eq I;
    return Parent(M) ! (c * M0), T;
end intrinsic;

intrinsic MinkowskiReduction(L::Lat : Canonical := true) -> Lat
    {The Minkowski reduction of L.}
    M, U := MinkowskiGramReduction(
               GramMatrix(L) : Canonical := Canonical );
    return LatticeWithBasis(
        U * BasisMatrix(L), InnerProductMatrix(L) ), U;
end intrinsic;

function IsLessThan(M1, M2)
    dim := Degree(Parent(M1));
    for i in [1..dim] do
	if M1[i,i] lt M2[i,i] then 
	    return true;
	elif M1[i,i] gt M2[i,i] then
	    return false; 
	end if;
    end for;
    for j in [1..dim-1] do
	for i in [1..dim-j] do 
	    if Abs(M1[i,i+j]) gt Abs(M2[i,i+j]) then 
		return true;
	    elif Abs(M1[i,i+j]) lt Abs(M2[i,i+j]) then
		return false; 
	    end if;
	end for;
    end for;
    for j in [1..dim-1] do
	for i in [1..dim-j] do 
	    if M1[i,i+j] gt M2[i,i+j] then 
		return true;
	    elif M1[i,i+j] lt M2[i,i+j] then
		return false; 
	    end if;
	end for;
    end for;
    return false;
end function;

function CompareGram(M1, M2)
    // Return 1 if M1 is less than M2, 0 if M1 and M2 are equal, 
    // and -1 if M2 is less than M1.
    dim := Degree(Parent(M1));
    for i in [1..dim] do
	if M1[i,i] lt M2[i,i] then 
	    return 1;
	elif M1[i,i] gt M2[i,i] then
	    return -1; 
	end if;
    end for;
    for j in [1..dim-1] do
	for i in [1..dim-j] do 
	    if Abs(M1[i,i+j]) gt Abs(M2[i,i+j]) then 
		return 1;
	    elif Abs(M1[i,i+j]) lt Abs(M2[i,i+j]) then
		return -1; 
	    end if;
	end for;
    end for;
    for j in [1..dim-1] do
	for i in [1..dim-j] do 
	    if M1[i,i+j] gt M2[i,i+j] then 
		return 1;
	    elif M1[i,i+j] lt M2[i,i+j] then
		return -1; 
	    end if;
	end for;
    end for;
    return 0;
end function;

function NormEchelon(QF)
    // Returns the matrix obtained by a basis permutation 
    // such that QF[i,i] le QF[j,j] for all i le j. }

    RMat := Parent(QF);
    I := Identity(RMat);
    dim := Degree(RMat);
    U0 := I; U1 := I;
    for i in [1..dim-1] do
	if QF[i+1,i+1] lt QF[i,i] then
	    P := I;
	    P[i+1,i+1] := 0; P[i,i] := 0;         
	    P[i,i+1] := 1; P[i+1,i] := 1;         
	    QF := P*QF*P; U0 := P*U0;
	end if;
    end for;
    if U0 ne I then
	QF, U1 := $$(QF); // Recursion.
    end if;
    return QF, U1*U0;
end function;

/* 
In the following function we make use of the following structure.

Let SignChange(QF,i) be the operation on QF defined by changing 
the sign of the ith variable.  Since Prod_i SignChange(QF,i) = 1, 
and there exists no other relations, the group generated by 
SignChanges is isomorphic to {1,-1}^(n-1). 

Moreover, it has a faithful representation on the sign values of 
a set of n-1 indices {{i_1,j_1},{i_2,j_2},...,{i_n-1,j_n-1}} for 
nondiagonal elements provided that for any subset of cardinality 
r, the collective set of indices has cardinality at least r+1.

For a subset S of r distinct index sets, the number s such that 
the collective set of indices has cardinality r + s is said to be 
the number of components of S.
*/

function SignNormalization(QF)
    // PRE: Takes a symmetric matrix over the Integers().
    // POST: Defines an ordering of the non-diagonal elements 
    // and makes as many as possible positive, with priority 
    // given to the elements of lowest position in the ordering.

    RMat := Parent(QF);
    I := Identity(RMat);
    dim := Degree(RMat);

    FF2 := FiniteField(2);
    VF2 := VectorSpace(FF2,dim);

    PrioritySet := { };
    BoundaryBasis := { VF2 | };
    count := 0;
    // Go through the indices in desired order:
    for j in [1..dim-1] do 
	for k in [1..dim-j] do
	    WF2 := sub< VF2 | BoundaryBasis, VF2.k - VF2.(k+j) >;
	    if Rank(WF2) gt count and QF[k,k+j] ne 0 then
		PrioritySet := PrioritySet join {[k,k+j]};
		BoundaryBasis := BoundaryBasis join {VF2.k - VF2.(k+j)};
		count := count + 1;
	    end if;
	end for;
    end for;
    SkewBasis := { VF2 | };
    for x in PrioritySet do
	if QF[x[1],x[2]] lt 0 then 
	    SkewBasis := SkewBasis join {VF2.x[1] + VF2.x[2] + VF2.1};
	else 
	    SkewBasis := SkewBasis join {VF2.x[1] + VF2.x[2]};
	end if;
    end for;
    WF2 := sub< VF2 | SkewBasis >;
    UF2 := VectorSpace(FiniteField(2),Dimension(WF2));
    HF2 := Hom(UF2,VF2);
    w := Kernel(Transpose(HF2![WF2.i : i in [1..Dimension(WF2)]])).1;
    // Now do the sign changes.
    P := Identity(Parent(QF));
    for i in [1..dim] do
	if w[i] eq One(FF2) then 
	    P[i,i] := -P[i,i];
	end if;
    end for;
    if P*QF*P eq QF then
	P := I;
    end if;
    return P*QF*P, P;
end function;

function PermutationMatrix(g)
    dim := Degree(Parent(g));
    P := DiagonalMatrix([ 0 : i in [1..dim] ]);
    for i in [1..dim] do P[i,i^g] := 1; end for;
    return P;
end function;

function CoordinatePermutationGroup(D)
    Sn := Sym(#D);      // Full permutation group on indices.
    X := SequenceToSet(D);
    StableSets := [ { i : i in [1..#D] | D[i] eq n } : n in X ];
    gens := &join[ { Sn!(i,j) : i in T | i ne j } 
                     where j := Rep(T) : T in StableSets ];
    return sub< Sn | gens >;
end function;

function PermutationReduction(QF)
    // PRE: QF is a Gram matrix.
    // POST: Returns the minimal form under the permutations of 
    // the basis elements.  

    RMat := Parent(QF);
    dim := Degree(RMat);  
    U := Identity(RMat);
 
    // Pick the smallest form from the permutations 
    // stabilizing the norms.

    Q0 := QF;
    G := CoordinatePermutationGroup([ QF[i,i] : i in [1..dim] ]);
    for g in G do 
	P := PermutationMatrix(g);
	Q1 := P*QF*Transpose(P);
	if IsLessThan(Q1,Q0) then 
	    Q0 := Q1; 
	    U := P;
	end if;
    end for;
    return Q0, U;
end function;

function NeighborReduction(QF)
    // Returns the smallest form from those in the neighborhood 
    // of QF.  The resulting form is Minkowski reduced.

    RMat := Parent(QF);
    I := Identity(RMat);
    M := BaseModule(RMat);
    dim := Degree(RMat);

    // Quick exit for the difficult cases. Others?
    if Eltseq(QF) eq [2,1,1,0,1,2,1,1,1,1,2,1,0,1,1,2] then
	return QF, I;
    end if;

    // Neighbor search variables.
    LocalNeighbors := [ { M | [ 1 ] cat [ 0 : i in [2..dim] ] } ];
    for i in [2..dim] do
	NearZero := {-1,0,1};
	Zeros := [ 0 : j in [i+1..dim] ];
	FreeHood := { M | [ x[k] : k in [1..i-1] ] cat [1] cat Zeros 
	: x in CartesianPower(NearZero,i-1) };
	for x in FreeHood do
	    n := InnerProduct(x*QF,x);
	    if n lt QF[i,i] then
		// Found smaller ith basis vector.
		B0 := I; 
		B0[i] := x;
		Q0, U0 := NormEchelon(B0*QF*Transpose(B0));
		return Q0, U0*B0;
	    elif n gt QF[i,i] then
		// Neighbor larger, exclude.
		Exclude(~FreeHood,x);
	    end if;
	end for;
	// Freehood now consists only of coordinates of neighbors 
	// which are ith successive minima.
	Append(~LocalNeighbors,FreeHood);
    end for;

    norms := { QF[i,i] : i in [1..dim] };
    for n in norms do
	inds := [ i : i in [1..dim] | QF[i,i] eq n ];
	X := &join[ LocalNeighbors[i] : i in inds ];
	for i in inds do
	    LocalNeighbors[i] := X;
	end for; 
    end for;

    vprint Minkowski, 2 : "Original NeighborSpace size:", 
    &*[ #S : S in LocalNeighbors ];

    NeighborSpace := [ [ x ] : x in LocalNeighbors[1] ];
    for i in [2..dim] do
	NS1 := [ ]; 
	n := QF[i,i];
	inds := [ j : j in [1..i-1] | QF[j,j] eq n ];
	for y in LocalNeighbors[i] do
	    for C in NeighborSpace do
		// Exclude (C,y) if C[j] = y for some y, or if inner 
		// product with neighboring vector is not maximal.
		if &and[ Booleans() | C[j] ne y : j in inds ] and 
		    Abs(InnerProduct(C[i-1]*QF,y)) ge Abs(QF[i,i-1]) then
		    Append(~NS1,C cat [y]);
		elif &or[ Booleans() | 
		    Abs(InnerProduct(C[j-1]*QF,C[j])) gt 
		    Abs(QF[j,j-1]) : j in [2..i-1] ] then
		    Append(~NS1,C cat [y]);
		end if;
	    end for;
	end for;
	NeighborSpace := NS1;
    end for;

    vprint Minkowski, 2 : 
    "Reduced to NeighborSpace of size:", #NeighborSpace;

    for C in NeighborSpace do
	B0 := Matrix(C); 
	if Abs(Determinant(B0)) eq 1 then
	    // PermutationReduction is redundant since all
	    // permutations are present in NeighborSpace.
	    // Q0, U1 := PermutationReduction(B0*QF*Transpose(B0)); 
	    Q0, U := SignNormalization(B0*QF*Transpose(B0));
	    if IsLessThan(Q0,QF) then
		return Q0, U*B0;
	    end if;
	end if;
    end for;
    return QF, I;
end function;

