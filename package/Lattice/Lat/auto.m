freeze;

/////////////////////////////////////////////////////////////////
//                                                             //
//          Automorphism Group of a Lattice                    //
//          by Bernd Souvignier, December 1999                 //  
//          Modified by David Kohel                            //
//          Modified by Allan Steel, Jul 06 (Nebe method)      //
//          Modified by Bill Unger, Jan 10 (New bktk)	       //
//                                                             //
/////////////////////////////////////////////////////////////////

forward autdec;

MaxInt := 2^25;
MaxInt := 2^15;

function IsGramSmall(L)
    M := GramMatrix(L);
    return not exists{ [i,j] :
       i,j in [1..Rank(L)] | i le j and M[i,j] gt MaxInt };
end function;

function candidates(F, B, V)
   // Given a Gram matrix F, a partial basis B compatible 
   // with F (i.e. InnerProduct(B[i], B[j]) eq F[i][j])
   // and a list of vectors V, compute the sublist of vectors 
   // v in V such that B cat [v] is a partial basis compatible 
   // with F.
   // 
   // N.B. the length of B is regarded as the length of the 
   // partial basis, so make sure B does not contain any 
   // additional junk elements
   i := #B + 1;
   // restrict list to vectors of correct norm
   cand := [ v : v in V | Norm(v) eq F[i][i] ];
   for j in [1..#B] do
      // loop over vectors in the partial basis B and restrict list
      // to vectors having correct inner product with vectors in B
      if #cand gt 0 then
         cand := [ v : v in cand | InnerProduct(v, B[j]) eq F[i][j] ];
      end if;
   end for;
   return cand;
end function;

function fingerprint(L, V)
   // Given a lattice L and a list of vectors V in L containing 
   // all vectors with norm up to the maximal diagonal entry of 
   // GramMatrix(L), compute some invariants for automorphisms 
   // of L: FP[i] is the number of vectors from V by which the 
   // first i-1 standard basis vectors can be extended to a 
   // partial basis of i elements note that the product of the 
   // FP[i] is an upper bound for the group order.
   F := GramMatrix(L);
   n := Nrows(F);
   One := MatrixRing(Integers(), n) ! 1;
   // get standard basis vectors as rows of a unity matrix
   E := [ L!One[i] : i in [1..n] ];
   FP := [ 0 : i in [1..n] ];
   for i in [1..n] do
      // set the first i-1 elements of B to the standard basis elements
      B := [ E[j] : j in [1..i-1] ];
      // get the number of vectors v such that B cat [v] is a partial basis
      // compatibel with F
      FP[i] := #candidates(F, B, V);
   end for;
   return FP;
end function;

function auto(L, V, FP, level) 
   // Given a lattice L, a list of vectors V, a sequence of invariants 
   // FP (as computed by fingerprint) and a stablizer level, compute 
   // elements g in Aut(L) such that each g fixes the first level-1
   // standard basis vectors and such that the orbit of the level-th 
   // standard basis vector under these elements is the full orbit 
   // under the point-stabilizer of the first level-1 standard basis 
   // vectors in Aut(L)

   /* print "in auto on level", level; */
   F := GramMatrix(L);
   n := Nrows(F);
   // start off with an empty sequence of generators
   gens := [];
   G := MatrixGroup< n, Integers() | gens >;
   One := MatrixRing(Integers(), n) ! 1;
   cand := [ [] : i in [1..n] ];
   // set the images of the first level-1 standard basis vectors 
   // to contain only the standard basis vectors themselves, thus 
   // ensuring the stabilizing property
   for i in [1..level-1] do
      cand[i] := [ L!One[i] ];
   end for;
   // Compute the candidates on the required level, this is the 
   // maximal possible orbit
   cand[level] := candidates(F, [ L!One[i] : i in [1..level-1] ], V);
   // Exclude the trivial image from the list, since it is covered 
   // by the identity.
   Exclude(~cand[level], L!One[level]);
   // Step is the length of the current partial basis and thus 
   // controlling the depth of the backtrack.
   step := level;
   // Finish backtrack when all possible images for the level-th 
   // basis vector have been processed.
   while #cand[level] gt 0 do
      // Set the current partial basis to being the first vector 
      // in the candidate lists up to depth step.
      B := [ cand[i][1] : i in [1..step] ];
      // If B is not yet a full basis, compute the possible extensions.
      if step+1 le n then
         cand[step+1] := candidates(F, B, V);
      end if;
      // Check if the number of possible extensions agrees with 
      // the precomputed number in FP.
      if step+1 le n and #cand[step+1] ne FP[step+1] then
         // This is a cul-de-sac, the vector cand[step][1] 
         // has to be replaced
         Remove(~cand[step], 1);
         // If this was the last candidate for the image of the 
         // step-th basis vector, we have to decrease step and 
	 // remove the candidate on the previous level.
         while step gt 0 and #cand[step] eq 0 do
   	    step -:= 1;
            // It turns out that the candidate on level 'level' 
	    // can not be extended to a partial basis, we therefore 
            // can remove the full orbit of this vector under the 
            // automorphisms found so far (on this level), since 
	    // these can not be extended, either
            if step eq level then
               orb := Orbit(G, cand[level][1]);
               for v in orb do
                  Exclude(~cand[level], v);
               end for;
               // For steps different from level, simply remove 
	       // the first candidate (the one chosen in B).
            elif step gt 0 then
               Remove(~cand[step], 1);
            end if;
         end while;
      else
         // Either the number of possible extensions was correct 
         // or we already found a full basis. 
         if step+1 lt n then
            // This is still only a partial basis, but we can 
      	    // increase the depth
            step +:= 1;
         else
            // Found a new generator for this level; 
	    // append it to the list of generators
	    g := MatrixRing(Integers(), n) ! 
               &cat[Eltseq(cand[i][1]) : i in [1..n]];
            /* print "new generator", g; */
	    Append(~gens, g);
            // Form the matrix group generated by the elements 
            // found so far.
            G := MatrixGroup< n, Integers() | gens >;
            // Compute the orbit of the (successful) candidate 
	    // on level 'level' and exclude it from the list of 
	    // candidates remaining to be considered.
            orb := Orbit(G, cand[level][1]);
            for v in orb do
               Exclude(~cand[level], v);
            end for;
            // Reset the backtrack search to the initial value
            // note that we might have more than one candidate 
	    // on the last level, and could thus obtain one 
	    // generator for each of these, but this gives 
            // many redundant generators, as they only differ 
	    // in the image of the last basis vector.
            step := level;
         end if;
      end if;
   end while;
   // return the sequence of generators found on this level
   return gens;
end function;

function isom(L, V, FP)
   // Given a target lattice L, a list of vectors V from a source 
   // lattice (L1, say), and a sequence of invariants FP for L 
   // (as computed by fingerprint) try to compute a matrix having 
   // as rows elements from V (i.e. from L1) such that their inner 
   // products agree with the entries of the Gram matrix of L 
   // (the target lattice) if such a matrix T exists, it is 
   // an isometry from the source to the target lattice 
   // (i.e. T * GramMatrix(L1) * Transpose(T) = GramMatrix(L))
   // otherwise the lattices are not isometric

   F := GramMatrix(L);
   n := Nrows(F);
   // Initialize the isometry to the 0-matrix (indicating that 
   // no isometry exists)
   T := MatrixRing(Integers(), n) ! 0;
   cand := [ [] : i in [1..n] ];
   // Compute the candidates for the first level
   cand[1] := candidates(F, [], V);
   // Initialize the backtrack depth
   step := 1;
   // Finish backtrack when all possible images for the first 
   // basis vector have been processed or when an isometry has 
   // been found (indicated by step eq 0).
   while #cand[1] gt 0 and step gt 0 do
      // Set the current partial basis to being the first vector 
      // in the candidate lists up to depth step.
      B := [ cand[i][1] : i in [1..step] ];
      // If B is not yet a full basis, compute the possible extensions.
      if step+1 le n then
         cand[step+1] := candidates(F, B, V);
      end if;
      // Check if the number of possible extensions agrees with 
      // the precomputed number in FP.
      if step+1 le n and #cand[step+1] ne FP[step+1] then
         // This is a cul-de-sac, the vector cand[step][1] has 
         // to be replaced.
         Remove(~cand[step], 1);
         // If this was the last candidate for the image of the 
         // step-th basis vector, we have to decrease step and 
         // remove the candidate on the previous level.
         while step gt 0 and #cand[step] eq 0 do
            step -:= 1;
            if step gt 0 then
               Remove(~cand[step], 1);
            end if;
         end while;
      else
         // Either the number of possible extensions was correct 
         // or we already found a full basis. 
         if step+1 lt n then
            // This is still only a partial basis, but we can 
            // increase the depth.
            step +:= 1;
         else
            // found an isometry, set step to 0 to finish backtracking
            T := MatrixRing(Integers(), n) !
               &cat[Eltseq(cand[i][1]) : i in [1..n]];
            step := 0;
         end if;
      end if;
   end while;
   // If no isometry exists, T will still be the 0-matrix, 
   // otherwise it is the found isometry
   return T;
end function;

intrinsic AutomorphismGroup(L::Lat :
   Depth := 0,
   BacherDepth := -1,
   BacherSCP := -1,	// ARGH: do not use 0!!!!!
   Stabilizer := 0,
   Generators := [],
   NaturalAction := false,
   Decomposition := false,
   VectorsLimit := -1,
   Vectors := 0
) -> GrpMat
   {The automorphism group of the lattice L.}
   // Send to InternalAutomorphismGroup provided coordinates 
   // are sufficiently small.

   if assigned L`AutomorphismGroup then
      if not NaturalAction then
	  return L`AutomorphismGroup;
      end if;
      if Rank(L) ne Degree(L) then
	error "Unable to compute natural action of lattice automorphism group";
      end if;
      GQ := ChangeRing(L`AutomorphismGroup, Rationals());
      T := Generic(GQ)!ChangeRing(BasisMatrix(L), Rationals());
      return GQ^T;
   end if;

   if Decomposition then
      f, G := autdec(L);
      if f then
	  L`AutomorphismGroup := G;
	  if not NaturalAction then 
	      return G;
	  end if;
      else
	  vprint AUTOISOM: "Decomposition method failed";
      end if;
   end if;

    if Vectors cmpeq 0 then
	return InternalAutomorphismGroup(L:
	    Depth := Depth,
	    BacherDepth := BacherDepth,
	    BacherSCP := BacherSCP,
	    Stabilizer := Stabilizer,
	    Generators := Generators,
	    NaturalAction := NaturalAction,
	    VectorsLimit := VectorsLimit
	);
    else
	return InternalAutomorphismGroup(L:
	    Depth := Depth,
	    BacherDepth := BacherDepth,
	    BacherSCP := BacherSCP,
	    Stabilizer := Stabilizer,
	    Generators := Generators,
	    NaturalAction := NaturalAction,
	    VectorsLimit := VectorsLimit,
	    Vectors := Vectors
	);
    end if;

end intrinsic;

/*
intrinsic IsIsomorphic(L1::Lat, L2::Lat :
   Depth := 0,
   BacherDepth := 0,
   BacherSCP := 0,
   Stabilizer := 0,
   Generators := [],
   NaturalAction := false) -> BoolElt
   {True and a matrix from L1 to L2 if L1 is isometric to L2;
   false otherwise.}
   return IsIsometric(L1,L2 :
           Depth := Depth,
           BacherDepth := BacherDepth,
           BacherSCP := BacherSCP,
           Stabilizer := Stabilizer,
           Generators := Generators,
           NaturalAction := NaturalAction);
end intrinsic;
*/

forward isodec;
intrinsic IsIsometric(L1::Lat, L2::Lat :
   Depth := 0,
   BacherDepth := 0,
   BacherSCP := 0,
   LeftGenerators := [],
   RightGenerators := [],
   VectorsLimit := 0,
   LeftVectors := 0,
   RightVectors := 0,
   Decomposition := false
) -> BoolElt, Mtrx
   {True and a matrix from L1 to L2 if L1 is isometric to L2;
   false otherwise.}
   // Send to InternalIsIsometric provided coordinates 
   // are sufficiently small.

   if Decomposition then
	return isodec(L1,L2);
   end if;

   if LeftVectors cmpeq 0 and RightVectors cmpeq 0 then
       return InternalIsIsometric(L1,L2 :
	       BacherDepth := BacherDepth,
	       BacherSCP := BacherSCP,
	       LeftGenerators := LeftGenerators,
	       RightGenerators := RightGenerators,
	       VectorsLimit := VectorsLimit
	    );
    elif LeftVectors cmpeq 0 then
       return InternalIsIsometric(L1,L2 :
	       BacherDepth := BacherDepth,
	       BacherSCP := BacherSCP,
	       LeftGenerators := LeftGenerators,
	       RightGenerators := RightGenerators,
	       VectorsLimit := VectorsLimit,
	       RightVectors := RightVectors
	    );
    elif RightVectors cmpeq 0 then
       return InternalIsIsometric(L1,L2 :
	       BacherDepth := BacherDepth,
	       BacherSCP := BacherSCP,
	       LeftGenerators := LeftGenerators,
	       RightGenerators := RightGenerators,
	       VectorsLimit := VectorsLimit,
	       LeftVectors := LeftVectors
	    );
    else
       return InternalIsIsometric(L1,L2 :
	       BacherDepth := BacherDepth,
	       BacherSCP := BacherSCP,
	       LeftGenerators := LeftGenerators,
	       RightGenerators := RightGenerators,
	       VectorsLimit := VectorsLimit,
	       LeftVectors := LeftVectors,
	       RightVectors := RightVectors
	    );
    end if;

   // Function to compute an isometry between two integral lattices.
   // If an isometry T is found, it has the property
   // T * GramMatrix(Lat1) * Transpose(T) = GramMatrix(Lat2).
   // handle a trivial case first.

   if Rank(L1) ne Rank(L2) then
      return false, 0;
   end if;

// "**** ORIG ****"; L1; L2;

   L1, T1 := LLL(L1);
   L2, T2 := LLL(L2);

// "**** NEW ****"; L1; L2;
   
   // perform the preprocessing as if computing the automorphism 
   // group for L2 the only difference between finding an automorphism 
   // of L2 and finding an isometry from L1 to L2 is that the matrix 
   // rows are taken as vectors from L1 instead of L2.
   L2 := CoordinateLattice(L2);
   F2 := GramMatrix(L2);
   n := Nrows(F2);
   // The norms of the images of the basis vectors must coincide 
   // with the diagonal entries of the Gram matrix, in particular 
   // they are bounded by the maximum of these values.
   max := Max([ F2[i][i] : i in [1..n] ]);
   // Compute the short vectors in L2 up to the maximal diagonal 
   // entry in the Gram matrix F2.
   SV2 := ShortVectors(L2, max);
   // ShortVectors only gives one of the +/- pairs of vectors, 
   // but to make life easy (and expecting only few vectors) 
   // we include the vectors with opposite sign explicitly.
   V2 := [ v[1] : v in SV2 ] cat [ -v[1] : v in SV2 ];
   // Compute the fingerprint containing some invariants under 
   // automorphisms with respect to L2 (see function explanation 
   // for 'fingerprint').
   FP := fingerprint(L2, V2);
   // At this point, everything about lattice L2 can be 
   // forgotten except for the invariants, which are basically 
   // stored in the Gram matrix F2 and the fingerprint FP.
   L1 := CoordinateLattice(L1);
   // Compute the short vectors in L1 up to the maximal diagonal 
   // entry in the Gram matrix F2.
   SV1 := ShortVectors(L1, max);
   // ShortVectors only gives one of the +/- pairs of vectors, 
   // but to make life easy (and expecting only few vectors) 
   // we include the vectors with opposite sign explicitly.
   V1 := [ v[1] : v in SV1 ] cat [ -v[1] : v in SV1 ];
   // Try to construct a basis B for L1 consisting of vectors 
   // from V1, such that the inner products agree with the Gram 
   //matrix of L2 (i.e. InnerProduct(B[i], B[j]) eq F2[i][j])
   T := isom(L2, V1, FP);
   // If a 0-matrix was returned, no isometry exists, otherwise 
   // the returned matrix is an isometry.
   if T eq MatrixRing(Integers(), n) ! 0 then
      return false, 0;
   else
      return true, T2^-1*T*T1;
   end if;
end intrinsic;

/*
Auto/Isom via decomposition of the Lattice.
Gabi Nebe, March 2006 (installed by Allan Steel).
*/

Z:=Integers();
Q:=Rationals();

make_group_base := function(n1, b1, n2, b2)
    res := [* *];
    d := n1 + n2;
    M := RSpace(Z, d);
    for i := 1 to #b1 do
	b := b1[i];
	if ISA(Type(b), ModTupRng) then
	    bm := BasisMatrix(b);
	    bm := HorizontalJoin(bm, ZeroMatrix(Z, Nrows(bm), n2));
	    bb := sub<M|bm>;
	else
	    assert ISA(Type(b), ModTupRngElt);
	    bb := M!HorizontalJoin(b, ZeroMatrix(Z, 1, n2));
	end if;
	Append(~res, bb);
    end for;
    for i := 1 to #b2 do
	b := b2[i];
	if ISA(Type(b), ModTupRng) then
	    bm := BasisMatrix(b);
	    bm := HorizontalJoin(ZeroMatrix(Z, Nrows(bm), n1), bm);
	    bb := sub<M|bm>;
	else
	    assert ISA(Type(b), ModTupRngElt);
	    bb := M!HorizontalJoin(ZeroMatrix(Z, 1, n1), b);
	end if;
	Append(~res, bb);
    end for;
    return res;
end function;

autdec := function(L)
    /*
    Try to decompose L and compute the Automorphism group via the
    decomposition; return true and Aut(L) if so; otherwise return false
    if the method is not applicable.
    */

    L := CoordinateLattice(L);

    //Calculates the orthogonal decomposable sublattice generated by
    // the "sucessive minima" 
    dimlist:=[];
    AA:=[**];
    bases := [**];
    orders := [];
    genlist:=[];
    F:=GramMatrix(L);
    if BaseRing(F) cmpne Z then
	return false, _;
    end if;
    N:=Rank(L);
    n:=0;
    R:=L; //remaining lattice = M ^perp
    T:=MatrixRing(Integers(),N) ! 1;
     //Transformation matrix from standardbasis of L
    // to standardbasis of R
    B:=RMatrixSpace(Integers(),0,N) ! 0;
    vprintf AUTOISOM: "Initial Rank %o\n", N;
    while (n lt N) do 
	S:=ShortestVectorsMatrix(R);
	vprintf AUTOISOM: "Got %o shortest vectors\n", Nrows(S);
	H:=HermiteForm(S);
	m:=Rank(H);
	vprintf AUTOISOM: "Rank %o\n", m;
	H:=RowSubmatrix(H,1,m);

	if Ncols(H) eq m  and IsUnit(H) then
	    vprint AUTOISOM: "Give up on decomposition method";
	    return false, _;
	end if;

	Append(~dimlist,m);
	FM:=H*F*Transpose(H);
	GM,TM:= LLLGram(FM);
	H:=TM*H;
	n:=n+m;
        AG:=AutomorphismGroup(LatticeWithGram(GM): Decomposition := false);
	GAG := Generic(AG);
	A:=[GAG| x: x in Generators(AG)];
	A := SequenceToList(A);
        AA:=AA cat A;
        if #genlist gt 0 then 
	    Append(~genlist,genlist[#genlist] + #A);
        else 
	    Append(~genlist, #A);
        end if;
	BSGS(AG);
	Append(~bases, Base(AG));
	Append(~orders, #AG);
	B:=VerticalJoin(B,H);
	R1:=KernelMatrix(T*F*Transpose(H));
	T:=R1*T;
	HH:=[];
	for i in [1..NumberOfRows(T)] do Append(~HH,L ! Eltseq(T[i])); end for;
	R:=sub<L | HH >;
    end while;

    n:=dimlist[1];
    G1:=sub<GL(n,Integers()) | [ AA[i] : i in [1..genlist[1]] ] >;
    G1`Base := bases[1];
    G1`Order := orders[1];
    S := RowSubmatrix(B, 1, n);
    SI:= Solution(Matrix(Q,S), Matrix(Q,Saturation(S)));
    denom:=LCM([Denominator(x): x in Eltseq(SI)]);
    SI:=Matrix(Z,denom*SI);
    if (Abs(denom )) ne 1 then 
	stab:=Stabilizer(G1, RowSpace(SI));
    else
	stab:=G1;
    end if;

    for j in [2..#dimlist] do 
	G1 := MatrixGroup<n+dimlist[j],Z|
	    [DiagonalJoin(stab.i,MatrixRing(Integers(),dimlist[j]) ! 1):
		i in [1..Ngens(stab)]] cat
	    [DiagonalJoin(MatrixRing(Integers(),n) ! 1, AA[i]) :
	     i in [genlist[j-1]+1..genlist[j]] ] >;
	G1`Base := make_group_base(n, Base(stab), dimlist[j], bases[j]);
	G1`Order := #stab*orders[j];
	n:=n+dimlist[j];
	S := RowSubmatrix(B, 1, n);
	SI:= Solution(Matrix(Q,S), Matrix(Q,Saturation(S)));
	denom:=LCM([Denominator(x): x in Eltseq(SI)]);
	if (Abs(denom )) ne 1 then 
	    SI:=Matrix(Z,denom*SI);
	    stab:=Stabilizer(G1, RowSpace(SI));
	else
	    stab:=G1;
	end if;
    end for; // j in #dimlist 
    B:=Matrix(Q,B);
    stabQ := ChangeRing(stab, Q);
    U := ChangeRing(stabQ^(Generic(stabQ)!B), Z);
    //U is the automorphism group of L

    assert HasAttribute(U, "Base");
    if not HasAttribute(U, "Order") then U`Order := #stab; end if;
    return true, U;

end function;


isodec:=function(L,M)
/*
This function determines whether the lattices L and M are isometric.
If the lattices are isometric, the function returns a transformation matrix T as a
second return value such that F_2 = T F_1 T^(tr), where F_1 and F_2
are the Gram matrices of L and M, respectively.  
It is the same as IsIsometric (and calls IsIsometric) if both
lattices are generated by their minimal vectors.
If L and M are isometric but not generated by their minimal vectors
then isodec automatically calculates the automorphism group of the second lattice M
and returns this group as a 3rd return value.
So this is as expensive as finding the full automorphism group of a lattice
(and I do not see how to avoid this).
It might however be much faster than IsIsometric if the lattices are
far from being generated by shortest vectors.
*/
    N:=Rank(L);
    if N ne Rank(M) then 
          // print "lattices have different rank";
          return false,_,_;
    end if;
    if Determinant(L) ne Determinant(M) then 
         // print "lattices have different determinants";
         return false,_,_;
    end if;
    L := CoordinateLattice(L);
    if IsGLattice(L) then L := LatticeWithGram(GramMatrix(L)); end if;
    M := CoordinateLattice(M);
    if IsGLattice(M) then M := LatticeWithGram(GramMatrix(M)); end if;
    //Calculates the orthogonal decomposable sublattice generated by
    // the "sucessive minima" 
    dimlist:=[];
    AA:=[**]; //Automorphism generators of perp Mi
    II:=[**]; //List of isometries between the Li and the Mi
    genlist:=[];
    FL:=GramMatrix(L);
    FM:=GramMatrix(M);
    n:=0;
    RL:=L; //remaining lattice = M ^perp
    RM:=M; //remaining lattice = M ^perp
    TL:=MatrixRing(Integers(),N) ! 1;
    TM:=MatrixRing(Integers(),N) ! 1;
     //Transformation matrix from standardbasis of L
    // to standardbasis of R
    BL:=RMatrixSpace(Integers(),0,N) ! 0;
    BM:=RMatrixSpace(Integers(),0,N) ! 0;
    // printf "Initial Rank %o\n", N;
    while (n lt N) do 
	SL:=ShortestVectorsMatrix(RL);
        nrl:=Nrows(SL);
	// printf "Got %o shortest vectors of L\n", nrl;
	SM:=ShortestVectorsMatrix(RM);
        nrm:=Nrows(SM);
	// printf "Got %o shortest vectors of M\n", nrm;
        if nrl ne nrm then 
            // print "lattices have different number of short vectors";
            return false,_,_;
        end if;
	if CoefficientRing(SL) eq Q then SL := ChangeRing(SL, Z); end if;
	HL:=HermiteForm(SL);
	mL:=Rank(HL);
	// printf "Rank %o\n", mL;
	HL:=RowSubmatrix(HL,1,mL);

	if Ncols(HL) eq mL and IsUnit(HL) then
	    // "Give up";
	    return IsIsometric(L,M:Decomposition:=false);
	end if;
	if CoefficientRing(SM) eq Q then SM := ChangeRing(SM, Z); end if;
	HM:=HermiteForm(SM);
	mM:=Rank(HM);
	// printf "Rank %o\n", mM;
	HM:=RowSubmatrix(HM,1,mM);
        if mM ne mL then 
            // print "lattices have different short vectors rank";
            return false,_,_;
        end if;
	Append(~dimlist,mL);
	F1L:=HL*FL*Transpose(HL);
	G1L,T1L:= LLLGram(F1L);
	HL:=T1L*HL;
	n:=n+mL;
	F1M:=HM*FM*Transpose(HM);
	G1M,T1M:= LLLGram(F1M);
	HM:=T1M*HM;
        flag,alpha:=IsIsometric(LatticeWithGram(G1L),LatticeWithGram(G1M):Decomposition:=false);
        if flag eq false then
             // print "sublattices are not isometric";
             return false,_,_;
        end if;
        Append(~II , alpha);
        AG:=AutomorphismGroup(LatticeWithGram(G1M):Decomposition:=false);
        a:=#Generators(AG);
	for g in Generators(AG) do 
            Append(~AA,g);
        end for;
        if #genlist gt 0 then 
	    Append(~genlist,genlist[#genlist] + a);
        else 
	    Append(~genlist, a);
        end if;
	BL:=VerticalJoin(BL,HL);
	R1L:=KernelMatrix(TL*FL*Transpose(HL));
	TL:=R1L*TL;
	HH:=[];
	for i in [1..NumberOfRows(TL)] do Append(~HH,L!Eltseq(TL[i])); end for;
	RL:=sub<L | HH >;
	assert Rank(RL) le #HH;
	BM:=VerticalJoin(BM,HM);
	R1M:=KernelMatrix(TM*FM*Transpose(HM));
	assert IsZero(R1M*TM*FM*Transpose(HM));
	TM:=R1M*TM;
	HH:=[];
	for i in [1..NumberOfRows(TM)] do Append(~HH,M!Eltseq(TM[i])); end for;
	RM:=sub<M | HH >;
	assert Rank(RM) le #HH;
    end while;

// return II,dimlist,genlist,BL,BM,AA;
// print "isometries between the orthogonal summands",II;

// II,dimlist,genlist,BL,BM,AA:=isodec(L,M);
stabi:=sub<GL(1,Integers()) | 1>;
// ???? Why do I have to initialize this ??? 

for j in [1..#dimlist] do 
	if j eq 1 then 
		isomi:=II[1]^(-1);
		n:=dimlist[1];
		G1:=sub<GL(n,Integers()) | [ AA[i] : i in [1..genlist[1]] ] >;
	else
		G1 := MatrixGroup<n+dimlist[j],Z|
		[DiagonalJoin(stabi.i,MatrixRing(Integers(),dimlist[j]) ! 1):
		 i in [1..Ngens(stabi)]] cat
		[DiagonalJoin(MatrixRing(Integers(),n) ! 1, AA[i]) :
 		i in [genlist[j-1]+1..genlist[j]] ] >;
		isomi:=DiagonalJoin(Matrix(Q, isomi),Matrix(Q,II[j])^(-1));
		n:=n+dimlist[j];
	end if;
	SM := RowSubmatrix(BM, 1, n);
	SIM:= Solution(Matrix(Q,SM), Matrix(Q,Saturation(SM)));
	denomM:=LCM([Denominator(x): x in Eltseq(SIM)]);
	SL := RowSubmatrix(BL, 1, n);
	SIL:= Solution(Matrix(Q,SL), Matrix(Q,Saturation(SL)));
	denomL:=LCM([Denominator(x): x in Eltseq(SIL)]);
	if (Abs(denomM) ne Abs(denomL)) then 
   		// printf "different denominators in %o th amalgamation\n",j;
   		return false,_,_;
	end if;
        if Abs(denomM) ne 1 then
		isommerk:=Matrix(Z,denomL*SIL*Matrix(Q,isomi));
		SIM:=Matrix(Z,denomM*SIM);
        	H1:=ChangeBase(G1,[RowSpace(SIM)]);
        	stabi := BasicStabilizer(H1,2);
        	isin,trans := IsInBasicOrbit(H1,1,RowSpace(isommerk));
        	if not isin then 
      			// printf "no isometry in the %o th amalgamation\n",j;
          		return false,_,_;
		else
  			isomi:=isomi*Matrix(Q, trans);
       			// print isomi;
       			// print Determinant(isomi);
    		end if;
	else
   		stabi:=G1;
		// print isomi;
	end if;
end for; // j in #dimlist 
BM:=Matrix(Q,BM);
BMi:=BM^(-1);

U:=sub<GL(n,Z)  | 
[ Matrix(Z, BMi*Matrix(Q,stabi.i)*BM) : i in [1..#Generators(stabi)] ] > ;

//U is the automorphism group of M
isom:=Matrix(Z ,BMi*Matrix(Q,isomi^(-1))*BL);

return true,isom,U;
end function;

intrinsic SVMForLattAuto(L::Lat, N::RngIntElt, M::RngIntElt) -> Mtrx
{}
    if M le 0 then return ShortVectorsMatrix(L, N, N); 
    else return ShortVectorsMatrix(L, N, N : Max := M);
    end if;

end intrinsic;

intrinsic SVMForLattIso(L1::Lat, L2::Lat, M::RngIntElt) -> BoolElt, Mtrx, Mtrx
{}
    if Rank(L1) ne Rank(L2) or Determinant(L1) ne Determinant(L2) then
	return false, _, _;
    end if;
    SV1 := ShortestVectorsMatrix(L1: Max := M);
    SV2 := ShortestVectorsMatrix(L2: Max := M);
    if Nrows(SV1) ne Nrows(SV2) or Minimum(L1) ne Minimum(L2) then
	return false, _, _;
    end if;
    if Nrows(SV1) ge M then
	error "Unable to enumerate shortest vectors within given limit";
    end if;
    SL1 := sub<L1 | SV1>; SL2 := sub<L2 | SV2>;
    if (SL1 eq L1 and SL2 ne L2) or (SL1 ne L1 and SL2 eq L2) then
	return false, _, _;
    end if;
    if SL1 eq L1 then
	return true, ChangeRing(SV1, Integers()), ChangeRing(SV2, Integers());
    end if;
    Q1 := AbelianInvariants(quo<L1 | SL1>);
    Q2 := AbelianInvariants(quo<L2 | SL2>);
    if Q1 ne Q2 then 
	return false, _, _;
    end if;
    start := Minimum(L1);
    X := GramMatrix(L1);
    step := GCD([X[i,i]: i in [1..Rank(L1)]]); 
    if step gt 2 then
	step := GCD(step, 2*GCD([X[i,j]: i,j in [1..Rank(L1)] | i lt j]));
    end if;
    repeat 
	start +:= step;
	SV1 := ShortVectorsMatrix(L1, start: Max := M);
	SV2 := ShortVectorsMatrix(L2, start: Max := M);
	if Nrows(SV1) ne Nrows(SV2) then
	    return false, _, _;
	end if;
	if Nrows(SV1) ge M then
	    error "Unable to enumerate shortest vectors within given limit";
	end if;
	SL1 := sub<L1 | SV1>; SL2 := sub<L2 | SV2>;
	if (SL1 eq L1 and SL2 ne L2) or (SL1 ne L1 and SL2 eq L2) then
	    return false, _, _;
	end if;
	if SL1 eq L1 then
	    return true, ChangeRing(SV1, Integers()), ChangeRing(SV2, Integers());
	end if;
	Q1 := AbelianInvariants(quo<L1 | SL1>);
	Q2 := AbelianInvariants(quo<L2 | SL2>);
	if Q1 ne Q2 then 
	    return false, _, _;
	end if;
    until false;
end intrinsic;

lattice_aut_preprocess_sets := function(L, F, S)
    Fnew := F;
    n := Degree(L);
    Snew := [];
    gm := GramMatrix(L);
    for s in S do
	Ss := [];
	lookup := {@ @};
	for f in s do

	    r := Rank(f);
	    fp := [r];
	    Append(~fp, r eq n select Determinant(f) else 0);

	    Append(~fp, IsSymmetric(f) select 1 else 0);

	    f2 := f + gm;
	    r := Rank(f2);
	    Append(~fp, r);
	    Append(~fp, r eq n select Determinant(f2) else 0);
	    delete f2;

	    f2 := f - gm;
	    r := Rank(f2);
	    Append(~fp, r);
	    Append(~fp, r eq n select Determinant(f2) else 0);
	    delete f2;

	    fpi := Index(lookup, fp);
	    if fpi eq 0 then
		Append(~Ss, [f]);
		Include(~lookup, fp);
	    else
		x := Ss[fpi];
		Append(~x, f);
		Ss[fpi] := x;
	    end if;
	end for;
	delete lookup;
	Fnew cat:= [&+x: x in Ss];
	Snew cat:= [x : x in Ss | #x gt 1];
    end for;
    return Fnew, Snew;
end function;

lattice_iso_preprocess_sets := function(L1, F1, S1, L2, F2, S2)

    n := Degree(L1);
    if
	n ne Degree(L2) or #F1 ne #F2 or #S1 ne #S2 or
	[#x:x in S1] ne [#x:x in S2]
    then
	return false, _, _, _, _;
    end if;
    
    F1new := F1;
    F2new := F2;
    S1new := [];
    S2new := [];
    gm1 := GramMatrix(L1);
    gm2 := GramMatrix(L2);

    for i := 1 to #S1 do
	s := S1[i];
	Ss1 := [];
	lookup := {@ @};
	for f in s do

	    r := Rank(f);
	    fp := [r];
	    Append(~fp, r eq n select Determinant(f) else 0);

	    Append(~fp, IsSymmetric(f) select 1 else 0);

	    f2 := f + gm1;
	    r := Rank(f2);
	    Append(~fp, r);
	    Append(~fp, r eq n select Determinant(f2) else 0);
	    delete f2;

	    f2 := f - gm1;
	    r := Rank(f2);
	    Append(~fp, r);
	    Append(~fp, r eq n select Determinant(f2) else 0);
	    delete f2;

	    fpi := Index(lookup, fp);
	    if fpi eq 0 then
		Append(~Ss1, [f]);
		Include(~lookup, fp);
	    else
		x := Ss1[fpi];
		Append(~x, f);
		Ss1[fpi] := x;
	    end if;

	end for;
	Ss2 := [Universe(Ss1) | [] :x in [1..#lookup]];
	s := S2[i];
	for f in s do

	    r := Rank(f);
	    fp := [r];
	    Append(~fp, r eq n select Determinant(f) else 0);

	    Append(~fp, IsSymmetric(f) select 1 else 0);

	    f2 := f + gm2;
	    r := Rank(f2);
	    Append(~fp, r);
	    Append(~fp, r eq n select Determinant(f2) else 0);
	    delete f2;

	    f2 := f - gm2;
	    r := Rank(f2);
	    Append(~fp, r);
	    Append(~fp, r eq n select Determinant(f2) else 0);
	    delete f2;

	    fpi := Index(lookup, fp);
	    if fpi eq 0 then
		return false, _, _, _, _;
	    else
		x := Ss2[fpi];
		Append(~x, f);
		Ss2[fpi] := x;
	    end if;

	end for;
	delete lookup;
	if [#x: x in Ss1] ne [#x: x in Ss2] then
	    return false, _, _, _, _;
	end if;
	F1new cat:= [&+x : x in Ss1];
	F2new cat:= [&+x : x in Ss2];
	S1new cat:= [x : x in Ss1 | #x gt 1];
	S2new cat:= [x : x in Ss2 | #x gt 1];
	delete Ss1, Ss2;
    end for;
    assert #F1new eq #F2new;
    assert [#x: x in S1new] eq [#x: x in S2new];
    return true, F1new, S1new, F2new, S2new;

end function;

intrinsic AutomorphismGroup(L::Lat, S::SetEnum[Mtrx] :
   Depth := 0,
   BacherDepth := -1,
   BacherSCP := -1,	// ARGH: do not use 0!!!!!
   Stabilizer := 0,
   Generators := [],
   NaturalAction := false,
   Decomposition := false,
   VectorsLimit := -1,
   Vectors := 0
) -> GrpMat
   {The subgroup of the automorphism group of the lattice L fixing the forms
    in S setwise.}

    if #S eq 0 then
	if Vectors cmpeq 0 then
	    return AutomorphismGroup(L:
		Depth := Depth,
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		Stabilizer := Stabilizer,
		Generators := Generators,
		NaturalAction := NaturalAction,
		VectorsLimit := VectorsLimit,
		Decomposition := Decomposition
	    );
	else
	    return AutomorphismGroup(L:
		Depth := Depth,
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		Stabilizer := Stabilizer,
		Generators := Generators,
		NaturalAction := NaturalAction,
		VectorsLimit := VectorsLimit,
		Vectors := Vectors,
		Decomposition := Decomposition
	    );
	end if;
    end if;
    F1, S1 := lattice_aut_preprocess_sets(L, [], [S]);
    if Vectors cmpeq 0 then
	A := InternalAutomorphismGroup(L, F1, S1 :
		Depth := Depth,
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		Stabilizer := Stabilizer,
		Generators := Generators,
		NaturalAction := NaturalAction,
		VectorsLimit := VectorsLimit
	);
    else
	A := InternalAutomorphismGroup(L, F1, S1 :
		Depth := Depth,
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		Stabilizer := Stabilizer,
		Generators := Generators,
		NaturalAction := NaturalAction,
		VectorsLimit := VectorsLimit,
		Vectors := Vectors
	);
    end if;
    return A;
end intrinsic;

intrinsic AutomorphismGroup(L::Lat, F::SeqEnum[Mtrx], S::SetEnum[Mtrx] :
   Depth := 0,
   BacherDepth := -1,
   BacherSCP := -1,	// ARGH: do not use 0!!!!!
   Stabilizer := 0,
   Generators := [],
   NaturalAction := false,
   Decomposition := false,
   VectorsLimit := -1,
   Vectors := 0
) -> GrpMat
   {The subgroup of the automorphism group of the lattice L fixing the forms
   in F individually and the forms in S setwise.}

    if #S eq 0 then
	if Vectors cmpeq 0 then
	    return AutomorphismGroup(L, F:
		Depth := Depth,
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		Stabilizer := Stabilizer,
		Generators := Generators,
		NaturalAction := NaturalAction,
		VectorsLimit := VectorsLimit
	    );
	else
	    return AutomorphismGroup(L, F:
		Depth := Depth,
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		Stabilizer := Stabilizer,
		Generators := Generators,
		NaturalAction := NaturalAction,
		VectorsLimit := VectorsLimit,
		Vectors := Vectors
	    );
	end if;
    end if;
    F1, S1 := lattice_aut_preprocess_sets(L, F, [S]);
    if Vectors cmpeq 0 then
	A := InternalAutomorphismGroup(L, F1, S1 :
		Depth := Depth,
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		Stabilizer := Stabilizer,
		Generators := Generators,
		NaturalAction := NaturalAction,
		VectorsLimit := VectorsLimit
	);
    else
	A := InternalAutomorphismGroup(L, F1, S1 :
		Depth := Depth,
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		Stabilizer := Stabilizer,
		Generators := Generators,
		NaturalAction := NaturalAction,
		VectorsLimit := VectorsLimit,
		Vectors := Vectors
	);
    end if;
    return A;
end intrinsic;

intrinsic AutomorphismGroup(L::Lat, F::SeqEnum[Mtrx], S::SeqEnum[SetEnum[Mtrx]] :
   Depth := 0,
   BacherDepth := -1,
   BacherSCP := -1,	// ARGH: do not use 0!!!!!
   Stabilizer := 0,
   Generators := [],
   NaturalAction := false,
   Decomposition := false,
   VectorsLimit := -1,
   Vectors := 0
) -> GrpMat
   {The subgroup of the automorphism group of the lattice L fixing the forms
   in F individually and the forms in S setwise.}

    if #S eq 0 or &+[#x: x in S] eq 0 then
	if Vectors cmpeq 0 then
	    return AutomorphismGroup(L, F:
		Depth := Depth,
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		Stabilizer := Stabilizer,
		Generators := Generators,
		NaturalAction := NaturalAction,
		VectorsLimit := VectorsLimit
	    );
	else
	    return AutomorphismGroup(L, F:
		Depth := Depth,
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		Stabilizer := Stabilizer,
		Generators := Generators,
		NaturalAction := NaturalAction,
		VectorsLimit := VectorsLimit,
		Vectors := Vectors
	    );
	end if;
    end if;
    F1, S1 := lattice_aut_preprocess_sets(L, F, S);
    if Vectors cmpeq 0 then
	A := InternalAutomorphismGroup(L, F1, S1 :
		Depth := Depth,
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		Stabilizer := Stabilizer,
		Generators := Generators,
		NaturalAction := NaturalAction,
		VectorsLimit := VectorsLimit
	);
    else
	A := InternalAutomorphismGroup(L, F1, S1 :
		Depth := Depth,
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		Stabilizer := Stabilizer,
		Generators := Generators,
		NaturalAction := NaturalAction,
		VectorsLimit := VectorsLimit,
		Vectors := Vectors
	);
    end if;
    return A;
end intrinsic;

intrinsic IsIsometric(L1::Lat, S1::SetEnum[Mtrx], 
    L2::Lat, S2::SetEnum[Mtrx]:
   Depth := 0,
   BacherDepth := -1,
   BacherSCP := -1,	// ARGH: do not use 0!!!!!
   LeftGenerators := [],
   RightGenerators := [],
   Decomposition := false,
   VectorsLimit := -1,
   LeftVectors := 0,
   RightVectors := 0
) -> BoolElt, Mtrx
   { True and a matrix from L1 to L2 if L1 is isometric to L2; false otherwise.
   The matrix must send set of forms S1 to S2. }

    flag, FF1, SS1, FF2, SS2 := lattice_iso_preprocess_sets(
	    L1, [], [S1], L2, [], [S2]);
    if not flag then
	return false, _;
    end if;
    if LeftVectors cmpeq 0 then
	assert RightVectors eq 0;
	fl, X := InternalIsIsometric(L1, FF1, SS1, L2, FF2, SS2 :
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		LeftGenerators := LeftGenerators,
		RightGenerators := RightGenerators,
		VectorsLimit := VectorsLimit
	);
    else
	fl, X := InternalIsIsometric(L1, FF1, SS1, L2, FF2, SS2 :
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		LeftGenerators := LeftGenerators,
		RightGenerators := RightGenerators,
		VectorsLimit := VectorsLimit,
		LeftVectors := LeftVectors,
		RightVectors := RightVectors
	);
    end if;
    if fl then
	return fl, X;
    else
	return false, _;
    end if;
end intrinsic;

intrinsic IsIsometric(L1::Lat, F1::SeqEnum[Mtrx], S1::SetEnum[Mtrx], 
    L2::Lat, F2::SeqEnum[Mtrx], S2::SetEnum[Mtrx]:
   Depth := 0,
   BacherDepth := -1,
   BacherSCP := -1,	// ARGH: do not use 0!!!!!
   LeftGenerators := [],
   RightGenerators := [],
   Decomposition := false,
   VectorsLimit := -1,
   LeftVectors := 0,
   RightVectors := 0
) -> BoolElt, Mtrx
   { True and a matrix from L1 to L2 if L1 is isometric to L2; false otherwise.
   The matrix must send forms in F1 to F2 and the set of forms S1 to S2. }

    flag, FF1, SS1, FF2, SS2 := lattice_iso_preprocess_sets(
	    L1, F1, [S1], L2, F2, [S2]);
    if not flag then
	return false, _;
    end if;
    if LeftVectors cmpeq 0 then
	assert RightVectors eq 0;
	fl, X := InternalIsIsometric(L1, FF1, SS1, L2, FF2, SS2 :
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		LeftGenerators := LeftGenerators,
		RightGenerators := RightGenerators,
		VectorsLimit := VectorsLimit
	);
    else
	fl, X := InternalIsIsometric(L1, FF1, SS1, L2, FF2, SS2 :
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		LeftGenerators := LeftGenerators,
		RightGenerators := RightGenerators,
		VectorsLimit := VectorsLimit,
		LeftVectors := LeftVectors,
		RightVectors := RightVectors
	);
    end if;
    if fl then
	return fl, X;
    else
	return false, _;
    end if;
end intrinsic;

intrinsic IsIsometric(L1::Lat, F1::SeqEnum[Mtrx], S1::SeqEnum[SetEnum[Mtrx]], 
    L2::Lat, F2::SeqEnum[Mtrx], S2::SeqEnum[SetEnum[Mtrx]]:
   Depth := 0,
   BacherDepth := -1,
   BacherSCP := -1,	// ARGH: do not use 0!!!!!
   LeftGenerators := [],
   RightGenerators := [],
   Decomposition := false,
   VectorsLimit := -1,
   LeftVectors := 0,
   RightVectors := 0
) -> BoolElt, Mtrx
   { True and a matrix from L1 to L2 if L1 is isometric to L2; false otherwise.
   The matrix must send forms in F1 to F2 and the set of forms S1 to S2. }

    flag, FF1, SS1, FF2, SS2 := lattice_iso_preprocess_sets(
	    L1, F1, S1, L2, F2, S2);
    if not flag then
	return false, _;
    end if;
    if LeftVectors cmpeq 0 then
	assert RightVectors eq 0;
	fl, X := InternalIsIsometric(L1, FF1, SS1, L2, FF2, SS2 :
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		LeftGenerators := LeftGenerators,
		RightGenerators := RightGenerators,
		VectorsLimit := VectorsLimit
	);
    else
	fl, X := InternalIsIsometric(L1, FF1, SS1, L2, FF2, SS2 :
		BacherDepth := BacherDepth,
		BacherSCP := BacherSCP,
		LeftGenerators := LeftGenerators,
		RightGenerators := RightGenerators,
		VectorsLimit := VectorsLimit,
		LeftVectors := LeftVectors,
		RightVectors := RightVectors
	);
    end if;
    if fl then
	return fl, X;
    else
	return false, _;
    end if;
end intrinsic;
