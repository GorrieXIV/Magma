freeze;

/*
 *
 * A polynomial time algorithm to solve cyclic algebra conjugacy and
 * module similarity over cyclic rings.
 *
 * Developed by Peter Brooksbank and James Wilson, 2015.
 * Based on Brooksbank and Wilson "Module isomorphism reconsidered",
 * J. Algebra, 2015.
 *
 */


/*--- Jordan form functions ---*/

/*
   Given an irreducible polynomial <p> over a field <k>,
   and a <partition>, construct the generalised Jordan
   block determined by these parameters.
   
   This is not the standard Magma form.
*/

__build_JF := function (p, partition)
     Cp := CompanionMatrix (p);
     s := #partition;
     m := &+ partition;
     k := BaseRing (Parent (p));
     d := Degree (p);
     IdBlock := Identity (MatrixAlgebra (k, d));
     JF := DiagonalJoin (< Cp : i in [1..m] >);
     mm := 1;      
     for i in [1..s] do
         mi := partition[i];
         for j in [1..mi - 1] do
	     InsertBlock (~JF, IdBlock, mm, mm + d);
             mm +:= d;
	 end for;
         mm +:= d;
     end for;
return JF;
end function;


/*
   Given a primary matrix <P>, return the generalized 
   Jordan normal form of <P> and the partition
   associated with the invariant factors of <P>
*/

__primary_JF := function (P)

     k := BaseRing (Parent (P));

     // first conjugate <P> to Magma JNF
     J, D := JordanForm (P);

     mpol := MinimalPolynomial (J);
     mfac := Factorisation (mpol);

     if (#mfac gt 1) then
        error "<P> must be primary";
     end if;
  
     p := mfac[1][1];
// THE INVARIANT FACTORS SOMETIMES DO NOT HAVE THE DIVISIBILITY PROPERTY: REPORT!!!
     ifacs := Sort (InvariantFactors (J));
     partition := [ Factorisation (ifacs[i])[1][2] : 
                                      i in [1..#ifacs] ];

     if (Degree (p) gt 1) then   
       
	 /* build the (primary) Jordan form for given parameters */
         JF := __build_JF (p, partition);
         J, C := JordanForm (JF);
         D := C^-1 * D;
         
     else

         /* My Jordan form agrees with the one used by Magma */       
         JF := J;
    
     end if;     
     
return JF, D, partition;
end function;


/* a partition ordering function */

__le_partition := function (part1, part2)
     if part1 eq part2 then return true; end if;
     if #part1 lt #part2 then return true; end if;
     if #part1 gt #part2 then return false; end if;
     i := Min ({ j : j in [1..#part1] | part1[j] ne part2[j] });
return part1[i] lt part2[i];
end function;



/*  
   Builds the generalized Jordan Normal Form of <X> with blocks 
   appearing in increasing order of min poly degree, and within 
   each min poly degree, "increasing" order of partition.

   This modification of an earlier function was written in
   Fort Collins in December, 2014.
*/

__JordanNormalForm := function (X)

     d := Nrows (X);
     k := BaseRing (Parent (X));
     mfac := Factorisation (MinimalPolynomial (X));
     degs := { Degree (mfac[i][1]) : i in [1..#mfac] };
     degs := [ m : m in degs ];
     ordered := [ [ mfac[i] : i in [1..#mfac] | Degree (mfac[i][1]) eq m ] : 
                    m in degs ];

     /* proceed sequentially through the primary components */
     info := [* *];
     basis := [ ];
     
     for j in [1..#degs] do
     
         nullspaces := [* *];
         transition_matrices := [* *];
         partitions := [* *];
         pols := [* *];
         
         for i in [1..#ordered[j]] do
	       
	         pi := ordered[j][i][1];
             Append (~pols, pi);
             ei := ordered[j][i][2];
             fi := pi^ei;   
             Xi := Evaluate (fi, X);
             Vi := Nullspace (Xi);
             Append (~nullspaces, Vi);
             di := Dimension (Vi);
           
             /* restrict <Xi> to <Vi> to get a primary matrix <Pi> */
             rows := [ Coordinates (Vi, (Vi.j) * X) : j in [1..di] ];
             Pi := Matrix (rows);
           
             Ji, Ci, parti := __primary_JF (Pi);
             Append (~transition_matrices, Ci);
             Append (~partitions, parti);
           
         end for;
     
         /* put partitions into a standard order */         
         index := { 1 .. #partitions };
         order := [ ];         
         while #order lt #partitions do
             assert exists (s){ t : t in index | 
                  forall { u : u in index | 
                               __le_partition (partitions[t], partitions[u]) } };
             Append (~order, s);
             Exclude (~index, s);
         end while;
     
         /* select basis to exhibit Jordan structure */
         for i in order do
             Ci := transition_matrices[i];
             Vi := nullspaces[i];
             di := Dimension (Vi);
             bas := [ &+ [ Ci[s][t] * Vi.t : t in [1..di] ] : s in [1..di] ];         
             basis cat:= bas;
             Append (~info, < pols[i], partitions[i] >);
         end for;
         
     end for;
     
     C := Matrix (basis);
     J := C * X * C^-1;
     
return J, C, info;    

end function;



/*----- field functions -----*/


/* analogue of "Eltseq" that allows one to specify basis */
__EltseqWithBasis := function (K, k, bas, x)
     assert #bas eq (Degree (K) div Degree (k));
     W, g := VectorSpace (K, k);
     U := VectorSpaceWithBasis ([ bas[i] @ g : i in [1..#bas] ]);
return Coordinates (U, x @ g);
end function;


/* 
  given <T> acting irreducibly on its underlying module, return 
  inverse isomorphisms from k[<T>] to the isomorphic field.
  Also return a generator for Gal(k[<T>]).
*/
__IsomorphismWithField := function (T)

     assert T ne 0;

     /* use min poly of T to build extension */
     mT := MinimalPolynomial (T);
     assert IsIrreducible (mT);
     e := Degree (mT);
     assert e eq Nrows (T);
     k := BaseRing (Parent (T));
     K := ext < k | mT >;

     /* build inverse isomorphisms */
     Kbas := [ (K.1)^i : i in [0..e-1] ];
     Tbas := [ T^i : i in [0..e-1] ];
     MS := KMatrixSpace (k, e, e);
     MS := KMatrixSpaceWithBasis ([ MS!(Tbas[i]) : i in [1..e] ]);
     EnvT := sub < Parent (T) | T >; 
     phi := hom < EnvT -> K | x :-> &+ [c[i] * Kbas[i] : i in [1..e]]
            where c := Coordinates (MS, MS!x) >;
     psi := hom < K -> EnvT | x :-> &+ [c[i] * Tbas[i] : i in [1..e]]
            where c := __EltseqWithBasis (K, k, Kbas, x) >;

     /* build Galois generator */
     /*
     J, C := JordanForm (T);
     u := VectorSpace (k, e).1;
     q := #k;
     gamma := Matrix ([ u * J^(q*i) : i in [0..e-1] ]);
     gamma := GL (e, k)!gamma;
     assert Order (gamma) eq e;
     gal := C^-1 * gamma * C;
     */

          /* sanity check */
          //assert gal * T * gal^-1 in sub < Parent (T) | T >;
     

return EnvT, K, phi, psi; 
//gal;
end function;


/*
  given <T1> and <T2> acting irreducibly on their (common) underlying module,
  return a transition matrix conjugating k[<T1>] to k[<T2>]

  This algorithm was communicated to us by W.M. Kantor.
*/
__IsomorphismBetweenFields := function (T1, T2)

     assert Nrows (T1) eq Nrows (T2);

     if Nrows (T1) eq 1 then
          return Identity (MatrixAlgebra (BaseRing (Parent (T1)), 1));
     end if;

     m1 := MinimalPolynomial (T1);
     assert IsIrreducible (m1);
     ET2, K2, phi2, psi2 := __IsomorphismWithField (T2);

     /* factor <m1> over <K2> */
     R2 := PolynomialRing (K2);
     m1K2 := R2!m1;
     roots := Roots (m1K2);

     /* take any root and pull back to ET2 */
     alpha := roots[1][1];
     assert alpha in K2;
     X2 := alpha @ psi2;
     assert MinimalPolynomial (X2) eq m1;

     /* conjugate k[<T1>] to k[<X1>] = k[<T2>] by module isomorphism */
     M1 := RModule (sub < Parent (T1) | T1 >);
     M2 := RModule (sub < Parent (X2) | X2 >);
     isit, C := IsIsomorphic (M1, M2);
     assert isit;

return C^-1;
end function;

/*----- the conjugacy test -----*/

/*
   given arbitrary <T1> and k[<T2>], determine whether or not <T1> can be
   conjugated into k[<T2>] and, if so, find a C that does the trick.
*/

__IsConjugateCyclic := function (T1, R)

     T2 := R.1;
     MA := Generic (R);
     d := Degree (MA);

     J1, C1, info1 := __JordanNormalForm (T1);
     J2, C2, info2 := __JordanNormalForm (T2);

     I1 := [ < Degree (info1[i][1]) , info1[i][2] > : i in [1..#info1] ];
     I2 := [ < Degree (info2[i][1]) , info2[i][2] > : i in [1..#info2] ];

     if I1 ne I2 then 
         //"(1)";
         return false, _; 
     end if;
     
     /* conjugate the primary components */
     pos := 1;
     blocks := < >;
     for i in [1..#info1] do
     
	  di := Degree (info1[i][1]);
          parti := info1[i][2];
     
          /* find the basic field isomorphism */
          Ti1 := ExtractBlock (J1, pos, pos, di, di);
          Ti2 := ExtractBlock (J2, pos, pos, di, di);
          Di := __IsomorphismBetweenFields (Ti1, Ti2);
     
          /* propogate basic iso to the other blocks in primary component */
          ni := &+ parti;
          Ci := DiagonalJoin (< Di : i in [1..ni] >);
          Append (~blocks, Ci);
          
          pos +:= di * ni;
     
     end for;
     
     C := DiagonalJoin (blocks);
     assert Nrows (C) eq d;
     
     C := C2^-1 * C * C1;
     if not C * T1 * C^-1 in R then
         //"(2)";
         return false, _;
     end if;

return true, C;

end function;


__IsCyclic := function (R)

//"# generators =", Ngens (R);

     if not Type (R) eq AlgMat then 
         //"input is not a matrix algebra";
         return false, _; 
     end if;

     if not IsCommutative (R) then 
         //"input is not commutative";
         return false, _; 
     end if;
     
     
     if Ngens (R) eq 1 then return true, R.1; end if;
     
     k := BaseRing (R);
     d := Degree (R);
     MA := MatrixAlgebra (k, d);
//tt := Cputime ();
     J, W := WedderburnDecomposition (R);
//"Wedderburn decomposition:", Cputime (tt);

     /* first compute what would be the 0-eigenspace of <sigma> */
     V0 := &meet [ Nullspace (W.i) : i in [1..Ngens (W)] ];
     n0 := Dimension (V0);
     
     /* find the remaining generalized eigenspaces and corresponding transition matrix */
     degrees := [ n0 ];

     M := RModule (W);
//tt := Cputime ();
     isubs := IndecomposableSummands (M);
     isubs := [ N : N in isubs | not forall{ w : w in Generators(W) | forall{ n : n in Generators(N) | (n @Morphism(N,M))*w eq N!0 } } ];
//"Indecomposable summands:", Cputime (tt);
     subs := [ ];
//tt := Cputime ();
     while #isubs gt 0 do
         N := isubs[1];
         U := N;
         while exists (j){ i : i in [1..#isubs] | IsIsomorphic (N, isubs[i]) } do
             U +:= isubs[j];
             Remove (~isubs, j);
         end while;
         Append (~subs, U);
     end while;
     degrees cat:= [ Dimension (subs[i]) : i in [1..#subs] ];
     basis := &cat [ [ M!(subs[i].j) : j in [1..Ngens (subs[i])] ] : i in [1..#subs] ];
     C := Matrix (basis);
//"Transition matrix:", Cputime (tt);
    
     JC := sub < MA | [ C * J.i * C^-1 : i in [1..Ngens (J)] ] >;
     WC := sub < MA | [ C * W.i * C^-1 : i in [1..Ngens (W)] ] >;
     
     /* build central primitive idempotents for <WC> */
//tt := Cputime ();
     idempotents := [ ];
     z := MA!0;
     pos := 1;
     for i in [1..#degrees] do
        Append (~idempotents, 
           InsertBlock (z, Identity (MatrixAlgebra (k, degrees[i])), pos, pos));
        pos +:= degrees[i];
     end for;
//"Primitive idempotents:", Cputime (tt);
     
     /* build semisimple part of <sigma> */
//tt := Cputime ();
     sigma := MA!0;
     pos := 1 + degrees[1];
     polys := [ ];
     for i in [2..#degrees] do
         ni := degrees[i];
         /* build the algebra induced by the (i-1)-th min ideal on its support */
         S := sub < MatrixAlgebra (k, ni) | [ ExtractBlock (WC.j, pos, pos, ni, ni) :
						    j in [1..Ngens (WC)] ] >;
         dS := Dimension (S);
         if exists (s){ t : t in S | Degree (MinimalPolynomial (t)) eq dS
		       //                  and t ne 0 
                  and not MinimalPolynomial (t) in polys } then
             InsertBlock (~sigma, s, pos, pos);
             Append (~polys, MinimalPolynomial (s));
         else
             //"could not build the semisimple part of <sigma>";
            return false, _;
         end if;
         pos +:= ni;
     end for;
//"Semisimple part:", Cputime (tt);
//"polys =", polys;
//tt := Cputime ();
//     assert sigma in WC;    
//"Sanity check 1:", Cputime (tt);

     /* build nilpotent part of <sigma> */
//tt := Cputime ();
     nsigma := MA!0;
     for i in [1..#degrees] do
         ni := degrees[i];
         ei := idempotents[i];
         Ji := sub < MA | [ ei * JC.j * ei : j in [1..Ngens (JC)] ] >;
         if Dimension (Ji) gt 0 then
              classes := [ ];
              for j in [1..Ngens (Ji)] do
                 isit, c := IsNilpotent (Ji.j);
                 assert isit;
                 Append (~classes, c);
              end for;        
              mi := Max (classes);
              assert exists (ui){ Ji.j : j in [1..Ngens (Ji)] |
                        forall { c : c in [1..mi-1] | Ji.j^c ne 0 } };
              nsigma +:= ui;
         end if;
     end for;
//"Nilpotent part:", Cputime (tt);     

     /* add together the nilpotent and semisimple parts */
     sigma +:= nsigma;
     
     /* if <R> is Env(<tau>) for some <tau>, then <R> is Env(<sigma>): check */
     sig := C^-1 * sigma * C;
//tt := Cputime ();
     assert sig in R;
//"Sanity check 2:", Cputime (tt);

//tt := Cputime ();
     isit := sub < MA | [ sig , Identity (MA) ] > eq R;   
//"Sanity check 3:", Cputime (tt); 
     if isit then
         return true, sig;
     else
         //"a candidate <sigma> was built but it doesn't generate";
         return false, _;
     end if;

return true, sig;

end function;


intrinsic IsCyclic( R::AlgMat ) -> BoolElt, AlgAssElt
{Decide if the algebra is generated by a single element, and return such a generator.}
	return __IsCyclic(R);
end intrinsic;

/*
intrinsic IsCyclic( R::AlgAss ) -> BoolElt, AlgAssElt
{Decide if the algebra is generated by a single element, and return such a generator.}
	
	// Convert into it regular representation.
	d := Dimension(R);
	B := Basis(R);
	mats := [];
	g := [];
	MA := MatrixAlgebra(BaseRing(R), d);
	for i in [1..Ngens(R)] do
		X := MA![ x*R.i : x in B ];
		Append(~mats, X);
		Append(~g, <X,R.i> );
	end for;
	Rmat := sub< MA | mats >;
	ghom := hom<Rmat->R | g >;

	b, sig := __IsCyclic( Rmat );
	if not b then
		return b, _;
	else
		return true, sig @ ghom;
	end if;
end intrinsic;
*/


intrinsic IsSimilar( M::ModRng, N::ModRng ) -> BoolElt, Map
{Decides if the given modules are similar; requires a cyclic coefficient ring.}
	A := Action(M);
	cyc, genA := IsCyclic(A);
	if not cyc then
		return false, _;
	end if;
	B := Action(N);
	cyc, genB := IsCyclic(B);
	if not cyc then 
		return false, _;
	end if;
	cycB := sub<Generic(B)| [genB] >;
	return __IsConjugateCyclic(genA, cycB);
//	if test then
//		f := hom<M->N | x:->N!(Vector(x)*X), y:->M!(Vector(y)*X^(-1)) >;
//		return true, f;
//	end if;
	return false, _;
end intrinsic;

