freeze;

declare verbose AlgLieRecog, 2;

//
//  SemisimpleType( <L> )
//
//  This function works for Lie algebras over a field of characteristic not
//  2 or 3, having a nondegenerate Killing form. Such Lie algebras are
//  semisimple. They are characterized as direct sums of simple Lie algebras,
//  and these have been classified: a simple Lie algebra is either an element
//  of the "great" classes of simple Lie algebas (A_n, B_n, C_n, D_n), or
//  an exceptional algebra (E_6, E_7, E_8, F_4, G_2). This function finds
//  the type of the semisimple Lie algebra L. Since for the calculations
//  eigenvalues and eigenvectors of the action of a Cartan subalgebra are
//  needed, we reduce the Lie algebra mod p (if it is of characteristic 0).
//  The p may not divide the determinant of the matrix of the Killing form,
//  nor may it divide the last nonzero coefficient of a minimum polynomial
//  of an element of the basis of the Cartan subalgebra.
//

intrinsic SemisimpleType( L::AlgLie: Check := true) -> MonStgElt
{The Cartan type of a semisimple Lie algebra}

    vprint AlgLieRecog: "Determine SemisimpleType for:", L;

    // AKS Aug 12:
    if IsSimple(L) then
	L`IsSemisimple := true;
    end if;

    if assigned L`RootDatum then
      L`SemisimpleType := CartanName( L`RootDatum );
    end if;
    if assigned L`SemisimpleType then 
      return L`SemisimpleType;
    end if;

    F:= CoefficientRing( L );
	if Characteristic(F) in {2,3} then
		/* Use special code -- definitely better than nothing */
		try
			R := ReductiveType(L);
		catch e
			error "Could not find semisimple type for this Lie algebra over a field of characteristic",  Characteristic(F);
		end try;
		return CartanName(R);
	end if;
    require Dimension( L ) gt 0 : "The dimension of L must be > 0.";

    if Check then
	// We test whether the Killing form of L is nondegenerate.

	vprint AlgLieRecog: "Get KillingMatrix and its determinant";
	vtime AlgLieRecog:
	d := Determinant(KillingMatrix(L));
	require not IsZero(d): "The Killing form of L is degenerate.";
	vprint AlgLieRecog: "Determinant is non-zero";
    end if;

    // check whether the CSA of L happens to be split:


    vprint AlgLieRecog: "Get CartanSubalgebra of L";
    vtime AlgLieRecog:
	H := CartanSubalgebra( L );

    rk:= Dimension(H);
    vprint AlgLieRecog: "CartanSubalgebra dim:", rk;

    split:= true; 
    k:= 1;
    while split and k le rk do
          fcs := FactoredCharacteristicPolynomial(AdjointMatrix(L, H.k));
          split := &and[ Degree(f[1]) eq 1: f in fcs];
          k +:= 1;
    end while;
    vprint AlgLieRecog: "split:", split;
    if split then 
	_,_,_, C := RootSystem(L);
	return CartanName( C ); 
    end if;     

    // For infinite fields, check whether the structure constants lie in 
    // the prime field:

    n:= Dimension(L);
    if not IsFinite(F) then
       PF:= PrimeField( F );  
       bp:= BasisProducts( L );
       isprime:= true;
       for i in [1..n] do
           if not isprime then break; end if;
           for j in [1..n] do
	       if not isprime then break; end if;
               for k in [1..n] do
                   if not isprime then break; end if;
                   isprime:= bp[i][j][k] in PF;
               end for;
           end for; 
       end for;
       require isprime : "The structure constants of L have to lie in the prime field of the field of definition";
    end if;

    // First we produce a basis of L such that the first basis elements
    // form a basis of a Cartan subalgebra of L. Then if L is defined
    // over a field of characteristic 0 we do the following. We multiply
    // by an integer in order to ensure that the structure constants
    // are integers. Finally we reduce modulo an appropriate prime p.

    vprint AlgLieRecog: "Extend Cartan subalgebra basis";
    bas:= [ L!H.i : i in [1..rk] ];
    V:= VectorSpace( F, n );
    W:= sub< V | [ V!Eltseq(L!H.i) : i in [1..rk] ] >;
    k:= 1;
    vtime AlgLieRecog:
    while #bas lt n do
	if not V!Eltseq( L.k ) in W then
	  Append( ~bas, L.k );
	  W:= sub< V | [ V!Eltseq(bas[i]) : i in [1..#bas] ] >;
	end if;
	k:= k+1;
    end while;

    W:= VectorSpaceWithBasis([ V | V!Eltseq(bas[i]) : i in [1..n] ]);
   
    T := 0;
    if 0 eq 1 then
	// Old slow version
	vprint AlgLieRecog: "Compute new T constants"; 
	T:=[ Zero(F) : i in [1..n^3]];
	n2 := n^2;
	vtime AlgLieRecog:
	for i in [1..n] do
	    for j in [i+1..n] do
		y := bas[i]*bas[j];
		cf := Coordinates(W, V!Eltseq(y));
		ind1 := (i-1)*n2 + (j-1)*n;
		ind2 := (j-1)*n2 + (i-1)*n;
		for k in [1..n] do
		    T[ind1 + k] := cf[k];
		    T[ind2 + k] := -cf[k];
		end for;
	    end for;
	end for;
    end if;

    B := Matrix(bas);
    inv := B^-1;
    vprint AlgLieRecog: "Compute new T constants via matrices";
    vtime AlgLieRecog:
    mat := [B*LeftMultiplicationMatrix(bas[i])*inv: i in [1 .. n]];
    //"mat:", mat; "T:", T;
    mat := &cat [Eltseq(x): x in mat];
    assert T cmpeq 0 or T eq mat;
    T := mat;

    p:= Characteristic( F );

    if p eq 0 then

      denoms:= [ ];
      for i in [1..n^3] do
        if T[i] ne 0 then den:= Denominator( T[i] );
                     else den:= 1;
        end if;
        if (den ne 1) and (not den in denoms) then
          Append( ~denoms, den );
        end if;
      end for;

      if denoms ne [] then scal:= LCM( denoms );
                      else scal:= 1;
      end if;

      S:= [ scal*T[i] : i in [1..n^3] ];

      K:= LieAlgebra<F, n | S: Check := false>;

      d:= Determinant( KillingMatrix( K ) );
      mp:= [ CharacteristicPolynomial( AdjointMatrix( K, K.i ) ) : 
                            i in [1..rk] ];
      for i in [1..rk] do
        cf:= Coefficients( mp[i] );
        k:=1;
        while cf[k] eq 0 do k:=k+1; end while;
        d:= d*cf[k];
      end for;

      p:= 5;

      // We determine a prime p>=5 not dividing d and the splitting
      // field of the Cartan subalgebra over F_p.

      d:= IntegerRing()!d;
      while d mod p eq 0 do
        p:= NextPrime( p );
      end while;

      G:= GF( p );
      R:= PolynomialRing( G );
      ff:= R!Coefficients( LCM( mp ) );
      F:= SplittingField( ff );
      S:= [ F!S[i] : i in [1..n^3] ];

    else

	// Here L is defined over a field of characteristic p>0. We determine
	// a splitting field for the Cartan subalgebra.

	vprint AlgLieRecog: "Determine Cartan subalgebra splitting field";

	K := LieAlgebra< F, n | T: Check := false>;

	if 1 eq 1 then
	    vprint AlgLieRecog: "Use Module method; get module";
	    vtime AlgLieRecog: M := ActionModule(L, 1);

	    vprint AlgLieRecog: "Check simplicity";
	    vtime AlgLieRecog: assert IsIrreducible(M);

	    vprint AlgLieRecog: "Get endo ring dim";
	    vtime AlgLieRecog: edeg := DimensionOfEndomorphismRing(M);

	    vprint AlgLieRecog: "Extension degree:", edeg;

	    F := ext<F | edeg>;
	else
	    mp := { CharacteristicPolynomial( AdjointMatrix( K, K.i ) ) : 
				i in [1..rk] };
	    F := SplittingField( LCM( mp ) );
	end if;

	vprint AlgLieRecog: "SplittingField:", F;

	//S:= [ F!T[i] : i in [1..n^3] ];
	vprint AlgLieRecog: "Change constants universe; length", #T;
	vtime AlgLieRecog:
	    S := ChangeUniverse(T, F);
	delete T;

    end if;

    K := LieAlgebra< F, n | S: Check := false>;

    // We already know a Cartan subalgebra of K.

    H := sub< K | [ K.i : i in [1..rk] ] : Basis >;
    K`CartanSubalgebra:= H;
    
    mv := GetVerbose("Meataxe");
    if false and Dimension(K) gt 50 then
	vprint AlgLieRecog: "Turn Meataxe verbose on";
	SetVerbose("Meataxe",1);
    end if;

    vprint AlgLieRecog: "Get DirectSumDecomposition of:", K;
    IndentPush();
    vtime AlgLieRecog:
	simples:= Decomposition( K );
	//simples:= DirectSumDecomposition( K );
    IndentPop();

    vprint AlgLieRecog: "Simples:", simples;
    SetVerbose("Meataxe", mv);

    types:= "";

    // Now for every simple Lie algebra in simples we have to determine
    // its type.
    // For Lie algebras not equal to B_l, C_l or E_6,
    // this is determined by the dimension and the rank.
    // In the other cases we have to examine the root system.

    for l in [1..#simples] do

	I := simples[l];

I`IsSemisimple := true; // Avoid stupidities later

	if types ne "" then types cat:= " "; end if;
   
	HI := H meet I;
	rk := Dimension( HI );

	vprintf AlgLieRecog: "%o: I dim: %o, H meet I dim: %o\n",
	  l, Dimension(I), rk;

	if Dimension( I ) eq 133 and rk eq 7 then
	    types cat:= "E7";
	elif Dimension( I ) eq 248 and rk eq 8 then
	    types cat:= "E8";
	elif Dimension( I ) eq 52 and rk eq 4 then
	    types cat:= "F4";
	elif Dimension( I ) eq 14 and rk eq 2 then
	    types cat:= "G2"; 
	else
	    if Dimension( I ) eq rk^2 + 2*rk then
		types cat:= "A"; types cat:= IntegerToString( rk );
	    elif Dimension( I ) eq 2*rk^2-rk then
		types cat:= "D"; types cat:= IntegerToString( rk );
	    elif Dimension( I ) eq 10 then
		types cat:= "B2";
	    else
		I`CartanSubalgebra:= HI;

		// We now determine the Cartan matrix of the root system.

		_,_,_,CM:= RootSystem( I ); 

		// Finally the properties of the endpoints determine
		// the type of the root system.

		endpts:= [ Integers() | ];
		for i in [ 1 .. Nrows(CM) ] do
		    nn:= 0;
		    for j in [1..Ncols(CM)] do
			if CM[i][j] ne 0 then nn +:=1; end if;
		    end for;
		    if nn eq 2 then
			Append( ~endpts, i );
		    end if;
		end for;

		if #endpts eq 3 then
		    types cat:= "E6";
		elif &+Eltseq(CM[ endpts[1] ]) eq 0 or
		    &+Eltseq(CM[ endpts[2]]) eq 0
		then
		    types cat:= "C"; types cat:= IntegerToString(rk);
		else
		    types cat:= "B"; types cat:= IntegerToString(rk);
		end if;

	    end if;
	end if;
    end for;

    L`SemisimpleType:= types;
    return types;

end intrinsic;


intrinsic CartanName( L::AlgLie ) -> MonStgElt
{The Cartan name of the reductive Lie algebra L}
  return SemisimpleType( L/Centre(L) );
end intrinsic;


