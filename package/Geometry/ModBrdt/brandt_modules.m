freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //  
//                    Brandt Modules of Quaternions                   // 
//                            David Kohel                             // 
//                           Created 2000                             //
//                    Last modified January 2001                      //
//                                                                    // 
////////////////////////////////////////////////////////////////////////

declare verbose Brandt, 2;

import "brandt_ideals.m" : ExtendAdjacencyHecke;
//import "../../Lattice/Lat/auto.m" : IsIsometricS;

IsIsometricS := IsIsometric;

forward ExtendHecke;

////////////////////////////////////////////////////////////////////////
//                                                                    // 
//                       Attribute declarations                       //
//                                                                    // 
////////////////////////////////////////////////////////////////////////

declare type ModBrdt [ModBrdtElt];

declare attributes ModBrdt:
    Module,          // inner product module of brandt module
    Degree,          // the degree r of the symmetric product Sym^r(I)
    BaseRing,        // the base ring
    LeftIdeals,
    IsIndecomposable,
    IsFull,          // either IsFull, or 
    AmbientModule,   //    AmbientModule must be defined 
    RamifiedPrimes,  // primes ramified of the quaternion algebra 
    Conductor,       // index of the order in a maximal order
    AutoNums,        // the numbers of units  
    NormGrams,       // quadratic norm lattices of ideals 
    ThetaSeries,     // theta series for the quadratic modules 
    HeckePrecision,  // Hecke operators are known for primes p up to this
    HeckePrimes,     // primes indices for known operators
    HeckeOperators,  // known hecke operators
    AtkinLehnerPermutations,  // The sequences of coordinate 
       // permutations defining the Atkin-Lehner operators
    AtkinLehnerPrimes,  // the prime divisors of the level
    FactorBases,
    FactorIsIndecomposable, 
    DecompositionBound;

declare type ModBrdtElt;

declare attributes ModBrdtElt:
    Parent,
    Element;

////////////////////////////////////////////////////////////////////////
//                                                                    // 
//                         Creation functions                         // 
//                                                                    //
////////////////////////////////////////////////////////////////////////

function HeckeMatrix(A,S,W)
    n := Degree(A);
    M := Zero(A);
    k := 1;
    for i in [1..n] do 
	M[i,i] := ExactQuotient(S[k],W[i]);
	k +:= 1;
	for j in [i+1..n] do 
	    M[i,j] := ExactQuotient(S[k],W[j]);
	    M[j,i] := ExactQuotient(S[k],W[i]);
	    k +:= 1;
	end for;
    end for;
    return M;
end function;

intrinsic BrandtModule(D::RngIntElt : ComputeGrams := true) -> ModBrdt
    {The Eichler-Brandt quaternion ideal divisor group.}

    prms := PrimeDivisors(D);
    require &*prms eq D and #prms mod 2 eq 1 : 
        "Argument must be a product of an odd number of primes.";
    A := QuaternionOrder(D);
    return BrandtModule(A,Integers() : ComputeGrams := ComputeGrams);
end intrinsic;

intrinsic BrandtModule(D::RngIntElt,m::RngIntElt : 
    ComputeGrams := true) -> ModBrdt
    {The Eichler-Brandt quaternion ideal divisor group.}

    prms := PrimeDivisors(D);
    require Max([ Valuation(D,p) : p in prms ]) le 1 :
        "Argument 1 can have valuation at most 1 at each prime.";
    require Max([ Valuation(m,p) : p in prms ]) le 1 :
        "Argument 2 can have valuation at most 1 
        at each prime divisor of argument 2.";
    A := QuaternionOrder(D,m);
    return BrandtModule(A,Integers() : ComputeGrams := ComputeGrams);
end intrinsic;

function NormGramsOrder(A);
    left_ideals := LeftIdealClasses(A);
    auto_nums := [ Integers() | ];
    norm_grams := [ MatrixAlgebra(Integers(),4) | ];
    k := 1;
    h := #left_ideals; 
    vprint Brandt : "Computing row entries...";
    for i in [1..h] do
	norm_grams[k] := 
	    ReducedGramMatrix(RightOrder(left_ideals[i]) );
	auto_nums[i] := 2*#ShortestVectors(
	    LatticeWithGram(norm_grams[k]));
  	RI := Conjugate(left_ideals[i]);
	k +:= 1;
	for j in [(i+1)..h] do
	    J := RI*left_ideals[j];
	    norm_grams[k] := Norm(J)^-1 * ReducedGramMatrix(J); 
	    k +:= 1;
	end for;
	if h ge 10 and i lt 10 then vprintf Brandt : " "; end if;
	if h ge 100 and i lt 100 then vprintf Brandt : " "; end if;
	if h ge 1000 and i lt 1000 then vprintf Brandt : " "; end if;
	vprintf Brandt : "%o ", i;
	if i mod 16 eq 0 then vprint Brandt : ""; end if;
    end for;
    if h mod 16 ne 0 then vprint Brandt, 2 : ""; end if;
    return norm_grams, auto_nums;
end function;

intrinsic BrandtModule(A::AlgQuatOrd : ComputeGrams := true) -> ModBrdt
    {The Eichler-Brandt quaternion ideal divisor group.}
    return BrandtModule(A,Integers() : ComputeGrams := ComputeGrams);
end intrinsic;

intrinsic BrandtModule(A::AlgQuatOrd,R::Rng :
    ComputeGrams := true) -> ModBrdt
    {The Eichler-Brandt quaternion ideal divisor group.}
    M := New(ModBrdt);
    M`IsFull := true;
    M`RamifiedPrimes := RamifiedPrimes(QuaternionAlgebra(A));
    M`Conductor := Level(A);
    M`BaseRing := R;
    if not ComputeGrams then 
	M`LeftIdeals := LeftIdealClasses(A);
	M`AutoNums := [ #Units(RightOrder(I)) : I in M`LeftIdeals ];
    else
	M`NormGrams, M`AutoNums := NormGramsOrder(A);
    end if;
    M`HeckePrecision := 1;
    M`ThetaSeries := [ LaurentSeriesRing(R) | ];
    M`HeckePrimes := [ Integers() | ];
    h := #M`AutoNums;
    MatR := MatrixAlgebra(R,h);
    M`HeckeOperators := [ MatR | ];
    M`Module := RSpace(R,h,DiagonalMatrix(MatR, 
                           [ w div 2 : w in M`AutoNums ]) );
    return M; 
end intrinsic;

function NormGramsGroupoid(G);
    A := Order(G,1);
    auto_nums := [ Integers() | ];
    norm_grams := [ MatrixAlgebra(Integers(),4) | ];
    k := 1;
    h := ClassNumber(G);
    for i in [1..h] do
	norm_grams[k] := ReducedGramMatrix(Order(G,i));
	auto_nums[i] := 2*#ShortestVectors(
                          LatticeWithGram(norm_grams[k]));
        k +:= 1;
	for j in [(i+1)..h] do
	    J := Ideal(G,[i,j]);
	    norm_grams[k] := Norm(J)^-1 * ReducedGramMatrix(J); 
	    k +:= 1;
	end for;
    end for;
    return norm_grams, auto_nums;
end function;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           Coercions                                //
//                                                                    // 
////////////////////////////////////////////////////////////////////////

function init_bool_ModBrdtElt(M,v)
    val, v := IsCoercible(M`Module,Eltseq(v));
    if not val then 
	x := "Invalid coercion"; 
    else 
	x := New(ModBrdtElt);
	x`Parent := M;
	x`Element := v;
    end if;
    return val, x;
end function;

intrinsic IsCoercible(M::ModBrdt,s::.) -> BoolElt, ModBrdtElt
    {}
    if Type(s) eq ModBrdtElt then
	N := Parent(s); 
	if M eq N then
	    return true, s;
	end if;
	A := AmbientModule(M);   
	if A eq AmbientModule(N) then
	    v := A`Module!s`Element;
	    if v in M`Module then
		return init_bool_ModBrdtElt(M,s);
	    end if;
	end if;
    elif Type(s) eq ElementType(M`Module) then
	if s in M`Module then
	    return init_bool_ModBrdtElt(M,s);
	end if;  
    elif Type(s) eq SeqEnum and #s eq Degree(M) then
	R := Universe(s);
	if Type(R) eq RngInt or R eq BaseRing(M) then
	    return init_bool_ModBrdtElt(M,s);
	end if; 
    end if;
    return false, "Invalid coercion";
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           Printing                                 //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Print(M::ModBrdt, level::MonStgElt)
    {}
    D := Discriminant(M);
    m := Conductor(M);
    printf 
    "Brandt module of level (%o,%o), dimension %o, and degree %o over %o", 
        D, m, Dimension(M), Degree(M), BaseRing(M);
end intrinsic;

intrinsic Print(x::ModBrdtElt, level::MonStgElt)
    {}
    printf "%o", x`Element;
end intrinsic;

intrinsic '.'(M::ModBrdt,i::RngIntElt) -> ModBrdtElt
    {The ith basis element of the Brandt module M}
    require i in [1..Dimension(M)] : 
        "Argument 2 should be in the range [1.." * 
        IntegerToString(Dimension(M)) * "]";
    return M!(M`Module).i;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                  Membership and equality testing                   //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic 'in'(x::., M::ModBrdt) -> BoolElt
    {Returns true if x is in X.}
    if Type(x) eq ModBrdtElt then
	if Parent(x) eq M then
	    return true;
	elif AmbientModule(Parent(x)) eq AmbientModule(M) then
	    return IsCoercible(M`Module,Eltseq(x));
	end if; 
    end if;
    return false;
end intrinsic;

intrinsic Parent(x::ModBrdtElt) -> ModBrdt
    {}
    return x`Parent;
end intrinsic;

intrinsic 'eq' (X::ModBrdt,Y::ModBrdt) -> BoolElt
    {True iff the Brandt modules X and Y are have the same ambient and are equal}
    if IsIdentical(X, Y) then
	return true;
    elif Degree(X) ne Degree(Y) or 
	Dimension(X) ne Dimension(Y) or 
	not IsIdentical(AmbientModule(X),AmbientModule(Y)) then
	return false;
    end if;
    dim := Dimension(X);
    M := AmbientModule(X)`Module;
    return sub< M | [ B[i] : i in [1..dim] ]
                               where B := BasisMatrix(X) > eq
           sub< M | [ B[i] : i in [1..dim] ]
                               where B := BasisMatrix(Y) >;
end intrinsic;

intrinsic 'eq' (x::ModBrdtElt,y::ModBrdtElt) -> BoolElt
    {True iff x and y belong to the same Brandt module and are equal}
    return x`Parent eq y`Parent and x`Element eq y`Element;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                          Hecke Operators                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function IsSelfDual(L)
    A := MinkowskiGramReduction(GramMatrix(L) : Canonical := true);
    B := MinkowskiGramReduction(GramMatrix(Dual(L)) : Canonical := true);
    return A eq B;
end function;

function LocalDualGram(L,q)
    Mat := MatrixAlgebra(ResidueClassRing(q), Rank(L));
    U := Kernel(Mat!GramMatrix(L));
    B := [ L!v : v in Basis(U) ] cat [ q*v : v in Basis(L) ];
    return MinkowskiGramReduction((1/q)*GramMatrix(sub< L | B >)
      : Canonical := true);
end function;

function brandt_index(i,j,h)
    if j lt i then
	return Binomial(h+1,2) - Binomial(h-j+2,2) + Abs(i-j) + 1;
    end if;
    return Binomial(h+1,2) - Binomial(h-i+2,2) + Abs(i-j) + 1;
end function;

function brandt_coordinates(k,h)
    i := 1;
    r := 1; 
    while k gt (r+h-i) do
	i +:= 1;
	r := Binomial(h+1,2) - Binomial(h-i+2,2) + 1;
    end while;
    j := i + k - r;
    return [i,j];
end function;

intrinsic AtkinLehnerPrimes(M::ModBrdt) -> SeqEnum
    {The sequence of primes for which the Atkin-Lehner operator 
    can be computed.}
    if not assigned M`AtkinLehnerPrimes then
	N := Level(M);
	D := Discriminant(M);
	prms := PrimeDivisors(N);
	admit_prms := [ p : p in prms | D mod p ne 0 or Valuation(N,p) le 2 ];
	M`AtkinLehnerPrimes := admit_prms;
    end if;    
    return M`AtkinLehnerPrimes;
end intrinsic;

procedure AtkinLehnerSetup(M)
    h := Degree(M);
    if assigned M`NormGrams then
	OrderGrams := [ M`NormGrams[k] where 
    	    k := brandt_index(i,i,h) : i in [1..h] ];
    else 
	OrderGrams := [ ReducedGramMatrix(RightOrder(I)) :
	    I in M`LeftIdeals ];
    end if;
    GramSet := SequenceToSet(OrderGrams);
    prms := AtkinLehnerPrimes(M);
    M`AtkinLehnerPermutations := [ [ i : i in [1..h] ] : p in prms ];
    for A in GramSet do
	L := LatticeWithGram(A);
	I := [ j : j in [1..h] | OrderGrams[j] eq A ];
	for t in [1..#prms] do
	    p := prms[t]; 
	    q := p^Valuation(Level(M),p); 
	    B := LocalDualGram(L,q);
	    for i in I do
		if assigned M`NormGrams then
		    K := [ brandt_index(i,j,h) : j in I ]; 
  		    Ip := [ k : k in K | M`NormGrams[k] eq B ];
		else
		    K := I;
		    /*
		    // This is currently slower than isometries
		    Ip := [ j : j in I |
		        MinkowskiGramReduction(
		            (1/Norm(I)/Norm(J)) *
			    GramMatrix(Conjugate(J) * I)
			        : Canonical := true ) eq B
				    where I := M`LeftIdeals[i]
				    where J := M`LeftIdeals[j] ];
		    */
   	            Ip := [ j : j in I | IsIsometricS(
  		        LatticeWithGram( (1/Norm(I)/Norm(J)) *
		            GramMatrix(Conjugate(J) * I)),
		        LatticeWithGram(B) )
				where I := M`LeftIdeals[i] 
                                where J := M`LeftIdeals[j] ]; 
		end if;
		// This if loop can now be deleted.
		if #Ip ne 1 then
		    vprint Brandt : "Failed to match reduced grams.";
		    vprint Brandt : "I =", I;
		    vprint Brandt : "Ip =", Ip;
		    vprint Brandt : "A =", Eltseq(A);
		    vprint Brandt : "B =", Eltseq(B);
		    if assigned M`NormGrams then
			J := [ k : k in [1..#M`NormGrams] |
			    M`NormGrams[k] eq B ];
			C := [ brandt_coordinates(k,h) : k in J ];
			vprint Brandt : "Corresponding coordinates: ";
			vprint Brandt : C;
			Lp := LatticeWithGram(B);
			Ip := [ k : k in K | 
			   IsIsomorphic(Lp,LatticeWithGram(M`NormGrams[k])) ];
			vprint Brandt : "Matches =", Ip;
			vprint Brandt : "Correct B =",
			    Eltseq(M`NormGrams[Ip[1]]);
		    else 
			Ip := [ j : j in I | IsIsometricS(
  		        LatticeWithGram( (1/Norm(I)/Norm(J)) *
		            GramMatrix(Conjugate(J) * I)),
		        LatticeWithGram(B) )
				where I := M`LeftIdeals[i] 
                                where J := M`LeftIdeals[j] ]; 
			vprint Brandt : "Matches =", Ip;
			vprint Brandt : "Correct B =",
			Eltseq(
			    MinkowskiGramReduction( 
			        1/Norm(I)/Norm(J) *
				    GramMatrix(Conjugate(J) * I)
				: Canonical := true )
				where I := M`LeftIdeals[i] 
                                    where J := M`LeftIdeals[Ip[1]] );
 	            end if;
		end if; 
		assert #Ip eq 1;
		M`AtkinLehnerPermutations[t][i] := I[Index(K,Ip[1])];
	    end for; 
	end for;  
    end for;
end procedure;

intrinsic AtkinLehnerOperator(M::ModBrdt,q::RngIntElt) -> AlgMatElt
    {The Atkin LehnerOperator W_q on the Brandt module M} 
    A := AmbientModule(M);
    N := Level(A);
    D := Discriminant(A);
    val, p, r := IsPrimePower(q);
    require val : "Argument 2 must be a prime power.";
    require p in AtkinLehnerPrimes(M) : 
        "Atkin-Lehner operator does not exist " * 
        "or is not computed for this prime.";
    // Convenient convention to ask for the Atkin-Lehner operator 
    // by the prime instead of the prime power.
    if r eq 1 then 
	r := Valuation(N,p);
	q := p^r;
    end if;
    require r eq Valuation(N,p) :  
        "Argument 2 must be an exact divisor of the level of argument 1.";
    if not assigned A`AtkinLehnerPermutations then
	AtkinLehnerSetup(A);
    end if;
    // Create Atkin-Lehner matrix for A.
    h := Dimension(A);
    W := MatrixAlgebra(BaseRing(A),h)!0;
    k := Index(A`AtkinLehnerPrimes,p);
    pi := A`AtkinLehnerPermutations[k];
    eps := D mod p eq 0 select -1 else 1;
    for i in [1..h] do
	W[i,pi[i]] := eps;
	W[pi[i],i] := eps;
    end for;
    // Reconstruct Atkin-Lehner matrix for M.
    g := Dimension(M);
    U := M`Module;
    C := BasisMatrix(U)*W;
    return Matrix(g,g, &cat[ Coordinates(U,U!C[i]) : i in [1..g] ]);
end intrinsic;

function HeckeRecursion(ap,p,r,k,e)
    if r eq 0 then
	return Parent(ap)!1;
    elif r eq 1 then
	return ap;
    else 
	return ap * HeckeRecursion(ap,p,r-1,k,e) - 
   	    e * p^(k-1) * HeckeRecursion(ap,p,r-2,k,e);
    end if;
end function;

intrinsic HeckeTrace(M::ModBrdt,q::RngIntElt : Proof := true) -> RngElt
    {The trace of the q-th Hecke operator on M, for prime power q.}
    val, p, r := IsPrimePower(q); 
    require val : "Argument 2 must be a prime power.";
    g := Dimension(M);
    if q eq 1 then
	return BaseRing(M)!g;
    elif IsPrime(q : Proof := false) then
	return Trace(HeckeOperator(M,q));
    end if;
    Tp := HeckeOperator(M,p);
    fp := CharacteristicPolynomial(Tp : Al := "Modular", Proof := Proof); 
    R<ap> := quo< Parent(fp) | fp >;
    // k := Weight(M);
    k := 2; 
    // e := Evaluate(DirichletCharacter(M),p);
    e := 1; 
    return Trace(HeckeRecursion(ap,p,r,k,e));
end intrinsic;

intrinsic HeckeOperator(M::ModBrdt,n::RngIntElt) -> AlgMatElt
    {The Hecke operator T_n on the Brandt module M} 
    require n ge 1 : "Argument 2 must be positive.";
    if n eq 1 then
	return Identity(Universe(M`HeckeOperators));
    elif IsPrime(n : Proof := false) then
	if n in M`HeckePrimes then
	    return M`HeckeOperators[Index(M`HeckePrimes,n)];
	end if;
    elif IsPrimePower(n) then
	// k := Weight(M);
	// e := Evaluate(DirichletCharacter(M),p);
	k := 2; 
	e := 1; 
	_, p, r := IsPrimePower(n); 
	// Testing purposes: what happens at theses primes?
	if Level(M) mod p eq 0 then
	    // By design, only computes up to Hecke operators 
	    // previous largest prime
	    ExtendHecke(M,n);
	    B := BasisMatrix(M);
	    A := AmbientModule(M);
	    T := HeckeMatrix(MatrixAlgebra(BaseRing(A),Degree(A)),
	        [ Coefficient(f,n) : f in A`ThetaSeries ], A`AutoNums);
	    U := M`Module; 
	    g := Dimension(M);
	    return Matrix([ Coordinates(U,U!(B[i]*T)) : i in [1..g] ]);
	end if;
	return HeckeOperator(M,p) * HeckeOperator(M,p^(r-1)) - 
    	    e * p^(k-1) * HeckeOperator(M,p^(r-2));
    end if;
    fac := Factorization(n);
    m := fac[#fac][1];
    if m notin M`HeckePrimes then 
	if assigned AmbientModule(M)`NormGrams then
	    ExtendHecke(M,m);
	else
	    ExtendAdjacencyHecke(M,[f[1] : f in fac]);
	end if;
    end if;
    return &*[ HeckeOperator(M,f[1]^f[2]) : f in fac ];
end intrinsic;

intrinsic ThetaSeries(
    u::ModBrdtElt, v::ModBrdtElt, prec::RngIntElt) -> RngSerElt
    {The value of the theta series pairing.}
    M := Parent(u);
    require M eq Parent(v) : "Arguments have different parents.";
    A := AmbientModule(M);
    if M ne A then
	return ThetaSeries(A!u, A!v, prec);
    end if;
    h := Dimension(M);
    if A`HeckePrecision lt prec then 
	ExtendHecke(A,prec); 
    end if;
    PS := Universe(A`ThetaSeries);  
    f := PS!0;
    c1 := Eltseq(u); c2 := Eltseq(v);
    for i in [1..h] do
	k := Binomial(h+1,2) - Binomial(h-i+2,2) + 1;
	c := c1[i]*c2[i];
	if c ne 0 then f +:= c1[i]*c2[i]*A`ThetaSeries[k]; end if;
	for j in [i+1..h] do
	    k := Binomial(h+1,2) - Binomial(h-i+2,2) + j-i+1;
	    c := c1[i]*c2[j] + c1[j]*c2[i];
	    if c ne 0 then f +:= c*A`ThetaSeries[k]; end if;
	end for;
    end for;
    return f + O(PS.1^(prec+1));
end intrinsic;

procedure ExtendHecke(M,prec)
    if prec le M`HeckePrecision then return; end if;
    if IsFull(M) then
	h := Dimension(M);
	PS := Universe(M`ThetaSeries);
	k := 1; 
	for i in [1..h] do
	    M`ThetaSeries[k] := PS![ Coefficient(t,2*k) : k in [0..prec] ]
	        where t is ThetaSeries(LatticeWithGram(M`NormGrams[k]),2*prec);
	    k +:= 1;
	    for j in [i+1..h] do
		M`ThetaSeries[k] := PS![ Coefficient(t,2*k) : k in [0..prec] ]
		where t is ThetaSeries(LatticeWithGram(M`NormGrams[k]),2*prec);
		k +:= 1;
	    end for;
	end for;
	M`HeckePrimes := [ t : t in [2..prec] | IsPrime(t) ];
	M`HeckeOperators := [
	HeckeMatrix(MatrixAlgebra(BaseRing(M),h),
   	    [ Coefficient(f,t) : f in M`ThetaSeries ], M`AutoNums)
	    : t in M`HeckePrimes ];
	M`HeckePrecision := prec;
    else 
	X := AmbientModule(M); 
	ExtendHecke(X,prec);
	// The submodules get created and destroyed with frequency.
	// Only compute Hecke operators from the ambient module up
	// to the needed precision. 
	g := Dimension(M);
	M`HeckePrimes := [ p : p in X`HeckePrimes | p le prec ];
	U := M`Module; 
	B := BasisMatrix(M);
	M`HeckeOperators := [
   	    Matrix([ Coordinates(U,U!(B[i]*T)) : i in [1..g] ])
	    : T in X`HeckeOperators[1..#M`HeckePrimes] ];
	M`HeckePrecision := prec;
   end if;
end procedure;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                      Attribute Access Functions                    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic IsFull(M::ModBrdt) -> BoolElt
    {True iff M is equal to AmbientModule(M).}
    return M`IsFull;
end intrinsic;

intrinsic IsAmbient(M::ModBrdt) -> BoolElt
    {"} // "
    return M`IsFull;
end intrinsic;

intrinsic AmbientModule(M::ModBrdt) -> ModBrdt
    {The ambient module of the Brandt module M}
    if assigned M`AmbientModule then
	return M`AmbientModule;
    end if;
    return M;
end intrinsic;

intrinsic Dimension(M::ModBrdt) -> RngIntElt
    {The dimension of the Brandt module M}
    return Dimension(M`Module);
end intrinsic;

intrinsic Degree(M::ModBrdt) -> RngIntElt
    {The dimension of the ambient module of the Brandt module M}
    return Dimension(AmbientModule(M));
end intrinsic;

intrinsic Norm(x::ModBrdtElt) -> RngElt
    {The norm of the Brandt module element x}
    return Norm(x`Element);
end intrinsic;

intrinsic GramMatrix(M::ModBrdt) -> AlgMatElt
    {The Gram matrix of the Brandt module M}
    return GramMatrix(M`Module); 
end intrinsic;

intrinsic InnerProductMatrix(M::ModBrdt) -> AlgMatElt
    {The inner product on the Brandt module M}
    return InnerProductMatrix(M`Module); 
end intrinsic;

intrinsic InnerProduct(x::ModBrdtElt,y::ModBrdtElt) -> RngElt
    {The inner product of Brandt module elements x and y}
    return InnerProduct(x`Element,y`Element);
end intrinsic;

intrinsic Conductor(M::ModBrdt) -> RngIntElt
    {The conductor of the Brandt module M}
    return M`Conductor;
end intrinsic;

intrinsic Discriminant(M::ModBrdt) -> RngIntElt
    {The discriminant of the order associated to the Brandt module M}
    return &*M`RamifiedPrimes; 
end intrinsic;

intrinsic Level(M::ModBrdt) -> RngIntElt
    {The level of the Brandt module M}
    return Discriminant(M)*Conductor(M);
end intrinsic;

intrinsic BaseRing(M::ModBrdt) -> Rng
    {The base ring of the Brandt module M}
    return M`BaseRing;
end intrinsic;

intrinsic Basis(M::ModBrdt) -> SeqEnum
    {A basis for M.}
    return [ M!x : x in Basis(M`Module) ];
end intrinsic;

intrinsic Eltseq(x::ModBrdtElt) -> SeqEnum
    {For internal use}
    return Eltseq(x`Element);
end intrinsic;

intrinsic BaseExtend(M::ModBrdt,R::Rng) -> ModBrdt
    {The base extension of the Brandt module M to R}
    N := New(ModBrdt);
    if M`IsFull then
	N`IsFull := true;
	N`RamifiedPrimes := M`RamifiedPrimes;
	N`Conductor := M`Conductor;
	N`BaseRing := R;
	N`AutoNums := M`AutoNums;
	N`NormGrams := M`NormGrams;
	N`ThetaSeries := [ PowerSeriesRing(R) | f : f in M`ThetaSeries ];
	N`HeckePrimes := M`HeckePrimes;
	N`HeckeOperators := [ MatrixAlgebra(R,Dimension(M))!T : 
	T in M`HeckeOperators ];
    else
	N`IsFull := false;
	N`AmbientModule := BaseExtend(AmbientModule(M),R);
	N`RamifiedPrimes := M`RamifiedPrimes;
	N`Conductor := M`Conductor;
	N`BaseRing := R;
    end if;
    N`Module := BaseExtend(M`Module,R);
    return N; 
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                    Arithmetic operations, etc.                     //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function init_ModBrdtElt(M,v)
    // _, v := IsCoercible(Representation(M),v);
    x := New(ElementType(M));
    x`Parent := M;
    x`Element := v;
    return x;
end function;

intrinsic '*'(a::RngElt,x::ModBrdtElt) -> ModBrdtElt
    {The scalar multiple a*x, where x is an element of a Brandt module}
    M := Parent(x);
    require Type(Parent(a)) eq RngInt or 
    Parent(a) cmpeq BaseRing(M) : "Elements have different parents."; 
    z := New(Type(x));
    z`Parent := M;
    z`Element := a*x`Element;
    return z;
end intrinsic;

/*
// This catches the matrix action defined below.

intrinsic '*'(x::ModBrdtElt,a::RngElt) -> ModBrdtElt
    {The scalar multiple a*x, where x is an element of a Brandt module}
    M := Parent(x);
    if Type(Parent(a)) eq AlgMat then
	require Type(BaseRing(Parent(a))) eq RngInt or 
	BaseRing(Parent(a)) eq BaseRing(M) : 
	"Arguments have different coefficient rings."; 
	require Degree(Parent(a)) eq Degree(M) : 
	"Arguments have incompatible dimensions."; 
    else 
	require Type(Parent(a)) ne RngIntElt or 
	Parent(a) cmpeq BaseRing(M) : 
	"Arguments have different coefficient rings."; 
    end if;
    return init_ModBrdtElt(M,x`Element * a);
end intrinsic;
*/

intrinsic '*'(x::ModBrdtElt,T::AlgMatElt) -> ModBrdtElt
    {The action x*T where x is an element of a Brandt module}
    M := Parent(x);
    require Type(BaseRing(Parent(T))) eq RngInt or 
    BaseRing(Parent(T)) eq BaseRing(M) : 
    "Arguments have different coefficient rings."; 
    // Assume that internal representation is via ambient module.
    if Degree(Parent(T)) eq Degree(M) then
	return init_ModBrdtElt(M,x`Element * T);
    elif Degree(Parent(T)) eq Dimension(M) then
	U := M`Module;
	B := BasisMatrix(M);
	y := ( Vector(Coordinates(U,x`Element)) * T ) * B;
        return init_ModBrdtElt(M,y);
    end if;
    require false : "Arguments have incompatible degrees."; 
end intrinsic;

intrinsic '+'(x::ModBrdtElt,y::ModBrdtElt) -> ModBrdtElt
    {The sum of Brandt module elements x and y}
    M := Parent(x);
    require Parent(y) eq M : "Elements have different parents."; 
    return init_ModBrdtElt(M,x`Element + y`Element);
end intrinsic;

intrinsic '-'(x::ModBrdtElt,y::ModBrdtElt) -> ModBrdtElt
    {The difference of Brandt module elements x and y}
    M := Parent(x);
    require Parent(y) eq M : "Elements have different parents."; 
    return init_ModBrdtElt(M,x`Element - y`Element);
end intrinsic;

