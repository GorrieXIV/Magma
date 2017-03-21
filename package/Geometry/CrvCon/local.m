freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    // 
//                     LOCAL CONDITIONS FOR CONICS                    // 
//                           David Kohel                              // 
//                            June 2002                               //
//                                                                    // 
//         Revised by Steve Donnelly, last modified March 2010        // 
//                                                                    // 
//////////////////////////////////////////////////////////////////////// 


//////////////////////////////////////////////////////////////////////// 
//                    Bad Prime and Discriminant                      //
//////////////////////////////////////////////////////////////////////// 

intrinsic BadPrimes(C::CrvCon) -> SeqEnum
    {The sequence of primes at which C has intrinsic bad reduction.}
    if BaseRing(C) cmpeq Integers() then C := ChangeRing(C, Rationals()); end if;
    K := BaseRing(C);
    require Type(K) in {RngInt, FldRat} or ISA(Type(K), FldNum) or ISA(Type(K), FldFunRat):
       "The given conic should be defined over Q, a number field or a function field.";
    if Type(K) in {RngInt, FldRat} then ans := RamifiedPrimes(QuaternionAlgebra(C));
    elif ISA(Type(K), FldNum) then ans := RamifiedPlaces(QuaternionAlgebra(C));
    else require false: "Not yet implemented for conics over function fields"; // TO DO
    end if;
    return ans;
end intrinsic;

intrinsic Discriminant(C::CrvCon) -> RngIntElt
    {The discriminant of the plane conic curve C}
    A := Ambient(C);
    f := DefiningPolynomial(C);
    a11, a12, a13, a22, a23, a33 := Explode(
        [ MonomialCoefficient(f,A.i*A.j) : i, j in [1..3] | i le j ]);
    return 4*a11*a22*a33-a11*a23^2-a12^2*a33+a12*a13*a23-a13^2*a22;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                   Hilbert Norm Residue Symbol                      //
////////////////////////////////////////////////////////////////////////

intrinsic NormResidueSymbol(a::FldRatElt,b::FldRatElt,p::RngIntElt) 
    -> RngIntElt
    {Returns 1 if ax^2 + by^2 represents a p-adic nonzero square, 
    and otherwise returns -1.}
    require IsPrime(p : Proof := false) : "Argument 3 must be prime";
    return NormResidueSymbol(
        Numerator(a)*Denominator(a),Numerator(b)*Denominator(b),p);
end intrinsic;

intrinsic NormResidueSymbol(a::RngIntElt,b::RngIntElt,p::RngIntElt) 
    -> RngIntElt
    {"} //"
    require IsPrime(p : Proof := false) : "Argument 3 must be prime";
    require a ne 0 and b ne 0 : "Arguments should be nonzero";
/*
    while a mod p^2 eq 0 do a div:= p^2; end while;
    while b mod p^2 eq 0 do b div:= p^2; end while;
*/
    v:=Valuation(a,p); a:=a div p^(2*(v div 2));
    v:=Valuation(b,p); b:=b div p^(2*(v div 2));
    if p ne 2 and &or[ KroneckerSymbol(x,p) eq 1 : x in {a,b,a+b} ] then
	return 1;
    end if;
    if a mod p eq 0 then 
	if b mod p eq 0 then
	    return NormResidueSymbol(p,-(b div p),p) *
	           NormResidueSymbol(a div p,b,p);
        elif p eq 2 and (b mod 4) eq 3 then
	    if KroneckerSymbol(a+b,p) eq -1 then 
		return -1;
	    end if;    
	elif KroneckerSymbol(b,p) eq -1 then 
	    return -1;
	end if;
    elif b mod p eq 0 then
	if p eq 2 and (a mod 4) eq 3 then
	    if KroneckerSymbol(a+b,p) eq -1 then 
		return -1;
	    end if;
	elif KroneckerSymbol(a,p) eq -1 then 
	    return -1;
	end if;
    elif p eq 2 and (a mod 4) eq 3 and (b mod 4) eq 3 then
	return -1;
    end if;
    return 1;
end intrinsic;


intrinsic IsLocallySolvable(C::CrvCon) -> BoolElt
{True iff the given conic is locally solvable over all completions
of the base field, which may be the rationals, a number field or a function field.} 

    if BaseRing(C) cmpeq Integers() then 
      C := ChangeRing(C, Rationals()); 
    end if;

    K := BaseRing(C);
    require Type(K) in {RngInt, FldRat} or ISA(Type(K), FldNum) or 
            ISA(Type(K), FldFunRat) and Characteristic(K) ne 2 :
       "The given conic should be defined over Q, a number field or a function field"*
       " (of characteristic not equal to 2).";
    
    if ISA(Type(K), FldNum) and not IsAbsoluteField(K) then
      return IsLocallySolvable(ChangeRing(C, AbsoluteField(K)));
    end if;

    a,b,c := Explode(Coefficients(LegendrePolynomial(C))); assert a*b*c ne 0;

    // solubility at real places
    if ISA(Type(K), FldFunG) then 
      ans := true;
    elif Type(K) eq FldRat then 
      ans := {Sign(a), Sign(b), Sign(c)} eq {1,-1};
    else 
      ans := true;
      realplaces := [v : v in InfinitePlaces(K) | IsReal(v)];
      for v in realplaces do 
        ans := ans and {Sign(Real(Evaluate(x,v))) : x in [a,b,c]} eq {1,-1};
      end for;
/*
num := #[v : v in realplaces | {Sign(Real(Evaluate(x,v))) : x in [a,b,c]} eq {1,-1}];
printf "    oo:%o/%o ", num, #realplaces;
*/
    end if; 

    // solubility at archimedean places 
    // (Rewritten to avoid unnecessary factorization, SRD September 2008)
    if ans then 
      if Type(K) in {RngInt, FldRat} then
        ds := [Denominator(c) : c in Coefficients(DefiningEquation(C))];
        badprimes := &join[ {tup[1] : tup in Factorization(d)} : d in ds ];
        D := Discriminant(C);
        D1 := Integers()!( D / &* [Rationals()| p^Valuation(D,p) : p in badprimes] );
        badprimes join:= {tup[1] : tup in Factorization(D1)};
        badprimes := [P : P in badprimes | exists{x: x in [a,b,c] | Valuation(x,P) ne 0} ];
        bb := -b/a; cc := -c/a;
        for P in Sort(badprimes) do
          ans := ans and NormResidueSymbol(bb,cc,P) eq 1; // 'and' is okay but 'and:=' is not
        end for;

      elif ISA(Type(K), FldAlg) then 
        OK := Integers(K);
        badprimes := {PowerIdeal(OK)| };
        coeffs := Coefficients(Equation(C));
        ds := [Denominator(c*OK) : c in coeffs] cat [Denominator(c) : c in coeffs];
        for d in ds do 
          badprimes1 := {tup[1] : tup in Factorization(d*OK)};
          badprimes join:= badprimes1;
          StoreFactor({Minimum(P) : P in badprimes1});
        end for;
        if IsDiagonal(Matrix(C)) then
          for x in coeffs cat [2] do 
            badprimes1 := {tup[1] : tup in Factorization(x*OK)};
            badprimes join:= badprimes1;
            StoreFactor({Minimum(P) : P in badprimes1});
          end for;
        else
          D := Discriminant(C);
          badprimes1 := {tup[1] : tup in Factorization(D*OK)};
          badprimes join:= badprimes1;
          StoreFactor({Minimum(P) : P in badprimes1});
        end if;

        badprimes := [P : P in badprimes | exists{x: x in [2,a,b,c] | Valuation(x,P) ne 0} ];
        if ans and #badprimes gt 0 then
          // Sort them in increasing norm, but putting the even primes last
          norms := [Integers()| AbsoluteNorm(P) : P in badprimes];
          norms2 := [ExtendedReals()| IsEven(n) select Infinity() else n : n in norms];
          ParallelSort(~norms2, ~badprimes);
          // construct A at most once, instead of in every call to Hilbert
          A := 0;
          for i := 1 to #badprimes do
            if not ans then
              break;
            end if;
            P := badprimes[i];
            if IsOdd(Minimum(P)) then
              ans := HilbertSymbol(-b*a, -c*a, P) eq 1;
            else
              if A cmpeq 0 then
                A := QuaternionAlgebra<K | -b*a, -c*a >; 
              end if;
              ans := HilbertSymbol(A,P) eq 1;
            end if;
          end for; 
        end if;

      else // FldFunRat case 
        F := BaseField(K);
        if IsFinite(F) then
          coeffs := Coefficients(DefiningEquation(C));
          if not forall{c : c in coeffs | c in F} then
            badprimes := &join [{tup[1] : tup in Factorization(Denominator(c))} : c in coeffs]
                          join {tup[1] : tup in FactorizationOfQuotient(Discriminant(C))};
            bb := -b/a; cc := -c/a;
            for P in badprimes do 
              ans := ans and HilbertSymbol(bb,cc,P) eq 1; // 'and' is okay but 'and:=' is not
            end for;
          end if;
        elif F cmpeq Rationals() then
          ans := HasRationalPoint(C); 
        else
          require false : "Only implemented for conics over F_q(t) or Q(t)";
        end if;
      end if;
    end if;

    return ans;
end intrinsic;

