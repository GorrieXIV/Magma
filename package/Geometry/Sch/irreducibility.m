freeze;
////////////////////////////////////////////////////////////////////////
// Schemes: Irreducibility and Reduced                                //
// Tests, irreducible and prime (reduced) components                  //
// David Kohel: Revised June 2002
// Nils Bruin: Revised Jan 2003
// Based on: April 2001 GDB                                           //
////////////////////////////////////////////////////////////////////////

intrinsic HasDecomposition(X::Sch) -> BoolElt
{True iff primary decomposition methods are available for the equations of X}
    // Currently decomposition only works over a field 
    // of characteristic 0, but update as necessary.
    return IsField(BaseRing(X));
end intrinsic;

////////////////////////////////////////////////////////////////////////
//            Predicates for Irreducibility and Reduced               //
////////////////////////////////////////////////////////////////////////

intrinsic IsIrreducible(X::Sch) -> BoolElt
    {True iff the scheme X is irreducible over its base ring.}
    if not assigned X`Irreducible then
	if IsHypersurface(X) then
	    require HasFactorisation(X):
		"Methods not available for this scheme";
	    X`Irreducible := #Factorisation(Polynomial(X)) le 1;
	else
	    require HasDecomposition(X):
		"The argument must admit decomposition operations";
	    Saturate(~X);
	    X`Irreducible := #RadicalDecomposition(DefiningIdeal(X)) eq 1;
	end if;
    end if;
    return X`Irreducible;
end intrinsic;

intrinsic IsReduced(X::Sch) -> BoolElt
    {True iff X is reduced.}
    /* NB. The hypersurface case gives IsGEOMETRICALLYreduced. This is
       only potentially different if BaseRing(X) is imperfect of char >0 */
    if not assigned X`Reduced then
	if IsHypersurface(X) then
	    isred := false;
	    f := Polynomial(X);
	    gcd := f;
	    for fi in JacobianSequence(f) do
		gcd := GCD(gcd,fi);
		isred or:= TotalDegree(gcd) le 0;
	    end for;
	    X`Reduced := isred;
	else 
	    require HasDecomposition(X):
		"The argument must admit ideal decomposition operations";
	    Saturate(~X);
	    /* mch - 02/09 - fix for weighted projective space. The fact
	       that the current code was insufficient when the ambient
	       wasn't covered by standard affine patchs was kindly pointed
	       out by Jaroslaw Buczynksi and Gavin Brown                  */
	    if IsProjective(X) and NumberOfGradings(X) eq 1 and
		  &or[g ne 1 : g in Gradings(X)[1]] then
		I := DefiningIdeal(X);
		Ir := Radical(I);
		// condition is that I(d) = Ir(d) where (d) represents the
		// dth truncation and d can be taken as LCM(var_wts)
		if Ir subset I then // easy check
		    X`Reduced := true;
		else
		    // check Ir(d)=I(d) [or not] by dth Hilbert series
		    //  (and both being saturated - this is mainly redundant
		    //   here - we could just check for dth Hilbert poly equality!)
		    d := LCM(Gradings(X)[1]);
		    X`Reduced := InternalEqualityOf_dthTruncations(Ir,I,d);
		end if;
	    else
	        X`Reduced := IsRadical(DefiningIdeal(X));
	    end if;
	end if;
    end if;
    return X`Reduced;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//                       Reduced Subschemes                          //
///////////////////////////////////////////////////////////////////////

intrinsic ReducedSubscheme(X::Sch) -> Sch, MapSch
    {The reduced subscheme of X defined by its reduced scheme
    structure, followed by the map to X.}
    require HasDecomposition(X):
        "Argument must admit decomposition operations";
    A := Ambient(X);
    R := CoordinateRing(A);
    if IsEmpty(X) then // This is another hack (??)
	Xred := EmptyScheme(A);
    else
	Saturate(~X);
	Xred := Scheme(A,Radical(DefiningIdeal(X)): Saturated := true);
    end if;
    return Xred,
           map< Xred -> X | [ R.i : i in [1..Rank(R)] ] : Check := false >;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//                       Components                                  //
///////////////////////////////////////////////////////////////////////

intrinsic IrreducibleComponents(X::Sch) -> SeqEnum
    {Same as PrimaryComponents}
    // THINK ??this is not reduced??!!
    // This should give PrimeComponents instead!
    // or change the description!
	if IsHypersurface(X) then
		return PrimaryComponents(X);
	else
		require HasDecomposition(X):
			"The argument must admit ideal decomposition operations";
		return PrimaryComponents(X);
	end if;
end intrinsic;

intrinsic PrimaryComponents(X::Sch) -> SeqEnum
    {A sequence containing the irreducible components of the scheme X.}
    A := Ambient(X);
    // handle hypersurfaces separately using factorisation.
    ishsf, eqn := IsHypersurface(X);
    if ishsf then
        return [ Scheme(A,fact[1]) : fact in Factorisation(eqn) ];
    end if;
    // now the general case using primary decomposition.
    require HasDecomposition(X):
    	"The argument must admit ideal decomposition operations";
    Saturate(~X);
    if IsEmpty(X) then return [PowerStructure(Sch)|]; end if;
    // THINK: for toric varieties, if there are quotient gradings,
    // one must patch the components together, to get it right!
    comps := [ Scheme(A,I: Saturated := true) : I in PD ]
        where PD is PrimaryDecomposition(DefiningIdeal(X));
    return comps;
end intrinsic;


intrinsic PrimeComponents(X::Sch) -> SeqEnum
    {A sequence containing the irreducible, reduced components
    of the scheme X.}
    require HasDecomposition(X):
	"The argument must admit ideal decomposition operations";
    A := Ambient(X);
    Saturate(~X);
    if IsEmpty(X) then return [PowerStructure(Sch)|]; end if;
    // THINK: for toric varieties, if there are quotient gradings,
    // one must patch the components together, to get it right!
    comps := [ Scheme(A,I: Saturated := true) : I in RD ]
  	    where RD is RadicalDecomposition(DefiningIdeal(X));
    return comps;
end intrinsic;

intrinsic MinimalPrimeComponents(X::Sch) -> SeqEnum
    {A sequence containing the minimal prime components of the scheme X.}
    require HasDecomposition(X):
	"The argument must admit ideal decomposition operations";
    primes := PrimeComponents(X);
    // THINK: the universe looks ridiculous! Why not simply
    // PowerStructure(Sch)?
    return [ Parent(EmptySubscheme(Ambient(X))) | Z : Z in primes |
	not IsEmpty(Z) and #[ Y : Y in primes | Z subset Y ] eq 1 ];
end intrinsic;


