freeze;

////////////////////////////////////////////////////////////////////////
//                            Degree                                  //
////////////////////////////////////////////////////////////////////////

intrinsic Degree(S::Sch) -> RngIntElt
    {The degree of the scheme S.}

    if assigned S`Degree then
	return S`Degree;
    end if;

    if IsHypersurface(S) then
	if #Gradings(Ambient(S)) gt 1 then
	    S`Degree := Multidegree(Ambient(S),Polynomial(S));
	    return S`Degree;
	end if;
	S`Degree := WeightedDegree(Polynomial(S));
	return S`Degree;
    elif Type(S) eq Clstr and IsAffine(S) then
	S`Degree := Dimension(CoordinateRing(S));
	return S`Degree;
    elif IsOrdinaryProjective(S) then
	require HasGroebnerBasis(S):
	    "Base ring of argument does not admit Groebner basis methods";
	h := HilbertPolynomial(DefiningIdeal(S));
	if Degree(h) eq -1 then return 0; end if;    
	S`Degree := Integers()!(Factorial(Degree(h))*LeadingCoefficient(h));
	return S`Degree;
    elif IsAffine(S) then
        if IsEmpty(S) then
	  S`Degree := 0;
          return 0;
        end if;
	b,Z := IsCluster(S);
	require b:
	    "Argument must be a hypersurface, a cluster or projective";
	// Must be in case of an affine cluster which was missed earlier
	// since its true type wasn't known at the time.
	S`Degree := Dimension(CoordinateRing(S));
	return S`Degree;
    elif Dimension(S) le 0 then
    // case added 04/08 - mch - can now use arithmetic genus in anything
    //  but affine x projective ambients.
	if Dimension(S) eq -1 then S`Degree := 0; return 0; end if;
	try
	    S`Degree := ArithmeticGenus(S)+1;
	    return S`Degree;
	catch e
	    // was bad ambient
	    i := 0; //do nothing!
	end try; 
    end if;
    grd:=Gradings(S);
    error if #grd ne 1,
        "Space must have only one grading";
    grd:=grd[1];
    error if not forall{i:i in [1..#grd]| grd[i] eq 1 or
                           IsEmpty(S meet Scheme(Ambient(S),S.i))},
        "Scheme must stay away from singular locus of ambient space.";
    deg:=0;
    for i in [i: i in [1..#grd]|grd[i] eq 1] do
      deg+:=Degree(AffinePatch(S,#grd+1-i));
      S:=S meet Scheme(Ambient(S),S.i);
      if IsEmpty(S) then
	S`Degree := deg;
        return deg;
      end if;
    end for;
    error "We should not be arriving here";
end intrinsic;

