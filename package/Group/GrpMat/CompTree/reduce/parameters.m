freeze;

//$Id:: parameters.m 3133 2015-08-09 05:12:49Z eobr007                     $:

// Maximum degree for char 2
MaxRybaEvenFieldDegree := 3;

function SLRybaParameters(G, d, q)
    useRyba := q^d gt 2^10 and 
      (IsOdd (q) or (IsEven (q) and Degree (GF(q)) le MaxRybaEvenFieldDegree));
    verify := q eq 2 and d le 4;
    method := q^d le 2^12 select "BSGS" else "CT";
    centraliserGens := 100;
    central := false;
    rank := d - 1;
    
    return useRyba, [* verify, method, centraliserGens, central, rank *];
end function;

function SpRybaParameters(G, d, q)
    useRyba := q^d gt 5^6 and 
      (IsOdd (q) or (IsEven (q) and Degree (GF(q)) le MaxRybaEvenFieldDegree));
    verify := q eq 2 and d le 4;
    method := q^d le 5^6 select "BSGS" else "CT";
    centraliserGens := 100;
    central := d eq 4;
    rank := d div 2;
    
    return useRyba, [* verify, method, centraliserGens, central, rank *];
end function;

function SURybaParameters(G, d, q)
    // q is the size of the underlying field
    useRyba := d gt 3 and q^d gt 5^2 and 
    (IsOdd (q) or (IsEven (q) and Degree (GF(q)) le MaxRybaEvenFieldDegree+1));

    verify := q le 8 and d le 6;
    method := q^d le 5^7 select "BSGS" else "CT";

    centraliserGens := 100;
    if q eq 2 and d ge 10 then 
       centraliserGens := 20; method := "CT"; useRyba := true; 
    end if;
    central := false;
    rank := d - 1;
    
    return useRyba, [* verify, method, centraliserGens, central, rank *];
end function;

function OmegaRybaParameters(G, d, q)
    useRyba := q^d gt 5^6 and 
      (IsOdd (q) or (IsEven (q) and Degree (GF(q)) le MaxRybaEvenFieldDegree));
    verify := q eq 2 and d le 4;
    method := q^d le 5^8 select "BSGS" else "CT";
    centraliserGens := 100;
    central := false;
    rank := (d - 1) div 2;
    
    return useRyba, [* verify, method, centraliserGens, central, rank *];
end function;

function OmegaMinusRybaParameters(G, d, q)
    useRyba := q^d gt 5^2 and d ne 2 and 
      (IsOdd (q) or (IsEven (q) and Degree (GF(q)) le MaxRybaEvenFieldDegree));
    verify := q eq 2 and d le 4;
    method := q^d le 5^3 select "BSGS" else "CT";
    centraliserGens := 100;
    central := false;
    rank := d div 2;
    
    return useRyba, [* verify, method, centraliserGens, central, rank *];
end function;

function OmegaPlusRybaParameters(G, d, q)
    useRyba := q^d gt 5^6 and d ne 2 and 
      (IsOdd (q) or (IsEven (q) and Degree (GF(q)) le MaxRybaEvenFieldDegree));
    verify := q eq 2 and d le 4;
    method := q^d le 5^3 select "BSGS" else "CT";
    centraliserGens := 100;
    central := false;
    rank := d div 2;
    
    return useRyba, [* verify, method, centraliserGens, central, rank *];
end function;

function GeneralRybaParameters(G, family, rank, q)
    // Sporadic groups and Alt have no defining field, but they should never
    // appear here
    assert Category(q) eq RngIntElt;

    if IsEven(q) and q gt 2^MaxRybaEvenFieldDegree then
	return false, _;
    end if;

    verify := false;
    method := "CT";
    centraliserGens := 100;
    central := false;

    return true, [* verify, method, centraliserGens, central, rank *];
end function;

I := cop<Strings(), Integers(), Booleans()>;

// Functions returning parameters for Reduction/Ryba
RybaParameters := AssociativeArray(I);
RybaParameters[I ! "A"] := func<G, family, rank, q |
    SLRybaParameters(G, rank + 1, q)>;
RybaParameters[I ! "2A"] := func<G, family, rank, q | 
    SURybaParameters(G, rank + 1, q)>;
RybaParameters[I ! "C"] := func<G, family, rank, q | 
    SpRybaParameters(G, 2 * rank, q)>;
RybaParameters[I ! "B"] := func<G, family, rank, q | 
    OmegaRybaParameters(G, 2 * rank + 1, q)>;
RybaParameters[I ! "D"] := func<G, family, rank, q |
    OmegaPlusRybaParameters(G, 2 * rank, q)>;
RybaParameters[I ! "2D"] := func<G, family, rank, q |
    OmegaMinusRybaParameters(G, 2 * rank, q)>;

RybaParameters[I ! "F"]  := GeneralRybaParameters;
RybaParameters[I ! "2F"] := GeneralRybaParameters;
RybaParameters[I ! "E"]  := GeneralRybaParameters;
RybaParameters[I ! "2E"] := GeneralRybaParameters;
RybaParameters[I ! "3D"] := GeneralRybaParameters;
RybaParameters[I ! "2B"] := GeneralRybaParameters;
RybaParameters[I ! "2G"] := GeneralRybaParameters;
RybaParameters[I ! "G"]  := GeneralRybaParameters;
RybaParameters[I ! 17]   := GeneralRybaParameters;
RybaParameters[I ! 18]   := GeneralRybaParameters;
