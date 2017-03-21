freeze;

forward ArtinSchreierRoot, MakeRelations;

function Lercier(E,F,ell)
    // Lercier's algorithm for computing a factor of the l'th 
    // division polynomial of the curve E, where E and E1 are 
    // ell-isogenous.

    vprint SEA, 3: "Using Lercier's algorithm.";
    RELS_TIME := Cputime();
    error if not (IsSimplifiedModel(E) and IsSimplifiedModel(F)),
        "ECs must be simplified models";
    error if not IsOdd(ell), "Isogeny degree must be odd.";

    aE := aInvariants(E);
    aF := aInvariants(F);
    a := aE[5];
    b := aF[5];

    error if aE[2] ne 0, "Wrong form for E.";
    error if aF[2] ne 0, "Wrong form for F.";

    FF := BaseRing(E);
    assert FF eq CoefficientRing(F);
    P := PolynomialRing(FF);
    X := P.1;

    d := (ell-1) div 2;
    k_max := (d-2) div 3;
    if k_max le 0 then
        Q := PolynomialRing(FF, 1);
        I := ideal< Q | [ Q.1 ] >;
    else
        Q := PolynomialRing(FF, k_max);
        I := ideal< Q | [ Q.i^2-Q.i : i in [1..Rank(Q)] ] >;
    end if;
    R := Q/I;
    AssignNames(~Q, ["x" cat IntegerToString(i): i in [1..Rank(Q)]]);

    alpha := Root(a, 4);
    beta := Root(b, 4);
    if ell eq 3 then 
        return true, X + alpha*Sqrt(alpha/beta);
    end if;

    p := [ Q | ];
    p[d+1] := Q!(FF!1);
    p[d] := Q!(alpha + beta);    
    p[d-1] := p[d]^4 + alpha * p[d] + d*alpha^2;
    p[1] := Root( (alpha^(2*d) + alpha^(2*d-1) * 
                  MonomialCoefficient(p[d],Q!1)), 4);
    // STEP 2 of Lercier: BEGIN LOOP. 
    k := 1;
    alpha_rt2 := Sqrt(alpha);
    alpha_rt4 := Sqrt(alpha_rt2);
    beta_rt4 := Root(beta,4);
    b_k := beta_rt4 * alpha_rt2^d / alpha_rt4;
    // we need to invert b_k below -- this must be an invalid
    // moduli point of the modular curve so return: 
    if b_k eq 0 then return false, P!0; end if;
    indets := [ Q.i : i in [1..Rank(Q)] ];
    // Manually reduced expressions for indeterminants.
    reduct := [ Q.i : i in [1..Rank(Q)] ]; 
    flatten_rels := [ xi^2 - xi : xi in indets ]; 
    rels := flatten_rels;
    while true do       
        if IsDefined(p,k+1) then 
            break; 
        end if; 
        b_k := b_k / alpha;
        c_k := Q!(R!( ( alpha_rt4 *
            &+[ Q | p[i+1]^2 * p[d-k+i+1]^2 * alpha^(2*i) 
                : i in [0..k-1] ]
            + beta_rt4 * alpha_rt2^d * alpha^k * 
            &+[ Q | Binomial(d-k+2*i,i) * p[k-2*i+1]
                        : i in [1..k div 2]] ) 
            / ( alpha_rt4 * alpha^(2*k) ) ) );
        RemovePowersInPlace(~c_k);
        c_k := Evaluate(c_k,reduct);
        RemovePowersInPlace(~c_k);
        q_k := c_k/(b_k)^2;
        poly_trace := &+[ Q | 
            Trace(MonomialCoefficient(q_k,mon))*mon 
                : mon in Monomials(q_k) ];
        if poly_trace eq 1 then 
            vprint SEA, 4:
                "Curves are nonisogenous of this degree.";
            return false, P!0;
        elif poly_trace eq 0 then
            p[k+1] := b_k * ( Q.k + 
                &+[ Q | ArtinSchreierRoot(
                    MonomialCoefficient(q_k,mon) ) * mon  
                        : mon in Monomials(q_k) ] );
        else
            vprint SEA, 4: "New relation =", poly_trace;
            Append(~rels,poly_trace);
            mons := [ mon : mon in Monomials(poly_trace) | mon in indets ]; 
            if #mons eq 0 then
                print "Found relation with no isolated indeterminate.";
                I := ideal< Q | I, poly_trace >;
                Groebner(I: Walk := false);
                R := Q/I;
                for j in [1..d+1] do
                    if IsDefined(p,j) then
                        p[j] := Q!(R!p[j]);
                    end if;
                end for;
                q_k := Q!(R!q_k);
            else
                xi := mons[#mons];
                ii := Index(indets,xi);
                ti := poly_trace + xi;
                for j in [1..Rank(Q)] do
                    reduct[j] := Evaluate(reduct[j],ii,ti);
                end for;
                for j in [1..d+1] do
                    if IsDefined(p,j) then
                        p[j] := Evaluate(p[j],reduct);
                        RemovePowersInPlace(~p[j]);
                    end if;
                end for;
                q_k := Evaluate(q_k,reduct);
                RemovePowersInPlace(~q_k);
            end if;
            p[k+1] := b_k * ( Q.k + 
                &+[ Q | ArtinSchreierRoot( 
                    MonomialCoefficient(q_k,mon) ) * mon  
                        : mon in Monomials(q_k) ] );
        end if;

        // STEP 3 of Lercier.
        if IsDefined(p,d-2*k) then 
            break; 
        end if; 
        p[d-2*k] := (p[k+1]^4 / alpha^(2*d-4*k-1)) - 
            ( &+[ Q | 
                Binomial(d+2*(i-k)-1,i) * p[d+2*(i-k)] * alpha^(2*i)
                    : i in [1..k] ]
            + alpha * &+[ Q |
                Binomial(d+2*(i-k),i) * p[d+2*(i-k)+1] * alpha^(2*i)
                    : i in [0..k] ] );
        RemovePowersInPlace(~p[d-2*k]);
        p[d-2*k] := Evaluate(p[d-2*k],reduct); 
        RemovePowersInPlace(~p[d-2*k+1]);

        // STEP 4 of Lercier.
        k := k+1;
        if IsDefined(p,d-2*k+1) then 
            break; 
        end if; 
        p[d-2*k+1] := p[d-k+1]^4 - 
            ( alpha * &+[ Q | 
                Binomial(d+2*(i-k)+1,i) * p[d+2*(i-k)+2] * alpha^(2*i)
                    : i in [0..k-1] ]
            + &+[ Q | 
                Binomial(d+2*(i-k),i) * p[d+2*(i-k)+1] * alpha^(2*i)
                    : i in [1..k] ] );
        RemovePowersInPlace(~p[d-2*k+1]);
        p[d-2*k+1] := Evaluate(p[d-2*k+1],reduct); 
        RemovePowersInPlace(~p[d-2*k+1]);
    end while;

    // Solve for the unknowns.
    vprint SEA, 4: "Found", #rels - Rank(Q), 
        "trivial relations among", Rank(Q), "unknowns."; 
    rels cat:= MakeRelations(p,d,alpha,R);
    vprint SEA, 3: "Relation construction time:", Cputime(RELS_TIME);

    vprint SEA, 3: "Solving for points.";

    VARIETY_TIME := Cputime();

    nvars := Rank(Q);
    rels := Set(rels) diff Set(flatten_rels);

    vprintf SEA, 3:
       "Solve system; variables: %o, relations: %o\n", nvars, #rels;
    IndentPush();

    list := Setseq(rels);

    // The sort is necessary to ensure 1 is first if present:
    mons := Sort(Setseq(&join{Seqset(Monomials(f)): f in list}));
    mons := {@ x: x in mons @};

    if 1 notin mons then
	point := [0: v in [1 .. nvars]];
	vprint SEA, 4: "Trivial solution:", point;
	IndentPop();

	Y := X/alpha^2;
	return true, 
            Evaluate(p[1],point)^(-2) * alpha^(2*d) *
                    &+[ Evaluate(p[d+1-i],point)^2*Y^i : i in [0..d] ];
    end if;

    assert Index(mons, 1) eq 1;
    vprint SEA, 5: "Number of monomials:", #mons;

    prime := PrimeField(FF);
    deg := Degree(FF, prime);
    A := RMatrixSpace(prime, 0, #mons) ! 0;
    V := RSpace(prime, deg);
    for k := 1 to #list do
	f := list[k];
	if f eq 0 then
	    continue;
	end if;
	c := Coefficients(f);
	m := Monomials(f);
	B := RMatrixSpace(prime, #c, deg) ! 0;
	for i := 1 to #c do
	    B[i] := V ! Eltseq(c[i], prime);
	end for;
	B := EchelonForm(Transpose(B));
	r := rep{i: i in [1 .. Nrows(B)] | IsZero(B[i])} - 1;
	vprintf SEA, 5: "Relation %o; rank: %o, columns: %o\n", k, r, #c;
	Ar := Nrows(A);
	A := VerticalJoin(A, RMatrixSpace(prime, r, #mons) ! 0);
	for j := 1 to #c do
	    index := Index(mons, m[j]);
	    for i := 1 to r do
		A[Ar + i, index] := B[i, j];
	    end for;
	end for;
    end for;
    vprintf SEA, 5:
        "Final matrix rows: %o, columns: %o\n", Nrows(A), Ncols(A);
    vprint SEA, 4: "Matrix construction time:", Cputime(VARIETY_TIME);

    A := EchelonForm(A);
    N := RowNullSpace(A);
    B := BasisMatrix(N);
    V := RSpace(prime, Ncols(B));

    repeat
	vprint SEA, 5: "Nullity:", Nrows(B);
	if Nrows(B) eq 0 or B[1, 1] ne 1 then
	    vprint SEA, 4: "No solution";
	    IndentPop();
	    return false, P!0; 
	end if;

	w := B[1];
	if Nrows(B) eq 1 then
	    break;
	end if;

	new := [];
	for j in [1 .. #mons] do
	    if forall{i: i in [2 .. Nrows(B)] | B[i, j] eq 0} then
		m := mons[j];
		for k in [1 .. j - 1] cat [j + 1 .. #mons] do
		    assert k ne j;
		    if w[j] eq 0 then
			// Any multiple of m must be 0 so must equal w[j]
			if IsDivisibleBy(mons[k], m) then
			    u := V!0;
			    u[j] := 1;
			    u[k] := -1;
			    Append(~new, u);
			end if;
		    else
			// Any divisor of m must be 1 so must equal w[j]
			if IsDivisibleBy(m, mons[k]) then
			    u := V!0;
			    u[j] := 1;
			    u[k] := -1;
			    Append(~new, u);
			end if;
			// If mons[k] divisible by m, then coordinate of
			// mons[k]/m must equal coordinate k if it exists
			if m ne 1 and IsDivisibleBy(mons[k], m) then
			    index := Index(mons, mons[k] div m);
			    if index gt 0 then
				assert index ne k;
				u := V!0;
				u[k] := 1;
				u[index] := -1;
				Append(~new, u);
			    end if;
			end if;
		    end if;
		end for;
	    end if;
	end for;
	vprint SEA, 5: "Number of new relations:", #new;
            
        lastB := B;
	AA := RMatrixSpace(prime, #new, Ncols(B)) ! new;
	A := VerticalJoin(A, AA);

	A := EchelonForm(A);
	N := RowNullSpace(A);
	B := BasisMatrix(N);
    until Nrows(B) eq Nrows(lastB) and B eq lastB;

    N := sub<V | [B[i]: i in [2 .. Nrows(B)]]>;
    for u in N do
	z := w + u;
	one := {};
	for i in [i: i in [1 .. #mons] | not IsZero(z[i])] do
	    m := mons[i];
	    one join:= {v: v in [1 .. nvars] | Degree(m, v) gt 0};
	end for;
	
	vprint SEA, 5: "Possible non-zero variables:", one;
	if not exists{
	    i: i in [i: i in [1 .. #mons] | IsZero(z[i])] |
	    {v: v in [1 .. nvars] | Degree(mons[i], v) gt 0}
	    subset one } then
	    point := [v in one select 1 else 0: v in [1 .. nvars]];
	    vprint SEA, 4: "Solution:", point;
	    IndentPop();

	    Y := X/alpha^2;
	    return true, 
                Evaluate(p[1],point)^(-2) * alpha^(2*d) *
                    &+[ Evaluate(p[d+1-i],point)^2*Y^i : i in [0..d] ];
	end if;
    end for;
    vprint SEA, 4: "No solution";
    IndentPop();
    return false, P!0; 
end function;

function MakeRelations(p,d,alpha,R) 
    // Given a sequence p of elements of a multivariate polynomial 
    // ring, the degree d of the kernel polynomial, and an element 
    // alpha of the constant field.
    // Returns the sequence of relations among the p[k].

    Q := Universe(p);
    return [ Q!(R!(
        p[k+1]^4 - alpha^(2*d-4*k-1) *
            ( alpha * &+[ Universe(p) |
                Binomial(d+2*(i-k),i) * p[d+2*(i-k)+1] * alpha^(2*i)
                    : i in [0..k] ]
            + &+[ Universe(p) |
                Binomial(d+2*(i-k)-1,i) * p[d+2*(i-k)] * alpha^(2*i)
                    : i in [0..k] ] ) ) )
        : k in [0..(d-1) div 2] ]
    cat [ Q!(R!(
        p[d-k+1]^4 -
            ( alpha * &+[ Universe(p) |
                Binomial(d+2*(i-k)+1,i) * p[d+2*(i-k)+2] * alpha^(2*i) 
                    : i in [0..k-1] ]
            + &+[ Universe(p) | 
                Binomial(d+2*(i-k),i) * p[d+2*(i-k)+1] * alpha^(2*i)
                    : i in [0..k] ] ) ) )
        : k in [1..d div 2] ];
end function;

function ArtinSchreierRoot(c_mu)
    P := PolynomialRing(Parent(c_mu));
    return Roots(P.1^2 + P.1 + c_mu)[1][1];
end function;

