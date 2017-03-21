freeze;

/* This file contains the code for two functions  invphi and invphifact
   imported by the InversePhi and InversePhiFactored package files.
   Wieb Bosma, April 2002
*/
invphifact := function(m)
    /* For a positive integer m, or a factorization sequence
       for such, this function returns a set containing the
       factorization sequences of all positive n with
       EulerPhi(n) = m
    */
    if Type(m) eq RngIntElt then
	if m lt 1 then
	    error "Runtime error 'InversePhi': argument not positive";
	end if;
	mfact := Factorization(m);
	mm := m;
    else
	mfact := m;
	mm := Facint(m);
    end if;
    if IsEven(mm) then
	twopows := [ 2^i : i in [0..mfact[1][2]]];
    else
	if mm gt 1 then
	    return { };
	end if;
	twopows := [1];
    end if;
    D := Divisors(mfact);
    P := [];
    for d in D do
	if d eq 1 then
	    continue;
	end if;
	if IsPrime(d+1) then
		Append(~P, d+1);
	end if;
    end for;
    S := [<SeqFact([]), mm>];
    last := false;
    for u in [#P..1 by -1] do
	p := P[u];
	if u eq 1 then last := true; end if;
	for s in S do
	    mmod :=  s[2] mod (p-1);
	    if mmod eq 0 then
		mdiv := s[2] div (p-1);
		k := 1;
		if (not last and IsEven(mdiv)) or IsOne(mdiv) then
			t := <SeqFact([<p, k>]  cat Eltseq(s[1])), mdiv>;

			Append(~S, t);
			while mdiv mod p eq 0 do
			    k +:= 1;
			    mdiv := mdiv div p;
			    t := <SeqFact([<p, k>]  cat Eltseq(s[1])), mdiv>;
			    Append(~S, t);
			end while;
		else
		    mdivold := mdiv;
		    while mdiv mod p eq 0 do
			k +:= 1;
			mdiv := mdiv div p;
		    end while;
		    if mdiv eq 1 or (last and mdiv in twopows) then
			for j := 1 to k do
			    Append(~S, <SeqFact([<p, j>]  cat Eltseq(s[1])),
			      mdivold div p^(j-1)>);
			end for;
		    end if;
		end if;
	    end if;
	end for;
    end for;
    R := {};
    for s in S do
	if s[2] in twopows then
	    j := Index(twopows, s[2]);
	    if j gt 0 then
		Include(~R, SeqFact([<2, j>] cat s[1]));
		if j eq 1 then
		    Include(~R, s[1]);
		end if;
	    end if;
	end if;
    end for;
    return Sort(Setseq(R));
end function;

invphi := function(m)
    /* For a positive integer m, or a factorization sequence
       for such, this function returns a sorted sequence of
       all positive n with EulerPhi(n) = m
    */
    return Sort([ Facint(nf) : nf in invphifact(m)]);
end function;

intrinsic EulerPhiInverse(m::RngIntElt) -> SeqEnum
    { Returns sorted sequence of integers m with EulerPhi(n) = m }
    requirege  m, 1;
    return invphi(m);
end intrinsic;

intrinsic EulerPhiInverse(m::RngIntEltFact) -> SeqEnum
    { Returns sorted sequence of integers m with EulerPhi(n) = m }
    return invphi(m);
end intrinsic;

intrinsic FactoredEulerPhiInverse(m::RngIntElt) -> SetEnum 
    { Returns set of factored n with EulerPhi(n) = m }
    requirege  m, 1;
    return invphifact(Factorization(m));
end intrinsic;

intrinsic FactoredEulerPhiInverse(m::RngIntEltFact) -> SetEnum 
    { Returns set of factored n with EulerPhi(n) = m }
    return invphifact(m);
end intrinsic;
