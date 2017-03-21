freeze;

// Elias bound			Lancelot Pecquet, 1996

intrinsic EliasBound(K::FldFin,n::RngIntElt,d::RngIntElt)->RngIntElt
{Return the upper Elias bound for the cardinality of a largest code
of length n and minimum distance d over the field K}
	requirege n,1;
	requirerange d,1,n;
	q := #K;
	t := 1 - 1/q;
	twotn := 2*t*n;
	tnd := t*n*d;
	rmax := Floor(t*n);
	a := Max([(r^2 - twotn*r + tnd)*SphereVolume(K,n,r)
		: r in [0 .. rmax]]);		
	return Floor(tnd*(q^n) / a);
end intrinsic;


intrinsic EliasAsymptoticBound(K::FldFin,delta::FldReElt)->FldReElt
{Return the Elias asymptotic upper bound for delta in [0, 1]
over the field K}
	theta := 1 - 1/#K;
	require delta ge 0:"Argument 1 should be in [0,1]";
	require delta le 1:"Argument 1 should be in [0,1]";	
	if (delta ge theta) then
		return 0;
	else
		return 1-Entropy(theta-Sqrt(theta*(theta-delta)),K);
	end if;
end intrinsic;

// Gilbert-Varshamov lower bound,		Lancelot Pecquet, 1996

intrinsic GilbertVarshamovBound(K::FldFin,n::RngIntElt,d::RngIntElt)->RngIntElt
{Return the Gilbert-Varshamov lower bound for the cardinality of a largest
code of length n and minimum distance d over the field K}
	requirege n,1;
	requirerange d,1,n;
	return Ceiling(#K^n / SphereVolume(K,n,d-1));
end intrinsic;

intrinsic GilbertVarshamovLinearBound(K::FldFin,n::RngIntElt,d::RngIntElt)
->RngIntElt
{Return the Gilbert-Varshamov lower bound of the size of a largest linear 
code of length n and minimum distance d over the field K}
	requirege n,1;
	requirerange d,1,n;
	q := #K;
	V := SphereVolume(K,n,d-1);
	b,pow := IsPowerOf(V, q);
	if b then
	    k := n - pow;
	else
	    k := n + 1 - Ceiling(Log(q, V));
	end if;
	return q^k;
end intrinsic;


// Gilbert-Varshamov asymptotic lower bound	Lancelot Pecquet, 1996

intrinsic GilbertVarshamovAsymptoticBound(K::FldFin,delta::FldReElt)->FldReElt
{Return the Gilbert-Varshamov asymptotic lower bound of the information rate 
for delta in [0, 1] over the field K}
	theta := 1 - 1/#K;
	require delta ge 0:"Argument 1 should be in [0,1]";
	require delta le 1:"Argument 1 should be in [0,1]";	
	if (delta gt theta) then
		return 0;
	else
		return 1 - Entropy(delta,K);
	end if;
end intrinsic;

// Griesmer bound for linear codes	Lancelot Pecquet, 1996

// n,k are integers >= 0, q is a power of a prime number

intrinsic GriesmerLengthBound(K::FldFin,k::RngIntElt,d::RngIntElt) -> RngIntElt
{Return the Griesmer lower bound of the length of a linear code of
dimension k and minimum distance d over K}
	requirege k,0;
	requirege d,1;
	q := #K;
	if (k eq 0) then
		return 1;
	else
		return &+[Ceiling(d/(q^i)) : i in [0 .. k-1]];
	end if;
end intrinsic;

intrinsic GriesmerMinimumWeightBound(K::FldFin,n::RngIntElt,k::RngIntElt)
-> RngIntElt
{Compute the Griesmer upper bound of the minimum weight of a linear code of
length n and dimension k over the field K}
    requirege n,1;
    requirerange k,1,n;
    d := 1;
    b := 0;
    q := #K;
    if (k eq 1) then
	return n;
    else
	while ((b le n) and (d le n)) do
	    d +:= 1;
	    b := &+[Ceiling(d/(q^i)) : i in [0 .. k-1]];
	end while;
	return d-1;
    end if;
end intrinsic;

intrinsic GriesmerBound(K::FldFin,n::RngIntElt,d::RngIntElt) -> RngIntElt
{Return the Griesmer upper bound of the cardinality of a linear code of
length n and minimum distance d over K}
	requirege n,1;
	requirerange d,1,n;
	q := #K;
	k := 0;
	b := 0;
	while (b le n) do
		b +:= Ceiling(d/q^k);
		k +:= 1;
	end while;
	return q^(k-1);
end intrinsic;

//Johnson bound for binary codes,		Lancelot Pecquet, 1996

intrinsic JohnsonBound(n::RngIntElt,d::RngIntElt)->RngIntElt
{Return the Johnson upper bound for the cardinality of a largest binary code 
of length n and minimum distance d}
	requirege n,1;
	requirerange d,1,n;
	if (d eq 1) then
		return 2^n;
	else
		if (IsEven(d)) then
			n1 := n-1;
			d1 := d-1;
		else	
			n1 := n;
			d1 := d;
		end if;
		r := (d1-1) div 2;
		return Floor(2^n1 / (&+[Binomial(n1,i): i in [0 .. r]]
			+ ((Binomial(n1,r) / (n1 div (r+1)))
			*((n1-r)/(r+1) - ((n1-r) div (r+1))))));
	end if;
end intrinsic;


// Nearly perfect binary codes,		Lancelot Pecquet, 1996

intrinsic IsNearlyPerfect(C::CodeLinFld) -> BoolElt
{Return true if the binary code is nearly perfect, else return false}
	require #Alphabet(C) eq 2:"Argument should be a binary code";
	d := MinimumDistance(C);
	require d ge 2:"Code should have a minimum distance > 1 to meet 
	Johnson Bound";
	if (#C eq JohnsonBound(Length(C),d)) then
		return true;
	else
		return  false;
	end if;
end intrinsic;

// Levenstein upper bound to A(n,d)		Lancelot Pecquet, 1996

intrinsic LevenshteinBound(K::FldFin,n::RngIntElt,d::RngIntElt) -> RngIntElt
{Return the Levenstein upper bound of the cardinality of a largest code of
length n, minimum distance d over the field K}
	requirege n,1;
	requirerange d,1,n;
	q := #K;
	RX := PolynomialRing(RealField()); X := RX.1;
	
	dk := function(k,n);
		if (k eq 0) then
			res := n+1;
		elif (k eq n+1) then
			res := 0;
		else
			P := RX!KrawchoukPolynomial(K,n,k);
			R := [r[1] : r in Roots(P) | IsReal(r[1])];
			if (#R eq 0) then
				res := 0;
				print "Argh";
			else
				res := Min(R);
			end if;
		end if;
		return res;
	end function;

	Lknrz := function(k,n,z);
		return SphereVolume(K,n,k-1) - Binomial(n,k)*(q-1)^k*
		Evaluate(KrawchoukPolynomial(K,n-1,k-1),z-1)/
		Evaluate(KrawchoukPolynomial(K,n,k),z);
	end function;

	Lnrz := function(n,z);
		if (z eq 1) then
			return q^n;
		elif (z eq n+1) then
			return 1;
		else
			for k in [0 .. n+1] do
				d1 := dk(k,n-1)+1;
				if ((d1 lt z) 
				and (z le dk(k-1,n-2)+1)) then
					rep := Lknrz(k,n,z);
					break;
				elif ((dk(k,n-2)+1 lt z) 
				and (z le d1)) then
					rep := q*Lknrz(k,n-1,z);
					break;
				end if;
			end for;
		end if;
		return rep;
	end function;

	return Floor(Lnrz(n,d));
end intrinsic;

// Linear programming bound		Lancelot Pecquet, 1996



// McEliece-Rodemich-Rumsey-Welch asymptotic bound	Lancelot Pecquet, 1996

intrinsic McElieceEtAlAsymptoticBound(delta::FldReElt)->FldReElt
{Return the McEliece-Rodemich-Rumsey-Welch asymptotic upper bound of the
binary information rate for delta in [0, 1].}
	require delta ge 0:"Argument 1 should be in [0,1/2]";
	require delta le 0.5:"Argument 1 should be in [0,1/2]";
	return Entropy(0.5-Sqrt(delta*(1 - delta)),GF(2));
end intrinsic;


// Plotkin upper bound,		Lancelot Pecquet, 1996
//                              re-written in 2002, GW

intrinsic PlotkinBound(K::FldFin,n::RngIntElt,d::RngIntElt) -> RngIntElt
{Return the Plotkin upper bound of the cardinality of a largest code of
length n and dimension d over the field K}
    requirege n,1;
    requirerange d,1,n;
        //first binary case
    if #K eq 2 then
        if IsEven(d) then
            //first for d even
            require n le 2*d : "Require n <= 2*d for even weight binary case";
            if n lt 2*d then
                return 2*Floor( d / (2*d-n) );
            elif n eq 2*d then
                return 4*d;
            end if;
        else
            //now for d odd
            require n le 2*d+1 : "Require n <= 2*d + 1 for odd weight binary cas
e";
            if n lt 2*d+1 then
                return 2*Floor( (d+1) / (2*d+1-n) );
            elif n eq 2*d+1 then
                return 4*d + 4;
            end if;
        end if;
	    //should never get to here;
        error "INTERNAL ERROR";
    end if;

    //now the general non-binary case

    tn := (1 - 1/#K)*n;
    require d gt tn : "Require d > (1 - 1/#K)*n for non binary case";

    return Floor(d/(d - tn));
end intrinsic;


// Test for code's equidistance		Lancelot Pecquet, 1996

intrinsic IsEquidistant(C::CodeLinFld) -> BoolElt
{Return true if the code is equidistant, else return false}
	if (#C eq PlotkinBound(Alphabet(C),Length(C),MinimumDistance(C))) then
		return true;
	else
		return false;
	end if;
end intrinsic;


// Plotkin asymptotic bound		Lancelot Pecquet, 1996

intrinsic PlotkinAsymptoticBound(K::FldFin,delta::FldReElt)->FldReElt
{Return the Plotkin asymptotic upper bound of the information rate for delta 
in [0, 1] over the field K}
	theta := 1 - 1/#K;
	require delta ge 0:"Argument 1 should be in [0,1]";
	require delta le 1:"Argument 1 should be in [0,1]";
	if (delta gt theta) then
		return 0;
	else
		return 1 - delta/theta;
	end if;
end intrinsic;

// Singleton upper bound to A(n,d)		Lancelot Pecquet, 1996

intrinsic SingletonBound(K::FldFin,n::RngIntElt,d::RngIntElt) -> RngIntElt
{Return the Singleton upper bound of the cardinality of a largest code of
length n, minimum distance d over the field K}
	requirege n,1;
	requirerange d,1,n;
	return #K^(n-d+1);
end intrinsic;


/*
// Test for Minimum Distance Separable codes	Lancelot Pecquet, 1996

intrinsic IsMDS(C::CodeLinFld) -> BoolElt
{Return true if C is Maximum Distance Separable, else return false}
	if (#C eq SingletonBound(Alphabet(C),Length(C),MinimumDistance(C))) then
		return true;
	else
		return false;
	end if;
end intrinsic;
*/

intrinsic SingletonAsymptoticBound(delta::FldReElt)->FldReElt
{Return the Singleton asymptotic upper bound of the information rate for 
delta in [0, 1] over any finite field}
	require delta ge 0:"Argument 1 should be in [0,1]";
	require delta le 1:"Argument 1 should be in [0,1]";
	return 1 - delta;
end intrinsic;

// Volume of a sphere over a finite field	Lancelot Pecquet, 1996

intrinsic SphereVolume(K::FldFin,n::RngIntElt,r::RngIntElt) -> RngIntElt
{Computes the volume of the closed ball of radius r in the vector space K^n}
	requirege n,1;
	requirerange r,0,n;
	qm1 := #K - 1;
	if (r le n div 2) then
		res := 0;
		bino := 1;
		qm1pi := 1;
		for i in [0 .. r] do
			res +:= bino*qm1pi;
			qm1pi *:= qm1;
			bino *:= (n-i);
			bino /:= (i+1);		//C_n^i	
		end for;
		return IntegerRing()!res;
//		return &+[Binomial(n,i)*(qm1^i) :i in [0 .. r]];
	else
		if r eq n then
			return #K^n;
		else
			rp1 := r+1;
			res := 0;
			bino := Binomial(n,rp1);
			qm1pi := 1;
			for i in [0 .. n-rp1] do
				res +:= bino*qm1pi;
				qm1pi *:= qm1;
//				print bino = Binomial(n,rp1+i);
				bino *:= (n-i)-rp1;
				bino /:= (i+1)+rp1;	//C_n^r+1+i
			end for;
			res *:= qm1^rp1;
			return #K^n - IntegerRing()!res;
//			return #K^n - &+[qm1^(rp1)*Binomial(n,rp1+i)*(qm1^i) 
//			:i in [0 .. n-(rp1)]];
		end if;
	end if;
end intrinsic;


// Spheres packing upper bound		Lancelot Pecquet, 1996

intrinsic SpheresPackingBound(K::FldFin,n::RngIntElt,d::RngIntElt) -> RngIntElt
{Return the Hamming sphere packing upper bound of the cardinality of a
largest codes of length n and minimum distance d over the field K}
        requirege n,1;
        requirerange d,1,n;
        return SpherePackingBound(K,n,d);
end intrinsic;

intrinsic SpherePackingBound(K::FldFin,n::RngIntElt,d::RngIntElt) -> RngIntElt
{Return the Hamming sphere packing upper bound of the cardinality of a
largest codes of length n and minimum distance d over the field K}
	requirege n,1;
	requirerange d,1,n;
	r := Floor((d-1)/2);
	q := #K;
	return Floor(q^n / SphereVolume(K,n,r));
end intrinsic;


// Test for code perfection		Lancelot Pecquet, 1996

intrinsic IsPerfect(C::CodeLinFld) -> BoolElt
{Return true if C is a perfect code, else return false}
	if #C eq SpheresPackingBound(Alphabet(C),Length(C),MinimumDistance(C)) then
		return true;
	else
		return false;
	end if;
end intrinsic;



// Hamming asymptotic bound		Lancelot Pecquet, 1996

intrinsic HammingAsymptoticBound(K::FldFin,delta::FldReElt)->FldReElt
{Return the Hamming asymptotic upper bound of the information rate 
for delta in [0, 1] over the field K}
	theta := 1 - 1/#K;
	require delta ge 0:"Argument 1 should be in [0,1]";
	require delta le 1:"Argument 1 should be in [0,1]";	
	return 1 - Entropy(delta/2,K);
end intrinsic;


// Lower bound for the size of a largest linear code, demo in van Lint's book
// Lancelot Pecquet, 1996

intrinsic VanLintBound(K::FldFin,n::RngIntElt,d::RngIntElt) -> RngIntElt
{Return the "Van Lint" lower bound to the size of a largest linear code of
length n and minimum distance d over the field K}
	requirege n,1;
	requirerange d,1,n;
	q := #K;
	if (n eq 1) then
		k := 1;
	elif (d eq 1) then
		k := n;
	elif (d eq 2) then
		k := 1;
	else
		V := SphereVolume(K,n-1,d-2);
		b,pow := IsPowerOf(V,q);
		if b then
			k := n - 1 - pow;
		else
			k := n - Ceiling(Log(q, V));
		end if;
	end if;
	return q^k;
end intrinsic;
