freeze;

//$Id:: order.m 2650 2014-05-27 01:26:16Z eobr007                          $:
// Changes by Allan Steel to improve performance for matrix groups Oct 2012 

/* 
intrinsic IsCentral (G :: Grp, g :: GrpElt) -> BoolElt
{If g central in G, return true, else false}
    if IsIdentity (g) then return true; end if;
    if Type (G) eq GrpMat and IsFinite (BaseRing (G)) and
       IsAbsolutelyIrreducible (G) then
       return IsScalar (g);
    end if;
    H := Generic (G); id := Identity (H); 
    g := H!g; gens := [H!G.i: i in [1..Ngens (G)]];
// g; gens;
if Type (G) eq GrpAb then "HERE is input "; G: Magma; g: Magma; end if;
    return forall{x : x in gens | x*g eq g*x};
    return forall{x : x in gens | (x, g) eq id};
    // return forall{i : i in [1 .. Ngens(G)] | (H ! g, H ! G.i) eq id};
end intrinsic;

*/

intrinsic IsCentral (G :: GrpMat, g :: GrpMatElt) -> BoolElt
{If g central in G, return true, else false}
    if IsIdentity (g) then return true; end if;
    if Type (G) eq GrpMat and IsFinite (BaseRing (G)) and
       IsAbsolutelyIrreducible (G) then
       return IsScalar (g);
    end if;
    H := Generic (G); id := Identity (H); 
    g := H!g; gens := [H!G.i: i in [1..Ngens (G)]];
    // return forall{x : x in gens | x*g eq g*x};
    return forall{x : x in gens | (x, g) eq id};
end intrinsic;

intrinsic IsCentral (G :: GrpPerm, g :: GrpPermElt) -> BoolElt
{If g central in G, return true, else false}
    if IsIdentity (g) then return true; end if;
    H := Generic (G); id := Identity (H); 
    g := H!g; gens := [H!G.i: i in [1..Ngens (G)]];
    return forall{x : x in gens | x*g eq g*x};
end intrinsic;

intrinsic IsCentral (G :: GrpAb, g :: GrpAbElt) -> BoolElt
{If g central in G, return true, else false}
    return true;
end intrinsic;

intrinsic IsCentral (G :: GrpPC, g :: GrpPCElt) -> BoolElt
{If g central in G, return true, else false}
    if IsIdentity (g) then return true; end if;
    gens := [G.i : i in [1..Ngens (G)]]; id := G.0;
    return forall{x : x in gens | (x, g) eq id};
end intrinsic;

function MyPow(g: CGens := 0)
    //L, T := Can(Matrix(g));
    _, T, L := PrimaryRationalForm(Matrix(g));
    TI := T^-1;
    MA := Parent(T);
    x := Parent(L[1, 1]).1;
    P := Generic(Parent(g));

    if CGens cmpne 0 then

	CGens := [T*X*TI: X in CGens];

	K := BaseRing(x);
	p := Characteristic(K);
	q := #K;

	return function(n)
	    M := <>;
	    pos := 1;
	    BL := <>;
	    posL := [];
	    for t in L do

		/*
		The following is equivalent to setting g to Modexp(x, n, f),
		but is a bit more efficient (uses smaller exponent).
		*/

		f := t[1];
		d := Degree(f);
		m := q^d - 1;
		e := t[2];
		if e gt 1 then
		    beta := Ilog(p, e - 1) + 1;
		    m *:= p^beta;
		    f ^:= e;
		    d *:= e;
		end if;
		nm := n mod m;
		g := Modexp(x, nm, f);

		//assert g eq Modexp(x, n, f);

		/*
		f := t[1]^t[2];
		d := Degree(f);
		g := Modexp(x, n, f);
		*/

		//f, g;

		B := [];
		for i := 0 to d - 1 do
		    B cat:= EltseqPad(g, d);
		    g := (g*x) mod f;
		end for;

		B := Matrix(d, B);
		Append(~BL, B);
		Append(~posL, pos);
		pos +:= d;
	    end for;

	    for X in CGens do
		LS := MA!0;
		RS := MA!0;

		for i := 1 to #BL do
		    pos := posL[i];
		    B := BL[i];
		    d := Ncols(B);
		    LB := B * RowSubmatrix(X, pos, d);
		    InsertBlock(~LS, LB, pos, 1);
		    RB := ColumnSubmatrix(X, pos, d) * B;
		    InsertBlock(~RS, RB, 1, pos);
		    delete LB, RB;
		end for;

		if LS ne RS then
		    return false;
		end if;
	    end for;
	    return true;
	end function, L;
    else
	return function(n)
	    M := <>;
	    pos := 1;
	    S := MA!0;
	    for t in L do
		f := t[1]^t[2];
		g := Modexp(x, n, f);
		//f, g;
		d := Degree(f);
		B := [];
		for i := 0 to d - 1 do
		    B cat:= EltseqPad(g, d);
		    g := (g*x) mod f;
		end for;
		B := Matrix(d, B);
		B := B * RowSubmatrix(T, pos, d);
		InsertBlock(~S, B, pos, 1);
		delete B;
		pos +:= d;
	    end for;
	    return P!(TI*S);
	end function, L;
    end if;
end function;


// smallest n such that g^n is central in H 
MyCentralOrder := function (H, g : Proof := true)

    if IsIdentity (g) then return 1, true; end if;

    if Type (H) eq GrpMat and IsFinite (BaseRing (H)) 
       and IsAbsolutelyIrreducible (H) then
       o, _, flag := ProjectiveOrder (g: Proof := Proof);
       return o, flag;
    end if;
    
    if IsCentral (H, g) then return 1, true; end if;

    USE_MyPow2 := false;
    USE_MyPow2 := true ; // and Ngens(H) le 2;

    USE_MyPow := false;
    USE_MyPow := true;

// EOB addition
if Type (g) eq GrpPermElt then
   USE_MyPow := false;
   USE_MyPow2 := false;
end if;


    if USE_MyPow2 then
	pow_ic, L := MyPow(g: CGens := [H.i: i in [1..Ngens(H)]]);

	mp := LCM([t[1]^t[2]: t in L]);
//assert mp eq MinimalPolynomial(g);
	fo := FactoredOrder(mp: Proof := Proof);
//assert fo eq FactoredOrder(g);
	if #fo eq 1 and fo[1, 2] eq 1 then return fo[1, 1], Proof; end if;
	proof := Proof;
    else
	if Type (H) eq GrpMat and IsFinite (BaseRing (H))  then 
	   fo, proof := FactoredOrder (g: Proof := Proof);
	else
// EOB addition
if Type (g) eq GrpPermElt then o := Order (g); fo := Factorisation (o);
else 
	   fo := FactoredOrder (g);
end if;
	   proof := true;
	end if;

	// if IsPrime (o) then return o, proof; end if;
	if #fo eq 1 and fo[1, 2] eq 1 then return fo[1, 1], proof; end if;

	if USE_MyPow then
	    pow := MyPow(g);
	end if;
    end if;

    //primes := Factorisation (o);
    primes := fo;
    o := FactorizationToInteger(fo);

    for j in [1..#primes] do
	p := primes[j][1];
	m := primes[j][2];
	k := 0;
	found := false;
	repeat
	    n := o div p;
	    if USE_MyPow2 then
		ic := pow_ic(n);
	    else
		if USE_MyPow then
		    h := pow(n);
		else
		    h := g^n;
		end if;
		ic := IsCentral (H, h);
	    end if;
	    if ic then
		o := n;
	    else
		found := true;
	    end if;
	    k +:= 1;
	until found or (k eq m);
    end for;
    return o, proof;
end function;

intrinsic CentralOrder (g:: GrpMatElt: ParentGroup := Parent (g),
                            Proof := true) -> RngIntElt, BoolElt
{return smallest n such that g^n is central in its parent,
 which can be supplied as the optional argument ParentGroup.
 If Proof is false then accept a multiple of this value;
 the second value returned is true if the answer is exact.}
 return MyCentralOrder (ParentGroup, g: Proof := Proof);
end intrinsic;

intrinsic CentralOrder (g:: GrpPermElt: ParentGroup := Parent (g),
                            Proof := true) -> RngIntElt, BoolElt
{return smallest n such that g^n is central in its parent,
 which can be supplied as the optional argument ParentGroup.
 If Proof is false then accept a multiple of this value;
 the second value returned is true if the answer is exact.}
 return MyCentralOrder (ParentGroup, g: Proof := Proof);
end intrinsic;

MyRandomElementOfOrder := function (G, order:
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)), 
    MaxTries := 100, Central := false, Proof := true) 

    local g, q, r, w, i;

    if Central then fct := CentralOrder; else fct := Order; end if;
    i := 0;
    repeat
	g, w := Random(Randomiser);

	// compute order 
	if Type (g) eq GrpMatElt then     
           o, precise := fct(g : Proof := Proof);
           q, r := Quotrem(o, order);
	else 
           q, r := Quotrem(fct(g), order);
           precise := true;
        end if;
	i +:= 1;
    until r eq 0 or (i ge MaxTries and MaxTries gt 0);

    if r ne 0 then
	vprint UserUtil, 1: "Element of order", order,
	    "not found in", MaxTries, "attempts";
	return false, _, _, _;
    end if;

    return true, g^q, w^q, precise;
end function;

function MyRandomElementOfPrimeOrder(G, order :
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)), 
    MaxTries := 100) 
    local i, g, w, n, flag;

    i := 0;
    repeat
	g, w := Random(Randomiser);

	flag, n := PrimeOrderElement(g, order);
	i +:= 1;
    until flag or (i ge MaxTries and MaxTries gt 0);

    if not flag then
	vprint UserUtil, 1: "Element of order", order,
	    "not found in", MaxTries, "attempts";
	return false, _, _;
    end if;

    return true, g^n, w^n;
end function;

intrinsic RandomElementOfPrimeOrder(G :: GrpMat, order :: RngIntElt :
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)), 
    MaxTries := 100) 
    -> BoolElt, GrpMatElt, GrpSLPElt
    { Search for a random element of specified prime order.
      If such is found, then return true, the element, and its SLP.
      MaxTries is the maximum number of random elements that are chosen. 
      Randomiser is the random process used to construct these,
      and the SLP for the returned element is in the word group of 
      this process. 
    }

    return MyRandomElementOfPrimeOrder (G, order : 
	Randomiser := Randomiser, MaxTries := MaxTries); 
end intrinsic;

intrinsic RandomElementOfPrimeOrder(G :: GrpPerm, order :: RngIntElt :
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)), 
    MaxTries := 100) 
    -> BoolElt, GrpPermElt, GrpSLPElt
    { Search for a random element of specified prime order.
      If such is found, then return true, the element, and its SLP.
      MaxTries is the maximum number of random elements that are chosen. 
      Randomiser is the random process used to construct these,
      and the SLP for the returned element is in the word group of 
      this process. 
    }

    return MyRandomElementOfPrimeOrder (G, order : 
	Randomiser := Randomiser, MaxTries := MaxTries); 
end intrinsic;

intrinsic RandomElementOfOrder(G :: GrpMat, order :: RngIntElt :
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)), 
    MaxTries := 100, Central := false, Proof := true) 
    -> BoolElt, GrpMatElt, GrpSLPElt, BoolElt
    { Search for a random element of specified order.
      If such is found, then return true, the element, and its SLP.
      If Proof is false, then accept
      an element whose order may be a multiple of the desired order.
      The final value returned indicates whether
      the element is known to have the precise order. 
      If Central then search for an element which has this order 
      modulo the centre of G.
      MaxTries is the maximum number of random elements that are chosen. 
      Randomiser is the random process used to construct these,
      and the SLP for the returned element is in the word group of 
      this process. 
    }
    return MyRandomElementOfOrder (G, order: Central := Central, 
    Randomiser := Randomiser, MaxTries := MaxTries, Proof := Proof); 

end intrinsic;

intrinsic RandomElementOfOrder(G :: GrpPerm, order :: RngIntElt :
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)), 
    Central := false, MaxTries := 100) -> BoolElt, GrpPermElt, GrpSLPElt
    { Search for a random element of specified order.
      If such is found, then return true, the element, and its SLP. 
      If Central then search for an element which has this order 
      modulo the centre of G.
      MaxTries is the maximum number of random elements that are chosen. 
      Randomiser is the random process used to construct 
      these, and the SLP for the returned element is in the word 
      group of this process. 
    }
    return MyRandomElementOfOrder (G, order:
    Central := Central, Randomiser := Randomiser, MaxTries := MaxTries);
end intrinsic;

/* multiplicative upper bound for order of x */

MultiplicativeUpperbound := function (x)
   F := BaseRing (Parent (x));
   p := Characteristic (F);
   q := #F;
   m := MinimalPolynomial (x);
   facs := Factorisation (m);
   degs := [Degree (facs[i][1]): i in [1..#facs]];
   alpha := Maximum ([facs[i][2]: i in [1..#facs]]);
   beta := Ceiling (Log (p, alpha));
   bound := LCM ([q^i - 1: i in degs]) * p^beta;
   return bound;
end function;

/* obtain an upper bound for the order of x as 2^k * odd,
   where the power k of 2 in the factorisation is correct; 
   c^(o * bound) is the identity, o = 2^k and y = c^bound 
   bound is odd */ 

EstimateOrder := function (x)
   bound := MultiplicativeUpperbound (x);
   /* largest odd divisor of upper bound */
   k := 0; while bound mod 2 eq 0 do k +:= 1; bound div:= 2; end while;
   /* obtain element of even order by powering up odd part */
   if k gt 0 then y := x^bound; else y := x^0; end if;
   o := Order (y);
   return bound * o, y, o, bound;
end function;

/* can we obtain an involution which is a power of x? 
   if degree and field is large, then powering up odd 
   part of x and computing order of resulting 2-power element 
   is faster than computing the order of x */

InvolutionIsPower := function (x: w := [])
   // "method 1";

   bound := MultiplicativeUpperbound (x);
   /* largest odd divisor of upper bound */
   while bound mod 2 eq 0 do bound div:= 2; end while;

   /* obtain element of even order by powering up odd part */
   y := x^bound;
   o := Order (y);
   if IsEven (o) then
      y := y^(o div 2);
      if not (w cmpeq []) then 
         w := w^bound; w := w^(o div 2); return true, y, w;
      end if;
      return true, y, _;
   else
      return false, _, _;
   end if;
end function;

OrderToInvolution := function (y: w := [])
    // "method 2";
   o := Order (y: Proof := false);
   if IsEven (o) then
      o := o div 2;
      y := y^(o);
      if not (w cmpeq []) then 
         w := w^(o); return true, y, w;
      end if;
      return true, y, _;
   else
      return false, _, _;
   end if;
end function;

GenerateInvolution := function (G: Words := true)
   
   if Words cmpeq true then 
      x, w := RandomWord (G);
   else 
      x := Random (G);
      w := [];
   end if;

   F := BaseRing (G);
   p := Characteristic (F);
   e := Degree (F);
   d := Degree (G);

   if   d ge 20 and p ge  5 and e ge 1 then return InvolutionIsPower (x: w := w);
   elif d ge 13 and p ge 11 and e ge 2 then return InvolutionIsPower (x: w := w);
   elif d ge  9 and p ge 11 and e ge 4 then return InvolutionIsPower (x: w := w);
   elif d ge  5 and p ge 11 and e ge 4 then return InvolutionIsPower (x: w := w);
   elif d eq  4 and p ge 11 and e ge 7 then return InvolutionIsPower (x: w := w);
   elif d eq  3 and p ge 11 and e ge 9 then return InvolutionIsPower (x: w := w);
   elif d ge  4 and p eq  7 and e ge 8 then return InvolutionIsPower (x: w := w);
   elif d ge  4 and p eq  5 and e ge 8 then return InvolutionIsPower (x: w := w);
   elif d ge  4 and p eq  3 and e ge 10 then return InvolutionIsPower (x: w := w);
   else return OrderToInvolution (x : w := w); end if;
end function;

intrinsic ElementOfOrder (G :: Grp, RequiredOrder, 
          Limit:: RngIntElt: Word := true, Fct := Order) -> GrpMatElt
{Fct can be Order or ProjectiveOrder; search at most Limit times for 
 element of (projective) order RequiredOrder; if found return element
 and possibly word, else return false}

   if Type (G) ne GrpMat then Fct := Order; end if;

   if not Word then 
      P := RandomProcess (G); 
   end if;

   if Type (RequiredOrder) eq RngIntElt then
      RequiredOrder := {RequiredOrder};
   end if;

   NmrTries := Limit;
   repeat
      if Word then 
         g, wg := RandomWord (G);
         if Type (g) eq BoolElt then return false, _; end if;
      else 
         g := Random (P);
      end if;
      o := Fct (g);
      NmrTries -:= 1;
      rem := exists (x) {x : x in RequiredOrder | (o mod x eq 0)};
   until rem or (NmrTries eq 0);

   if rem then o := o div x; 
      if Word then return g^o, wg^o; else return g^o, _; end if; 
   end if;

   return false, _;

end intrinsic;

intrinsic PrimePowerOrderElement(g :: GrpElt, p :: RngIntElt :
    Proof := false) ->
    BoolElt, GrpElt, RngIntElt, RngIntElt, BoolElt
    { p is a prime. Determine if p divides the order of g and if so 
      return true, an element h of order a power of p, a 
      multiplicative upper bound for order of h, 
      the power of g equal to h, and a flag indicating if the upper bound
      is the true order. }

   if not IsPrime(p) then
      error "p must be a prime number";
   end if;

   // Avoid integer factorisation if Proof is false,
   // obtain multiplicative upper bound
   if Type (g) eq GrpMatElt then 
      n, precise := Order (g : Proof := Proof);
   else 
      n := Order(g);
      precise := true; 
   end if;

   k, s := Valuation (n, p);
   b := g^s;
   return IsIdentity (b) eq false, b, p^k, s, precise;
end intrinsic;

intrinsic PrimeOrderElement(g :: GrpElt, p :: RngIntElt) -> BoolElt, RngIntElt
    { p is a prime. Determine if p divides the order of g and if so return true
    and the power of g which gives an element of order p.

    The algorithm is Las Vegas polynomial time, in particular it avoids
    integer factorisation. }
    
    flag, b, n, s, precise := PrimePowerOrderElement(g, p);

    if flag then
	if precise then
	    flag, r := IsDivisibleBy(n, p);
	    assert flag;
	    
	    return true, s * r;
	else
	    k := Valuation(n, p);
	
	    // Binary search for the correct power
	    bounds := [1, k];
	    while bounds[2] gt bounds[1] do
		i := Floor(&+bounds / 2);
		
		if IsIdentity(b^(p^i)) then
		    bounds[2] := i;
		else
		    bounds[1] := i + 1;
		end if;
	    end while;
	
	    return true, s * (p^(bounds[1] - 1));
	end if;
    else
	return false, _;
    end if;
end intrinsic;

function RandomInvolution(G :
    Randomiser := RandomProcessWithWords(G : WordGroup :=
	WordGroup(G)), MaxTries := 1000) 
	/* Wrapper around RandomElementOfOrder. */
    
    repeat
	flag, g, slp := RandomElementOfPrimeOrder(G, 2 : Randomiser := Randomiser,
	    MaxTries := MaxTries);
    until flag;

    return g, slp;
end function;

function IsProbablySL2(G : Randomiser := RandomProcess(G),
    ErrorProb := 2^(-100), Projective := false, q := #CoefficientRing(G)) 
    /* G \leq GL(d, q). Determines if (P)SL(d, q) is contained in G. The
    algorithm is one-sided Monte Carlo and a positive answer is always
    correct. The error probability is at most ErrorProb.

    Randomiser is used to find random elements of G. If Projective is true then
    PSL rather than SL is used. */
    local foundFirst, foundSecond, order, i, prob, nrElements;

    foundFirst := false;
    foundSecond := false;
    i := 0;

    // EOB -- added next line since SL(2, q) = PSL(2, q) when q is even 
    if IsEven (q) then Projective := false; end if;

    // A crude estimate of the error probability is used
    nrElements := Ceiling(Log(ErrorProb) / Log((1 - EulerPhi(q - 1) / (q - 1))
	* (1 - EulerPhi(q + 1) / (q + 1))));

    nrElements := Max(nrElements, 100);    
    vprintf UserUtil, 2: "Checking %o elements\n", nrElements;
    
    if Category(G) eq GrpMat then
	fct := func<g | Order(g : Proof := false)>;
    else
	fct := func<g | Order(g)>;
    end if;

    goodOrder1 := (Projective eq true select (q - 1) div 2 else (q - 1));
    goodOrder2 := (Projective eq true select (q + 1) div 2 else (q + 1));
    
    // If we can find elements of order (q ± 1) / 2 then we have PSL(2, q)
    repeat
	order := fct(Random(Randomiser));
	    
	if order eq goodOrder1 then
	    foundFirst := true;
        elif order eq goodOrder2 then
	    foundSecond := true;
	end if;

	i +:= 1;
    until i ge nrElements or (foundSecond and foundFirst);

    return foundFirst and foundSecond;
end function;

/* 
Nmr := 100;
p := 7;
repeat 
for i in [10..12 by 1] do
   for d in [2 .. 20 by 1] do 
      F := GF (p^i);
      G := SL (d, F);
//      "d = ", d, "p = ", p, "i = ", i; 
//      "==============================";
      result := 0;
      for k in [1..Nmr] do 
      x := Random (G);
      y := x;
      t := Cputime ();
      a := IsPowerInvolution (x);
      t1 := Cputime (t);
      delete x;
      t := Cputime ();
      b := Test2 (y);
      t2 := Cputime (t);
      result +:= t1 - t2;
      end for;
      // "Smaller? ", t1, t2, t1 le t2, t2 - t1; 
    if result gt 0 then 
      "d = ", d, "p = ", p, "i = ", i; "result ", result;
      "==============================";
       end if;
   end for;
end for;
p := NextPrime (p);
until p gt 7;
*/
