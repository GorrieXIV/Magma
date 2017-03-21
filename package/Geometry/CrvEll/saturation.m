freeze;

/********************************************************************

  Saturation of the group spanned by given points of infinite order
  in elliptic curves over Q and number fields
 
  Steve Donnelly, November 2005

  Last modified: November 2013

**********************************************************************

OUTLINE AND REMARKS

   The basic idea is explained in Samir Siksek's paper "Infinite Descent
   on Elliptic Curves", and runs as follows: for P in E(K), if the
   equation p*R = P admits no solution R in E(K), then it admits
   no solution over F_q for some suitable prime q. Thus, if we are given
   a subgroup G < E(K), we hope to efficiently identify the "p-divisible part of G",
   namely { P in G : p*R = P for some R in E(K) }, by reducing at enough primes q.
   
   For each prime p,
      1) Except in the "special case", find a prime q such that #E(Fq)[p] = p. 
      2) Construct a homomorphism G -> E(Fq)[p] = Z/p by
      				  P :-> m*( Pbar ), where m = #E(Fq)/p.
         The "p-divisible part of G" must be contained in the kernel. 
      3) Repeat steps 1 and 2, intersecting the kernels, until empty, 
         or until we've tried at least 30+Rank(E) different primes q.
      4) If we're not done, or if we're in the "special case", we go through
         an analogous procedure, using primes q such that #E(Fq)[p] = p^2.
	 This time for each q we get two homomorphisms are, namely 
	 for T = T1 or T2 where E(Fq)[p] = <T1,T2>,
	 	G  -> E(Fq)[p]    ->   mu_p(Fq) = Z/p	
		P :-> m*( Pbar ) :-> WeilPairing( T, . )
		  where m = 1/p( exponent of E(Fq) ).
      5) If we haven't proved p-saturation, test each P in the
         remaining subgroup by actually trying to solve p*R = P.
	 (well actually, test one P in each cyclic subgroup).

   Fact: There always exist primes q as in Step 1, except in the case
         (obviously) where all p-torsion is defined over K, or in the
         case where E(K)[p] is trivial but any extension containing one
         p-torion point contains them all.  
         When K has at least one real place, this happens precisely when
         p = 2 and the discriminant of E is a square.
         We refer to this as the "special case".
   Proof: For odd p, the extension K_1/Q obtained by adjoining one element 
         of E[p] is smaller than K_all/Q obtained by adjoining all of them
	 (because over the reals, you get one cyclic subgroup but not all).
	 So, by Cebotarev, there exist primes q with a degree one factor
	 in K_1 but not in K_all.
	 For p = 2, K_1 = K_all iff K_all is K or cyclic of degree 3,
         which holds iff the discriminant of the cubic is a square.
	
   OBVIOUS QUESTION: 
         Can it happen that P is not in p*E(K), but is in p*E(Fq) for all q 
         that we are allowed to use in step 1, or in both steps 1 and 4?
   ANSWERS:
       1) If P is not in p*E(K), then P is not in p*E(Fq) for all primes q.
          This is proved in Martin Prickett's thesis.
       2) In some cases Step 4 is certainly needed to prove saturation.
          One such situation, to do with the existence of a p-isogeny,
          is in Martin Prickett's thesis.
          Another (different?) situation occurs because decomposition groups 
          at unramified primes are cyclic. Let K_1 := K( one p-torsion point ) 
          and let L := K( all p-torsion points, and all R satisfying p*R=P ).
	  L/K_1 is Galois, and it can happen that every cyclic subgroup of Gal(L/K_1)
	  either fixes all the p-torsion, or fixes one of the R's. Therefore, for
	  every q such that E(Fq) has one p-torsion point, E(Fq) must either contain
	  all the p-torsion, or contain one of the R's. In particular, for every
	  prime allowed in Step 1, P will be in p*E(Fq). (This is why we try Step 4
	  if we're not done after Step 1.)

   NOTES
    + Optimizations are based on the assumption that the input is nearly saturated.
    + Step 5 simply calls IsDivisibleBy(pt, p)
    + In the NF case, it is sufficient to use degree 1 primes.

   TO DO
    + lookup table for Eq?

*************************************************************************************

EXAMPLES

 SetVerbose("Saturation", 2);

 // cannot be saturated at 3 without step 4 (due to 3-isogeny)
 E := EllipticCurve("254a2");
 pts := Generators(E);
 sat := Saturation(E, 3);

************************************************************************************/

declare verbose ECSaturation, 3;


function reduce(P, q, res, Eq)
    P := Eltseq(P);
    try
        return Eq! [c@res : c in P];
    catch E
        v := Min([Valuation(c,q) : c in P]);
        assert v lt 0;
        u := UniformizingElement(q) ^ -v;
        return Eq! [(u*c)@res : c in P];
    end try;
end function;


// Precomputation
// for each prime p in [1..N], list primes q with p|#Eq
// pqDB[p] = sorted sequence of q's

function pqDatabase(E, N, B)
    ps := PrimesUpTo(N);
    qs := PrimesUpTo(B);
    empty := [Integers()|];
    pqDB := [];
    for p in ps do 
        pqDB[p] := empty;
    end for;
    orders := AssociativeArray();
    bad := LCM([Denominator(c) : c in Coefficients(E)] cat 
               [Numerator(Discriminant(E))]);
    for q in qs do
        if bad mod q ne 0 then
	    orderq := q + 1 - TraceOfFrobeniusDirect(E,q);
	    for tup in Factorization(orderq) do
	    	p := tup[1];
                if p gt N then
                   break;
                else

                   // Append(~pqDB[p], q);
                   // This does not append in place (November 2013)
                   // Geoff's workaround ensures tmp has only 1 ref:
                   tmp     := pqDB[p];
                   pqDB[p] := empty;
                   Append(~tmp, q);
                   pqDB[p] := tmp;
                   delete tmp;

                   orders[q] := orderq;
		end if;
	    end for;
	end if;
    end for;
    return [* pqDB, orders *], bad;
end function;


// TO DO: for E over Q, only do one q from each conjugacy class

function pqDatabase_NF(E, N, B)

    K := BaseRing(E);
    ZK := Integers(K);
    PI := PowerIdeal(ZK);

    bad := LCM([Integers()| Denominator(c) : c in Coefficients(E)]);
    disc := Discriminant(E);
    while Denominator(disc) ne 1 do
        disc *:= bad;
    end while;
    bad *:= Norm(disc); 
    bad *:= Discriminant(ZK);
    bad := Integers() ! bad;

    ps := PrimesUpTo(N);
    qs := PrimesUpTo(B, K : coprime_to := bad);
    qs := [Universe(qs)| q : q in qs | Degree(q) eq 1];
    // TO DO: PrimesUpTo option to compute only degree 1 primes
    assert IsIdentical(PI, Universe(qs));

    pqDB := AssociativeArray();
    empty := [Parent(<1,1*ZK>) | ];
    for p in ps do
        pqDB[p] := empty;
    end for;
    orders := AssociativeArray();

    for q in qs do
        Nq := Norm(q);
        orderq := Nq + 1 - TraceOfFrobenius(E,q);
        for tup in Factorization(orderq) do
            p := tup[1];
            if p le N then 
               // Append(~pqDB[p], <Nq, q, orderq>);
               // This does not append in place (November 2013)
               // Geoff's workaround ensures tmp has only 1 ref:
               tmp     := pqDB[p];
               pqDB[p] := empty;
               Append(~tmp,  <Nq, q>);
               pqDB[p] := tmp;
               delete tmp;

               orders[q] := orderq;
            else
               break;
            end if;
        end for;
    end for;

    return [* pqDB, orders *], bad;
end function;


// Find a good prime q such that #E(F_q)[p] = p
// i = index in DB 
// q0 = starting point for search

function findq (E, p, bad, pqDB, i, q0, fldrat)

     Ecoeffs := Coefficients(E);

     // First look in pqDB
     pqDBp := pqDB[1,p];
     orders := pqDB[2];
     if fldrat then
         while i lt #pqDBp do
             i := i + 1;
             q := pqDBp[i];
             if p eq 2 or (q mod p) ne 1 then
                 Eq := EllipticCurve(ChangeUniverse(Ecoeffs, GF(q)));
                 if p ne 2 or #TwoTorsionSubgroup(Eq) eq 2 then 	
                     return q, orders[q] div p, Eq, _, i, q0;
                 end if;
             end if;
         end while;
     else
         while i lt #pqDBp do
             i := i + 1;
             Nq := pqDBp[i,1];
             if p eq 2 or (Nq mod p) ne 1 then
                 q := pqDBp[i,2];
                 _, res := ResidueClassField(q);
                 Eq := EllipticCurve([c@res : c in Ecoeffs]);
                 if p ne 2 or #TwoTorsionSubgroup(Eq) eq 2 then 	
                     return q, orders[q] div p, Eq, res, i, q0;
                 end if;
             end if;
         end while;
     end if;

     vprintf ECSaturation, 2: "Searching for q (not precomputed): ";
     timeq := Cputime();

     if not fldrat then
         K := BaseRing(E);
         ZK := Integers(K);
     end if;

     // If #Eq = A*p , then A*p must be in a Hasse interval around q,
     // and so roughly speaking, q must be in a "Hasse interval" around A*p.
     // In view of Sato-Tate, we use only the middle part of each Hasse interval
     ST := 0.7;
     A := Ceiling(q0/p);
     delta := Ceiling(2*ST*Sqrt(A*p));
     if 2*delta lt p then
        interval := [A*p - delta, A*p + delta];
     else
        // intervals would overlap, so don't use intervals
        interval := [q0, Infinity()];
     end if;
     q := Max(q0, interval[1]);
     while true do 
         q := NextPrime(q);
         if q gt interval[2] then
            A := A + 1;
            delta := Ceiling(2*ST*Sqrt(A*p));
            if 2*delta lt p then
               interval := [A*p - delta, A*p + delta];
            else
               // intervals now overlap, so stop using intervals
               interval := [interval[2], Infinity()];
            end if;
            q := NextPrime(interval[1]);
         end if;

         // Ensure #E(F_q)[p] ne p^2
         if p ne 2 then
            while bad mod q eq 0 or q mod p eq 1 do
               q := NextPrime(q);
            end while;
         else 
            while bad mod q eq 0 do
               q := NextPrime(q);
            end while;
         end if;

         if fldrat then
             // Test whether #Eq is divisible by p
             order := q + 1 - TraceOfFrobeniusDirect(E,q);
             bool, m := IsDivisibleBy(order, p);
             if bool then
                 Eq := EllipticCurve(ChangeUniverse(Ecoeffs, GF(q)));
                 if p ne 2 or #TwoTorsionSubgroup(Eq) eq 2 then
                    vprintf ECSaturation, 2: "Found q = %o, %os\n", q, Cputime(timeq);
                    return q, m, Eq, _, i, q;
                 end if;
             end if;
             /* 
             // TO DO: is this trick ever better?
             if (q is large) and p le 4*Sqrt(q) then
                // A*p is the only multiple of p in the Hasse interval around q.
                // So p|#Eq <==> #Eq = A*p, and if this holds,
                // A*pt has order p with high probability for a random pt.
                // (Assume p and q are large here)
                Eq := EllipticCurve(ChangeUniverse(Ecoeffs, GF(q)));
                pt := A*Random(Eq);
                if p*pt eq Eq!0 and pt ne Eq!0 then 
                   m := A;
                   break;
                end if;
             end if;
             */
         else // fldnum
             if q gt Ceiling(100*p^1.5) then  // TO DO (do any cases need this?)
                 return 0, _, _, _, _, _;
             end if;
             Nq := q;
             qs := [t[1] : t in Factorization(Nq*ZK) | Norm(t[1]) eq Nq];
             // TO DO: fast way to get degree 1 primes
             for qq in qs do
                 _, res := ResidueClassField(qq);
                 Eq := EllipticCurve([c@res : c in Ecoeffs]);
                 order := Nq + 1 - TraceOfFrobenius(Eq);
                 bool, m := IsDivisibleBy(order, p);
                 if bool then
                    if p ne 2 or #TwoTorsionSubgroup(Eq) eq 2 then
                       vprintf ECSaturation, 2: "Found q of norm %o, %os\n", Nq, Cputime(timeq);
                       return qq, m, Eq, res, i, Nq;
                    end if;
                 end if;
             end for;
         end if;

     end while;

end function;


// find q such that #E(Fq)[p] = p^2

function findqSpecialCase (E, p, bad, pqDB, i, q0, fldrat)

    Ecoeffs := Coefficients(E);

    // First look in pqDB
    pqDBp := pqDB[1,p];
    if fldrat then
        while i lt #pqDBp do
            i := i + 1;
            q := pqDBp[i];
            if q mod p eq 1 then
                Eq := EllipticCurve(ChangeUniverse(Ecoeffs, GF(q)));
                EqA := AbelianGroup(Eq);
                if #[x : x in Invariants(EqA) | IsDivisibleBy(x,p)] eq 2 then
                    return q, Eq, _, i, q0;
               end if;
            end if;
        end while;
    else
        while i lt #pqDBp do
            i := i + 1;
            Nq := pqDBp[i,1];
            if Nq mod p eq 1 then
                q := pqDBp[i,2];
                _, res := ResidueClassField(q);
                Eq := EllipticCurve([c@res : c in Ecoeffs]);
                EqA := AbelianGroup(Eq);
                if #[x : x in Invariants(EqA) | IsDivisibleBy(x,p)] eq 2 then
                    return q, Eq, res, i, q0;
                end if;
            end if;
        end while;
    end if;

    // Now its a pretty naive search, quite slow

    vprintf ECSaturation, 2: "Searching for q (not precomputed, special case): ";
    timeq := Cputime();

    if not fldrat then
        K := BaseRing(E);
        ZK := Integers(K);
    end if;

    q := 1 + p*Floor(q0/p);     	
    while true do
        repeat
            q := p + q;
        until IsPrime(q) and not IsDivisibleBy(bad,q);
        if fldrat then
            order := q + 1 - TraceOfFrobeniusDirect(E,q);
            if not IsDivisibleBy(order,p) then continue; end if;
            Eq := EllipticCurve(ChangeUniverse(Ecoeffs, GF(q)));
            EqA := AbelianGroup(Eq);
            if #[x : x in Invariants(EqA) | IsDivisibleBy(x,p)] eq 2 then
                vprintf ECSaturation, 2: "Found q = %o, %os\n", q, Cputime(timeq);
                return q, Eq, _, i, q;
            end if;
        else
            Nq := q;
            qs := [t[1] : t in Factorization(Nq*ZK) | Norm(t[1]) eq Nq];
            for qq in qs do
                _, res := ResidueClassField(qq);
                Eq := EllipticCurve([c@res : c in Ecoeffs]);
                EqA := AbelianGroup(Eq);
                if #[x : x in Invariants(EqA) | IsDivisibleBy(x,p)] eq 2 then
                    vprintf ECSaturation, 2: "Found q of norm %o, %os\n", Nq, Cputime(timeq);
                    return qq, Eq, res, i, Nq;
                end if;
            end for;
        end if;
    end while;

end function;


intrinsic Saturation(points::SeqEnum[PtEll], N::RngIntElt :
                     OmitPrimes := [],
                     TorsionFree := false,
                     Check := true ) 
       -> SeqEnum[PtEll]
{Given a sequence of points on an elliptic curve over Q or a number field, 
returns a sequence of generators for the group obtained by saturating at 
all primes up to N.}
   
   E := Curve(Universe(points));
   K := BaseRing(E);
   fldrat := Type(K) eq FldRat;
   fldnum := ISA(Type(K), FldNum);

   require fldrat or fldnum:
       "The base ring must be Q or a number field";

   require fldrat or IsAbsoluteField(K):
       "Not implemented for relative extensions";

   if Check then 
       points := IndependentGenerators(points); 
   end if;

   T, Tmap := TorsionSubgroup(E);
   t := #Invariants(T);
   r := #points;
   tr := r + t;

   if r eq 0 or N le 1 then
       if TorsionFree then
           return points;
       else
           return [E(K)| Tmap(g) : g in Generators(T) ] cat points;
       end if;
   end if;

   // When E has CM defined over K, p is special when p is nonsplit in the CM field
   // TO DO:
   // larger database, because for nonsplit p,
   // Prob(p|#Eq given q = 1 mod p) is still 1/p asymptotically BUT need q > p^2

   if IsOdd(Degree(K)) then
       CM := false;
   else
       CM, CMd := HasComplexMultiplication(E);
       CM := CM and HasRoot(Polynomial([K| -CMd, 0, 1]));
   end if;

   // need to include torsion when checking p-divisibility (at least when p | #T)
   points := [ Tmap(g) : g in Generators(T) ] cat points;
   assert #points eq tr;

   // For each p, we will usually need r primes q which satisfy p|#E(Fq).  
   // This occurs with probability 1/p, so we will typically need to try 
   // the first O(r*N) primes.  Therefore taking C = r+1 below is natural. 
   // The "fudge constant" Cf then balances implemenational trade-offs
   // (the cost of precomputing primes that don't get used, vs the slower 
   // search for extra primes when not enough were precomputed).
   // Cf = 2 or 3 seems about right, currently; Cf = 3 means almost all 
   // the q's are precomputed, which doesn't cost too much time/memory.
   // TO DO: larger Cf for fldnum case
   Cf := 2.5;
   if fldnum and CanChangeUniverse(Coefficients(E), Rationals())
       and Degree(K) gt 2 and IsAbelian(K)
   then
       // hard case for finding q (due to splitting pattern)
       // TO DO: other such cases
       Cf := Degree(K);
   end if;
   C := r + 1;
   B := Ceiling( Cf * C*N * Log(C*N) );
   B := Min(B, 2^30 - 1);

   vprintf ECSaturation: "Precomputing table of auxiliary primes q up to %o: ", B;
   vtime ECSaturation:
   if fldrat then 
       pqDB, bad := pqDatabase(E, N, B);
   else
       pqDB, bad := pqDatabase_NF(E, N, B);
   end if;

   p := 1;
   while true do
       p := NextPrime(p);
       if p gt N then
           break;
       elif p in OmitPrimes then 
           continue;
       end if;

       vprintf ECSaturation, 2: "Saturating at p = %o\n",p;
	
       // Determine the subgroup of G consisting of those elements
       // whose image in E(F_q) is p-divisible for suitable primes q
       //   (primes such that p divides #E(F_q) exactly once). 
       Fp := GF(p);
       Gmodp := RSpace(Fp, tr); // abstract copy of G/p*G as a Z/p module
       tors := sub< Gmodp | [Gmodp.i : i in [1..t]] >;
       ker := Gmodp;
       // ker always contains the p-divisible subgroup (mod p);
       // ker gets cut down until hopefully we have equality

       special := p eq 2 and IsSquare(Discriminant(E)) or
                  CM and p gt 2 and LegendreSymbol(CMd, p) ne 1;

       // GENERAL CASE

       if not special then
            ii := 0;
	    q0 := B;
	    for i := 1 to r + 30 do 
		if ker subset tors then 
                    break; 
                end if;
		q, m, Eq, res, ii, q0 := findq(E, p, bad, pqDB, ii, q0, fldrat);

                // TO DO
                if q cmpeq 0 then
                    vprint ECSaturation: "Failed to find q for main case";
                    break;
                end if;

		// vprintf ECSaturation, 3: "q = %o\n", Norm(q);
		// Apply the map
		//       phi: pdivG -> E(F_q) -> E(F_q)[p]
		// to the generators of pdivG
		// (where the first map is reduction mod q,
		// and the second map is multiplication by m)
                if fldrat then
                    images := [m * (Eq!P) : P in points];
                else
                    images := [m * reduce(P, q, res, Eq) : P in points];
                end if;
                I := [i : i in [1..tr] | not IsZero(images[i])];
		if #I eq 0 then 
                    continue; 
                end if;
                i1 := I[1];
                L := Matrix(Fp, tr, 1, []);
                L[i1,1] := 1;
                if #I gt 1 then
                    im1 := images[i1];
                    for i in I[2..#I] do
                        L[i,1] := Log(im1, images[i]);
                    end for;
                end if;
		ker meet:= Kernel(L);
	        // vprintf ECSaturation, 3: "current kernel is %o\n", ker;
	    end for;
	end if;

	// STEP 4: SPECIAL CASE

	if (p le 163 or fldnum) and not ker subset tors then
	    vprintf ECSaturation, 2:
	          "Special case: Now trying primes q such that #E(Fq)[%o] = %o^2\n", p, p;

            ii := 0;
	    q0 := B;
	    for i := 1 to r + 10 do
		if ker subset tors then 
                    break;
                end if;
                q, Eq, res, ii, q0 := findqSpecialCase(E, p, bad, pqDB, ii, q0, fldrat);
		vprintf ECSaturation, 3: "q = %o\n",q;

		// Find a basis [T1,T2] of Eq[p]
                // (we already got the abelian group, so use it)
                A, mA := AbelianGroup(Eq);
                assert Ngens(A) eq 2;
                T1 := ((Order(A.1) div p) * A.1) @ mA;
                T2 := ((Order(A.2) div p) * A.2) @ mA;

		// For T = T1 or T2, consider the map
		//   phi : E(Q)/p*E(Q) -> E(F_q)/p*E(F_q) -> E(F_q)[p] -> mu_p -> Z/p
		//
		//                 P  :->   . . . .      :->        Tate_p(T, P)
                //
                if fldrat then
                    rpoints := ChangeUniverse(points, Eq);
                else
                    rpoints := [reduce(P, q, res, Eq) : P in points];
                end if;
                L := Matrix(2, [Fp | Log(TatePairing(T, P, p)) : T in [T1,T2], P in rpoints]);
		ker meet:= Kernel(L);
		vprintf ECSaturation, 3 : "current kernel is %o\n", ker;
	    end for;
	end if;

	// STEP 5: Naive division by p in E(Q).

	if not ker subset tors then

            vprintf ECSaturation: "Looks like G is divisible by %o\n", p;

            new := 0;
            points0 := points;

            BM := ReverseColumns(EchelonForm(ReverseColumns(BasisMatrix(ker))));
            basis := [v : v in Rows(BM) | v notin tors];

            for v in basis do
                P := &+ [ (Integers()!v[i]) * points[i] : i in [1..#points]];
                bool, newpt := IsDivisibleBy(P, p);
                if bool then 
                    vprintf ECSaturation: "Found new point: %o\n", newpt;
                    new +:= 1;
                    // insert newpt at pivot
                    i := Max([i : i in [1..tr] | not IsZero(v[i])]);
                    assert v[i] eq 1;
                    points[i] := newpt;
                else
                    vprintf ECSaturation: "False positive in saturation at %o : %o\n", p, v;
                end if;
            end for;

            if #basis - new gt 1 then
                vprintf ECSaturation: "Rare case!!! %o %o\n", #basis, new;
                // need to check all vectors rather than only pivots
                points := points0;
                newpoints := [];
                vecs := [v : v in ker | v notin tors];
                for v in vecs do
                    P := &+ [ (Integers()!v[i]) * points[i] : i in [1..#points]];
                    bool, newpt := IsDivisibleBy(P, p);
                    if bool then 
                        vprintf ECSaturation: "Found new point: %o\n", newpt;
                        Append(~newpoints, newpt);
                    end if;
                end for;
                if #newpoints gt 0 then
                    assert #points eq tr;
                    points := points[1..t] cat
                              IndependentGenerators(points[t+1..tr] cat newpoints
                                                   : Start:=tr-t+1);
                    assert #points eq tr;
                end if;
                new := #newpoints;
            end if;

            if new gt 0 then
                // points were modified; continue saturation testing at p
                p -:= 1; 
            end if;
        end if;   // end of Step 5.

        assert #points eq tr;

   end while; 
  	
   if TorsionFree then
       return [E(K) | P : P in points | Order(P) eq 0];
   else
       return points;
   end if;

end intrinsic;


intrinsic Saturation(points::SeqEnum[PtEll] :
                     TorsionFree := false,
                     Check       := true,
                     HeightBound := Infinity())
       -> SeqEnum[PtEll], BoolElt
{Given a sequence of points on an elliptic curve over Q or a number field,
returns a sequence of generators for the subgroup of the Mordell-Weil group
consisting of all points P such that m*P for some integer m > 0 lies in the
group generated by the given points.}
   
   if IsEmpty(points) then
      return points, true;
   end if;

   E := Curve(Universe(points));
   K := BaseRing(E);
   fldrat := Type(K) eq FldRat;
   fldnum := ISA(Type(K), FldNum);
   deg := AbsoluteDegree(K);

   require fldrat or fldnum:
      "The base ring must be Q or a number field";

   require fldrat or IsAbsoluteField(K):
      "Not implemented for relative extensions";

   if Check then
      points := IndependentGenerators(points);
   end if;

   n := #points;
   R := Regulator(points);
   h := HermiteConstant(n); // min height <= (h*R)^(1/n)

   _, HD := CPSHeightBounds(E); // h(pt) <= h^(pt) + HD

   if HD*deg gt 10 then
      vprintf ECSaturation :
         "Height difference bound = %o\n", RealField(3)! HD;
   end if;

   proven := HD le HeightBound;
   if not proven then
      vprintf ECSaturation :
         "User height bound = %o\n", RealField(3)! HeightBound;
      HD := HeightBound;
   end if;

   // Optimization
   // 1 prime is worth 1000 x-values

   function cost(N)
      H := (R/N^2/h) ^ (1/n) + HD;
      return Exp(3/2*deg*H) + 1000*N;
   end function;

   N := 1;
   C := cost(N); 
   while true do
      N1 := Max(NextPrime(N + 5) - 1, Ceiling(1.1*N));
      C1 := cost(N1);
      if C1 ge C then
         break;
      end if;
      N := N1;
      C := C1;
   end while;
   N := Min(N, 2^20);

   vprintf ECSaturation :
      "Saturation bound = %o\nSearch bound = %o\n",
         N, Ceiling(Exp( (R/N^2/h) ^ (1/n) + HD ));
   
   if N gt 1 then
      points0 := points;
      vprintf ECSaturation : "Saturation time : ";
      vtime ECSaturation :
      points := Saturation(points, N : Check:=false, TorsionFree);
 
      if points ne points0 then
         R := Regulator(points);
      end if;
   end if;

   H := (R/N^2/h) ^ (1/n) + HD;
   X := Ceiling(Exp(H));

error if X ge 2^30, "Search bound is too large";

   vprintf ECSaturation : "Search time : ";
   vtime ECSaturation :
   small := Points(E : Bound := X);

   if not IsEmpty(small) then
      points := IndependentGenerators(points cat Setseq(small)
                                     : Start := #points + 1);
   end if;

   if TorsionFree then
      return points, proven;
   else
      T, mT := TorsionSubgroup(E);
      tors := [T.i @ mT : i in [1..Ngens(T)]];
      return tors cat points, proven;
   end if;

end intrinsic;

