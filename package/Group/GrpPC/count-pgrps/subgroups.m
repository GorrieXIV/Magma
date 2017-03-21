freeze;
/* count number of subgroups of abelian p-group */

/* is each element of alpha at least as large as corresponding
   element of beta? */

CompareSequences := function (alpha, beta)

  return forall {i : i in [1..Minimum (#alpha, #beta)] | alpha[i] ge beta[i]};

end function;

/* order of GL (n, p) */

intrinsic OrderGL (n::RngIntElt, p::RngIntElt) -> RngIntElt 
{Return order of GL (n, p)}
   if n eq 0 then return 1; end if;
   factor := p^n;
   return &*[(factor - p^i): i in [0..n - 1]];
end intrinsic;

intrinsic FactoredOrderGL (n::RngIntElt, p::RngIntElt) -> RngIntElt 
{Return order of GL (n, p)}
   if n eq 0 then return 1; end if;
   pf := Factorization(p);
   res := pf^Binomial(n,2);
   pp := 1;
   for i := 1 to n do
      pp := pp * p;
      res := res * Factorization(pp - 1);
   end for;
   return res;
end intrinsic;

DecreasingSequence := function (a)

   return [&+[a[j] : j in [i..#a]]: i in [1..#a]];

end function;

PrimeSequence := function (alpha)

  return [alpha[i] : i in [2..#alpha]];

end function;

PlusSequence := function (alpha, beta)
  
  beta[1] := alpha[1];
  return beta;

end function;

/* order of automorphism group of an abelian group */

OrderAbelianGroup := function (p, beta)

   three := 1; order := 1;
   for i in [1..#beta - 1] do
      one := beta[i] - beta[i + 1];
      two := [beta[j] : j in [1..i - 1]]; 
      Append (~two, beta[i + 1]);
      three *:= p^(one * &+two); 
      order *:= OrderGL (one, p);
   end for;

   return three * order;

end function;

intrinsic OrderAutomorphismGroupAbelianPGroup (a::SeqEnum) -> RngIntElt
{Order of automorphism group of abelian p-group G where 
 a = [a[1], a[2], a[3], ...] and G = C_a[1] x C_a[2] x C_a[3] ... } 

    require #a gt 0 and Universe(a) eq Integers() and Min(a) gt 1 :
					"Sequence must contain integers > 1";

   r := Rep (a);
   flag, p := IsPrimePower (r);
   error if flag eq false, 
      "Runtime Error: abelian invariants must be prime-powers";

   A := [];
   for i in [1..#a] do
      flag, A[i] := IsPowerOf(a[i], p);
      error if flag eq false, 
	    "Runtime Error: abelian invariants must be power of same prime";
   end for;

   /* construct sequence which lists number of C_(p^s) which occur */
   S := Set (A);
   m := Maximum (S);
   a := [0: i in [1..m]];
   for s in S do
      a[s] := #[x : x in A | x eq s];
   end for;
 
   alpha := DecreasingSequence (a) cat [0];
   return OrderAbelianGroup (p, alpha);

end intrinsic;

/* number of k-dimensional spaces in an
   n-dimensional space defined over GF (p) */

NmrSpaces := function (p, n, k)

   if k eq 0 then return 1; end if;
   pn := p^n; pk := p^k;
   powers := [p^i : i in [0..k - 1]];
   x := &*[(pn - powers[i]): i in [1..k]];
   y := &*[(pk - powers[i]): i in [1..k]];
   return x div y;
 
end function;

Nsubs := function (p, Lambda, V)

   Append (~V, 0);
   return &*[p^(V[i + 1] * (Lambda[i] - V[i])) * 
     NmrSpaces (p, Lambda[i] - V[i + 1], V[i] - V[i + 1]) : i in [1..#V - 1]];

end function;

intrinsic NumberOfSubgroupsAbelianPGroup (a::SeqEnum) -> SeqEnum
{Return the number of subgroups of each non-trivial order in 
 the abelian p-group G where a = [a[1], a[2], ...] and 
 G = C_a[1] x C_a[2] x ...}

    require #a gt 0 and Universe(a) eq Integers() and Min(a) gt 1 :
					"Sequence must contain integers > 1";

   r := Rep (a);
   flag, p := IsPrimePower (r);
   error if flag eq false, 
      "Runtime Error: abelian invariants must be prime-powers";

   A := [];
   for i in [1..#a] do
      flag, A[i] := IsPowerOf(a[i], p);
      error if flag eq false,
	    "Runtime Error: abelian invariants must be power of same prime";
   end for;

   a := A;
   Sort (~a);
   Reverse (~a);
      
   r := {x : x in [1..Maximum (a)]};
   Lambda := DualPartition (a);
   N := &+a;
   Count := [];
   N2 := N div 2;
   for n in [1..N2] do
      X := RestrictedPartitions (n, r);
      Count[n] := &+[Nsubs (p, Lambda, DualPartition (v)) : v in X];
      Count[N - n] := Count[n];
   end for;
   Append (~Count, 1);

   return Count;

end intrinsic;
