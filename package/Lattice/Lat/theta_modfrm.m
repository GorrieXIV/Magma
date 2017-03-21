freeze;

////////////////////////////////////////////////////////////////////////////////
// ThetaSeriesModularForm
// Steve Donnelly, 2009
// (Last modified November 2011)
////////////////////////////////////////////////////////////////////////////////

declare attributes Lat: modular_form_space, // = ThetaSeriesModularFormSpace(L) 
                        modular_form;       // = ThetaSeriesModularForm(L)

intrinsic ThetaSeriesModularFormSpace(L::Lat) -> ModFrm
{The space of modular forms, or half-integral weight forms, 
 which contains the theta series of the lattice L}
   
    bool, mfs := HasAttribute(L, "modular_form_space");
    if bool then
       return mfs;
    end if;

    require IsIntegral(L): "The given lattice L should be integral";

    // Odd lattices are rescaled by sqrt(2) to obtain an even lattice
    if not IsEven(L) then
       L2 := LatticeWithGram(2*GramMatrix(L));
       L`modular_form_space := ThetaSeriesModularFormSpace(L2);
       return L`modular_form_space; 
    end if;
  
    d := Dimension(L);
    D := Determinant(L);

    /* [this was for the use_integral option in ThetaSeriesModularForm]
    if use_integral and d gt 1 then
        // Augment by a 1-dim lattice
        A := (-1)^((d+1) div 2) * 2 * SquarefreeFactorization(2*D);
        sqrtAZ := LatticeWithGram(Matrix(1,1,[A]));
        LZ := DirectSum(L, sqrtAZ);
        MLZ := ThetaSeriesModularFormSpace(LZ);
        assert IsTrivial(DirichletCharacters(MLZ)[1]); 
        return MLZ;
    end if;
    */

    N := Exponent(DualQuotient(L));
    Lstar := RescaledDual(L);  // TO DO: make sure scaling factor is the right one
    level := IsEven(Lstar) select N else 2*N;
    wt := Dimension(L)/2;
    if IsIntegral(wt) then 
       wt := Integers()! wt;
       chi := KroneckerCharacter( (-1)^wt * D );
       M := ModularForms( DirichletGroup(level)! chi, wt);
    else
       chi := DirichletGroup(LCM(level,4))! KroneckerCharacter(2*D); 
       M := HalfIntegralWeightForms(chi, wt);
    end if;
    L`modular_form_space := M;
    return M;
end intrinsic;

function q_qprime_split(n, q)
   q := &*[Integers()| ff[1]^ff[2] : ff in Factorization(n) | q mod ff[1] eq 0];
   qq := n div q;
   assert q*qq eq n and GCD(q,qq) eq 1;
   return q, qq;
end function;

// time estimate for ThetaSeries(L, n : ExponentConstant:=1/2)
function theta_time(L, n)
   norm := 2.0*(n-1);
   search_size := EnumerationCost(L, norm);
   return search_size/(10^7);
end function;

// Return integers [n_1,..,n_k] indicating how many coefficients 
// of each of the k duals should be computed in order to get n
// coefficients in total, as quickly as possible.
// The option 'ns0' specifies how many coeffs we have for free.

// By definition theta = Sum of q^(1/2*|v|^2)

function best_strategy(duals, n, ns0)
   if #duals eq 1 then return [n], [theta_time(duals[1][2],n)]; end if;

   ns := [n : dual in duals];  assert #ns0 eq #ns;
   times := [theta_time(tup[2], n) : tup in duals];
   dim := Dimension(duals[1][2]); // = dimension of all of the lattices

   // quick guess, assuming time ~ const*n^(dim/2)
   consts := [t/n^(dim/2) : t in times]; 
   while &+ns gt n do 
     // reduce the most expensive by 1
     _,i := Max(times);
     if ns[i] le ns0[i] then
       times[i] := 0; continue; end if; // we get this for free
     ns[i] -:= 1;  times[i] := consts[i]*ns[i]^(dim/2);
   end while;
   // We now have (and will have from now on): &+ns = n and ns >>= ns0

//"Quick guess: number of coeffs =", ns;
   // Now adjust using Damien's time estimate
   times := [(ns[i] le ns0[i]) select 0 else theta_time(duals[i][2], ns[i]) : i in [1..#ns]];
   ns1 := ns;  times1 := times;
   while true do  assert &and[ ns[i] ge ns0[i] : i in [1..#ns]];
     maxtime,h := Max(times);  
     inctime,l := Min([theta_time(duals[i][2], ns[i]+1) : i in [1..#ns]]);
     if inctime lt maxtime then
       ns1[h] -:= 1;  ns1[l] +:= 1;  
       times1[l] := inctime;
       if ns1[h] le ns0[h] then
         times1[h] := 0;  // we get this for free
       else
         times1[h] := theta_time(duals[h][2], ns1[h]);
       end if;
       ns := ns1;  times := times1;  
     else
//"Best guess: number of coeffs =", ns; 
       return ns, times;
     end if;
   end while;
end function;

procedure check_W(W, errormessage)
   V := Generic(W);
   n := Dimension(V) - 1;
   ok := Dimension(W) le n;
   projn := sub< V | [Eltseq(w)[1..n] cat [0] : w in Basis(W)] >;  // projection to the first n coords
   ok and:= Dimension(W) eq Dimension(projn);
   error if not ok, errormessage;
end procedure;

// return seq containing divisors q of N for which the partial dual L_q
// is isometric to L (from among only the 'candidates', if specified).
function test_for_modularities(L,N : known_modularities:={}, candidates:=0)
   d := Dimension(L);
   D := Determinant(L);
   if candidates cmpeq 0 then
      prime_powers := { tup[1]^tup[2] : tup in Factorization(N) | 2*Valuation(D,tup[1]) eq d };
      candidates := { &* set : set in Subsets(prime_powers) | not IsEmpty(set) };
   elif Type(candidates) eq SetEnum then 
      primes := {};
      for c in candidates do
         for tup in Factorization(c) do 
            if 2*Valuation(D,tup[1]) ne d then Exclude( ~candidates, c); break;
            else primes join:= {tup[1]}; end if;
         end for;
      end for;
      prime_powers := { p^Valuation(N,p) : p in primes };
      candidates := { c : c in candidates | c ne 1 and &and[GCD(c,pp) eq 1 or c mod pp eq 0 : pp in prime_powers] };
   end if;
   assert &and[ GCD(q,pp) eq 1 or q mod pp eq 0 : pp in prime_powers, q in known_modularities ]; 
   modularity_group := { a1*a2 div GCD(a1,a2)^2 : a1, a2 in known_modularities join {1} };
   for q in candidates do
      if q in modularity_group then continue; end if;
      Lq := RescaledDual(L,q); // TO DO: is the rescaling the right one?
      assert IsIntegral(Lq);
    //assert Determinant(Lq) eq D;  // by conditions pre-imposed on q
      if Determinant(Lq) ne D then continue; end if; // TO DO: redundant if IsIsometric checks this first 
      vprintf Theta,1: "Testing %o-modularity ... ", q;
      vtime Theta,1:
      if IsIsometric(L, Lq) then 
         modularity_group join:= { a*q div GCD(a,q)^2 : a in modularity_group };
      end if;
   end for;
   return { q : q in modularity_group | q in candidates and q ne 1 };
end function;

////////////////////////////////////////////////////////////////
// Main routine
////////////////////////////////////////////////////////////////

forward InternalThetaSeriesModularForm;
      
intrinsic ThetaSeriesModularForm(L::Lat : KnownTheta:=0,
                                          KnownDualThetas:=[],
                                          KnownModularities:={},
                                          ComputeModularities:=0)
       -> ModFrmElt

{Returns the theta series of the integral lattice L as a modular form
in the appropriate space (given by ThetaSeriesModularFormSpace).
The theta series is normalized as follows (so that its level as a 
modular form is the most natural level): for even lattices, theta 
is the sum of e^(pi*i*Norm(v)) and for odd lattices it is the sum 
of e^(2*pi*i*Norm(v)).

If some coefficients of the theta series of L or any of its partial duals
are already known, this information may be passed in using the optional
arguments KnownTheta (a power series) or KnownDualThetas (a sequence of
power series).  If it is known that L has modularities, these may be
specified as KnownModularities (as set of integers).  In addition,
ComputeModularities (a boolean, or a set of integers) may be specified,
to control whether the function should determine the modularities of L.}

   bool, f := HasAttribute(L, "modular_form");
   if bool then
      return f;
   end if;

   require IsIntegral(L) : "The given lattice L must be integral";

   require ComputeModularities cmpeq 0 or
           ISA(Type(ComputeModularities), BoolElt) or
           ISA(Type(ComputeModularities), SetEnum) :
      "Optional argument 'ComputeModularities' should be a boolean or a set of integers";
   
   require ISA(Type(KnownModularities), SetEnum) :
      "Optional argument 'KnownModularities' should be a set of integers";

   require KnownTheta cmpeq 0 or 
           ISA(Type(KnownTheta), RngSerPowElt) and IsFinite(AbsolutePrecision(KnownTheta)): 
      "Optional argument 'KnownTheta' should be a power series with finite precision";

   require ISA(Type(KnownDualThetas), SeqEnum) and
           forall{x : x in KnownDualThetas | ISA(Type(x), Tup) and 
                                             ISA(Type(x[1]), RngIntElt) and 
                                             ISA(Type(x[2]), RngSerPowElt) and 
                                             IsFinite(AbsolutePrecision(x[2])) } :
      "Optional argument 'KnownDualThetas' should be a sequence of tuples <m, f_m>, "*
      "where f_m is a power series with finite precision";

   if KnownTheta cmpne 0 and not exists{x : x in KnownDualThetas | x[1] eq 1} then
      KnownDualThetas := [<1,KnownTheta>] cat KnownDualThetas;
   end if;

   q := PowerSeriesRing(Integers()).1;

   // Use stored theta info (TO DO: for duals too)
   if assigned L`ThetaSeries and
      (not exists(t){x[2] : x in KnownDualThetas | x[1] eq 1} 
       or AbsolutePrecision(t) lt AbsolutePrecision(L`ThetaSeries))
   then
      KnownDualThetas := [<1, L`ThetaSeries>] cat [x : x in KnownDualThetas | x[1] ne 1];
   end if;

   // Even lattices need theta normalised (1/2 the exponent)
   if IsEven(L) and exists(t){x[2] : x in KnownDualThetas | x[1] eq 1} then
      // don't use Evaluate(t,Parent(t).1^2), it puts the wrong precision
      // (and this keeps getting re-broken every time it is fixed)
      p := AbsolutePrecision(t);
      p2 := Ceiling(p/2);
      require forall{i : i in [1..p-1] | IsEven(i) or Coefficient(t,i) eq 0}:
         "Wrong value of optional argument: Theta series of even lattice should be even";
      t2 := &+ [Coefficient(t,2*i)*q^i : i in [0..p2-1]] + O(q^p2);
      KnownDualThetas := [<1,t2>] cat [x : x in KnownDualThetas | x[1] ne 1];
   end if;
   // TO DO: what is supposed to be the normalisation of the 'known duals'? 

   // Odd lattices are rescaled by sqrt(2) to obtain an even lattice
   if IsOdd(L) then
      L2 := LatticeWithGram(2*GramMatrix(L));
      if IsOdd(Determinant(L)) then 
         KnownModularities join:= {4}; 
      end if;

      // Caching: space must contain form
      L`modular_form_space := ThetaSeriesModularFormSpace(L2);
      L`modular_form := InternalThetaSeriesModularForm(L2 : 
                        modularities := KnownModularities,
                        compute_modularities := ComputeModularities,
                        known_thetas := KnownDualThetas);
   else
      L`modular_form := InternalThetaSeriesModularForm(L :
                        modularities := KnownModularities,
                        compute_modularities := ComputeModularities,
                        known_thetas := KnownDualThetas);
   end if;
   return L`modular_form; 
end intrinsic;


/* Options currently for internal use:
 'known_thetas' is a sequence of tuples <q,theta> where theta is a power series representing 
                the theta function of the partial dual L_q (with exponent constant 1/2)
 'modularities' is a set of integers, the lattice is assumed to have these modularities 
 'omit_duals' is a set of integers q
 'num_coeffs' tells us to use more coeffs in total than we naively expect to need
 'safety' is the number of extra coefficients computed as a check
 If 'use_integral' is true, then for odd dimensions it will augment by a 1-dimensional
     lattice (currently in this case it returns a power series instead of a ModFrmElt) 
*/

function InternalThetaSeriesModularForm(L : known_thetas:=[],
                                            modularities:={},
                                            compute_modularities:=0,
                                            omit_duals:={},
                                            num_coeffs:=[],
                                            safety:=0)
   assert IsEven(L);
   d := Dimension(L);
   D := Determinant(L);

   // Parse varargs + set defaults
   if compute_modularities cmpeq 0 then
      compute_modularities := d le 20; 
   end if;

   /* TO DO: use this approach?
   if use_integral and d gt 1 then
      // Augment by a 1-dim lattice
      A := 2 * SquarefreeFactorization(2*D);
      sqrtAZ := LatticeWithGram(Matrix(1,1,[A]));
      vprint Theta,1: "Augmenting by the %o-dimensional lattice \n%o\n", 
                                Dimension(sqrtAZ), GramMatrix(sqrtAZ);
      LZ := DirectSum(L, sqrtAZ);
      MLZ := ThetaSeriesModularFormSpace(LZ);
      assert d mod 4 eq 1 or IsTrivial(DirichletCharacters(MLZ)[1]); 
      thetaLZ := ThetaSeriesModularForm(LZ);
      prec := Max(prec, PrecisionBound(MLZ) );
      theta1 := ThetaSeries(sqrtAZ, prec : ExponentConstant:=1/2);
      return PowerSeries(thetaLZ, prec)/theta1;
   end if;
   */
  
   M := ThetaSeriesModularFormSpace(L);
   N := Level(M);
   k := Weight(M);
   vprint Theta,1: "Theta lives in", M;

   if not IsIntegral(k) then 
      vprint Theta,1: "Half-integral weight case ... can't use duals or modularities.";
      //return M! ThetaSeries(L, PrecisionBound(M:Exact) : ExponentConstant:=1/2);
   end if;

   // Impose linear constraints, obtaining a coset inside M in which theta must live.
   // There are various ways to get them, and we'll maintain enough flexibility 
   // to be able to apply the various approaches in any order (dynamically).
   // So, each approach will be a separate function returning a coset of M 
   // (or possibly, if a coset is passed in, returning a sub-coset).
   // A 'coset' will be described in terms of linear relations; it will be 
   // represented by a subspace W of the (n+1)-dimensional vector space
   //   V := VectorSpace(M) + Q 
   // where W encodes the following coset, writing Basis(M) = [b_1,...,b_n]
   //   { Sum_i c_i*b_i : Sum_{1<=i<=n} c_i*w_i = w_{n+1} for all vectors w in W }.
   // Note that W must always have the property that 
   //   Dimension(W) = Dimension(W meet Vn)  where  Vn := Span(V.1,..,V.n)

   Q := Rationals();
   n := Dimension(M);
   V := VectorSpace(Q, n+1);
   W := sub< V | >;  // initially the 'coset' is the whole of M
   W := sub< V | W, V! ([1] cat [0 : i in [1..n-1]] cat [1]) >; 
                     // constant coeff is 1, Basis(M) is echelonized

   // Data structure for listing the partial duals: 
   //   <q, L_q, Wq, Theta_(L_q)>  where Wq is as computed below.
   qq := PowerSeriesRing(Q).1;
   theta_known := exists(tup){tup: tup in known_thetas | tup[1] eq 1};
   theta := theta_known select tup[2] else 1+O(qq);
   duals := [* <1, L, IdentityMatrix(Q,n), theta> *];

   // ***** Work out the values at cusps ***** 
   // TO DO ...
   
   // ***** Get Atkin-Lehner matrices. ***** 

   // Theoretical note: 
   // (For q=N, this is Miyake's Corollary 4.9.5, item 3, and in general it is a slight
   // rearrangement of (2.3) from Quebbemann's paper 'Atkin-Lehner eigenforms...').
   // Suppose k is even, and let q be a divisor of N = Level(M). 
   // Write D = det(L) = D_q * D_q_prime with (Dq, Dq_prime) = 1.  For example, D_N = D. 
   // Suppose D_q is a square.  Then the theta series of the partial dual L_q equals 
   //      (-1)^s Sqrt(Dq/q^k) w_q(Theta_L)
   // where s = k/2 when q=N. For general q, Quebbemann's identity (2.3) says the sign 
   // (-1)^s is (-i)^k times the Gauss sum associated to the q'-dual quotient of the 
   // partial dual L_q'. We then apply the lemma in Rains-Sloane ('Shadow theory...') 
   // that gives a Gauss sum in terms of local invariants of the lattice.

   // Compute the matrix Wq acting on M (acting on the basis b_i from the left), such that 
   // if Theta_L = Sum_i c_i*b_i then Theta_(L_q) = Sum_i g_i*b_i where (g_i) = (c_i)*Wq.
   prime_powers_in_N := { tup[1]^tup[2] : tup in Factorization(N) };
   qs := IsIntegral(k)
          select [ &*subs : subs in Subsets(prime_powers_in_N) | not IsEmpty(subs) ]
           else  [ ];
   vprint Theta,1: "Computing q-expansion basis of modular forms and Atkin-Lehner operators ... ";
   time0_MF := Cputime();
   for q in qs do
      if q in omit_duals then 
         continue; 
      elif q ne N and not IsSquare(D) then 
         continue; 
      end if;
      Dq := q_qprime_split(D, q);
      bool,cc := IsSquare( Dq/q^k ); 
      if IsOdd(k) or k eq 2 or not bool then 
         continue; 
      end if;
      // We're in the case where k is even (so q^k is square), and D, Dq, Dq_prime are all square.
      // Now calculate the sign (-1)^s (see the theoretical note above).
      Lqq := RescaledDual(L, N div q);
    //GaussSumCheck(Lqq);
      gauss := GaussSum(Lqq, N div q);  assert Abs(Im(gauss)) le 10-10;
      gauss := Round(Real(gauss)); 
      Wq := gauss * (-1)^(-k div 2) * cc * AtkinLehnerOperator(M, q);
      thetaq_known := exists(tup){tup: tup in known_thetas | tup[1] eq q};
      thetaq := thetaq_known select tup[2] else 1+O(qq);
      duals cat:= [* <q, RescaledDual(L,q), Wq, thetaq> *];
   end for;
   if #duals gt 1 then 
      vprintf Theta,1: " ... done computing modular forms, %o sec\n", Cputime(time0_MF); 
   end if;

   //  ***** Use modularities. *****
   // The resulting coset will be an intersection of Atkin-Lehner eigenspaces.

   // remove anything that doesn't make sense or that we can't use, from what the user passed in 
   modularities := {q : q in modularities | q ne 1 and N mod q eq 0 and GCD(q, N div q) eq 1
                                            and q in {tup[1] : tup in duals}}; 
   if compute_modularities cmpeq true then
      compute_modularities := {tup[1] : tup in duals};
   elif compute_modularities cmpeq false then
      compute_modularities := {Integers()|};
   else
      compute_modularities meet:= {tup[1] : tup in duals};
   end if;
   if #compute_modularities gt 1 then 
      modularities := test_for_modularities(L,N : known_modularities := modularities, 
                                                  candidates := compute_modularities);
   end if;
   // list out full group of modularities, and choose generators
   modularities_gens := {};
   modularities_group := {1};
   while exists(q){q: q in modularities | q notin modularities_group} do
      modularities_gens join:= {q};
      modularities_group join:= {q*qq div GCD(q,qq)^2 : qq in modularities_group};
   end while;
   modularities := modularities_group diff {1}; 
   assert #modularities eq 2^#modularities_gens - 1;

   if not IsEmpty(modularities) then 
      vprint Theta,1: "Using modularities ", modularities; end if;
   for q in modularities_gens do 
      Dq := q_qprime_split(D, q);  assert Dq eq q^k;
      // rels cutting out this Atkin-Lehner eigenspace
      _ := exists(Wq){tup[3] : tup in duals | tup[1] eq q};
      T := Wq - IdentityMatrix(Q,n);  // recall Wq = 1/eigval * w_q
      // Recall that Wq acts on the vector of coeffs (c_i) from the right, 
      // so the relations on (c_i) are given by the columns of T.
      columns_of_T := [ Transpose(T)[i] : i in [1..Ncols(T)] ];
      rels := [V| Eltseq(col) cat [0] : col in columns_of_T ];
      W := sub< V | W, rels >;
      check_W(W, "Something went wrong while trying to use modularities"); 
   end for;

   // Get rid of duals which are now redundant (after using modularities).
   if not IsEmpty(modularities) then 
      old_duals := duals;
      duals := [* *];
      while #old_duals gt 0 do
         q := old_duals[1][1];
         qs := {q} join { q*m div GCD(q,m)^2 : m in modularities}; 
         equiv_duals_indices := [ i : i in [1..#old_duals] | old_duals[i][1] in qs ];
         _,i := Min([ old_duals[i][1] : i in equiv_duals_indices ]);
         Append( ~duals, old_duals[i]);
         for i in Reverse(equiv_duals_indices) do Remove(~old_duals, i); end for;
      end while;
   end if;

   // ***** Determine enough coefficients (ask for several extra, as a safety check). ***** 
   // Using the EnumerationCost estimate, we know how many to ask for from each dual.
   // First ask for total number = dimension of space in which theta lives + safety margin.
   // If those don't determine theta uniquely, but determine theta modulo a space of dim k, 
   // then increase the total number by k. 
   if #duals gt 1 then 
      vprint Theta,1: "Can use partial duals", [tup[1] : tup in duals];
   elif exists(dummy_q){q : q in qs | q ne 1 and q notin modularities} then
      vprint Theta,1: "Can't use duals, unfortunately"; end if;

   // First get rels from known thetas 
   prec := Max([ AbsolutePrecision(duals[i][4]) : i in [1..#duals] ]);
   _ := qExpansionBasis(M, Dimension(M)+safety+2 ); // hopefully enough, so we dont have to get more later
   q_exp_coeffs_matrix := Matrix([[Q| Coefficient(bi,j) : j in [0..prec-1]] : bi in Basis(M)]); 
                       // rows are q-expansion coeffs of basis elts of M
   if #duals eq 1 then 
      vprint Theta,1: "  ... done computing modular forms,", Cputime(time0_MF); 
   end if;

   for i := 1 to #duals do 
      Wq := duals[i][3];
      theta := duals[i][4];
      // we have (c_i) * Wq * column_j == coeff_j of theta
      rels := [V| ];
      for j := 1 to AbsolutePrecision(theta) - 1 do 
         rel := Transpose(q_exp_coeffs_matrix)[j+1] * Transpose(Wq);
         Append( ~rels, Eltseq(rel) cat [Coefficient(theta,j)] );
      end for;
      W := sub< V | W, rels >;
      check_W(W, "\nAn inconsistency arose while applying conditions obtained from the 'known thetas'."
                *"\n(Incorrect values given for optional arguments?)");
   end for;

   hkz_done := [false : tup in duals];
   while Dimension(W) lt n or safety gt 0 do
      ns0  := [AbsolutePrecision(tup[4]) : tup in duals];
      total_num_coeffs_known := &+ ns0; // counting the constant coeffs (which = 1)
      num_extra_coeffs_needed := (n-Dimension(W)) + safety;
      total_coeffs := total_num_coeffs_known + num_extra_coeffs_needed;
      vprintf Theta,1: "Asking for %o coefficients in total\n", total_coeffs;
      // only add safety margin once
      if safety gt 0 then 
        vprintf Theta,1: " (plus %o extra as a safety check)\n", safety;
        safety := 0;
      end if;  
      ns, times := best_strategy(duals, total_coeffs, ns0);

      use_given_num_coeffs := #num_coeffs eq #duals and &+num_coeffs ge total_coeffs;
      if use_given_num_coeffs then ns := num_coeffs; end if;

      // Do HKZ on the duals where we think we want more coeffs
      if d le 20 then
         for i := 1 to #duals do
           if ns[i] gt ns0[i] and not hkz_done[i] then
             vprintf Theta,1: "HKZ reducing L_%o ... ", duals[i][1]; 
             vtime Theta,1:
             duals[i][2] := LatticeWithGram(HKZGram(GramMatrix(duals[i][2]))); 
             hkz_done[i] := true; 
           end if; 
         end for; 
         ns, times := best_strategy(duals, total_coeffs, ns0); 
      end if;
      vprintf Theta: "Time estimates: %o\n", times;

      if use_given_num_coeffs then 
        ns := num_coeffs;
        print "Using user-specified strategy: number of coeffs =", ns, "\nTime estimates:", 
              [ns[i] le ns0[i] select 0 else theta_time(duals[i][2], ns[i]) : i in [1..#duals]]; 
      end if;

      _ := qExpansionBasis(M, Max(ns));
      q_exp_coeffs_matrix := Matrix([[Q| Coefficient(bi,j) : j in [0..Max(ns)-1]] : bi in Basis(M)]);
      for i := 1 to #duals do 
        if ns[i] gt AbsolutePrecision(duals[i][4]) then 
          // get more coeffs for this dual
          time0 := Cputime();
          theta := ThetaSeries(duals[i][2], 2*ns[i]-2); // largest term is q^(2*ns[i]-2)
          coeffs := [Coefficient(theta,k) : k in [0 .. AbsolutePrecision(theta)-1 by 2]];
          theta := PS! coeffs + O(PS.1^#coeffs) where PS is PowerSeriesRing(Integers());
          duals[i][4] := theta; 
          vprintf Theta,1: "Computed Theta(L_%o) up to O(q^%o) in %o sec \n", 
                            duals[i][1], AbsolutePrecision(theta), Cputime(time0); 
          vprintf Theta,2: "Theta(L_%o) = %o\n", duals[i][1], theta;
          Wq := duals[i][3];
          // we have (c_i) * Wq * column_j == coeff_j of theta
          rels := [V| ];
          for j := ns0[i] to ns[i]-1 do 
             rel := Transpose(q_exp_coeffs_matrix)[j+1] * Transpose(Wq);
             Append( ~rels, Eltseq(rel) cat [Coefficient(theta,j)] );
          end for;
          W := sub< V | W, rels >;
          check_W(W, "An inconsistency arose while applying conditions obtained " * 
                     "from theta coefficients of L_" * IntegerToString(duals[i][1]) );
        end if;
      end for;
   end while; // Dimension(W) lt n
   
   Wtranspose := Transpose(Matrix(Basis(W)));
   bool, soln := IsConsistent( RowSubmatrix(Wtranspose,1,n), Wtranspose[n+1] );
   error if not bool, "An inconsistency arose in the linear algebra, right at the end";
   L`modular_form := M! soln;
   return L`modular_form;

end function;

