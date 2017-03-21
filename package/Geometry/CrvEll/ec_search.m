freeze;

///////////////////////////////////////////////////////////////////////
// Finding elliptic curves with given conductors
//
// Steve Donnelly 
// Last modified December 2011
///////////////////////////////////////////////////////////////////////

declare verbose ECSearch, 3;

import "../Algaem/pointsearch.m" : NonInertPrimes;
import "../LSeries/Lseries.m"    : fullgammaseries, G0;
import "../LSeries/bsdnf.m"      : BSDEasyTerms;

///////////////////////////////////////////////////////////////////////
// Miscellaneous functions

function CasselsTatePairingMatrix(basis)
   M := MatrixRing(GF(2), #basis) ! 0;
   for i in [1..#basis], j in [1..i-1] do
      ct := CasselsTatePairing(basis[i], basis[j]);
      M[i,j] := ct;
      M[j,i] := ct;
   end for;
   return M;
end function;

function is_S_integral(x, S)
   vals := [Valuation(x,P) : P in S];
   X := x * Ring(Universe(S));
   for i := 1 to #S do 
      if vals[i] lt 0 then
         X *:= S[i] ^ -vals[i];
      end if;
   end for;
   return IsIntegral(X);
end function;

// Return all elliptic curves over a finite field F 
// (up to isomorphism)

function EllipticCurves(F)
   Es := [];
   if Characteristic(F) in {2,3} then
      for j in F do
         E := EllipticCurveWithjInvariant(j);
         Es cat:= Twists(E);
      end for;
      traces := [Trace(E) : E in Es];
   else
      q := #F;
      g := PrimitiveElement(F);
      // j = 0
      e := GCD(6, q-1);
      Es cat:= [EllipticCurve([0,g^i]) : i in [0..e-1]];
      // j = 1728
      e := GCD(4, q-1);
      Es cat:= [EllipticCurve([g^i,0]) : i in [0..e-1]];
      traces := [Trace(E) : E in Es];
      // other j
      for j in F do
         if j notin {F|0,1728} then
            C4 := 1/(1-1728/j);
            E := EllipticCurve([-27*C4, -54*C4]);
            Eg := EllipticCurve([-27*C4*g^2, -54*C4*g^3]);
            Es cat:= [E, Eg];
            // here we save by getting two traces together
            t := Trace(E);
            traces cat:= [t, -t];
         end if;
      end for;
   end if;
   return Es, traces;
end function;

///////////////////////////////////////////////////////////////////////
// Tools to compute weightings for the search on elliptic curve

function integer_bounds(lengths, bound)
   gmlength := (&*lengths) ^ (1/#lengths);
   return [Max(1, Round(bound*gmlength/l)) : l in lengths];
end function;

// Inverse cube roots of the conjugates of delta

function weights(delta, prec)
   return [Abs(x)^(-1/3) : x in Conjugates(delta : Precision:=prec)];
end function;

// Gram matrix of the weighted Minkowski inner product wrt basis B, 
// with weights W on the (real) infinite places 

function trace_form_matrix(B, W, prec)
   if IsTotallyReal(NumberField(Universe(B))) then
      R := RealField(prec);
      M := Matrix(R, [Conjugates(b : Precision:=prec) : b in B]);
      W := DiagonalMatrix(R, W);
      return M * W^2 * Transpose(M);
   else
      C := ComplexField(prec);
      M := Matrix(C, [Conjugates(b : Precision:=prec) : b in B]);
      W := DiagonalMatrix(C, W);
      Mbar := Matrix(Ncols(M), [Conjugate(m): m in Eltseq(M)]);
      T := M * W^2 * Transpose(Mbar);
//assert forall{x : x in Eltseq(T) | Abs(Im(x)) lt eps} where eps is 10^-50;
      return ChangeRing(T, RealField(prec));
   end if;
end function;

// Choose basis and integer bounds to use in the Sieve routine,
// if we want to search a box which is approximately square
// wrt the norm given by the trace_form_matrix

function basis_and_bounds(C, delta, wts, prec)
   //wts := weights(delta, prec);
   basis := ChangeUniverse(Basis(C), Order(C));
   n := #basis;
   T := trace_form_matrix(basis, wts, prec);
   T := (T + Transpose(T))/2; // ensure symmetric
   T1, tr := LLLGram(T);
   basis1 := [ &+[tr[i,j]*basis[j] : j in [1..n]] : i in [1..n]];
   /* check
   T11 := trace_form_matrix(basis1, wts);
   assert forall{c : c in Eltseq(T1 - T11) | Abs(c) le eps} where eps is 10^-20;
   assert ideal< Order(C) | basis1 > eq C;
   */
   lengths := [Sqrt(T1[i,i]) : i in [1..n]];
   return basis1, lengths;
end function;

// Search for elliptic curves with discriminant delta or -delta.
// More precisely, search for c-invariants C4 and C6 satisfying
// 1728*Disc(E) = C4^3 - C6^2, where Disc(E) = delta or -delta.
// A curve with those invariants is given by coeffs 
// c4 = -C4/48, c6 = -C6/864, and scaling this by 6 gives
// c4 = -27*C4, c6 = -54*C6
// Returns only one of each pair (C4, +-C6)
// The 'bound' controls the size of the search for short vectors:
// the size of the search space is roughly bound^(n/2)
/*
function weighted_integral_C4_search(F, delta, bound : res_maps:=0)
   ZF := Integers(F);
   delta := ZF! delta;
   assert delta ne 0;
 
   // C = scaling constant for rounding to integral Gram
   C := 10 ^ Round(100 + 2/Log(10)*AbsoluteLogarithmicHeight(delta)); 
   W := weights(delta);
   G_real := trace_form_matrix(Basis(ZF), W);
   G := Matrix(Degree(F), [Round(C*x) : x in Eltseq(G_real)]);
   L := LatticeWithGram(G);
   n := Dimension(L);
   scal_det := C^n * (&*W)^2 * Abs(Discriminant(ZF));
   scal := scal_det ^ (1/n);
   assert Abs( Determinant(L) - scal_det ) lt C^n*10^-20;
   SV := ShortVectors(L, Round(scal*bound));

   // For each C4 found in the lattice search, we must also try 
   // its negative, and we also try likely multiples 
   // TO DO: other multiples? maybe 3, 4, 16, 48
   mults := [1, -1];
   found := [];
   pts_delta := [];
   pts_mdelta := [];

   vprintf ECSearch, 4: "%o short vectors ... ", #SV;
   vtime ECSearch, 4:

   for tup in SV do 
      v := Eltseq(tup[1]);
      _C4 := ZF! v;
      flag := false;
      for s in mults, t in [1,-1] do
         C4 := s*_C4;
         C6sq := C4^3 - t*1728*delta;

         bool, C6 := IsSquare(C6sq);
         if bool then
            case t: 
               when 1:  Append(~pts_delta, [C4,C6]);
               when -1: Append(~pts_mdelta, [C4,C6]);
            end case;
            E := EllipticCurve([F| -27*C4, 54*C6]);
            if not exists{EE: EE in found | IsIsomorphic(E,EE)} then
               Append(~found, E);
            end if;
         end if;

      end for; // s
   end for; // tup

   return found, pts_delta, pts_mdelta;
end function;
*/

///////////////////////////////////////////////////////////////////////
// Main routine

// Better strategies (needs to be checked at primes above 2 and 3)
//  if vD < vN, should increase vD by 6
//  if vN >= 2 and vD = 5, point cannot be integral
//  if vN >= 2 and vD < 6 then vj >= 0, so vC4 >= vD/3 

function InternalEllipticCurveSearch(conductors, Effort : All:=false,
                                     Full:=0, Max:=Infinity(), 
                                     Primes:=[], Traces:=[], 
                                     Deltas:=[], Flags:=[true,true,true], 
                                     Smart:=false, ReturnExtraCurves:=false)
   time00 := Cputime();
//ProStart();

   ZF := Ring(Universe(conductors));
   F := NumberField(ZF); 
   n := Degree(ZF);
   PI := PowerIdeal(ZF);

   Nfacts := [Factorization(N) : N in conductors];
   Ss := {PI| t[1] : t in x, x in Nfacts};
   S := Sort(Setseq(Ss));

   if Full cmpeq 0 then 
      // by default, full search if there is no early stopping condition
      Full := Max cmpeq Infinity() and Traces cmpeq [];
   end if;

   use_traces := not IsEmpty(Traces);
   if use_traces then
      // Traces is a sequence of sequences
      for seq in Traces do 
         assert #seq eq #Primes; 
      end for;
      // Remove primes dividing N
      inds := [i : i in [1..#Primes] | Primes[i] notin Ss];
      Primes := [Primes[i] : i in inds];
      if IsEmpty(Primes) then
         use_traces := false;
         print "WARNING: 'Traces' will be ignored";
      else
         Traces := [[S[i] : i in inds] : S in Traces];
      end if;
   end if;
   if use_traces and Max cmpeq Infinity() then
      // Max not specified; return if we find curves with the desired Traces
      Max := 0;
   end if;

   // Use the nontrivial field automorphisms that fix some conductor
   function conjugate(I,a)
      return ideal<ZF| [b@a : b in Basis(I)] >;
   end function;
   auts := [a : a in Automorphisms(F) 
              | not forall{g: g in GeneratorsSequence(F) | g@a eq g}];
   if not All then
      auts := [a : a in auts | 
                   exists{N: N in conductors | conjugate(N,a) in conductors} ];
   end if;

   Cl, mCl := ClassGroup(ZF);

   Q := Rationals();
   CDB := CremonaDatabase();
   CDBmax := LargestConductor(CDB);

   ///////////////////////////////////////////////////////////////////////////
   // Functions for processing found curves

   function conductor_is_wanted(I)
      if All then
         return forall{t : t in Factorization(I) | t[1] in S};
      else
         return I in conductors;
      end if;
   end function;

   // This is a cheap test compared with computing Conductor(E)
   function conductor_might_be_wanted(E, j)
      if All then // TO DO?
         return true;
      else
         // assert forall{c: c in Coefficients(E) | IsIntegral(c)};
         D := Discriminant(E);
         // assert j eq jInvariant(E);
         for Nfact in Nfacts do
            for t in Nfact do
               p, vN := Explode(t);
               vD := Valuation(D,p);
               impossible := vD lt vN or
                             // Ogg: vD = vN + (#components - 1) >= vN 
                             vN eq 1 and Valuation(j,p) ge 0;
                             // curve with integral j cannot have mult redn
               if impossible then
                  continue Nfact; // conductor can't be N
               end if;
            end for;
            return true; // conductor might be N
         end for;
         //assert Conductor(E) notin conductors;
         return false; // impossible for all conductors
      end if;
   end function;
 
   small_primes := NonInertPrimes(ZF, &*S, 30);

   procedure check_twists(E, twists, ~curves, ~traces, ~matched, ~done : search:="")

      assert forall{c : c in Coefficients(E) | IsIntegral(c)};

      matched := {};

      // If traces are given, check whether absolute values match
      // before running through many twists
      if #traces gt 0 and #twists gt 1 then
         disc := Discriminant(E);
         inds := [1 .. #traces];
         for i := 1 to #Primes do
            if Valuation(disc,Primes[i]) eq 0 then
               api := TraceOfFrobenius(E, Primes[i]);
               inds := [t : t in inds | Abs(api) eq Abs(traces[t,i])]; 
               if #inds eq 0 then
                 return;
               end if;
            end if;
         end for;
      end if;

      j := jInvariant(E);
      for d in twists do
         Ed := QuadraticTwist(E, d);
         if not exists{EE: EE in curves | IsIsomorphic(Ed,EE)} 
            and conductor_might_be_wanted(Ed,j) and conductor_is_wanted(Conductor(Ed))
         then
            if #Cl eq 1 then
               Ed := MinimalModel(Ed);
               disc := Discriminant(Ed);
            else
               disc := Discriminant(Ed)/6^12;
            end if;
            c := Coefficients(Ed);
            vprintf ECSearch, 2: "\n";
            vprintf ECSearch: "Found curve with discriminant %o (norm %o) and j = %o\n", 
                               disc, Norm(disc), j;
            vprintf ECSearch: "Coefficients: [%o, %o, %o, %o, %o]\n", c[1],c[2],c[3],c[4],c[5];
            vprintf ECSearch, 2: "Twisting element: %o\n", F!d;

            if IsVerbose("ECSearch") and search eq "MW" and j in Q and 
               Conductor(MinimalTwist(EllipticCurveWithjInvariant(Q!j))) le CDBmax 
            then
               print "\n  WARNING!!!!!\n  "*
                     "Curve with rational j-invariant should have been found at the start!\n"; 
            end if;

            Append(~curves, Ed);
            new_curves := [Ed];
            // take conjugate curves too
            for a in auts do 
               Eda := EllipticCurve([x@a : x in c]);
               if not exists{EE: EE in curves | IsIsomorphic(Eda,EE)} 
                  and conductor_might_be_wanted(Eda,j) and conductor_is_wanted(Conductor(Eda))
               then
                  Append(~curves, Eda);
                  Append(~new_curves, Eda);
               end if;
            end for;

            if #traces gt 0 then
               for EE in new_curves do
                  t := Index(traces, [TraceOfFrobenius(EE, P) : P in Primes]);
                  if t ne 0 and t notin matched then
                     vprintf ECSearch: "New curve matches given traces\n";
                     Include(~matched, t);
                  end if;
               end for;
            end if;

         end if;
      end for; // d in twists

      if #matched gt 0 then
         traces := [traces[t] : t in [1..#traces] | t notin matched];
      end if;

      done := IsFinite(Max) and #traces eq 0 and
              #{[TraceOfFrobenius(E,P) : P in small_primes] : E in curves} ge Max;
   end procedure;

   //////////////////////////////////////////////////////////////////////
   // This guesses whether we should skip a rank 1 curve:
   // 'answer' is true if A has rank 1 and probably has large regulator 
   // (based on a few terms of the L-value)

   procedure check_large_rank1(d, e, ~points, ~rankbounds, ~analregs, ~answer)

      answer := false;

      if Smart and rankbounds[d] eq 1 then
         // the smart money is on the higher rank curves
         printf "rank = 1, skipping";
         answer := true;
         return;
      end if;

/* (switched off for now)
      if #points[d] ne 0 or rankbounds[d] ne 1 then
         return;
      end if;

      // we should use this iff we do TD, currently for effort e >= 400
      ee := Ilog(4, e div 100); // ee = 1, 2, 3 ...
      assert ee ge 1; // this is assumed below

      bool, ar := IsDefined(analregs, d);
      if not bool then
         time0:=Cputime();
         A := auxil[d];
         L := LSeries(A);
         L`cfrequired := Min(1000*ee, L`cfrequired);
         lstar := Real(LStar(L, 1 : Derivative:=1));
         C := Ceiling( L`expfactor / L`cfrequired ); // lstar = Sum of a_n * G(n/L`expfactor)
printf "L*:%o", Round(lstar);
// temporary hack / experiment
if L`cfrequired lt L`expfactor/10 then
 for ii := 1 to 0 do
  L`cfrequired := 2*L`cfrequired;
  _lstar := Real(LStar(L, 1 : Derivative:=1));
  printf ":%o", Round(_lstar);
 end for;
end if;
         if C gt 1 then
            // Asymptotic: G(t) ~ c*Log(t)^n as t --> 0
            GC := Round(Real( G0(L,1/C,1,1) * C )); // G0 absorbs the 1/n
            c := Ceiling(GC/Log(C)^n); // get constant c empirically
            expected_tail := c*Log(C)^(n+1)/(n+1); // assuming C >> 1
printf ":C:%o", C;
printf ":G:%o", GC;
printf ":TAIL:%o", Round(expected_tail);
            if lstar lt 4^ee * expected_tail then
printf ":%o ", Cputime(time0);
               return;
            end if;
         end if;
         // lstar is positive and bigger than the expected tail of the sum, 
         // so it's likely that it really has this magnitude
         l := lstar / L`expfactor / Coefficient(fullgammaseries(L, 1.0, 1), 0);
if false and Abs(l - Evaluate(L, 1 : Derivative:=1)) ge 10^-3 then
 l; Evaluate(L, 1 : Derivative:=1); L`expfactor; fullgammaseries(L, 1.0, 1);
 assert false;
end if;
         ar := l / BSDEasyTerms(A);
         analregs[d] := ar;
         vprintf ECSearch, 2: ":REG:%o:%o ", Round(ar), Cputime(time0);
      end if;

      // On the first pass (e = 400), ignore if height > 50.
      // This value should be at least 40 or so, considering the kind of points
      // we find using either TDsearch or MW search with x-coordinate weights.
      // TO DO: should take into account the weights (archidean height of delta)
      // Note also that some points are much smaller than their canonical height.
      answer := ar gt 50*2^(ee-1);
*/
   end procedure;

   //////////////////////////////////////////////////////////////    
   // Start collecting curves, using various techniques
   // Call 'check_twists' to decide when done

   done := false;
   Es := [];

   SQ := Sort(Setseq({Minimum(P) : P in S}));
   SQ6 := {2,3} join Seqset(SQ);

   // List reps mod squares, to be used for quadratic twisting
   // (don't try to be Nice, just give me the actually units etc)
   F2S, mF2S := pSelmerGroup(2, Ss : Integral, Nice:=false);
   F2Selts0 := [F| x @@ mF2S : x in F2S];
   bool, F2Selts := CanChangeUniverse(F2Selts0, ZF);
   if not bool then
//error "2-Selmer group elements are not integral"; // TO DO
      // They are only used for twisting, this shouldn't be much worse 
      F2Selts := [ZF| IsIntegral(w) select w 
                       else w * Denominator(w)^2 : w in F2Selts0];
   end if;

   //////////////////////////////////////////////////////////////
   // j = 0 (follow Cremona-Lingham Proposition 4.1)

   vprint ECSearch: "Checking for curves with j-invariant 0 or 1728";

   odd3 := [P : P in Support(3*ZF) | IsOdd(Valuation(ZF!3,P))];
   if odd3 subset S then
      primes2 := {P : P in Support(2*ZF) | Valuation(ZF!2,P) mod 3 ne 0};
      primes3 := {P : P in Support(3*ZF) | Valuation(ZF!3,P) mod 4 eq 2};
      SS := Ss join primes2 join primes3; 
      // TO DO: unfortunately the Integral option does not always work
      F2SS, mF2SS := pSelmerGroup(2, SS : Integral, Nice:=false);
      F2SSelts := [ZF| x @@ mF2SS : x in F2SS];
      F2SSelts := [F| IsIntegral(w) select w 
                       else w * Denominator(w)^2 : w in F2SSelts];
      F3SS, mF3SS := pSelmerGroup(3, SS : Integral, Nice:=false);
      F3SSelts := [ZF| x @@ mF3SS : x in F3SS]; 
      F3SSelts := [F| IsIntegral(w) select w 
                       else w * Denominator(w)^3 : w in F3SSelts];
      twists := [F| s2^3 * s3^2 : s2 in F2SSelts, s3 in F3SSelts];
      for P in primes3 diff Ss do
         twists := [F| w : w in twists | Valuation(w,P) mod 6 eq 3];
      end for;
      for P in primes2 diff Ss do
         twists := [F| w : w in twists | Valuation(w,P) mod 6 in {2,4}];
      end for;
      for w in twists do 
         E := EllipticCurve([0,w]);
         check_twists(E, {1}, ~Es, ~Traces, ~matched, ~done);
         if done then
            return Es, [];
         end if;
      end for;
   end if;

   //////////////////////////////////////////////////////////////
   // j = 1728 (follow Cremona-Lingham Proposition 4.2)

   odd2 := {P : P in Support(2*ZF) | IsOdd(Valuation(ZF!2,P))};
   SS := Ss join odd2;
   F4SS, mF4SS := pSelmerGroup(4, SS : Integral, Nice:=false); 
   twists := [ZF| x @@ mF4SS : x in F4SS];
   twists := [F| w * Denominator(w)^4 : w in twists]; // make them integral
   for P in odd2 diff Ss do
      twists := [F| w : w in twists | Valuation(w,P) mod 4 eq 2];
   end for;
   for w in twists do 
      E := EllipticCurve([w,0]);
      check_twists(E, {1}, ~Es, ~Traces, ~matched, ~done);
      if done then
         return Es, [];
      end if;
   end for;

   //////////////////////////////////////////////////////////////
   // Try to obtain curves as twists of curves defined over Q 
   // (for conductors N that have same valuation at all primes above each Q-prime)
   // TO DO: capture all twists by ignoring square factors in the conductor

if not All then // TO DO
 for N in conductors do

   vals := [{Valuation(N,P) : P in Support(p*ZF)} : p in SQ];
   if forall{v: v in vals | #v eq 1} then
      vals := [Rep(v) : v in vals];
      NQ := &* [Integers()| SQ[i]^vals[i] : i in [1..#SQ]];
      // Curve over Q might acquire good/better reduction over F
      // (at primes with ramification degree divisible by 2 or 3)
      // TO DO: THINK!!!
      ram := [p : p in PrimeDivisors(Discriminant(ZF))
                | forall{P : P in Support(p*ZF) | GCD(RamificationDegree(P), 6) ne 1}];
      extra := [1];
      for p in ram do
         if p eq 2 then
            if p in SQ then
               ppowers := [2^i : i in [2..8]];
            else
               ppowers := [2^4, 2^6];
            end if;
         elif p eq 3 then
            if p in SQ then
               ppowers := [3^i : i in [2..5]];
            else
               ppowers := [3^2];
            end if;
         else 
            ppowers := [p^2];
         end if;
         extra cat:= [e*pp : e in extra, pp in ppowers];
      end for;
      conds := Sort(Setseq( {LCM(e,NQ) : e in extra} ));
      if ram subset SQ then
         twists := F2Selts;
      else
         F2Sram, mF2Sram := pSelmerGroup(2, Ss join Support(&*ram*ZF) : Integral, Nice:=false);
         twists := [ZF| x @@ mF2Sram : x in F2Sram];
      end if;
         
      vprint ECSearch: "Checking Q-rational curves with conductors", conds;
      // TO DO: for larger conductors, call this routine over Q? or similar?
      for NQ in conds do 
         if NQ le CDBmax then
            for i := 1 to NumberOfIsogenyClasses(CDB, NQ) do
               E := BaseChange(EllipticCurve(CDB, NQ, i, 1), F);
               check_twists(E, twists, ~Es, ~Traces, ~matched, ~done);
               if done then
                  return Es, [];
               end if;
            end for;
         end if;
      end for;
   end if;

 end for; // N in conductors
end if;
    
   //////////////////////////////////////////////////////////////////////
   // Main search starts here

   if Effort lt 1 then
      return Es, [];
   end if;

   // List the candidate discriminants delta
   // First get the S-units (modulo 6th powers)
   SU, mSU := SUnitGroup(S);
   SUgens := [ZF| SU.i @ mSU : i in [1..Ngens(SU)]];
   // List reps of S-units modulo 6th powers, modulo torsion units
   cart := [[0]] cat [[1,2,3,4,5,6] : i in [2..Ngens(SU)]];
   deltas := [ZF| mSU(SU![x: x in t]) : t in CartesianProduct(cart)];

   // Put in class group contribution by hand, to retain full control. 
   // Let I = ideals, P = principal ideals.
   // List elements d mod P^6 such that d*P^6 = Delta*I^12 with Delta supported in S
   // It's not worth separating trivial cases, there's not much overhead.

   IS := AbelianGroup([0 : i in S]);
   IStoCl := hom< IS -> Cl | [I@@mCl : I in S] >;
   SCl := Image(IStoCl);
   ClS, modS := quo< Cl | SCl >;
   ClS6 := Kernel(hom< ClS -> ClS | [6*ClS.i : i in [1..Ngens(ClS)]] >);
   G := ClS6 meet 2*ClS;

   if #G gt 1 then
      class_reps := [ZF| 1];
      for j := 1 to Ngens(G) do
         x := G.j;
         m := Order(x);
         I := x @@ modS @ mCl;
         J := Eltseq((-m * (x @@ modS)) @@ IStoCl);
         J := &* [PI| S[j]^J[j] : j in [1..#J]];
         bool, r1 := IsPrincipal(I^m*J);
         r := r1^(12 div m);
         class_reps := [ZF| c*r^i : c in class_reps, i in [0..m-1]];
      end for;
      vprintf ECSearch: "S-class group reps: \n%o\n", class_reps;

      deltas := [ZF| d*c : d in deltas, c in class_reps];
   end if;

   signs := [Universe(deltas)| tu @ mTU : tu in TU] where TU, mTU is TorsionUnitGroup(F);

   vprintf ECSearch: "\n%o candidates for discriminants (up to 6th powers)\n", 2*#deltas;

   // Multiply deltas by 6th powers of fundamental unit, to make them as small as possible
   // TO DO: standard routine for this, not only in real quadratic case
   function adjust_by_units(deltas)
      if n ne 2 or Signature(F) ne 2 then
         return deltas;
      end if;
      deltas0 := deltas;
      seq := Type(deltas) eq SeqEnum;
      deltas := seq select [ZF|] else {ZF|};
      u6 := SUgens[2] ^ 6;
      um6 := SUgens[2] ^ -6;
      for d0 in deltas0 do
         d := d0;
         size := &+ [x^2 : x in Eltseq(d)];
         while true do
            d1 := u6*d;
            size1 := &+ [x^2 : x in Eltseq(d1)];
            if size1 lt size then
               d := d1;
               size := size1;
               continue;
            end if;
            d1 := um6*d;
            size1 := &+ [x^2 : x in Eltseq(d1)];
            if size1 lt size then
               d := d1;
               size := size1;
               continue;
            end if;
            if seq then 
               Append(~deltas, d); 
            else
               Include(~deltas, d); 
            end if;
            continue d0;
         end while;
      end for;
      return deltas;
   end function;

   if use_traces then
      // Sieve to cut down the possible discriminants for each newform,
      // using that 1728*d = c4^3 - c6^2 and j*d = c4^3
      pmdeltas := {s*d : s in signs, d in deltas};
      num_primes := 0;
      stable := false;
      while not stable and num_primes lt #Primes do
         num_primes := Min(num_primes + 20, #Primes);
         stable := true;
         inds := [i : i in [1..num_primes] | IsPrime(Norm(Primes[i]))];
         resmaps := [* 0 : i in [1..#Primes] *];
         res_jts := [* 0 : i in [1..#Primes] *];
         squares := [* 0 : i in [1..#Primes] *];
         cubes   := [* 0 : i in [1..#Primes] *];
         vprintf ECSearch, 2: "Setting up to sieve the deltas:\n";
         vtime ECSearch, 2:
         for i in inds do 
            k, res := ResidueClassField(Primes[i]);
            vprintf ECSearch, 2: "%o ", #k;
            Ek, tk := EllipticCurves(k);
            res_jts[i] := [<jInvariant(Ek[i]), tk[i]> : i in [1..#Ek]];
            resmaps[i] := res;
            squares[i] := {x^2 : x in k};
            cubes[i] := {x^3 : x in k};
         end for;
         pmdeltas_for_traces := [];
         for t := 1 to #Traces do
            sieve := pmdeltas;
            sh := [#sieve];
            vprintf ECSearch, 2: "Sieving the %o possible deltas:\n", #sieve;
            vtime ECSearch, 2:
            for r in inds do
               res := resmaps[r];
               q := #Codomain(res);
               // possible j-invariants of reduction of curve with these traces
               js := {jt[1] : jt in res_jts[r] | jt[2] eq Traces[t,r]};
               // sieve down to d for which there exists some j with
               // d*j        = a cube (= c4^3), and
               // d*(j-1728) = a square (= c6^2)
               use_s := 1728 notin js;
               use_c := 0 notin js and q mod 3 eq 1;
               if use_s then
                  sieve_s := {x/(j-1728) : x in squares[r], j in js};
                  use_s := #sieve_s lt q;
               end if;
               if use_c then
                  sieve_c := {x/j : x in cubes[r], j in js};
                  use_c := #sieve_c lt q;
               end if;
               if not use_s and not use_c then
                  continue r;
               end if;
               sieve := {d : d in sieve | (not use_s or rd in sieve_s) and
                                          (not use_c or rd in sieve_c)
                                          where rd is res(d) };
               Append(~sh, #sieve);
               vprintf ECSearch, 2: "(%o) %o ", #Codomain(resmaps[r]), #sieve;
            end for; // r
            // the sieved set is always closed under inverse (mod 6th powers)
            // TO DO: this is crap, it can change after stable for 10 primes
          //stable and:= #sieve le 2 or #sh gt 10 and sh[#sh-10] eq sh[#sh];
            stable and:= #sieve le 2;
            if not stable and num_primes lt #Primes then
               break t; // set up more Primes
            end if;
            error if #sieve eq 0, "No elliptic curves have the specified 'Traces'";
            Append(~pmdeltas_for_traces, sieve);
         end for; // t
      end while;
      assert #pmdeltas_for_traces eq #Traces;

      vprintf ECSearch, 2: "Adjusting %o elements by units: ", 
                           &+ [#pmd : pmd in pmdeltas_for_traces]; 
      vtime ECSearch, 2:
      pmdeltas_for_traces := [adjust_by_units(pmd) : pmd in pmdeltas_for_traces];
      possible_pmdeltas := &join pmdeltas_for_traces;
      pmdeltas := Setseq(possible_pmdeltas);

      vprintf ECSearch: "After sieving, %o candidate discriminants: %o\n", 
                         #pmdeltas, [#x : x in pmdeltas_for_traces];
   else
      vprintf ECSearch, 2: "Adjusting %o elements by units: ", #deltas; 
      vtime ECSearch, 2:
      pmdeltas := [s*d : s in signs, d in adjust_by_units(deltas)];
   end if; // use_traces

if not IsEmpty(Deltas) then
   pmdeltas := Deltas;
end if;

   // For each delta, list ideals C where c4 might live:
   // we will search for c4 satisfying to c4^3 - c6^2 = d*dd^6 
   // (for certain 'denominators' dd in ZF) 
   // Let Delta be the minimal discriminant of the curve given by [c4,c6]
   // (ie the product of the local minimal discriminants). 
   // Then we have (d*dd^6) = Delta*C^6 for some integral ideal C,
   // furthermore C has the form I^2*P, and c4 lies in C^2
   // Write Delta = Delta0 * Delta1^6, both integral ideals in I_S

   Cl2, mod2 := quo< Cl | 2*Cl >;
   cl2 := hom< IS -> Cl2 | [I @@mCl @mod2 : I in S] >;
   C4ideals := AssociativeArray();
   for d in pmdeltas do
      D0 := &* [PI| P^(Valuation(d,P) mod 6) : P in S];
      bool, D1 := IsPower(d*D0^-1, 6); assert bool;
      if IsOne(D1) then
         C4ideals[d] := [D1];
      else
         // D1 = Delta1 * C, with C = I^2*P,
         // List exponent vectors of the possibilities for Delta1
         c := D1 @@mCl @mod2;
         vv := [];
         for x in CartesianProduct(<[0..Valuation(D1,P)] : P in S>) do
            v := [i : i in x];
            if cl2(IS!v) eq c then
               Append(~vv, v);
            end if;
         end for;
         C4ideals[d] := [(D1 / &* [PI| S[i]^v[i] : i in [1..#S]]) ^ 2 : v in vv];
      end if;
   end for;

   // TO DO
   // Spend more effort on the more likely deltas
   // TO DO: should be based on minimal discriminant rather than delta
   effort := AssociativeArray(pmdeltas);
   for d in pmdeltas do
      effort[d] := 1;
   end for;
   /* Note: here N = the desired conductor
   for P in S do 
     if Valuation(N, P) eq 1 and (ZF!2) notin P then
        for d in pmdeltas do
           case Valuation(d, P):
             when 1: effort[d] *:= 4;
             when 2: effort[d] *:= 2;
           end case;
        end for;
     elif Valuation(N, P) eq 2 and (ZF!2) notin P then
        for d in pmdeltas do
           case Valuation(d, P) mod 6:
             when 0: effort[d] *:= 2;
           end case;
        end for;
     end if;
   end for;
   // Set an upper limit on the effort factors
   for d in pmdeltas do
      effort[d] := Min(8, effort[d]);
   end for;
   */

   // Sort deltas (try the more likely ones first)
   ordering := [[-effort[d], Abs(Norm(d)), AbsoluteLogarithmicHeight(d)] : d in pmdeltas];
   ParallelSort(~ordering, ~pmdeltas);

   vprintf ECSearch, 3: "Norms of candidate discriminants: \n%o\n", [Norm(d) : d in pmdeltas];
   vprintf ECSearch, 3: "Effort factors: \n%o\n", [effort[d] : d in pmdeltas];

   vprintf ECSearch: "Preliminary phase took %os\n", Cputime(time00);
//ProShow(40);

   // Initialize the auxiliary elliptic curves corresponding to deltas
   // (we want to only check things once, not for every B in Bs, below)
   auxil := AssociativeArray(pmdeltas);
   rankbounds := AssociativeArray(pmdeltas);
   analregs := AssociativeArray(pmdeltas); // assigned by check_large_rank1
   tdct := AssociativeArray(pmdeltas);     // tuple <td, tdm> is assigned iff done CT
   points := AssociativeArray(pmdeltas);
   checked_points := AssociativeArray(pmdeltas);
   for d in pmdeltas do 
      A := EllipticCurve([F| 0, -1728*d]);
      auxil[d] := A;
      rankbounds[d] := Infinity();
      points[d] := [A(F)| ];
      checked_points[d] := {A(F)| };
   end for;
   checked_Es := {PowerSequence(F)| }; // (could make it an array on deltas)

   procedure include(~points, d, pts)
      if #pts gt 0 then
         points[d] := IndependentGenerators(points[d] cat [Universe(points[d]) | pt : pt in pts]);
      end if;
   end procedure;

   bab_cache := AssociativeArray(); // used for basis_and_bounds

   // Run the searches with increasing amount of effort, alternating between the
   // candidate discriminants.
   Bound := Ceiling(Maximum(1, Effort));
   if Full or Bound lt 16 then
      Bs := [Bound];
   else
      Bs := [Ceiling(Bound/4^i) : i in [Ilog(4,Bound) .. 0 by -1]];
      Bs := [B : B in Bs | B ge 4]; assert not IsEmpty(Bs);
   end if;
   Bmax := Bs[#Bs];

   // We want heuristic class groups in TwoDescent
   // (there is no need for rigour here, obviously)
   CGBFB := GetClassGroupBoundFactorBasis();
   CGBG := GetClassGroupBoundGenerators();
   SetClassGroupBounds("GRH");

   for B in Bs do 
//ProStart();
      vprintf ECSearch, 2: "\n";
      vprintf ECSearch: "Effort = %o: ", B;

      // Prepare some ideals, a subset of which will be the denominators in each MW search.
      // (Consider at least first powers, but not absurd powers, and bound the norms)
      MWDenoms := {1*ZF};
      for P in S do
         case Minimum(P):
            when 2: e1 := 4; f1 := 2;
            when 3: e1 := 2; f1 := 1;
            else  : e1 := 1; f1 := 1;
         end case;
         Ppowers := [Pi2^e : e in [0 .. e1 + f1 * Ilog(4, 1 + B div 100)] ] where Pi2 is P^-2;
         MWDenoms := {I * PP : I in MWDenoms, PP in Ppowers};
      end for;
      MWDenoms := Setseq(MWDenoms join {1/i^2*ZF : i in [2..20]});
      norms := [1/Norm(I) : I in MWDenoms];
      ParallelSort(~norms, ~MWDenoms);
      assert IsOne(MWDenoms[1]);
      if IsVerbose("ECSearch", 3) then
         print "Potential denominators for MW search:";
         for I in MWDenoms do 
            print Norm(I), [<Norm(t[1]),t[2]> : t in Factorization(I)]; 
         end for;
      end if;

      timeB := Cputime();

      for d in pmdeltas do
            if use_traces and d notin possible_pmdeltas then
               continue;
            end if;

            BB := Ceiling(B * effort[d]);
            if BB ge 400 then
               vprintf ECSearch, 2: "\n%o%o ", str, &*[Strings()| " " : i in [#str..40]]
                                     where str is "["*Sprint(BB)*"]  "*Sprint(F!d);
            end if;

            // Decide whether and how to use TwoDescent:
            // for searching or for identifying rank zero curves
            TD  := Flags[1] and BB ge 400 and Abs(Discriminant(ZF)) le 10^20;
            TDR := Flags[2] and TD;   // reduce the 2-coverings (and search on them)
            CT  := Flags[3] and TDR;  // use Cassels-Tate
CT := CT and #signs mod 3 ne 0; // TO DO implement it

            // Choose bounds so that search time is close to O(BB)
            // The search routine spends time setting up the filter, 
            // so there's no point calling it with a small bound.
            MWB := Ceiling( (10000*BB)^(1/n) );
            TDB := Ceiling( MWB ^ (1/2) );
            // Choose denominators: the MWdenoms are ideals which could occur in 
            // denominators of the point(s) we are looking for, because the MW search 
            // targets finding these points directly rather than just finding generators.
            // TO DO: spend more effort on the most likely denominators?
            // The TDdenoms are just elements of small height, no clever choices. 
            // TO DO: could predict congruences on x-coords of points on 2-coverings?
            MWdenoms :=  MWDenoms[1 .. Min(#MWDenoms, Ceiling(2*MWB^0.2))];
            // Balance MWB with TDB (c = 1 for same number of x-values)
            MWB := Ceiling( MWB * (c/#MWdenoms)^(1/n) ) where c is 2;

            // Mordell-Weil search and/or 2-descent search, and (always) check torsion points
            A := auxil[d];
            TA, mTA := TorsionSubgroup(A);
            torsA := [t@mTA : t in TA];
            large_rank1 := false;

            if TD then

               if rankbounds[d] eq Infinity() then
                  vprintf ECSearch, 2: "TD:";
                  time0 := Cputime(); 
                  rankbounds[d] := Ilog(2, #TwoSelmerGroup(A) div #TwoTorsionSubgroup(A));
                  assert #points[d] le rankbounds[d];
                  vprintf ECSearch, 2: "%o ", Cputime(time0);
               end if;

               done_ct, tup := IsDefined(tdct, d);
               if done_ct then
                  td, tdm := Explode(tup);
               end if;

               // Reduction is needed for searching, and for Cassels-Tate
               // (Note: results of TwoSelmerGroup and TwoDescent are cached)
               if TDR and not done_ct and #points[d] lt rankbounds[d] then
                  check_large_rank1(d, BB, ~points, ~rankbounds, ~analregs, ~large_rank1);
                  if not large_rank1 then
                    done_tdr := true; // just a check
                    vprintf ECSearch, 2: "TDR:";
                    time0 := Cputime(); 
                    td, tdm, tdsel := TwoDescent(A : RemoveTorsion, MinRed);
                    tds := [Domain(tdsel) | q @@ tdsel : q in td];
                    vprintf ECSearch, 2: "%o ", Cputime(time0);
                  end if;
               end if;

               // TO DO: now check which 2-coverings contain a preimage of points[d]

               // Cassels-Tate
               if CT and not done_ct and #points[d] le rankbounds[d] - 2 then
                  assert done_tdr;
                  vprintf ECSearch, 2: "CT:";
                  time0 := Cputime(); 
                  tdS := Universe(tds);
                  // TO DO: choose tdbasis to be the smallest ones
                  tdbasis := [ td [Index(tds,tdS.i)] : i in [1..Ngens(tdS)] ];
                  ctmat := CasselsTatePairingMatrix(tdbasis);
                  kernel_inds := [Index(tds, tdS!Eltseq(v)) : v in Kernel(ctmat)];
                  Exclude(~kernel_inds, 0);
                  td := [td[i] : i in kernel_inds];
                  tdm := [tdm[i] : i in kernel_inds];
                  rct := Ilog(2, 1+#td);
                  sha := rankbounds[d] - rct;
                  assert sha ge 0 and IsEven(sha);
                  // update stored data
                  tdct[d] := <td, tdm>;
                  rankbounds[d] := rct;
                  if sha gt 0 then
                     vprintf ECSearch, 2: "SHA%o:", sha;
                     vprintf ECSearch, 2: "%o ", Cputime(time0);
                     check_large_rank1(d, BB, ~points, ~rankbounds, ~analregs, ~large_rank1);
                  else
                     vprintf ECSearch, 2: "%o ", Cputime(time0);
                  end if;
               end if;

               // Spend more effort if rank >= 2 (the hard ones are almost always rank 2, 
               // so we want to spend a positive proportion of total time on these cases)
               // TO DO: could make this even more if we could get rid of the ones with Sha[4]
               if CT and rankbounds[d] ge 2 then
                  // multiply effort by some factor (except don't bother to use more denominators)
                  e := Ceiling(16 / effort[d]);
                  BB *:= e;
                  MWB := Ceiling( MWB * e^(1/n) );
                  TDB := Ceiling( TDB * e^(1/(2*n)) );
                end if;

               // Search on 2-coverings
               if TDR and #points[d] lt rankbounds[d] and not large_rank1 then
                  // TO DO: Search all 2-coverings except those in the preimage of <points[d]>
                  // Note: it's not a good idea to only search coset representatives for TD/<points[d]>
                  if #td gt 0 and #points[d] lt rankbounds[d] then
                     time0 := Cputime();
//""; time
                     TDdenoms := ShortElements(ZF, TDB); // TO DO: don't recompute every time when e = 1
//"#TDdenoms =", #TDdenoms;
                     sizes := [Round(Log(10,1+Abs(Norm(LeadingCoefficient(HyperellipticPolynomials(C2)))))) : C2 in td];
                     Sort(~sizes, ~perm);
                     td := [td[i] : i in Eltseq(perm)];
                     tdm := [tdm[i] : i in Eltseq(perm)];
                     num_td_searched := 0;
                     for t := 1 to #td do 
                        if sizes[t] gt 10 then vprintf ECSearch, 2: "X"*Sprint(sizes[t])*":"; end if;
                        num_td_searched +:= 1;
                        pts2 := RationalPoints(td[t] : Max:=1, Bound:=TDB, Denominators:=TDdenoms, NPrimes:=20);
                        if not IsEmpty(pts2) then
                           include(~points, d, [pt@tdm[t] : pt in pts2]);
                           assert #points[d] le rankbounds[d];
                           if #points[d] eq rankbounds[d] then
                              break t;
                           end if;
                        end if;
                        delete pts2;
                     end for;
                     vprintf ECSearch, 2: "%o/%o", num_td_searched, #td;
                     if num_td_searched gt 0 then 
                        vprintf ECSearch, 2: ":%o ", Cputime(time0); 
                     end if;
                  end if;
               end if;

            end if; // TD

            // Search on A itself, if we have not found generators yet.
            // Note: here we are aiming to directly find the point with 
            // x = C4, rather than just to find some generators of A, 
            // so we use the weighting and congruences coming from delta.

            // We search for x-values in g*I1 = I = C4_ideal*D_ideal
            // (where I1 is integral).  
            // Only call basis_and_bound once for each I1.
            gIs := [];
            // take the ideals C*D in that order without repeats
            for I in {@ C*D : C in C4ideals[d], D in MWdenoms @} do
               gi := Minimum(I^-1);
               I1 := PI! (gi*I);
               Append(~gIs, <Q!1/gi, I1>);
            end for;

            if #points[d] lt rankbounds[d] and not large_rank1 then
               time0 := Cputime();
               babprec := 100;
               wts := weights(d, babprec);
               fA := HyperellipticPolynomials(A);
               x := Parent(fA).1;
               for tup in gIs do
                  g, I := Explode(tup);
                  bool, baboR := IsDefined(bab_cache, <I,d>);
                  if bool then
                     ba, boR := Explode(baboR);
                  else
                     ba, boR := basis_and_bounds(I, d, wts, babprec);
                     bab_cache[<I,d>] := <ba, boR>;
                  end if;
                  bo := integer_bounds(boR, MWB);
                  // Need to search for x in g*I 
                  // Here g is in Q, not necessarily square (although often close to a square)
                  // Note that scaling f by a square integer doesn't hurt 
                  f := Numerator(g)^4 * Evaluate(fA, x/g); 
                  f := ChangeRing(f, ZF);
                  // TO DO: more conditions on primes for Sieve? 
                  //        or skip this and let Sieve figure it out?
                  sp := [P : P in small_primes | Valuation(Fg,P) eq 0] where Fg is F!g;
                  sp := sp[1..Min(20,#sp)];
                  sieve := Sieve(f, sp, bo : Basis:=ba);
                  xcandidates := [&+[ v[i]*ba[i] : i in [1..#ba]] : v in sieve];
                  pts := {xpts[1] : x in xcandidates | not IsEmpty(xpts) 
                          where xpts is Points(A,g*x)};
                  if not IsEmpty(pts) then
                     include(~points, d, pts);
                     assert #points[d] le rankbounds[d];
                     if #points[d] eq rankbounds[d] then
                        break tup;
                     end if;
                  end if;
                  delete pts;
               end for;

               vprintf ECSearch, 2: "MW:%o ", Cputime(time0);
               vprintf ECSearch, 3: "(MWB=%o*%o) ", MWB, #gIs;
            end if;

            // Check whether points give us elliptic curves with desired conductor
/*
R0 := Regulator(points[d]);
*/
            points[d] := Saturation(points[d], 3 : TorsionFree);
/*
R1 := Regulator(points[d]);
if Abs(R0 - R1) gt 10^-10 then "\nREGULATOR RATIO", R0/R1; end if;
*/
            basis := points[d];
            r := #basis; 
            if r eq 0 then
               combs := torsA;
            else
               // Test combinations of generators up to some bound
               // (only one of each pair +-pt, since we check twists by -1)
               // Let b = bound on coeffs of combinations of the basis.
               // These have log height O(R*b^2), so cost of listing them is O(R*b^(2+r))
               // TO DO: 
               // make this a smaller proportion of work (except at very low effort),
               // since testing large multiples is really wasted time 
               // TO DO: non-rectangular search region?
               R := Regulator(basis); 
               assert Abs(R) ge 10^-10;
               b := Ceiling( (100*BB/R) ^ (1/(2+r)) );
               if b gt 20 then // large multiples are surely a waste of time, so cut down a bit
                  b := 20 + (b-20) div 5;
               elif r ge 2 then // don't want to miss out
                  b := Maximum(5, b);
               end if;
               vprintf ECSearch, 2: "%o^%o", #basis, b;
               time0 := Cputime();
               combs := [A!0];
               for i := 1 to #basis do
                  coeffs := (i eq 1) select [0..b] else [-b..b];
                  mults := [c*basis[i] : c in coeffs];
                  combs := [p1 + p2 : p1 in combs, p2 in mults];
               end for;
               delete mults;
               combs := [p1 + p2 : p1 in combs, p2 in torsA];
               vprintf ECSearch, 2: ":%o ", Cputime(time0);
            end if;
            for pt in combs do
               X,Y,Z := Explode(Eltseq(pt));
               if 0 in [X,Y,Z] then
                  continue;
               end if;
               if is_S_integral(X/Z, S) then
                  if pt notin checked_points[d] then
                     // Don't use checked_points, for now
                     // Include(~checked_points[d], pt);
                     E := IntegralModel(EllipticCurve([F| -27*X/Z, 54*Y/Z]));
                     nchecked := #checked_Es;
                     Include(~checked_Es, Coefficients(E));
                     if #checked_Es gt nchecked then // E has not been checked
                        vprintf ECSearch, 2: "E ";
                        check_twists(E, F2Selts, ~Es, ~Traces, ~matched, ~done : search:="MW");
                        if done then
//if B ge 4 then ProShow(40); end if;
                           break B;
                        elif use_traces and not IsEmpty(matched) then
                           // for each matched index t, Traces[t] was matched and removed
                           num := #pmdeltas_for_traces;
                           assert num eq #Traces + #matched and num gt 0;
                           pmdeltas_for_traces := [pmdeltas_for_traces[t] : t in [1..num] | t notin matched];
                           possible_pmdeltas := &join pmdeltas_for_traces;
                           vprintf ECSearch: "%o newforms still to be matched, %o candidate discriminants: %o\n", 
                                              #Traces, #possible_pmdeltas, [#x : x in pmdeltas_for_traces];
                        end if;
                     end if;
                  end if;
               end if;
            end for; // pt
            delete combs;

            // Get rid of stored fields that clutter up the Kant graph
            // (otherwise everything will slow down massively)
            // Note: this can result in recomputing the TwoSelmerGroup 
            //       only if TD is true but TDR is false
            if assigned A`TwoSelmerGroup then
               delete A`TwoSelmerGroup;
            end if;
            if assigned A`Algebra then
               delete A`Algebra;
            end if;

            if B eq Bmax then
               // Conserve memory, since these won't be used again
               delete A, TA, mTA, torsA;
               if assigned td then delete td; end if;
               if assigned tdm then delete tdm; end if;
               Remove(~auxil, d);
               Remove(~tdct, d);
               Remove(~points, d);
               Remove(~checked_points, d);
            end if;

            if TD then
               mark_sweep;
            end if;

      end for; // d

      vprintf ECSearch: "\nEffort = %o took %os ", B, Cputime(timeB);
      vprintf ECSearch: "[memory usage %oM]\n", GetMemoryUsage() div 10^6;

//if B ge 4 then ProShow(40); end if;
   end for; // B in Bs

   // Restore ClassGroup bounds to their initial state
   SetClassGroupBoundMaps(CGBFB, CGBG);

   if ReturnExtraCurves then 
      XEs := []; 
      for c in checked_Es do 
         E := EllipticCurve(c);
         if true or jInvariant(E) notin Q then
            Append(~XEs, E);
         end if;
      end for;
      return Es, XEs;
   else
      return Es;
   end if;

end function;

///////////////////////////////////////////////////////////////////////////////
// Intrinsics

function check(S, Primes, Traces, Max)

   if Max lt 1 then
      return false, "'Max' should be a positive integer", _, _;
   end if;

   if IsNull(S) then
      return false, "First argument is null set -- a universe must be specified", _, _;
   end if;

   F := NumberField(Ring(Universe(S)));

   if not IsAbsoluteField(F) then 
      return false, "Not implemented for relative fields", _, _;
   end if;

   if not ISA(Type(Primes), SeqEnum) then
      return false, "'Primes' should be a sequence", _, _;
   elif not ISA(Type(Traces), SeqEnum) then
      return false, "'Traces' should be a sequence", _, _;
   elif not IsEmpty(Traces) then
      // Traces can be a single sequence of integers, or a sequence of such
      if Type(Traces[1]) ne SeqEnum then
         Traces := [Traces];
      end if;
      try
         Traces := [ChangeUniverse(seq, Integers()) : seq in Traces];
         okay := true;
      catch ERR
         okay := false;
      end try;
      if not okay then
         return false, "The optional argument Traces should be a sequence of sequences of integers", _, _;
      end if;
      for P in Primes do 
         if not IsPrime(P) then
            return false, "The optional argument Primes should contain primes", _, _;
         end if;
      end for;
      for seq in Traces do 
         if #seq ne #Primes then
            message := Sprintf("Bad optional arguments: number of Primes (= %o) does not match number of Traces (= %o)\n",
                                IntegerToString(#Primes), IntegerToString(#seq) );
            return false, message, _, _;
          end if;
      end for;
   end if;

   return true, _, Primes, Traces;
end function;

// ReturnExtraCurves option is not documented

// Possible additional options: NoTwoDescentReduction

intrinsic EllipticCurveSearch(N::RngOrdIdl, Effort::RngIntElt :
                              Full:=0, Max:=Infinity(), 
                              Primes:=[], Traces:=[], 
                              NoTwoDescent:=false,
                              ReturnExtraCurves:=false)
       -> SeqEnum
{Search for elliptic curves with conductor equal to the ideal N.
 This is a search routine only: it does not necessarily return all such curves!
 'Effort' controls the length of the search (running time is roughly linear in this)}
/*
 'Full' means use full effort immediately,
 'Max' is desired number of isogeny classes of curves,
 'Primes' and 'Traces' are used to specify the traces of Frobenius of the desired curves(s)
 'ReturnExtraCurves' also returns a second sequence containing curves with other conductors
*/
   bool, message, Primes, Traces := check({N}, Primes, Traces, Max);
   require bool : message;

   f := not NoTwoDescent;

   return InternalEllipticCurveSearch({N}, Effort : Full:=Full, Max:=Max,
                                      Primes:=Primes, Traces:=Traces, Flags:=[f,f,f],
                                      ReturnExtraCurves:=ReturnExtraCurves);
end intrinsic;

intrinsic EllipticCurveWithGoodReductionSearch(N::RngOrdIdl, Effort::RngIntElt :
                                               Full:=0, Max:=Infinity(), 
                                               Primes:=[], Traces:=[], 
                                               NoTwoDescent:=false,
                                               ReturnExtraCurves:=false)
       -> SeqEnum
{Search for elliptic curves with good reduction except at primes dividing N,
 or in the ideal S.
 This is a search routine only: it does not necessarily return all such curves!
 'Effort' controls the length of the search (running time is roughly linear in this)}

   S := {PowerIdeal(Order(N)) | t[1] : t in Factorization(N)};

   bool, message, Primes, Traces := check(S, Primes, Traces, Max);
   require bool : message;

   f := not NoTwoDescent;

   return InternalEllipticCurveSearch(S, Effort : All, Full:=Full, Max:=Max,
                                      Primes:=Primes, Traces:=Traces, Flags:=[f,f,f],
                                      ReturnExtraCurves:=ReturnExtraCurves);
end intrinsic;

intrinsic EllipticCurveWithGoodReductionSearch(S::Set, Effort::RngIntElt :
                                               Full:=0, Max:=Infinity(), 
                                               Primes:=[], Traces:=[], 
                                               NoTwoDescent:=false,
                                               ReturnExtraCurves:=false)
       -> SeqEnum
{"} // "
   require forall{P : P in S | Type(P) eq RngOrdIdl and IsPrime(P)} :
          "The first argument should be a set of prime ideals";

   bool, message, Primes, Traces := check(S, Primes, Traces, Max);
   require bool : message;

   f := not NoTwoDescent;

   return InternalEllipticCurveSearch(S, Effort : All, Full:=Full, Max:=Max,
                                      Primes:=Primes, Traces:=Traces, Flags:=[f,f,f],
                                      ReturnExtraCurves:=ReturnExtraCurves);
end intrinsic;


/*************************************************************************
// Examples

SetVerbose("ECSearch", 3);

F, ZF, w := nf(x^2 - 44); // 929
for N in IdealsUpTo(100, F) do
   "\n\nConductor N =", N;
   EllipticCurveSearch(N, 400 : Max:=1);
end for;

F, ZF, w := nf(x^2 - 23);
N := ideal< ZF | [ RationalField() | 42, 0 ], [ RationalField() | 9, 3 ] >;
EllipticCurveSearch(N, 10 : Full, Max:=2);

F, ZF, w := nf(x^2 -x - 23);
E := EllipticCurve([w, w, 0, -1156096*w - 4996445, 1481037671*w + 6400786196]);
N := Conductor(E);
EllipticCurveSearch(N, 100); // 4 isogeny classes

F, ZF, w := nf(x^2 - x - 52);
N := ideal< ZF | 10, 5*w >; 
EllipticCurveSearch(N, 1600 : Max:=4); // 4 isogeny classes 
// the last is very awkward, with I23, I9 and I5 reduction!
E := EllipticCurve( [1, -1, 0, -148410*w - 998564, -83632855*w - 562716652] );
delta := 7366625375*w - 56932346500;

**************************************************************************/

