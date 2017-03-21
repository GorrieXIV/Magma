freeze;

///////////////////////////////////////////////////////////////////////
// Finding elliptic curves with given conductors
// over rational function fields
//
// Steve Donnelly 
// October 2012
//
///////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////
// Elementary functions

function PolynomialsUpToDegree(P, d : Monic:=false)
   if Monic then
      pols := [P.1^d];
      d -:= 1;
   else
      pols := [P!0];
   end if;
   for i := 0 to d do
      xi := P.1^i;
      pols := [f + c*xi : f in pols, c in BaseRing(P)];
   end for;
   if Monic then
      if d gt 0 then
         pols := PolynomialsUpToDegree(P, d : Monic) cat pols;
      elif d eq 0 then
         pols := [P| 1] cat pols;
      end if;
   end if;
   return pols;
end function;

function ProductsUpToDegree(S, d)
   S := {p : p in S | Degree(p) le d};
   L := S;
   repeat
      n := #L;
      L join:= {l*p : l in L, p in S 
                    | Degree(l) + Degree(p) le d};
   until n eq #L; // stable
   return Sort(Setseq(L));
end function;

function SUnitsModPowers(S, n : nonzero:=false)
   R := Universe(S);
   ff := BaseRing(R);
   m := GCD(n, #ff-1);
   elts := [R| 1];
   if m gt 1 then
      g := PrimitiveElement(ff);
      elts cat:= [R| g^i : i in [1..m-1]];
   end if;
   exps := nonzero select [1..n] else [0..n-1];
   for s in S do
      elts := [e*s^i : e in elts, i in exps];
   end for;
   return elts;
end function;

function CasselsTatePairingMatrix(basis)
   M := MatrixRing(GF(2), #basis) ! 0;
   for i in [1..#basis], j in [1..i-1] do
      ct := CasselsTatePairing(basis[i], basis[j]);
      M[i,j] := ct;
      M[j,i] := ct;
   end for;
   return M;
end function;

///////////////////////////////////////////////////////////////////////
// EC functions

// Return elt for finite part of divisor
function _Conductor(E)
   R := Integers(BaseRing(E));
   return &* [R| t[1]^t[2] : t in Conductor(E) | t[1] in R];
end function;

// Lame attempt to saturate
// TO DO: Saturation routine

function try_to_saturate(basis, n)
   if #basis eq 0 or n lt 2 then
      return basis;
   end if;
   divpts := [Universe(basis)| ];
   for p in PrimesUpTo(n) do
      combs := [basis[1]];
      for b in basis[2..#basis] do 
         mults := [n*b : n in [1..p-1]];
         combs := [b] cat combs cat [c + nb : c in combs, nb in mults];
      end for;
      assert #combs eq (p^#basis - 1) / (p - 1);
      divpts cat:= &cat [DivisionPoints(pt,p) : pt in combs];
      if #divpts ne 0 then
         basis := IndependentGenerators(basis cat divpts);
      end if;
   end for;
   return basis;
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

procedure GetEllipticCurves(k, ~ecs, ~es, ~ts);
   d := Degree(k);
   bool, data := IsDefined(ecs, d);
   if bool then
      k1, es, ts := Explode(data);
      Embed(k1, k);
      es := [ChangeRing(E, k) : E in es];
   else
      es, ts := EllipticCurves(k);
      ecs[d] := <k, es, ts>;
   end if;
end procedure;

///////////////////////////////////////////////////////////////////////
// Main routine

function _EllipticCurveSearch(conductors, Effort : All:=false,
                                     Full:=0, Max:=Infinity(), 
                                     Primes:=[], Traces:=[], 
                                     ReturnExtraCurves:=false) // option not documented
   time00 := Cputime();

// TO DO: decide input type
ZF := Integers(Parent(Rep(conductors)[1,1]));
conductors := {ZF| &* [ZF| t[1]^t[2] : t in N | t[1] in ZF] : N in conductors};

   ZF := Universe(conductors);
   F  := FieldOfFractions(ZF);
   ff := BaseRing(ZF);
   p := #ff;

   error if Characteristic(F) le 3, "The characteristic must be at least 5";

   Nfacts := [Factorization(N) : N in conductors];
   Ss := {ZF| t[1] : t in x, x in Nfacts};
   S := Sort(Setseq(Ss));
   assert forall{P : P in S | IsMonic(P) and IsIrreducible(P)};

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
      ChangeUniverse(~Primes, ZF);
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
         //assert _Conductor(E) notin conductors;
         return false; // impossible for all conductors
      end if;
   end function;
 
   small_primes := &cat [Setseq(AllIrreduciblePolynomials(ff, i)) : i in [1]];
   small_primes := [ZF| ];
   i := 0;
   while #small_primes lt 50 do
      i +:= 1;
      small_primes cat:= [f : f in Setseq(AllIrreduciblePolynomials(ff, i))
                            | forall{N: N in conductors | GCD(N,f) eq 1} ];
   end while;

   procedure check_twists(E, twists, ~curves, ~traces, ~matched, ~done : search:="")

      assert forall{c : c in Coefficients(E) | c in ZF};

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
            and conductor_might_be_wanted(Ed,j) and conductor_is_wanted(_Conductor(Ed))
         then
            Ed := MinimalModel(Ed);
            disc := Discriminant(Ed);
            c := Coefficients(Ed);
            vprintf ECSearch, 2: "\n";
            vprintf ECSearch: "Found curve with discriminant %o and j = %o\n", disc, j;
            vprintf ECSearch: "Coefficients: [%o, %o, %o, %o, %o]\n", c[1],c[2],c[3],c[4],c[5];
            vprintf ECSearch, 2: "Twisting element: %o\n", F!d;

            Append(~curves, Ed);
            new_curves := [Ed];

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

   //////////////////////////////////////////////////////////////    
   // Start collecting curves, using various techniques
   // Call 'check_twists' to decide when done

   done := false;
   Es := [];

   // List reps mod squares, to be used for quadratic twisting
   F2Selts := SUnitsModPowers(Ss, 2);
    
   // List the candidate discriminants delta
   deltas := SUnitsModPowers(S, 6 : nonzero);
   pmdeltas := Seqset(deltas);

   vprintf ECSearch: "\n%o candidates for discriminants (up to 6th powers)\n", 2*#deltas;

   if use_traces then
      ecs := AssociativeArray();

      // Sieve to cut down the possible discriminants for each newform,
      // using that 1728*d = c4^3 - c6^2 and j*d = c4^3
      num_primes := 0;
      stable := false;
      while not stable and num_primes lt #Primes do
         num_primes := Min(num_primes + 20, #Primes);
         stable := true;
         inds := [1..num_primes];
         resmaps := [* 0 : i in [1..#Primes] *];
         res_jts := [* 0 : i in [1..#Primes] *];
         squares := [* 0 : i in [1..#Primes] *];
         cubes   := [* 0 : i in [1..#Primes] *];
         vprintf ECSearch, 2: "Setting up to sieve the deltas:\n";
         vtime ECSearch, 2:
         for i in inds do 
            k, res := ResidueClassField(Primes[i]);
            vprintf ECSearch, 2: "%o ", Degree(k);
            GetEllipticCurves(k, ~ecs, ~Ek, ~tk);
            res_jts[i] := [<jInvariant(Ek[i]), tk[i]> : i in [1..#Ek]];
            resmaps[i] := res;
            squares[i] := {x^2 : x in k};
            cubes[i]   := {x^3 : x in k};
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
                  vprintf ECSearch, 2: "%o: --, ", Degree(Codomain(resmaps[r]));
                  continue r;
               end if;
               sieve := {ZF| d : d in sieve | (not use_s or rd in sieve_s) and
                                              (not use_c or rd in sieve_c)
                                              where rd is res(d) };
               Append(~sh, #sieve);
               vprintf ECSearch, 2: "%o: %o, ", Degree(Codomain(resmaps[r])), #sieve;
            end for; // r
            // the sieved set is always closed under inverse (mod 6th powers)
            stable and:= #sieve le 2 or #sh gt 10 and sh[#sh-10] eq sh[#sh];
            if not stable and num_primes lt #Primes then
               break t; // set up more Primes
            end if;
            Append(~pmdeltas_for_traces, sieve);
         end for; // t
      end while;
      assert #pmdeltas_for_traces eq #Traces;

      for t := 1 to #Traces do
         if #pmdeltas_for_traces[t] eq 0 then
            print "WARNING: No elliptic curve has the specified 'Traces':";
            print Traces[t];
         end if;
      end for;
      goodt := [t : t in [1..#Traces] | #pmdeltas_for_traces[t] gt 0];
      Traces := [Traces[t] : t in goodt];
      pmdeltas_for_traces := [pmdeltas_for_traces[t] : t in goodt];

      possible_pmdeltas := &join pmdeltas_for_traces;
      pmdeltas := Setseq(possible_pmdeltas);

      delete ecs;

      vprintf ECSearch: "After sieving, %o candidate discriminants: %o\n", 
                         #pmdeltas, [#x : x in pmdeltas_for_traces];

      if #Traces eq 0 then
         return [];
      end if;
   end if; // use_traces

   // TO DO: Sort deltas (try the more likely ones first)

   vprintf ECSearch: "Preliminary phase took %os\n", Cputime(time00);

   // Initialize the auxiliary elliptic curves corresponding to deltas
   // (we want to only check things once, not for every B in Bs, below)
   auxil := AssociativeArray(pmdeltas);
   rankbounds := AssociativeArray(pmdeltas);
   tdct := AssociativeArray(pmdeltas);     // tuple <td, tdm> is assigned iff done CT
   points := AssociativeArray(pmdeltas);
   for d in pmdeltas do 
      A := EllipticCurve([F| 0, -1728*d]);
      auxil[d] := A;
      rankbounds[d] := Infinity();
      points[d] := [A(F)| ];
   end for;
   checked_Es := {PowerSequence(F)| }; // (could make it an array on deltas)

   procedure include(~points, d, pts)
      if #pts gt 0 then
         points[d] cat:= [Universe(points[d]) | pt : pt in pts];
         points[d] := IndependentGenerators(points[d]);
      end if;
   end procedure;

   // Run the searches with increasing amount of effort, alternating between the
   // candidate discriminants.
   // At step B, currently the effort is
   //    MW search: #MWnums = p^((B+2) div 2), #MWdens <=  p^(B div 4) * (const*B)^#S

   Bound := Ceiling(Maximum(1, Effort));
   if Full then
      Bs := [Bound];
   else
      Bs := [Min(2, Bound) .. Bound];
   end if;

   for B in Bs do 
if IsEven(B) and p lt 10 then continue; end if; // TO DO
      vprintf ECSearch, 2: "\n";
      vprintf ECSearch: "Effort = %o: ", B;

      timeB := Cputime();

      // In MW search, x values are x = X/Z^2 for X in MWnums, Z in MWdens.
      // Include more nums when B is odd, and more dens with B is even.
      MWdens := Setseq(Seqset(ProductsUpToDegree(S, 2*(B div 2))) join
                       Seqset(PolynomialsUpToDegree(ZF, B div 4 : Monic)));
      MWnums := PolynomialsUpToDegree(ZF, (B+1) div 2);
      MWdens6 := [x^6 : x in MWdens];
      MWnums3 := [x^3 : x in MWnums];
// "MWdens:"; MWdens;
// "MWnums:"; MWnums;

      for d in pmdeltas do
            if use_traces and d notin possible_pmdeltas then
               continue;
            end if;

            BB := B;
            vprintf ECSearch, 2: "\n%o%o ", str, &*[Strings()| " " : i in [#str..40]]
                                  where str is "["*Sprint(BB)*"]  "*Sprint(F!d);

            // Decide whether and how to use TwoDescent:
            // for searching or for identifying rank zero curves
            TD := p^BB gt 50000;
            TDR := false;// reduce the 2-coverings (and search on them)
            CT := TDR;  // use Cassels-Tate

            // Choose bounds so that search time is close to O(BB)
            // The search routine spends time setting up the filter, 
            // so there's no point calling it with a small bound.
            MWB := Ceiling( 10000*p^BB );
            TDB := Ceiling( Sqrt(MWB) );
            // Choose denominators: the MWdenoms are ideals which could occur in 
            // denominators of the point(s) we are looking for, because the MW search 
            // targets finding these points directly rather than just finding generators.
            // TO DO: spend more effort on the most likely denominators?
            // The TDdenoms are just arbitrary small rational integers, no clever choices. 
            // TO DO: for larger degree fields, shouldn't only take integers.
            // TO DO: could predict congruences on x-coords of points on 2-coverings?
            TDdenoms := AllIrreduciblePolynomials(ff, 1);

            // Mordell-Weil search and/or 2-descent search, and (always) check torsion points
            A := auxil[d];
            TA, mTA := TorsionSubgroup(A);
            torsA := [t@mTA : t in TA];

            if TD then   // TO DO: 2-torsion case (TwoSelmerGroup or TwoIsogenySelmerGroup)

               if rankbounds[d] eq Infinity() and IsOdd(#TA) then
                  vprintf ECSearch, 2: "TD:";
                  time0 := Cputime(); 
                  rankbounds[d] := Ilog(2, #TwoSelmerGroup(A) div #TwoTorsionSubgroup(A));
                  assert #points[d] le rankbounds[d];
                  vprintf ECSearch, 2: "%o RANK<=%o ", Cputime(time0), rankbounds[d];
               end if;

               done_ct, tup := IsDefined(tdct, d);
               if done_ct then
                  td, tdm := Explode(tup);
               end if;

               // Reduction is needed for searching, and for Cassels-Tate
               // (Note: results are cached by TwoDescent)
               if TDR and not done_ct and #points[d] lt rankbounds[d] then
                    done_tdr := true; // just a check
                    vprintf ECSearch, 2: "TDR:";
                    time0 := Cputime(); 
                    td, tdm, tdsel := TwoDescent(A); // TO DO: tdsel
                    tds := [Domain(tdsel) | q @@ tdsel : q in td];
                    vprintf ECSearch, 2: "%o ", Cputime(time0);
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
                  else
                     vprintf ECSearch, 2: "%o ", Cputime(time0);
                  end if;
               end if;

               // Spend more effort if rank >= 2 (the hard ones are almost always rank 2, 
               // so we want to spend a positive proportion of total time on these cases)
               // TO DO: could make this even more if we could get rid of the ones with Sha[4]
               if CT and rankbounds[d] ge 2 then
                  // multiply effort by some factor (except don't bother to use more denominators)
                  e := 2;
                  BB +:= e;
                  MWB := Ceiling( MWB * e );
                  TDB := Ceiling( TDB * Sqrt(e) );
                end if;

               // Search on 2-coverings
               if TDR and #points[d] lt rankbounds[d] then
                  // TO DO: Search all 2-coverings except those in the preimage of <points[d]>
                  // Note: it's not a good idea to only search coset representatives for TD/<points[d]>
                  if #td gt 0 and #points[d] lt rankbounds[d] then
                     time0 := Cputime();
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

            // Just a naive search currently

            nptsd := #points[d];

            if #points[d] lt rankbounds[d] then
               time0 := Cputime();

               for i in [1..#MWdens] do
                  Z  := MWdens[i];
                  Z6 := MWdens6[i];
                  for j in [1..#MWnums] do
                     // Note: does not save time to check GCD(Z,X) here
                     Y2 := MWnums3[j] - 1728*d*Z6;
                     bool, Y := IsSquare(Y2);
                     if bool then
                        X := MWnums[j];
                        if GCD(Z,X) ne 1 then 
                           continue; 
                        end if;
                        include(~points, d, {A![X/Z^2,Y/Z^3]});
                        assert #points[d] le rankbounds[d];
                        if #points[d] eq rankbounds[d] then
                           break;
                        end if;
                     end if;
                  end for;
               end for;

               vprintf ECSearch, 2: "MW:%o ", Cputime(time0);
            end if;
              
            // Saturate?
            if #points[d] gt nptsd or IsSquare(BB) and IsPrime(Isqrt(BB)) then 
               points[d] := try_to_saturate(points[d], 1 + Isqrt(BB));
            end if;

            // Check whether points give us elliptic curves with desired conductor
            basis := points[d];
            r := #basis; 
            if r eq 0 then
               combs := torsA;
            else
               // Test combinations of generators up to some bound
               // (only one of each pair +-pt, since we check twists by -1)
               // Let b = bound on coeffs of combinations of the basis.
               // These have log height O(R*b^2), so cost of listing them is O(R*b^(2+r))
               R := Regulator(basis); 
               assert Abs(R) gt 0;
               vprintf ECSearch, 2: "REG=%o ", R;
               b := Ceiling( (10*p^BB/R) ^ (1/(2+r)) );
               if b gt 10 then // large multiples are probably a waste of time, so cut down a bit
                  b := 10 + Round((b-10)^(1/2));
               elif b lt Min(4, BB) then
                  b := Min(4, BB);
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
             //if 0 in [X,Y,Z] then // TO DO
               if Z eq 0 then
                  continue;
               end if;
               assert Z eq 1;
               Z := Denominator(X);
               bool, Z := IsSquare(Z); assert bool;
               if forall{t : t in Factorization(Z) | t[1] in S} then
                  // untwist by Z, so disc(E) contains Z^6 instead of Z^12
                  assert Denominator(Y) eq Z^3 and Numerator(Y) eq Y*Z^3;
                  E := EllipticCurve([F| -27*Numerator(X), 54*Numerator(Y)]);
assert ZF!Discriminant(E) mod Z^6 eq 0;
                  nchecked := #checked_Es;
                  Include(~checked_Es, Coefficients(E));
                  if #checked_Es gt nchecked then // E has not been checked
                     vprintf ECSearch, 2: "E ";
//time0 := Cputime();
                     check_twists(E, F2Selts, ~Es, ~Traces, ~matched, ~done : search:="MW");
//vprintf ECSearch, 2: ": %o ", Cputime(time0);
                     if done then
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

            if B eq Maximum(Bs) then
               // Conserve memory, since these won't be used again
               delete A, TA, mTA, torsA;
               if assigned td then delete td; end if;
               if assigned tdm then delete tdm; end if;
               Remove(~auxil, d);
               Remove(~tdct, d);
               Remove(~points, d);
            end if;

            if TD then
               mark_sweep;
            end if;

      end for; // d

      vprintf ECSearch: "\nEffort = %o took %os ", B, Cputime(timeB);
      vprintf ECSearch: "[memory usage %oM]\n", GetMemoryUsage() div 10^6;

   end for; // B in Bs

   if ReturnExtraCurves then 
      XEs := []; 
      for c in checked_Es do 
         E := EllipticCurve(c);
         if true or jInvariant(E) notin F then
            Append(~XEs, E);
         end if;
      end for;
      return Es, XEs;
   else
      return Es;
   end if;

end function;

/////////////////////////////////////////////////////////////////////////////////////////
// Interface
// TO DO: exception handling

intrinsic EllipticCurveSearch(N::SeqEnum[Tup], Effort::RngIntElt 
                             : Full:=0, Max:=Infinity(), 
                               Primes:=[], Traces:=[]) 
       -> SeqEnum
{Search for elliptic curves with conductor(s) matching the first argument.
 This is a search routine only: it does not necessarily return all such curves!
 'Effort' controls the length of the search (running time is roughly linear in this)}

  return _EllipticCurveSearch({N}, Effort : 
                              Full:=Full, Max:=Max, Primes:=Primes, Traces:=Traces);
end intrinsic;

intrinsic EllipticCurveSearch(N::Setq, Effort::RngIntElt 
                             : Full:=0, Max:=Infinity(), 
                               Primes:=[], Traces:=[]) 
       -> SeqEnum
{"} // "

  return _EllipticCurveSearch(N, Effort : 
                              Full:=Full, Max:=Max, Primes:=Primes, Traces:=Traces);
end intrinsic;


/****************************************************************************************
// Examples

SetVerbose("ECSearch", 3);

p := 5;
F := FunctionField(GF(p)); t := F.1;
ZF := Integers(F);

E := EllipticCurve([0, t^2, 0, 0, 1]);
LocalInformation(E); 
N := Conductor(E);

primes := &cat [[ZF| p : p in AllIrreduciblePolynomials(BaseRing(F), d)] : d in [1..2]];
primes := [p : p in primes | not exists{t : t in N | p eq t[1]}];
traces := [TraceOfFrobenius(E, p) : p in primes]; traces;

EllipticCurveSearch({N}, 10 : Primes:=primes, Traces:=[traces]);

****************************************************************************************/

