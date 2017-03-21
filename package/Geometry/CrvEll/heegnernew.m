freeze;

          /*******************************
          *                              *
          *    HEEGNER POINTS OVER       *
          *       NUMBER FIELDS          *
          *                              *
          *   Steve Donnelly, May 2006   *
          *                              *
          *                              *
          ********************************/

/**********************
  
        *** PLEASE LOG ALL CHANGES HERE ***

                                  **********************/

/* TO DO
    * Speed up the sanity check in the case where the degree is less than the class number
    * Use isogenies to help deal with difficult cases.
      (The most difficult curves usually seem to have them!)
    * Recognising Polynomials:
      Apparently we are mis-recognising polynomials and they are getting caught
      by the sanity check ... they are supposed to be caught earlier!
      Example: HeegnerPoints(E11,-3500 : ReturnPoint:=false);
  BUGS
    > E := EllipticCurve("709a1");
    > HeegnerPoints(E, -7*5^2 : ReturnPoint);
      ... fails assertion (inverse_pairs or mock), also fails further down
    > E := EllipticCurve("389a1");
    > HeegnerPoints(E, -7*5^2 : ReturnPoint);
    > E := EllipticCurve("718b1");
    > HeegnerPoints(E, -7*5^2 : ReturnPoint);
*/

function myEllipticExponential(E,cc)  // return 0 if answer is the point at infinity
  // check if cc is (nearly) a lattice point
  if Norm(cc) le 10^-50 then return 0; end if;
  pi1,pi2 := Explode(Eltseq(Periods(E : Precision:=Precision(cc) )));
  A := Re(pi1); B := Re(pi2); C := Im(pi1); D := Im(pi2);
  det := A*D-B*C;  assert Abs(det) ge 10^-20;
  m := (D*Re(cc)-B*Im(cc))/det;  n := (-C*Re(cc)+A*Im(cc))/det;
  if Abs(m-Round(m)) lt 10^-50 and Abs(n-Round(n)) lt 10^-50 then return 0; end if;
  return EllipticExponential(E,cc); 
end function;

// return a polynomial over Z that approximates an integral multiple 
// of the given monic polynomial over a real (or complex) field. 
// If there is no "especially good" approximation, returns false
// (indicating that you probably need more precision to identify
// the desired answer), otherwise returns true and the poly.
// The 'safetymargin' is defined to be such that the heuristic 
// probability of returning an incorrect polynomial is at most 
//                   1/10^safetymargin 
// (assuming the given polynomial is accurate to precision 'prec')

function recognise_polynomial_over_Q(pol_over_R : safetymargin:="default", prec:="default", verbose:=false) 
//    -> boolean, pol_over_Q 

     error if not IsMonic(pol_over_R), 
       "The function 'recognise_polynomial_over_Q' is only for monic polynomials";
     d := Degree(pol_over_R);
     if prec cmpeq "default" then 
        prec := Precision(BaseRing(pol_over_R));
        if ISA( Type(prec), Infty) then 
           prec := Min([ RelativePrecision(c) : c in Coefficients(pol_over_R) ]); end if;
        prec -:= 10; // assume there was at most this many digits round-off error in computing pol_over_R
     end if;
     error if prec le 0, "Not enough precision in 'recognise_polynomial_over_Q'";
     Qx := PolynomialRing(Rationals());  
     x := Qx.1;
 
     // Method 1  --  Standard LLL approach
     if d ne 1 then
        // for d = 1, might as well use Method 2
        coeffs := [Real(c) : c in Coefficients(pol_over_R)];
        if safetymargin cmpeq "default" then safetymargin := 50;  end if;
        C := Max([ Ceiling(Log(10, Max(c,1))) : c in coeffs ]);
        if prec - C ge 10 then  // otherwise go to Method 2
          B := 10^(prec - C);
          L := B*IdentityMatrix(Integers(), d+1);
          L[1] := Vector(Reverse([-Round(c*B) : c in coeffs]));
          L[1][1] := 1;
          _,b := LLL(L : Delta:=0.99);
          if b[1][1] ne 0 and Max([Abs(bi) : bi in Eltseq(b)])^(d+1) le B^d/10^safetymargin then
             // accept the answer, since the probability of there being 
             // a random answer satisfying this is 1/10^safetymargin
             if verbose then print "Recognised polynomial using the LLL method"; end if;
             pol := Qx! Reverse(Eltseq(b[1]));
             return true, ExactQuotient(pol, Content(pol));
          end if;
        end if;
     end if;

     // Method 2
     // Try to recognise the coefficients as rationals 
     // one after another, starting with the highest order term.
     // (This method could be useful when this coefficient is simpler
     // than the others, which sometimes happens).
     // Allow at most numdigits in the numerator and denominator,
     // and multiply through by the denominator at each step.
     numdigits := prec div 2 - 20;  
     for i := 1 to d do
       ci := BestApproximation(RealField(2*prec)!Real(Coefficient(pol_over_R,d-i)),10^numdigits); 
       // (The reason for putting in the funny coercion is that BestApproximation 
       // once complained about not enough precision.)
       if Ilog(10,Denominator(ci)) ge numdigits-10 then 
          // might be bogus, so start again with more precision
          if verbose then print "Can't recognise coefficients, need to increase precision."; end if;
          return false, _; end if;
       pol_over_R := pol_over_R*Denominator(ci); 
       if &and[Abs(Round(Real(c))-c) lt 10^-20 : c in Coefficients(pol_over_R)] then 
          pol := &+[ x^i*Round(Real(Coefficient(pol_over_R,i))) : i in [0..d]]; 
          pol := ExactQuotient(pol, Content(pol)); 
          if verbose then print "Recognised polynomial using the naive method"; end if;
          return true, pol;
       end if;
     end for;
end function;


Precision_intrinsic:=Precision;
intrinsic HeegnerPoints(E::CrvEll, D::RngIntElt : Precision:=100, ReturnPoint:=false, KolyvaginPrime:=0 ) 
       -> Tup, PtEll
{Given an elliptic curve E over Q, and a negative integer D 
(which must be a fundamental discriminant times a square), 
the function returns a polynomial whose roots are the x-coordinates of the Heegner points
on E associated to D.  Two objects are returned: 
firstly a tuple containing the polynomial and a multiplicity,
and secondly one of the Heegner points}
 
  require D lt 0 : "The given integer D must be negative";
  require IsSquare(Integers(4*Conductor(E))!D):
         "The discriminant D does not satisfy the Heegner hypothesis, " *
         "that D should be a square modulo 4*N(E)";

  Qx := PolynomialRing(Rationals()); x := Qx.1;
  
  p := KolyvaginPrime;  koly := p cmpne 0;  
  
  eqn_of_order := IsEven(D) select x^2 - D div 4
                             else  x^2 - x - (D-1) div 4;
  K := NumberField(eqn_of_order);
  O := EquationOrder(K);
  OK := Integers(K);
  disc := Discriminant(OK);
  d := IsOdd(disc) select disc else disc div 4;
  _,n := IsSquare(D div disc);

  require IsDivisibleBy(D, disc) : "The given integer $D$ should be a discriminant times a square";
//  require GCD( Conductor(E), n) eq 1 : "Not implemented in this case; the conductor of the order",
//         "given by x^2-D must be coprime to the conductor of E.";
  mock := not IsFundamental(D) and not disc in HeegnerDiscriminants(E,disc,disc);
  if mock then print "WARNING: The code is not guaranteed to work for \"mock Heegner points\" " 
                            * "(especially when ReturnPoint is set to true)."; end if;

  if not IsMinimalModel(E) then 
     Emin, E_to_Emin := MinimalModel(E);
     tup, Hpt := HeegnerPoints(Emin, D : KolyvaginPrime:=p,ReturnPoint:=ReturnPoint,Precision:=Precision);
     map_eqns := DefiningEquations(E_to_Emin); assert map_eqns[3] eq E.3;
     pol_E := Evaluate(tup[1], Evaluate(map_eqns[1], [x,0,1]) );
     if ReturnPoint then
       Hpt_E := Hpt @@ E_to_Emin; assert Evaluate(pol_E, Hpt_E[1]) eq 0;
       return <pol_E/LeadingCoefficient(pol_E), tup[2]>, Hpt_E;
     else 
       return <pol_E/LeadingCoefficient(pol_E), tup[2]>, _;
     end if;
  end if;

  // When rank of E(Q) is  0, the image of (cusp_inf - cusp_0) in E(Q) might be nontrivial 
  rank, LE1 := AnalyticRank(E);
  if rank eq 0 then 
     TT_frac := BestApproximation( LE1/RealPeriod(E), 50);
     TT_frac -:= Floor(TT_frac);  assert Denominator(TT_frac) le 10; // Q-rational torsion point!
     vprintf Heegner,2: "The image of (cusp_infinity - cusp_zero) is %o * Omega\n", TT_frac;
  else 
     TT_frac := 0; 
  end if;

  if koly then 
     require TT_frac eq 0 : "The Kolyvagin option is not yet implemented for the case",
                            "where the image of (cusp_infinity - cusp_zero) is nontrivial";
     require &and[ not IsSquare(GF(pp)! d) : pp in PrimeDivisors(n) ] : "Kolyvagin's hypotheses" *
           " are not satisfied: primes dividing n should be inert in the quadratic field";
     require &and[ (pp+1) mod p eq 0 : pp in PrimeDivisors(n) ] : "Kolyvagin's hypotheses are" *
           " not satisfied: primes dividing n should be congruent to -1 modulo KolyvaginPrime";
     HF := HeegnerForms(E,D : Use_wQ:=false);
     HFsafe := HeegnerForms(E,D : Use_wQ:=false, UseAtkinLehner:=false);
     assert &and[ x[2] eq 1 and x[3] eq E!0 : x in HFsafe];
     Hforms_safe := [x[1] : x in HFsafe];
  else 
     HF := HeegnerForms(E,D : Use_wQ:=false);  // TO DO: get wQ to work!
  end if;
  Hforms := [x[1] : x in HF];
  muls := [x[2] : x in HF]; 
  torspts := [x[3] : x in HF];
  multiplicity := Abs(muls[1]);
  require &and[ Abs(mul) eq multiplicity : mul in muls ]: 
          "Multiplicities are not all the same size";
  muls := [mul div multiplicity : mul in muls];
  class_number := #Hforms * multiplicity;

  vprintf Heegner,1: "Heegner forms are %o\n", Hforms;
  Cl, fromCl := RingClassGroup(O);
  sqrtD := O! Roots(x^2-D, K)[1][1];
  if koly then 
     require #Cl gt 1 and #Invariants(Cl) eq 1: "Kolyvagin is only implemented in the cyclic case";
     // Establish a bijection between Heegner forms and the ring class group.
     // (Use the safe forms to get the bijection, and then apply it to the others, 
     //  under the assumption that HeegnerForms returns them in consistent order).
     Hforms_in_Cl := [];
     for hf in Hforms_safe do
        A,B,C := Explode(Eltseq(hf));  assert B^2-4*A*C eq D and GCD(n,A) eq 1;
        tau := (-B - sqrtD)/(2*A);
        cl := ideal< O | [AA, AA*tau] > @@ fromCl where AA is A*Modinv(A,n);
        Append( ~Hforms_in_Cl, Eltseq(cl));
     end for;
     Hforms_in_Cl_inds := [ cl[1] : cl in Hforms_in_Cl ];
     assert #Hforms eq #Cl and SequenceToSet(Hforms_in_Cl_inds) eq {0..#Cl-1};
     Sort( ~Hforms_in_Cl_inds, ~permut);
     Hforms := [ Hforms[p] : p in Eltseq(permut) ];
     Hforms_safe := [ Hforms_safe[p] : p in Eltseq(permut) ];
Hforms := Hforms_safe; muls := [1 : hf in HF]; torspts := [E!0 : hf in HF];
  end if;
 
  // THE MAIN COMPUTATION
  prec := Precision;
  fib := -1; 
  recognisedpol := false; 
  while not recognisedpol do
     // loop, increasing precision as much as necessary
     fib +:= 1;
     
     // COMPUTE IMAGES ON E OVER C 
     prec +:= Precision*Fibonacci(fib);
     C := ComplexField(prec);
     tors := [EllipticLogarithm(pt : Precision:=prec) : pt in torspts];
     vprintf Heegner,1: "Computing ModularParametrization to precision %o\n", prec;
     Hpts := ModularParametrization(E,Hforms : Precision:=prec);
     Hpts := [muls[i]*(Hpts[i]+tors[i]) : i in [1..#HF]];
     if TT_frac ne 0 then 
        // The Gal(H/Q) conjugates of P in Hpts include TT - P, so
        // if these have different x-coordinates then we need to throw them in.
        TT := TT_frac*RealPeriod(E : Precision:=prec);
        if &and[ Abs( TT-Hpts[1] - otherHpt) gt 10^-20 
               : otherHpt in Hpts[2..#Hpts] cat [-Hpt : Hpt in Hpts] ] then
           Hpts cat:= [ TT-Hpt : Hpt in Hpts ];
        end if;
     elif koly then  // note koly currently assumes TT_frac eq 0
        // Apply a 'modified Kolyvagin operator',
	// namely trace down to the field of degree p in K_n/K,
        // then apply the sum of i*sigma^i for i = 1 to p-1,
	// where <sigma> = Gal(K_n/K) = Z/(l+1) = Z/#Cl
        Hpts_traces := [ &+[ Hpts[k+p*j] : j in [0 .. #Cl div p - 1]] : k in [1..p]];  
        Hpts := [ &+[ i*Hpts_traces[1 + (i+k) mod p] : i in [1..p]] : k in [1..p]];
 Hpts := Hpts_traces;
 print "Kolyvagin Hpts are ", ChangeUniverse(Hpts,ComplexField(10));
     end if;
     HptsinEC := [* myEllipticExponential(E,u) : u in Hpts *];
     // these "conjugates" should all be the point at infinity if any are...
     if &and[ hpt cmpeq 0 : hpt in HptsinEC ] then 
        return <1/x, #HptsinEC>, E!0; 
     elif &or[ hpt cmpeq 0 : hpt in HptsinEC ] then 
        continue; end if; 
     
     // Sometimes these values are repeated (ie. several points on X_0(n)
     // map to the same point on E), so take each only once:
     HptsinECgrouped := [ [HptsinEC[1]] ];
     inverse_pairs := false;  // will be true if any two of the images on E form an inverse pair
     for j in [2..#HptsinEC] do
        pt  := HptsinEC[j];
        for i in [1..#HptsinECgrouped] do 
            pt1 := HptsinECgrouped[i][1];
            if Abs(pt[1]-pt1[1]) lt 10^-50 then 
              if Abs(pt[2]-pt1[2]) lt 10^-50 then
                 // pt is within 10^-20 of pt1 (and the other points in the ith group)
                 Append(~HptsinECgrouped[i], pt);
                 break;
              else inverse_pairs := true; end if;
            end if;
        if i eq #HptsinECgrouped then Append(~HptsinECgrouped, [pt] ); end if;
        end for;
     end for;
     numrepeats := #HptsinECgrouped[1];
     if &and[#HptsinECgrouped[i] eq numrepeats : i in [1..#HptsinECgrouped]] then
        // each point occurs the same number of times, as it should
        if numrepeats gt 1 and not koly then
           vprintf Heegner,1: 
           "Each fibre of the modular parametrisation X_0(n) -> E contains 
            %o distinct conjugate Heegner points\n", numrepeats;
        end if;
        multiplicity *:= numrepeats;
        HptsinECreps := [HptsinECgrouped[i][1] : i in [1..#HptsinECgrouped]];
     else
        print "WARNING: Something seems to have gone wrong while trying to identify repeats";
        HptsinECreps := HptsinEC;
     end if;

     Cz := PolynomialRing(C); z:=Cz.1;
     if inverse_pairs then 
        xcoords := [];
        for pt in HptsinECreps do 
          if &and[ Abs(pt[1]-xc) gt 10^-20 : xc in xcoords ]
	   then Append( ~xcoords, pt[1]); end if;
        end for;
        assert 2*#xcoords eq #HptsinECreps;
     else
        xcoords := [pt[1] : pt in HptsinECreps];
     end if;
     poloverC := &*[z-xc : xc in xcoords];
     vprintf Heegner,3: "poloverC is approx %o\n",
			ChangeRing(poloverC, ComplexField(10));
     d := Degree(poloverC); 
     
     // RECOGNISING THE POLYNOMIAL 
     vprintf Heegner,2: "Computed polynomial (deg %o) over C; "*
                "trying to recognise the coefficients in Q\n",d;
     coeff_prec := Min([prec] cat [ Floor(Log(10, Abs(Re(c)/Im(c)) )) : c in Coefficients(poloverC)[1..d] 
                                                                      | Abs(c) gt 10^-10 and Im(c) ne 0 ]); 
//"prec =", prec, "coeff_prec =", coeff_prec;
     recognisedpol, pol := recognise_polynomial_over_Q(poloverC : prec:=coeff_prec-10, safetymargin:= "default",
                                                                  verbose := GetVerbose("Heegner") ge 1);
                        // safety margin is "empirical, based on small conductor" (ie pretty arbitrary)
   end while; // not recognisedpol

   if 2^Ilog(2,multiplicity) ne multiplicity then 
      vprintf Heegner, 2: "Surprising example: multiplicity is %o\n", multiplicity; end if;
   require IsIrreducible(pol) : "Something is wrong: obtained non-irreducible polynomial";

   // sanity check: Check that pol has the right splitting at small primes
   sane := true;
   poldisc := Integers()! (LeadingCoefficient(pol)*Discriminant(pol));
   // TO DO: this dominates the time!! 
   // Better not compute it at all,
   // instead check for repeated factors at each prime ...

   if multiplicity eq 1 and not inverse_pairs and not koly then
     vprint Heegner,1: 
       "Heuristic check: that the polynomial has the correct "*
       "splitting at p for the first 100 primes p that don't divide "*
       "its discriminant and that split in the quadratic field.";
     numprimes := 0;
     pp := 2;
     while numprimes lt 100 do 
       pp := NextPrime(pp); 
       if LegendreSymbol(D,pp) ne 1 then continue; end if;
       if IsDivisibleBy( poldisc, pp) then continue; end if;
       P := Factorization(ideal< OK | pp >)[1][1] meet O;
       order := Order(P @@ fromCl);
       factpolmodpp := Factorization( PolynomialRing(GF(pp))! pol );
       for fact in factpolmodpp do
          if not (fact[2] eq 1 and Degree(fact[1]) eq order)
          then sane := false; break; end if;
       end for;
       if not sane then break; end if;
       numprimes +:= 1;
     end while;
   else   // this case is a much less efficient check
     vprint Heegner,1: "Heuristic check: that the polynomial has the correct "
                     * "splitting modulo p, for 50 small primes p"; 
     numprimes := 0;
     pp := 2;
     while numprimes lt 50 do
       pp := NextPrime(pp);
       if LegendreSymbol(D,pp) ne 1 then continue; end if;
       if IsDivisibleBy( poldisc, pp) then continue; end if;
       P := Factorization(ideal< OK | pp >)[1][1] meet O;
       order := Order(P @@ fromCl);
       if order ne 1 
          and not (koly and IsCyclic(Cl) and IsDivisibleBy(#Cl, p*order)) 
          then continue; end if;
       factpolmodpp := Factorization( PolynomialRing(GF(pp))! pol );
       if not #factpolmodpp eq Degree(pol) then sane := false; break; end if;
       numprimes +:= 1;
     end while;
   end if;
   if not sane then
      vprintf Heegner,1: 
         "The polynomial failed the sanity check (after trying %o primes), " * 
         "starting again with higher precision\n", numprimes+1;
//"\n\n       INSANE!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n\n";
      return HeegnerPoints(E, D : KolyvaginPrime:=p, ReturnPoint:=ReturnPoint, Precision:=2*prec);
   end if;
  
   H<u> := NumberField(ChangeRing(pol,Rationals())/LeadingCoefficient(pol) : DoLinearExtension); 
        // should be a subfield of the class field
// work-around for Automorphisms
if koly then
 H<utimesLC> := NumberField(MinimalPolynomial(u*LeadingCoefficient(pol)) : DoLinearExtension);
 u := utimesLC/LeadingCoefficient(pol);
end if;

   x_multiplicity := inverse_pairs select 2*multiplicity else multiplicity;
   if not ReturnPoint then
     return <pol, x_multiplicity>, _;
   else
     PTs := Points( ChangeRing(E,H), u );  
     if IsEmpty(PTs) then 
 assert inverse_pairs or mock;
        PH := PolynomialRing(H);
        polYcoord := Evaluate( DefiningPolynomial(E), [u,PH.1,1]);
        L := ext< H | polYcoord : Check:=false >;
        H := AbsoluteField(L); // TO DO: AbsoluteField is in order to Conjugates below ... is that necessary??
        PTs := Points( ChangeRing(E,H), H!u ); 
 // work-around for Automorphisms
 if koly then 
  LC := LeadingCoefficient(polH1)*LCM([Denominator(coeff) : coeff in Coefficients(polH1)])
             where polH1 is MinimalPolynomial(H.1);
  HH := NumberField(MinimalPolynomial(H.1*LC));
  HtoHH := hom< H -> HH | HH.1/LC >;
  PTs := Points( ChangeRing(E,HH), HtoHH(H!u) ); 
  H := HH;
 end if;
 else assert not inverse_pairs;
     end if;
     PTs := ChangeUniverse(PTs, E(H));
     degPTs := Degree(H);
     require multiplicity*degPTs eq class_number
          or mock
          or rank eq 0 and multiplicity*degPTs eq 2*class_number  // = Degree of H_K
          or koly and multiplicity*degPTs in {p, 2*p}
           : "The polynomial obtained does not seem to have the correct degree";
     // now check which of the two points in PTS is in HptsinEC
     if inverse_pairs then 
        HPT := PTs[1];  // either will do
     else 
        vprint Heegner,2: "Constructed point, now choosing between the point and its inverse";
        HPT := 0;
        for PT in PTs do
          PTcomplex := <Conjugates(PT[1])[1], Conjugates(PT[2])[1]>;
          for Hpt in HptsinEC do
            if &and[ Abs(Hpt[j]-PTcomplex[j]) lt Abs(Hpt[j])/10^10  or
                     Abs(Hpt[j]-PTcomplex[j]) lt 10^-10             // in case Hpt[j] = 0    
                   : j in [1,2] ] then HPT := PT; end if;
          end for; 
        end for; 
     end if;
     require HPT cmpne 0 : 
            "Something went wrong computing a representative point ... precision problems?"; 

     return <pol, x_multiplicity>, HPT;
   end if;

end intrinsic;
