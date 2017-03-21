freeze;

///////////////////////////////////////////////////////////////////////////
//   Code to reduce the problem of solving conics to subfields           // 
//   Steve Donnelly, February 2010                                       // 
///////////////////////////////////////////////////////////////////////////

import "points.m" : can_factor, 
                    reduce_ideal;

debug := false;

/* 
Consider a conic C : x^2 - a*y^2 = b*z^2 for a,b in K.
Let F be a subfield of K with [K:F] = 2 or 3. 
We find a solution to x^2 - a*y^2 = b*s with x,y in K and s in F.

Hence we can replace b by s, and then likewise replace a by some r in F.
Then x^2 - r^y^2 = s*z^2 is soluble over K, and solving it is equivalent
to solving C over K.  Trying this several times, we hope to find r,s 
for which the new conic is soluble over F, not only over K.

TO DO: clean up!!!
*/

function pretty_norms(primes)
  s := "";
  for i := 1 to #primes do 
    if i gt 1 then 
      s *:= ", ";
    end if;
    p, e := Explode(Factorization(Norm(primes[i]))[1]);
    s *:= IntegerToString(p);
    if e gt 1 then 
      s *:= "^" * IntegerToString(e);
    end if;
  end for;
  return s;
end function;

// return a value of the form A*X^2 + B*X*Y + C*Y^2 with valuation v at p, 
// where v must be the minimum valuation of the A1, B1, C1

function min_val(A, B, C, v, p) 
  if Valuation(A, p) eq v then
    return A;
  elif Valuation(C, p) eq v then
    return C;
  else 
    return A + B + C;
  end if;
end function;

function point_on_quadric_surface(Q)

    assert Type(Q) eq RngMPolElt;

    Pol<x0, x1, y0, y1> := Parent(Q);
    F := BaseRing(Pol);
    ZF := Integers(F);
    Proj2<R, S, T> := ProjectiveSpace(F, 2);

    // obvious solutions? (below we assume the diagonal coeffs are nonzero)
    for i := 1 to 4 do 
      if MonomialCoefficient(Q, Pol.i^2) eq 0 then
        s := [F|0,0,0,0]; s[i] := 1;
        assert Evaluate(Q,s) eq 0;
        return s;
      end if;
    end for;

    // Clear denominators (TO DO : redundant if we do reduce_ideal next)
    denom := LCM([ Denominator(c*ZF) : c in Coefficients(Q) ]);
    Q *:= denom;
vprintf Conic: "Scaled quadric to clear denominator by %o\n", Factorization(denom);

    // Try to factor out content
    content := ideal< ZF | Seqset(Coefficients(Q)) >; // sequences are subject to misinterpretation!
Q0 := Q; content0 := content;
    _, s := reduce_ideal(content);
    Q *:= s;
    content *:= s;
    assert &and [IsIntegral(x) : x in Coefficients(Q)];
    StoreFactor([Minimum(tup[1]) : tup in Factorization(content) ]);
vprintf Conic: "Scaled quadric to remove content by %o\n", [<Norm(tup[1]),tup[2]> : tup in Factorization(1/s*ZF)];
vprintf Conic: "Remaining content is %o\n", [<Norm(tup[1]),tup[2]> : tup in Factorization(content)];

assert IsEmpty(Seqset(Monomials(Q)) meet {x0*y0, x0*y1, x1*y0, x1*y1});

  if IsEmpty(Seqset(Monomials(Q)) meet {x0*y0, x0*y1, x1*y0, x1*y1}) then

    // METHOD 1: break Q = Q1 + Q2 and find t such that we can solve Q1 = t and Q2 = -t
vprint Conic: "METHOD 1 in point_on_quadric_surface";

    Q1 := Evaluate(Q, [R, S, 0, 0]);
    Q2 := Evaluate(Q, [0, 0, R, S]);

    A1,B1,C1 := Explode([MonomialCoefficient(Q1,m) : m in [R^2,R*S,S^2]]);
    A2,B2,C2 := Explode([MonomialCoefficient(Q2,m) : m in [R^2,R*S,S^2]]);
assert &and [IsIntegral(x) : x in [A1,B1,C1,A2,B2,C2]];
    D1 := B1^2 - 4*A1*C1;
    D2 := B2^2 - 4*A2*C2;
    gcd1 := ideal< ZF | A1, B1, C1>;
    gcd2 := ideal< ZF | A2, B2, C2>;

    // Find congruence conditions t == t0 mod M, to guarantee local solubility
    // at primes dividing the discriminants D1 and D2
    // TO DO: explain how this works!

    primes := Setseq({tup[1] : tup in Factorization(D1*ZF) cat Factorization(D2*ZF) | F!2 notin tup[1] }); 
    Sort(~primes, func<P1,P2|Norm(P1)-Norm(P2)> );
    // skip large ones that don't divide the gcds, so that t0 is not too large. 
    function really_need(p)
      if Valuation(gcd1,p) eq 0 and Valuation(gcd2,p) eq 0 then
        return false;
      end if; 
      _, modp := ResidueClassField(p);
      if IsSquare(D1@modp) and IsSquare(D2@modp) then
        return false;
      end if;
      return true;
    end function;
    cprimes := [p: p in primes | Norm(p) le 10^10 or really_need(p)];

    vprintf Conic, 2: "Arranging local solubility at primes dividing the discriminants. "*
                      "Norms of primes: %o\n", pretty_norms(cprimes);
    if #cprimes ne #primes then
      vprintf Conic, 2: "Skipping: %o\n", pretty_norms([p: p in primes | p notin cprimes]);
    end if;
    moduli := [];
    values := [];
    for p in cprimes do 
printf "prime %o: ", Factorization(Norm(p))[1];
      v := func< x | Valuation(x,p) >;
      pi := UniformizingElement(p); 
      kp, modp := ResidueClassField(p);
      vD1 := v(D1);   
      vD2 := v(D2);
      vg1 := v(gcd1); 
      vg2 := v(gcd2);
      // values with minimal valuation
      V1 := min_val(A1,B1,C1,vg1,p); assert v(V1) eq vg1;
      V2 := min_val(A2,B2,C2,vg2,p); assert v(V2) eq vg2;

      if IsEven(vD1) and IsEven(vD2) then
        if IsEven(vg1) and IsEven(vg2) then
          tp := ZF!1;
printf "case 1 ";
        elif IsOdd(vg1) and IsOdd(vg2) then
          tp := pi;
printf "case 2 ";
        elif not IsSquare( (D1/pi^vD1) @modp) then
          tp := V1;
printf "case 3 ";
        elif not IsSquare( (D2/pi^vD2) @modp) then
          tp := V2;
printf "case 4 ";
        else 
          tp := ZF!1; // any value works
printf "case 5 ";
        end if;
      elif IsOdd(vD1) and IsOdd(vD2) then
printf "case 6 ";
        if (vg1 - vg2) mod 2 ne 0 then
printf "odd ";
          V1 *:= -D1;
        end if;
        r := V1/V2;
        vr := v(r); assert IsEven(vr);
        r /:= pi^vr;
        if not IsSquare(-r@modp) then
printf "nonsquare ";
          V1 div:= -D1;
          V2 *:= -D2;
          r := V1/V2;
          vr := v(r); assert IsEven(vr);
          r /:= pi^vr;
          assert IsSquare(-r@modp);
        end if;
        tp := V1;
      elif IsOdd(vD1) then
        if (vg1 - vg2) mod 2 eq 0 then
          tp := V1;
printf "case 7 ";
        else
          tp := V1 * -D1;
printf "case 8 ";
        end if;
      elif IsOdd(vD2) then
        if (vg1 - vg2) mod 2 eq 0 then
          tp := -V2;
printf "case 9 ";
        else
          tp := -V2 * -D2;
printf "case 10 ";
        end if;
      end if;

      // use standard choices
      vtp := v(tp);
      if IsEven(vtp) then
        sp := ZF!1; 
        Mp := p;
      else
        sp := pi;   
        Mp := p^2;
      end if;
      if not IsSquare( (tp/pi^vtp) @modp) then
        // standard nonsquare mod p
        assert IsOdd(#kp);
        if #kp mod 4 eq 3 then
          ns := -1;
        else
          s := kp!-1;
          repeat
            ns := s;
            bool, s := IsSquare(s);
          until not bool;
          ns := ns @@modp;
        end if;
        sp *:= ns;
      end if;

if debug and Norm(p) lt 10^4 then printf "checking ";
con1 := Conic(Proj2, Q1 - sp*T^2);
con2 := Conic(Proj2, Q2 + sp*T^2);
assert IsLocallySolvable(con1,p);
assert IsLocallySolvable(con2,p); 
end if;
printf "tp = %o\n", F!sp;

      Append(~values, sp);
      Append(~moduli, Mp);
    end for;

    if #cprimes gt 0 then
      t0 := F! CRT(values, moduli);
      M := &* moduli;
      vprintf Conic, 2: "Congruences for solvability: \nt = %o mod ideal of norm %o\n", t0, Norm(M);
    else
      t0 := F! 0;
      M := 1*ZF;
    end if;
    
    // adjust t0 to have the right sign at real places, if they matter
    places := [];
    signs := [];
    for v in RealPlaces(F) do 
      tv := 0;
      if Evaluate(D1,v) lt 0 then
        tv := Sign(Evaluate(A1,v));
      elif Evaluate(D2,v) lt 0 then
        tv := Sign(Evaluate(-A2,v));
      end if;
      if tv ne 0 then
        Append(~places, v);
        Append(~signs, tv);
      end if;
    end for;
    if exists{i: i in [1..#places] | Sign(Evaluate(t0,places[i])) ne signs[i]} then 
"Getting t0 right at the infinite places:  RealWeakApproximation ... "; time 
      t00 := RealWeakApproximation(places, signs);
      assert &and [Sign(Evaluate(t00,places[i])) eq signs[i] : i in [1..#places]];
      m := Minimum(M); 
      if t0 eq 0 then
        jump := m;
      else
        ratio := Exp(AbsoluteLogarithmicHeight(t0) - AbsoluteLogarithmicHeight(t00));
        jump := m*Ceiling(ratio/m);
      end if;
      repeat
printf ".";
        t0 +:= jump*t00;
      until forall{i: i in [1..#places] | Sign(Evaluate(t0,places[i])) eq signs[i]}; 
      t0 +:= 1*jump*t00; // jump a healthy distance into the good sector
printf "\n";
    end if;

    BM := LLLBasis(M);

    success := false;
    L := StandardLattice(Degree(F));
    N := -1;
    while not success do 
      N +:= 1;
      if N eq 0 then 
        elts := [F| s*n : s in [1,-1], n in [1..5]];
      else
        coeffs := [Eltseq(tup[1]) : tup in ShortVectors(L, N, N)];
        elts := [F| t0 + &+[c[i]*BM[i] : i in [1..#c]] : c in coeffs];
      end if;
      for t in elts do 
         if t eq 0 or not can_factor(t, 1) then 
  printf "F ";
            continue t;
         end if;
  printf "t = %o ", t;
  printf "\n";
         C1 := Conic(Proj2, Q1 - t*T^2);
         C2 := Conic(Proj2, Q2 + t*T^2);
         if not IsLocallySolvable(C1) or not IsLocallySolvable(C2) then 
            continue t;
         end if;

printf "\nIn parametrize_quadric_surface, over degree %o field, first conic:\n", Degree(F); Equation(C1);
         bool, A := HasRationalPoint(C1); assert bool;
printf "In parametrize_quadric_surface, over degree %o field, second conic:\n", Degree(F); Equation(C2);
         bool, B := HasRationalPoint(C2); assert bool;
         if A[3] eq 0 and B[3] eq 0 then 
printf "both binary forms Q1 and Q2 are solvable ";              
            sol := [A[1], A[2], B[1], B[2]];
         elif A[3] eq 0 then
printf "binary form Q1 is solvable ";              
            Proj1<u,v> := Curve(ProjectiveSpace(F, 1));
            pramC1 := Parametrization(C1, C1!A, Proj1);
            for pp in [Proj1| [1,0], [0,1], [1,1] ] do 
               A := Eltseq(pp @ pramC1);
               if A[3] ne 0 then
                  break;
               end if;
            end for;
            sol := [A[1]/A[3], A[2]/A[3], B[1]/B[3], B[2]/B[3]];
         elif B[3] eq 0 then
printf "binary form Q2 is solvable ";              
            Proj1<u,v> := Curve(ProjectiveSpace(F, 1));
            pramC2 := Parametrization(C2, C2!B, Proj1);
            for pp in [Proj1| [1,0], [0,1], [1,1] ] do 
               B := Eltseq(pp @ pramC2);
               if B[3] ne 0 then
                  break;
               end if;
            end for;
            sol := [A[1]/A[3], A[2]/A[3], B[1]/B[3], B[2]/B[3]];
         else 
            sol := [A[1]/A[3], A[2]/A[3], B[1]/B[3], B[2]/B[3]];
         end if;
         assert Evaluate(Q, sol) eq 0;
         success := true;
printf "t = %o worked\n", t;
         break t;
      end for; // t
    end while;

  else

    // METHOD 2: intersect Q with random planes until we get a conic soluble over F
    // TO DO: diagonalize and use method 1 
vprint Conic: "METHOD 2 in point_on_quadric_surface";

    success := false;
    L := StandardLattice(2);
    Nmax := 50;
Nmax := 1000;
    N := 0;
    repeat
       N +:= 1;
       if N gt 10 and Dimension(L) eq 2 then
          L := StandardLattice(3);
          N := 1;
       elif N gt Nmax then
          error "In replace: bug detected (failed to find a soluble conic)";
       end if;
       if N eq 0 then
          vecs := [L!0];
       else
          vecs := ShortVectors(L, N, N);
          if #vecs eq 0 then continue; end if;
       end if;
printf " N = %o : %o vectors", N, #vecs;
       for tup in vecs do
          v := Eltseq(tup[1]);
//if #v eq 4 and v[4] eq 0 then continue; end if;
printf " .";
          // Take hyperplane with coefficient vector v;
          // substitute into Q replacing the 4th variable y1
          // (to make diagonalization simpler, take special hyperplanes;
          //  TO DO: prove we must find a soluble conic this way)
          y1_subst := (#v eq 2) select (v[1]*R + v[2]*S)
                                 else  (v[1]*R + v[2]*S + v[3]*T);
          eqnC := Evaluate(Q, [R, S, T, y1_subst]);
          disc_nonzero, C := IsConic(Scheme(Proj2, eqnC));
          if disc_nonzero then
             if can_factor(Discriminant(C), 1) then 
//vprintf Conic: "\nIsLocallySolvable? (should be quick) ... "; time0 := Cputime();
//""; SetVerbose("Factorization", 1);
//ProStart();                  
                soluble := IsLocallySolvable(C);
//vprintf Conic: "%o  (time: %o)\n", soluble, Cputime(time0);
//SetVerbose("Factorization", 0);
//if Cputime(time0) ge 3 then ProShow(15); end if;             
                if soluble then
                   bool, p := HasRationalPoint(C); assert bool;
                   sol := Eltseq(p) cat [Evaluate(y1_subst, Eltseq(p))];
                   assert Evaluate(Q, sol) eq 0;
                   success := true;
                   break tup;
                end if;
             end if;
          end if;
       end for; // tup
    until success;

  end if;
  return sol;
end function;

function parametrize_quadric_surface(Q)
    QS := Scheme(ProjectiveSpace(Parent(Q)), Q);
    sol := point_on_quadric_surface(Q);
    assert IsNonsingular(QS, QS!sol);
    Proj2<R,S,T> := ProjectiveSpace(BaseRing(QS), 2);
    bool, pram := ParametrizeQuadric(QS, Proj2 : Point:=sol); assert bool;
    return DefiningPolynomials(pram), sol;
end function;

// Return s in F, and a transformation from X^2 - a*Y^2 = s*Z^2 back to X^2 - a*Y^2 = b*Z^2

function replace(a, b, K, F : factorable:=false, solvable:=false)
   if solvable then
      assert a in F;
      assert factorable; // otherwise can't test solvability
   end if;

   bool, bF := IsCoercible(F, b);
   if bool and 
      ( not solvable or IsLocallySolvable(Conic([F| 1, -a, -bF])) )
   then
      return bF, IdentityMatrix(K,3); 
   end if;

   VF, toVF := VectorSpace(K, F);
   function overF(x)
      s := Eltseq(x@toVF);
      return s;
   end function;

   n := Dimension(VF);
   w := K.1;

ZK := Integers(K);
ZF := Integers(F);
FF := FieldOfFractions(ZF);

//assert IsLocallySolvable(Conic([K| 1, -a, -b])); // this is assumed

   if n eq 2 then
      
      a0, a1 := Explode(overF(a));
      b0, b1 := Explode(overF(b));
      c0, c1 := Explode(overF(w^2));

      _<x0, x1, y0, y1> := PolynomialRing(F, 4);

      // Expand x^2 - a*y^2 with respect to [1,w], writing x = x0 + w*x1 etc
      X0 := x0^2 + c0*x1^2;
      X1 := 2*x0*x1 + c1*x1^2;
      Y0 := y0^2 + c0*y1^2;
      Y1 := 2*y0*y1 + c1*y1^2;
      Q0 := X0 - a0*Y0 - c0*a1*Y1;
      Q1 := X1 - a0*Y1 -a1*Y0 - c1*a1*Y1;
      Q := b1*Q0 - b0*Q1;

      pram, sol0 := parametrize_quadric_surface(Q);

      pram_primes := {};
      vprintf Conic, 2: "Factoring coefficients in parametrization "; 
      vtime Conic, 2:
      for x in &cat [Coefficients(x) : x in pram] do 
         if can_factor(x, 5) then
            xprimes := {tup[1] : tup in Factorization(x*ZF)};
            pram_primes join:= xprimes;
            StoreFactor([Minimum(p) : p in xprimes]);
            vprintf Conic, 2: ".";
         else
            vprintf Conic, 2: "!";
         end if;
      end for;
      pram_primes := Sort(Setseq(pram_primes), func<p1,p2|Minimum(p1)-Minimum(p2)>);
      pram_primes_K := [tup[1] : tup in Factorization(ZK!!p), p in pram_primes];
      vprint Conic, 2: "Primes appearing in coefficients of parametrization have norms:", pretty_norms(pram_primes);

if solvable then
    //awkward_primes := [PowerIdeal(ZF)| tup[1] : tup in Factorization((2*a)*ZF) | #Factorization(ideal<ZK|tup[1]>) eq 1];
    //awkward_pram_primes := [p : p in awkward_primes | p in pram_primes];
      awkward_primes := [PowerIdeal(ZK)| tup[1] : tup in Factorization((2*b)*ZK) | LocalDegree(Place(tup[1])) eq 2];
      awkward_pram_primes := [p : p in awkward_primes | p in pram_primes_K];
      Sort(~awkward_primes, func<p1,p2|Minimum(p1)-Minimum(p2)>);
"Awkward primes (dividing 2 or b, with local degree 2 in K/F) have norms:", pretty_norms(awkward_primes);
"Awkward primes that also appear in pram coefficients have norms:", pretty_norms(awkward_pram_primes);

      // Choose congruences by finding a local solution with s = 1 
      // (a local point on the conic's restriction of scalars to F, a Del Pezzo of degree 4)
      P4<V,W,X,Y,Z> := ProjectiveSpace(F, 4);
      S := Scheme(P4, [ Evaluate(Q0, [V,W,X,Y]) - b0*Z^2, 
                        Evaluate(Q1, [V,W,X,Y]) - b1*Z^2 ]); 
/*
      my_primes := [p : p in awkward_primes | Norm(p) lt 10^3];
      my_primes cat:= [tup[1] : tup in Factorization(2*ZF) | tup[1] notin my_primes];
      my_primes := [p : p in my_primes | Norm(p) le 100];
      my_primes := [p : p in my_primes | Norm(p) le 100];
      Sort(~my_primes, func<p1,p2|Norm(p1)-Norm(p2)>);
      my_points := [* *];
      for p in my_primes do 
vprintf Conic, 2: "IsLocallySolvable at %o ... ", Factorization(Norm(p))[1]; 
vtime Conic, 2:
         bool, pt := IsLocallySolvable(S, p); assert bool;
         Append(~my_points, pt);
      end for;
*/
end if;

printf "Trying solutions to quadric: "; 

      l := Min(20, Degree(F));
      L := StandardLattice(3*l);
      ZFb := ChangeUniverse(LLLBasis(1*ZF)[1..l], F);
      zero_pt := [F| 0,0,0,0];
      Proj3 := ProjectiveSpace(F, 3); 
      proj_pts := {Proj3| }; // to detect repeats
pp0 := Proj3! sol0;
      okay := false;
      N := -1;
      while not okay do 
         N +:= 1;
if N gt 1 then printf " %o distinct points tested ", #proj_pts; end if;
         if N gt 0 then
            SVP := ShortVectorsProcess(L, N, N);
         end if;

         repeat
            if N eq 0 then
               p := sol0;
            else
               v, nv := NextVector(SVP);
               if nv eq -1 then 
                  break; 
               end if;
               vv := [F| &+[ v[i+j*l] * ZFb[i] : i in [1..l]] : j in [0..2]];
               p := [Evaluate(x, vv) : x in pram];
               if p eq zero_pt then
                  continue;
               end if;
            end if;
            pp := Proj3!p;
            if pp in proj_pts then 
if pp eq pp0 then printf " P0"; else printf " P"; end if;
               continue;
            else
               Include(~proj_pts, pp);
            end if;

            xx := p[1] + w*p[2];
            yy := p[3] + w*p[4];
            gcd := GCD(Denominator(xx), Denominator(yy)); 
            xx *:= gcd;
            yy *:= gcd;

            // Try to get rid of the F-part of GCD(xx,yy)
            // TO DO : instead, take out content coming from pram first ???
            content := ideal< ZF | overF(xx) cat overF(yy) >;
            if Norm(content) gt 10^5 then
//printf "Removing content ... "; time
               _, sc := reduce_ideal(content);
               xx *:= sc;
               yy *:= sc;
//printf "Scaled xx,yy to remove F-content by %o\n", [<Norm(tup[1]),tup[2]> : tup in Factorization(1/sc*ZK)];
//printf "Remaining K-content is %o\n", [<Norm(tup[1]),tup[2]> : tup in Factorization(ideal<ZK|xx,yy>)];
            end if;

            s := (xx^2 - a*yy^2)/b;
/*
if N gt 0 then "vector is", v; end if;
"p =", p;
"xx, yy =", xx, yy;
"s =", s;
*/
            if s eq 0 then // TO DO: s = 0 means we've solved the conic 
 "Throwing away brilliant solution!!! s = 0!!!";
               continue; 
            end if;
            
            Nb := F!Norm(b);
            too_many := Infinity(); // TO DO: not sure 

            if factorable then 
               eff := (N le 1) select 3 else 1;
               if not can_factor(s, eff) then
printf " F";
                  continue; 
               end if;
            end if;
            if solvable then
               sfact := Factorization(s*ZF);
               if #[tup : tup in sfact | Valuation(a,tup[1]) eq 0 and Valuation(Nb,tup[1]) eq 0] gt too_many then
printf " >%o", too_many;
                  continue;
               end if;
               time0 := Cputime();
               ls := IsLocallySolvable(Conic([F| 1, -a, -s]));
if Cputime(time0) gt 1 then printf " (S:%os)", Round(Cputime(time0)); end if;
               if not ls then 
printf " S";
                  continue;
               end if;
            end if;
            
            // Now found a valid s
            okay := true;
            delete L;
            delete proj_pts;
printf " got one! (replace succeeded!)\n";

            // Make s integral
            if not IsIntegral(s) then
               ds_sqrt := &* [PowerIdeal(FF)| tup[1] ^ Floor(tup[2]/2) 
                                            : tup in Factorization(s*ZF) | tup[2] lt 0];
               _, ss := reduce_ideal(ds_sqrt);
assert IsIntegral(ss*ds_sqrt);
               s *:= ss^2; 
               xx *:= ss;
               yy *:= ss;
               assert IsIntegral(s);
               assert (xx^2-a*yy^2) eq b*s;
            end if;
     
         until okay or N eq 0;
      end while; 

   elif n eq 3 then

      _<x0, x1, x2, y0, y1, y2> := PolynomialRing(F, 6);
      if a in F then // slightly simpler quadrics than general case
         a := F!a;
         b0, b1, b2 := Explode(overF(b));
         w30, w31, w32 := Explode(overF(w^3));
         w40, w41, w42 := Explode(overF(w^4));
         Q0 := x0^2 + 2*w30*x1*x2 + w40*x2^2 - a*(y0^2 + 2*w30*y1*y2 + w40*y2^2);
         Q1 := 2*x0*x1 + 2*w31*x1*x2 + w41*x2^2 - a*(2*y0*y1 + 2*w31*y1*y2 + w41*y2^2);
         Q2 := 2*x0*x2 + x1^2 + 2*w32*x1*x2 + w42*x2^2 - a*(2*y0*y2 + y1^2 + 2*w32*y1*y2 + w42*y2^2);
         if b0 eq 0 then
            quadrics := [Q0, b2*Q1 - b1*Q2];
         else 
            quadrics := [b1*Q0 - b0*Q1, b2*Q0 - b0*Q2];
         end if;
      else
         error "Not implemented yet";
      end if; // a in F
 
SetVerbose("Classify", 1);
      // Intersect with random planes, obtaining degree 4 Del Pezzo surfaces
      // Repeat until we find a soluble one
    //repeat 
         P4<V,W,X,Y,Z> := ProjectiveSpace(F, 4);
         eqns := [Evaluate(q, [V,W,X,Y,Z,0]) : q in quadrics];
         S := Scheme(P4, eqns);
if IsSingular(S) then
 "Warning: surface is singular, so parametrization routine may fail";
end if;
         Proj2<r,s,t> := ProjectiveSpace(F, 2);
         bool, pram := ParametrizeDelPezzo(S, Proj2);
if bool then "Obtained parametrization"; pram; end if;
return bool; 
     //until bool;
   end if;

   // transformation that replaces s by b 
   T := Matrix(K,3,3, [xx,yy,0, a*yy,xx,0, 0,0,s]);
   return s, T;
end function;


intrinsic ConicOverSubfield(a::FldAlgElt, b::FldAlgElt, K::FldAlg, F::Fld) -> RngElt, RngElt, Mtrx
{Given a and b in a number field K such that the conic x^2 - a*y^2 = b*z^2 
 is solvable over K, and a subfield F of K : returns c and d in F such that
 x^2 - c*y^2 = d*z^2 is solvable over F, together with the transformation 
 between the two conics (over K)}

   require Parent(a) eq K and Parent(b) eq K : "The given elements must belong to the larger field";
   require IsCoercible(K, F.1) : "The fourth argument must be a subfield of the third argument";
  
   // TO DO: surely we don't need to kludge this?
   if F cmpeq Rationals() then
      QQ := NumberField(Polynomial([-1,1]) : DoLinearExtension);
      Embed(QQ, K, K!1);
      aa, bb, T := ConicOverSubfield(a, b, K, QQ); 
      return F!aa, F!bb, ChangeRing(T,K);
   end if;
   require ISA(Type(F), FldAlg) : "The third argument should be a number field";

   n := AbsoluteDegree(K) div AbsoluteDegree(F);
   require n in {2,3} : "Implemented only for subfields of index 2 or 3";

   require IsLocallySolvable(Conic([1, -a, -b])) :
          "The given conic is not solvable over its base field";

   // trans = transformation back to original conic, so [x,y,z]*trans = [x0,y0,z0]
   swap := Matrix(K,3,3, [1,0,0, 0,0,1, 0,1,0]); // swaps a and b

   swap_recurse := (a in F and b notin F)            // want to keep a, replace only b
                or not (b in F and a notin F)        // avoid infinite recursion 
                   and Abs(Norm(a)) gt Abs(Norm(b)); // want a smaller than b, since replacing b first
   if swap_recurse then
"ConicOverSubfield: calling recursively with a and b swapped";
      bb, aa, T := ConicOverSubfield(b, a, K, F);
      trans := swap * T * swap;
      return aa, bb, trans;
   end if;

printf "Replacing b = %o\n", b; 
   bb, trans := replace(a, b, K, F : factorable);
printf "Replaced b = %o\n    with b = %o\n", b, bb; 

   if a in F then // try aa = a
      aa := F!a;
      if IsLocallySolvable(Conic([F| 1, -aa, -bb])) then
         return aa, bb, trans;
      end if;
   end if;

printf "Replacing a = %o ...\n", a; time
   aa, T := replace(bb, a, K, F : factorable, solvable);
printf "Replaced a = %o\n    with a = %o\n", a, aa; 

   trans := swap * T * swap * trans; // swap because arguments to replace were swapped
   return aa, bb, trans;

end intrinsic;


// Transform back from Conic([1,-a,-b]) to Conic([1,-a0,-b0])

function transform_soln(a, b, a0, b0, xyz, trans)  
   K := Parent(a0); 
   assert ISA(Type(K), FldNum) and K eq BaseRing(trans);
   okay := xyz[1]^2 - a*xyz[2]^2 - b*xyz[3]^2 eq 0;
   x0,y0,z0 := Explode(Eltseq( Vector(K,xyz) * trans ));
   okay and:= x0^2 - a0*y0^2 - b0*z0^2 eq 0;
   error if not okay, "OH NO!!! Solution is incorrect!!!";
   return [x0,y0,z0];
end function;

// Temporary intrinsic (TO DO!)

intrinsic HasRationalPointUsingSubfield(a::FldAlgElt, b::FldAlgElt, K::FldAlg, F::Fld) -> Bool, SeqEnum
{Temporary intrinsic.  Solve the conic x^2 - a*y^2 = b*z^2 using ConicOverSubfield}

assert IsLocallySolvable(Conic([1, -a, -b]));

if true then
   // Temporary special case, because some of Allan's examples hit this
   if a*b in F then
      K := Parent(a);
      hasi, i := IsSquare(K! -1);
      if hasi then
         "\n  !!!!!!! IN SPECIAL CASE --- a*b is in F !!!!!!!\n";
         bool, sol0 := HasRationalPointUsingSubfield(a, a*b, K, F); 
         if bool then
            trans := Matrix(K,3,3, [0,i,0, i*a,0,0, 0,0,a]);
            sol := transform_soln(a, a*b, a, b, sol0, trans);
            return true, sol;
         else
            return false, _;
         end if;
      end if;
   end if;
end if;

   aa, bb, trans := ConicOverSubfield(a, b, K, F);
   bool, sol1 := HasRationalPoint(Conic([F | 1, -aa, -bb])); 
   if bool then
      return true, transform_soln(aa, bb, a, b, Eltseq(sol1), trans); 
   else
      error "ConicOverSubfield came up with an insoluble conic";
      return false, _;
   end if;
end intrinsic;

