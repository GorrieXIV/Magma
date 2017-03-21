freeze;
// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// these package files are updated concurrently by
// ourselves (magma) AND M. Stoll
// Thank you!
/*************************************
 * Hyperelliptic/torsion.m           *
 *                                   *
 * Compute rational torsion subgroup *
 *                                   *
 * Michael Stoll                     *
 *                                   *
 * started 29-Jun-1998               *
 *************************************/

/*------------------------------------------------------------------

  TO DO:
  
    TwoTorsionSubgroup for general J

  CHANGES

  M. Stoll, 2000-08-11
  
    Corrected a few typos in documentation and the like
    
    Corrected bound1 in TorsionSubgroup (taking LLL bounds into account)
    
  2000-08-18:
  
    Now using infinite precision p-adic field

  2001-05-24:
    replace pSubgroup by Sylow (kernel function)
 
   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
                 Curve fix
   
   2001-10-08 Michael Stoll
     Fixed a small bug in TwoTorsionSubgroup (`illegal null sequence')
   
   2005-12, Steve:
 
     Fixed a problem in LiftTorsionPoint to do with pAdic fields.
     (update F`DefaultPrecision each time the required precision goes up)

   2007-1, Steve:
     
     Fixed a typo near the end of LiftTorsionPoint, which came up in Brumer's example:
     > TorsionSubgroup(Jacobian(HyperellipticCurve(4*x^6+12*x^5+13*x^4-2*x^3-11*x^2-12*x-4)));
 
  ---------------------------------------------------------------------------------------------*/

intrinsic TwoTorsionSubgroup(J::JacHyp) -> GrpAb, Map
{The rational 2-torsion subgroup of J for curves of genus 2 in simplified model.}
    // For the time being only for genus 2 and simplified model 
    // of the curve
    if assigned J`TwoTorsion then 
      return J`TwoTorsion[1], J`TwoTorsion[2];
    end if;
    C := Curve(J);
    if Genus(C) ge 3 then
      require Degree(C) mod 2 eq 1:
       "TwoTorsionSubgroup is currently only implemented for Jacobians",
       "of odd degree curves or genus 2 curves";
      f,h := HyperellipticPolynomials(C);
      require h cmpeq 0:
       "TwoTorsionSubgroup requires a curve in the form y^2 = f(x)";
      fact := Factorization(f);
      gens := Prune([J![ g[1],0] : g in fact ]); 
      G<[P]> := AbelianGroup([2 : i in [1..#gens]]);
      iso := map< G -> J | g :-> &+[J | s[i]*gens[i] : i in [1..#s]]
          where s := Eltseq(g) >;
      return G,iso;
    end if;
      
    require Genus(C) eq 2:
       "TwoTorsionSubgroup is currently only implemented for Jacobians",
       "of genus 2 curves.";
    f, h := HyperellipticPolynomials(C);
    require h eq 0:
       "TwoTorsionSubgroup requires a curve in the form y^2 = f(x).";
    fact := Factorization(f);
    // look for factors of degree 2
    fact1 := [ pair[1] : pair in fact | Degree(pair[1]) eq 1 ];
    fact2 := [ pair[1] : pair in fact | Degree(pair[1]) eq 2 ];
    if Degree(f) eq 5 then
      gens := [ J ! [pol, 0] : pol in fact1 ];
    elif #fact1 ge 2 then
      gens := [ J ! [ pol1*fact1[i], 0 ] : i in [2..#fact1] ]
              where pol1 := fact1[1];
    else
      gens := [];
    end if;
    gens cat:= [ J ! [ pol, 0 ] : pol in fact2 ];
    if #fact1 + 2*#fact2 eq Degree(f) then Prune(~gens); end if;
    L := [ J!0 ];
    for g in gens do L cat:= [ g + pt : pt in L ]; end for;
    G<[P]> := AbelianGroup([ 2 : i in [1..#gens] ]);
    iso := map< G -> J | g :-> &+[J | s[i]*gens[i] : i in [1..#s]]
                               where s := Eltseq(g) >;
    J`TwoTorsion := <G, iso, L>;
    return G, iso;
end intrinsic;

function HasPointOrder(P, n, B)
    // Tests whether P::SrfKumPt (on K over the rationals) is a torsion
    // point of order n. B is a bound for the non-logarithmic naive height
    // of a torsion point.
    check := func< pt | Abs(pt[1]) gt B or Abs(pt[2]) gt B
                         or Abs(pt[3]) gt B or Abs(pt[4]) gt B >;
    m := n;
    K := Parent(P);
    Px := K!0; Py := P; Pz := P;
    // invariants: Px = ax*P, Py = ay*P, Pz = az*P with
    //  ax + ay = az  and  ax + m*az = n .
    while true do
      if IsOdd(m) then
        Px := PseudoAdd(Px, Pz, Py);
        if check(Px) then return false; end if;
      else
        Py := PseudoAdd(Py, Pz, Px);
        if check(Py) then return false; end if;
      end if;
      m div:= 2;
      if m eq 0 then return Px eq K!0; end if;
      Pz := Double(Pz);
      if check(Pz) then return false; end if;
    end while;
end function;

// Lift a torsion point in J(F_p) to J(Q) if possible
function LiftTorsionPoint(P, J, b, B)
// (P::JacHypPt, J::JacHyp, b::RngIntElt, B::FldReElt) -> BoolElt, JacHypPt
    // J = Jacobian of genus 2 curve over the rationals,
    // P = point on Jacobian over F_p,
    // b = bound for p-adic approximation precision.
    // B = height bound for torsion points
    prec := 1;
    p := #CoefficientRing(Parent(P));
    n := Order(P);
    if n eq 2 then
      // this is a special case
      tt := TwoTorsionSubgroup(J);
      tt := J`TwoTorsion[3];
      K := KummerSurface(J);
      Kp := KummerSurface(Parent(P));
      PKp := Kp!P;
      for i := 2 to #tt do
        if Kp!(K!tt[i]) eq PKp then return true, tt[i]; end if;
      end for;
      return false, _;
    end if;
    _, a := Xgcd(p, n);
    m := a*p; // p divides m and m is congruent to 1 mod n
    K := KummerSurface(J);
    // first lift
    F := pAdicField(p);
    Kp := BaseExtend(K, F);
    PK:= Kp![ (F!Integers()!a) + O(F!p)
               : a in Eltseq(KummerSurface(Parent(P))!P) ];
    L := Lattice(4, ChangeUniverse(Eltseq(PK), Integers())
                     cat [p,0,0,0, 0,p,0,0, 0,0,p,0, 0,0,0,p]);
    app := Eltseq(Basis(L)[1]);
    while prec lt b do
      // next lift
      newprec := Min(2*prec,b);
      F`DefaultPrecision := Max(F`DefaultPrecision, newprec);
      Onew := O(F!p^newprec);
      Kp := BaseExtend(K, F);
      // lift point
      s := [ (F!Integers()!a) + Onew : a in Eltseq(PK) ];
      kv := Evaluate(Kp`Equation, s);
      dkv := [ Evaluate(Kp`DEquation[i], s) : i in [1..4] ];
      i := 1;
      while i le 4 and Valuation(dkv[i]) gt 0 do i +:= 1; end while;
      error if i gt 4, "LiftTorsionPoint: Singularity detected!!\n",
            "K =",Kp,"\nP =",s;
      s1 := s;
      s1[i] -:= kv/dkv[i];
      s2 := Eltseq(m*(Kp!s1));
      error if Min([ Valuation(s1[i]-s2[i]) : i in [1..4] ]) lt prec,
            "LiftTorsionPoint: Precision loss!!";
      PK := Kp![ (m*s1[i] - s2[i])/(m-1) : i in [1..4] ];
      // compute approximation
      q := p^newprec;
      L := Lattice(4, ChangeUniverse(Eltseq(PK), Integers())
                       cat [q,0,0,0, 0,q,0,0, 0,0,q,0, 0,0,0,q]);
      app1 := Eltseq(Basis(L)[1]);
      // check if already found
      if app eq app1 and IsPoint(K, app1) then
        PQ := K!app1;
        if HasPointOrder(PQ, n, B) then
          PJ := Points(J, PQ);
          if IsEmpty(PJ) then
            return false, _;
          else
            return true, PJ[1];
          end if;
        end if;
      end if;
      prec := newprec; app := app1;
    end while;
    // now prec = b. Check if found
    if not IsPoint(K, app) then return false, _; end if;
    PQ := K!app;
    //Bug fix by Steve:
    //if not HasPointOrder(P, n, B) then return false, _; end if;
    if not HasPointOrder(PQ, n, B) then return false, _; end if;
    PJ := Points(J, PQ);
    if IsEmpty(PJ) then return false, _; else return true, PJ[1]; end if;
end function;

intrinsic TorsionSubgroup(J::JacHyp)
    -> GrpAb, Map
{Finds the rational torsion subgroup of J. The curve of J must have genus 2
 and be defined over the rationals and have form  y^2 = f(x)  with integral 
 coefficients. Second value gives the map from the group into J. }
    tstart := Cputime();
    tlift := 0.0;
    if assigned J`TorsionGroup then
      return J`TorsionGroup, J`TorsionMap;
    end if;
    C := Curve(J);
    require Genus(C) eq 2 and CoefficientRing(C) cmpeq Rationals():
            "TorsionSubgroup is only implemented",
            "for Jacobians of genus 2 curves over the rationals.";
    f, h := HyperellipticPolynomials(C);
    require h eq 0 and &and[ Denominator(c) eq 1 : c in Coefficients(f)]:
            "TorsionSubgroup needs a curve of the form  y^2 = f(x),",
            "where f has integral coefficients.";
    vprint JacHypTorsion: "TorsionSubgroup of J = \n",J;
    bound := HeightConstant(J);
    // This bounds the logarithmic naive height of the torsion points
    vprint JacHypTorsion: " Height Constant =",bound;
    Bound := Exp(bound);           // non-log height bound
    bound1 := Log(64.0) + 2*bound; // bound for p-adic precision
    // Get a bound for the order of the torsion subgroup
    //  (by looking at the reduction at a few good primes).
    tb := TorsionBound(J, 10);
    tb1 := J`TorsionBound[3];
    fact := Factorization(tb);
    vprintf JacHypTorsion: " Torsion Bound = %o, factored: %o\n",tb,fact;
    // Initialize data for group.
    ed := [];      // elementary divisors
    gL := [ J | ]; // generators
    for pair in fact do
      q := pair[1];
      vprintf JacHypTorsion: "  Determining %o-part...\n",q;
      // Find p such that J(F_p) has minimal p-valuation and p ne q.
      e, pos := Min([ Valuation(t[2],q) + (t[1] eq q select 1000 else 0) :
                      t in tb1 ]);
      p := tb1[pos][1];
      vprintf JacHypTorsion:
              "   Using prime %o; %o-torsion has order %o^%o\n",p,q,q,e;
      pbound := Ceiling(bound1/Log(p));
      vprintf JacHypTorsion: "   Approximation up to O(%o^%o)\n",p,pbound;
      // Compute q-subgroup of J(F_p)
      Jp := BaseExtend(J, GF(p));
      if GetVerbose("JacHypTorsion") gt 0 then
        Kp := BaseExtend(KummerSurface(J), GF(p));
      end if;
      Gp, mp := Sylow(Jp, q);
      inv := Invariants(Gp);
      vprintf JacHypTorsion: "   Structure of %o-subgroup: %o\n",q,inv;
      // Determine subgroup of points that lift to J(Q)
      Tcurr := sub<Gp |>;
      Tgens := [Gp | ];
      Tgimages := [J | ];
      Gcurr, qmap := quo<Gp | Tcurr>;
      S0 := { Gcurr | 0 };
      S1 := Set(Gcurr) diff S0;
      while not IsEmpty(S1) do
        vprint JacHypTorsion:
               "    Current subgroup has invariants", Invariants(Tcurr);
        vprint JacHypTorsion:
               "     There are at most",#S1 div (q-1),"elements to be tested.";
        // Choose some element in S1
        g := Rep(S1);
        // Make it primitive
        g := Gcurr![ s div gcd : s in gs ]
               where gcd := GCD(gs)
               where gs := Eltseq(g);
        // Find smallest j such that q^j*g lifts
        j := 0; gg := g;
        while gg ne Gcurr!0 do
          gl := gg @@ qmap; // Some preimage in Gp
          pt := mp(gl);     // and the corresponding point on J(F_p)
          vprint JacHypTorsion: "     Trying to lift point",pt,"...";
          vprintf JacHypTorsion, 2:
                  "     Image on Kummer surface = %o\n", Kp!pt;
          tt := Cputime();
          flag, lift := LiftTorsionPoint(pt, J, pbound, Bound); // Lift
          tlift +:= Cputime(tt);
          if flag then 
            vprintf JacHypTorsion: "     Point lifts";
            vprintf JacHypTorsion, 2: " to %o", lift;
            vprintf JacHypTorsion: "\n";
            break;
          else
            vprint JacHypTorsion: "     Point does not lift";
          end if;
          j +:= 1;
          gg := q*gg;
        end while; // gg ne Gcurr!0
        // Here, gg = q^j*g, and gl is a preimage of gg in Gp
        if gg ne Gcurr!0 then
          // Can enlarge current subgroup
          Append(~Tgens, gl);
          Append(~Tgimages, lift);
          Tcurr := sub<Gp | Tcurr, gl>;
          Gcurr, qmap1 := quo<Gcurr | gg>;
          qmap := qmap*qmap1;
          // Note new elements we know don't lift
          S0 := qmap1(S0) join { k*g1 : k in [1..q^j-1] } where g1 := qmap1(g);
          S1 := Set(Gcurr) diff S0;
        else // gg eq Gcurr!0
          // Note new elements we know don't lift
          Snew := { k*g : k in [1..q^j-1] };
          S0 join:= Snew;
          S1 diff:= Snew;
        end if; // gg ne Gcurr!0
      end while; // not IsEmpty(S1)
      // Now, Tcurr is the subgroup of Gp of points that lift to J(Q).
      // Find generators in J(Q).
      invs := Invariants(Tcurr);
      vprintf JacHypTorsion:
              "   The %o-part of the torsion subgroup has invariants %o\n",
              q, invs;
      if not IsEmpty(Tgens) then
        // This `if' is necessary since Magma 2.4 barfs on
        //  hom< G -> G | [G|] > where G := FreeAbelianGroup(0)
        vprintf JacHypTorsion:
                "  Determining generators for the %o-part...\n",q;
        qqmap := hom< FreeAbelianGroup(#Tgens) -> Tcurr | Tgens >;
        Lp1 := [ &+[ s[j]*Tgimages[j] : j in [1..#s] ]
                 where s :=  Eltseq(Tcurr.i @@ qqmap)
                 : i in [1..#invs] ];
        if GetVerbose("JacHypTorsion") ge 2 then
          print "   Generators with their orders:";
          for i := 1 to #invs do
            print "    ", Lp1[i], ",  of order", invs[i];
          end for;
        end if; // GetVerbose("JacHypTorsion") ge 2

        // Now put q-part together with what we've got so far.
        d := #invs-#ed;
        vprintf JacHypTorsion:
                "  Combining %o-part with what we've already got...\n",q;
        if d gt 0 then
          ed := invs[[1..d]] cat [ Lcm(ed[i], invs[i+d]) : i in [1..#ed] ];
          gL := Lp1[[1..d]] cat [ gL[i] + Lp1[i+d] : i in [1..#gL] ];
        else
          ed := ed[[1..-d]] cat [ Lcm(ed[i-d], invs[i]) : i in [1..#invs] ];
          gL := gL[[1..-d]] cat [ gL[i-d] + Lp1[i] : i in [1..#Lp1] ];
        end if;
      end if; // not IsEmpty(Tgens)
      vprint JacHypTorsion: "  Current invariants:",ed;
    end for; // pair in fact
    vprintf JacHypTorsion: "\n";
    
    // Construct the abstract group
    G<[P]> := AbelianGroup(ed);
    vprint JacHypTorsion: " Torsion subgroup has structure", ed;
    if GetVerbose("JacHypTorsion") ge 2 and not IsEmpty(ed) then
      print "   Generators with their orders:";
      for i := 1 to #ed do
        print "    ", gL[i], ",  of order", ed[i];
      end for;
    end if;
    vprintf JacHypTorsion: "\n";
    // Construct the isomorphism from the abstract group to the points on J
    iso := map< G -> J | g :-> &+[ J | s[i]*gL[i] : i in [1..#s]]
                               where s := Eltseq(g) >;
    J`TorsionGroup := G; J`TorsionMap := iso;
    t := Cputime(tstart);
    vprintf JacHypTorsion: "Time used for lifting: %o ms\n", Round(1000*tlift);
    vprintf JacHypTorsion: "Total time:            %o ms\n\n", Round(1000*t);
    return G, iso;
end intrinsic;
