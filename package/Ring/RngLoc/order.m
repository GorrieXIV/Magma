freeze;

//
//bad example by David:
//(in particular this fails the reduced discriminant estimate)
/* <example>
P<x> := PolynomialRing(Rationals());
f := x^8 - 11487605004*x^6 + 49245944224574660406*x^4
         - 93363654664521132466213088876*x^2
                  + 66053631439751607918935257121233240401;
 A := NumberField(f);
 [ Completion(A,Ideal(p[1])) : p in Decomposition(A,2) ];
 </example> 
*/
/*
 <example>
   Attach("/home/claus/Magma/RngLoc.m");

   M := MaximalOrder(x^3-17);
   P := Decomposition(M, 11)[2][1];

   q,w := LocalRing(P, 20);

   (q.1 @@w)^20 - ((q.1^20)@@w);
   Valuation($1, P);
   q`DefaultPrecision := 10;
   (q.1 @@w)^20 - ((q.1^20)@@w);
   Valuation($1, P);
   q`DefaultPrecision := 40;
   (q.1 @@w)^20 - ((q.1^20)@@w);
   Valuation($1, P);
   (M.2 @ w)^20 - (M.2^20)@w;


   M := MaximalOrder(x^2-3);
   N := MaximalOrder(Polynomial(M, x^3-17));
   Na := AbsoluteOrder(N);
   Decomposition(Na, 17);
   P := $1[1][1];
   
 </example>

 <example 3>
     Qz<z> := CyclotomicField(56);
     K := sub< Qz | z + 1/z >;
     K<a> := NumberField(DefiningPolynomial(K));
     H<i,j,k> := QuaternionAlgebra< K | -1,-1 >;
     MaximalOrder(H);
   (27/2/2009)
 </example>  
*/   
     

declare verbose LocalRing , 2;

intrinsic LocalRing(P::RngOrdIdl, Prec::RngIntElt) -> RngPad, Map, .
{the completion at P up to a precision of Prec together with the embedding}
  O := Order(P);

  //"LocalRing", P, Prec;

  require IsAbsoluteOrder(O) : "The ideal must belong to some absolute order";
  require IsPrime(P) : "The ideal must be prime";
  require IsMaximal(O) or RamificationDegree(P) eq 1 : "For ramified primes the order must be maximal";

  Z := BaseRing(O);
  f := InertiaDegree(P);
  e := RamificationDegree(P);
  p := Minimum(P);

  function Mod(a, Pk)
    // assumes that a is integral wrt to Pk = P^k.
    // However, a may have a denominator in the representation.
    if Type(a) eq RngOrdElt then
      assert (a in Pk) or (a mod Pk ne 0);
      return a mod Pk;
    end if;
    d := Denominator(a);
    pk := Minimum(Pk);
    if Gcd(d, pk) eq 1 then
      a := a*d*Modinv(d, pk);
      return (O!a) mod Pk;
    end if;

    // now we have a p in the denominator...
    lp := Decomposition(O, p);
    // we cannot use UniformizingElement as it does not have valuation 0
    // at the other primes. Typically, UniformizingElement(i[1]) eq p
    // which is NOT what we need here.
    // However, by definition the 2nd generator of a p-normal presentation
    // will work.
    u := &* [ b^Maximum(0, -Valuation(a, i[1])) 
                         where _, b := TwoElementNormal(i[1])
                                                  : i in lp | i[1] ne P];
    assert Valuation(u, P) eq 0;
    _, mq := quo<O|Pk>;
    a := (Mod(a*u, Pk)@mq / (Mod(u, Pk)@mq))@@mq;
    return a;
  end function;

  function Lift(f, w, P, k)
    PP := P;
    pk := P^k;
    fs := Derivative(f);

    modP, qP := quo<O | P>;

    b := qP(Evaluate(fs, w));
    if b eq 0 then
      vfs := Valuation(Evaluate(fs, w), P);
      assert 2*vfs lt Valuation(Evaluate(f, w), P);
      assert Denominator(w) eq 1;
      vprint LocalRing, 1: "Starting difficult lift up to precision ", k;
      lp := [1, w];
      for i in [2.. Degree(f)] do
        Append(~lp, lp[i]*w);
      end for;
      fs := Eltseq(Derivative(f));
      f := Eltseq(f);
      ef := &+ [ f[i]*lp[i]: i in [1..#f]];
      if ef eq 0 then
        return w;
      end if;
      kk := Valuation(ef, P);

      /*
Newton Lifting:
  We have, generically in char 0:
    f(a+b) = \sum_0^infty f^(i)(a)b^i/i!
           = f(a) + bf`(a) + b^2(\sum_2^infty f^(i)(a)b^(i-2)/i!)
    
    Now if f is monic, then, as a polynomial in b, f(a+b) is monic as well.
    Thus
      f(a+b) - f(a) - bf`(a) = b^2(\sum_2^infty f^(i)(a) b^(i-2)/i!)
    is a factorisation the monic polynomial on the left into
      b^2 (monic) and some other poly which thus HAS to be monic as well.
    If the coefficient ring is integrally closed (a local ring for example)
    We get:
    Lemma:
      for all a, b in R, ther is some c in R such that
        f(a+b) = f(a)+f'(a)b + b^2c
    And thus:
    Theorem:
      if v(f(a)) > 2v(f'(a)) then the Newton iteration works
    Pf:
      A :=  a - f(a)/f'(a)
      k := v(f(a)), l := v(f'(a))
      f(A) = f(a-f(a)/f'(a)) = f(a) - f'(a) f(a)/f'(a) + (f(a)/f'(a))^2 c
           = (f(a)/f'(a))^2 c
      And v(f(A)) >= 2v(f(a)) - 2v(f'(a)) = 2k-2l = 2(k-l)
      Since 2k-2l = k+(k-2l) > k, this converges.  

    Now, algorithmically, it is more difficult as we also want to invert
    f'(a) efficiently and use modular methods.
      a_0 is the starting point, v(f(a_0)) = k > 2l where
      l := v(f'(a_0))

    Assume a_0 = a_0 + O(pi^k)    
     
    b_0 := f'(a_0)/pi^l  (thus b_0 = b_0 + O(pi^(k-l)))
    c_0 := 1/b_0 + O(pi^(k-l))

    Then for the lift:
      a_0 +O(pi^k)   -> a_0 + O(pi^2k)
      c_0 +O(pi^k-l) -> c_0 + O(pi^2k)
    
    Compute powers of a_0 (in new precision) and evaluate f(a_0) in new
    precision:
      a_1 := a_0 + f(a_0)/pi^k c_0
    
    Now, a_1 should be a root of prec. 2(k-l).
    f'(a_1) = f'(a_0) + pi^(l-k)
    thus
      f'(a_1)/pi^k b_0 = 1+pi^(l-2k)
    so we need to do several iterations for b:
      b_1 := b_0(2-b_0 f'(a_1))
    (which gives 
      f'(a_1)/pi^k b_1 = 1+pi^(2(l-2k))
     but since 2(l-2k) < 2(k-l) this is not enough for the next a's
     repeating this:
       b_1 <- b_1(2-b_1f'(a_1))
       produces f'(a_1)/pi^k b_1 = 1+pi^4(l-2k)
       so we need to iterate until 2^i(l-2k) >= 2(l-k)
     All in precision 2k.
      
     Then go for the next a.  
        
     */ 

      Pk := P^kk;  
      _, mq := quo<Order(P)|Pk>;
      _, pi := TwoElementNormal(P);
      piv := pi^-vfs;

      ff := &+ [ fs[i]*lp[i] : i in [1..#fs]];
      ff := Mod(ff * piv, Pk);
      b := Modinv(ff, Pk); // could be mod P^(k-vfs)

      Pk := P^(2*kk);
      _, mq := quo<Order(P)|Pk>;

      t := Cputime();
      lp := [mq(1), mq(w)];
      for i in [2.. #f-1] do
        Append(~lp, mq(lp[i])*lp[2]);
      end for;
      vprint LocalRing, 2: "Time for pre loop powering", Cputime(t);

      while true do
        vprint LocalRing, 1: "k now: ", kk, "working modulo", 2*kk;

        ef := &+ [ mq(f[i])*mq(lp[i]): i in [1..#f]];
        ef := Mod((ef@@mq)*piv, Pk) @ mq;
        w := w@mq - ef*mq(b);
        assert Valuation(Evaluate(Polynomial(f), w@@mq), P) ge 2*kk-2*vfs;
       
        kk := 2*(kk - vfs);
        if kk ge k then break; end if;
        kk := Minimum(k div 2 + 2*vfs, kk);

        Pk := P^(2*kk);
        _, mq := quo<Order(P)|Pk>;

        t := Cputime();
        lp := [mq(1), mq(w)];
        for i in [2.. #f-1] do
          Append(~lp, mq(lp[i])*lp[2]);
        end for;
        vprint LocalRing, 2: "Time for in loop powering", Cputime(t);
        ff := &+ [ mq(fs[i])*lp[i]: i in [1..#fs]];
        assert Valuation(ff@@mq, P) eq vfs;
        ff := Mod((ff@@mq)*piv, Pk) @ mq;
        b_st := kk div 2 - vfs;
        while b_st lt kk do
          b := mq(b)*(2-mq(b)*ff);
          b_st *:= 2;
        end while;
        assert  
          Valuation((b@@mq*Evaluate(Polynomial(fs), w@@mq)*piv -1 ), P) ge kk;

      end while;
      return w @@ mq;
    end if;
    P := P^2;
    mod2P, q2P := quo<O | P>;
    b := (1/b) @@ qP;
    w := q2P(w);
    w := ((w - q2P(b)*Evaluate(PolynomialRing(mod2P)!f, w))) @@ q2P; 
    k := k div 2;

    fs := Eltseq(fs);
    f := Eltseq(f);

    while k gt 0 do
      vprint LocalRing, 1: "k now: ", k;
      modP := mod2P;
      qP := q2P;
      P := P^2;
      if k ne 1 then
        k := (k+1) div 2;
      else
        k := k div 2;
      end if;

      lp := [mod2P | 1, q2P(w)];
      vtime LocalRing, 2: for i in [3..#f] do
        lp[i] := lp[i-1] * lp[2];
      end for;

      mod2P, q2P := quo<O | P>;

      vtime LocalRing, 2: b := O!((qP(b)*(2-qP(b)* &+ [ qP(fs[i]) * lp[i] : i in [1..#fs]])));
      vtime LocalRing, 2: w := O!((q2P(w)-q2P(b)*&+ [ q2P(f[i]) * mod2P!lp[i] : i in [1..#f]]));
    end while;
    
    _, qP := quo<O | pk>;
    return (qP(w)) @@ qP;
  end function;  



  if IsRamified(P) or 
     exists{x: x in Decomposition(O, p) | x[2] gt 1} or
     not IsSimple(NumberField(O))  or
     Valuation(LeadingCoefficient(DefiningPolynomial(O)), p) ne 0
     or Valuation(Discriminant(DefiningPolynomial(O))/Discriminant(O), p) gt 0 then

   vprint LocalRing, 1: "complicated";
   /* Precision: we have 3 different notions of precision
    * in Z_p and the unramified part Up:
      - precision is unram_prec := Ceil(prec/e)
      in the ramified part Rp:
      - precision is prec
      in the number field (ring):
      - precision is prec, always, but measured in P^prec
        (powers of the prime ideal)
      In the local rings, precisino is in powers of the uniformizer

      Of course, all of this in duplicate since we need the user
      precision and the minimal precision to make the system work.  
    */    

   pi := PrimitiveElement(P);
   ed := ElementaryDivisors(TraceMatrix(O));
   pr := Valuation(ed[#ed-1], p) + Valuation(ed[#ed], p) +1;

   vprintf LocalRing, 1: "Minimal Precision is %o=%o*%o\n", pr*e, pr, e;

   F, mF := ResidueClassField(P);
   e := RamificationDegree(P);
   u_Prec := (Prec +e-1) div e;
   

   Zp := pAdicRing(p : Global:=false); // MUST(!) not modify independently existing structure
   if Degree(P) gt 1 then
     f := Polynomial(Integers(), DefiningPolynomial(F, GF(p)));
     function get_poly(I)
       local prZ;
       prZ := Zp`DefaultPrecision;
       AssertAttribute(Zp, "DefaultPrecision", I);
       ff := Polynomial(Zp, f);
       AssertAttribute(Zp, "DefaultPrecision", prZ);
       return ff;
     end function;
     mp_f := map<Integers() -> PolynomialRing(Zp) | n:->get_poly(n)>;
     Up := ext<Zp|mp_f>;
     r := Lift(f, F.1@@mF, P, e*pr);
   else
     Up := Zp;
     f := Polynomial(Integers(),[0,1]);
     r := F.1@@mF;
   end if;
   Up`DefaultPrecision := u_Prec;

   to_O_get, to_O_set := NewEnv(["Prec", "Alpha"]);
   to_O_set("Prec", pr);
   to_O_set("Alpha", r);

   function mpUp_to_O(E)
     local pr, r;
     if f eq 1 then
       return Integers()!E;
     end if;

     if IsWeaklyZero(E) then 
       return O!0;
     end if;

     pr := Precision(E)*RamificationDegree(P);
       // precision in O should always be * e! (as was discovered many times)
     ppr := to_O_get("Prec");

     if pr gt ppr then
       vprintf LocalRing, 2: "Increasing Up to %o=%o*%o from %o\n", 
                                                      pr*1, pr, 1, ppr;
       r := Lift(f, F.1@@mF, P, e*pr); // careful: in the number field
       // we always work in the ramified extensions, kind of, so precision 
       // here is always(?) measured in pr*e.
       // see example 3.
       to_O_set("Alpha", r);
       to_O_set("Prec", pr);
     elif pr lt ppr then
       vprintf LocalRing, 2: "Decreasing Up to %o=%o*%o from %o\n", 
                                                      pr*1, pr, 1, ppr;
       r := to_O_get("Alpha") mod P^(1*pr);
     else
       r := to_O_get("Alpha");
     end if;
     E := Eltseq(E);
     return Evaluate(Polynomial(Integers(), E), r);
   end function;

   g := MinimalPolynomial(pi);
   if false and Degree(g) eq RamificationDegree(P) then
     mp_g := map<Integers() -> PolynomialRing(Up) | n :-> g>;
     Rp := ext<Up | mp_g>;
   else
     Pk := P^(e*pr);
     l := [1, pi];
     for i in [2..e-1] do
       Append(~l, (pi*l[#l]) mod Pk);
     end for;
     s := [O|1];
     r := Lift(f, F.1@@mF, P, e*pr);
     for i in [2..Degree(P)] do
       Append(~s, (r*s[#s]) mod Pk);
     end for;

     L := [ (i*j) mod Pk : i in s, j in l];
     Append(~L, (pi*l[#l]) mod Pk);
     L := [ ChangeUniverse(Eltseq(x), Integers()) : x in L];
     L := Matrix(L);
     L := VerticalJoin(L, BasisMatrix(Pk));
     n := NullspaceMatrix(L);
     i := 1;
     while n[i][e*Degree(P)+1] mod p eq 0 do
       i+:= 1;
     end while;
     n := Eltseq(n[i]);
     function do_poly(I)
       local prU, prZ;
       prU := Up`DefaultPrecision;
       prZ := Zp`DefaultPrecision;
       AssertAttribute(Up, "DefaultPrecision", I);
       AssertAttribute(Zp, "DefaultPrecision", I);
       nn := [ Up!n[1+i*Degree(P)..(i+1)*Degree(P)] : i in [0..e]];
       nn[#nn] := Up!Eltseq(nn[#nn])[1];
       assert IsUnit(nn[#nn]);
       u := 1 div nn[#nn];
       nn := [i*u : i in nn];
       f := Polynomial(nn);

       AssertAttribute(Up, "DefaultPrecision", prU);
       AssertAttribute(Zp, "DefaultPrecision", prZ);
       return f;
     end function;

     Up`DefaultPrecision := pr;
     mp_g := map<Integers() -> PolynomialRing(Up) | i :-> do_poly(i)>;

     Rp := ext<Up | mp_g>;
     Rp`DefaultPrecision := pr*e;
     

     f := Polynomial([mpUp_to_O(x) : x in Eltseq(DefiningPolynomial(Rp))]);
     // we need f to be at pr*e at least - otherwise the lifting
     // may not work: (Nils)
     /* <example>
        K<a>:=NumberField(x^15-6*x^14+19*x^13-32*x^12-x^11+42*x^10+
                 5*x^9+36*x^8-31*x^7- 134*x^6+35*x^5-8*x^4-x^3+10*x^2+5*x-4);

        g:=1/385700720*(23068377*a^14 - 102389649*a^13 + 251308944*a^12 -
          227335896*a^11 - 646129365*a^10 + 83289153*a^9 + 1400645764*a^8 +
          2332132464*a^7 + 1165112729*a^6 - 3048648177*a^5 - 4849030848*a^4 -
          3462545824*a^3 - 708601773*a^2 - 134849143*a + 184037260);

        OK:=IntegerRing(K);

        P:=g*OK;

        Completion(K,P);

        <//example>
     */


     s := Lift(f, pi, P, e*pr);

     R_to_O_get, R_to_O_set := NewEnv(["Prec", "Alpha"]);
     R_to_O_set("Prec", pr*e);
     R_to_O_set("Alpha", s);

     function mpRp_to_O(E)
       local pr, r;

       if IsWeaklyZero(E) then 
         return O!0;
       end if;
       pr := Precision(E);
       ppr := R_to_O_get("Prec");
       s := R_to_O_get("Alpha");
       Rp_cprec := CoefficientRing(Rp)`DefaultPrecision;
       AssertAttribute(CoefficientRing(Rp), "DefaultPrecision", (pr+e-1) div 1 );

       if pr gt ppr then
         vprint LocalRing, 2: "Increasing inverse Rp to ", pr, "was", ppr;
         f := Polynomial([mpUp_to_O(x) : x in Eltseq(DefiningPolynomial(Rp))]);
         s := Lift(f, s, P, pr); 
         R_to_O_set("Alpha", s);
         R_to_O_set("Prec", pr);
       elif pr lt ppr then
         vprint LocalRing, 2: "Decreasing inverse Rp to ", pr;
         s := Mod(s, P^(pr));
         //s := s mod P^pr;
         //to_O_set("Alpha", r);
       end if;
       E := Eltseq(E);
       AssertAttribute(CoefficientRing(Rp), "DefaultPrecision", Rp_cprec);
       return Evaluate(Polynomial([mpUp_to_O(x) : x in E]), s);
     end function;

     // OK, now for the inverse maps...
     // we'll do linear algebra to start with and then lifting (I think)
     f := Degree(P);
     function LinAlg(pr)
//       "LinAlg(", pr, ");";
       old_pr := Up`DefaultPrecision;
       old_bpr := Zp`DefaultPrecision;
       AssertAttribute(Up, "DefaultPrecision", (pr +e-1) div e);
       AssertAttribute(Zp, "DefaultPrecision", (pr +e-1) div e);
       bU := [Up!1];
       for i in [2..f] do
         Append(~bU, bU[i-1]*Up.1);
       end for;
       bR := [Rp!1];
       for i in [2..e] do
         Append(~bR, ChangePrecision(bR[i-1]*Rp.1, pr));
         //think about this: problem is that powers of e gain precision
         //which, while nice, slows down things later on
         //Take Nils's example...
       end for;
       bU := [mpUp_to_O(x) : x in bU];
       bR := [mpRp_to_O(x) : x in bR];
       bL := [ i*j : i in bU, j in bR];
       b := Basis(O, O);
       if true or #bL ne #b then
         PP := P^pr;
         m1 := Matrix(Integers(Minimum(PP)), [Eltseq(x) : x in bL]);
         m1 := VerticalJoin(m1, Matrix(Integers(Minimum(PP)), 
                                BasisMatrix(P^(pr))));
         m2 := IdentityMatrix(Integers(Minimum(PP)), Degree(O));
         fl, m1 := IsConsistent(m1, m2);
         assert fl;
       else
         m1 := Matrix([Eltseq(x) : x in bL]);
         m1 := m1^-1;
       end if;
       im := [];
       for i in [1..Nrows(m1)] do
         x := Eltseq(m1[i])[1..e*f];
         x := Rp![Up!x[j*f+1..(j+1)*f] : j in [0..e-1]];
         Append(~im, x);
       end for;
       AssertAttribute(Up, "DefaultPrecision", old_pr);
       AssertAttribute(Zp, "DefaultPrecision", old_bpr);
       return im;
     end function;
     im := LinAlg(pr*e);

     O_to_R_get, O_to_R_set := NewEnv(["Prec", "Im", "Pols", "Corr"]);
     O_to_R_set("Prec", pr*e);
     O_to_R_set("Im", im);
     O_to_R_set("Pols", false);

     function mpO_to_Rp(E)
       local pr, r, im;

       pr := Rp`DefaultPrecision;
       ppr := O_to_R_get("Prec");
       im := O_to_R_get("Im");
       if pr gt ppr then
         vprint LocalRing, 2: "Increasing Rp to ", pr;
         if true then
           im := LinAlg(pr);
         else
           pols := O_to_R_get("Pols");
           if pols cmpeq false then
             pols := [ MinimalPolynomial(x) : x in Basis(O)];
             O_to_R_set("Pols", pols);
             corr := Maximum([ Valuation(Evaluate(Derivative(pols[i]), 
                                          Basis(O)[i]), P) : i in [1..#pols]]);
             O_to_R_set("Corr", corr);
             "Corr: ", corr; // does not work...
             error "";
           else
             corr := O_to_R_get("Corr");
           end if;
           z := Rp`DefaultPrecision;
           AssertAttribute(Rp, "DefaultPrecision",  z+corr); 
           im := [ HenselLift(Polynomial(Rp, pols[i]), im[i]) :
                                                 i in [1..Degree(O)]];
//             for i in [1..Degree(O)] do
//               Valuation(Evaluate(pols[i], im[i]));
//             end for;
           AssertAttribute(Rp, "DefaultPrecision",  z); 
         end if;
         O_to_R_set("Im", im);
         O_to_R_set("Prec", pr);
       elif pr lt ppr then
         vprint LocalRing, 2: "Decreasing Rp to ", pr;
         im := [ChangePrecision(x, pr) : x in im];
         // reduce
       end if;
       E := Eltseq(E);
       old_pr := Up`DefaultPrecision;
       old_bpr := Zp`DefaultPrecision;
       AssertAttribute(Up, "DefaultPrecision", (pr+e-1) div e);
       AssertAttribute(Zp, "DefaultPrecision", (pr+e-1) div e);
       im :=  &+ [ E[i]*im[i] : i in [1..Degree(O)]];
       AssertAttribute(Up, "DefaultPrecision", old_pr);
       AssertAttribute(Zp, "DefaultPrecision", old_bpr);
       return im;
     end function;
 
     m := map<FieldOfFractions(O) -> Rp | x :-> mpO_to_Rp(x), y:-> mpRp_to_O(y)>;
     m`IsHomomorphism := true;
     Rp`DefaultPrecision := Prec;
     Up`DefaultPrecision := u_Prec;
     return Rp, m;
   end if;

               /********************************************/
  else         /* the easy case                            */
               /********************************************/
    F, mF := ResidueClassField(P);
    f := DefiningPolynomial(F, PrimeField(F));
    f := Polynomial(Integers(), f);
    R := pAdicRing(p : Global:=false); // MUST(!) not modify independently existing structure
    mp := map<Integers() -> PolynomialRing(R) | n :-> Polynomial(R, f)>;
    Qf := ext<R|mp>;
    if Prec gt 0 then
      Qf`DefaultPrecision := Prec;
      R`DefaultPrecision := Prec;
    else
      Prec := 20;
    end if;

    alpha := PrimitiveElement(NumberField(O));
    d := LeadingCoefficient(DefiningPolynomial(O));
    alpha *:= d;
    alpha := O!alpha;
    d := Modinv(d, p);
    alpha *:= d;
    alpha := alpha mod (p*O);

    // now alpha (together with Lift) should give the map from the Order
    // to Qf.
    // To go from Qf to O we have to lift alpha as a root of the defining
    // Poly of Qf (over Z) in O to whatever precision is desired.
    // The other direction should be alpha -> Qf.1 lifted...

    get, set := NewEnv(["Prec", "Lift", "Pk", "pLift", "pPrec"]);
    a := Generator(F, PrimeField(F))@@mF;
    a := Lift(f, a, P, Prec);
    Pk := P^Prec;
    set("Prec", Prec);
    set("Lift", a);
    set("Pk", Pk);
    b := HenselLift(Polynomial(Qf, DefiningPolynomial(O)), Qf!ResidueClassField(Qf)!Eltseq(mF(alpha), PrimeField(F)));
    set("pLift", b);
    set("pPrec", Prec);

//    FE := FieldOfFractions(EquationOrder(O));
    FE := NumberField(O);
    function O_to_Qf(e)
      e := FE!e;
      ppr := get("pPrec");
      pr := Qf`DefaultPrecision;
      old_pr := R`DefaultPrecision;
      AssertAttribute(R, "DefaultPrecision", pr);
      a := get("pLift");
      if ppr gt pr then
        Pk := P^pr;
        ChangePrecision(~a, pr);
        set("pLift", a);
        set("pPrec", pr);
      elif ppr lt pr then
        a := HenselLift(Polynomial(Qf, DefiningPolynomial(O)), a);
        set("pLift", a);
        set("pPrec", pr);
      else
        a := get("pLift");
      end if;
      d := Denominator(e); 
      assert GCD(d, p) eq 1;
      z := Evaluate(Polynomial(Integers(), Eltseq(e*d)), a)/d;
      AssertAttribute(R, "DefaultPrecision", old_pr);
      return z;
    end function;

    function Qf_to_Q(e)
      p := get("Prec");
      pr := Qf`DefaultPrecision;
      a := get("Lift");
      if p gt pr then
        Pk := P^pr;
        a := a mod Pk;
        set("Lift", a);
        set("Pk", Pk);
        set("Prec", pr);
      elif p lt pr then
        a := Lift(f, a, P, pr);
        Pk := P^pr;
        set("Lift", a);
        set("Pk", Pk);
        set("Prec", pr);
      else
        a := get("Lift");
      end if;
      return Evaluate(Polynomial(Z, Eltseq(e)), a);
    end function;

    m := map<O -> Qf | x :-> O_to_Qf(x), y :-> Qf_to_Q(y)>;
    m`IsHomomorphism := true;
    return Qf, m;
  end if;

end intrinsic;


function _Completion(P, Prec)
// the completion of Order(P) at P up to a precision of Prec 
// together with the embedding
    return a,b where a,b := LocalRing(P, Prec);
end function;  

// the next two are for comp<O | ideal>
//
intrinsic IntegerRing(O::RngOrd) -> RngOrd
{Returns the order O}
  return O;
end intrinsic;

intrinsic Completion(O::RngOrd, P::RngOrdIdl : Precision := false) -> RngPad, Map
{Returns the completion of O at P}
  require O eq Order(P) : "Argument 1 must be the order of argument 2";
  require IsAbsoluteOrder(O) : "The ideal must belong to some absolute order";
  require IsPrime(P) : "The ideal must be prime";
  require IsMaximal(O) or RamificationDegree(P) eq 1 : "For ramified primes the order must be maximal";

  if Precision cmpeq false then
      Precision := 20;
  end if;

  return a,b where a,b := _Completion(P, Precision);
end intrinsic;

_NumberField := function(K)
  if ISA(Type(K), FldNum) then return K; 
  else return NumberField(K);
  end if;
end function;  

intrinsic Completion(K::FldAlg, P::RngOrdIdl: Precision := false, UseRelPrec := true) -> RngPad, Map
{Completion of K at P}
  require IsAbsoluteField(K) : "Field must be a direct extension of Q";
  require IsPrime(P) : "Ideal must be a prime ideal";
  O := Order(P);
  require IsMaximal(O) or RamificationDegree(P) eq 1 :
                      "Order must be maximal or the ideal unramified";
  require NumberField(O) eq _NumberField(K): 
                      "Ideal and field are not compatible";

  if Precision cmpeq false then
      Precision := 20;
  end if;

  R, M := _Completion(P, Precision);
  FR := FieldOfFractions(R);
  
  im := function(x)
    x := FieldOfFractions(O)!x;
    Rdef := R`DefaultPrecision;
    FRdef := FR`DefaultPrecision;
    AssertAttribute(R, "DefaultPrecision", FRdef);
    if UseRelPrec then
      v := IsZero(x) select 0 else Valuation(x, P);
      xd := Denominator(x);
      if xd eq 1 then
        AssertAttribute(R, "DefaultPrecision", FRdef+v);
        AssertAttribute(FR, "DefaultPrecision", FRdef+v);
        x := FR!M(O!x);
      else
        xd := O!xd;
        xn := O!(x*xd);
        vd := Valuation(xd, P);
        v1 := Max(vd, v+vd); // = valuations of xd, xn
        AssertAttribute(R, "DefaultPrecision", FRdef+v1);
        AssertAttribute(FR, "DefaultPrecision", FRdef+v1);
        xnFR := FR!M(xn);
        xdFR := FR!M(xd);
        x := xnFR/xdFR;
      end if;
    else
      xd := Denominator(x);
      if xd eq 1 then
        x := FR!M(O!x);
      else
        xd := O!xd;
        xn := O!(x*xd);
        vd := Valuation(xd, P);
        if vd gt 0 then
          AssertAttribute(R, "DefaultPrecision", FRdef+vd);
          AssertAttribute(FR, "DefaultPrecision", FRdef+vd);
        end if;
        xn := FR!M(xn);
        xd := FR!M(xd);
        x := xn/xd;
      end if;
    end if; // UseRelPrec
    AssertAttribute(R, "DefaultPrecision", Rdef);
    AssertAttribute(FR, "DefaultPrecision", FRdef);
    return x;
  end function;
  
  e := RamificationDegree(P);
  pre := function(y)
    v := Valuation(y);
    if not IsFinite(v) then return K!0; end if; 
    pi := FR!UniformizingElement(R);
    if v ne 0 then     
      xn := y*pi^-v;
      xd := K!(pi@@M)^v;
    else
      xn := y;
      xd := K!1;
    end if;
    x := K!(xn@@M)*xd;
    _, c:= Valuation(Denominator(x), Minimum(P));
    cc := Modinv(c, Minimum(P)^((FR`DefaultPrecision +e -1) div e));
    x *:= c*cc;
    return x;
  end function;
  m := map<K -> FR | x:-> im(x), y:-> pre(y)>;
  m`IsHomomorphism := true;
  return FR, m;
end intrinsic;

intrinsic Completion(K::FldAlg, P::PlcNumElt: Precision := false, UseRelPrec := true) -> RngPad, Map
{Completion of K at P}
  require IsAbsoluteField(K) : "Field must be an extension of Q";
  require IsFinite(P) : "P must be a finite place of K";
  P := Ideal(P);
  O := Order(P);
  require NumberField(O) eq _NumberField(K): 
                      "Place and field are not compatible";

  return Completion(K, P:Precision := Precision, UseRelPrec := UseRelPrec);

end intrinsic;
