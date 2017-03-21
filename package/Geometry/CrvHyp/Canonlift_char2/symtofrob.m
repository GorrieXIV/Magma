freeze;

/********************************************************

  Functions to compute the characteristic polynomial of 
  frobenius (for genus >= 3) given the minimal polynomial
  of the "beta" parameter of a (char 2) hyperelliptic
  curve:
    beta = (l_1 * l_2 * .. l_g) + q^g/(l_1 * .. * l_g)
  where l_1, .. , l_g are the frobenius e-values which
  are 2-adic units for some 2-adic embedding.
  
  The functions may fail to give a result if the
  Jacobian decomposes badly. Cases covered are
  a) all genus 3 cases.
  b) the "general" case - almost certain for q large.
  c) J isogenous to a product of isomorphic elliptic 
      curves over GF(q^infinity).
      
         Mike Harrison 01/2004
      
********************************************************/

/********** CONDITION JAC *******************************

  In the functions below, possibilities for the char poly,
  P_J, of the Jacobian of C, Jac(C), are computed.
  Jac(C) is an ordinary abelian variety, so the same is 
  true for each of its simple factors.
  We have an additional condition though: we know that
  over the basefield, k, Jac(C) actually has all of
  its 2^g 2-torsion points defined, and the same
  holds for its quadratic twist.
  It can then be seen that each simple factor A, and its
  twist, is k-isogenous to an abelian variety with all of
  its 2-torsion defined over k.
  This means that - if dim(A) = d - then #A(k) and #A'(k)
  must be divisible by 2^d. This gives the following
  condition on factors of the char poly of Jac(C):
  
  (JAC): If f is an irreducible factor of degree d of P_J
         then f(1)=f(-1)=0 mod 2^d.
	 
*******************************************************/
          
function SymToChar(spols,q)

    g := Degree(spols[1]);
    x := Parent(spols[1]).1;
    polx := x^2 + q;
    return
    [ &+[ Coefficient(spol,i)*(polx^i)*(x^(g-i)) : i in [0..g]] :
                                         spol in spols];

end function;

function Deg1Case(c,q,g)

    /*
       Here, Jacobian(C) ~ E^g where E is an elliptic curve
       over GF(q^N), some N.
       For condition (JAC), we use the fact that if z is a
       root of unity in the algebraic closure of the 2-adic
       field, then z = 1 mod 2 iff z = 1 or -1.
    */

    assert IsOdd(c)and (c^2 lt 4*(q^g));
    PR := PolynomialRing(IntegerRing()); x := PR.1;
    facts := Factorization(x^(2*g)+((c mod 4)-2)*c*(x^g)+(q^g));
    r := (Minimum([Degree(p[1]) : p in facts])) div 2;
    // the following assertion comes from condition (JAC)
    assert (r eq 1) or (IsEven(r)and IsDivisibleBy(g,r));
    drfacts := [p[1] : p in facts | (Degree(p[1]) eq 2*r)];
    pol := x^(2*r)+(q^r);
    drfacts := [f : f in drfacts | ((a mod 4) eq 3) and
           (f eq pol+(a*x^r)) where a is Coefficient(f,r)];
    assert #drfacts eq 1;
    //NB. That the below give the only possibilities for
    // char poly Jac(C) comes from condition (JAC).
    // a stronger 2-torsion analysis shows that r = power of 2. 
    if r gt 1 then
        assert r eq 2^Valuation(r,2); 
        assert ((1+Coefficient(drfacts[1],r)) mod 2^r) eq 0;
        return true,[drfacts[1]^(g div r)];
    else
        p1 := drfacts[1]; p2 := Evaluate(p1,-x);
        return true,[(p1^(g-i))*(p2^i) : i in [0..g]];
    end if;

end function;

function Deg2Case(Psym,q)

    /*
       Here, Jacobian(C) ~ A2 x E where E is an elliptic curve
       and A2 is a 2-dim abelian variety which is isogenous to
       the product of an elliptic curve E1 with itself over
       GF(q^2) - E is not isogenous to E1.
    */
    a := Coefficient(Psym,1);
    boo,b := IsDivisibleBy(Coefficient(Psym,0),q);
    assert (boo and IsOdd(a) and IsOdd(b));
    boo,E := IsSquare((b+4*q^2)^2-4*q*a^2);
    assert boo;
    r := (b+E) div 2;
    if IsEven(r) then r -:= E; end if;
    assert Abs(r) lt 2*q^2;
    boo,v := IsSquare(r+2*q^2);
    assert boo;
    v *:= (-1)^((v mod 4)div 2); // square root = 1 mod 4
    boo,u := IsDivisibleBy(a,v);
    assert boo and (u^2 lt 4*q);
    IP := PolynomialRing(IntegerRing()); x := IP.1;
    pols2 := [x^2-u*x+q,x^2+u*x+q];
    boo,r1 := IsSquare(v+2*q);
    if boo then //E1 defined over GF(q)
      pols1 := [(x^2 + r1*x + q)^2,(x^2 - r1*x + q)^2,
                              x^4 + (2*q-r1^2)*x^2 + q^2];
    else //E1 not defined over GF(q)
      pols1 := [ x^4 - v*(x^2) + q^2 ];
    end if;
    pols := [p1*p2 : p1 in pols1, p2 in pols2];
    // Note that, by (JAC), in the A2xE case we can
    // exclude (from pols1) the possible polys for A2:
    //            x^4 + v*x^2 + q^2 and
    //    x^4 +/- r1*x^3 + r1^2*x^2 +/- q*r1*x +q^2
    return true,pols;

end function;

function PolySquareRts(h,q)

    g := Degree(h);
    x := Parent(h).1;
    u := ResidueClassRing(2^g)!(1+q);
    sfacts := Factorization(h);
    facts := [];
    for i in [1..#sfacts] do
        assert sfacts[i][2] eq 1;
        pair := Factorization(Evaluate(sfacts[i][1],x^2));
        assert (#pair eq 2);
        deg := Degree(pair[1][1]);
        if (2^(g-deg)*Evaluate(pair[1][1],u)) eq 0 and
           (2^(g-deg)*Evaluate(pair[2][1],u)) eq 0 then
        // Condition (JAC) for this factor
            Append(~facts,[pair[1][1],pair[2][1]]);
        end if;
    end for;
    assert #facts gt 0;
    delete sfacts;
    posspols := [];
    u := ResidueClassRing(2^g)!(1+q);
    for i in [0..(2^#facts)-1] do
        bits := a cat [0: j in [#a..#facts-1]] where a is Intseq(i,2);
        pol := facts[1][bits[1]+1];
        for j in [2..#facts] do
           pol := pol * facts[j][bits[j]+1];
        end for;
         Append(~posspols,pol);
    end for;
    return true,SymToChar(posspols,q);

end function;

function GenCase(Psym,q,g)

    //NB. Assumption that q >= 4 is made.

    n := Valuation(q,2);
    if g le 2*q then
        N := 1 + g*(n+1);
    else
        N := (g-i)*(n+1) + 1 + Ceiling(Log(2,Binomial(g,i)))
                         where i is g div (2*q+1);
    end if;
    d := Degree(Psym) - 1;
    R := pAdicQuotientRing(2,N + n*d);
    PR := PolynomialRing(R); x := PR.1;
    u_sym := HenselLift(PR!Psym,R!1);
    pol := [a[i+1] div q^(d-i) where a is
               Coefficients((PR!Psym) div (x-u_sym)) : i in [0..d]];
    ChangePrecision(~R,N);
    PR := PolynomialRing(R); x := PR.1;
    u_sym := R!u_sym;
    pol := PR!pol;
    u := HenselLift(x^2 - u_sym*x + q^g, u_sym);
    
    _,d1 := Min([Valuation(a) : a in Coefficients(pol)]);
    d1 -:= 1; d  -:= d1;
    assert d le g;
    if d lt g-1 then return false,_ ; end if;
    if d1 gt 0 then
        pol := (HenselLift(pol,[ PR![Coefficient(pol,i) : i in [d1..d+d1]],
                                                                 x^d1]))[1];
    end if;
    pol := (HenselLift( &+[ Coefficient(pol,i)*(qpol^i)*(x^(d-i))
                           where qpol is x^2+q^(g-2) : i in [0..d]],
                                       [pol,x^d]))[1];
    if d lt g then
        pol := pol * (x + ((-1)^g)*((u^(g-2)) div Coefficient(pol,0)));
    end if;

    pol := PR!Reverse(Coefficients(Evaluate(pol,u*x)));
    pol := pol/LeadingCoefficient(pol);

    pol := pol * (pol1/LeadingCoefficient(pol1))
            where pol1 is PR!Reverse(Coefficients(Evaluate(pol,(q^2)*x)));
    
    pol := [Coefficient(pol,i) : i in [deg-g..deg]] where deg is Degree(pol);
    h := [R!1,pol[g]];
    for j in [2..g] do
       Append(~h, pol[g+1-j] -
          &+[Binomial(g+2*t-j,t)*(q^(2*t))*h[j+1-2*t] : t in [1..j div 2]]);
    end for;
    qpow := 2^(N-1);
    h := PolynomialRing(IntegerRing())!
       [ (a le qpow) select a else a-2*qpow where a is 
           IntegerRing()!h[g+1-i] : i in [0..g] ];
    h := Evaluate(h,Parent(h).1 - 2*q);
    return PolySquareRts(h,q);
    
end function;

function PsymToFrob(Psym,q,g)

    if Degree(Psym) eq 1 then
        return Deg1Case(Coefficient(Psym,0),q,g);
    end if;
    if (Degree(Psym) eq 2) and (g eq 3) then
        return Deg2Case(Psym,q);
    end if;
    // general case.
    if Degree(Psym) ge g then
        return GenCase(Psym,q,g);
    end if;
    return false,_;

end function;
