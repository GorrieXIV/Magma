freeze;

///////////////////////////////////////////////////////////////////////
//                                                                   //
//             S-INTEGRAL POINTS ON GENUS ONE CURVES                 //
//                                                                   //
//                    Emanuel Herrmann, 1999                         //
//                                                                   //
///////////////////////////////////////////////////////////////////////

// Intrinsics for finding S-integral points on quartic hyperelliptic curves, 
// Desboves curves, and Ljunggren curves (see below for definitions).  
// The intrinsic names identify the curve model in lieu of a type check 
// on the curve:
//   IntegralQuarticPoints
//   SIntegralQuarticPoints
//   SIntegralLjunggrenPoints
//   SIntegralDesbovesPoints

import "sintpoints.m" : MWFreeBasis, height_difference_bounds;

function TorsionElements(E)
  T, TtoE := TorsionSubgroup(E);
  return [t@TtoE : t in T];
end function;

function IsSIntegral(x, S)
  if IsEmpty(S) then
    return IsIntegral(x);
  end if;
  s := LCM(S);
  d := Denominator(x);
  g := GCD(d, s);
  while g ne 1 do
    d := d div g;
    g := GCD(d, s);
  end while;
  return d eq 1;
end function;

///////////////////////////////////////////////////////////////////////
//                                                                   //
//                 Linear Combinations of Points                     //
//                                                                   //
///////////////////////////////////////////////////////////////////////

function PointLinearCombinations(G, n)

    E := Curve(Universe(G));
    // require n ge 0: "Argument 2 must be nonnegative";

    PreCalc:= function(E, G, n)
	L := [];
	L1 := [];
	for c in [1..#G] do
	    P := G[c];
	    if c eq 1 then
		lower:=0;
	    else
		lower:=-n;
	    end if;
	    for i in [lower..n] do
	       Append(~L1,i*P);
	    end for;
	    Append(~L,L1);
	    L1:= [];
	end for;
	return L;
    end function;

    Rank3Combs := function(E,G,T,n)
	Sols := [];
	lc := [];
	for i in [0..n] do
	   iP := i*G[1];
	   for j in [-n..n] do
	      jP := j*G[2];
	      for k in [-n..n] do
		 kP := k*G[3];
		 nP := iP+jP+kP;
		 x:=[i,j,k];
		 tv:= 0;
		 for Tp in T do
		    tP := nP+Tp;
		    tv +:= 1;
		    if tP notin Sols then
		       Append(~Sols, tP);
		       Append(~x,tv);
		       Append(~lc,x);
		    end if;
		end for;
	     end for;
	  end for;
       end for;
       return Sols, lc;
    end function;

    Rank4Combs := function(E, G, Tors, n)
	Precalc := PreCalc(E,G, n);
	Sols := [];
	lc:=[];

	for i in [0..n] do
	    iP := Precalc[1][i+1];
	    for j in [-n..n] do
		jP := Precalc[2][j+n+1];
		for k in [-n..n] do
		    kP := Precalc[3][k+n+1];
		    for l in [-n..n] do
			lP := Precalc[4][l+n+1];
			nP := iP+jP+kP+lP;
			x := [i,j,k,l];
			for T in Tors do
			    tP:=nP+T;
			    if tP notin Sols then
				Append(~Sols, tP);
				Append(~lc,x);
			    end if;
			end for;
		    end for;
		end for;
	    end for;
	end for;
	return Sols, lc;
    end function;

    T := TorsionElements(E);

    if #G eq 0 then
        return [T,[]];
    end if;

    if #G eq 3 then
       return Rank3Combs(E,G,T,n);
    end if;

    if #G eq 4 then
       return Rank4Combs(E,G,T,n);
    end if;

    A := [[]];
    B := [];
    Points := [ ];
    COMBS := [ ];

    for i in [1..#G] do
       if i eq 1 then
          lower:=0;
       else
          lower:=-n;
       end if;
       for j in [lower..n] do
          for elt in A do
             elt2 := Append(elt,j);
             Append(~B,elt2);
          end for;
       end for;
       s := #B[1];
       for elt in B do
          P := E!0;
          for k in [1..s] do
             P +:= elt[k]*G[k];
             torsc:=0;
             for tors in T do
                P1 := P + tors;
                torsc +:= 1;
                if P1 notin Points then
                   Append(~Points,P1);
                   elt2 := elt;
                   for z in [1..#G-#elt] do
                      Append(~elt2,0);
                   end for;
                   Append(~elt2,torsc);
                   Append(~COMBS, elt2);
                end if;
             end for;
          end for;
       end for;
       delete A;
       A := B;
       delete B;
       B := [];
    end for;
    return Points;
end function;

///////////////////////////////////////////////////////////////////////
//                                                                   //
//             Integral Points on Hyperelliptic Quartic              //
//                 y^2 = ax^4 + bx^3 + cx^2 + dx +e                  //
//                                                                   //
///////////////////////////////////////////////////////////////////////

// New signature to allow point with rational coords (added Jan 2009, SRD)

intrinsic IntegralQuarticPoints(Q::[RngIntElt], P::[FldRatElt]) -> SeqEnum
   {Returns the sequence of integral points on the quartic curve
   y^2 = ax^4 + bx^3 +cx^2 + dx + e, where Q = [a,b,c,d,e] and P
   is a rational point not equal to [0,1,0].}

   if not &and [IsCoercible(Integers(), p) : p in P] then 
     if #P eq 2 then Append(~P,1); end if;
     den := LCM([ Denominator(P[i]) : i in [1,2] ]);
     P := [p*den : p in P];
   end if;
   return IntegralQuarticPoints(Q, ChangeUniverse(P,Integers()) );

end intrinsic;

intrinsic IntegralQuarticPoints(Q::[RngIntElt], P::[RngIntElt]) -> SeqEnum
   {"} // "

IsOnCurve:= function(Q, P)
    if #P gt 3 or #P lt 2 then
        return false;
    end if;
    if #P eq 3 then
        z:= P[3];
        if z eq 0 then
            return true;
        end if;
    else
        z:= 1;
    end if;
    a,b,c,d,e := Explode(Q);
    x:= P[1]/z;
    y:= P[2]/z;
    if a*x^4 + b*x^3 + c*x^2 + d*x + e - y^2  eq 0 then
        return true;
    end if;
    return false;
end function;

    require IsOnCurve(Q,P): "Argument 2 is not on curve";

    a,b,c,d,e := Explode(Q);

    PR := PolynomialRing(Rationals()); U := PR.1;
    f:= a*U^4 + b*U^3 + c*U^2 + d*U + e;
    z:= 1;
    if #P eq 3 then
        z:= P[3];
    end if;
    require z ne 0:
        "point at infinity is not allowed";

    x:= P[1]/z;
    xnum:= Numerator(x);
    xden:= Denominator(x);

    g:=Evaluate(f,(U+xnum)/xden)*xden^4;

    a1:= Integers()!Coefficient(g,4);
    b1:= Integers()!Coefficient(g,3);
    c1:= Integers()!Coefficient(g,2);
    d1:= Integers()!Coefficient(g,1);
    e1:= Integers()!Coefficient(g,0);

    L:= IntegralQuarticPoints([a1,b1,c1,d1,e1]);
    L1:= [ ];
    for p in L do
        xp:= p[1];
        yp:= p[2];
        xn:= (xp + xnum)/xden;
        yn:= yp/xden^2;
        if IsIntegral(xn) then
           Append(~L1,[xn, yn]);
        end if;
    end for;
    return L1;
end intrinsic;

intrinsic IntegralQuarticPoints(Q::[RngIntElt]) -> SeqEnum
   {Returns the sequence of integral points on the quartic curve
   y^2 = ax^4 + bx^3 + cx^2 + dx + e, where Q = [a,b,c,d,e] and
   e is a square.}

   a,b,c,d,esq := Explode(Q);

   // y^2 =  a^2 x^4 + ...
   if IsSquare(a) then
      return SIntegralQuarticPoints(Q,[]);
   end if;

   // y^2 = a x^4 + c x^2 +  e
   if b eq 0 and d eq 0 then
      return SIntegralLjunggrenPoints([1,a,c,esq],[]);
   end if;

   // a lt 0
   if a lt 0 then
        P := PolynomialRing(Rationals()); x := P.1;
        f := a*x^4 + b*x^3 + c*x^2 + d*x + esq;
        fz := RealRoots(f, RealField(), 10^-10);
        L := [];
        if #fz ge 2 then
            lw := Floor(fz[1]);
            up := Ceiling(fz[2]);
            // printf "lower: %m\n",lw;
            // printf "upper: %m\n",up;
            for i in [lw..up] do
                blt,y:= IsSquare( Evaluate(f,i));
                if blt then
                   Append(~L, [i,y]);
                end if;
            end for;
        end if;

        if #fz eq 4 then
            lw := Floor(fz[3]);
            up := Ceiling(fz[4]);
            // printf "lower: %m\n",lw;
            // printf "upper: %m\n",up;
            for i in [lw..up] do
                blt, y := IsSquare( Evaluate(f,i));
                if blt then
                   Append(~L, [i,y]);
                end if;
            end for;
        end if;
        return L;
    end if;

   // y^2 = a x^4 + ... + e
   // here one has to find a rational point on the curve
   // in this case one has to call the function with
   // an point not equal [0,y]

   bool, e := IsSquare(esq); 
   require bool : "Last element of argument must be a square";

   // y^2 = a x^4 + ... + d x
   if esq eq 0 then
        Ais:= [0,c,0,d*b,d^2*a];
        PR := PolynomialRing(Rationals()); U := PR.1;

        f:= a*U^4 + b*U^3 + c*U^2 + d*U;

        require IsEllipticCurve(Ais):
            "curve must be non-singular.";

        E:= EllipticCurve(Ais);

        F:= MWFreeBasis(E);
        T:= TorsionElements(E);

        if #F eq 0 and #T eq 1 then
            return [[0,0]];
        end if;

        S := PointLinearCombinations(F, 4);
        L := [];

        for P in S do
            X:= P[1]; Y:=P[2]; Z:= P[3];
            if Z ne 0 then

                x:= X/d; y:= Y/d;
                if x ne 0 then

                    x:= 1/x; y:= y*x^2;

                    g:=Evaluate(f,(U+Numerator(x))/Denominator(x) )
                        *Denominator(x)^4;

                    if Coefficient(g,0) ne 0 then 
                        return IntegralQuarticPoints([a,b,c,d,0], [x,y]);
                    end if;
                end if;
            end if;
        end for;

        fz:= Roots(f);
        L:= [ ];
        for r in fz do
            if IsIntegral(r[1]) then
               Append(~L,[r[1],0]);
            end if;
        end for;
        return L;
    end if; // esq eq 0

    // GENERAL CASE STARTS HERE

    forward Sigma;

    // long WNF

    a1:= d/e;
    a2:= (4*esq*c - d^2)/(4*esq);
    a3:= 2*e*b;
    a4:= -4*esq*a;
    a6:= a*(d^2-4*esq*c);

    // b's

    b2:= a1^2+4*a2;
    b4:= 2*a4+a1*a3;
    b6:= a3^2+4*a6;

    // SWNF

    A := -c^2/3+b*d-4*esq*a;
    B := 2/27*c^3-1/3*b*c*d-8/3*esq*a*c+esq*b^2+a*d^2;

    require IsEllipticCurve([A,B]) :
       "Argument does not define a nonsingular curve.";

    // printf "curve is: %m\n", [A,B];

    // Point at infinity

    x0:= 2*e*a^(1/2)+c/3;

// some functions

Phi2:= function(E,P,n)
    l:= EllipticLogarithm(P : Precision := n)
           / RealPeriod(E : Precision := n);
    if l lt 0 then
        return l+1;
    else
        return l;
    end if;
end function;

Phi:= function(E, x_P, y_P, prec) //SNF only, P not a torsion point :)

    p:= Max(50,prec);

    R:= RealField(p);

    log:=R!0;

    a4:= R!aInvariants(E)[4];
    a6:= R!aInvariants(E)[5];

    a6:= R!2*a6;
    x:= R!x_P; y:=R!y_P;

    if Sign(y) lt 0 then
    log:= R!(1/2);
    end if;

    i:=1;

    while i lt prec do

    i +:= 1;

    t:= x^2;
    s:= a4 - t;
    t:= R!3*t + a4;
    y:= y+y;
    t:= t/y;

    s:= (x*s + a6)/y;
    x:= t*t-x-x;
    y:= -x*t-s;

    if Sign(y) lt 0 then
    log:= log+(R!1/2)^i;
    end if;
    end while;
    return log;
end function;

    Sigma:= function(a,b,c,d,e)

        if d*a^(1/2) +  e*b eq 0 then
            return Sign(8*e^3*a^(1/2)+4*e^2*c-d^2);
        else
            return Sign(d*a^(1/2)+e*b);
        end if;
    end function;

// Lemma 2, p. 30

    Getu01:= function(a,b,c,d,e)

        P := PolynomialRing(Rationals()); x := P.1;
        f:= a*x^4 + b*x^3 + c*x^2 + d*x + e^2;
        g:= (a*d^2-b^2*e^2)*x^3 + (b*d^2+8*e^2*a*d-4*e^2*b*c)*x^2+
            (c*d^2+2*e^2*b*d+16*e^4*a-4*c^2*e^2)*x+
            d^3+8*e^4*b-4*e^2*c*d;

        fz:= RealRoots(f, Rationals(), 10^-10);
        Append(~fz, 0);

        gz:= RealRoots(g, Rationals(), 10^-10);
        Append(~gz, 0);

        u1:= Max(fz);
        u2:= Max(gz);

        num:= b*e - d*a^(1/2);

        if num eq 0 then
            u3:= u1;
        else
            u3:= Max([u1, (d^2+8*e^3*a^(1/2)-4*e^2*c)/(4*e*num)]);
        end if;

        num:= 64*e^6*a-(4*e^2*c-d^2)^2;

        if num eq 0 then
            u4:= u1;
        else
            u4:= Max([8*e^2*(4*e^2*c*d-d^3-8*e^4*b)/num, u1]);
        end if;

        s:= Sigma(a,b,c,d,e);

        if s eq 1 then
            u0:= Max([u2,u4]);
        else
            u0:= Max([u2,u3,u4]);
        end if;

        return Ceiling(u0);

    end function;

// Lemma 7&8  p.

    Getu02:= function(a,b,c,d,e,A,B,u0)

    a1:= d/e;
    a2:= ( 4*esq*c - d^2 )/(4*esq);
    a3:= 2*e*b;
    a4:= -4*esq*a;
    a6:= a*(d^2-4*esq*c);

    b2:= a1^2+4*a2;
    b4:= 2*a4+a1*a3;
    b6:= a3^2+4*a6;

    sigma:= Sigma(a, b, c, d, e);


    Fun:= function(a, b, c, d, esq, b2, b4, b6, sigma, X)
        _,e := IsSquare(esq);
        num:= 4*esq*X+4*esq*c-d^2;
        den:= -d*X-2*esq*b;
        rad:= Abs(4*X^3+b2*X^2+2*b4*X+b6)^(1/2);
        den:= den + sigma*e*rad;
        return num/den;
    end function;

        P := PolynomialRing(Rationals()); x := P.1;
        q := x^3+A*x+B;  // SWNF
        qz := RealRoots(q,Rationals(),10^-10);
        qz := Sort(qz);

        if #qz eq 1 then
            e1:= qz[1];
            e1_prime:= e1 - c/3;

            v:= d*e1 - c*d/3 + 2*e^2*b;

            if v lt 10^-7 then
                e1_prime:= e1_prime+0.5;
            end if;

            U0:= Max(Fun(a, b, c, d, e^2, b2, b4, b6, sigma, e1_prime), u0);
            return Ceiling(U0);
        end if;

        e3:= qz[1]; e3_prime:= e3-c/3;
        e2:= qz[2]; e2_prime:= e2-c/3;

        dist:= (e2-e3)/Pi(RealField());;

        v1:= d*e3 - c*d/3 + 2*e^2*b;
        v2:= d*e2 - c*d/3 + 2*e^2*b;

        if v1 lt 10^-7 then
            e3_prime:= e3_prime+dist;
        end if;

        if v2 lt 10^-7 then
            e2_prime:= e2_prime-dist;
        end if;

        v1:= Fun(a, b, c, d, e^2, b2, b4, b6, sigma, e2_prime);
        v2:= Fun(a, b, c, d, e^2, b2, b4, b6, sigma, e3_prime);
        U0:= Max([v1, v2, u0]);
        return Ceiling(U0);
    end function;

    Getc9:= function(a, b, c, d, e, U0);
        P := PolynomialRing(Rationals()); x := P.1;
        g:= b*x^3+2*c*x^2+3*d*x+4*e^2;
        gx:= RealRoots(g, Rationals(), 10^-10);
        Append(~gx, U0);
        Append(~gx, 10^30);
        max:= 0;
        for p in gx do
           if p ge U0 then
              v:= p^2/(a*p^4+b*p^3+c*p^2+d*p+e^2)^(1/2);
              if v gt max then
                 max:= v;
              end if;
           end if;
        end for;
        return max;
    end function;

    Getc10:= function(a, b, c, d, e, A, B, U0)

        a1:= d/e;  a2:= ( 4*e^2*c - d^2 ) / (4*e^2); a3:= 2*e*b;
        a4:= -4*e^2*a; a6:= a*(d^2-4*e^2*c);

        E:= EllipticCurve([a1, a2, a3, a4, a6]);
        F,m,n:= MinimalModel(E);

        r:= IsomorphismData(m)[1];
        u:= IsomorphismData(m)[4];

        u:=u^2;

        k1:= Numerator(u);
        k2:= Denominator(u);

        l1:= Numerator(r);
        l2:= Denominator(r);

        g:= GCD([2*e*l2*k1, d*l2*k1, 2*l2*k1*e^2, k2*l1, l2*k2]);

        m1:= 2*e*l2*k1/g;
        m2:= d*l2*k1/g;
        m3:= 2*l2*k1*e^2/g;
        m4:= k2*l1/g;
        m5:= l2*k2/g;

        if m5 lt 0 then
            m5:= -m5;
            m1:= -m1;
            m2:= -m2;
            m3:= -m3;
            m4:= -m4;
        end if;

        P := PolynomialRing(Rationals()); x := P.1;

        f:= a*x^4+b*x^3+c*x^2+d*x+e^2;

        g:= (m5*x^2-m2*x-m3-m4*x^2)^2 - m1^2*f;
        h:= (m5*x^2+m2*x+m3+m4*x^2)^2 - m1^2*f;

        gz:= RealRoots(g, RealField(), 10^-10);
        hz:= RealRoots(h, Rationals(), 10^-10);

        Uhat1:= Max(gz);
        Uhat2:= Max(hz);

        Uhat:= Ceiling(Max([Uhat1, Uhat2, U0]));

        Uhat +:= 1;

        val:= Abs(m1*Evaluate(f, Uhat)^(1/2)+m2*Uhat+m3+m4*Uhat^2);

        if val gt m5*Uhat^2 then
            c10:= Log( Max([val/Uhat^2, Abs(m1*a^(1/2)+m4)]));
        else
            c10:= Log(Abs(m5));
        end if;

        return [c10, Uhat];

    end function;

    U:= Max( Getu01(a, b, c, d, e),
             Getu01(a, -b, c, -d, e) );
    U:= Max( Getu02(a, b, c, d, e, A, B, U),
             Getu02(a, -b, c, -d, e, A, B, U));

    c9:= Max( Getc9(a, b, c, d, e, U),
              Getc9(a, -b, c, -d, e, U));

    c10_1:= Getc10(a, b, c, d, e, A, B, U);
    c10_2:= Getc10(a, -b, c, -d, e, A, B, U);

    c10:= Max( c10_1[1], c10_2[1]);
    U:= Max( c10_1[2], c10_2[2]);

    U:= Ceiling(U);

    // printf "|U| > %m\n", U;

    P := PolynomialRing(Rationals()); x := P.1;
    q:= x^3 + A*x + B;
    qz:= #Roots(q);
    if qz eq 3 then D:= 1; end if;
    if qz eq 2 then D:= 3; end if;
    if qz eq 1 then D:= 2; end if;
    if qz eq 0 then D:= 3; end if;

Back:= function(a,b,c,d,esq,L);
    _,e := IsSquare(esq);
    s := Sigma(a,b,c,d,e);
    Q :=[];
    for P in L do
       X:= P[1] - c/3; Y:=s*P[2]-d/(2*e)*P[1]+c*d/(6*e)-e*b;
       if Y ne 0 and P[3] ne 0 then
          x1:= 2*e*(X+c)-d^2/(2*e);
          x1:= x1/Y;
          V:= -e + (x1*(x1*X-d))/(2*e);
          elt1:= [x1,V];  elt2:= [x1,-V];
          if not (elt1 in Q or elt2 in Q) then
             Append(~Q,[x1,V]);
          end if;
       end if;
    end for;
    return Q;
end function;

    E:= EllipticCurve([A,B]);
    F, EtoF:= MinimalModel(E);
    MWG := MWFreeBasis(F);
    r := #MWG; 

    if r eq 0 then 
     G,m:=TorsionSubgroup(E); PTS:=[m(g) : g in G];
     PTS:=Back(a,b,c,d,esq,PTS);
     return [P: P in PTS | IsIntegral(P[1]) and IsIntegral(P[2])]; end if;

  //c1:= SmallestEigenvalueRegMatrix(MWG);
    c1:= Min([tup[1] : tup in Eigenvalues(HeightPairingMatrix(MWG))]);
    assert c1 gt 0;

    c11 := Max(B1, B2) where B1, B2 := height_difference_bounds(F);

    g2:= A/4; g3:= -B/16;

    j:= 2^8*3^3*A^3/(4*A^3 + 27*B^2);

    j_num:= Numerator(j);
    j_den:= Denominator(j);

    g2_num:= Numerator(g2);
    g2_den:= Denominator(g2);

    g3_num:= Numerator(g3);
    g3_den:= Denominator(g3);

    bt:= LCM(g2_den, g3_den);

    h_1:= Log( Max([bt, bt*Abs(g2_num/g2_den), bt*Abs(g3_num/g3_den)]));
    h_2:= Log( Max([Abs(j_num), Abs(j_den)]));

    h_E:= Max([1, h_1, h_2]);

    omega1, omega2 := Explode(Periods(E : Precision := 20));
    tau:= omega1/omega2;
    if Im(tau) lt 0 then
        tau:= -tau;
    end if;

    pi:= Pi(RealField());

    A_0:= Max(h_E, 3*pi/(D*Im(tau))) ;

    m := LCM(2, Order(TorsionSubgroup(F)));
    LOGS := [ ];
    for P in MWG do
       P1 := m*P;
       Append(~LOGS, EllipticLogarithm(m*P : Precision := 50)/m);
    end for;
    L := [ Max([h_E, 3*pi*Re(phi)^2/(Im(tau)), Height(P1)]) : phi in LOGS ];

    e := Exp(1);

    k:= (D*A_0*RealField()!Im(tau)/(3*pi))^(1/2);
    i:= 1;
    L2:= [k];

    for A in L do
       Append(~L2, m^2/Phi(F,P1[1],P1[2],20)*
            (D*A*RealField()!Im(tau)/(3*pi))^(1/2));
    end for;

    e:= e*Min(L2);

    c4:= 2.9*10^(6*r+12)*D^(2*r+4)*4^(2*(r+1)^2)*(r+2)^(2*r^2+13*r+23.3)
        *Log(e)^(-2*r-3)*A_0;

    for A in L do
        c4:= c4*A;
    end for;

    c5:= Log(D*e);

    c6:= c5 + h_E;

    c12:= 2*r;
    c13:= 12*r;

    c7:= c5+Log(c12)+c13/(16*c12);
    c8:= c6+(Log(c12)+c13/(16*c12))/Log(16);

    P := PolynomialRing(Rationals()); x := P.1;
    q:= x^3+A*x+B;

    // get case

    qz:= RealRoots(q,RealField(),10^-10);
    M_:= 10;

    l:= #qz;

    if l eq 1 or (l eq 3 and x0 gt qz[l]) then cs:= 13; end if;
    if l eq 3 and qz[1] lt x0 and qz[2] gt x0 then cs:= 14; end if;
    if l eq 3 and Abs(x0-qz[3]) lt 10^-5 then cs:=15; end if;
    if l eq 3 and Abs(x0-qz[2]) lt 10^-5 then cs:=16; end if;

    // get M

    k1:= 2/c1*(Log(c9)+c10/2+c11/2);
    k2:=  2*c4/c1;

    while i lt 2500 do
     M:= 10^i; i:= i+5;
     val:= k1+k2*(Log(M)+c7)*(Log(Log(M))+c8)^(r+2) - M^2;
     if val gt 0 then erg:=10^5*M; end if;
    end while;

    prec := Ceiling(Log(erg)/Log(10))+1; // Upper bound

    // chap 4

    if cs eq 15 or cs eq 16 or cs eq 13 or cs eq 14 then

    flag := false;
    while not flag do

    K3 := 10^prec;

    K1:= c9/omega1*Exp(c11/2+c10/2);
    K2:= c1/2;

    t:= Order(TorsionSubgroup(E));
    r := Rank(E);
    K0 := (2^(r/2)*t*K3*(r^2+r))^(r+1);
    prec := Round(Log(K0)/Log(10))+1;

    K0 := 10^prec;

    Q := MatrixAlgebra(Integers(),r+1);

    Mat:= Q![0: i in [1..(r+1)^2]];


    R:= RealField(Max(200,50));

    local_prec:= Ceiling( 3.32193 * prec);
    logs:= [
       Real(EllipticLogarithm(m*P : Precision := local_prec))/m : P in MWG ];
    for i in [1..r] do
        Mat[i][i]:= 1;
        if logs[i] lt 0 then
            Mat[r+1][i]:=
               Round(R!(K0*(1+logs[i])));
        else
            Mat[r+1][i]:=
               Round(R!(K0*(logs[i])));
        end if;
    end for;

    Mat[r+1][r+1]:= K0;

    Redu:= LLL(Transpose(Mat));
    //bv:= Redu[1];
    //ab:= Norm(bv)^2;
    ab := Min([Norm(Redu[k]) : k in [1..Nrows(Redu)]]);  

    qv:= 2^(r/2)*t*K3*(r^2+r)^(1/2);

    if ab gt qv then
        M:= K2^(-1)*( Log(K0*K1)-Log( (t^-2*2^-r*ab^2-r*K3^2)^(1/2)-r*K3));
        M:= Ceiling(Max(100,Abs(M))^(1/2));
        new_prec:= Ceiling(Log(M)/Log(10))+1;

        if new_prec le local_prec then
            flag:= true;
            prec:= new_prec;
        end if;
    end if;

    end while;

    end if;

    if cs eq 13 or cs eq 14 then
        M:= M+2*r;
    end if;

  //MWbasis := MWFreeBasis(E);
    MWbasis := [E| P@@EtoF : P in MWG];
    vprintf IntegralPoints: "Associated %o has rank %o\n", E, #MWbasis;
    vprintf IntegralPoints: "Listing linear combinations of generators with coeffs up to %o ... ", M_; 
    vtime IntegralPoints:
    Combs:= PointLinearCombinations(MWbasis,M_);

    c2 := [];
    for P in Combs do
       Append(~c2, P);
       Append(~c2,-P);
    end for;

    Ints := Back(a,b,c,d,esq,c2);
    final := [];
    for P in Ints do
       if IsIntegral(P[1]) and IsIntegral(P[2]) then
          Append(~final,P);
       end if;
    end for;

    // additional search
    if U ge 10^8 then 
      printf "WARNING: The final step (naive x-coordinate search up to |x| = %o) will be time-consuming\n", U;
    end if;
    vprintf IntegralPoints: "Final step: naive x-coordinate search up to |x| = %o ... ", U; 
    vtime IntegralPoints:

     for x1 in [-U..U] do
        f := a*x1^4 + b*x1^3 + c*x1^2 + d*x1 + esq;
        blt, V := IsSquare(f);
        if blt then
            if [x1,V] notin final and [x1,-V] notin final then
               Append(~final,[x1,V]);
            end if;
        end if;
    end for;
    return final;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//                                                                   //
//            S-Integral Points on Hyperelliptic Quartics            //
//                 y^2 = ax^4 + bx^3 + cx^2 + dx +e                  //
//                                                                   //
///////////////////////////////////////////////////////////////////////

intrinsic SIntegralQuarticPoints(Q::[RngIntElt], S::[RngIntElt]) -> SeqEnum
   {Returns the sequence of S-integral points on the quartic curve
   y^2 = ax^4 + bx^3 + cx^2 + dx + e, where Q  = [a,b,c,d,e] with
   square a, and where S is a sequence of primes.}

   require #Q eq 5:
        "Argument 1 must have length 5.";
   require &and[ IsPrime(p : Proof := false) : p in S ] :
        "Argument 2 must be a sequence of primes.";

   a,b,c,d,e := Explode(Q);
   require IsSquare(a): "First element of argument 1 must be a square";

Back:= function(a,b,c,d,e,L);
    Q := [];
    for P in L do
        X := P[1];
        Y := P[2];
        if Y ne 0 then
           ar := Integers()!Floor((a^(1/2)));
           x1 := (2*ar*(X/(4*a)+c)-b^2/(2*ar))/ (Y/(8*a*ar));
           V := -ar + (x1*(x1*X/(4*a)-b))/(2*ar);
           if x1 ne 0 then
	      x := 1/x1;
              y := V*x^2;
              Append(~Q, [x,y]);
           end if;
        end if;
    end for;
    return Q;
end function;

    a1:= 2*b;
    a3:= 16*a^2*d;
    a2:= 4*a*c-b^2;
    a4:= -64*a^3*e;
    a6:= -256*a^4*e*c + 64*a^3*e*b^2;

    Ais:= [a1,a2,a3,a4,a6];

    require IsEllipticCurve(Ais):
       "Argument 1 must define a nonsingular elliptic curve.";

    E:= EllipticCurve(Ais);

    S1:= S;
    if S eq [] then
        F:= E;
        n:= map< E -> E | P :-> P >;
    else
        F,m,n:= MinimalModel(E);
        if IsomorphismData(n)[4] ne 0 then
            f:= Factorization(Integers()!IsomorphismData(n)[4]);
            for i in [1..#f] do
                f1:= f[i][1];
                if f1 notin S then
                   Append(~S1,f1);
                end if;
           end for;
        end if;

        if IsomorphismData(n)[3] ne 0 then
            g:= Factorization(Integers()!IsomorphismData(n)[3]);
            for i in [1..#g] do
                f1:= g[i][1];
                if f1 notin S then
                   Append(~S1,f1);
                end if;
            end for;
       end if;

        S1:= Sort(S1);
    end if;

    L := SIntegralPoints(F,S1);
    L2 := &cat[ [ n(P), -n(P) ] : P in L ];
    delete L;

    Q := Back(a,b,c,d,e,L2);

    // probably missed points

    P := PolynomialRing(Rationals()); x := P.1;

    q:= x^3 + a2*x^2 + a4*x + a6;
    f:= 4*a*(a*x^4+b*x^3+c*x^2+d*x+e) - b^2*x^2 - 4*a*b*x - 4*a^2;

    qz:= Roots(q);
    fz:= Roots(f);

    // case X == 0

    for r in fz do
        s:= r[1];
        bool, sq := IsSquare(a*s^4+b*s^3+c*s^2+d*s+e);
        if bool then
           Append(~Q,[s,sq]);
        end if;
    end for;

    // case Y == 0

    for r in qz do
        s := r[1];
        f := (s-2*a-b*x)^2- 4*a*(a*x^4+b*x^3+c*x^2+d*x+e);
        for k in Roots(f) do
            t:= k[1];
            V:= a*t^4+b*t^3+c*t^2+d*t+e;
            u, v := IsSquare(V);
            if u then
               Append(~Q,[t,v]);
            end if;
        end for;
    end for;

    val, sqrte := IsSquare(e);
    if val then
       Append(~Q, [0,sqrte]);
    end if;

    Q2:= [];
    for P in Q do
        P2:= [P[1],-P[2]];
        if P notin Q2 and P2 notin Q2 then
           if IsSIntegral(P[1],S) and IsSIntegral(P[2],S) then
              Append(~Q2,P);
           end if;
        end if;
    end for;
    return Q2;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//                                                                   //
//              S-Integral Points on Ljunggren Curves                //
//                   a*y^2 = b*x^4 + c*x^2 + d                       //
//                                                                   //
///////////////////////////////////////////////////////////////////////

intrinsic SIntegralLjunggrenPoints(Q::[RngIntElt], S::[RngIntElt])
-> SeqEnum
   {Returns the sequence of S-integral points on the Ljunggren curve
   a*y^2 = b*x^4 + cx^2 + d, where Q = [a,b,c,d], and S is a
   sequence of primes.}
   require #Q eq 4:
        "Argument 1 must be have length 4";
   require &and[ IsPrime(p : Proof := false) : p in S ] :
        "Argument 2 must be a sequence of primes";

   a,b,c,d := Explode(Q);
   E:= EllipticCurve([0, a*c, 0, a^2*b*d, 0]);

   L := SIntegralPoints(E,S);
   L1 := [];
   for P in L do
      L1 cat:= [P,-P];
   end for;

   V := [];
   for P in L do
       x:= P[1]/(a*b);
       y:= P[2]/(a^2*b);
       blt, v := IsSquare(x);
       if IsSIntegral(x,S) and blt then
          x1 := v;
          if x1 eq 0 then
             v := d/a;
             blt, y := IsSquare(v);
             if IsSIntegral(v,S) and blt then
                Append(~V, [x,y]);
             end if;
          else
             if IsSIntegral( y/x1, S) then
                y := y/x1;
                V cat:= [[x1,y],[-x1,y]];
             end if;
          end if;
       end if;
    end for;
    return V;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//                                                                   //
//              S-Integral Points on Desboves Curves                 //
//                 a*y^3 + b*x^3 + c*x*y + d = 0                     //
//                                                                   //
///////////////////////////////////////////////////////////////////////

intrinsic SIntegralDesbovesPoints(Q::[RngIntElt], S::[RngIntElt])
    -> SeqEnum {Returns the sequence of S-integral points to the
    Desboves curve a*y^3 + b*x^3 + c*x*y + d = 0, where C = [a,b,c,d],
    and S is a sequence of primes.}

    require &and[ IsPrime(p : Proof := false) : p in S ] :
       "Argument 2 must be a sequence of primes";
    a,b,c,d := Explode(Q);
    val, E := IsEllipticCurve([-c, 0, a*b*d, 0, 0]);
    require val :
       "Argument 1 must define a nonsingular elliptic curve.";
    L := &cat[ [ P, -P ] : P in SIntegralPoints(E, S) ];

    F := [];
    for P in L do
        X:= P[1]; Y:=P[2];

        x := -X/(a*b);
        y := Y/(a*b^2);

        blt, v := IsPower(y,3);
        if blt then
            if x ne 0 and IsSIntegral(x,S) and IsSIntegral(v,S) then
                if [v,x/v] notin F then
                   Append(~F,[v, x/v]);
                end if;
            end if;
        end if;
    end for;
    // special cases
    // x == 0 and y == 0
    if IsSIntegral(d/a, S) then
        y1:= -d/a;
        blt, v := IsPower(y1,3);
        if blt then
           Append(~F, [0, v]);
        end if;
    end if;
    if IsSIntegral(d/a, S) then
        y1:= -d/b;
        blt, v := IsPower(y1,3);
        if blt then
           Append(~F,[v,0]);
        end if;
    end if;
    return F;
end intrinsic;
