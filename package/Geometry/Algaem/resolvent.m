freeze;

/******************************************************************************
 *
 * resolvent.m
 *
 * date:   2010 Nov 23
 * author: Nils Bruin
 *
 * routine for internal usage.
 *
 * degnres(f,n)
 *  INPUT:  f - even degree polynomial
 *          n - degree(f)/2
 *  OUTPUT: if f=(x-t[1])*...*(x-t[2n])
 *          return polynomial
 *          Product( (x-t[i1])*(x-t[i2])*...*(x-t[in])+(x-t[j1])*(x-t[j2])*...*(x-t[jn]) )
 *          where {i1,...,in},{j1,...,jn} loop through the partitions of {1,...,2n}
 *          into two sets.
 *
 * NOTE:    for degree 4, 6, this polynomial is precomputed and the result is simply
 *          obtained by specializing.
 *          for other degrees, f must be defined over Q and the answer is
 *          constructed via CRT.
 ******************************************************************************/

_<s1,s2,s3,s4>:=PolynomialRing(Integers(),4);
Resolvent4:=[-s1^2*s4 + 4*s2*s4 - s3^2,s1*s3 - 4*s4,-s2,1];

_<s1,s2,s3,s4,s5,s6>:=PolynomialRing(Integers(),6);
Resolvent6:=[
    s1^6*s6^4 - 4*s1^4*s2*s6^4 - 2*s1^4*s3*s5*s6^3 + s1^4*s4^2*s6^3 + 
        8*s1^3*s3*s6^4 - 4*s1^3*s4*s5*s6^3 + 2*s1^3*s5^3*s6^2 + 
        8*s1^2*s2*s3*s5*s6^3 - 2*s1^2*s2*s4*s5^2*s6^2 - 2*s1^2*s3^2*s4*s6^3 + 
        s1^2*s3^2*s5^2*s6^2 - 4*s1*s2*s5^3*s6^2 - 12*s1*s3^2*s5*s6^3 + 
        8*s1*s3*s4*s5^2*s6^2 - 2*s1*s3*s5^4*s6 + s2^2*s5^4*s6 - 
        2*s2*s3^2*s5^2*s6^2 + s3^4*s6^3 + 8*s3*s5^3*s6^2 - 4*s4*s5^4*s6 + s5^6,
    -s1^5*s4*s6^3 - 2*s1^4*s5*s6^3 + 3*s1^3*s2*s5^2*s6^2 + 3*s1^3*s3^2*s6^3 - 
        s1^3*s3*s4*s5*s6^2 - 8*s1^3*s6^4 + 16*s1^2*s2*s5*s6^3 + 
        8*s1^2*s3*s4*s6^3 - 6*s1^2*s3*s5^2*s6^2 - 8*s1^2*s4^2*s5*s6^2 + 
        3*s1^2*s4*s5^3*s6 - 8*s1*s2^2*s5^2*s6^2 - 8*s1*s2*s3^2*s6^3 + 
        8*s1*s2*s3*s4*s5*s6^2 - s1*s2*s3*s5^3*s6 - s1*s3^3*s5*s6^2 - 
        24*s1*s3*s5*s6^3 + 16*s1*s4*s5^2*s6^2 - 2*s1*s5^4*s6 + 8*s2*s3*s5^2*s6^2
        - s2*s5^5 + 8*s3^3*s6^3 - 8*s3^2*s4*s5*s6^2 + 3*s3^2*s5^3*s6 - 
        8*s5^3*s6^2,
    -s1^4*s2*s6^3 + s1^4*s3*s5*s6^2 - 4*s1^3*s3*s6^3 + 10*s1^3*s4*s5*s6^2 - 
        4*s1^3*s5^3*s6 + 8*s1^2*s2^2*s6^3 - 8*s1^2*s2*s3*s5*s6^2 - 
        2*s1^2*s2*s4^2*s6^2 + s1^2*s2*s4*s5^2*s6 + s1^2*s3^2*s4*s6^2 - 
        6*s1^2*s4*s6^3 - 7*s1^2*s5^2*s6^2 - 24*s1*s2*s3*s6^3 - 
        4*s1*s2*s4*s5*s6^2 + 10*s1*s2*s5^3*s6 + 8*s1*s3^2*s5*s6^2 + 
        8*s1*s3*s4^2*s6^2 - 8*s1*s3*s4*s5^2*s6 + s1*s3*s5^4 + 36*s1*s5*s6^3 + 
        8*s2^2*s3*s5*s6^2 - 2*s2^2*s4*s5^2*s6 - 2*s2*s3^2*s4*s6^2 + 
        s2*s3^2*s5^2*s6 - 6*s2*s5^2*s6^2 + 18*s3^2*s6^3 - 24*s3*s4*s5*s6^2 - 
        4*s3*s5^3*s6 + 8*s4^2*s5^2*s6 - s4*s5^4,
    s1^4*s5*s6^2 + 2*s1^3*s2*s4*s6^2 - s1^3*s2*s5^2*s6 - s1^3*s3^2*s6^2 + 
        9*s1^3*s6^3 - 14*s1^2*s2*s5*s6^2 - 11*s1^2*s3*s4*s6^2 + 
        6*s1^2*s3*s5^2*s6 + 3*s1^2*s4^2*s5*s6 - s1^2*s4*s5^3 + 3*s1*s2^2*s5^2*s6
        + 3*s1*s2*s3^2*s6^2 - s1*s2*s3*s4*s5*s6 + 39*s1*s3*s5*s6^2 - 
        14*s1*s4*s5^2*s6 + s1*s5^4 - 11*s2*s3*s5^2*s6 + 2*s2*s4*s5^3 - 
        3*s3^3*s6^2 + 3*s3^2*s4*s5*s6 - s3^2*s5^3 + 9*s5^3*s6,
    s1^3*s3*s6^2 - 3*s1^3*s4*s5*s6 + s1^3*s5^3 - s1^2*s2^2*s6^2 + 
        s1^2*s2*s3*s5*s6 - 2*s1^2*s4*s6^2 + 6*s1^2*s5^2*s6 + 16*s1*s2*s3*s6^2 - 
        3*s1*s2*s5^3 - s1*s3^2*s5*s6 - 2*s1*s3*s4^2*s6 + s1*s3*s4*s5^2 - 
        30*s1*s5*s6^2 - 4*s2^3*s6^2 - 2*s2^2*s3*s5*s6 + s2^2*s4^2*s6 + 
        18*s2*s4*s6^2 - 2*s2*s5^2*s6 - 15*s3^2*s6^2 + 16*s3*s4*s5*s6 + s3*s5^3 -
        4*s4^3*s6 - s4^2*s5^2 - 27*s6^3,
    -2*s1^3*s6^2 + 2*s1^2*s2*s5*s6 + 2*s1^2*s3*s4*s6 - s1^2*s3*s5^2 - 
        s1*s2^2*s4*s6 - 3*s1*s2*s6^2 - 16*s1*s3*s5*s6 + 4*s1*s4^2*s6 + 
        2*s1*s4*s5^2 + 4*s2^2*s5*s6 + s2*s3*s4*s6 + 2*s2*s3*s5^2 - s2*s4^2*s5 - 
        9*s3*s6^2 - 3*s4*s5*s6 - 2*s5^3,
    s1^2*s4*s6 - s1^2*s5^2 - 3*s1*s2*s3*s6 + s1*s2*s4*s5 + 9*s1*s5*s6 + s2^3*s6 
        - 9*s2*s4*s6 + s2*s5^2 + 3*s3^2*s6 - 3*s3*s4*s5 + s4^3 + 27*s6^2,
    s1*s2*s6 + 2*s1*s3*s5 - s1*s4^2 - s2^2*s5 + 6*s3*s6 + s4*s5,
    -s1*s5 + s2*s4 - 9*s6,
    -s3,
    1
];
//given f with rational coefficients and an integer n=deg(f)/2, compute a resolvent
//that determines if f is the product of two (conjugate) factors of degree n.

function degnres(f,n)
  x:=Parent(f).1;
  //for degree 4,6 we have a precomputed form we can use
  if Degree(f) eq 4 and n eq 2 then
    res:=Resolvent4;
    d:=4;
  elif Degree(f) eq 6 and n eq 3 then
    res:=Resolvent6;
    d:=6;
  else
    res:=false;
  end if;
  //handle degree 4,6, where we can use precomputed form
  if res cmpne false then
    fmonic:=f/LeadingCoefficient(f);
    while true do
      s:=Reverse(Eltseq(fmonic)[1..d]);
      s:=[(-1)^i*s[i]:i in [1..d]];
      h:= Polynomial([Evaluate(r,s):r in res]);
      if Degree(GCD(h,Derivative(h))) eq 0 then
        break;
      end if;
      fmonic:=Evaluate(fmonic,x+1);
    end while;
  else
    //for other cases we need f to have rational coefficients
    error if not(Type(BaseRing(f)) eq FldRat), "Only implemented for f defined over rationals.";
    f:=LCM([Denominator(c): c in Eltseq(f)])*f; //clear denominators
    function hres(f)
      vprint Selmer:"entering hres with f=",f," n=",n;    
      //make monic
      f:=Evaluate(f,x/cf)*cf^(Degree(f)-1) where cf:=LeadingCoefficient(f);

      Coeffs:=Eltseq(f);

      B:=&+[Abs(c[i+1])^(1/(2*n-i)): i in [0..Degree(f)-1]] where c:=Eltseq(f);

      C:=2*B^n;

      Bound:=Maximum([Binomial(d,d-i)*C^(d-i):i in [0..d-1]]) where
                                   d:=Integers()!(Binomial(2*n,n)/2);

      p:=NextPrime(32000);
      N:=[Integers()|];
      CFS:=[];

      while &*N le 2*Bound do
        Fp:=GF(p);
        ffp := Factorization(Polynomial(Fp,f));
        if Max({ a[2] : a in ffp }) eq 1 then 
          d:=LCM([Degree(g[1]):g in ffp]);
          if d le 10 then 
	    FF:=GF(p^d);
	    theta:=[a[1]:a in Roots(Polynomial(FF,f))];
	     X:=PolynomialRing(FF).1;
	     h:=Polynomial(Fp,&*[(X-&*[theta[i]:i in v]-&*[theta[i]:i in {1..2*n} diff v]):v in {v: v in 
	     Subsets({1..2*n},n)|1 in v}]);
	     Append(~N,p);
	     Append(~CFS,[Integers()!c: c in Eltseq(h)]);
          end if;
        end if;
        p:=NextPrime(p);
      end while;

      T:=[[CFS[i][j] : i in [1..#CFS]]: j in [1..#CFS[1]]];
      M:=&*N;
      sym:=func<a| 2*a gt M select a-M else a>;
      return Parent(x)![sym(CRT(t,N)):t in T];
    end function;
    repeat
      h:=hres(f);
      f:=Evaluate(f,x+1);
    until Degree(GCD(h,Derivative(h))) eq 0;
  end if;
  if Type(BaseRing(f)) eq FldRat then
    S:={c[1]: c in Factorisation(LCM([Denominator(c):c in Eltseq(f)]))} join
       {c[1]: c in Factorisation(4*Numerator(Discriminant(f))) | c[2] ge 2};
    for p in S do
      SL:=Slopes(NewtonPolygon(h,p));
      if #SL ne 0 then
        e:=Floor(-Maximum(Slopes(NewtonPolygon(h,p))));
        h:=Evaluate(h,Parent(h).1*p^e)/p^(e*Degree(h));
      end if;
    end for;
  end if;
  return h;
end function;
