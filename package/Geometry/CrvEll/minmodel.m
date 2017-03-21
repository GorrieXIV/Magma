freeze;

/************************************************************************
minmodel.m

Date: 25/08/2003
Original author: John Cremona

Interface adapted by Nils Bruin on John Cremona's request for incorporation
with MAGMA.
Mangled by Geoff Bailey for consistency with similar intrinsics over Q.

Interface presently:

intrinsic LocalInformation(E::CrvEll, P::RngOrdIdl) -> Tup, CrvEll

  Returns:

    <P, vpd, fp, c_p, K, split>, Emin

  where 
    P = the prime ideal
    vpd = valuation of local minimal discriminant
    fp = valuation of conductor
    K = Kodaira Symbol
    cp = Tamagawa number
    split = false iff curve has nonsplit mult. reduction
    Emin is a model (integral and) minimal at P

intrinsic LocalInformation(E::CrvEll) -> SeqEnum

  Returns local reduction data at all bad primes.

intrinsic Conductor(E::CrvEll) -> RngOrdIdl

  Conductor of an elliptic curve E over a number field

intrinsic MinimalModel(E::CrvEll) -> CrvEll, MapIsoSch

  Minimal Model and Conductor of an elliptic curve E over a number field,
  only for class number one.

intrinsic LocalMinimalModel(E::CrvEll, P::RngOrdIdl) -> CrvEll, RngIntElt

  local minimal model of an elliptic curve E at prime ideal P;
  this is a faster algorithm than the one used in LocalInformation for
  primes of residue characteristic bigger than 3. For residue characteristics
  2 and 3, this routine simply returns data computed by LocalInformation

***********************************************************************/

declare attributes CrvEll: LocalInformation, MinimalModels;
// These are associative arrays indexed by primes 
// (added SRD, Sep 2009)

/////////////////////////////////////////////////////////////////////////
// LocalInformation(E, p) over Q
//
// Work around the problem that the internal code factors Discriminant(E)
//
// November 2013, SRD
/////////////////////////////////////////////////////////////////////////

intrinsic LocalInformation(E::CrvEll[FldRat], p::RngIntElt : Check)
  -> SeqEnum
{The tuple 
  <p, exponent, f_p, c_p, kodaira symbol, split> 
of local information for E at the prime p}

  // If factorization is not hard, use internal
  // (U assigned iff factorization incomplete)
  D := Discriminant(E);
  _, _, U := Factorization(Denominator(D) : ECMLimit := 10000,
                                            MPQSLimit := 0 );
  if not assigned U then
    _, _, U := Factorization(Numerator(D) : ECMLimit := 10000,
                                            MPQSLimit := 0 );
  end if;
  if not assigned U then
    return InternalLocalInformation(E, p : Check:=Check);
  end if;

  require not Check or IsPrime(p) : "The second argument is not prime";

  // check cache
  bool, LI := HasAttribute(E, "LocalInformation");
  if bool then
    bool, LI_p := IsDefined(LI, p);
    if bool then
      return LI_p;
    end if;
  else
    E`LocalInformation := AssociativeArray();
  end if;

  Q  := RationalsAsNumberField();
  EQ := BaseChange(E, Q);
  LI := LocalInformation(EQ, p*Integers(Q));

  LI := <p, LI[2], LI[3], LI[4], LI[5], LI[6] >;
  E`LocalInformation[p] := LI;
  return LI;

end intrinsic;

// TO DO
// intrinsic MinimalModel(E::CrvEll[FldRat], p::RngIntElt)

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                TATE'S ALGORITHM OVER NUMBER FIELDS                 //
//                           John Cremona                             //
//                                                                    //
//             (based on code which originated with a                 //
//               Fortran program of Richard Pinch)                    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

//15.08.06 (TD)
//Commented out ScaleCurve - was not used
//Commented out iso from rst_transform - was not used
//Commented out import Denom - was not used
//Made a generic Tate's algorithm over a DVR (TateAlgorithm)
//  to avoid multiple implementations; LocalInformation calls it

declare verbose Tate,4;

// Transforms an elliptic curve E with standard parameters [r,s,t]
// Returns the transformed curve F and the isomorphism E->F

//intrinsic rst_transform(E::CrvEll, rst::SeqEnum) -> CrvEll, Map

function rst_transform(E, rst)
//{transforms the elliptic curve using the unimodular (u=1) transform with 
//standard parameters [r,s,t].   Returns the transformed curve F and the 
//isomorphism E->F.}
     r,s,t:=Explode(rst);
     a1,a2,a3,a4,a6:=Explode(aInvariants(E));
     a6 := a6 + r*(a4 + r*(a2 + r)) - t*(a3 + r*a1 + t);
     a4 := a4 - s*a3 + 2*r*a2 - (t + r*s)*a1 + 3*r*r - 2*s*t;
     a3 := a3 + r*a1 +t+t;
     a2 := a2 - s*a1 + 3*r - s*s;
     a1 := a1 + s+s;
     F:=EllipticCurve([a1,a2,a3,a4,a6]);
     //iso:=Isomorphism(F,E,[r,s,t,1]);
     return F;//,iso;
end function;
//     end intrinsic;

//intrinsic ScaleCurve(E::CrvEll, u::FldNumElt) -> CrvEll, Map
//function ScaleCurve(E, u)
//{transforms the elliptic curve using scale factor u: 
//i.e. multiplies c_i by u^i.}
//     a1,a2,a3,a4,a6:=Explode(aInvariants(E));
//     a1*:=u; a2*:=u^2; a3*:=u^3; a4*:=u^4; a6*:=u^6;
//     F:=EllipticCurve([a1,a2,a3,a4,a6]);
//     iso:=Isomorphism(E,F,[0,0,0,u]);
//     return F,iso;
//end function;
//     end intrinsic;

// helper function to reduce mod 3, returning just the quotient, 
// with remainder in {-1,0,1}

function redmod3(n)
r:=n mod 3; 
if r eq 2 then r:= -1; end if;
return (n-r) div 3;
end function;

// this only works on integral models
//intrinsic tidy_model(E::CrvEll) -> CrvEll, Map

function tidy_model(E)
//{transforms the elliptic curve to a model in which a1,a2,a3 are reduced
// modulo 2,3,2 respectively.   Intended for use over Q or a number field;  
// requires EltSeq() of the coefficients to be integers.}
a1,a2,a3,a4,a6:=Explode(aInvariants(E));
K:=BaseRing(E); Z:=Integers();
// N.B. Must define s,r,t in the right order!
if Type(K) eq FldRat then
  s:=-K![(Z!a) div 2 : a in Eltseq(a1)];
  r:=-K![redmod3(Z!a) : a in Eltseq(a2-s*a1-s*s)];
  t:=-K![(Z!a) div 2 : a in Eltseq(a3+r*a1)];
else
  O:=IntegerRing(K);
  s:=-(a1-((O!a1) mod (2*O)))/2;
  b:=a2-s*a1-s^2;
  r:=-(b-((O!b) mod (3*O)))/3;
  b:=a3+r*a1;
  t:=-(b-((O!b) mod (2*O)))/2;
end if;
  
return rst_transform(E,[r,s,t]);
end function;

//end intrinsic;


intrinsic TamagawaNumber(E::CrvEll[FldAlg], P::RngOrdIdl) -> RngIntElt
{The Tamagawa number at the prime P for the elliptic curve E (over a number field)}
  return LocalInformation(E, P)[4];  
end intrinsic;

intrinsic KodairaSymbol(E::CrvEll[FldAlg], P::RngOrdIdl) -> SymKod
{The Kodaira symbol for the reduction type of E at the prime P}
  return LocalInformation(E, P)[5];  
end intrinsic;


// Tate's algorithm for elliptic curves over number fields
// Given curve E and a prime ideal P, 
// returns <P, vpd, ord_p(cond), c_p, Kodaira>

function TateAlgorithm(E,P,red,val,pi: RootsF:=Roots, IsPowerF:=IsPower)
  // Tate's algorithm for an elliptic curve E defined over a field F with a
  // discrete valuation val, uniformizer pi and red: (valuation ring) -> F.
  // May override default intrinsics IsPower, Roots for taking roots of elts
  // of F and finding roots of polys over F with your Intrinsic/UserProgram
  // Returns:
  //   <P, vpd, fp, c_p, K, split>, Emin
  // P     = the place (Passed as a parameter but otherwise not used)
  // vpd   = valuation of local minimal discriminant
  // fp    = valuation of conductor
  // K     = Kodaira Symbol
  // cp    = Tamagawa number
  // split = false if reduction is nonsplit multiplicative, true otherwise
  // Emin  = integral minimal model at P

  // residue field
  F:=Codomain(red);
  p:=Characteristic(F);
  pdiv2:=(p eq 2);
  pdiv3:=(p eq 3);

  // reducing and lifting elements
  lift:=Inverse(red);
  pdiv:=func<x|val(x) gt 0>;
  redmod:=func<x|lift(red(x))>;
  invmod:=func<x|lift(1/red(x))>;
  halfmodp:=pdiv2 select 0 else invmod(2);

  function rootmod(x,e)
    fl,y:=IsPowerF(red(x),e);
    return fl select lift(y) else 0;
  end function;

  function rootsexist(a,b,c)
    f:=PolynomialRing(F)![red(c),red(b),red(a)];
    return #RootsF(f) gt 0;
  end function;

  function nrootscubic(b,c,d)
    f:=PolynomialRing(F)![red(d),red(c),red(b),red(1)];
    return #RootsF(f);
  end function;

  a1,a2,a3,a4,a6:=Explode(aInvariants(E));
  if Min([val(ai) : ai in [a1,a2,a3,a4,a6] | ai ne 0]) lt 0 then
    vprint Tate,1: "Non-integral model at P: valuations are ",
      <val(ai) : ai in [a1,a2,a3,a4,a6]>,": making integral";
    e:=0;
    if a1 ne 0 then e:=Max(e,-val(a1)); end if;
    if a2 ne 0 then e:=Max(e,Ceiling(-val(a2)/2)); end if;
    if a3 ne 0 then e:=Max(e,Ceiling(-val(a3)/3)); end if;
    if a4 ne 0 then e:=Max(e,Ceiling(-val(a4)/4)); end if;
    if a6 ne 0 then e:=Max(e,Ceiling(-val(a6)/6)); end if;
    pie:=pi^e;
    a1*:=pie; a2*:=pie^2; a3*:=pie^3; a4*:=pie^4; a6*:=pie^6;
    vprint Tate,1: "P-integral model is ",[a1,a2,a3,a4,a6],
      " with valuations ",<val(ai) : ai in [a1,a2,a3,a4,a6]>;
  end if;

  while true do
    C:=EllipticCurve([a1,a2,a3,a4,a6]);
    b2,b4,b6,b8:=Explode(bInvariants(C));
    c4,c6:=Explode(cInvariants(C));
    delta:=Discriminant(C);
    vpd := val(delta);

    if vpd eq 0 then // Good reduction already
      c_p := 1;
      KS:=KodairaSymbol("I0");
      reduct_array := <P, 0, 0, 1, KS, true>;
      vprint Tate,1: "Tate returns ",reduct_array;
      return reduct_array, C;
    end if;

    //change coords so that p|a3,a4,a6

    if pdiv2 then
      if pdiv(b2) then
        r := rootmod(a4,2);
        t := rootmod(((r+a2)*r+a4)*r+a6,2);
      else a1inv :=invmod(a1);
        r := a1inv*a3;
        t := a1inv*(a4 + r*r);
      end if;
    else if pdiv3 then
      r := pdiv(b2) select rootmod(-b6,3) else -invmod(b2)*b4;
      t :=  a1*r + a3;
    else
      r := pdiv(c4) select -invmod(12)*b2 else -invmod(12*c4)*(c6+b2*c4);
      t :=  -halfmodp*(a1*r+a3);
    end if; end if;
    r := redmod(r);
    t := redmod(t);
    //print "Before first transform, C = ",C;
    //print "[a1,a2,a3,a4,a6] = ",[a1,a2,a3,a4,a6];
    C:=rst_transform(C,[r,0,t]);
    a1,a2,a3,a4,a6:=Explode(aInvariants(C));
    b2,b4,b6,b8:=Explode(bInvariants(C));
    error if Min([val(ai) : ai in [a1,a2,a3,a4,a6] | ai ne 0]) lt 0,
    "Non-integral model after first transform!";
    vprint Tate,4: "After first transform ",[r,0,t];
    vprint Tate,4: "[a1,a2,a3,a4,a6] = ",[a1,a2,a3,a4,a6];
    vprint Tate,4: "Valuations:  ",<val(ai):ai in [a1,a2,a3,a4,a6]>;

    error if val(a3) eq 0, "p ndiv a3 after first transform!";
    error if val(a4) eq 0, "p ndiv a4 after first transform!";
    error if val(a6) eq 0, "p ndiv a6 after first transform!";

    // test for Types In, II, III, IV
    if not pdiv(c4) then   // Type In (n:=vpd)
      split:=rootsexist(1,a1,-a2);
      c_p := split select vpd else IsOdd(vpd) select 1 else 2;
      KS:=KodairaSymbol("I" cat IntegerToString(vpd));
      reduct_array := <P, vpd, 1, c_p, KS, split>;
      vprint Tate,1: "Tate returns ",reduct_array;
      return reduct_array, C;
    end if;

    if val(a6) lt 2 then   // Type II
      KS:=KodairaSymbol("II");
      reduct_array := <P, vpd, vpd, 1, KS, true>;
      vprint Tate,1: "Tate returns ",reduct_array;
      return reduct_array, C;
    end if;

    if val(b8) lt 3  then   // Type III
      KS:=KodairaSymbol("III");
      reduct_array := <P, vpd, vpd - 1, 2, KS, true>;
      vprint Tate,1: "Tate returns ",reduct_array;
      return reduct_array, C;
    end if;

    if val(b6) lt 3 then   // Type IV
      c_p := rootsexist(1,a3/pi,-(a6/pi)/pi) select 3 else 1;
      KS:=KodairaSymbol("IV");
      reduct_array := <P, vpd, vpd - 2, c_p, KS, true>;
      vprint Tate,1: "Tate returns ",reduct_array;
      return reduct_array, C;
    end if;

    // else change coords so that p|a1,a2, p^2|a3,a4, p^3|a6

    if pdiv2 then
      s := rootmod(a2,2);
      t := pi*rootmod((a6/pi)/pi,2);
    elif pdiv3 then
      s := a1;
      t := a3;
    else
      s := -a1*halfmodp;
      t := -a3*halfmodp;
    end if;

    C:=rst_transform(C,[0,s,t]);
    a1,a2,a3,a4,a6:=Explode(aInvariants(C));
    b2,b4,b6,b8:=Explode(bInvariants(C));
    vprint Tate,4: "After second transform ",[0,s,t];
    vprint Tate,4: "[a1,a2,a3,a4,a6] = ",[a1,a2,a3,a4,a6];
    vprint Tate,4: "Valuations: ",<val(ai):ai in [a1,a2,a3,a4,a6]>;
    error if val(a1) eq 0, "p ndiv a1 after second transform!";
    error if val(a2) eq 0, "p ndiv a2 after second transform!";
    error if val(a3) lt 2, "p^2 ndiv a3 after second transform!";
    error if val(a4) lt 2, "p^2 ndiv a4 after second transform!";
    error if val(a6) lt 3, "p^3 ndiv a6 after second transform!";
    error if Min([val(ai) : ai in [a1,a2,a3,a4,a6] | ai ne 0]) lt 0,
      "Non-integral model after second transform!";

    //                             3     2
    // Analyse roots of the cubic T  + bT  + cT + d := 0, where
    // b:=a2/p, c:=(a4/p)/p, d:=((a6/p)/p)/p

    b:=a2/pi;
    c:=(a4/pi)/pi;
    d:=((a6/pi)/pi)/pi;
    bb:=b*b; cc:=c*c; bc:=b*c;
    w := 27*d*d - bb*cc + 4*b*bb*d - 18*bc*d + 4*c*cc;
    x := 3*c - bb;

    sw := pdiv(w) select pdiv(x) select 3 else 2 else 1;

    vprint Tate,2: "Analysing roots of cubic ",[1,b,c,d],"; case " , sw;

    case  sw:
    when 1:      //Three distinct roots - Type I*0

      KS:=KodairaSymbol("I0*");
      c_p:=1+nrootscubic(b,c,d);
      reduct_array := <P, vpd, vpd - 4, c_p, KS, true>;
      vprint Tate,1: "Tate returns ",reduct_array;
      return reduct_array, C;

    when 2:      // One double root - Type I*m for some m
      // Change coords so that the double root is T:=0 mod p
      r:= pdiv2 select rootmod(c,2) else
          pdiv3 select c*invmod(b)  else  (bc - 9*d)*invmod(2*x);
      r := pi * redmod(r);
      C:=rst_transform(C,[r,0,0]);
      a1,a2,a3,a4,a6:=Explode(aInvariants(C));
      b2,b4,b6,b8:=Explode(bInvariants(C));

      ix := 3; iy := 3; mx := pi*pi; my := pi*pi;
      loop := true;
        while loop do
          a2t := a2/pi;
          a3t := a3/my;
          a4t := (a4/pi)/mx;
          a6t := (a6/mx)/my;
          if pdiv(a3t*a3t + 4*a6t) then
            t:= pdiv2 select my*rootmod(a6t,2) else my*redmod(-a3t*halfmodp);
            C:=rst_transform(C,[0,0,t]);
            a1,a2,a3,a4,a6:=Explode(aInvariants(C));
            b2,b4,b6,b8:=Explode(bInvariants(C));
            my := my*pi;
            iy+:=1;
            a2t := a2/pi;
            a3t := a3/my;
            a4t := (a4/pi)/mx;
            a6t := (a6/mx)/my;
            if pdiv(a4t*a4t - 4*a6t*a2t) then
	    r := pdiv2 select mx*rootmod( a6t*invmod(a2t), 2)
                       else mx*redmod( -a4t*invmod(2*a2t));
            C:=rst_transform(C,[r,0,0]);
            a1,a2,a3,a4,a6:=Explode(aInvariants(C));
            b2,b4,b6,b8:=Explode(bInvariants(C));
            mx := mx*pi;
            ix+:=1;       // and stay in loop
	    else
              c_p := rootsexist(a2t,a4t,a6t) select 4 else 2;
              loop := false;
            end if;  // and exit loop
          else
            c_p := rootsexist(1,a3t,-a6t) select 4 else 2;
            loop := false;
	  end if;
      end while;
      KS:= KodairaSymbol("I" cat IntegerToString(ix+iy-5) cat "*");
      reduct_array := <P, vpd, vpd - ix - iy + 1, c_p, KS, true>;
      vprint Tate,1: "Tate returns ",reduct_array;
      return reduct_array, C;

    when 3:      // Triple root
      // change coords so that T:=0 mod p
      r := pdiv2 select b else pdiv3 select rootmod(-d,3) else -b*invmod(3);
      r := pi*redmod(r);
      C:=rst_transform(C,[r,0,0]);
      a1,a2,a3,a4,a6:=Explode(aInvariants(C));
      b2,b4,b6,b8:=Explode(bInvariants(C));
      vprint Tate,4: "After third transform ",[r,0,0];
      vprint Tate,4: "[a1,a2,a3,a4,a6] = ",[a1,a2,a3,a4,a6];
      vprint Tate,4: "Valuations:  ",<val(ai):ai in [a1,a2,a3,a4,a6]>;
      vprint Tate,4: "[a1,a2,a3,a4,a6] = ",[a1,a2,a3,a4,a6];
      error if Min([val(ai) : ai in [a1,a2,a3,a4,a6] | ai ne 0]) lt 0,
        "Non-integral model after third transform!";
      error if (val(a2) lt 2) or (val(a4) lt 3) or (val(a6) lt 4),
        "Cubic after transform does not have triple root at 0";

      a3t := (a3/pi)/pi;
      a6t := (((a6/pi)/pi)/pi)/pi;

      // test for Type IV*
      if not pdiv(a3t*a3t + 4*a6t) then
	 c_p := rootsexist(1,a3t,-a6t) select 3 else 1;
         KS:=KodairaSymbol("IV*");
	 reduct_array := <P, vpd, vpd - 6, c_p, KS, true>;
         vprint Tate,1: "Tate returns ",reduct_array;
         return reduct_array, C;
      end if;

      // change coords so that p^3|a3, p^5|a6
      t := pdiv2 select -pi*pi*rootmod(a6t,2)
                 else  pi*pi*redmod(-a3t*halfmodp);
      C:=rst_transform(C,[0,0,t]);
      a1,a2,a3,a4,a6:=Explode(aInvariants(C));
      b2,b4,b6,b8:=Explode(bInvariants(C));

      // test for types III*, II*
      if val(a4) lt 4 then  // Type III*
        KS:=KodairaSymbol("III*");
         reduct_array := <P, vpd, vpd - 7, 2, KS, true>;
         vprint Tate,1: "Tate returns ",reduct_array;
         return reduct_array, C;
      end if;

      if val(a6) lt 6  then  // Type II*
        KS:=KodairaSymbol("II*");
        reduct_array := <P, vpd, vpd - 8, 1, KS, true>;
        vprint Tate,1: "Tate returns ",reduct_array;
        return reduct_array, C;
      end if;

      vprint Tate,1: "Non-minimal equation, dividing out...";
      a1/:=pi; a2/:=pi^2; a3/:=pi^3; a4/:=pi^4; a6/:=pi^6;
      vprint Tate,1: "new model is ",[a1,a2,a3,a4,a6];

    end case;
  end while;

end function;


// Tate's algorithm for elliptic curves over number fields
// Given curve E and a prime ideal P,
// returns <P, vpd, ord_p(cond),c_p,Kodaira,split>, Emin

intrinsic LocalInformation(E::CrvEll[FldAlg], P::RngOrdIdl : UseGeneratorAsUniformiser:=false )
       -> Tup,CrvEll
{Tate's algorithm for an elliptic curve over a number field:
 computes local reduction data at the prime ideal P,
 and a local minimal model.
The model is not required to be integral on input.
 Output is
    <P, vpd, fp, c_p, K, split>, Emin
 where
    P = the prime ideal,
    vpd = valuation of local minimal discriminant
    fp = valuation of conductor
    cp = Tamagawa number
    K = Kodaira Symbol
    split = false if non-split mult. red., true otherwise
    Emin is a model (integral and) minimal at P
}
  require IsPrime(P) : "second argument must be a prime ideal";
  require Order(P) eq Integers(BaseRing(E)):
    "mismatch between order of P and base field of E";
  vprint Tate,1: "Running Tate's algorithm with P = ",P;

  // Check cache (use Emin only in default case)
  if not UseGeneratorAsUniformiser and 
     assigned E`LocalInformation and IsDefined(E`LocalInformation,P) and
     assigned E`MinimalModels and IsDefined(E`MinimalModels,P) 
  then
     return E`LocalInformation[P], E`MinimalModels[P];
  end if;

  if UseGeneratorAsUniformiser then
     princ, pi := IsPrincipal(P);
     if princ then vprintf Tate,2: "P is principal, using generator %o as uniformiser",pi;
     else pi:=UniformizingElement(P); end if;
  else
     pi:=UniformizingElement(P);
  end if;

  _,red:=ResidueClassField(P);
  val:=func<x|Valuation(x,P)>;

  info, Emin := TateAlgorithm(E,P,red,val,pi);

  // Cache results (cache Emin only in default case)
  if not assigned E`LocalInformation then
     E`LocalInformation := AssociativeArray(Parent(P));
  end if;
  if not assigned E`MinimalModels then
     E`MinimalModels := AssociativeArray(Parent(P));
  end if;
  E`LocalInformation[P] := info;
  if not UseGeneratorAsUniformiser then
    E`MinimalModels[P] := Emin;
  end if;

  return info, Emin;
end intrinsic;

// primes appearing in the denominator of coefficients, 
// or in the discriminant
function badprimes(E)
    R := Integers(BaseRing(E));
    PI := PowerIdeal(R);
    coeffs := Coefficients(E);
    d := LCM([Denominator(c) : c in coeffs]);
    dprimes := [PI| t[1] : t in Factorization(d*R) 
                         | exists{c: c in coeffs | Valuation(c,t[1]) lt 0}];
    Dprimes := [PI| t[1] : t in Factorization(Discriminant(E)*R) 
                         | t[1] notin dprimes];
    return dprimes cat Dprimes;
end function;

intrinsic LocalInformation(E::CrvEll[FldAlg]) -> SeqEnum
{The sequence of tuples
  <p, exponent, f_p, c_p, kodaira symbol, split>
of local information for E at all primes p appearing in Discriminant(E)}

    return [LocalInformation(E,P) : P in badprimes(E)]; 
end intrinsic;

intrinsic Conductor(E::CrvEll[FldAlg] : Primes:=0) -> RngOrdIdl
{Conductor of an elliptic curve E over a number field}

    K := BaseRing(E);
    R := Integers(K);
 
    if Primes cmpeq 0 then
       Primes := badprimes(E);
    end if;

    if #Primes eq 0 then
       return 1*R;
    end if;

    // Avoid Tate's algorithm except above 2 and 3
    EE := IntegralModel(E);
    c4, c6 := Explode(cInvariants(EE));
    D := Discriminant(EE);
    j := jInvariant(EE);
    N := 1*R;
    for P in Primes do 
      if Minimum(P) in {2,3} then 
        N *:= P^LocalInformation(E,P)[3];
      else
        level := Floor(Min(Valuation(c4,P)/4, Valuation(c6,P)/6));
        vD := Valuation(D,P) - 12*level; // valuation of minimal discriminant
        if vD eq 0 then
          continue;
        end if;
        vj := Valuation(j,P);
        if vj ge 0 then
          N *:= P^2;
        elif vj eq -vD then
          N *:= P;
        else
          assert vD eq 6 - vj;
          N *:= P^2;
        end if;
      end if;
    end for;

    // check using Tate's algorithm at all primes:
    // assert N eq &*[ P^LocalInformation(E,P)[3] : P in Primes ];

    return N;
end intrinsic;


function local_minimal_model(E, P : UseGeneratorAsUniformiser:=false )
// Local minimal model of an elliptic curve E at prime ideal P

    p := Characteristic(ResidueClassField(P)); 
    if p in {2,3} then
	_,Emin := LocalInformation(E, P : UseGeneratorAsUniformiser:=UseGeneratorAsUniformiser);
	return Emin;
    end if;

    c4,c6 := Explode(cInvariants(E));
    v4 := Valuation(c4, P);
    v6 := Valuation(c6, P);
    v0 := Floor(Min(v4/4, v6/6));
    if UseGeneratorAsUniformiser then
       princ,pi := IsPrincipal(P);  
       if not princ then pi := UniformizingElement(P); end if;
    else   
       pi := UniformizingElement(P); 
    end if; 
                  
    Emin := EllipticCurve([-(1/48)*c4/pi^(4*v0), -(1/864)*c6/pi^(6*v0)]);
    return Emin;
end function;

intrinsic MinimalModel(E::CrvEll[FldRat], P::RngOrdIdl) -> CrvEll, MapIsoSch
{A local minimal model of the elliptic curve E at prime ideal P}

    require IsPrime(P) : "Second argument must be a prime ideal";

    p := Minimum(P); 
    return MinimalModel(E, p);
end intrinsic;

intrinsic MinimalModel(E::CrvEll[FldAlg], P::RngOrdIdl : UseGeneratorAsUniformiser:=false ) 
       -> CrvEll, MapIsoSch
{"} // "
    require IsPrime(P) : "Second argument must be a prime ideal";
    require Order(P) eq Integers(BaseRing(E)) :
			"Mismatch between order of P and base field of E";

    Emin := local_minimal_model(E, P : UseGeneratorAsUniformiser:=UseGeneratorAsUniformiser);
    return Emin, Isomorphism(E, Emin);
end intrinsic;

intrinsic MinimalModel(E::CrvEll[FldAlg]) -> CrvEll, MapIsoSch
{A minimal model of the elliptic curve E together with the map E:->M.  
 E must be defined over a number field with class number one}

    K := BaseRing(E);
    require IsAbsoluteField(K): 
           "The elliptic curve E must be defined over an absolute extension of Q";

    R := Integers(K);
    require ClassNumber(R) eq 1: 
           "The elliptic curve E must be defined over a field with class number 1";

    p6 := { f[1] : f in Factorization(6*R) };
    primes := Seqset(badprimes(E)) diff p6;

    EE := E;

    for P in primes do
	EE := local_minimal_model(EE, P : UseGeneratorAsUniformiser);
    end for;

    for P in p6 do
	_,EE := LocalInformation(EE, P : UseGeneratorAsUniformiser);
    end for;

if IsTotallyReal(K) then
    // Since we already have the class group, this is not expensive
    // (using the known units; full UnitGroup may still be hard)
    U, mU := IndependentUnits(R);
    units := [U.i@mU : i in [2..Ngens(U)]]; 
    Ered := ReducedModel(EE : Units:=units); // calls tidy_model
    return Ered, Isomorphism(E, Ered);
else
    return EE, Isomorphism(E, EE);
end if;

end intrinsic;

//////////////////////////////////////////////////////////////////////////////////////////////
// ReducedModel
// Steve Donnelly, October 2011
//////////////////////////////////////////////////////////////////////////////////////////////

// Solve s*B = v for s, and return s rounded to integers
// (work-around since Solution only works when B has full rank)

function iSolution(B, v)
  n := Ncols(v);
  assert n eq Ncols(B);
  assert n-1 eq Nrows(B);
  // Trick: add independent row with length M much larger than all coords
  // (here we assume that the rows sum to zero)
  epsilon := 10^(20 - Precision(BaseRing(B)));
  assert Abs(&+Eltseq(v)) lt epsilon;
  assert forall{i: i in [1..n-1] | Abs(&+Eltseq(B[i])) lt epsilon};
  M := Round(10^100 * Max([Abs(x) : x in Eltseq(B) cat Eltseq(v)]) );
  B := VerticalJoin(B, Vector(BaseRing(B), [M : i in [1..n]]) );
  s := NumericalSolution(B, v : Epsilon:=0.0); // TO DO: check MW criterion
  assert Abs(s[n]) lt epsilon;
  return [Round(s[i]) : i in [1..n-1]];
end function;

function closest_vector(L, v)
  // Get some w in L, with w close to v
  // TO DO: could also try w + s for some short vectors s
  B := BasisMatrix(LLL(LatticeWithBasis(L)));
  s := iSolution(B, v);
  w := Vector(BaseRing(B),s) * B;
  // Get coords of w as a combination of the given basis L
  c := iSolution(L, w);
  // Check it's a good approximation
  delta := w - Vector(BaseRing(L),c) * L;
  assert Norm(delta) lt 10^-20;
  return w, c;
end function;

intrinsic ClosestUnit(K::FldAlg, v::SeqEnum : Units:=0) -> RngOrdElt
{A unit u in the ring of integers of the number field K, such that
the vector [log|u_w| : w in InfinitePlaces(K)] is close to the given v}

  require IsAbsoluteField(K) : "Not implemented for relative number fields";
require IsTotallyReal(K) : "Currently only for totally real fields"; // TO DO
  n := #InfinitePlaces(K);
  require #v eq n : 
     "The second argument must be a sequence of length #InfinitePlaces(K)";

  if n eq 1 then
     return K!1;
  end if;

  if Units cmpeq 0 then
     U, mU := UnitGroup(K);
     assert Order(U.1) gt 0;
     Units := [U.i@mU : i in [2..Ngens(U)]];
  end if;
  require #Units eq n-1 : "#Units must equal #InfinitePlaces(K) - 1";

  R := Universe(v);
  require ISA(Type(R), FldRe): "The second argument must contain elements of a real field";
  prec := Precision(R);
  // project v to the subspace of vectors with sum 0, since that's where the units live
  v := [x-a : x in v] where a := &+v/#v;

  // images in log space, as row vectors
  logs := [Log(Abs(c)) : c in ChangeUniverse(Conjugates(u:Precision:=prec),R), u in Units];
  L := Matrix(n, logs);
 
  // One day this will work (wouldn't it be lovely)
  // ClosestVector(LatticeWithBasis(L), Vector(v))
  _, c := closest_vector(L, Vector(v));

  return &* [K| Units[i]^c[i] : i in [1..n-1]];
end intrinsic;


// TO DO: Precision option needed?

intrinsic ReducedModel(E::CrvEll[FldAlg] : Units:=0) -> CrvEll, MapIsoSch
{A reduced model of the elliptic curve E}

  K := BaseRing(E);
require IsTotallyReal(K) : "Currently only for totally real fields"; // TO DO

  // Note: sometimes get a better model using c4 and c6 here rather than Disc(E),
  // and occasionally helps marginally to use both c4 and c6 rather than just one 
  c4, c6 := Explode(cInvariants(E));
  C4 := Conjugates(c4);
  C6 := Conjugates(c6);
  v := [Log( Abs(C4[i])^(1/4) + Abs(C6[i])^(1/6) ) : i in [1..#C4]];
 
  u := 1/ClosestUnit(K, v : Units:=Units);

  a1, a2, a3, a4, a6 := Explode(Coefficients(E));
  Ered := EllipticCurve([a1*u, a2*u^2, a3*u^3, a4*u^4, a6*u^6]);
  Ered := tidy_model(Ered); // make model unique by choice of a1, a2, a3
  assert Discriminant(Ered) eq u^12*Discriminant(E);

  return Ered, Isomorphism(E, Ered);
end intrinsic;

