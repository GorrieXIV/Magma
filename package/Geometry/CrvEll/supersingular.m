////////////////////////////////////////////////////////////////////
//                                                                //
//                SUPERSINGULAR ELLIPTIC CURVES                   //
//                         David Kohel                            //
//                    Last modified January 2001                  //
//                                                                //
//                      mch - May 2010 -                          //	
//      added SupersingularPolynomial and changed                 // 
//      IsSuperSingular to use that.                              //
////////////////////////////////////////////////////////////////////

freeze;

forward IsClassOnejInvariant, IsSmallSS; 
forward CertifySupersingular, IsProbableExponent;

////////////////////////////////////////////////////////////////////
//                                                                //
//                 SUPERSINGULAR REPRESENTATIVE                   //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic SupersingularEllipticCurve(K::FldFin) -> CrvEll
   {A representative supersingular elliptic curve over K.}
   p := Characteristic(K);
   D := -3;
   while true do
      if D mod 4 in {0,1} and KroneckerSymbol(D,p) eq -1 then
         f := PolynomialRing(K)!HilbertClassPolynomial(D);
         S := Roots(f);
         if #S ne 0 then
            j := Rep(S)[1];
            break;
         end if;
      end if;
      D +:= -1;
   end while;
   return EllipticCurveWithjInvariant(j);
end intrinsic;

intrinsic SupersingularPolynomial(p::RngIntElt) -> RngUPolElt
{ The monic polynomial over GF(p) [p prime] whose roots are
  precisely the supersingular j invariants in characteristic p }

    require IsPrime(p) : "Argument 1 must be prime.";
    if p le 5 then return PolynomialRing(GF(p)).1; end if;
    k := GF(p);
    P := PolynomialRing(k);
    // Atkin: if G(X) is the reverse of H1(X) -the supersingular
    //  j poly with poss roots 0 and 1728 removed - then G is
    //  the reduction mod p of F(X) mod X^([p/12]+1) where
    //  F(X) is an integral powers series in X given by
    //  hypergeometric functions, viz
    //  F(X) = F(1/12,5/12;1,1728X) if p = 1 mod 4
    //  F(X) = F(7/12,11/12;1,1728X) if p = 3 mod 4 
    m := p div 12;
    coeffs := [k!1];
    if (p mod 4) eq 1 then
	a := 1/k!12; b := k!5/k!12;
    else
	a := k!7/k!12; b := k!11/k!12;
    end if;        
    u := k!1;
    k1 := k!1; k1728 := k!1728;
    for i in [1..m] do
	u *:= ((a*b*k1728)/(k!i)^2);
	Append(~coeffs,u);
	a  +:= k1; b +:= k1;
    end for;
    f := P!Reverse(coeffs);

    // add in x & (x-1728) factors
    if (p mod 4) eq 3 then
	f *:= (P.1-k1728);
    end if;
    if (p mod 3) eq 2 then
	f *:= P.1;
    end if;

    return f;

end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//             SUPERSINGULAR VS. ORDINARY BOOLEANS                //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic IsOrdinary(E::CrvEll) -> BoolElt
    {Returns true if ordinary, false if supersingular.}
    return not IsSupersingular(E);
end intrinsic;

intrinsic IsSupersingular(E::CrvEll : Proof := true) -> BoolElt
    {True iff the elliptic curve E is supersingular}

    FF := BaseRing(E);
    p := Characteristic(FF);    
    j := jInvariant(E);

    // Non-finite field case (added March 2009, SRD) -- not optimized

    if p eq 0 then
        return false;
    elif ( ISA(Type(FF),FldAlg) or ISA(Type(FF),FldFunG) ) and 
         forall{c : c in Coefficients(E) | IsCoercible(BaseRing(FF),c)} 
    then
        E1 := EllipticCurve(ChangeUniverse(Coefficients(E), BaseRing(FF)));
        return IsSupersingular(E1);
    elif not IsFinite(FF) then
        if not IsCoercible(GF(p), j) then  // ordinary if j not in GF(p^2) 
            try // in case HasRoot is not available for FF
                bool, r := HasRoot(MinimalPolynomial(GF(p^2).1), FF);
                success := true;
            catch ERR
                success := false;
            end try;
            if success and not bool then
                return false; // j not in GF(p) but j in FF ==> j not in GF(p^2)
            elif success then
                // TO DO: for various Type(FF), see if j is in the GF(p) span of 1 and r
            end if;
        end if;
        return Degree(DivisionPolynomial(E,p)) eq 0;
    end if;

    // FF is a finite field

    cm_test, D := IsClassOnejInvariant(j);
    if cm_test then
        return not (KroneckerSymbol(D,p) eq 1);
    elif p lt 200 then
        return IsSmallSS(j);    
    end if;

    jp := j^p; jp2 := jp^p;
    if jp2 ne j then
        return false;
    elif jp eq j then 
        e := 1; 
    else 
        e := 2;
    end if;

    if not (Degree(FF) eq e) then
        j := FiniteField(p,e)!j;
        E := EllipticCurveWithjInvariant(j);
    end if;

    // Characteristic is large and j-invariant is not 0 or 12^3 
    // so the groups structure must be 
    //    Z/2Z x Z/((p+1)/2)Z or  Z/(p+1)Z (e = 1); or 
    //    Z/(p-1)Z^2 or Z/(p+1)Z^2 (e = 2).

    if e eq 1 and not IsProbableExponent(E,p+1) then
       return false;
    elif e eq 2 then 
       if not ( IsProbableExponent(E,p-1) or 
                IsProbableExponent(E,p+1) ) then
          return false;
       end if;
    end if;

    if not Proof then 
        return true;
    end if;

    return CertifySupersingular(j);
end intrinsic;

intrinsic IsProbablySupersingular(E::CrvEll) -> BoolElt
    {Returns false if shown to be ordinary, true otherwise.}
    return IsSupersingular(E : Proof := false);
end intrinsic;

function IsClassOnejInvariant(j)
    FF := Parent(j); 
    j_list := [FF|0,54000,-12288000,1728,287496,-3375,8000,-32768,         
        -884736,-884736000,-147197952000,-262537412640768000];
    if j in j_list then
        D_list := [-3,-12,-27,-4,-16,-7,-8,-11,-19,-43,-67,-163]; 
        return true, D_list[Index(j_list,j)]; 
    end if;
    return false, 0;
end function;

function IsSmallSS(j)
    // Should use calls to a database of supersingular polynomials.

    p := Characteristic(Parent(j));
    if p in [ 2, 3, 5, 7, 13 ] then
        ss_test := j - 720;
    elif p in [ 11, 17, 19 ] then
        ss_test := j^2 - 1640*j - 748;
    elif p in [ 23, 29, 31, 37 ] then
        ss_test := j^3 - 155525*j^2 - 3140*j + 106053;
    elif p in [ 41, 43 ] then 
        ss_test := j^4 + 142*j^3 + 789*j^2 - 228*j - 41;
    elif p in [ 47, 53, 61 ] then
        ss_test := j^5 - 54901*j^4 + 46246*j^3 - 54263*j^2 
            + 36011*j - 14946;
    elif p in [ 59, 67, 73 ] then
        ss_test := j^6 - 83817*j^5 + 37663*j^4 + 85930*j^3 
            - 110995*j^2 - 125448*j + 62422;
    elif p in [ 71, 79 ] then
        ss_test := j^7 - 804*j^6 + 1713*j^5 + 159*j^4 
            - 1186*j^3 - 2414*j^2 + 1840*j + 1917;
    elif p in [ 83, 89, 97 ] then
        ss_test := j^8 - 293462*j^7 - 348705*j^6 - 256372*j^5 
            - 237163*j^4 - 146204*j^3 + 281497*j^2 + 278612*j 
            - 325028;
    elif p in [ 101, 103, 109 ] then
        ss_test := j^9 - 341219*j^8 - 48292*j^7 + 395887*j^6 
            - 224724*j^5 + 445186*j^4 - 487583*j^3 - 529265*j^2 
            - 9788*j + 19291;
    elif p in [ 107, 113 ] then
        ss_test := j^10 - 4121*j^9 + 1925*j^8 - 4533*j^7 
            - 2615*j^6 + 3437*j^5 + 3622*j^4 - 4558*j^3 
            - 4562*j^2 + 4719*j;
    elif p in [ 127 ] then
        ss_test := j^11 - 42*j^10 + 10*j^9 + 62*j^8 + 35*j^7 
            - 20*j^6 - 8*j^5 - 42*j^4 - 35*j^3 + 27*j^2 + 58*j - 51;
    elif p in [ 131, 137, 139 ] then
        ss_test := j^12 + 1182781*j^11 + 689023*j^10 + 967649*j^9 
            + 70279*j^8 - 676703*j^7 - 199997*j^6 - 1107259*j^5 
            + 828521*j^4 + 345654*j^3 - 1017964*j^2 - 616670*j + 1005032;
    elif p in [ 149, 151, 157 ] then
        ss_test := j^13 + 1684356*j^12 - 1387193*j^11 - 1431065*j^10 
            + 865075*j^9 - 1008521*j^8 + 1540692*j^7 + 494307*j^6 
            - 536760*j^5 - 1520906*j^4 - 999561*j^3 - 505204*j^2 
            + 492133*j - 520755;
    elif p in [ 163 ] then
        ss_test := j^14 + 11*j^13 + 24*j^12 + 68*j^11 + 32*j^10 
            - 13*j^9 + 69*j^8 + 44*j^7 + j^6 - 16*j^5 + 40*j^4 
            + 55*j^3 - 54*j^2 - j - 53;
    elif p in [ 167, 173, 181 ] then
        ss_test := j^15 - 1816094*j^14 + 697353*j^13 + 1817790*j^12 
            + 640152*j^11 + 2442284*j^10 - 944204*j^9 + 1465359*j^8 
            - 1651360*j^7 + 2118308*j^6 - 751840*j^5 - 1400077*j^4 
            - 966149*j^3 - 2207580*j^2 - 2358184*j + 982294;
    elif p in [ 179, 193 ] then
        ss_test := j^16 + 2955*j^15 + 13146*j^14 + 15348*j^13 
            - 1032*j^12 + 6156*j^11 - 11508*j^10 + 14138*j^9 
            - 11448*j^8 - 14045*j^7 - 9333*j^6 - 6421*j^5 
            + 7442*j^4 + 12946*j^3 - 14449*j^2 + 9505*j - 7697;
    elif p in [ 191, 197, 199 ] then
        ss_test := j^17 - 2737452*j^16 + 983016*j^15 
            - 1566747*j^14 + 967043*j^13 - 2727550*j^12 
            - 1050981*j^11 - 971244*j^10 - 2179299*j^9  
            + 661814*j^8 - 3341193*j^7 - 239717*j^6 - 89836*j^5 
            - 710212*j^4 - 2009139*j^3 - 2359555*j^2 + 3717404*j 
            + 1204064;
    end if;
    return IsZero(ss_test);
end function;

function IsProbableExponent(E,n)
    for i in [1..8] do
        P := n*Random(E);
        if not IsIdentity(P) then 
           return false;
        end if; 
    end for;
    return true;
end function;

function CertifySupersingular(j)
    FF := Parent(j);
    p := Characteristic(FF);

    // Find a sequence of sufficiently many primes.
    ell := 2;
    SQ := [ ell ];
    prime_prod := ell;
    while prime_prod lt 2*p do
        ell := NextPrime(ell : Proof := false);
        Append(~SQ,ell);
        prime_prod *:= ell;
    end while;

    // Characterize by modular splitting of j-invariant.
    P2 := PolynomialRing(FF,2); 
    R := PolynomialRing(FF); 
    x := R.1;
    for ell in SQ do 
        if ell lt 101 and ell mod 12 ne 11 then
	    phi := UnivariatePolynomial(
	               Evaluate(P2!CanonicalModularEquation(ell),2,j));
        else
            phi := UnivariatePolynomial(
                       Evaluate(P2!AtkinModularEquation(ell),2,j));
        end if;
        null_test := Modexp(x,p^2,phi) - x;
        if null_test ne 0 then
            // Modular equation may not have distinct roots;
            // have to count multiplicities.
            h := Degree(GCD(null_test,phi));
            k := Degree(GCD(phi,Derivative(phi)));
            if h  + k ne (ell+1) then 
                vprint ECPointCount: 
                    "Failed to certify curve as supersingular.";
                return false;
            end if;
        end if;
    end for;
    return true;
end function;
