freeze;

///////////////////////////////////////////////////////////////////////
//                                                                   //
//                 PERIODS AND ELLIPTIC LOGARITHMS                   //
//                                                                   //
///////////////////////////////////////////////////////////////////////

/*
Intrinsics:
   RealPeriod
   FundamentalVolume & FaltingsHeight (Jan 2007, MW)
   pAdicEllipticLogarithm
*/

intrinsic RealPeriod(E::CrvEll[FldRat] : Precision:=0) -> FldReElt
{Returns the real period of an elliptic curve.}
  if Precision ne 0 then return Real(Periods(E : Precision := Precision)[1]);
  else return Real(Periods(E)[1]); end if; end intrinsic;

intrinsic FundamentalVolume(E::CrvEll[FldRat] : Precision:=0) -> FldReElt
{Returns the fundamental volume of an elliptic curve.}
 if Precision ne 0 then p:=Periods(E : Precision := Precision);
 else p:=Periods(E); end if; return Real(p[1])*Imaginary(p[2]); end intrinsic;

intrinsic FaltingsHeight(E::CrvEll[FldRat] : Precision:=0) -> FldReElt
{Returns the (logarithmic) Faltings height of an elliptic curve}
 E:=MinimalModel(E);
 if Precision ne 0 then V:=FundamentalVolume(E : Precision := Precision);
 else V:=FundamentalVolume(E); end if;
 P:=PrimeDivisors(Denominator(jInvariant(E)));
 X:=&*[Integers()|p^Valuation(Discriminant(E),p) :p  in P];
 return Log(X)-Log(Abs(Discriminant(E)))/12-Log(V)/2; end intrinsic;

// can generalise to curves over number fields, but need tau for embeddings
intrinsic FaltingsHeight2(E::CrvEll[FldRat] : Precision:=0) -> FldReElt
{Returns the Faltings height of an elliptic curve.}
 E:=MinimalModel(E);
 if Precision ne 0 then p:=Periods(E : Precision:=Precision);
  PI:=Pi(RealField(Precision));
 else p:=Periods(E); PI:=Pi(Parent(Real(p[1]))); end if;
 tau:=p[2]/p[1]; O:=Abs((2*PI)^(12)*Delta(tau)*Imaginary(tau)^6);
 P:=PrimeDivisors(Denominator(jInvariant(E)));
 X:=&*[Integers()|p^Valuation(Discriminant(E),p) :p  in P];
 return Log(X/O)/12; end intrinsic;


///////////////////////////////////////////////////////////////////////
//                    p-adic elliptic logarithm                      //
//                    Steve Donnelly, Nov 2009                       //
///////////////////////////////////////////////////////////////////////

intrinsic
pAdicEllipticLogarithm(P::PtEll, p::RngIntElt : Precision:=20) -> FldPadElt
{The p-adic logarithm of the specified point on an elliptic curve over Q}

    E := Curve(Parent(P));
    require Type(BaseRing(E)) eq FldRat :
           "The first argument must be a point on an elliptic curve over Q";
    require IsIntegralModel(E): "The elliptic curve must have integer coefficients";
    require IsPrime(p): "The second argument must be a prime integer";
    require Type(Ring(Parent(P))) in {FldRat, RngInt} 
            or forall{c : c in Eltseq(P) | RelativePrecision(c) ge Precision} :
           "The given point has too low precision";

    return pAdicEllipticLogarithmOfCombination([P], [1], p : Precision:=Precision);
end intrinsic;

intrinsic pAdicEllipticLogarithmOfCombination(points::SeqEnum[PtEll], coeffs::SeqEnum, p::RngIntElt 
                                             : Precision:=20) -> FldPadElt
{"} // "
    E := Curve(Universe(points));
    require Type(BaseRing(E)) eq FldRat :
           "The first argument must be a sequence of points on an elliptic curve over Q";
    require IsIntegralModel(E): "The elliptic curve must have integer coefficients";
    require IsPrime(p): "The third argument must be a prime integer";
    require coeffs cmpeq [1] or Type(Ring(Universe(points))) in {FldRat, RngInt} : 
           "The given points should have coordinates in Q or Z";

    n := Max(2, Ceiling(Sqrt(Precision)));
    Omega := FormalLog(E : Precision:=n, ReturnPoint:=false);

    // Let m be the order of E(Q_p)/E_1(Q_p)
    type := ReductionType(E, p);
    if type eq "Good" then
      m := p + 1 - FrobeniusTraceDirect(E, p);
    elif type eq "Additive" then
      m := TamagawaNumber(E, p) * p;
    elif type eq "Split multiplicative" then
      m := TamagawaNumber(E, p) * (p-1);
    elif type eq "Nonsplit multiplicative" then
      m := TamagawaNumber(E, p) * (p+1);
    end if;

    // For P in E_0(Q_p), want Omega(p^k*P) to have relative precision >= Precision
    // Choose k such that E_k(Q_p) is contained in the domain of log, and such that 
    //  k*n - Ilog(p,n) > prec + k + k0,
    // since the nth term of Omega(p^k*m*P) has valuation at least k*n - Ilog(p,n)
    k0 := Valuation(m, p);
    k := Ceiling( (Precision + Ilog(p,n) + k0)/(n-1) );
    k := Max(k, (p eq 2) select 2 else 1);
    m *:= p^k;

    if IsExact(Ring(Universe(points))) then
      prec := Precision;
      repeat
        // MUST create a new pointset (with a new Qp) each time
        prec +:= 20;
        Qp := pAdicField(p : Precision:=prec); 
        P := &+ [coeffs[i] * E(Qp)!points[i] : i in [1..#points]];
        Q := m*P;
      until forall{c : c in Eltseq(Q) | RelativePrecision(c) ge Precision};
      Qp`DefaultPrecision := Precision; // Qp is the parent of returned value
    else
      // this loses a lot of precision (TO DO: why?)
      P := &+ [coeffs[i] * points[i] : i in [1..#points]];
      Q := m*P; 
      // TO DO: Qp was never defined in this case, oops
    end if;
    z := -Q[1]/Q[2];
    l := Evaluate(Omega, Qp!z); 
    return l/m + O(Qp!p^Precision);
end intrinsic;

/* temp code for E/K - MW 21 Jan 2010 */

function ComplexAGM1(y) prec:=Precision(y);
 a:=(1+y)/2; m:=Sqrt(y); d1:=Abs(a-m); d2:=Abs(a+m);
 if d1 gt d2 then m:=-m; d1:=d2; end if;
 if d1 lt 5*10^(-prec) then return a; end if;
 return a*ComplexAGM1(m/a); end function;

function ComplexAGM(x,y) return x*ComplexAGM1(y/x); end function;

intrinsic AGM(x::FldComElt,y::FldComElt) -> FldComElt
{Compute an AGM of two complex numbers}
 if IsWeaklyZero(x*y) then return Parent(x)!0; end if;
 return ComplexAGM(x,y); end intrinsic;

intrinsic AGM(x::FldComElt,y::FldReElt) -> FldComElt
{Compute an AGM of two complex numbers}
 if IsWeaklyZero(x*y) then return Parent(x)!0; end if;
 return ComplexAGM(x,ComplexField(Parent(y))!y); end intrinsic;

intrinsic AGM(x::FldReElt,y::FldComElt) -> FldComElt
{Compute an AGM of two complex numbers}
 if IsWeaklyZero(x*y) then return Parent(x)!0; end if;
 return ComplexAGM(y,x); end intrinsic;

PREC:=Precision;
function MyBPeriods(B : prec:=PREC(ComplexField()))
 b2,b4,b6:=Explode(B); poly:=Polynomial([b6,2*b4,b2,4]);
 roo:=Roots(poly,ComplexField(prec)); roo:=[r[1] : r in roo];
 e13:=Sqrt(roo[1]-roo[3]); e12:=Sqrt(roo[1]-roo[2]); e23:=Sqrt(roo[2]-roo[3]);
 twopi:=2*Pi(RealField(prec)); I:=ComplexField(prec).1;
 return [twopi/ComplexAGM(e12,e13)/2,twopi*I/ComplexAGM(e23,e13)/2];
end function;

intrinsic
Periods(E::CrvEll[FldNum] :  Precision:=PREC(ComplexField())) -> SeqEnum
{Periods of an elliptic curve defined over a number field,
 one pair for each embedding}
 CC:=ComplexConjugate; FP:=Precision;
 if Precision lt 10 then Precision:=10; end if;
 Precision:=Precision+Min(50,5+(Precision div 4));
 K:=BaseRing(E); IP:=InfinitePlaces(K); b2,b4,b6:=Explode(bInvariants(E));
 D:=[[* Evaluate(b2,ip : Precision:=Precision+20),
	Evaluate(b4,ip : Precision:=Precision+20),
	Evaluate(b6,ip : Precision:=Precision+20), ip *] : ip in IP];
 B:=[[d[1],d[2],d[3]] : d in D] cat
     [[CC(d[1]),CC(d[2]),CC(d[3])] : d in D | not IsReal(d[4])];
 return [ChangeUniverse(MyBPeriods(b : prec:=Precision),ComplexField(FP)) :
			 b in B]; end intrinsic;

intrinsic
EllipticCurveFromPeriods(om::SeqEnum[FldComElt] : Epsilon:=0.001) -> CrvEll
{Given the real and imaginary periods of a minimal model for an elliptic
 curve over Q, construct the elliptic curve corresponding to it.}
 C:=Parent(om[1]); u:=2*Pi(C)/om[1]; rat:=om[2]/om[1];
 require Imaginary(rat) gt 0: "Ratio is not in upper half-plane";
 c4:=Eisenstein(4,rat)*u^4; c6:=Eisenstein(6,rat)*u^6;
 a:=-27*Real(c4); b:=-54*Real(c6);
 err4:=Abs(Round(a)-a); err6:=Abs(Round(b)-b); eps:=Epsilon;
 require err4 lt eps and err6 lt eps: "Periods do not a curve over Q";        
 E:=MinimalModel(EllipticCurve([Round(a),Round(b)])); return E; end intrinsic;
