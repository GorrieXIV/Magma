freeze;


/************************* LAYOUT OF THE FILE ******************************/
/***** (1) ATTRIBUTES OF LSER
/***** (2) BASIC INTRINSICS DEFINING THE LSER TYPE
/***** (3) SOME HELPFUL ONE-LINERS
/***** (4) LAURENT EXPANSION OF THE GAMMA FACTOR
/***** (5) DIRICHLET COEFFICIENTS: GROWTH, NUMBER AND GENERATION
/***** (6) COMPUTING PHI AND G:
/*****     TAYLOR EXPANSIONS, RECURSIONS AT INFINITY AND CONTINUED FRACTIONS
/***** (7) FUNCTIONAL EQUATION
/***** (8) COMPUTING L(S) AND ITS TAYLOR EXPANSION
/***** (9) GENERAL LSER SIGNATURE
/***** (10) ARITHMETIC WITH LSERIES [moved to arithmetic.m]
/***** (11) OTHER BUILT-IN LSER SIGNATURES [moved to create.m]
/*****
/***** please email me (timdok@gmail.com) for bugs and the like
/**************************************************************************/
/***** "todo" things are marked with //! throughout the file
/**************************************************************************/


/***** (1) ATTRIBUTES OF LSER *****/

declare type LSer;

declare verbose LSeries,3;

// MAIN INVARIANTS OF AN L-SERIES
// conductor: real positive, conductor of the L-function
// gamma:     vector [g_1,...,g_d] of (rational) gamma parameters;
//            gamma factor of L(s) is the product over k of Gamma((s+g_k)/2)
// weight:    real positive, func. eq. relates L(s)<->L(weight-s)
// sign:      complex, sign in the functional equation
//            if =0 (meaning undefined, default) will be
//            determined by CheckFunctionalEquaion(L) or any of the L-series evaluation functions
// lpoles:    [] by default, sequence of (simple) poles of L^*(s) with Re(s)>weight/2
// lresidues: sequence of residues in there. If undefined (default), will be
//            determined by CheckFunctionalEquaion(L) or any of the L-series evaluation functions

declare attributes LSer: conductor, weight, sign, gamma, lpoles, lresidues;
declare attributes LSer: effwt; // though Tim-ified to be +1 more than expected

// OPTIONAL PARAMETERS
// precision: main precision to which L(s) is computed,
// Parent:    any type, L-series of what is this one, used
//            to compare two L-series (if parent is defined)
// Name:      used for printing
// ImS:   0 by default, largest Im(s) for which L(s) is going to be called
// cutoff:    1.2 by default, used in CheckFunctionalEquaion(L)
// cfgrowth:  function f(LSer L,real t) that determines the growth of the
//            coefficients a_n for n=t. Must be an increasing function,
//            by default is set to DefaultCfGrowth(L,t)

declare attributes LSer: signfun, lresiduesfun;

// FUNCTIONS TO RE-CALCULATE REAL PARAMETERS IF PRECISION IS CHANGED
// lresiduesfun: if this is set, it is a function that computes lresidues,
//               this is done every time when LSetPrecision is called
// signfun:      same for the sign

declare attributes LSer: precision, parent, name, ImS, cutoff, cfgrowth;

// DATA ASSOCIATED TO THE GAMMA-FACTOR
// expfactor:       exponential factor in the functional equation
//                    = sqrt(conductor/Pi^d) where d=#L`gamma;
// gammapoles:      representatives of poles of the gamma factor (mod 2Z)
// gammapoleorders: and their multiplicites

declare attributes LSer: expfactor, gammapoles, gammapoleorders;

// VARIOUS PRECISIONS USED IN COMPUTATIONS, APART FROM THE MAIN L`precision
//
// taylorprecision: internal precision used for Phi and G computed at 0
//     this is quite high since when using Taylor expansions at 0 to compute
//     these special functions, a lot of cancellation occurs
// asympprecision:  internal precision used for Phi and G computed at infinity
// termprecision:   precision of output of Phi and G; these are used as
//     terms in various series, hence the name
// lfunprecision:   precision used in LStar(s)
//     this is lower than termprecision (or, rather, termprecision is set to
//     be higher), since extra cancellation occurs for weight>1 due to the
//     size of the gamma-factor
// technical note: these are reals, not rounded to the nearest integer
// the corresponding real & complex fields are also declared here

declare attributes LSer: lfunprecision, asympprecision,
                         termprecision, taylorprecision;
declare attributes LSer: LfunReals, LfunComplexes, TermReals, TermComplexes;
declare attributes LSer: TaylorReals, TaylorComplexes,
                         AsympReals, AsympComplexes;


// cffun:      this is passed as a parameter to the main LSeries() procedure
//             and remembered here. This is the source of Dirichlet coeffs
// cftype:     0,1,2 meaning one of the following:
               lcf_list           := 0;
               lcf_localfactors   := 1;
               lcf_function       := 2;
// cfvec:      vector of Dirichlet coeffs that have already been evaluated
// cfrequired: this many coefficients are necessary to generate
// cfprecpar:  true iff cffun is a function that has Precision parameter
// cfmax:      do not store more coefficients than this (default cfmaxdefault)
               cfmaxdefault:=10^7;

declare attributes LSer: cffun, cfvec, cfrequired, cftype, cfprecpar, cfmax;
declare attributes LSer: cffuncK,degreeK,hodgeK,condK; // Mark's attr Lseries/K
declare attributes LSer: aacoeff,known_ef,EF_SAVE_LIM; // assoc array of coeffs
declare attributes LSer: SAVE; // Euler factors, HGMs

// Technical parameters that remember the data used to compute Phi and G
// and also to decide when to use Taylor and when to use continued fractions
// of asymptotic expansions

declare attributes LSer: asymptotics, maxasympcoeff, phiV, phiVnn, phiVser;
declare attributes LSer: recF, recG, lastt, PhiCaseBound, GCaseBound, termstep;
declare attributes LSer: logsum, Gvec, fcf, gcf, gncf, fncf,
                         phiinfterms, Ginfterms;

// constants in asymptotic expansions of phi and G
declare attributes LSer: expdifff, asympconstf, expdiffg, asympconstg;

// last calculated values in G and FullGammaSeries to avoid re-calculation
declare attributes LSer: last_fgs_s, last_fgs_terms, last_fgs_val,
                         last_g_logsum, last_g_s;

// if the L-function is a product or quotient of other L-series, then
//   prod = [<L1,n1>,...,<Lk,nk>] with L_i L-series, n_i exponents
// and all evaluation functions do it separately on the constituents, and
// only prod, parent, name and precision are used. Otherwise prod = false;
declare attributes LSer: prod;

declare attributes LSer: object; // MW: like parent, but I understand it better

// How often to print progress indicator when generating coefficients
// and computing series when verbose LSeries is at least 3
// defaults are 1000 and 5000 respectively
declare attributes LSer: vprint_coeffs, vprint_series;

declare attributes LSer: maxcoeff; // max# of coeff, even when not a list (MW)

declare attributes ModFrmElt : ef_warning;

/***** (2) BASIC INTRINSICS DEFINING THE LSER TYPE *****/

function lser_string(L,level)
 if Type(L) eq MonStgElt then return L; end if;
 if Type(L) eq Tup then S:="";
  for i:=1 to #L do
   if Type(L[i]) ne MonStgElt and Type(L[i]) ne Tup and Type(L[i]) ne LSer
    then S*:=Sprint(L[i],level); else S*:=lser_string(L[i],level); end if;
   end for; return S; end if;
 if Type(L) ne LSer then return Sprint(L,level); end if;
 if (level eq "Magma") and (Type(L`name) ne Tup) then
  return Sprintf("LSeries(%o)",Sprint(L`parent,"Magma")); end if;
 if Type(L`name) ne Tup then
  return Sprintf("L-series of %o",Sprint(L`name,level)); end if; S:="";
 for i:=1 to #L`name do
  if Type(L`name[i]) ne MonStgElt and Type(L`name[i]) ne Tup
   and Type(L`name[i]) ne LSer then S*:=Sprintf("%o",Sprint(L`name[i],level));
  else S*:=lser_string(L`name[i],level); end if; end for;
 return S; end function;

procedure PrintTuple(L,level) // lser_string "fixes" part of newline problem
 gc:=GetColumns(); SetColumns(0); S:=lser_string(L,level); SetColumns(gc);
 printf "%o",S; return; end procedure;

intrinsic HackobjPrintNamedLSer(L::LSer, name::MonStgElt, level::MonStgElt) {}
 if (name ne "$") and (level eq "Minimal") then
  printf "%o",name; return; end if;
 PrintTuple(L,level); end intrinsic;

intrinsic Print(L::LSer, level::MonStgElt) {}
 PrintTuple(L,level); end intrinsic;

intrinsic IsCoercible(x::LSer, y::.) -> BoolElt, . {}
 return false, _; end intrinsic;

intrinsic 'in'(x::LSer, y::.) -> BoolElt {} return false; end intrinsic;


/***** (3) SOME HELPFUL ONE-LINERS *****/
     
// Evaluate an element f in R(x)[y] at x=v
EvaluateBelow := func<f,v | PolynomialRing(BaseRing(BaseRing(f)))!
			      [Evaluate(g,v) : g in Eltseq(f)]>;

// Check whether x is close to zero (tolerance is 10^(d-Precision(x)))
IsCloseZero:=func<x,d|Abs(x) le 10^(d-Precision(x))>;

// Check whether x is close to an integer (tolerance is 10^(d-Precision(x)))
IsCloseInt:=func<x,d|Type(x) eq RngIntElt or
                     (Type(x) eq FldRatElt and Denominator(x) eq 1) or
                     Abs(x-Round(Real(x))) le 10^(d-Precision(x))>;

// Largest/smallest abs. value of coefficients of a Laurent series or a vector
VMax:=func<x|Max([Abs(t): t in Eltseq(Vector(x))])>;
VMin:=func<x|Min([Abs(t): t in Eltseq(Vector(x))])>;

// nargs: Number of arguments of a function
// hasprecpar: does it have an optional parameter precision (assumed at most 1)
nargs:=func<f|#Split(s,",")-Min(1,Position(s,"()"))-Min(1,Position(s,"( ["))
  where s is Sprint(f)>;
hasprecpar:=func<f|Position(Sprint(f),"[ Precision ]") ne 0>;

// Difference of two lists
function ExcludeList(L1,L2)
 for x in L2 do Exclude(~L1,x); end for; return L1; end function;

//Given a floating real/complex number, change its precision to r digits
//ChangePrec:=func<x,r|ComplexField(r)!x>;
//RChangePrec:=func<x,r|RealField(r)!Real(x)>;

// Like ChangePrec but for Laurent series
function ChangePrecSeries(s,C) P:=LaurentSeriesRing(C,Precision(Parent(s)));
 return (P!1-P!1)+P.1^Valuation(s)*P![C!x:x in Eltseq(s)]; end function;

function RChangePrecSeries(s,R) P:=LaurentSeriesRing(R,Precision(Parent(s)));
 return (P!1-P!1)+P.1^Valuation(s)*P![R!Real(x):x in Eltseq(s)]; end function;

/***** (4) LAURENT EXPANSION OF THE GAMMA FACTOR *****/

// GammaSeries(z0,terms)
// Taylor series expansion of Gamma(z0+x) around 0, z0 arbitrary complex
// - up to O(x^(terms+1))
// - uses precision of z0
// - makes use of Gamma(complex number) and Gamma(power series)
// See Luke "Mathematical functions and their approximations", section 1.4
// note a misprint there in the recursion formulas [(z-n) term in c3 below]

function GammaSeries(z0,terms)
  bitprec:=Precision(z0: Bits:=true);
  prec:=Precision(z0);
  err:=10^(1-prec);
  negint:=IsCloseInt(z0,1) and (Re(z0) le 0.5); // Gamma has a pole?
  R:=Parent(z0);
  pterms:=terms+(negint select 2 else 1);
  P:=LaurentSeriesRing(R,pterms);
  if (terms eq 0) and not negint then   // built-in Gamma function
    return P!Gamma(z0);
  end if;
  // frequent special cases: z0=0,1,2
  if IsCloseZero(z0,1)   then return P!Gamma(1+P.1)/P.1; end if;
  if IsCloseZero(z0-1,1) then return P!Gamma(1+P.1); end if;
  if IsCloseZero(z0-2,1) then return P!Gamma(1+P.1)*(1+P.1); end if;

  // reflect about Re(z)=1/2 when Re(z) is small
  reflect:=Re(z0) le 0.5;
  if reflect then z0:=1-z0; end if;

  R:=ComplexField(prec+3); //! check // geh: deg 20 example needs prec+5
  z0:=R!z0;
  P:=LaurentSeriesRing(R,pterms);
  z:=z0+P.1;

  Avec:=[1,(z+6)/2,(z^2+82*z+96)/6,(z^3+387*z^2+2906*z+1920)/12];
  Bvec:=[1,4,8*z+28,14*z^2+204*z+310];
  Qvec:=[0,0,0,Avec[4]/Bvec[4]];
  n:=4;
  tolerance:=0.1^(prec+1.5); //! check
  repeat
    c1:=(2*n-1)*(3*(n-1)*z+7*n^2-9*n-6);
    c2:=-(2*n-3)*(z-n-1)*(3*(n-1)*z-7*n^2+19*n-4);
    c3:=(2*n-1)*(n-3)*(z-n)*(z-n-1)*(z+n-4);
    c0:=(2*n-3)*(n+1);
    Append(~Avec,(c1*Avec[n]+c2*Avec[n-1]+c3*Avec[n-2])/c0);
    Append(~Bvec,(c1*Bvec[n]+c2*Bvec[n-1]+c3*Bvec[n-2])/c0);
    Append(~Qvec,Avec[n+1]/Bvec[n+1]);
    err:=VMax(Coefficients(Qvec[n+1]-Qvec[n]));
    n+:=1;
  until err le tolerance;
  pi:=Pi(R);
  gamma:=EulerGamma(R);
  res:=Gamma(z0)*Exp(Integral(-gamma+2*(z-1)/z*Qvec[n]));
  if reflect then
    sinser:=Sin(pi*z);
    if negint then sinser:=sinser-Coefficient(sinser,0); end if;
    res:=Evaluate(pi/(res*sinser),-P.1);
  end if;

  if IsReal(z0)
    then return RChangePrecSeries(res,RealField(bitprec: Bits:=true));
    else return ChangePrecSeries(res,ComplexField(bitprec: Bits:=true));
  end if;

end function;


// fullgammaseries(ss,extraterms)
//   Laurent series for the gamma factor without the exponential factor, i.e.
// Gamma((s+gamma[1])/2)*...*Gamma((s+gamma[d])/2)
// around s=ss with a given number of extra terms.

function fullgammaseries(L,s,extraterms)
  if (s ne L`last_fgs_s) or (Precision(s) ne Precision(L`last_fgs_s)) or
			   (extraterms ne L`last_fgs_terms) then
    GSD:=extraterms + &+[ IsCloseInt((s+L`gammapoles[j])/2,1)
        select L`gammapoleorders[j] else 0 : j in [1..#L`gammapoles]];
    L`last_fgs_s:=s;
    L`last_fgs_terms:=extraterms;
    ser:=&*[GammaSeries((s+x)/2,GSD) : x in L`gamma];
    L`last_fgs_val:=Evaluate(ser,Parent(ser).1/2);
 end if;
 return L`last_fgs_val;
end function;


/***** (5) DIRICHLET COEFFICIENTS: GROWTH, NUMBER AND GENERATION *****/

// Default growth rate of the coefficients of a motivic L-function
function DefaultCfGrowth(L,t)
 if #L`lpoles gt 0 // bleh
    then return 1.5*t^(Max([Max(Re(x),Re(L`effwt-x)):x in L`lpoles])-1);
    else return Sqrt(4*t)^(L`effwt-1); end if; end function;

function ExtraPrecision(gamma, expfactor, weight, effwt, maximg)
  if IsEmpty(gamma) then return 0; end if;
  s:=0.7*effwt+maximg*ComplexField(6).1;
  fullgamma:=expfactor^s * &*[Gamma((s+x+weight-effwt)/2) : x in gamma];
  return Max(0.0,-Log(10,Abs(fullgamma)));
end function;

// LCfRequired( L )
// number of coefficients necessary to compute with the L-series

intrinsic LCfRequired(L::LSer: Precision:=0) -> RngIntElt
{How many Dirichlet coefficients are needed to compute L(s)}
  require Type(Precision) cmpeq RngIntElt and (Precision ge 0):
    "Precision must be either 0 (current for L(s)) or a positive integer";
  if Precision eq 0 then Precision:=L`precision; end if;
  if L`prod cmpne false then
    lr:=Max([LCfRequired(t[1]: Precision:=Precision): t in L`prod] cat [0]);
    return lr; end if;
  d:=#L`gamma; if d eq 0 then return 1; end if;
  expfactor:=Sqrt(L`conductor/Pi(RealField(Precision))^#L`gamma);
  lfunprecision:=
     Precision+0.6+ExtraPrecision(L`gamma,expfactor,L`weight,L`effwt,L`ImS);
  expdifff:=(1+&+L`gamma)/d-1+(L`weight-L`effwt)/2;
  asympconstf:=2*&*[Gamma(k/d):k in [1..d]];
  err:=0.1^lfunprecision; t1:=0; t2:=2;
  repeat
    t:=(t1 ne 0 select (t1+t2)/2 else t2);
    tt:=t/L`cutoff/expfactor;
    res:=L`cfgrowth(L,t) * asympconstf*Exp(-d*tt^(2/d))*tt^expdifff;
    if t1 ne 0
      then if res gt err then t1:=t; else t2:=t; end if;
      else if res lt err then t1:=t2/2; else t2:=2*t2; end if; end if;
  until t2-t1 le 1; return Ceiling(t2); end intrinsic;

function ToSeries(c,d)
  B:=Type(c) in [RngUPolElt,FldFunRatUElt,RngSerPowElt,RngSerLaurElt]
     select BaseRing(Parent(c)) else Parent(c);
  return PowerSeriesRing(B, 1+d)!c;
end function;

function Vec2InvSer(v,d)
 R:=PowerSeriesRing(Universe(v),1+d); return 1/R!v; end function;

// this needs re-thinking... recomputation intervals are likely short
procedure CoefficientsFromLocalFactors(~V,f,N,printfrequency,Precision)
 have:=#V; hasprec:=hasprecpar(f); last_print:=0; Z:=Integers();
 if have eq 0 then V:=[* 1 :k in [1..N] *]; have:=1;
 else V cat:=[* 1 :k in [have+1..N] *]; end if;
 for p in PrimesUpTo(N) do d:=Ilog(p,N); A:=[* 0:i in [1..d] *];
  if p ge last_print+1000 then last_print:=p;
   vprint LSeries,3:
    Sprint(p)*"/"*Sprint(N)*" ["*Sprint(Round(100*p/N))*"%]"; end if;
  if Ilog(p,N) eq Ilog(p,have) then
   c:=1/ToSeries(Polynomial([V[p^u] : u in [0..Ilog(p,have)]]),d);
  elif hasprec then c:=f(p,d: Precision:=Precision); else c:=f(p,d); end if;
  S:=1/ToSeries(c,d); for j in [1..d] do A[j]:=Coefficient(S,j); end for;
// this should only need the ToSeries when Ilog differ
  for j in [1..d] do if IsCoercible(Z,A[j]) then A[j]:=Z!A[j]; end if; end for;
  for k in [1..d] do pk:=p^k; for j in [Ceiling(have/pk)..Floor(N/pk)] do
   if j mod p eq 0 or j*pk le have then continue; end if;
   V[j*pk]*:=A[k]; end for; end for; end for; end procedure;

// Generate and store the necessary number of coefficients for the L-series

intrinsic LSetCoefficients(L::LSer, cffun::Any)
{Set coefficients of the L-series. The options are
   LSetCoefficients(L,[1,1,1,1,1,1]);  // pre-computed vector of a_n's
   LSetCoefficients(L,func<n|1>);      // a_n as a function of n
   LSetCoefficients(L,func<p,d|1-x>);  // inv local factor at p [+O(x^(d+1))]
in the last two cases the function may have an optional parameter "Precision",
if your coefficients are real/C numbers rather than integers/rationals, e.g.
   LSetCoefficients(L,func<n:Precision| Pi(RealField(Precision))^n >);
}
  require ((Type(cffun) in [SeqEnum,List]) and (#cffun gt 0))
  or ((Type(cffun) cmpeq UserProgram) and (nargs(cffun) in [1..2])):
    "cffun must be either a non-empty sequence of coefficients [a1..ak], "*
    "a function a(n) or a local factor function l(p,d)";
  L`cffun:=cffun;
  if (Type(cffun) in [SeqEnum,List]) then  L`cftype:=lcf_list;
  elif nargs(cffun) eq 2 then              L`cftype:=lcf_localfactors;
  else                                     L`cftype:=lcf_function; end if;
  L`cfprecpar:=L`cftype eq lcf_list select false else hasprecpar(L`cffun);
  delete L`cfvec;
end intrinsic;

intrinsic Coefficient(L::LSer, n::RngIntElt) -> .
{nth coefficient of the L-series L(s)}
//  if IsDefined(L`aacoeff,n) then return L`aacoeff[n]; end if;
  if n eq 1 then return 1; end if;
  if assigned L`cfvec and (n le #L`cfvec) then return L`cfvec[n]; end if;
  if L`cftype eq lcf_list then
   return n le #L`cffun select L`cffun[n] else 0; end if;
  if L`cftype eq lcf_function then
   c:=L`cfprecpar select L`cffun(n: Precision:=L`precision) else L`cffun(n);
   L`aacoeff[n]:=c; return c; end if;
  primepower,p,m:=IsPrimePower(n); Z:=Integers(); // From local factors
  if not primepower then
   return &*[Coefficient(L,F[1]^F[2]): F in Factorisation(n)]; end if;
  if L`cfprecpar then c:=L`cffun(p,m: Precision:=L`precision);
                 else c:=L`cffun(p,m); end if;
  c:=Coefficient(1/ToSeries(c,m),m); if IsCoercible(Z,c) then c:=Z!c; end if;
  L`aacoeff[n]:=c; return c; end intrinsic;

procedure GenerateCoefficients(L,need)
  need:=Min(need,L`cfmax);
  if not assigned L`cffun then
    error "Coefficients have not yet been specified";
  end if;
  cffun:=L`cffun;
  precision:=L`precision;
  if not assigned L`cfvec then
    L`cfvec:=[* *]; // and if it is assigned, we let it grow
  end if;
  have:=#L`cfvec;
  if need le have then return; end if;
  needstr:=Sprint(have+1)*".."*Sprint(need);
  if L`cftype eq lcf_list then
    if have eq 0 then
      vprint LSeries,2:
         "Assigning "*Sprint(#cffun)*" coefficients from the supplied vector";
      L`cfvec:=[* x: x in cffun *];
    end if;
  elif L`cftype eq lcf_localfactors then
    vprint LSeries,2: "Generating coefficients "*needstr*" from local factors";
   CoefficientsFromLocalFactors(~L`cfvec,cffun,need,L`vprint_coeffs,precision);
  else
    vprint LSeries,2: "Computing coefficients "*needstr;
    if L`cfprecpar
      then L`cfvec:=L`cfvec cat
                    [* cffun(k: Precision:=precision): k in [have+1..need] *];
      else L`cfvec:=L`cfvec cat [* cffun(k): k in [have+1..need] *];
    end if;
  end if;
  if not forall{c: c in L`cfvec| IsCoercible(C,c)}
          where C is ComplexField(L`precision)
    then error "Coefficients must be numbers, coercible into ComplexField()";
  end if;
end procedure;


function MultiplicativityCheck(L)
  if L`cftype eq lcf_localfactors then return true; end if;
  GenerateCoefficients(L,12); v:=[Coefficient(L,n): n in [1..12]];
  numeq:=func<x,y|Abs(x-y) lt 10^(1/3-2/3*p)> where p is L`precision;
  return numeq(v[1],1)
    and ((#L`cfvec lt 6) or (numeq(v[6],v[2]*v[3])))
    and ((#L`cfvec lt 10) or (numeq(v[10],v[2]*v[5])))
    and ((#L`cfvec lt 12) or (numeq(v[12],v[3]*v[4])));
end function;

function MaxCoefficients(L)
  if assigned L`maxcoeff then return L`maxcoeff; end if;
  return L`cftype eq lcf_list select #L`cffun else 10^50;
end function;

intrinsic LGetCoefficients(L::LSer, N::RngIntElt) -> List
{The sequence of first N coefficients of the L-series}
  GenerateCoefficients(L,N);
  return [* Coefficient(L,k): k in [1..Min(N,MaxCoefficients(L))] *];
end intrinsic;

intrinsic LSeriesData(L::LSer : Hodge:=false) -> Tup
{Return the tuple of invariants of the L-function
  <weight, gamma, conductor, cffun, sign, poles, residues>
This is the data that can be used to create L with LSeries}
 if Hodge then HS:=HodgeStructure(L);
  return <L`weight,HS,L`conductor,L`cffun,L`sign,L`lpoles,L`lresidues>; end if;
 return <L`weight,L`gamma,L`conductor,L`cffun,L`sign,L`lpoles,L`lresidues>;
end intrinsic;

function LocalFactorFun(L, precision)
  if not assigned L`cffun then
    error "Cannot compute local factors: coefficients are not yet assigned";
  end if;
  f:=L`cffun;
  if Type(f) cmpeq UserProgram and nargs(f) eq 2 then 
    if L`cfprecpar
      then loc:=func<p,d|f(p,d:Precision:=precision)>;
      else loc:=f;
    end if;
  elif Type(f) cmpeq UserProgram then
    if L`cfprecpar
      then loc:=func<p,d|Vec2InvSer([f(p^k: Precision:=precision):
					k in [0..d]],d) >;
      else loc:=func<p,d|Vec2InvSer([f(p^k):k in [0..d]],d) >;
    end if;
  else
    N:=#f;
    function loc(p,d)
      d0:=p^d gt N select Floor(Log(p,N+1/2)) else d;
      return Vec2InvSer([f[p^k]:k in [0..d0]],d);
    end function;
  end if;
  return loc;
end function;


/***** (6) COMPUTING PHI AND G:                                  *****/
/* TAYLOR EXPANSIONS, RECURSIONS AT INFINITY AND CONTINUED FRACTIONS *****/

procedure RecursionsAtInfinity(L)
  R:=L`AsympReals;
  R:=Rationals(); //!
  P:=RationalFunctionField(R); n:=P.1;
  W:=PolynomialRing(R); x:=W.1;
  PS:=PolynomialRing(P); s:=PS.1;
  d:=#L`gamma;
  sympol:=&*[x+R!g:g in L`gamma];
  symvec:=Append(Reverse(Coefficients(sympol)),0);
  modsymvec:=[R!0: k in [1..d+2]];
  for j:=0 to d do 
  for k:=0 to j do
    modsymvec[j+1]+:=(-symvec[2])^k*d^(j-1-k)*Binomial(k+d-j,k)*symvec[j-k+1];
  end for;
  end for;

  // Delta polynomials
  M:=PowerSeriesRing(R,2*d+2); t:=M.1;
  Q:=PowerSeriesRing(M,2*d+2); y:=Q.1;
  deltapol:=[Evaluate(s,x) : s in Coefficients((Sinh(y)/y)^t)];

  // recursion coefficients for phi at infinity
  recF:=[
    -1/2^p/d^(p-1)/n*
    &+[modsymvec[m+1]*
    (m gt p-1 select 1 else &*[d-j: j in [m..p-1]])*
    &+[(2*n-p+1)^(p-m-2*k)/Factorial(p-m-2*k)*Evaluate(deltapol[2*k+1],d-p)
    : k in [0..Floor((p-m)/2)]]
    : m in [0..p]]
    : p in [1..d+1]
   ];
  // recF is poly(n)/n

  // recursion coefficients for G at infinity
  L`recG:=[recF[p+1]-(symvec[2]+d*(s-1)-2*(n-p)-1)/2/d*recF[p] : p in [1..d]];
  // this part we want to store
  L`recF:=recF[[2..d]];
end procedure;


function SeriesToContFrac(L,vec)
  tolerance:=0.1^L`asympprecision;
  R:=Universe(vec);
  P:=PowerSeriesRing(R,#vec+1); x:=P.1;
  res:=[R|];
  repeat
    Append(~res,vec[1]);
    ind:=0;
    repeat
      ind+:=1;
      vec[ind]:=0;
    until (ind eq #vec) or (Abs(vec[ind+1]) gt tolerance);
    if ind ge #vec then break; end if;
    Append(~res,ind);
    vec:=Eltseq(x^ind/(P!vec+O(x^#vec)));
  until false;
  return res;
end function;


procedure RecursePhiV(L)
  S:=Parent(L`phiVser[1]);
  X:=S.1;
  R:=BaseRing(S);
  L`phiVnn+:=1;
  Append(~L`phiV, Matrix(R,#L`gammapoles,Max(L`gammapoleorders),
    [Coefficient(L`phiVser[j],-k):
		  k in [1..Max(L`gammapoleorders)], j in [1..#L`gammapoles]]
  ));
  for j in [1..#L`gammapoles], k in [1..#L`gamma] do
    L`phiVser[j]/:=(X/2-R!L`gammapoles[j]/2-L`phiVnn+R!L`gamma[k]/2);
  end for;
end procedure;


function Phi0(L,t)
  t:=L`TaylorReals!t;
  t2:=t^2;
  logt:=-L`TaylorReals!Log(t);
  res:=0;
  nn:=0;
  if L`phiVnn eq 0 then
    RecursePhiV(L);
  end if;
  P:=Parent(L`phiV[1,1,1]);
  LogTTerm:=Vector([P|logt^(k-1)/Factorial(k-1):
		       k in [1..Max(L`gammapoleorders)]]);
  TPower:=Vector([P|t^x: x in L`gammapoles]);
  tolerance:=0.1^(L`termprecision+0.6);
  //maxterm:=0;
  repeat
    totalold:=res;
    nn+:=1;
    if nn gt L`phiVnn then RecursePhiV(L); end if;
    res+:=InnerProduct(TPower*L`phiV[nn],LogTTerm);  
    TPower*:=t2;
  until nn gt 3 and Abs(res-totalold) lt tolerance;
  return L`TermReals!res;
end function;


function EvaluateContFrac(cfvec,terms,t,infty)
  if terms lt 0 or terms gt Floor(#cfvec/2) then terms:=Floor(#cfvec/2);end if;
  res:=cfvec[2*terms+1];
  while terms gt 0 do
    if res eq 0 then res:=infty;
      else res:=cfvec[2*terms-1]+t^cfvec[2*terms]/res; end if;
    terms-:=1;
  end while;
  return res;
end function;


function PhiInfinity(L,t,ncf)
 t:=L`AsympReals!t; d:=#L`gamma; td2:=t^(-2/d); //! special cases: ncf=1,2
 res:=EvaluateContFrac(L`fcf,ncf,td2,L`AsympReals!10^L`asympprecision);
 res:=res*L`asympconstf*Exp(-d/td2)*t^L`expdifff;
 return L`TermReals!res; end function;

function Phi(L,t)
  if #L`gamma eq 1 then return L`TermReals!(2*t^L`gamma[1]*Exp(-t^2)); end if;
  if (not L`asymptotics) or (t lt L`PhiCaseBound) then return Phi0(L,t);
  else u:=L`phiinfterms[Min(1+Floor(Abs(t)/L`termstep),#L`phiinfterms)];
   return PhiInfinity(L,t,u); end if; end function;

function LogInt(L,i,j,logt,D)
  if Abs(i) lt 10^(2-L`termprecision) then return Parent(logt)!0; end if;
  return &+ [Binomial(k-j,D)*Factorial(D)*(-i*logt)^k/Factorial(k)
		: k in [0..j-1]]/i^(j+D); end function;

procedure MakeLogSum(L,ss,D,v)
  if #L`logsum eq L`phiVnn then                     // more phiV's necessary
    for j:=1 to Floor(L`phiVnn/10)+1 do RecursePhiV(L); end for;
  end if;
  if L`phiVnn-#L`logsum gt 5 then
    vprint LSeries,3: "Computing Taylor coefficients about 0"
	              *" for the incomplete Gamma factor for n="*
      Sprint(#L`logsum+1)*".."*Sprint(L`phiVnn);
  end if;
  for nn:=#L`logsum+1 to L`phiVnn do              // generate logsums
    V:=L`phiV[nn];
    logsum:=[
      &+[ Parent(v)| V[j,k]*LogInt(L,L`gammapoles[j]+2*(nn-1)+ss,k,v,D)
          :k in [1..L`gammapoleorders[j]]]
    :j in [1..#L`gammapoles]];
    Append(~L`logsum,logsum);
  end for;
end procedure;


function G0(L,t,ss,D)
  ss:=L`TaylorComplexes!ss;
  t:=L`TaylorReals!t;
  P:=PolynomialRing(L`TaylorComplexes); v:=P.1;
  if [ss,D] ne L`last_g_logsum then L`logsum:=[]; end if;
  t2:=t^2;                                 // time
  LT:=L`TaylorReals!Log(t); // = money
  TPower:=Vector([t^x: x in L`gammapoles]);
  res:=0;
  nn:=0;
  term:=1;
  tolerance:=0.1^(L`termprecision+1);
  repeat
    oldterm:=term;
    nn+:=1;
    if nn gt #L`logsum then
      MakeLogSum(L,ss,D,v);
      L`last_g_logsum:=[ss,D];
    end if;
    term:=InnerProduct(Vector([Evaluate(x,LT):x in L`logsum[nn]]),TPower);
    res+:=term;
    TPower*:=t2;
  until nn gt 3 and Max(Abs(term),Abs(oldterm)) le tolerance;
  gmser:=fullgammaseries(L,ss,D);
  c_S:=Parent(gmser).1;
  gmser/:=t^(c_S+ss);
  gmcf:=Coefficient(gmser,D)*Factorial(D);
  return L`TermComplexes!(gmcf-res);
end function;


// G(t,s,D) computed using asymptotic expansion
// at infinity and associated continued fraction

function GInfinity(L,t,ss,D,ncf)
 ss:=L`AsympComplexes!ss; t:=L`AsympReals!t;
 if ncf eq -1 then ncf:=L`gncf; end if; d:=#L`gamma; tt:=t^(-2/d);
 //! special cases: ncf=1,2
 res:=L`asympconstg*Exp(-d/tt)*t^L`expdiffg*tt^D*
       EvaluateContFrac(L`gcf,ncf,tt,L`AsympReals!10^L`asympprecision);
 return L`AsympComplexes!res; end function;

// pre-compute asymptotic expansions for a given s
procedure initGInfinity(L,ss,D) // ?? comment is wrong, this is for contfrac?
  vprint LSeries,3: "Computing Taylor expansions about 0"
                    *" for the inverse Mellin transform of the Gamma factor";
  ss:=L`AsympComplexes!ss; d:=#L`gamma; gvec:=L`Gvec; lgvec:=#gvec;
  for k:=1 to D do gvec:=[Derivative(x): x in gvec];
                   Rotate(~gvec,-1); gvec[lgvec]:=1; end for;
  L`gcf:=SeriesToContFrac(L,[Evaluate(gvec[d+k-1],ss):
				       k in [1..L`maxasympcoeff+1]]);
  L`gncf:=Floor(#L`gcf/2);
  L`Ginfterms:=[-1:k in [1..Round(L`lastt/L`termstep)+1]];

  terms:=L`gncf; L`GCaseBound:=0;
  //tolerance:=0.1^(L`termprecision+2);
  tolerance:=0.09^(L`termprecision+2); //!
  for k:=1 to #L`Ginfterms do
    t1:=(k-1)*L`termstep;
    while k gt 1 and terms gt 1
      and Abs(GInfinity(L,t1,ss,D,terms-1)-GInfinity(L,t1,ss,D,terms))
           lt tolerance
        do terms-:=1;
    end while;
    if terms eq 0 or &+[Abs(L`gcf[2*j]): j in [1..terms]] lt L`maxasympcoeff
      then L`Ginfterms[k]:=terms;
      else L`GCaseBound:=k*L`termstep;
    end if;
  end for;
end procedure;

function G(L,t,ss,D) //inc gamma function - no work for complex s or small t
 if (#L`gamma eq 1) and (D eq 0) and IsReal(ss) and (t gt 0.25) then
  ss:=L`AsympReals!ss; t:=L`AsympReals!t;
  return L`TermReals!(t^(-ss)*Gamma((ss+L`gamma[1])/2,t^2:Complementary));
  end if;
 if (L`last_g_s ne [ss,D]) and L`asymptotics then
  initGInfinity(L,ss,D); L`last_g_s:=[ss,D]; end if;
 if (not L`asymptotics) or (t lt L`GCaseBound) then return G0(L,t,ss,D);
 else nn:=Min(1+Floor(Abs(t)/L`termstep),#L`Ginfterms);
      return GInfinity(L,t,ss,D,L`Ginfterms[nn]); end if; end function;

procedure InitializePhiAndG(L)
  d:=#L`gamma;
  vprint LSeries,2: "Computing Taylor expansions about 0"
                    *" for the inverse Mellin transform of the Gamma factor";
  RP:=L`TaylorReals; Over2:=func<s|Evaluate(s,Parent(s).1/2)>;
  InitV:=[ &* [
    Over2(GammaSeries(RP!((-L`gammapoles[j]+L`gamma[k])/2),
		      L`gammapoleorders[j]-1))
		  : k in [1..d]] : j in [1..#L`gammapoles]];
  L`phiV:=[]; L`phiVnn:=0; L`phiVser:=InitV;
  if not L`asymptotics then return; end if;
  RP:=L`AsympReals;
  vprint LSeries,2: "Computing asymptotic expansion coefficients"
                    *" for special functions involved";
  RecursionsAtInfinity(L);
  L`expdifff    := RP! ((1+&+L`gamma)/d-1);
  L`asympconstf := RP! (2 * &*[Gamma(RP!k/d):k in [1..d]]);
  L`expdiffg    := RP! ((1+&+L`gamma)/d-1-2/d);
  L`asympconstg := RP! (&*[Gamma(RP!k/d):k in [1..d]]);
  // Coefficients for the asymptotic expansion of Phi(t) and G(t)
  Fvec:=[RP!0: k in [1..d+L`maxasympcoeff]]; Fvec[d]:=RP!1;
  if d ne 1 then
   for y:=1 to L`maxasympcoeff do
     Fvec[d+y]:=&+[Evaluate(L`recF[j],y)*Fvec[d+y-j]: j in [1..d-1]];
   end for; end if;
  P:=PolynomialRing(RP); s:=P.1;
  L`Gvec:=[P!RP!0: k in [1..d+L`maxasympcoeff]]; L`Gvec[d]+:=1;
  for y:=1 to L`maxasympcoeff do
    L`Gvec[d+y]:=&+[P!EvaluateBelow(L`recG[j],y)*L`Gvec[d+y-j]: j in [1..d]];
  end for;

  // Convert the Fvec (Taylor asymptotic) coeffs into fcf (contfrac coeffs)
  vprint LSeries,2:"Converting asymptotic expansions into continued fractions";
  L`fcf:=SeriesToContFrac(L,Fvec[[d..d+L`maxasympcoeff]]);
  L`fncf:=Floor(#L`fcf/2); // at most L`maxasympcoeff+1, less if terminates
  L`termstep:=L`lastt lt 35 select 1 else Floor(L`lastt^(1/3));
  L`phiinfterms:=[-1:k in [1..Round(L`lastt/L`termstep)+1]];
  terms:=L`fncf; L`PhiCaseBound:=0; tolerance:=0.1^(L`termprecision+1);
  for k:=1 to #L`phiinfterms do t1:=(k-1)*L`termstep;
    while k gt 1 and terms gt 1
      and Abs(PhiInfinity(L,t1,terms-1)-PhiInfinity(L,t1,terms)) lt tolerance
        do terms-:=1; end while;
    if terms eq 0 or &+[Abs(L`fcf[2*j]): j in [1..terms]] lt L`maxasympcoeff
      then L`phiinfterms[k]:=terms;
    else L`PhiCaseBound:=k*L`termstep; end if; end for;

end procedure;


/***** (7) FUNCTIONAL EQUATION *****/

function LTheta(L,t) t:=L`TaylorReals!(t/L`expfactor); res:=0;                
 N:=Min([Floor(L`lastt/t+1),MaxCoefficients(L),LCfRequired(L)]);              
 for k:=1 to N do                                                             
  if (N gt L`vprint_series) and (k mod L`vprint_series eq 1) then             
    vprint LSeries,3: "Theta: "*Sprint(k-1)*"/"*Sprint(N)                      
			      *" ["*Sprint(Round(100*(k-1)/N))*"%]"; end if;   
  c:=Coefficient(L,k); if c ne 0 then res+:=c*Phi(L,k*t); end if; end for;    
 return res; end function; // this is the main &+[coeff*weighting] function   

procedure VPrintCheckFEQ(err,prec,str,val,forcewarning);
  if err lt 10^(1-prec) then
    vprint LSeries,1: str*"="*val*" to correct precision, magnificent";
  elif err lt 10^(1-0.8*prec) then
    vprint LSeries,1: str*" is close to "*val*", looks ok";
  elif err lt 10^(1-0.3*prec) then
    vprint LSeries,1: str*" is away from "*val*", looks very suspicious";
  elif err lt 0.001 then
    vprint LSeries,1: str*" is far from "*val
                         *", I'd bet on a wrong functional equation";
  elif err lt 0.1 then
    if forcewarning 
      then print str*" is far from "*val*", wrong functional equation?";
      else vprint LSeries,1: str*" is far from "*val
	     *", wrong functional equation?"; end if;
  else 
    if forcewarning 
      then print str*" is nowhere near "*val*", wrong functional equation?";
      else vprint LSeries,1: str*" is nowhere near "*val
	     *", wrong functional equation?"; end if; end if; end procedure;

// * Checks that coefficients have already been generated
// * Initializes recursions and Taylor coefficients for Phi and G
//   if this has not been done yet
// * If either L`sign or L`lresidues are still undefined, solve
//   them now from the functional equation.
//   Note that for #L`lresidues>1, loss of precision is likely

procedure CheckEverythingAssigned(~L);
  if L`prod cmpne false then
    for i:=1 to #L`prod do CheckEverythingAssigned(~(L`prod[i][1])); end for;
    L`sign:=IsEmpty(L`prod) select 1 else &*[(F[1]`sign)^F[2]: F in L`prod];
  end if;

  if (#L`lpoles ne #L`lresidues) and (L`sign eq 0) then
    error "Cannot automatically determine both the sign in the"*
          " functional equation and residues of L*(s)"; end if;
  if not assigned L`phiV then InitializePhiAndG(L); end if;
  GenerateCoefficients(L,L`cfrequired);
  // Nothing else to do
  if (#L`lpoles eq #L`lresidues) and (L`sign ne 0) then return; end if;

  if L`sign eq 0 then // determine sign
    vprint LSeries,1:"Solving sign from the functional equation, need "*
      Sprint(Floor(L`lastt*L`expfactor/1.1+1))*" coefficients";
    t:=L`LfunReals!(11/10);
    lhs:=LTheta(L,t); rhs:=t^(-L`weight)*ComplexConjugate(LTheta(L,1/t));
    if #L`lpoles gt 0 then
      lhs+:= &+[L`lresidues[k]*((11/10)^-L`lpoles[k]) :k in [1..#L`lpoles] ];
      rhs+:= &+[L`lresidues[k]*(11/10)^(-L`weight+L`lpoles[k]) :
		   k in [1..#L`lpoles] ]; end if;
    L`sign:=lhs/rhs; err:=Abs(Abs(L`sign)-1);
    L`sign:=ComplexField(L`precision)!L`sign;
    vprint LSeries,1:"  Found sign="*Sprint(L`sign);
    VPrintCheckFEQ(err,L`precision,"  |Sign|","1",true);
  else // determine residues, solving them from the functional equation
    N:=#L`lpoles; R:=L`TermComplexes;
    if #L`lresidues eq N then return; end if;
    lpx:=[R!23/20+(k eq 1 select 0 else k-1)/10:k in [1..N]];
    vprint LSeries,1:"Solving residues from the functional equation, need "*
      Sprint(Floor(L`lastt*L`expfactor/lpx[#lpx]+1))*" coefficients";
    if N gt 1 then
     vprint LSeries,1:"  #residues>1, do not expect decent precision"; end if;
    lpv:=Vector(R,[L`sign*x^L`weight*ComplexConjugate(LTheta(L,x))-
		      LTheta(L,1/x): x in lpx]);
    lpm:=Matrix(R,N,N,
      [ R!(x^s-L`sign*x^(L`weight-s) where s is L`lpoles[j] where x is lpx[k]):
      j,k in[1..N]]);
    L`lresidues:=[L`LfunComplexes!v[k]: k in [1..N]]
      where v is Solution(lpm,lpv);
    vprint LSeries,1:"  Found residues="*Sprint(L`lresidues);
  end if;
end procedure;


// Check that the functional equation on the level of inverse Mellin
// transforms is satisfied; so
//   LTheta(L,t) = sign * t^(-weight) * ComplexConjugate(LTheta(L,1/t))
// holds for a given 1<t<=1.2. Note that for t=1 the equation is _always_
// satisfied, so t has to be somewhat away from 1.

function cfsz(L,n) omega:=2;
 return Degree(L)^omega*n^(MotivicWeight(L)/2); end function;
 // omega is dodgy, max #primefac, though (very) unlikely get Deg from each

function LThetaLIM(L,t) t:=L`TaylorReals!(t/L`expfactor); res:=0;
 r:=LCfRequired(L); s:=Max(10,Ceiling(r/100)); lim:=0; err:=10^(-L`precision);
 while true do _:=LGetCoefficients(L,lim+s);
  for k in [lim+1..lim+s] do c:=Coefficient(L,k);
  if c ne 0 then phi:=Phi(L,k*t); res+:=c*phi;
   /* k,c*phi,res; */ end if; end for;
  lim:=lim+s; vprint LSeries,3: "ThetaLIM: "*Sprint(lim)*"/"*Sprint(r);
  // Abs(res),cfsz(L,lim)*Phi(L,lim*t);
  if cfsz(L,lim)*Phi(L,lim*t)/Abs(res) lt err then break; end if;
  end while; vprint LSeries,2: "ThetaLIM Finished: "*Sprint(lim)*"/"*Sprint(r);
 return res; end function;

intrinsic LPhi(L::LSer, t::FldReElt) -> FldReElt {Testing function}
 if not assigned L`phiV then InitializePhiAndG(L); end if;
 return Phi(L,L`LfunReals!t); end intrinsic;

intrinsic GTest(L::LSer, t::FldReElt,s::FldComElt,dv::RngIntElt) -> FldComElt
{Testing function}
 if not assigned L`phiV then InitializePhiAndG(L); end if;
 return G(L,L`LfunReals!t,s,dv); end intrinsic;

intrinsic CFENew(L::LSer : t:=11/10) -> FldReElt
{New version of CheckFunctionalEquation}
 if L`prod cmpne false then
  err:=Max([CFENew(F[1]: t:=t): F in L`prod] cat [0]);
  L`sign:=IsEmpty(L`prod) select 1 else &*[(F[1]`sign)^F[2]: F in L`prod];
  return err; end if; RF5:=RealField(5);
 if not assigned L`phiV then InitializePhiAndG(L); end if; t:=L`LfunReals!t;
 lhs:=LThetaLIM(L,t); rhs:=ComplexConjugate(LThetaLIM(L,1/t)*t^(-L`weight));
// lhs,rhs;
 p:=10^(L`precision-Min([L`taylorprecision,L`termprecision,L`asympprecision]));
 if Max(Abs(lhs),Abs(rhs)) lt p and Abs(lhs/rhs) lt 1.1 and Abs(lhs/rhs) gt 0.9
  then t:=t*11/10; vprintf LSeries: "Try new t=%o %o %o\n",RF5!t,lhs,rhs;
       if t gt 5.0 then error "Non-convergent in CFENew?"; end if;
       return CFENew(L : t:=t); end if;
 if #L`lpoles gt 0 then
  rhs+:= &+[L`lresidues[k]*(t^(-L`weight+L`lpoles[k])) : k in [1..#L`lpoles] ];
  lhs+:= &+[L`lresidues[k]*(t^-L`lpoles[k]) :k in [1..#L`lpoles] ]; end if;
 CF:=ComplexField(L`precision); L`sign:=CF!(lhs/rhs);
 return Abs(Abs(L`sign)-1); end intrinsic;

// with HGM([2,2,3,6],[4,8],1)
// the precision at oo is 10, which is not enough in Phi(L,k*t) I guess

intrinsic CheckFunctionalEquation(L::LSer : t:=6/5) -> FldReElt
{Verify numerically that L(s) satisfies the assumed functional equation.
 Ideally, this should return 0, i.e. about 10^(-28) if you did not change
 the precision with LSetPrecision. If this is far from 0, the functional
 equation is probably wrong.

 If the residues of L^*(s) or have not been set, this function
 will compute them first. If the sign has not been determined yet, the
 function computes it and returns Abs(sign-1). Again, this should be 0.}

 if L`prod cmpne false then
  err:=Max([CheckFunctionalEquation(F[1]: t:=t): F in L`prod] cat [0]);
  L`sign:=IsEmpty(L`prod) select 1 else &*[(F[1]`sign)^F[2]: F in L`prod];
  return err; end if;
 require IsReal(t) and (t gt 1):
  "in CheckFunctionalEquation(L[,t]) t must be a real number >1.0";
 computesign:=L`sign eq 0;
 CheckEverythingAssigned(~L);
 if computesign then
  return RealField(L`precision)!(Abs(L`sign)-1); end if;
 vprint LSeries,1:"Verifying the functional equation at t="*Sprint(t)*
  ", need "*Sprint(Floor(L`lastt*L`expfactor/t+1))*" coefficients";
 t:=L`LfunReals!t;
 res:=LTheta(L,t)-L`sign*t^(-L`weight)*ComplexConjugate(LTheta(L,1/t));
 if #L`lpoles gt 0 then
  res+:=&+[L`lresidues[k]*(t^-L`lpoles[k]-L`sign*t^(-L`weight+L`lpoles[k]))
	      : k in [1..#L`lpoles] ]; end if;
  VPrintCheckFEQ(Abs(res),L`precision,"  LHS-RHS","0",false);
  return RealField(L`precision)!Abs(res); end intrinsic;

intrinsic LSetPrecision(L::LSer, precision::RngIntElt: ImS:=0,
  Asymptotics:=true, CoefficientGrowth :=DefaultCfGrowth)
{
  Change precision that is used to computing values L(s) to a given number
of decimal digits and set two other precision-related settings:
  "ImS" specifies the largest Im(s) for which you are planning to compute L(s).
Default is 0 and if you will try to ask for L(s) with Im(s) large, precision
loss will occur and a warning will be printed.
  "asymptotics" specifies whether to use only Taylor expansions of special
functions at 0 or to allow using continued fractions of the asymptotic
expansions at infinity. The former (false) is very slow but known to converge,
the latter (true, default) is faster but as yet unproved to work in general.
  "cfgrowth" is a name of a function C(x) or C(L,x) that bounds the Dirichlet
coefficients, |a_n|<C(n). Must be increasing and defined for all
real x. (Default one would normally work fine.)
}
  if precision eq 0 then precision:=GetPrecision(1.2); end if;
  if nargs(CoefficientGrowth) eq 1
    then cfgrowth:=func<L,t|CoefficientGrowth(t)>;
    else cfgrowth:=CoefficientGrowth;
  end if;

  if (assigned L`precision) and (L`precision eq precision)
    and (assigned L`ImS) and (assigned L`cfgrowth) and
    (assigned L`asymptotics) and (L`ImS eq ImS) and
    (L`asymptotics eq Asymptotics) and (cfgrowth cmpeq L`cfgrowth) then
      return;  //! nothing to do
  end if;

  require ((Type(CoefficientGrowth) cmpeq UserProgram) and
   (nargs(CoefficientGrowth) in [1..2])):
    "CoefficientGrowth must be a function f(t) or f(L,t)";
  require IsReal(ImS) and (ImS ge 0): "ImS must be real positive";
  require Type(Asymptotics) cmpeq BoolElt: "Asymptotics must be boolean";

  L`cfgrowth:=cfgrowth;

  if assigned L`cffun and Type(L`cffun) eq UserProgram
   and L`cfprecpar and (precision gt L`precision)
   and assigned L`cfvec and #L`cfvec gt 0
   and not &and[Type(x) in {RngIntElt,FldRatElt} : x in L`cfvec] then
    vprint LSeries,1: "Precision upped, have to recalculate old coefficients";
    delete L`cfvec; end if;
 // MW typically always has cfprecpar set, just for convenience

  L`precision:=precision; L`ImS:=ImS; L`asymptotics:=Asymptotics;

  undefined:=1E100; L`last_fgs_s:=undefined;
  L`last_fgs_terms:=0; L`last_fgs_val:=0;
  L`last_g_logsum:=[]; L`last_g_s:=[undefined,undefined]; L`logsum:=[];
  delete L`phiV;  // force reinitialization of phi and G. Probably
                  // do not always have to do it, but I am not bothered.
  L`cfrequired:=LCfRequired(L);
  FUDGE:=5+Degree(L)+MotivicWeight(L); // MW guess
  // point is that eg Gamma(s/2)^6 has a Mellin trans
  // with (log x)^5 at x=0, so small n act like (log N)^5
  // FUDGE=17 was insufficient for [2^16][1^16] t=1 HGM (deg 14 wt 15)
  // should be related to Phi(L,1/L`expfactor) size
  L`lfunprecision   :=
    L`precision+0.6+ExtraPrecision
    (L`gamma,L`expfactor,L`weight,L`effwt,L`ImS)+FUDGE;
  L`termprecision   := L`lfunprecision + MotivicWeight(L)+Degree(L);
  // MW: not sure what termprec is, but it needs to be increased...
  L`asympprecision := L`termprecision-FUDGE+5; // +5 MW, else CFENew loops (+2)
  L`taylorprecision := (Asymptotics select 2 else 3)*(L`termprecision-0.6);
  // with 3* must be a careful calculation, ... Maybe I'll do this one day
  L`taylorprecision-:=(Asymptotics select 2 else 3)*FUDGE;

  F:=func<f,p| f(Ceiling(p*Log(2,10)):Bits:=true) >;
  L`LfunReals       := F(RealField,L`lfunprecision);
  L`LfunComplexes   := F(ComplexField,L`lfunprecision);
  L`TermReals       := F(RealField,L`termprecision);
  L`TermComplexes   := F(ComplexField,L`termprecision);
  L`TaylorReals     := F(RealField,L`taylorprecision);
  L`TaylorComplexes := F(ComplexField,L`taylorprecision);
  L`AsympReals      := F(RealField,L`asympprecision);
  L`AsympComplexes  := F(ComplexField,L`asympprecision);
  vprint LSeries,2 :
    "  digits: "*Sprint(L`precision)*" (answer), "
      *Sprint(Ceiling(L`taylorprecision))*" (at 0), "
      *Sprint(Ceiling(L`asympprecision))*" (at infinity), need "
      *Sprint(LCfRequired(L))*" coefficients";

  L`lresidues:=[];
  if assigned L`lresiduesfun then
    if Type(L`lresiduesfun) cmpeq UserProgram
      then L`lresidues:=L`lresiduesfun(L,Ceiling(L`lfunprecision));
      else L`lresidues:=L`lresiduesfun; end if; end if;

  L`sign:=0;
  if assigned L`signfun then
    if Type(L`signfun) cmpeq UserProgram
      then L`sign:=L`signfun(L,Ceiling(L`lfunprecision));
      else L`sign:=L`signfun; end if; end if;

  RP:=L`TaylorReals;
  L`expfactor:=Sqrt(RP!L`conductor/Pi(RP)^#L`gamma);
  L`lastt:=L`cfrequired/L`expfactor;

// if not assigned L`phiV then InitializePhiAndG(L); end if;
// Phi(L,1/L`expfactor);

  if L`prod cmpne false then
   for d in L`prod do LSetPrecision(d[1],precision); end for; end if;

end intrinsic;


/***** (8) COMPUTING L(S) AND ITS TAYLOR EXPANSION *****/

procedure ErrorIfPole(L,ss)
  if #L`lpoles eq 0 then return; end if;
  dist1,ind1:=VMin([x-ss: x in L`lpoles]);
  dist2,ind2:=VMin([L`weight-x-ss: x in L`lpoles]);
  pole:=dist1 lt dist2 select L`lpoles[ind1] else L`weight-L`lpoles[ind2];
  dist:=Min(dist1,dist2);
  if dist lt 0.1^L`precision then error "L*(s) has a pole at s =",pole; end if;
  if dist lt 0.1^(L`precision/2) then
    print "Warning: L*(s) has a pole very close to s =",ss,"
           expect high precision loss"; end if; end procedure;

// LStar(s) = L(s) * Gamma factor

intrinsic LStar(L::LSer, s0::. : Cutoff:=1, Derivative:=0) -> .
{Value (D:=0) or D-th derivative of the modified L-function
 L^*(s)=L(s)*gamma factor at s=s0.}
  require IsCoercible(ComplexField(L`precision),s0):
    "in LStar(L,s0) s0 must be a number, coercible into ComplexField()";
  D:=Derivative;
  require (Type(D) cmpeq RngIntElt) and (D ge 0):
    "in LStar(L,s0[,D]) D must be a non-negative integer";
  require IsReal(Cutoff) and (Cutoff ge 1):
    "in LStar(L,s0,[Cutoff]) Cutoff must be a real number and at least 1.0";
  CheckEverythingAssigned(~L);
  require (D eq 0) or (Cutoff eq 1):
    "Cannot compute Derivatives of L(s) with Cutoff>1";
  s0:=L`TaylorComplexes!s0;

  // L-function is a product
  if (L`prod cmpne false) and not (s0 in &cat([F[1]`lpoles: F in L`prod])) then
    if IsEmpty(L`prod) then
      return ComplexField(L`precision)!(D eq 0 select 1 else 0);
    end if;
    if D eq 0 then
     return &*[LStar(F[1],s0: Cutoff:=Cutoff,Derivative:=0)^F[2]: F in L`prod];
    end if;
    res:=1;
    for F in L`prod do
      FGSeries:=fullgammaseries(F[1],s0,D);
      x:=LaurentSeriesRing(ComplexField(L`precision)).1;
      FGSeries*:=F[1]`expfactor^(s0+x);
      res:=res*(LTaylor(F[1],s0,D)*FGSeries)^F[2]+O(x^(D+1));
    end for;
    return Coefficient(res,D);
  end if;

  ErrorIfPole(L,s0);
  Cutoff:=L`TaylorReals!Cutoff;
  ncf1:=Min(Round(L`cfrequired*Cutoff),MaxCoefficients(L));
  ncf2:=Min(Round(L`cfrequired/Cutoff),MaxCoefficients(L));
  res:=L`TermComplexes!0; res1:=res; res2:=res;
  if #L`lpoles gt 0 then
   for k:=1 to #L`lpoles do
     res-:=(-1)^D*Factorial(D)*L`lresidues[k]/(s0-L`lpoles[k])^(D+1)* 
 	Cutoff^(-L`lpoles[k]);
     res-:=L`sign*L`lresidues[k]*Factorial(D)/(L`weight-L`lpoles[k]-s0)^(D+1)*
       Cutoff^(-L`weight+L`lpoles[k]);
   end for;
  end if;

  // don't repeatedly access attributes (this saves a noticeable percentage)
  // SRD, July 2011
  Le := L`expfactor; LeC := L`expfactor*Cutoff; Lws0 := L`weight-s0;

  for kk:=0 to ncf1 by L`vprint_series do
    if (kk ge L`vprint_series) then
      vprint LSeries,3: "LStar-A: "*Sprint(kk)*"/"*Sprint(ncf1)*" ["*
				 Sprint(Round(100*kk/ncf1))*"%]";
    end if;
    for k:=kk+1 to Min(ncf1,kk+L`vprint_series) do
      c:=Coefficient(L,k);  // These do &+[coeff*weights] also
      if c ne 0 then
        res1+:=ComplexConjugate(c)*(-1)^D*G(L,k/LeC,Lws0,D);
      end if;
    end for;
  end for;

  for kk:=0 to ncf2 by L`vprint_series do
    if (kk ge L`vprint_series) then
      vprint LSeries,3: "LStar-B: "*Sprint(kk)*"/"*Sprint(ncf2)*" ["*
				 Sprint(Round(100*kk/ncf2))*"%]";
    end if;
    for k:=kk+1 to Min(ncf2,kk+L`vprint_series) do
      c:=Coefficient(L,k);  // These do &+[coeff*weights] also
      if c ne 0 then
        res2+:=c*G(L,k*Cutoff/Le,s0,D);
      end if;
    end for;
  end for;

  res:= (res + L`sign*res1/Cutoff^L`weight + res2)*Cutoff^s0;
  return ComplexField(L`precision)!res;
end intrinsic;


// LTaylor(s,,n) = L(s)+L'(s)c_S+L''(s)*c_S^2/2!+..., first n+1 terms

intrinsic LTaylor(L::LSer, s0::., n::RngIntElt : Cutoff:=1, ZeroBelow:=0) -> .
{First n+1 terms of the Taylor expansion of L(s) about s=s0}

  // L-function is a product
  if (L`prod cmpne false) then
    if IsEmpty(L`prod) then
      return LaurentSeriesRing(ComplexField(L`precision))!1;
    end if;
    return &*[LTaylor(F[1],s0,n: Cutoff:=Cutoff, ZeroBelow:=0)^F[2] :
						 F in L`prod];  //! :=0
  end if;

  require IsCoercible(ComplexField(L`precision),s0):
    "in LTaylor(L,s0,n) s0 must be a number, coercible into ComplexField()";
  require n ge 0: "in LTaylor(L,s0[,n]) n must be a non-negative integer";
  require (Type(ZeroBelow) cmpeq RngIntElt)
     and (ZeroBelow ge 0) and (ZeroBelow le n):
    "ZeroBelow must be an integer in the range [0..n]";
  require IsReal(Cutoff) and (Cutoff ge 1):
    "Cutoff must be a real number and at least 1.0";
  require Real(s0) lt 3*10^5:
    "Re(s0) is too large (>3*10^5) to compute Gamma(s0)";

  CheckEverythingAssigned(~L);

  C:=L`LfunComplexes;
  s0:=C!s0;
  FGSeries:=fullgammaseries(L,s0,n);
  x:=LaurentSeriesRing(C,n+1).1;

  FGSeries*:=L`expfactor^(s0+x);
  PrecisionLoss:=(-Log(10,VMax(Eltseq(FGSeries))))-
                 (L`lfunprecision-L`precision);
  if PrecisionLoss gt 1.5 then
    print "Warning: in L-series calculation, loss of",
    Ceiling(PrecisionLoss),"digits due to cancellation";
  end if;
  //! Actually need only even/odd for sign +1/-1 and real coeffs s=weight/2
  //  but is this worth checking? Probably not
  LSSeries := &+[C!LStar(L,s0: Cutoff:=Cutoff,Derivative:=k)*x^k/Factorial(k)
    : k in [ZeroBelow..n]];
  res:=LSSeries/FGSeries+O(x^(n+1));
  return ChangePrecSeries(Parent(x)!res,ComplexField(L`precision));
end intrinsic;


intrinsic Evaluate(L::LSer, s0::. : Cutoff:=1,Derivative:=0,Leading:=false)-> .
{Value (Derivative:=0) or D-th derivative of the L-function L(s) at s=s0.
 Set leading if you know that all lower order derivatives L^(k)(s0) vanish}
 z:=Coefficient(LTaylor(L,s0,Derivative:Cutoff:=Cutoff,
			ZeroBelow:=(Leading and (Derivative gt 0)
				    select Derivative-1 else 0)),Derivative)
     *Factorial(Derivative);
 if Abs(Imaginary(z)) lt 10^(1.5-L`precision) then z:=Real(z); end if;
 return z; end intrinsic;


/***** (9) GENERAL LSER SIGNATURE *****/


intrinsic LSeries(
  weight::.,       // positive integer/real
  gamma::[],       // list of integers/rationals
  conductor::.,    // positive integer/real
  cffun::.         // 0 (later) or list/function describing the coefficients
  :
  Sign     :=0,    // meaning automatically determined
  Poles    :=[],   // meaning no poles
  Residues :=[],   // meaning automatically determined
  Parent   :=false,
  Name     :="unknown origin",
  CoefficientGrowth :=DefaultCfGrowth,
  Precision:=0,    // meaning current Precision(RealField())
  ImS      :=0,    // meaning will only call L(s) for s real (or Im(s) small)
  Asymptotics:=true
  ) -> LSer
{Construct an L-Series L with given invariants.  The arguments are as follows:
 weight     = enters the functional equation L(s)<->L(weight-s),
 gamma      = list of Hodge numbers [l_1,..,l_d] that specify the gamma
              factor = A^s * product over k of Gamma((s+l_k)/2),
 conductor  = with, in the above line, A = Sqrt(conductor/pi^d),
 cffun      = specifies Dirichlet coefficients, either of the following four options:
              - pre-computed vector, e.g. [1,1,1,1,1,1]
              - a_n as a function of n, e.g. func<n|1>
              - function that computes the inverse local factor at p as a
                polynomial or a series up to O(x^(d+1)), e.g. func<p,d|1-x>
              - 0, coefficients will be set later with LSetCoefficients
              in cases 2 and 3, your function may have optional parameter "precision", 
              (if your coefficients are real/complex numbers rather than 
      integers/rationals), e.g. func<n:precision| Pi(RealField(precision))>.
 Sign       = complex number of absolute value 1 in the func. equation
              or a function s(p) (or s(L,p)) which computes it to p digits
              or 0, meaning solve numerically,
 Poles      = poles of L^*(s), only half of them needs to be specified
              (they are symmetric about s=weight/2), of type SeqEnum,
 Residues   = list of residues at the poles of L*(s),
              or a function r(p) (or r(L,p)) which computes them to p digits
              or 0, meaning solve numerically,
 Parent     = any Magma object, used to compare two L-series.
              e.g. for LSeries(ell. curve), parent = ell.curve.
 Name       = used for printing (if not specified, print Parent).
 CoefficientGrowth  = name of a function C(x) or C(L,x) that bounds the
      Dirichlet coefficients, |a_n|<C(n). Must be increasing
                      and defined for all real x.
 Precision  = number of digits to compute the values L(s) to. Can be also
              changed later with LSetPrecision.
 ImS (default 0) and asymptotics (default true): see LSetPrecision
}
  Z:=Integers();
  Q:=Rationals();
  precision:=Precision; //! clean up
  require Type(precision) cmpeq RngIntElt and (precision ge 0):
    "precision must be either 0 (default real field) or a positive integer";
  precision:=(precision gt 0 select precision else GetPrecision(0.5));
  R:=RealField(precision);
  require IsReal(weight): "weight must be real positive";
/* // MW: not sure why weight has to be positive ?
  require IsReal(weight) and (weight gt 0):
    "weight must be real positive";
*/
  require IsReal(conductor) and (conductor gt 0):
    "conductor must be real positive";
  require (#gamma gt 0) or (conductor eq 1):
    "L-function must have gamma factors";
  require (Universe(gamma) cmpeq Q) or (Universe(gamma) cmpeq Z):
    "elements of gamma must be integer or rational numbers";
  require (Type(Sign) eq UserProgram and nargs(Sign) in [1..2]) or
    IsCoercible(ComplexField(precision),Sign):
    "sign must be a number or a function s(precision) or s(L,precision)";
  require Type(Poles) cmpeq SeqEnum:
    "poles must be a sequence of complex numbers";
  require Type(Residues) cmpeq SeqEnum or
         (Type(Residues) cmpeq UserProgram and nargs(Residues) in [1,2]):
    "residues must be a sequence of complex numbers or a function "*
    "r(precision) or r(L,precision) that computes them";
  if Type(Residues) cmpeq SeqEnum then
    require (#Poles eq #Residues) or (#Residues eq 0):
      "Number of residues does not match the number of poles";
  end if;

  L:=New(LSer); // this and only this function does it

  // Store main parameters of the L-series

  L`weight:=weight; L`effwt:=weight;
  L`gamma:=gamma;
  L`conductor:=conductor;
  L`precision:=precision;
  L`cfmax:=cfmaxdefault;
  L`aacoeff:=AssociativeArray();
  L`known_ef:=AssociativeArray();
  L`EF_SAVE_LIM:=10^6;

  L`lpoles:=Poles;
  L`cutoff:=6/5;
  L`parent:=Parent;
  L`name:=((Name cmpeq "unknown origin") and (Parent cmpne false))
    select Parent else Name;
  L`prod:=false;

  if cffun cmpeq 0
    then // keep L`cffun unassigned for now
    else LSetCoefficients(L,cffun);
  end if;

  L`maxasympcoeff:=40;
  L`vprint_coeffs:=1000;
  L`vprint_series:=5000;

  if Type(Residues) cmpeq UserProgram then
    if nargs(Residues) eq 1 
      then L`lresiduesfun:=func<L,prec|Residues(prec)>;
      else L`lresiduesfun:=Residues;
    end if; 
  else
    if #Residues gt 0 then L`lresiduesfun:=Residues; end if;
    // otherwise keep it unassigned, LSetPrecision will force to calculate them
  end if;

  if Type(Sign) cmpeq UserProgram then
    if nargs(Sign) eq 1 
      then L`signfun:=func<L,prec|Sign(prec)>;
      else L`signfun:=Sign;
    end if; 
  else
    if Sign cmpne 0 then L`signfun:=Sign; end if;
    // otherwise keep it unassigned, LSetPrecision will force to calculate it
  end if;

  vprint LSeries, 2: "Defining L-series of",L`name;
  vprint LSeries, 2: "  weight="*Sprint(weight)*", gamma="*Sprint(gamma)*
    ", conductor="*Sprint(conductor)*
    (IsCoercible(Z,conductor) select 
      "="*Sprint(Factorization(Z!conductor))*")" else "");

  // Initialize

  L`expfactor:=Sqrt(L`conductor/Pi(RealField(L`precision))^#L`gamma);
    // needed in ExtraPrecision(...) below but will be recalculated
    // with proper precision later

  // poles (with their orders) of the gamma factor

  d:=#L`gamma;
  pordtmp:=[1:k in [1..d]];
  for j,k in [1..d] do
  if j ne k then
    gdiff:=L`gamma[j]-L`gamma[k];
    if not IsCloseInt(gdiff,1) then continue; end if;
    gdiff:=Round(gdiff);
    if gdiff mod 2 eq 0 and gdiff le 0 then
      pordtmp[j]+:=pordtmp[k];
      pordtmp[k]:=0;
    end if;
  end if;
  end for;

  L`gammapoles:=[];
  L`gammapoleorders:=[];
  for j in [1..d] do
  if pordtmp[j] ne 0 then
    Append(~L`gammapoles,L`gamma[j]);
    Append(~L`gammapoleorders,pordtmp[j]);
  end if;
  end for;
  LSetPrecision(L,precision: ImS:=ImS, Asymptotics:=Asymptotics,
     CoefficientGrowth:=CoefficientGrowth);

  vprint LSeries,2 : 
    "  sign="*(L`sign eq 0 select "uncomputed" else Sprint(L`sign))*", "*
    "poles="*Sprint(Poles)*", "*
    "residues="*(#L`lresidues lt #Poles select "uncomputed" else Sprint(L`lresidues))*
    "";

 if HasHodgeStructure(L) then // bleh, Tim's weight
   L`effwt:=1+Weight(EffectiveHodgeStructure(HodgeStructure(L))); end if;

  return L;

end intrinsic;
