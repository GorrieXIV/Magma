freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: lser.m
   DESC: Basic ModAbVarLSer functionality.

   Creation: 06/16/03 -- initial creation

   2004-10-24 (WAS):
               Fixed very stupid bug.  All L-function analytic special
               values were off by a factor of 10% because the line
                  val := 1.0;
               was
                  val := 1.1; 
 
      
 ***************************************************************************/

/*
HANDBOOK_TITLE: $L$-series 

*/

import "modabvar.m":
   Verbose;

import "misc.m":
   GatherFactorExponents;

import "rings.m":
   IsNumberField,
   QQ;

forward
   CharpolyOfFrobenius_OverQ,
   Compute_FrobeniusPolynomial,
   Create_VarAbModLSer,
   FixForBiggerField, 
   Name,
   SetName;


declare type ModAbVarLSer;   // really VarAbModLSeries

declare attributes ModAbVarLSer:  
   abelian_variety,
   critical_strip,
   name;

function Create_VarAbModLSer(A)
   assert Type(A) eq ModAbVar;
   assert Type(BaseRing(A)) in {FldCyc, FldRat};

   L := New(ModAbVarLSer);
   L`abelian_variety := A;
   if Name(A) ne "" then
      L`name := Sprintf("L(%o,s)",Name(A));
   else
      L`name := "";
   end if;
   return L;
end function;


/***************************************************************************

  << Creation >>

The {\tt LSeries} command creates the $L$-series $L(A,s)$
associated to a modular abelian variety $A$ over $\Q$
or a cyclotomic field.  No actual computation is performed. 

EXAMPLES

\begincode
> A := JZero(23);
> L := LSeries(A);
> L;
L(JZero(23),s): L-series of Modular abelian variety JZero(23) of 
dimension 2 and level 23 over Q
> LSeries(ModularAbelianVariety("65B"));
L(65B,s): L-series of Modular abelian variety 65B of dimension 2 
and level 5*13 over Q
\endcode
You can create $L$-series of abelian varieties over cyclotomic fields,
but currently no interesting functionality is implemented for
them.  [TODO: something for abelian extensions using twists and
characters.]
\begincode
> LSeries(BaseExtend(JZero(11),CyclotomicField(5)));
L(JZero(11),s): L-series of Modular abelian variety JZero(11) of 
dimension 1 and level 11 over Q(zeta_5)
\endcode

 ***************************************************************************/

intrinsic LSeries(A::ModAbVar) -> ModAbVarLSer
{The L-series associated to A.}
   require Type(BaseRing(A)) in {FldCyc, FldRat} :
                   "Argument 1 must be defined over Q or Q(zeta_n).";
   return Create_VarAbModLSer(A);
end intrinsic;


/***************************************************************************

  << Invariants >>

EXAMPLES
We define several $L$-functions of modular abelian varieties and modular
motives, and compute their critical strip (which is from $0$ to $k$,
where $k$ is the weight).
\begincode
> L := LSeries(JZero(37));
> CriticalStrip(L);
0 2
> L := LSeries(JZero(37,6));
> CriticalStrip(L);
0 6
> J := JOne(11,3);  J;
Modular motive JOne(11,3) of dimension 5 and level 11 over Q
> CriticalStrip(LSeries(J));
0 3
> A_delta := JZero(1,12);
> L := LSeries(A_delta);
> CriticalStrip(L);
0 12
> ModularAbelianVariety(L);
Modular motive JZero(1,12) of dimension 1 and level 1 over Q
\endcode

 ***************************************************************************/

function Name(L)
   // A short string that describes L.
   return L`name;
end function;

procedure SetName(L, name)
   // Set the name of L.
   L`name := name;
end procedure;

intrinsic ModularAbelianVariety(L::ModAbVarLSer) -> ModAbVar
{Given an L-function L of a modular abelian variety return 
the abelian variety to which L was attached.}
   return L`abelian_variety;
end intrinsic;

intrinsic CriticalStrip(L::ModAbVarLSer) -> RngIntElt, RngIntElt
{Given an L-function L of a modular abelian variety return 
integers x and y such that the critical strip for L is the
set of complex numbers with real part strictly between x and y.}
   if not assigned L`critical_strip then
      w := Weights(ModularAbelianVariety(L));
      L`critical_strip := [Integers() | 0, Max(w)];
   end if;
   return Explode(L`critical_strip);
end intrinsic;


intrinsic Print(L::ModAbVarLSer, level::MonStgElt)
{}
   printf "%o%oL-series of %o", 
          Name(L), Name(L) eq "" select "" else ": ", ModularAbelianVariety(L);
end intrinsic;


/***************************************************************************

  << Characteristic Polynomials of Frobenius Elements>>

 ***************************************************************************/

intrinsic FrobeniusPolynomial(A::ModAbVar, 
     p::RngIntElt : Factored := false) -> RngUPolElt
{Given an abelian variety A over a number field, return 
the characteristic polynomial of Frob_p acting on any ell-adic Tate
module of A, where p and ell do not divide the level of A.}
   Verbose("FrobeniusPolynomial", 
     Sprintf("Computing characteristic polynomial of Frob(%o) on A=%o.",p, A), "");
   require p ge 0 and IsPrime(p) and Level(A) mod p ne 0 : 
            "Argument 2 must be a prime coprime to the level of argument 1.";

   require IsNumberField(BaseRing(A)) : "Argument 1 must be defined over a number field.";

   if Type(BaseRing(A)) in {FldRat, RngInt} then
      return Compute_FrobeniusPolynomial(A,GF(p), Factored);
   end if;

   K := BaseRing(A);
   D := Discriminant(K);
   if (Degree(K)*D) mod p ne 0 then
      F := Factorization(PolynomialRing(GF(p))!DefiningPolynomial(K));
   else
      // TODO: Using maximal order here is insanely slow -- figure
      // out how to use pMaximalOrder...
      O := MaximalOrder(BaseRing(A));
      F := Factorization(p*O);
   end if;
   degrees := Sort([Degree(f[1]) : f in F]);
   t, B := CanChangeRing(A,QQ);
   return [Compute_FrobeniusPolynomial(B,GF(p^d),Factored) 
                    : d in degrees];  // TODO: this could be optimized more...

end intrinsic;

intrinsic FrobeniusPolynomial(A::ModAbVar, P::RngOrdIdl) -> RngUPolElt
{The characteristic polynomial of Frobenius at the nonzero prime ideal P
on the modular abelian variety A, where P is assumed to be a prime of 
good reduction for A, and A is defined over a field that contains the prime P.}
   Verbose("FrobeniusPolynomial", 
     Sprintf("Computing characteristic polynomial of Frob(%o) on A=%o.",P, A), "");
   return Compute_FrobeniusPolynomial(A,GF(Characteristic(P)^Degree(P)));
end intrinsic;

function FixForBiggerField(f, k)
   R := PolynomialRing(QQ);
   x := R.1;
   f := R!f;
   Q := quo<R|ideal<R|[f]>>;  
   a := Q!x;
   g := a^Degree(k);
   return CharacteristicPolynomial(g);
end function;

function FrobeniusPolynomial_OverQ(A, p, factored)
   assert Type(A) eq ModAbVar;
   assert Type(p) eq RngIntElt;
   assert Type(factored) eq BoolElt;
   assert IsPrime(p);

   if not factored then
      return &*[PolynomialRing(Integers())|
           CharpolyOfFrobenius(ModularSymbols(Af[1])[1],p)^#Af[2] : 
                    Af in Factorization(A)];
   end if;
   X := [];
   for Af in Factorization(A) do
      F := Factorization(FrobeniusPolynomial(ModularSymbols(Af[1])[1],p));
      Append(~X,[<fac[1],fac[2]*#Af[2]> : fac in F]);
   end for;
   return GatherFactorExponents(&cat X);
end function;

intrinsic FrobeniusPolynomial(A::ModAbVar : 
       Factored := false) -> RngUPolElt
{The characteristic polynomial of Frobenius on A.}
   k := BaseRing(A);
   require Type(k) eq FldFin : "Argument 1 must be defined over a finite field.";
   require IsAbelianVariety(A) : "Argument 1 must have good reduction.";
   p := Characteristic(k);
   t, B := CanChangeRing(A,QQ);
   // TODO
   require t : "It (currently) must be possible to change the base ring of " *
               "argument 1 to the rational field.";
   return Compute_FrobeniusPolynomial(B, k, Factored);
end intrinsic;
   
function Compute_FrobeniusPolynomial(A, k, factored)
/* The characteristic polynomial of Frobenius on the reduction of 
   A to the finite field k.  Here A is assumed defined over Q. */

   if not assigned A`frobpolys then
      A`frobpolys := [];
   end if;
   assert Type(k) eq FldFin;
   assert Type(BaseRing(A)) eq FldRat;

   if exists(t) { t[2] : t in A`frobpolys | t[1] eq #k } then
      return t;
   end if;

   p := Characteristic(k);
   f := FrobeniusPolynomial_OverQ(A, p, factored);
   if Degree(k) eq 1 then
      Append(~A`frobpolys, <#k, f>);
      return f;
   end if;
   if not factored then
      f := FixForBiggerField(f, k);
      Append(~A`frobpolys, <#k, f>);
      return f;
   end if;
   G := [];
   for g in f do 
      h := Factorization(FixForBiggerField(g[1], k));
      for j in h do 
         Append(~G, <j[1], j[2]*g[2]>);
      end for;
   end for;
   f := GatherFactorExponents(G);
   Append(~A`frobpolys, <#k, f>);
   return f;

end function;
   
  

/***************************************************************************

  << Values at Integers in the Critical Strip  >>

 ***************************************************************************/

intrinsic LRatio(A::ModAbVar, s::RngIntElt) -> FldRatElt
{The ratio L(A,j)*(j-1)!/((2pi)^\{j-1\}*Omega_j), where j is a "critical
 integer", so 1<=j<=k-1, and Omega_j is the volume of the group of real
 points on A when j is odd, and the volume of the -1 eigenspace for 
 conjugation when j is even.}
   require Type(BaseRing(A)) eq FldRat : 
       "Argument 1 must be the L-series of an abelian variety over Q.";
   require IsAttachedToNewform(A) : 
       "Argument 1 must be attached to a newform.";
   L := LSeries(A);
   min, max := CriticalStrip(L);
   require s gt min and s lt max : "Argument 2 must lie between", min, " and", max,".";
   return LRatio(L,s);
end intrinsic;

intrinsic LRatio(L::ModAbVarLSer, s::RngIntElt) -> FldRatElt
{"} // "
   Verbose("LRatio", Sprintf("Computing L(A,%o)/Omega.", s),"");
   A := ModularAbelianVariety(L);
   require Type(BaseRing(A)) eq FldRat : 
       "Argument 1 must be the L-series of an abelian variety over Q.";
   min, max := CriticalStrip(L);
   require s gt min and s lt max : "Argument 2 must lie between", min, " and", max,".";
   t, Af := IsAttachedToNewform(A);
   require t : "Argument 1 must be attached to a newform.";
   A := Af;
   M := ModularSymbols(A)[1];
   if Type(BaseField(M)) ne FldRat then
      M := RestrictionOfScalarsToQ(M);
   end if;
   return LRatio(M,s);
end intrinsic;

intrinsic IsZeroAt(L::ModAbVarLSer, s::RngIntElt) -> BoolElt
{Determines (rigorously) whether the L-function L is zero at s} 
   Verbose("IsZeroAt", Sprintf("Determining if %o is zero at %o.", L, s), "");
   A := ModularAbelianVariety(L);
   require Type(BaseRing(A)) eq FldRat : 
       "Argument 1 must be the L-series of an abelian variety over Q.";
   min, max := CriticalStrip(L);
   require s gt min and s lt max : "Argument 2 must lie between", min, " and", max,".";

   // TODO: This could be optimized by just checking whether {0,oo} projects to 0!
   return 0 eq &*[LRatio(B[1], s) : B in Factorization(A)];

end intrinsic;

intrinsic Evaluate(L::ModAbVarLSer, s::RngIntElt) -> FldReElt
{The value of L at s, where s must be an integer 
 that lies in the critical strip for L.} 
   require Type(BaseRing(ModularAbelianVariety(L))) eq FldRat : 
       "Argument 1 must be the L-series of an abelian variety over Q.";
   min, max := CriticalStrip(L);
   require s gt min and s lt max : "Argument 2 must be an integer between", min, " and", max,".";
   return Evaluate(L,s,100);
end intrinsic;

intrinsic Evaluate(L::ModAbVarLSer, s::RngIntElt, prec::RngIntElt) -> FldReElt
{The value of L at s, where s must be an integer 
 that lies in the critical strip for L, computed using prec
 terms of power series.} 
   Verbose("Evaluate", 
        Sprintf("Evaluating L=%o at %o using %o terms of q-expansions", L, s, prec), "");
   A := ModularAbelianVariety(L);
   require Type(BaseRing(A)) eq FldRat : 
       "Argument 1 must be the L-series of an abelian variety over Q.";
   min, max := CriticalStrip(L);
   require s gt min and s lt max : "Argument 2 must lie between", min, " and", max,".";
   ans := 1.0;
   F := Factorization(ModularAbelianVariety(L));
   for i in [1..#F] do 
       M := ModularSymbols(F[i][1])[1];
       if Type(BaseField(M)) ne FldRat then
          N := RestrictionOfScalarsToQ(M);
          D := NewformDecomposition(N);
          assert #D eq 1;
          N  := D[1];
       else
          N := M;
       end if;
       ans := ans * LSeries(N,s,prec)^(#F[i][2]);
   end for;
   return ans;
end intrinsic;

intrinsic '@'(s::RngIntElt, L::ModAbVarLSer) -> RngElt
{The value of L at s, where s is an integer that lies in the critical strip.}
   require Type(BaseRing(ModularAbelianVariety(L))) eq FldRat : 
       "Argument 1 must be the L-series of an abelian variety over Q.";
   min, max := CriticalStrip(L);
   require s gt min and s lt max : "Argument 2 must lie between", min, " and", max,".";
   return Evaluate(L,s); 
end intrinsic;

/***************************************************************************

  << Leading Coefficient >>

 ***************************************************************************/

intrinsic LeadingCoefficient(L::ModAbVarLSer, s::RngIntElt, prec::RngIntElt) -> 
    FldReElt, RngIntElt
{The leading coefficient of the Taylor expansion about the critical
integer s and the order of vanishing of L at s.  }
   Verbose("LeadingCoefficient", 
       Sprintf("Computing leading coefficing and order of vanishing of L=%o at %o using %o terms of q-expansions", L, s, prec), "");
   A := ModularAbelianVariety(L);
   min, max := CriticalStrip(L);
   require max eq 2 : "Argument 1 must be of weight 2.";   // remove later
   require s gt min and s lt max : "Argument 2 must lie between", min, " and", max,".";

   val := 1.0;
   ord := 0;          
   for F in Factorization(A) do A_f, n := Explode(F);
      require Weights(A_f) eq {2} :  
               "Argument 1 must be of weight 2.";
      require IsTrivial(DirichletCharacter(A_f)) : 
            "Argument 1 must be a attached to a trivial-character abelian variety.";
      M := ModularSymbols(A_f)[1];
      val_f, ord_f := LSeriesLeadingCoefficient(M, s, prec);
      ord_f := ord_f*Dimension(A_f);
      val := val*val_f;
      ord := ord + ord_f;
   end for;
        
   return val, ord;

end intrinsic;

