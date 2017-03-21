freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: elliptic.m  (Analytic invariants of elliptic curves)               
                                                                            
   $Header: /home/was/magma/packages/modsym/code/RCS/elliptic.m,v 1.6 2001/12/09 04:19:48 was Exp $

   $Log: elliptic.m,v $
   Revision 1.6  2001/12/09 04:19:48  was
   Made the is_cuspidal check in EllipticCurve weaker.

   Revision 1.5  2001/10/30 21:10:34  was
   *** empty log message ***

   Revision 1.4  2001/07/27 20:25:43  was
   BaseExtend --> ChangeRing

   Revision 1.3  2001/05/30 19:16:08  was
   Searched for a bug that turned out to be in another file...

   Revision 1.2  2001/05/13 03:49:21  was
   Changed ModularForms flag to ModularSymbols.

   Revision 1.1  2001/04/20 04:46:57  was
   Initial revision

   Revision 1.9  2000/09/09 20:59:16  was
   Removed import of round from arith.m, since now Round is part of Magma.

   Revision 1.8  2000/08/01 04:23:17  was
   Don't know... left out.

   Revision 1.7  2000/06/03 04:52:29  was
   verbose: ModularForm --> ModularForms

   Revision 1.6  2000/06/03 04:50:46  was
   *** empty log message ***

   Revision 1.5  2000/06/03 04:18:47  was
   *** empty log message ***

   Revision 1.4  2000/06/03 03:20:14  was
   TraceOfFrobenius

   Revision 1.3  2000/05/26 00:23:27  was
   fixed Elliptic_ap bug; assumed that argument 1 is minimal.

   Revision 1.2  2000/05/09 17:17:07  was
   got rid of "Minimal Model".

   Revision 1.1  2000/05/02 08:01:30  was
   Initial revision

 ***************************************************************************/


import "analytic.m"  : DefaultPrecision;

import "arith.m"     : DotProd,
                       SmallestPrimeNondivisor;

import "linalg.m"    : Saturate;

import "modsym.m"    : ModularSymbolsDual;


function ellinv_NormalizePair(w1, w2)
   tau := w1/w2;
   if Imaginary(tau) lt 0 then
      w1  := -w1; 
      tau := -tau ; 
   end if;
   w1  := w1 - w2*Round(Real(tau));
   tau := w1/w2;
   for i in [1..300] do       // Just to stop infinite loop due to rounding
      if Abs(tau) ge 1 then
         break;
      end if;
      w3:=-w1; w1:=w2; w2:=w3; tau:=w1/w2;
      w1:=w1-w2*Round(Real(tau));
      tau:=w1/w2;
   end for;
   return tau, w1, w2;     
end function;

function ellinv_c4c6(w1, w2)
   tau  := w1/w2;
   zero := 0; one := 1; two := 2;
   pi   := Pi(RealField());
   x    := two*pi*Real(tau);
   y    := two*pi*Imaginary(tau);
   q    := Exp(-y) * (Cos(x) + ComplexField().1*Sin(x));
   f    := two*pi/w2;
   f2   := f*f;  
   f4   := f2*f2;
    
   term := one; 
   qpower := one;
   sum4 := zero;
   sum6 := zero;
   tiny := 10.0^(-10);
   
   for n in [1..2000] do
      if Abs(term) lt tiny then
         break ;
      end if;
      n2 := n^2;
      qpower *:= q;
      term := n*n2*qpower/(one-qpower);
      sum4 +:= term;
      term *:= n2;
      sum6 +:= term;
   end for;
   if Abs(term) gt 10^(-4) then
       "term = ",term;
	"ellinv_getc4c6: WARNING: precision very bad!";
   end if;
   c4 := (one +  240*sum4)*f4;
   c6 := (one -  504*sum6)*f4*f2;
   return c4, c6;
end function;

intrinsic EllipticPeriods(A::ModSym)
                    -> FldComElt, FldComElt
{The standard elliptic periods w1 and w2, computed to precision n.}
  return EllipticPeriods(A, DefaultPrecision(A));
end intrinsic;


intrinsic EllipticPeriods(A::ModSym, n::RngIntElt) -> FldComElt, FldComElt
{"} // "
   L           := Periods(A,n);
   tau, w1, w2 := ellinv_NormalizePair(L[1][1], L[2][1]);
   return w1, w2;
end intrinsic;


intrinsic EllipticInvariants(A::ModSym)
                    -> FldComElt, FldComElt, FldComElt, CrvEll
{The invariants c4, c6, and j, and an elliptic curve E over C with
those invariants, computed using precision n terms of q-expansion.}
  return EllipticInvariants(A, DefaultPrecision(A));
end intrinsic;


intrinsic EllipticInvariants(A::ModSym, n::RngIntElt) 
      -> FldComElt, FldComElt, FldComElt, CrvEll
{"} // "
   require DimensionComplexTorus(A) eq 1 : "Torus of argument 1 must have dimension 1.";
   require IsCuspidal(A) : "Argument 1 must be cuspidal.";
   if IsVerbose("ModularSymbols") then
      print "Computing elliptic invariants.";
   end if;
   w1, w2      := EllipticPeriods(A,n);
   c4, c6      := ellinv_c4c6(w1,w2);
   j           := 1728*c4*c4*c4/(c4*c4*c4 - c6*c6);
   E := EllipticCurve([-c4/48,-c6/864]);
   return c4, c6, j, E;
end intrinsic;


// E is assumed to be minimal; otherwise, BaseExtend will fail at primes
// dividing the discriminant of E.
function Elliptic_ap(E, p)
   //return Trace(ChangeRing(E,GF(p)));
   assert IsPrime(p);
   return FrobeniusTraceDirect(E,p);
end function;


intrinsic EllipticCurve(M::ModSym : 
                         StartPrec := -1,
                         Database := true ) -> SeqEnum
{An elliptic curve over the rational numbers that lies in the isogeny 
 class of elliptic curves associated to M.}

   require Weight(M) eq 2 : "Argument 1 must be of weight 2.";
   require IsTrivial(DirichletCharacter(M)) : "Argument 1 must be on Gamma_0(N), i.e., have trivial character.";

   // checking cuspidal if it hasn't been checked takes too long using the current algorithm.
   if assigned M`is_cuspidal then
      require IsCuspidal(M) : "Argument 1 must be cuspidal.";
      require DimensionComplexTorus(M) eq 1 : "Argument 1 must correspond to an elliptic curve.";
   end if;

   N := Level(M);

   if Database then    // attempt to get the curve from the CremonaDatabase.
      if IsVerbose("ModularSymbols") then
         printf "Looking up curve in Cremona's elliptic curve database.\n";
      end if;
      D := EllipticCurveDatabase();
      low, high := ConductorRange(D);
      levels := assigned M`is_new and M`is_new select [N] else  [N : N in Divisors(Level(M)) | N ge low and N le high];
      Elist := [EllipticCurve(D,N,i,1) : 
                i in [1..NumberOfIsogenyClasses(D,N)], N in levels
                  | N ge low and N le high];
      p := 1;
      while #Elist gt 1 and p le HeckeBound(M) do
         p := SmallestPrimeNondivisor(N,NextPrime(p));

         i := 1;
         while i le #Elist do
            if Elliptic_ap(Elist[i],p) ne DualHeckeOperator(M,p)[1,1] then
               Remove(~Elist,i);
            else
               i +:= 1; 
            end if;         
         end while;
      end while;
      assert #Elist le 1;
      if #Elist eq 1 then
         return Elist[1];
      else
         error "No elliptic curve found in the database.";         
      end if;
   end if;

   require not IsPlusQuotient(M) : "Argument 1 must not be a +1 quotient.";
   require not IsMinusQuotient(M) : "Argument 1 must not be a -1 quotient.";

   sturm := HeckeBound(M);
   if StartPrec eq -1 then
      n := 40 + Level(M) div 4;
   else
      n := Max(2,StartPrec);
   end if;
   f := qEigenform(M,n);
   n := Degree(f);  // it might be known to much higher precision...
   c4, c6, j := EllipticInvariants(M,n);
   if IsVerbose("ModularSymbols") then
      "c4 =",c4;
      "c6 =",c6;
   end if;
   c4 := Integers()!Round(Real(c4));
   c6 := Integers()!Round(Real(c6));

   // Find an elliptic curve, whose c4 and c6 are close and
   // whose ap for p good and less than n equal those of M.  

   maxtries := 200;
   tries := 1;
   rad   := 1;
   cur   := 0;
   dir   := 0;   // 0=right, 1=down, 2=left, 3=up.
   seen  := {@ [c4,c6] @};   // index set of positions seen so far. 
   if IsVerbose("ModularSymbols") then
      "Searching...";
   end if;
   while true do   
      if GetVerbose("ModularSymbols") ge 2 then
         printf "[%o,%o] ",c4,c6;
         if tries mod 6 eq 0 then
            "";
         end if;
      end if;
      Include(~seen, [c4,c6]);
      if IsEllipticCurve([-27*c4,-54*c6]) then
         E := EllipticCurve([-27*c4,-54*c6]);
         if Conductor(E) eq Level(M) then
            found := true;
            if IsVerbose("ModularSymbols") then
               printf "Candidate curve [%o,%o]:\n",c4,c6;
            end if;
            EE := MinimalModel(E);
            for p in [1..sturm] do
               if IsPrime(p) and (Level(M) mod p ne 0) then
                  ap  := Elliptic_ap(EE,p);
                  if ap ne Coefficient(f,p) then
                     if IsVerbose("ModularSymbols") then
                        "Rejecting--the ",p,"th L-series coefficients disagree";
                     end if;
                     found := false;
                     break;
                  end if;
               end if;
            end for;
            if found eq true then
               if IsVerbose("ModularSymbols") then
                  "This curve must be in the isogeny class.";
               end if;
               return E;
            end if;
         end if;
      end if;
      if tries gt maxtries then
         if IsVerbose("ModularSymbols") then
            "\nRecomputing period integrals to higher precision"; 
         end if;
         n     := Integers()!Round(Degree(f) + 50);
         c4, c6, j := EllipticInvariants(M,n);
         if IsVerbose("ModularSymbols") then
            "c4 =",c4;
            "c6 =",c6;
         end if;
         c4    := Integers()!Round(Real(c4));
         c6    := Integers()!Round(Real(c6));
         f     := qEigenform(M,n);
         tries := 1;
         rad   := 1;
         cur   := 0;
         dir   := 0;
      end if;
      if Index(seen,[c4,c6]) ne 0 then
         // move to next pair [c4,c6].            
         tries +:= 1; 
         repeat
            if cur ge rad then  // turn
               dir := (dir + 1) mod 4;
               cur := 0;
               if dir eq 3 then
                  cur  := 1;
                  c4  -:= 1;
                  rad +:= 2;
                  continue;
               end if;
            end if;
            case dir:   // 0=right, 1=down, 2=left, 3=up.
               when 0: c4 +:= 1;
               when 1: c6 +:= 1;
               when 2: c4 -:= 1;
               when 3: c6 -:= 1;
            end case;
            cur +:= 1;
         until Index(seen,[c4,c6]) eq 0;
      end if;
   end while;
end intrinsic;

intrinsic ModularSymbolsModSmallPrime(E::CrvEll, ell::RngIntElt) -> ModSym
{The space of mod ell modular symbols associated to E, 
 where ell should be a very small prime.}

   require IsPrime(ell) : "Argument 2 must be prime.";

   repeat 
      p := NextPrime(1000+Random(2000));
      print "Trying p = ", p;
      t := Cputime();
      Mminus := ModularSymbols(E,GF(p),-1 : stop := 29);
      printf "Computed Mminus (%o seconds)\n",Cputime(t); t:=Cputime();
      if Dimension(Mminus) eq 1 then
         Mplus := ModularSymbols(E,GF(p),+1 : stop := 29);
         printf "Computed Mplus (%o seconds)\n",Cputime(t); t:=Cputime();
      end if;
   until Dimension(Mminus) eq 1 and Dimension(Mplus) eq 1;     

   N := Conductor(E);
   M := ModularSymbols(N,2,GF(ell));
   printf "Computed M (%o seconds)\n",Cputime(t); t:=Cputime();
   Am := AmbientSpace(Mminus);
   Ap := AmbientSpace(Mplus);
   Bm := [Am!<1,ModularSymbol(M.i)[1][2]> : i in [1..Dimension(M)]];
   Bp := [Ap!<1,ModularSymbol(M.i)[1][2]> : i in [1..Dimension(M)]];
   printf "Computed coercions (%o seconds)\n",Cputime(t); t:=Cputime();
   vm := Eltseq(Basis(DualVectorSpace(Mminus))[1]);
   vp := Eltseq(Basis(DualVectorSpace(Mplus))[1]);
   V := VectorSpace(GF(p),Dimension(M));
   Im := V![DotProd(vm,Eltseq(Bm[i])) : i in [1..#Bm]];
   Ip := V![DotProd(vp,Eltseq(Bp[i])) : i in [1..#Bp]];
   printf "Computed dotprods (%o seconds)\n",Cputime(t); t:=Cputime();

   okm, ratm := RationalReconstruction(Im);
   okp, ratp := RationalReconstruction(Ip);

   if not (okm and okp) then
      error "Failed to rationally reconstruct, with p=",p;
   end if;

   ratm *:= LCM([Denominator(x) : x in Eltseq(ratm)]);
   ratm *:= 1/GCD([Numerator(x) : x in Eltseq(ratm)]);
   ratp *:= LCM([Denominator(x) : x in Eltseq(ratp)]);
   ratp *:= 1/GCD([Numerator(x) : x in Eltseq(ratp)]);

   W := DualVectorSpace(M);
   B := Basis(Saturate([ratm,ratp]));
   b1 := W![GF(ell)!(Integers()!x) : x in Eltseq(B[1])];
   b2 := W![GF(ell)!(Integers()!x) : x in Eltseq(B[2])];

   Answer := ModularSymbolsDual(M, sub<W|[b1,b2]>);
   printf "Created modsym space (%o seconds)\n",Cputime(t); t:=Cputime();

   return Answer;

end intrinsic;
