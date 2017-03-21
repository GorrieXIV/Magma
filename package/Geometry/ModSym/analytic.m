freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                             
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: analytic.m  (Computations involving approx. period lattice)        
  
   $Header: /home/was/magma/packages/ModSym/code/RCS/analytic.m,v 1.7 2002/10/01 06:01:53 was Exp $

   $Log: analytic.m,v $
   Revision 1.7  2002/10/01 06:01:53  was
   ..

   Revision 1.6  2002/09/12 03:40:46  was
   ..

   Revision 1.6  2002/08/26 06:19:25  was
   Support for MultiChar spaces.

   Revision 1.5  2002/06/06 16:57:56  was
   Modified function SlowPeriodIntegral(A, f, Pg) so it works with nontrivial character.

   Revision 1.4  2001/05/25 04:22:42  was
   fixed fixed comments.

   Revision 1.3  2001/05/25 03:52:22  was
   Added that
      require Sign(A) eq 0 : "Argument 1 must have sign 0.";
      require IsCuspidal(A) : "Argument 1 must be cuspidal.";
   to the intrinsics.  This should have been there all along.

   Revision 1.2  2001/05/13 03:43:40  was
   verbose flag change.

   Revision 1.1  2001/04/20 04:42:18  was
   Initial revision

   Revision 1.19  2001/04/14 03:25:19  was
   Changed MinusVolume so that it returns a positive real number.  After all,
   it is supposed to be a the measure of something.

   Revision 1.18  2001/04/13 13:58:27  was
   Fixed the sign error!!

   Revision 1.17  2001/04/12 22:00:54  was
   NO -- there is still something wrong with the sign!!!

   Revision 1.16  2001/04/12 21:00:09  was
   Fix a sign error in LSeries -- it returned -L(E,i).

   Revision 1.15  2001/02/19 21:27:26  was
   nothing

   Revision 1.14  2001/01/24 18:13:30  was
   *** empty log message ***

   Revision 1.13  2000/07/29 04:35:54  was
   Removed spurious M := AmbientSpace(A); at end of program.

   Revision 1.12  2000/06/19 09:54:01  was
   freeze

   Revision 1.11  2000/06/19 09:53:23  was
   added freeze

   Revision 1.10  2000/06/19 08:24:56  was
   nothing.

   Revision 1.9  2000/06/03 04:58:06  was
   verbose

   Revision 1.8  2000/06/03 03:41:41  was
   Round eliminated

   Revision 1.7  2000/05/09 17:30:33  was
   removed IsNew condition.

   Revision 1.6  2000/05/09 17:16:28  was
   ...

   Revision 1.5  2000/05/03 14:52:12  was
   Robust error checking, sign-wise

   Revision 1.4  2000/05/02 07:54:29  was
   added $Log: analytic.m,v $
   added Revision 1.7  2002/10/01 06:01:53  was
   added ..
   added
   added Revision 1.6  2002/09/12 03:40:46  was
   added ..
   added
   added Revision 1.6  2002/08/26 06:19:25  was
   added Support for MultiChar spaces.
   added
   added Revision 1.5  2002/06/06 16:57:56  was
   added Modified function SlowPeriodIntegral(A, f, Pg) so it works with nontrivial character.
   added
   added Revision 1.4  2001/05/25 04:22:42  was
   added fixed fixed comments.
   added
   added Revision 1.3  2001/05/25 03:52:22  was
   added Added that
   added    require Sign(A) eq 0 : "Argument 1 must have sign 0.";
   added    require IsCuspidal(A) : "Argument 1 must be cuspidal.";
   added to the intrinsics.  This should have been there all along.
   added
   added Revision 1.2  2001/05/13 03:43:40  was
   added verbose flag change.
   added
   added Revision 1.1  2001/04/20 04:42:18  was
   added Initial revision
   added
   added Revision 1.19  2001/04/14 03:25:19  was
   added Changed MinusVolume so that it returns a positive real number.  After all,
   added it is supposed to be a the measure of something.
   added
   added Revision 1.18  2001/04/13 13:58:27  was
   added Fixed the sign error!!
   added
   added Revision 1.17  2001/04/12 22:00:54  was
   added NO -- there is still something wrong with the sign!!!
   added
   added Revision 1.16  2001/04/12 21:00:09  was
   added Fix a sign error in LSeries -- it returned -L(E,i).
   added
   added Revision 1.15  2001/02/19 21:27:26  was
   added nothing
   added
   added Revision 1.14  2001/01/24 18:13:30  was
   added *** empty log message ***
   added
   added Revision 1.13  2000/07/29 04:35:54  was
   added Removed spurious M := AmbientSpace(A); at end of program.
   added
   added Revision 1.12  2000/06/19 09:54:01  was
   added freeze
   added
   added Revision 1.11  2000/06/19 09:53:23  was
   added added freeze
   added
   added Revision 1.10  2000/06/19 08:24:56  was
   added nothing.
   added
   added Revision 1.9  2000/06/03 04:58:06  was
   added verbose
   added
   added Revision 1.8  2000/06/03 03:41:41  was
   added Round eliminated
   added
   added Revision 1.7  2000/05/09 17:30:33  was
   added removed IsNew condition.
   added
   added Revision 1.6  2000/05/09 17:16:28  was
   added ...
   added
   added Revision 1.5  2000/05/03 14:52:12  was
   added Robust error checking, sign-wise
   added header

                                                                            
 ***************************************************************************/


import "core.m"   : ConvFromModularSymbol;

import "linalg.m" : IntegerKernelOn,
                    MakeLattice,
                    VectorSpaceZBasis;

import "multichar.m" : AssociatedNewformSpace,
                       HasAssociatedNewformSpace,
                       MC_ConvToModularSymbol;

import "operators.m" : AtkinLehnerSign;

import "period.m" : RationalPeriodMapping,
                    RationalPeriodLattice,
                    RationalPeriodConjugation,
                    ScaledRationalPeriodMap,
                    SignedRationalPeriodMapping;

import "qexpansion.m":EigenformInTermsOfIntegralBasis;

import "subspace.m":MinusSubspaceDual,
                    PlusSubspaceDual;





// Constants
EULER := EulerGamma(RealField());      
PI    := Pi(RealField());

function DefaultPrecision(A)
   prec := 40+Integers()!(Level(A) div 20);
   if assigned A`qintbasis then
      prec := Max(prec,A`qintbasis[1]);
   end if;
   if IsVerbose("ModularSymbols") then
      printf "(Using at least %o terms of q-expansions.)\n",prec;
   end if;
   return prec;
end function;



/////////////////////////////////////////////////////////////
// Compute Int_{alp}^{oo} z^m*q^n dz, using                //
// an explicit formula derived via integration by parts.   //
// (C = complex numbers)                                   //
/////////////////////////////////////////////////////////////
function Int1(alp, m, n, C) 
   c := 2*Pi(C)*C.1*n;
   return 
      Exp(c*alp) 
      * &+[(-1)^s *(alp^(m-s)) / c^(s+1) * (&*[Integers()|i : i in [m-s+1..m]])
          : s in [0..m]];
end function;


/////////////////////////////////////////////////////////////
// Compute Int_{alp}^{oo} P(z)*f(q) dz, using              //
// an explicit formula derived via integration by parts.   //
/////////////////////////////////////////////////////////////
function Int2(f, alp, m)
   C := ComplexField();
   return &+[Int1(alp,m,n,C)*(C!Coefficient(f,n)) : n in [1..Degree(f)]];
end function;


function PeriodIntegral(f, P, alpha)
   // {Computes <f, P\{alpha,oo\}> = -2*pi*I*Int_{alp}^{oo} P(z) f(q) dz
   // for alpha any point 
   // in the upper half plane.}
   C := ComplexField(); i := C.1;
   return -2*Pi(C)*i* &+[Int2(f,alpha,m)* (C!Coefficient(P,m))      
               : m in [0..Degree(P)] | Coefficient(P,m) ne 0];
end function;

////////////////////////////////////////////////////////////////
// In the following, "fast" refers to using the Fricke        //
// involution trick to speed convergence.  This only works    //
// in some cases, so we have also implemented a standard      //
// slow method which should work in all cases.                //
////////////////////////////////////////////////////////////////

function FastPeriodIntegral(A, f, Pg)
// Compute <f, Pg[1]*\{oo, Pg[2](oo)\}>.
   //assert IsNew(A);

   P, g := Explode(Pg);
   if g[3] eq 0 then // g(oo)=oo.
      return 0;
   end if;
   if g[4] lt 0 then 
      g[1] *:= -1; g[2] *:= -1; g[3] *:= -1; g[4] *:= -1;
   end if;

   R    := Parent(P);
   phi  := hom <R -> R  |  g[1]*R.1+g[2]*R.2, g[3]*R.1+g[4]*R.2>; 
   giP  := phi(P) / (g[1]*g[4]-g[2]*g[3]);
   assert giP eq P;


   C := ComplexField(); i := C.1;

   N    := Level(A);
   k    := Weight(A);
   e    := AtkinLehnerSign(A);
   rootN:= Sqrt(Level(A));
   PI   := Pi(ComplexField());
   a    := g[1]; 
   b    := g[2]; 
   c    := g[3] div N; 
   d    := g[4];
   if k eq 2 then     // the formula takes a simpler form when k=2.
      cn := [
         (e-1)*Exp(-2*PI*n/rootN)
              + Exp(-2*PI*n/(d*rootN))*(Exp(2*PI*i*n*b/d)-e*Exp(2*PI*i*n*c/d))
                  : n in [1..Degree(f)]
            ];
      return &+[(Coefficient(f,n)/n) * cn[n] : n in [1..Degree(f)]];

   else
      /* The following formula is in my (William Stein) 
         Ph.D. thesis.  It generalizes Cremona's Prop 2.10.3
         to the case of higher weight modular symbols. */
      W  := hom <R -> R  |  R.2, -N*R.1>; 
      WP := W(P)/N^(Integers()!(k/2-1));
      
      S := PolynomialRing(Rationals()); z := S.1;      
      ev   := hom <R -> S | z, 1>;
      P    := ev(P);
      WP   := ev(WP);
      ans  :=  PeriodIntegral(f,  P-e*WP, i/rootN) 
              +PeriodIntegral(f,    e*WP, c/d+i/(d*rootN))
              +PeriodIntegral(f, -P     , b/d+i/(d*rootN));
      return ans;
   end if;
end function;



function SlowPeriodIntegral(A, f, Pg)
/* A::ModSym,  f::RngSerPowElt, Pg::Tup) -> FldComElt
 Given a homogeneous polynomial P(X,Y) of degree k-2, 
 a 2x2 matrix g=[a,b,c,d], and a q-expansion f of a weight k
 modular form, this function returns the period
 <f, P {oo,g(oo)}> = -2*pi*I*Int_{oo,g(oo)} P(z,1) f(z) dz.
   Resort to VERY SLOWLY CONVERGING METHOD.
   We have, for any alp in the upper half plane,
      <f, P{oo,g(oo)}>
       = <f, P{oo,alp} + P{alp, g(alp)} +         P{g(alp),g(oo)}>
       = <f, P{oo,alp} + P{alp, g(alp)} + (eps(g)g^(-1)P){alp,oo}>
       = <f, ((eps(g)g^(-1)P)-P){alp, oo} + P{alp, oo} - P{g(alp),oo}>
       = <f, (eps(g)g^(-1)P){alp, oo} - P{g(alp),oo}>.
      The integrals converge best when Im(alp) and Im(g(alp)) 
      are both large.  We choose alp=i/c.
      ************/  

   P, g := Explode(Pg);
   if g[3] eq 0 then // g(oo)=oo.
      return 0;
   end if;

   R    := Parent(P);
   phi  := hom <R -> R  |  g[1]*R.1+g[2]*R.2, g[3]*R.1+g[4]*R.2>; 
   giP  := phi(P) / (g[1]*g[4]-g[2]*g[3]);

   C := ComplexField(); i := C.1;

   if g[3] lt 0 then   // g(oo) = (-g)(oo), since g acts through PSL.
      g[1] *:= -1; g[2] *:= -1; g[3] *:= -1; g[4] *:= -1;
   end if;

   alp  := (-g[4]+i)/g[3];
   galp := (g[1]*alp + g[2])/(g[3]*alp+g[4]);
   S := PolynomialRing(Rationals()); z := S.1;      
   ev   := hom <R -> S | z, 1>;
   P    := ev(P);
   giP  := ev(giP);
   eps_g:= C!Evaluate(DirichletCharacter(A),g[1]);
   return eps_g*PeriodIntegral(f,giP,alp) - PeriodIntegral(f,P,galp);
end function;


function NextElement(N,k, P,g, fast)
   R<X,Y> := Parent(P);
   if fast then  // IT IS ABSOLUTELY ESSENTIAL THAT g[4] be VERY SMALL!!

/*
      if g[2] lt 2*N then
         g[2] +:= 1;
      else
         g[2] := 1;
         repeat
            g[4] +:= 1;
         until Gcd(g[4],N) eq 1;
      end if;
      while Gcd(g[4],g[2]) ne 1 do
         g[2] +:= 1;
      end while;
      d, g[1], g[3] := Xgcd(g[4],-g[2]*N);
      g[3] *:= N;
*/

      if Random(1,2) eq 1 then
         repeat
            g[2] +:= 1;
         until Gcd(g[2],N) eq 1;
      else
         repeat
            g[4] +:= 1;
         until Gcd(g[4],N) eq 1;
      end if;
      while Gcd(g[4],g[2]) ne 1 do
         g[2] +:= 1;
      end while;
      d, g[1], g[3] := Xgcd(g[4],-g[2]*N);
      g[3] *:= N;

      P :=  k gt 2 select 
               ( (1-g[1]*g[4])*X^2 - g[2]*(g[4]-g[1])*X*Y + g[2]^2*Y^2)^((k-2) div 2)  
            else 
               R!1;
   else
      if P ne Y^(k-2) then
         P := R!(P/X) * Y;
      else  
         P := X^(k-2);
          // only change g after trying all P's. 
         if g[1] lt g[3] then
            g[1] +:= 1;
         else
            g[3] +:= N;
         end if;
         while Gcd(g[1],g[3]) ne 1 do
            g[1] +:= Sign(g[1]);
         end while;
         d, g[4], g[2] := Xgcd(g[1],-g[3]);
      end if;
   end if;
   return P, g;
end function;


function PeriodGenerators(A, fast) 
///////////////////////////////////////////////////////////////////////////
//  The period map Phi:Mk(N,eps;Q) --- > C^d factors through             //
//  a finite dimensional Q-vector space quotient                         //
//   Mk/Ker(Phi).  This function returns a sequence of elements          //
//   of Mk(N,eps,Q) which (1) their images in Mk/Ker(Phi) form           //
//   a basis for Mk/Ker(P), and (2) each symbols is of the               //
//   form P{oo,g(oo)} for some polynomial P and matrix g in Gamma_0(N)   //
//   with the lower left entry of g positive.                            //
//   The second condition is necessary so that we can compute            //
//   the map Phi on these elements.                                      //
//   Note also: if g(P)=P then the precision of the period               //
//   computation can be greatly enhanced.                                //
///////////////////////////////////////////////////////////////////////////

   //assert IsCuspidal(A) and IsNew(A);

   if not assigned A`PeriodGens then
      vprintf ModularSymbols : "Computing period generators (fast=%o).\n", fast;

      M  := AmbientSpace(A);
    sign := Sign(M);
      N  := Level(A);
      k  := Weight(A);
      pi := RationalPeriodMapping(A);    // M_k --> Mk/Ker(Phi)
      V  := Image(pi);
      S  := sub<V | V!0>;
      G  := [];
      X  := [];
      RR<a,b>  := PolynomialRing(BaseField(A),2);
      P  := a^(k-2);      
      g  := [1,N,0,1];
      star := StarInvolution(M);
      cnt := 0;
      while Dimension(S) lt Dimension(V) do
         repeat
            P,g := NextElement(N,k,P,g,fast); 
         until g[3] ne 0;
         x := Representation(M!<P, [[1,0],[g[1],g[3]]]>);
         // image of x+*(x) and x-*(x)
         vprintf ModularSymbols, 2 : 
             "\tConsidering %oth modular symbol (dim = %o; goal dim = %o).\n", 
                cnt+1, Dimension(S), Dimension(V);

         minus := V!0;
         plus  := V!0;
         if sign le 0 then         
            minus := pi(x - x*star);
         end if;
         if sign ge 0 then
            plus  := pi(x + x*star);
         end if;
         SS := sub<V | X cat [plus, minus]>;               
         if (sign eq 0 and Dimension(SS) eq Dimension(S) + 2) or
            (sign ne 0 and Dimension(SS) eq Dimension(S) + 1) then
               if plus ne 0 then
                  Append(~X, plus); 
               end if;
               if minus ne 0 then
                  Append(~X, minus);
               end if;
               Append(~G, <P,g>);
               S := SS;
         end if;

         cnt +:= 1;
         if fast and cnt gt 100 then
            vprint ModularSymbols, 1 : "Switching methods.";
            return PeriodGenerators(A, false);
         end if;
      end while;
      A`PeriodGens := G;
      A`PGfast     := fast;
   end if;  
   return A`PeriodGens, A`PGfast;
end function;



intrinsic PeriodMapping(A::ModSym, prec::RngIntElt) -> Map
{The complex period mapping, computed using n terms of q-expansion.  
 The period map is a homomorphism M --> C^d, where d is the
 dimension of A.}
   require Sign(A) eq 0 : "Argument 1 must have sign 0.";
   require IsCuspidal(A) : "Argument 1 must be cuspidal.";

   if IsMultiChar(A) then
      require HasAssociatedNewformSpace(A) : "Argument 1 must be created using NewformDecomposition.";
      M := AssociatedNewformSpace(A);
      phi := PeriodMapping(M,prec);
      A`PeriodMapPrecision := prec;
      return hom< AmbientSpace(A) -> Codomain(phi) | 
                   x :-> phi(M!MC_ConvToModularSymbol(AmbientSpace(A),x)) > ;
   end if;

   n := prec;

   if not assigned A`PeriodMap or A`PeriodMapPrecision lt n then
      vprint ModularSymbols : "Computing period mapping.";
      k  := Weight(A);

      /****************************************************************
      * If fast = true then we can use tricks arising from the       *
      * Atkin-Lehner involution to greatly speed of the convergence  *
      * of the series.  If fast = false we rely on a simplistic      *
      * method which gives series that do not converge as quickly.   *
      ****************************************************************/
      fast := (Level(A) gt 1) and (k mod 2 eq 0)
               and IsTrivial(DirichletCharacter(A))
               and IsScalar(AtkinLehner(A,Level(A)));

      vprint ModularSymbols : "Computing period generators.";     
      G, fast  := PeriodGenerators(A, fast);

      vprint ModularSymbols : "Computing an integral basis.";     
      Q  := qIntegralBasis(A, n);
      // A is cuspidal with sign 0, so dimension is twice as large
      dim := Dimension(A) * AbsoluteDegree(BaseRing(A)) / 2;
      if #Q ne dim then
         require #Q le dim : "Too many q-expansions!";
         require #Q eq dim : "The precision ( =", prec, ") is too low";
      end if;
      vprint ModularSymbols : "Found integral basis, now creating C^d.";
      C := ComplexField(); i := C.1;
      Cd := VectorSpace(C,DimensionComplexTorus(A)*Degree(BaseField(A)));

      if fast then
         vprintf ModularSymbols : "\t\t(Using WN trick.)\n";
      end if;

      vprint ModularSymbols : "Computing period integrals.";     
      if fast then
         P  := [Cd![FastPeriodIntegral(A,Q[i],x) : i in [1..#Q]] : x in G];
      else
         P  := [Cd![SlowPeriodIntegral(A,Q[i],x) : i in [1..#Q]] : x in G];
      end if;

      vprint ModularSymbols : "Constructing period mapping from integrals.";     
      M    := AmbientSpace(A);
      star := StarInvolution(M);
      gens := &cat[[v + v*star, v - v*star] where v is 
                   ConvFromModularSymbol(M,
                [ <x[1],[[1,0],[x[2][1],x[2][3]]]>] ) 
                         : x in G];
      // images of the gens
      periods := &cat[[2*Cd![Real(z):z in Eltseq(x)],
                       2*i*Cd![Imaginary(z):z in Eltseq(x)]] : x in P];
      
      pi := RationalPeriodMapping(A);
      PG := [ pi(Representation(g)) : g in gens];
      V  := VectorSpaceWithBasis(PG);      
      
      IMAGES := 
        [ &+[periods[i]*coord[i] : i in [1..#coord]] where
                       coord is Coordinates(V, pi(b)) 
            :        b in Basis(DualRepresentation(M))  ];
      A`PeriodMapPrecision := n;
      W := VectorSpace(ComplexField(),Degree(IMAGES[1]));

      A`PeriodMap := hom<AmbientSpace(A)->W | x :-> &+[y[i]*IMAGES[i] : i in [1..#y]] where
                                 y := Eltseq(x)>;

   end if;
   return A`PeriodMap;
end intrinsic;


intrinsic Periods(M::ModSym, n::RngIntElt) -> SeqEnum
{The complex period lattice associated to A using n terms of the q-expansions.}
   require Sign(M) eq 0 : "Argument 1 must have sign 0.";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   require Type(BaseField(M)) eq FldRat : "The base ring of M must be the rational field.";
   
   if not assigned M`period_lattice  or M`PeriodMapPrecision lt n then
      phi := PeriodMapping(M,n);  // compute to precision n.
      pi := RationalMapping(M);
      L,psi := Lattice(CuspidalSubspace(AmbientSpace(M)));
      piL := [pi(psi(x)) : x in Basis(L)];
      P := MakeLattice(piL);
      B := Basis(P);
      V := LatticeWithBasis(RMatrixSpace(RationalField(),#B,#B)!&cat[Eltseq(b) : b in B]);

      // Now find a set B of elements of L that map onto a basis for W.
      A := RMatrixSpace(IntegerRing(), Rank(L), #B)!
                            &cat[Coordinates(V,V!x) : x in piL];
      Z := RSpace(IntegerRing(),#B);

      C := [];
      for i in [1..#B] do 
         x := Solution(A,Z.i);
         t := x[1]*psi(Basis(L)[1]);
         for j in [2..Rank(L)] do
            if x[j] ne 0 then
               t := t + x[j]*psi(Basis(L))[j];
            end if;
         end for;
         Append(~C, t);
      end for;
      M`period_lattice := [phi(z) : z in C];
   end if;
   return M`period_lattice;
end intrinsic;


intrinsic RealVolume(M::ModSym) -> FldReElt
{The volume vol(A_M(R)) of the real points of the abelian variety 
attached to M.}
   require Sign(M) eq 0 : "Argument 1 must have sign 0.";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   return RealVolume(M,DefaultPrecision(M));
end intrinsic;


intrinsic RealVolume(M::ModSym, n::RngIntElt) -> FldReElt
{The volume vol(A_M(R)) of the real points of the abelian variety 
attached to M.}
   require Sign(M) eq 0 : "Argument 1 must have sign 0.";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   if true or not assigned M`real_volume or M`PeriodMapPrecision lt n then
      r := RationalPeriodMapping(M);
      B := Basis(IntegralRepresentation(CuspidalSubspace(AmbientSpace(M))));
      S := Basis(VectorSpaceZBasis([r(v) : v in B]));
      Conj := RationalPeriodConjugation(M);  // * on Image(r).
      P := IntegerKernelOn(Conj-1, S);  // plus one subspace.
      Z := [v@@r : v in Basis(P)];
      Phi := PeriodMapping(M,n);  
      C := &cat[Eltseq(Phi(AmbientSpace(M)!z)) : z in Z];
      R := MatrixAlgebra(Parent(C[1]), #Z)!C;
      M`real_volume := RealTamagawaNumber(M)*Abs(Determinant(R));
   end if;
   return M`real_volume;
end intrinsic;


intrinsic MinusVolume(M::ModSym) -> FldReElt
{The volume vol(A_M(C)^-) of the points on A_M(C) that are
 in the -1 eigenspace for complex conjugation.}
   require Sign(M) eq 0 : "Argument 1 must have sign 0.";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";

   return MinusVolume(M,DefaultPrecision(M));
end intrinsic;


intrinsic MinusVolume(M::ModSym, n::RngIntElt) -> FldReElt
{The volume vol(A_M(C)^-) of the points on A_M(C) that are
 in the -1 eigenspace for complex conjugation.}
   require Sign(M) eq 0 : "Argument 1 must have sign 0.";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";

   if not assigned M`minus_volume or M`PeriodMapPrecision lt n then
      r := RationalPeriodMapping(M);
      B := Basis(IntegralRepresentation(CuspidalSubspace(AmbientSpace(M))));
      S := Basis(VectorSpaceZBasis([r(v) : v in B]));
      Conj := RationalPeriodConjugation(M);  // * on Image(r).
      P := IntegerKernelOn(Conj+1, S);  // minus one subspace.
      Z := [v@@r : v in Basis(P)];
      Phi := PeriodMapping(M,n);  
      C := &cat[Eltseq(Phi(AmbientSpace(M)!z)) : z in Z];
      R := MatrixAlgebra(Parent(C[1]), #Z)!C;
      M`minus_volume := MinusTamagawaNumber(M)*Abs(Determinant(R));
   end if;
   return M`minus_volume;
end intrinsic;


function PolyOverCyclo_to_PolyOverQ(R)
   S := PolynomialRing(RationalField());
   if ISA(Type(R), FldNum) then
      T := quo<S | DefiningPolynomial(R)>;
      return hom< R -> T | x :-> T!(S!Eltseq(x))>;
   end if;
   h := Modulus(R);
   K := NumberField(h);
   L := AbsoluteField(K);
   poly_ring := Parent(h);
   number_field_coercion_map := hom<poly_ring -> L | L!K.1>;

   T := quo<S | DefiningPolynomial(L)>;
   phi := hom<R -> T | x :-> T!(S!Eltseq(number_field_coercion_map(poly_ring!x)))>;
   return phi;
end function;

intrinsic LSeries(M::ModSym, j::RngIntElt, n::RngIntElt)
                                           -> FldComElt
{The value L(M,j), where j is a critical integer, i.e., one of
 the integers 1,2,...,k-1.  Series are computed to precision n.
 The sign of M must be 0.}

   /************************************************************
    *                                                          
    *  L(f,j) = (2*pi)^(j-1)/(i^(j+1)*(j-1)!)                  
    *            * < f, X^(j-1)*Y^(k-2-(j-1)) {0,oo}>,
    * where
    *      <f,P(X,Y){0,oo}> = -2*pi*i*int_{0}^{ioo} f(z)P(z,1)dz
    *
    *  L(M,j) := prod L(f,j) over the conjugate f's.             
    *                                                          
    ************************************************************/ 
 
   k      := Weight(M);

   require j ge 1 and j le k-1 : "Argument 2 must lie between 1 and k-1, inclusive.";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   require Sign(M) eq 0 : "Argument 1 must have sign 0.";
   /*
   if Sign(M) eq 1 then
      require IsOdd(j) : "The sign of argument 1 is +1, so argument 2 must be odd.";
   end if;
   if Sign(M) eq -1 then
      require IsEven(j) : "The sign of argument 1 is -1, so argument 2 must be even.";
   end if;
   */
   vprintf ModularSymbols, 1: "Computing LSeries(M,%o,%o)...\n",j,n;

   C := ComplexField(); i := C.1;
   R<X,Y> := PolynomialRing(Rationals(),2);

   // In PeriodMaping, prec needs to be large enough that #qIntegralBasis(M,prec) = dim
   // (changed April 2009, SRD)
   dim := Dimension(M) div 2; // since Sign(M) = 0
   prec := Maximum(n, dim+1);
   repeat
      try
         Phi := PeriodMapping(M, prec);
      catch ERR
         if ERR`Object[1..47] eq "Runtime error in 'PeriodMapping': The precision" then 
            prec +:= 1;
         else
            error ERR`Object;
         end if;
      end try;
   until assigned Phi;

   wind   := AmbientSpace(M)!<X^(j-1)*Y^(k-2-(j-1)), [[0,1],[1,0]]>;
   z0     := Phi(wind) ;
   z      := Eltseq((2*Pi(C))^(j-1)/(Factorial(j-1)*i^(j+1)) * z0);

   // The vector z now contains the values L(g,j) as g varies
   // over our basis of modular forms with integer Fourier expansion.
   if #z eq 1 then
      return z[1];   // nothing more to do.
   end if;
   // The linear combination of the integral basis which equals newform f.
   e      := EigenformInTermsOfIntegralBasis(M);
   // If entries of e are over a cyclotomic field (or poly ring over cyclo field),
   // descend them to poly ring over Q.
   phi := PolyOverCyclo_to_PolyOverQ(Parent(e[1]));
   e := [phi(x) : x in e];

   // Q: Field over which the linear combination is defined
   Q      := Parent(e[1]);
   // PC: Polynomial ring in one variable over C.
   PC := PolynomialRing(ComplexField()); a := PC.1;
   // g: Q = Q[x]/(g)
   g      := Modulus(Q);
   // P: Q[x]
   P      := PreimageRing(Q);
   // e: Linear combination lifted to Q[x].
   e      := [P!alpha : alpha in e];  
   // roots: These define the embeddings from Q into the complex field.
   roots  := Roots(PC!g);         // find all conjugates of eigen...
   assert #roots eq Degree(g);   // g must be square free!
   assert #roots eq #e;
   
   // For each embedding sigma of Q into C, take the vector 
   // embedded e's and dot product it with the z vector.   This gives L(sigma(f),j).
   // Now multiply together to get L(A,j).
   Lfval  := &*[ &+[Evaluate(PC!e[i],roots[j][1])*z[i] : i in [1..#z]] 
                     : j in [1..#roots]];
   return Lfval;
end intrinsic;


intrinsic ClassicalPeriod(M::ModSym, j::RngIntElt) 
       -> FldComElt
{The number r_j(f) = int_\{0\}^\{ioo\} f(z) z^j dz.}
   require Sign(M) eq 0 : "Argument 1 must have sign 0.";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
/*
   if Sign(M) eq 1 then
      require IsOdd(j) : "The sign of argument 1 is +1, so argument 2 must be odd.";
   end if;
   if Sign(M) eq -1 then
      require IsEven(j) : "The sign of argument 1 is -1, so argument 2 must be even.";
   end if;
*/

   return ClassicalPeriod(M, j, DefaultPrecision(M));
end intrinsic;


intrinsic ClassicalPeriod(M::ModSym, j::RngIntElt, n::RngIntElt) 
       -> FldComElt
{"} // "
   require Sign(M) eq 0 : "Argument 1 must have sign 0.";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
/*
   if Sign(M) eq 1 then
      require IsOdd(j) : "The sign of argument 1 is +1, so argument 2 must be odd.";
   end if;
   if Sign(M) eq -1 then
      require IsEven(j) : "The sign of argument 1 is -1, so argument 2 must be even.";
   end if;
*/

   C := ComplexField(); i := C.1;
   return Factorial(j)*i^(j+1)*(2*Pi(C))^(-(j+1))*
            LSeries(M,j+1,n);
end intrinsic;


intrinsic MinusTamagawaNumber(M::ModSym) -> RngIntElt
{The number of connected components of the subgroup of
the complex torus A_M(C) that are acted on as -1 by complex
conjugation.}
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   require Sign(M) eq 0 : "Argument 1 must have sign 0.";
   if not assigned M`c_inf_minus then
      C := RationalPeriodConjugation(M);
      Cmod2 := MatrixAlgebra(GF(2),Ncols(C)) ! C;
      M`c_inf_minus := 2^(Dimension(Kernel(Cmod2+1))-DimensionComplexTorus(M));
   end if;
   return M`c_inf_minus;
end intrinsic;


intrinsic RealTamagawaNumber(M::ModSym) -> RngIntElt
{The number of real components of the complex torus
A_M associated to M.}
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   require Sign(M) eq 0 : "Argument 1 must have sign 0.";
   if Dimension(M) eq 0 then
      return 1;
   end if;
   if not assigned M`c_inf then
      C := RationalPeriodConjugation(M);
      Cmod2 := MatrixAlgebra(GF(2),Ncols(C)) ! C;
      M`c_inf := 2^(Dimension(Kernel(Cmod2-1))-DimensionComplexTorus(M));
   end if;
   return M`c_inf;
end intrinsic;



