freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: period.m     (rational period maps)   

   $Header: /home/was/magma/packages/ModSym/code/RCS/period.m,v 1.4 2002/09/17 04:57:05 was Exp was $

   12/09/02: Added IsCuspidal constraints to IntegralMapping.

   $Log: period.m,v $
   Revision 1.4  2002/09/17 04:57:05  was
   Rewrote RationalPeriodLattice.

   Revision 1.3  2001/05/30 19:17:53  was
   ?

   Revision 1.2  2001/04/23 01:11:26  was
   changed RationalMapping comment.

   Revision 1.1  2001/04/20 04:47:01  was
   Initial revision

   Revision 1.6  2001/03/12 04:58:12  was
   Finished implementing IntegralPeriodMapping.

   Revision 1.5  2001/02/07 01:08:33  was
   Add IsCuspidal condition to ModularSymbolOdd/Even.

   Revision 1.4  2001/01/13 04:03:04  was
   In the process of exporting the "RationalPeriodMap" function....  finish!

   Revision 1.3  2000/06/29 21:03:00  was
   special case of dimension 0 for "ScaledRationalPeriodMap".

   Revision 1.2  2000/06/14 18:18:43  was
   Added intrinsic DualModularSymbol(M::ModSym) -> Map

   Revision 1.1  2000/05/02 08:08:55  was
   Initial revision

                                                                            
 ***************************************************************************/

import "linalg.m"   : MakeLattice,
                      VectorSpaceZBasis;

import "arith.m"    : DotProd;

import "subspace.m" : MinusSubspaceDual,
                      PlusSubspaceDual;


/*************************************************************
 *                                                           *
 * COMPUTATION OF THE RATIONAL PERIOD MAPPING                *
 *           r_A : M_k(Q) ----> M_k(Q)/Ker(Phi).             *
 *                                                           *
 *************************************************************/


function ScaledRationalPeriodMap(A) 
   assert IsCuspidal(A);
   /* Compute the rational period mapping.  The period mapping
    is scaled so that the integral modular symbols are
    taken surjectively onto the lattice Z^d. */
   if not assigned A`scaled_rational_period_map then
      d := Dimension(A);
      if d eq 0 then
         A`scaled_rational_period_map := RMatrixSpace(BaseField(A),1,Degree(A))!0;
         return A`scaled_rational_period_map;
      end if;
      P := Transpose(RMatrixSpace(BaseField(A), d, Degree(A))
                                         !Basis(DualRepresentation(A)));
      Z := IntegralRepresentation(CuspidalSubspace(AmbientSpace(A)));
      V := VectorSpace(BaseField(A),Degree(A));
      PofZ := [(V!z)*P : z in Basis(Z)];
      B := Basis(Lattice(RMatrixSpace(Rationals(),
                          #PofZ, d)!PofZ));
      B := [VectorSpace(BaseField(A), d)  |  b : b in B];
      I := (RMatrixSpace(BaseField(A), d, d)!B)^(-1); 
      A`scaled_rational_period_map := P*I;
   end if;
   return A`scaled_rational_period_map;
end function;


intrinsic IntegralMapping(M::ModSym) -> Map
   {A surjective linear map from the ambient space of M to
   a vector space, such that the kernel of this map is the
   same as the kernel of the period mapping.   Note that M must be defined
    over the rational numbers.  This map is normalized so that the
    image of IntegralBasis(CuspidalSubspace(AmbientSpace(M))) is
    the standard Z-lattice.}
 
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   phi := ScaledRationalPeriodMap(M);
   V := Image(phi);
   Amb := AmbientSpace(M);
   W := VectorSpace(Amb);
   return hom<Amb -> V | x :-> phi(W!Eltseq(x)) > ;
end intrinsic;


function RationalPeriodMapping(A)
// {A map r_A : VectorSpace(M_k(Q)) ----> M_k(Q)/Ker(Phi).}
   if not assigned A`RatPeriodMap then
      M := AmbientSpace(A);
      V := VectorSpace(BaseField(M), Dimension(A));
        dat := [V![DotProd(m,a) : a in Basis(DualVectorSpace(A))] 
                       : m in Basis(DualVectorSpace(M))];
        AmbV := VectorSpace(BaseField(M),Dimension(M));
        A`RatPeriodMap := hom < AmbV -> V | dat>;
   end if;
   return A`RatPeriodMap;
end function;


intrinsic RationalMapping(M::ModSym) -> Map
   {A surjective linear map from the ambient space of M to
   a vector space, such that the kernel of this map is the
   same as the kernel of the period mapping.}
   phi := RationalPeriodMapping(M);
   V := Image(phi);
   Amb := AmbientSpace(M);
   W := VectorSpace(Amb);   
   return hom<Amb -> V | x :-> phi(W!Eltseq(x))> ;
end intrinsic;


intrinsic DualModularSymbol(M::ModSym) -> Map
{The dual modular symbol associated to M, viewed as a map of Hecke modules 
 M_k ----> M_k/Ker(Phi_M), where the quotient is viewed as 
 an abstract *vector space.*}
   phi := RationalPeriodMapping(M);
   V := Image(phi);
   A := AmbientSpace(M);
   return  hom< A->V | x :-> phi(VectorSpace(A)!Eltseq(x)) > ;
end intrinsic;


function SignedRationalPeriodMapping(A, sign)
// Returns the map r_A : M_k(Q) ----> M_k(Q)/(Ker(Phi)+(sign quotient)).
   if not assigned A`RatPeriodMapSign then
      M      := VectorSpace(AmbientSpace(A));
      Bplus  := PlusSubspaceDual(A);
      Bminus := MinusSubspaceDual(A);
      V      := VectorSpace(BaseField(M), Dimension(Bplus));
      A`RatPeriodMapSign := 
           [* hom < M -> V | 
                [V![InnerProduct(m,b) : b in Basis(DualRepresentation(Bplus))] 
                        : m in Basis(M)]>,
              hom < M -> V | 
                [V![InnerProduct(m,b) : b in Basis(DualRepresentation(Bminus))]     
                        : m in Basis(M)]> *];
   end if;
   if sign eq 1 then
      return A`RatPeriodMapSign[1];
   else
      return A`RatPeriodMapSign[2];
   end if;
end function;

function RationalPeriodLattice(A) 
// Returns a basis for the image of S_k(Z) in M_k/Ker(Phi).
   if not assigned A`RatPeriodLat then
      pi := RationalMapping(A);
      // Generators for rational period lattice.
/*      B  := [pi(v) : v in 
             Basis(Lattice(CuspidalSubspace(AmbientSpace(A))))];
*/
      B := [pi(x) : x in IntegralBasis(CuspidalSubspace(AmbientSpace(A)))];
      A`RatPeriodLat := MakeLattice(B);
   end if;
   return A`RatPeriodLat;
end function;

function RationalPeriodConjugation(A) 
// Returns matrix of "conjugation" with respect to the 
// basis of RationalPeriodLattice(A).
   if not assigned A`RatPeriodConj then
      pi   := RationalPeriodMapping(A);
      Z    := RationalPeriodLattice(A);
      B    := Basis(Z);
      V := VectorSpaceWithBasis([Codomain(pi)!x : x in B]);
      star := StarInvolution(AmbientSpace(A));
      C    := [Coordinates(V, pi((b@@pi)*star)) : b in B];
      C    := &cat[Eltseq(x) : x in C];
      A`RatPeriodConj := MatrixAlgebra(BaseField(A), #B)!C;
   end if;
   return A`RatPeriodConj;
end function;

intrinsic ModularSymbolEven(M::ModSym, x::RngIntElt) -> ModTupFldElt
{The "even modular symbol phi_M^+", as on page 209 of Mazur, "On the Arithmetic
of Special Values of L-functions."}
   require Weight(M) eq 2 : "Argument 1 must have weight 2.";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";

   return ModularSymbolEven(M,x*1/1);
end intrinsic;

intrinsic ModularSymbolEven(M::ModSym, x::FldRatElt) -> ModTupFldElt
{The "even modular symbol phi_M^+", as on page 209 of Mazur, "On the Arithmetic
of Special Values of L-functions."}
   require Weight(M) eq 2 : "Argument 1 must have weight 2.";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   
   A := AmbientSpace(M);
   z := A!<1,[Cusps()|x,Infinity()]> + A!<1,[Cusps()|-x,Infinity()]>;
   return VectorSpace(A)!Eltseq(z)*ScaledRationalPeriodMap(M);
end intrinsic;

intrinsic ModularSymbolOdd(M::ModSym, x::RngIntElt) -> ModTupFldElt
{The "odd modular symbol phi_M^-", as on page 209 of Mazur, "On the Arithmetic
of Special Values of L-functions."}
   require Weight(M) eq 2 : "Argument 1 must have weight 2.";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";

   return ModularSymbolOdd(M,x*1/1);
end intrinsic;

intrinsic ModularSymbolOdd(M::ModSym, x::FldRatElt) -> ModTupFldElt
{The "odd modular symbol phi_M^-", as on page 209 of Mazur, "On the Arithmetic
of Special Values of L-functions."}
   require Weight(M) eq 2 : "Argument 1 must have weight 2.";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   
   A := AmbientSpace(M);
   z := A!<1,[Cusps()|x,Infinity()]> - A!<1,[Cusps()|-x,Infinity()]>;
   return VectorSpace(A)!Eltseq(z)*ScaledRationalPeriodMap(M);
end intrinsic;
