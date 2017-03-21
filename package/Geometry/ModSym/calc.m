freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: calc.m (Standard calculations)

   2004-10-24: (was) commented out some exported intrinsics that begin xxx_

   2003/12/14: was
   In modular degree I wrote Floor(Sqrt(ord)), then asserted
   that it was equal to the integer square root of ord.  
   David Kohel pointed out that a much better way is to use

   Revision 1.21  2002/10/02 19:04:25  was
   No need to check that poly is irreducible when creating number field
   in HeckeEigenvalueField.

   Revision 1.20  2002/10/02 18:57:43  was
   Added
   intrinsic HeckeAlgebraFields(M::ModSym) -> SeqEnum

   Revision 1.19  2002/10/02 18:05:10  was
   Removed some experimental code.

   Revision 1.18  2002/10/02 17:33:11  was
   *** empty log message ***

   Revision 1.17  2002/08/29 01:47:33  was
   Added multichar code.

   Revision 1.16  2002/05/04 16:44:49  was
   Minor update to HeckeEigenvalueField because coercion from polynomial
   ring to number field is no longer allowed.

   Revision 1.15  2002/04/10 03:29:42  was
   change a ! to a | in HeckeAlgebraZBasis.

   Revision 1.14  2002/04/10 03:21:55  was
   Added HeckeAlgebraZBasis.

   Revision 1.13  2002/01/22 02:09:57  was
   Improved the maps returned by SubgroupOfTorus and RationalCuspidalSubgroup.

   Revision 1.12  2002/01/21 01:52:04  was
   same..

   Revision 1.11  2002/01/21 01:47:53  was
   LRatio allowed even when sign is =/= 0 again, since it is
   often way faster than LRatioOddPart.

   Revision 1.10  2002/01/21 01:10:00  was
   Added a Bound parameter to LRatioOdd.

   Revision 1.9  2002/01/20 03:43:07  was
   Added CuspidalSubgroup and RationalCuspidalSubgroup.

   Revision 1.8  2001/09/03 01:41:24  was
   .

   Revision 1.7  2001/06/30 03:15:54  was
   Better require statements in LRatio.

   Revision 1.6  2001/05/30 19:17:14  was
   ?

   Revision 1.5  2001/05/13 03:44:21  was
   verbose change

   Revision 1.4  2001/04/23 01:11:53  was
   Deleted "ElementProjection", which offered the same functionality as RationalMapping (periods.m).

   Revision 1.3  2001/04/23 00:53:47  was
   Improved the comment for "CongruenceModulus".

   Revision 1.2  2001/04/23 00:52:01  was
   Improved the comment for CongruenceGroup.

   Revision 1.1  2001/04/20 04:44:20  was
   Initial revision

   Revision 1.22  2001/04/19 06:23:04  was
   *** empty log message ***

   Revision 1.23  2001/04/14 03:54:44  was
   Fixed a bug in LRatio.  The result of LRatio was off by a factor of
   RealTamagawaNumber or MinusTamagawaNumber from what is claimed in the
   documentation.   This is because I had "thought of" LRatio as being
   the number computed before dividing by the number of real components;
   however, the documentation says otherwise.  Now it is fixed.

   Revision 1.22  2001/04/12 20:41:06  was
   Fixed a VERY embarassingly stupid bug in the
   implementation of IntersectionGroup.  This probably doesn't affect weight-2
   computations, but did cause serious problems in higher weight.  For example
    M := MS(127,4,+1); D := DC(M,2); factor(#IntersectionGroup(D[2],D[3]));
   gave nonsense (the answer should be only divisible by 2 and 127).
   The problem is now fixed!

   Revision 1.21  2001/02/27 15:02:41  was
   Added
      if Dimension(W) eq 0 then
         return Rationals()!0;
      end if;
   to the beginning of PeriodIndex to address a special case.

   Revision 1.20  2001/01/15 23:33:38  was
   Added a comment that gives how to write HeckeEigenvalueField in more
   generality.

   Revision 1.19  2001/01/14 06:55:30  was
   nothing.

   Revision 1.18  2000/10/28 10:58:05  was
   Nothing.

   Revision 1.17  2000/08/21 01:20:01  was
   I don't know.

   Revision 1.16  2000/08/01 21:16:53  was
   Added an additional special case to SubgroupOfTorus, which deals
   with the case Dimension(A) = 0.

   Revision 1.15  2000/07/27 07:47:26  was
   nothing, really.

   Revision 1.14  2000/06/29 21:06:27  was
   Changed SubgroupOfTorus to deal with trivial case.

   Revision 1.13  2000/06/29 03:42:26  was
   I don't remember.

   Revision 1.12  2000/06/22 01:58:57  was
   fixed small bug in WindingElement -- when called with M not ambient it
   went boom.

   Revision 1.11  2000/06/22 01:42:32  was
   fine tuning TwistedWindingSubmodule (added cacheing)

   Revision 1.10  2000/06/21 23:46:30  was
   Added TwistedLDim, TwistedWindingSubmodule.

   Revision 1.9  2000/06/14 18:32:02  was
   Added intrinsic TwistedWindingElement(M::ModSym, i::RngIntElt, eps::GrpDrchElt) -> ModSymElt

   Revision 1.8  2000/06/05 00:45:10  was
   *** empty log message ***

   Revision 1.7  2000/06/03 04:57:51  was
   verbose

   Revision 1.6  2000/06/03 03:42:34  was
   Round

   Revision 1.5  2000/05/04 10:12:38  was
   Changed OrderOfTorusPoint to SubgroupOfTorus.

   Revision 1.4  2000/05/03 14:53:21  was
   More robust error checking sign-wise.

   Revision 1.3  2000/05/02 17:49:44  was
   Made LRatioOddPart and LRatio more robust, and added better error checking.

   Revision 1.2  2000/05/02 07:56:11  was
   Added $Log: calc.m,v $
   Added Revision 1.21  2002/10/02 19:04:25  was
   Added No need to check that poly is irreducible when creating number field
   Added in HeckeEigenvalueField.
   Added
   Added Revision 1.20  2002/10/02 18:57:43  was
   Added Added
   Added intrinsic HeckeAlgebraFields(M::ModSym) -> SeqEnum
   Added
   Added Revision 1.19  2002/10/02 18:05:10  was
   Added Removed some experimental code.
   Added
   Added Revision 1.18  2002/10/02 17:33:11  was
   Added *** empty log message ***
   Added
   Added Revision 1.17  2002/08/29 01:47:33  was
   Added Added multichar code.
   Added
   Added Revision 1.16  2002/05/04 16:44:49  was
   Added Minor update to HeckeEigenvalueField because coercion from polynomial
   Added ring to number field is no longer allowed.
   Added
   Added Revision 1.15  2002/04/10 03:29:42  was
   Added change a ! to a | in HeckeAlgebraZBasis.
   Added
   Added Revision 1.14  2002/04/10 03:21:55  was
   Added Added HeckeAlgebraZBasis.
   Added
   Added Revision 1.13  2002/01/22 02:09:57  was
   Added Improved the maps returned by SubgroupOfTorus and RationalCuspidalSubgroup.
   Added
   Added Revision 1.12  2002/01/21 01:52:04  was
   Added same..
   Added
   Added Revision 1.11  2002/01/21 01:47:53  was
   Added LRatio allowed even when sign is =/= 0 again, since it is
   Added often way faster than LRatioOddPart.
   Added
   Added Revision 1.10  2002/01/21 01:10:00  was
   Added Added a Bound parameter to LRatioOdd.
   Added
   Added Revision 1.9  2002/01/20 03:43:07  was
   Added Added CuspidalSubgroup and RationalCuspidalSubgroup.
   Added
   Added Revision 1.8  2001/09/03 01:41:24  was
   Added .
   Added
   Added Revision 1.7  2001/06/30 03:15:54  was
   Added Better require statements in LRatio.
   Added
   Added Revision 1.6  2001/05/30 19:17:14  was
   Added ?
   Added
   Added Revision 1.5  2001/05/13 03:44:21  was
   Added verbose change
   Added
   Added Revision 1.4  2001/04/23 01:11:53  was
   Added Deleted "ElementProjection", which offered the same functionality as RationalMapping (periods.m).
   Added
   Added Revision 1.3  2001/04/23 00:53:47  was
   Added Improved the comment for "CongruenceModulus".
   Added
   Added Revision 1.2  2001/04/23 00:52:01  was
   Added Improved the comment for CongruenceGroup.
   Added
   Added Revision 1.1  2001/04/20 04:44:20  was
   Added Initial revision
   Added
   Added Revision 1.22  2001/04/19 06:23:04  was
   Added *** empty log message ***
   Added
   Added Revision 1.23  2001/04/14 03:54:44  was
   Added Fixed a bug in LRatio.  The result of LRatio was off by a factor of
   Added RealTamagawaNumber or MinusTamagawaNumber from what is claimed in the
   Added documentation.   This is because I had "thought of" LRatio as being
   Added the number computed before dividing by the number of real components;
   Added however, the documentation says otherwise.  Now it is fixed.
   Added
   Added Revision 1.22  2001/04/12 20:41:06  was
   Added Fixed a VERY embarassingly stupid bug in the
   Added implementation of IntersectionGroup.  This probably doesn't affect weight-2
   Added computations, but did cause serious problems in higher weight.  For example
   Added  M := MS(127,4,+1); D := DC(M,2); factor(#IntersectionGroup(D[2],D[3]));
   Added gave nonsense (the answer should be only divisible by 2 and 127).
   Added The problem is now fixed!
   Added
   Added Revision 1.21  2001/02/27 15:02:41  was
   Added Added
   Added    if Dimension(W) eq 0 then
   Added       return Rationals()!0;
   Added    end if;
   Added to the beginning of PeriodIndex to address a special case.
   Added
   Added Revision 1.20  2001/01/15 23:33:38  was
   Added Added a comment that gives how to write HeckeEigenvalueField in more
   Added generality.
   Added
   Added Revision 1.19  2001/01/14 06:55:30  was
   Added nothing.
   Added
   Added Revision 1.18  2000/10/28 10:58:05  was
   Added Nothing.
   Added
   Added Revision 1.17  2000/08/21 01:20:01  was
   Added I don't know.
   Added
   Added Revision 1.16  2000/08/01 21:16:53  was
   Added Added an additional special case to SubgroupOfTorus, which deals
   Added with the case Dimension(A) = 0.
   Added
   Added Revision 1.15  2000/07/27 07:47:26  was
   Added nothing, really.
   Added
   Added Revision 1.14  2000/06/29 21:06:27  was
   Added Changed SubgroupOfTorus to deal with trivial case.
   Added
   Added Revision 1.13  2000/06/29 03:42:26  was
   Added I don't remember.
   Added
   Added Revision 1.12  2000/06/22 01:58:57  was
   Added fixed small bug in WindingElement -- when called with M not ambient it
   Added went boom.
   Added
   Added Revision 1.11  2000/06/22 01:42:32  was
   Added fine tuning TwistedWindingSubmodule (added cacheing)
   Added
   Added Revision 1.10  2000/06/21 23:46:30  was
   Added Added TwistedLDim, TwistedWindingSubmodule.
   Added
   Added Revision 1.9  2000/06/14 18:32:02  was
   Added Added intrinsic TwistedWindingElement(M::ModSym, i::RngIntElt, eps::GrpDrchElt) -> ModSymElt
   Added
   Added Revision 1.8  2000/06/05 00:45:10  was
   Added *** empty log message ***
   Added
   Added Revision 1.7  2000/06/03 04:57:51  was
   Added verbose
   Added
   Added Revision 1.6  2000/06/03 03:42:34  was
   Added Round
   Added
   Added Revision 1.5  2000/05/04 10:12:38  was
   Added Changed OrderOfTorusPoint to SubgroupOfTorus.
   Added
   Added Revision 1.4  2000/05/03 14:53:21  was
   Added More robust error checking sign-wise.
   Added
   Added Revision 1.3  2000/05/02 17:49:44  was
   Added Made LRatioOddPart and LRatio more robust, and added better error checking.
   Added

                                                                            
 ***************************************************************************/

import "arith.m":  NormPolResElt, 
                   SmallestPrimeNondivisor,
                   DotProd,
                   OddPart;

import "core.m"  : ConvFromModularSymbol;

import "linalg.m": AbelianGroupQuotient, 
                   DiscriminantMatAlgZ,
                   IndexInSaturation,
                   LatticeIndex,
                   MakeLattice,
                   TrivialLattice,
                   Volume,
                   ZAlgDisc;

import "multichar.m" : AssociatedNewformSpace,
                       HasAssociatedNewformSpace;

import "period.m": RationalPeriodMapping,
                   RationalPeriodLattice,
                   RationalPeriodConjugation,
                   ScaledRationalPeriodMap;

import "qexpansion.m": EigenvectorModSymSign;

import "representation.m": 
                   DualIntegralCuspidalRepresentation, 
                   IntegralCuspidalRepresentation;

import "subspace.m":MinusSubspaceSub,
                   PlusSubspaceDual,
                   PlusSubspaceSub;

forward PeriodImage;


intrinsic HeckeAlgebraZBasis(M::ModSym) -> SeqEnum
{A sequence of matrices that form a Z-basis for the 
 Hecke algebra attached to M.}
   require Type(BaseField(M)) eq FldRat : "Argument 1 must be over the rational field.";
   require Sign(M) ne 0 : "Argument 1 must have nonzero sign.";
   if not assigned M`hecke_algebra_z_basis then
      Bound := HeckeBound(M);
      vprintf ModularSymbols : 
         "Computing hecke algebra Z basis at level %o (using %o generators).\n", Level(M), Bound;
      V := VectorSpace(RationalField(),Dimension(M)^2);
      T := [V | Eltseq(HeckeOperator(M,n)) : n in [1..Bound]];
      L := MakeLattice(T);
      Mat := MatrixAlgebra(RationalField(),Dimension(M));
      M`hecke_algebra_z_basis := [Mat!Eltseq(b) : b in Basis(L)];
   end if;   
   return M`hecke_algebra_z_basis;
end intrinsic;

/*intrinsic HeckeAlgebraTensorQ(M::ModSym) -> AlgMat
{The Hecke algebra over Q associated to M.}
   require Sign(M) ne 0 : "Argument 1 must have nonzero sign.";
   if not assigned M`hecke_algebra_over_q then
      if IsVerbose("ModularSymbols") then
         printf "Computing hecke algebra at level %o.\n", 
               Level(M);
      end if;
      MAT := MatrixAlgebra(BaseField(M),Dimension(M));
      T := sub<MAT | [MAT!1]>;
      n := 2;
      while Dimension(T) lt Dimension(M) and n lt HeckeBound(M) do
print Dimension(T);
time         t := HeckeOperator(M,n);
time         T := T + sub<MAT | t>;
         //T := T + sub<MAT | [t^i : i in [2..Dimension(M)-1]]> ;
         n := n + 1;
      end while;
      M`hecke_algebra_over_q := T;
   end if;
   return M`hecke_algebra_over_q; 
end intrinsic;
*/


intrinsic HeckeAlgebra(M::ModSym: Bound := -1) -> AlgMat
{The Hecke algebra associated to M.  If the optional integer parameter 
Bound is set, then the algebra generated only by those T_n, with
n <= Bound, is computed.  This is a Q-algebra T such that Generators(T) 
is guaranteed to be a Z-generator set for the module generated over Z
by all Hecke operators.  To get a Q-algebra whose generators have no
special integral structure, use the HeckeAlgebraTensorQ command, which
is much faster.}

   // The following requirement is made because we don't know a good bound
   // on the number of additive generators in general. 
   // Usually it is larger than HeckeBound(M), e.g., N=54,k=2.
   require Sign(M) ne 0 : "Argument 1 must have nonzero sign.";
   require IsCuspidal(M) : "Argument 1 must be contained in the cuspidal subspace.";

   if not assigned M`hecke_algebra then
      if Bound eq -1 then
         Bound := HeckeBound(M);
      end if;
      requirege Bound,0;
      if IsVerbose("ModularSymbols") then
         printf "Computing hecke algebra at level %o (using %o generators).\n", 
               Level(M), Bound;
      end if;
      if Dimension(M) ge Dimension(AmbientSpace(M)) / 2 then
         P := PlusSubspaceSub(M);
         alg := sub<MatrixAlgebra(BaseField(M),Dimension(P)) | 
                 [HeckeOperator(P,n) : n in [1..Bound]]>;
      else
         P := PlusSubspaceDual(M);
         alg := sub<MatrixAlgebra(BaseField(M),Dimension(P)) | 
                 [DualHeckeOperator(P,n) : n in [1..Bound]]>;
      end if;     
      if Bound ge HeckeBound(M) then
         M`hecke_algebra := alg;
      else
         return alg;
      end if;
   end if;
   return M`hecke_algebra; 
end intrinsic;


intrinsic DiscriminantOfHeckeAlgebra(M::ModSym: 
                       Bound := -1) -> RngIntElt
{The discriminant of the Hecke algebra associated to M.
If the optional parameter Bound is set, then the discriminant
of the algebra generated by only those T_n, with n <= Bound, 
is computed instead.}
   require BaseField(M) cmpeq RationalField() :
         "The base field of M must be the rationals.";

   require IsCuspidal(M) : "Argument 1 must be contained in the cuspidal subspace.";

   if not assigned M`hecke_algebra_disc then
      if Dimension(M) eq 0 then
         M`hecke_algebra_disc := 1;
         return 1;
      end if;     
      T := HeckeAlgebra(M : Bound := Bound);
      if IsVerbose("ModularSymbols") then
         printf "Computing discriminant at level %o.\n", Level(M);
      end if;
      disc := DiscriminantMatAlgZ(T, Sign(M) eq 0 select Dimension(M) div 2 else Dimension(M));
      if assigned M`hecke_algebra then
         M`hecke_algebra_disc := disc;
      else
         return disc;
      end if;
   end if;
   return M`hecke_algebra_disc; 
end intrinsic;


/*intrinsic XXXTorsionBound(A::ModSym, maxp::RngIntElt) -> RngIntElt
{The following upper bound on the torsion subgroup of A:   
      gcd \{ #A(F_p) : 3 <= p <= maxp, p not dividing Level(A)\}.}

   require Weight(A) eq 2 and IsTrivial(DirichletCharacter(A)) : 
       "Argument 1 must have weight 2 and trivial character.";
   require Type(BaseField(A)) eq FldRat : 
      "The base field of argument 1 must be the rationals.";
   S := [ p : p in [3..maxp] | 
               IsPrime(p) and Level(A) mod p ne 0];
   seq := [Integers()|Evaluate(
            CharacteristicPolynomial(HeckeOperator(A, p) : 
                                              Al := "pAdic"), p+1) 
                   : p in S];
   bound := Gcd(seq);
   if Sign(A) eq 0 then
      b := Integers()!Floor(Sqrt(bound));
      assert b^2 eq bound;
      bound := b;
   end if;
   return bound, seq;

end intrinsic;
*/

function PolyNorm(f)
   R := Parent(f);
   K := BaseRing(R);
   if Type(K) eq FldRat then
      return f;
   end if;
   assert Type(K) eq FldCyc;
   v := Eltseq(f);
   return PolynomialRing(RationalField())!
             &*[R![sigma(a) : a in v] : sigma in Automorphisms(K)];
end function;

intrinsic CharpolyOfFrobenius(M::ModSym, p::RngIntElt) -> RngUPolElt
{The characteristic polynomial of Frob_p acting on the dimension 2g 
 Q_ell-adic representation attached to the newform class associated to M.
 We assume that M corresponds to a single Gal(Qbar/Q)-conjugacy class of
 newforms.  This function returns the charpoly, over Q, of Frobenius
 acting on any of corresponding ell-adic representations.}
   /* This algorithm is described in Section 3.5 of Agashe-Stein, 
      "Visible Evidence ..." */

   require Level(M) mod p ne 0 : 
              "Argument 2 must not divide the level of argument 1.";
   require Type(BaseField(M)) in {FldRat, FldCyc} : 
              "Argument 1 must be defined over Q or a cyclotomic field.";
   require IsCuspidal(M) : 
              "Argument 1 must be cuspidal.";

   if IsMultiChar(M) then
      if HasAssociatedNewformSpace(M) then
         M := AssociatedNewformSpace(M);
      else
         return &*[ CharpolyOfFrobenius(A,p) : A in NewformDecomposition(M)];
      end if;
   end if;


   eps := DirichletCharacter(M);
   require BaseRing(Parent(eps)) eq BaseRing(Parent(MinimalBaseRingCharacter(eps))) : 
        "The Dirichlet character eps attached to M must be defined over Q(eps).";

   Gp := CharacteristicPolynomial(HeckeOperator(M,p));

   if Sign(M) eq 0 then
      Gp := Sqrt(Gp);
   end if;

   R := Parent(Gp);  X := R.1;
   dprime := Dimension(M) div (Sign(M) eq 0 select 2 else 1);
   k := Weight(M);
   h := X^dprime * Evaluate(Gp,X+Evaluate(eps,p)*p^(k-1)/X);
   a :=  PolyNorm(R!h);
   return a;
end intrinsic;

intrinsic TorsionBound(M::ModSym, n::RngIntElt) -> RngIntElt
{A bound on the size of the rational torsion subgroup of the
associated abelian variety A_f obtained by looking at the 
first n good odd primes.}
/* We compute #M(F_p) = deg(1-Frob_p) for lots of primes p, as indicated. */
   if Dimension(M) eq 0 then
      return 1;
   end if;
   S := [ p : p in [3..n] |  IsPrime(p) and Level(M) mod p ne 0];
   return GCD([Integers()|Evaluate(CharpolyOfFrobenius(M, p), 1) : p in S]);
end intrinsic;

intrinsic SubgroupOfTorus(M::ModSym, x::ModSymElt) -> RngIntElt
{The cyclic subgroup of the complex torus attached to M
that is generated by the image under the period map of the point x.}

   return SubgroupOfTorus(M,[x]);

end intrinsic;


intrinsic SubgroupOfTorus(M::ModSym, s::[ModSymElt]) -> GrpAb, Map, Map
{An abelian group G that is isomorphic to the finite group 
generated by the sequence of images pi(s[i]) in the complex 
torus attached to M, where pi is PeriodMapping(M).
This intrinsic also returns a map from AmbientSpace(M)
to G, which is defined only on the subgroup generated
by the s (i.e., there is an error if you evaluate 
it elsewhere), and a set-theoretic section from G to AmbientSpace(M).}

   if #s eq 0 or Dimension(M) eq 0 then
      G := AbelianGroup([]);
      return G, map<AmbientSpace(M) -> G | x :-> G!0>,
		map<G -> AmbientSpace(M) | x :-> AmbientSpace(M)!0>;
   end if;

   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   require s[1] in AmbientSpace(M) :
          "The elements of argument 2 must lie in the ambient space of argument 1.";

   // S is a matrix that maps the integral homology exactly onto the
   // the trivial lattice Z^n.
   S   := ScaledRationalPeriodMap(M);   

   // Sinv is a left inverse for S.
   Sinv := Solution(S,IdentityMatrix(BaseRing(S),Ncols(S)));

   ims := [Representation(x)*S : x in s];
   if #ims eq 0 or not exists (i) {i : i in [1..#ims] | ims[i] ne Parent(ims[1])!0} then
      G := AbelianGroup([]);
      return G, map<AmbientSpace(M) -> G | x :-> G!0>,
		map<G -> AmbientSpace(M) | x :-> AmbientSpace(M)!0>;
   end if;
   Im  := MakeLattice(ims);
   Std := TrivialLattice(Degree(Im));
   G, phi := quo<Im | Std meet Im>;
   V := VectorSpace(RationalField(),Degree(Im));
   psi := map<AmbientSpace(M) -> G | x :-> phi(Im!(Representation(x)*S))>;
   lifting := map<G -> AmbientSpace(M) | 
          x :-> AmbientSpace(M)!(V!(x@@phi)*Sinv)>;
   return G, psi, lifting; 
end intrinsic;

intrinsic CuspidalSubgroup(M::ModSym) -> GrpAb, Map
{The subgroup C of the abelian variety attached to M generated by the
cusps on X_0(N), along with a map sending the rational number alpha
to the image of (alpha)-(oo) in C.}

   require IsTrivial(DirichletCharacter(M)) : 
                      "The dirichlet character of M must be trivial.";
   require Weight(M) eq 2 : "The weight of M must equal 2.";

   require IsCuspidal(M) : "Argument 1 must be cuspidal.";

   A := AmbientSpace(M);
   oo := Cusps()!Infinity();
   X := [A!<1,[alpha,oo]> : alpha in Cusps(M) | alpha ne oo];
   G, phi := SubgroupOfTorus(M,X);
   psi := map<RationalField() -> G | 
                        x :-> phi(A!<1,[StandardCusp(A,x),oo]>)>;
   return G, psi;
end intrinsic;

intrinsic RationalCuspidalSubgroup(M::ModSym) -> GrpAb
{The subgroup C of the abelian variety quotient of J_0(N) 
attached to M generated by the rational cusps on X_0(N).  
(To compute the map that sends a rational number to 
its image in C, see CuspidalSubgroup.)}
   require IsTrivial(DirichletCharacter(M)) : "The dirichlet character of M must be trivial.";
   require Weight(M) eq 2 : "The weight of M must equal 2.";
   require Type(BaseField(M)) eq FldRat : "Argument 1 must be over the rational field.";
   A := AmbientSpace(M);
   oo := Cusps()!Infinity();
   X := [A!<1,[alpha,oo]> : alpha in RationalCusps(M) | alpha ne oo];
   G, _ := SubgroupOfTorus(M,X);
   return G ;
end intrinsic;


intrinsic ModularKernel(M::ModSym) -> GrpAb
{The kernel of the modular isogeny.  Let T be the complex torus attached to M.
Then the modular isogeny is the natural map from the dual of T into T 
induced by autoduality of CuspidalSubspace(AmbientSpace(M)).}
   require IsCuspidal(M) : "Argument 1 must be cuspidal";
   require Type(BaseField(M)) eq FldRat : "Argument 1 must have base field the rational numbers.";
   if not assigned M`modular_kernel then
      BZ  := Basis(IntegralCuspidalRepresentation(M));
      BZdual := Basis(DualIntegralCuspidalRepresentation(M));
      D := MatrixAlgebra(Integers(),#BZ)! 
            [InnerProduct(v, w) : v in BZ, w in BZdual];
      S := SmithForm(D);
      M`modular_kernel := 
         AbelianGroup([S[i,i] : i in [1..Ncols(S)] | S[i,i] ne 1]);
   end if;
   return M`modular_kernel;
end intrinsic;


intrinsic ModularDegree(M::ModSym) -> RngIntElt
{This is Sqrt(#ModularKernel(M)).  If A_M is an elliptic curve E,
then this degree of the map of algebraic curves X_0(N) --> E.}

/*******************************************************************
  IMPLEMENTATION WARNING:
     "My" algorithm for computing the modular degree is very simple.
     Cremona's book and one of his papers contains a possibly better
     algorithm in some elliptic curve situations, especially when 
     working in the +1 quotient.   At some point I'll have to 
     implement it.
 *******************************************************************/

   require IsTrivial(DirichletCharacter(M)) : "Argument 1 must have trivial character.";
   require Weight(M) eq 2 : "Argument 1 must have weight 2.";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";

   if not assigned M`modular_degree then
      ord := Order(ModularKernel(M));
      if Sign(M) eq 0 then
         M`modular_degree := Isqrt(ord);
         assert M`modular_degree^2 eq ord;
      else
         M`modular_degree := ord;
         if IsVerbose("ModularSymbols") then
            print "WARNING: Because working in +1 or -1 quotient, the modular degree is only correct up to a power of 2.";
         end if;
      end if;
   end if;
   return M`modular_degree;
end intrinsic;


intrinsic pNewModularDegree(M::ModSym, p::RngIntElt) -> RngIntElt
   {The p-new modular degree of M.  Assume that M has
   trivial character, is p-new, and for notational simplicity
   the weight of $M$ is $2$.  Let r be the (rational)
   period map.  The p-new modular degree of M is the order of
   the finite quotient
        r(H_\{p-new\}) / r(M), where H_\{p-new\}
   is the p-new subspace of H = H_1(X_0(N),Z) and N is the level of M.
   WARNING:  This number need not be a square, so we do not take the
   square root as we would for the usual modular degree.}

   require IsPrime(p) : "Argument 2 must be prime.";
   require IsTrivial(DirichletCharacter(M)) : "Argument 1 must have trivial character.";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";

   Hpnew := NewSubspace(CuspidalSubspace(AmbientSpace(M)),p);
   Hpnew_b := CuspidalSubspace(AmbientSpace(M));
   require M subset Hpnew : "Argument 1 must be p-new, where p is argument 2.";

   r := RationalPeriodMapping(M);

   HpnewZ := IntegralRepresentation(Hpnew);
   HpnewZIf := IntegralRepresentation(M);

   r1 := PeriodImage(M,HpnewZ);
   r2 := PeriodImage(M,HpnewZIf);

   ord := LatticeIndex(r1,r2);
   if Sign(M) ne 0 then
      vprint ModularSymbols : "WARNING: Because working in +1 or -1 quotient, the modular degree is only correct up to a power of 2.";
   end if;
   return ord;
end intrinsic;


intrinsic CongruenceModulus(M::ModSym : 
                          Bound := -1) -> RngIntElt
{The congruence number r of M.  This is the index in
 S=S_k(Gamma_0(N),Z) of the sum L+W of the lattice of 
cusp form L corresponding to M and the lattice 
of cusp forms corresponding to the complement of L in S.}

   return #CongruenceGroup(M : Bound := Bound);

end intrinsic;


intrinsic CongruenceGroup(M::ModSym :
                          Bound := -1) -> GrpAb
{The congruence group of space of cusp forms corresponding to the
 space of cuspidal modular symbols M.  Let S=S_k(Gamma_0(N),Z), 
 let V be the sub Z-module corresponding to 
 M, and W be its orthogonal complement.  Then the congruence
 group is S/(V+W).  This group encodes information about congruences
 between forms in V and forms in the complement of V.

 The optional parameter Bound is a bound on the number
 of Hecke operators used in the computation; if it is too small,
 then Congruence group will give only an upper bound on
 the correct answer.  The default is HeckeBound(M) + 1, which
 gives a provably correct answer.}
 
   if not assigned M`congruence_group then
      if Bound eq -1 then
         Bound := HeckeBound(M)+1;
      end if;
      requirege Bound,0;
      require IsCuspidal(M) : "Argument 1 must be cuspidal.";
      if Dimension(M) eq Dimension(CuspidalSubspace(AmbientSpace(M))) then
         return AbelianGroup([]);
      end if;
      Q1 := qIntegralBasis(M, Bound);
      Mperp := CuspidalSubspace(Complement(M));
      Q2 := qIntegralBasis(Mperp,Bound);
      m, M`congruence_group := IndexInSaturation(Q1 cat Q2, Bound);
   end if;
   return M`congruence_group;
end intrinsic;


intrinsic IntersectionGroup(M1::ModSym, M2::ModSym) -> GrpAb
{An abelian group G that encodes information about the intersection of the
 complex tori corresponding to M1 and M2. 
 When the intersection group is finite, it 
 is isomorphic to this intersection.}
   return IntersectionGroup([M1,M2]);
end intrinsic;


intrinsic IntersectionGroup(S::SeqEnum) -> GrpAb
{An abelian group G that encodes information about the intersection of the
 collection of complex tori corresponding to the sequence S of spaces of 
 modular symbols.  When G is finite, G is isomorphic to this intersection.}
   if #S eq 0 then 
      return AbelianGroup([]);
   end if;
   M := AmbientSpace(S[1]);
   for i in [2..#S] do 
      require AmbientSpace(S[i]) eq M : "Elements of argument 1 must have the same root.";
   end for;

   
   L  := IntegralRepresentation(M);

   n  := #S;
   m  := Degree(L);
   Z  := RModule(Integers(),m);
   
   ZS0:= [Basis(IntegralRepresentation(S[i])) : i in [1..n]];
   ZS := [[Z|Coordinates(L,b) : b in B] : B in ZS0];
   
   ///////////////////////////////////////////////////////////////////
   // Fill up a matrix D with generators for the image of the map //
   //      f: B_1 + ... + B_n --> Z^m + ... + Z^m                   //
   // given by                                                      //
   //      f(x_1,...,x_n) = (x_1-x_2, x_2-x_3, ..., x_{n-1}-x_n).   //
   ///////////////////////////////////////////////////////////////////
   D  := RMatrixSpace(Integers(),&+[#ZS[i] : i in [1..n]], 
                                   (n-1)*m)!0;

   B := ZS[1]; 
   for i in [1..#B] do 
      for c in [1..m] do
         D[i,c] := B[i][c];
      end for;
   end for;
   s := #B+1;
   t := 0;

   for j in [2..#ZS-1] do
      B := ZS[j]; 
      for i in [1..#B] do 
         for c in [1..m] do
            D[s,t+c]   := -B[i][c];
            D[s,t+c+m] :=  B[i][c];          
         end for;
         s +:= 1;
      end for;
      t +:= m;
   end for;

   B := ZS[#ZS]; 
   for i in [1..#B] do 
      for c in [1..m] do
         D[s,t+c] := -B[i][c];
      end for;
      s +:= 1;
   end for;
   S := SmithForm(D);
   G := AbelianGroup([S[i,i] 
         : i in [1..Min(Nrows(S),Ncols(S))] | S[i,i] ne 1]);
   return G;
end intrinsic;

intrinsic HeckeEigenvalueRing(M::ModSym : Bound := -1) -> Rng, Map
{The order generated by the Fourier coefficients of one of the
q-expansions of a newform corresponding to the irreducible cuspidal
space M of modular symbols, along with a map from the ring containing
the coefficients of qExpansion(M) to this order.  If the optional
integer parameter Bound is set, then the order generated by at least
those T_n, with n <= Bound, is computed.}

   require BaseField(M) cmpeq RationalField() : 
                 "The base field of argument 1 must be RationalField().";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   require IsNew(M) : "Argument 1 must be new.";
   require IsIrreducible(M): "Argument 1 must irreducible.";

   if not assigned M`hecke_eigenvalue_ring or Bound ne -1 then
      if Bound eq -1 then
         Bound := HeckeBound(M);
      end if;
      if DimensionComplexTorus(M) eq 1 then 
         O := Integers();    
         M`hecke_eigenvalue_ring := 
               <O, hom<O->O | alpha :-> alpha>>;
      else
         K, phi := HeckeEigenvalueField(M);
         f := qEigenform(M,Bound+1);
         O := Order([phi(Coefficient(f,n)) : n in [2..Bound]]);
         psi := hom<Domain(phi)->O | alpha :-> O!phi(alpha)>;
         if Bound ge HeckeBound(M) then  
            // save for next time only if full order.
            M`hecke_eigenvalue_ring := <O, psi>;
         else
            return O, psi;
         end if;
      end if;
   end if;
   return Explode(M`hecke_eigenvalue_ring);
end intrinsic;


intrinsic HeckeEigenvalueField(M::ModSym) -> Fld, Map
{The number field generated by the Fourier coefficients of one
of the q-expansions of a newform corresponding to the irreducible cuspidal
space M, along with a map from the ring containing the coefficients 
of qExpansion(M) to the field.}

   require Type(BaseField(M)) eq FldRat:
              "The base field of argument 1 must be RationalField().";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   require IsIrreducible(M): "Argument 1 must irreducible.";
   require IsNew(M) : "Argument 1 must be new.";

   if not assigned M`hecke_eigenvalue_field then
      if DimensionComplexTorus(M) eq 1 then 
         M`hecke_eigenvalue_field := <Rationals(), 
                      hom<Rationals()->Rationals() | alpha:->alpha>>;
      else
         a1 := Coefficient(qEigenform(M,3),1);
         F  := Parent(a1);
	 if ISA(Type(F), FldNum) then
	     K := F;
	     psi := Coercion(K, K);
	 else
	     R  := PreimageRing(F);
	     K  := NumberField(Modulus(F) : Check := false);
	     psi:= hom<F->K | K.1>;
	 end if;
         M`hecke_eigenvalue_field := <K, psi> ;
         //M`hecke_eigenvalue_field := <K, hom<F->K | alpha :-> K!phi(R!alpha)>;
      end if;
   end if;
   return Explode(M`hecke_eigenvalue_field);
end intrinsic;

/***********************
Here is how to write a more enhanced version:


function HeckeField(A)
   B := BaseField(A);
   assert Characteristic(B) eq 0;
   if Type(B) eq FldCyc and Degree(B) eq 1 then  
      // program around bug in MAGMA; NumberField(CyclotomicField(1)) fails.
      K := RationalField();
      phi := map<B->K | a :-> a>;
   else
      K, phi := NumberField(B);
   end if;

   f := qEigenform(A,1);    // this won't work unless A is simple!
   L := BaseRing(Parent(f));
   if L cmpeq B then
      return K;
   end if;
   g := Modulus(L);
   R := PolynomialRing(K); x := R.1;
   phi_of_g := &+[phi(Coefficient(g,n))*x^n : n in [0..Degree(g)]];
   KL := ext<K|phi_of_g>;
   return AbsoluteField(KL);

end function;

***************/



/*************************************************************
           Rational parts of L-functions
 *************************************************************/
function PeriodImage(A, W) 
// Returns the lattice spanned by the basis of W under the 
// period map defined by A.

   assert Type(A) eq ModSym;
   assert Type(W) eq Lat;

   if Dimension(W) eq 0 then
      return VectorSpaceWithBasis([DualRepresentation(A)|]);
   end if;
   n := #Eltseq(Basis(DualRepresentation(A))[1]);
   V := VectorSpace(Rationals(), n);
   basisW := [V!b : b in Basis(W)];

   Phi  := RMatrixSpace(Rationals(), Dimension(A), n)!Basis(DualRepresentation(A));
   MatW := Transpose(RMatrixSpace(Rationals(), #basisW, n)!basisW);
   PhiW := Transpose(Phi*MatW);
   if PhiW eq 0 then
      return RowSpace(PhiW);
   end if;
   return Lattice(PhiW);
end function;
                            
                            
function PeriodIndex(A, W, Plus) 
   assert Type(A) eq ModSym;
   assert Type(W) eq Lat;
 /* Compute "[Phi(SkZ)^+:Phi(W)]".  If Plus is false, compute
    instead "[Phi(SkZ)^-:Phi(W)]".  It should be the case 
    that W tensor Q is contained in SkZ^+ tensor Q (or SkZ^- 
    tensor Q, when Plus is false). */

   if Dimension(W) eq 0 then
      return Rationals()!0;
   end if;
   phi    := RationalMapping(A);
   phiW   := MakeLattice([phi(x) : x in Basis(W)]);
    // this next step is the part that takes most of the time,
    // probably because it requires computing an integral
    // basis of modular symbols for the ambient space.
   phiSkZ := RationalPeriodLattice(A);
   C := RationalPeriodConjugation(A);  // matrix of conjugation on Phi(SkZ).
   T := C + (Plus select -1 else +1);
   T := MatrixAlgebra(IntegerRing(),Degree(Parent(T)))!Eltseq(T);
/*
   K := Kernel(T);
   B := [Eltseq(x) : x in Basis(K)];
   LC := LinearCombinations(B, Basis(phiSkZ));
   PhiSkZsign := MakeLattice(LC);
*/
   K := KernelMatrix(T);
   R := BaseRing(phiSkZ);
   LC := ChangeRing(K,R) * BasisMatrix(phiSkZ);
   PhiSkZsign := Lattice(LC);
   
   return LatticeIndex(PhiSkZsign, phiW);
end function;


intrinsic TwistedWindingElement(M::ModSym, i::RngIntElt, eps::GrpDrchElt) -> ModSymElt
{The element sum_\{a in (Z/mZ)^*\} <eps(a)*X^(i-1)*Y^(k-2-i-1)*\{0,a/m\}>.}

   require BaseField(M) cmpeq BaseRing(eps) : 
        "The base field of argument 1 must equal the base field of argument 3.";

   require i ge 1 and i le Weight(M)-1 : "Argument 2 must lie between 1 and k-1, inclusive, where k is the weight of argument 1.";

   if IsTrivial(eps) then
      return WindingElement(M,i);
   end if;

   M := AmbientSpace(M);
   R<X,Y> := PolynomialRing(BaseField(M),2);
   i := i-1;
   e := M!0;
   m := Modulus(eps);
   for a in [n : n in [1..m-1] | GCD(n,m) eq 1] do
      e +:= Evaluate(eps,a)*M!<X^i*Y^(Weight(M)-2-i),[0,a/m]>;   
   end for;
   return e;
end intrinsic;


intrinsic WindingElement(M::ModSym) -> ModSymElt
{The winding element \{0,oo\}.}
   return WindingElement(M,1);
end intrinsic;


intrinsic WindingElement(M::ModSym, i::RngIntElt) -> ModSymElt
{The winding element X^(i-1)*Y^(k-2-(i-1))*\{0,oo\}.}
   require i ge 1 and i le Weight(M)-1 : "Argument 2 must lie between 1 and k-1, inclusive, where k is the weight of argument 1.";
   M := AmbientSpace(M);
   R<X,Y> := PolynomialRing(BaseField(M),2);
   i := i-1;
   return ConvFromModularSymbol(M,<X^i*Y^(Weight(M)-2-i),[[0,1],[1,0]]>);
end intrinsic;


intrinsic WindingElementProjection(M::ModSym) -> ModTupFld
{The image under RationalMapping(M) of \{0,oo\}.}
   return WindingElementProjection(M,1);
end intrinsic;


intrinsic WindingElementProjection(M::ModSym, i::RngIntElt) -> ModTupFld
{The image under RationalMapping(M) of the ith winding element
X^(i-1)*Y^(k-2-(i-1))*\{0,oo\}.}
   require i ge 1 and i le Weight(M)-1 : 
                "Argument 2 must lie between 1 and k-1, inclusive, where k is the weight of argument 1.";
   V := VectorSpace(AmbientSpace(M));
   winding := V!Eltseq(WindingElement(AmbientSpace(M),i));
   phi := RationalPeriodMapping(M);
   return phi(winding);
end intrinsic;


intrinsic WindingLattice(M::ModSym, j::RngIntElt : 
               Bound := -1)  -> Lat
{The image under RationalMapping(M) of the lattice generated by
the images of the jth winding element under all Hecke operators T_n.  
If M is the ambient space, then the image under RationalMapping(M) 
is not taken.}

   require j ge 1 and j le Weight(M)-1 : "Argument 2 must lie between 1 and k-1, inclusive, where k is the weight of argument 1.";
   require Type(BaseField(M)) eq FldRat : "Argument 1 must be the rational field.";

   if not assigned M`winding then
      M`winding := Seqlist([0 : i in [1..Weight(M)-1]]);
   end if;

   if Type(M`winding[j]) eq RngIntElt then     
      L := HeckeSpan(WindingElement(M,j) : Bound := Bound);
      if not IsAmbientSpace(M) then  // apply period mapping
         B := Basis(L);
         phi := RationalPeriodMapping(M);
         L := MakeLattice([phi(b) : b in B]);
      end if;
      if Bound eq -1 then
         M`winding[j] := L;
      else
         return L;
      end if;
   end if;

   return M`winding[j];

end intrinsic;


/*intrinsic XXX_WindingSubmodule(M::ModSym, j::RngIntElt 
                          : Bound := -1)  -> ModTupFld
{The image under RationalMapping(M) of the vector space generated by
 all images of WindingElement(M,j)
 under all Hecke operators T_n.  If M is the ambient space, then the 
 image under the rational period mapping is not taken.}
   require j ge 1 and j le Weight(M)-1 : 
     "Argument 2 must lie between 1 and k-1, inclusive, where k is the weight of argument 1.";
   if not assigned M`winding then
      M`winding := Seqlist([0 : i in [1..Weight(M)-1]]);
   end if;
   if Type(M`winding[j]) eq RngIntElt then     
      M`winding[j] := HeckeFieldSpan(WindingElement(M,j) : Bound := Bound);
      if not IsAmbientSpace(M) then  // apply period mapping
         B := Basis(M`winding[j]);
         phi := RationalPeriodMapping(M);
         M`winding[j] := sub<Codomain(phi) | [phi(b) : b in B]>;
      end if;
   end if;
   return M`winding[j];
end intrinsic;
*/

intrinsic WindingSubmodule(M::ModSym 
                          : Bound := -1)  -> ModTupFld
{The projection onto M of the vector space generated by all
images of WindingElement(AmbientSpace(M),j), under all Hecke 
operators T_n. (If not given, j=1)}
   return WindingSubmodule(M,1);
end intrinsic;

intrinsic WindingSubmodule(M::ModSym, j::RngIntElt 
                          : Bound := -1)  -> ModTupFld
{"} // "
   require j ge 1 and j le Weight(M)-1 : 
     "Argument 2 must lie between 1 and k-1, inclusive, where k is the weight of argument 1.";
   if not assigned M`winding then
      M`winding := Seqlist([0 : i in [1..Weight(M)-1]]);
   end if;
   if Type(M`winding[j]) eq RngIntElt then
      // IDEA for later: should do better caching.
      M`winding[j] := HeckeFieldSpan(WindingElement(M,j) : Bound := Bound);
      if not IsAmbientSpace(M) then  // apply projection map
         B := Basis(M`winding[j]);
         phi := ProjectionMatrix(M);
         V := VectorSpace(M);
         W := sub<V | [b*phi : b in B]>;
         M`winding[j] := VectorSpaceWithBasis(Basis(W));
      end if;
   end if;
   return M`winding[j];
end intrinsic;


function TwistedWindingSubmodule_helper(M, j, eps) 
   assert j ge 1 and j le Weight(M)-1; // : "Argument 2 must lie between 1 and k-1, inclusive, where k is the weight of argument 1.";
   assert IsAmbientSpace(M);

   vprint ModularSymbols, 2 : "Computing twisted winding submodule.";
   e := TwistedWindingElement(M,j,eps);
   W := HeckeFieldSpan(e);
   return W;
end function;


intrinsic TwistedWindingSubmodule(M::ModSym, j::RngIntElt, eps::GrpDrchElt) -> ModTupFld
{The Hecke submodule of the vector space Phi(M) generated by the image of the jth eps-twisted
modular winding element, where Phi is RationalMapping(M).  
This module is useful, for example, because in characteristic 0, if
M is new of weight 2, has sign +1 or -1, and corresponds to 
a collection \{f_i\} of Galois-conjugate 
newforms, then the dimension of the twisted winding submodule equals the 
cardinality of the subset of those f_i such that L(f_i,eps,1) =/= 0.}

   require BaseRing(eps) cmpeq BaseField(M) : "The base fields of arguments 1 and 3 must be equal.";

   B := Basis(TwistedWindingSubmodule_helper(AmbientSpace(M),j,eps));
   phi := RationalPeriodMapping(M);
   im := sub<Codomain(phi) | [phi(b) : b in B]>;

   return im;
end intrinsic;


intrinsic LRatio(A::ModSym, j::RngIntElt 
                  : Bound := -1) -> FldRatElt
{The rational number L(A,j)*(j-1)! / ((2pi)^(j-1)*Omega), where j is a
 "critical integer", so 1<=j<=k-1, and
 Omega is the volume of A(R) when j is odd, and the 
 volume of the -1 eigenspace for conjugation when j is even.
 The volume is computed with respect to a saturated basis of cusp forms
 that have integral Fourier coefficients at infinity.
 If the optional parameter Bound is set, then the result
 is a divisibility upper bound on the above rational number.
 If Sign(A) is not 0, then the answer is only correct up to
 a power of 2.}

   /* require Sign(A) eq 0:
       "The sign of argument 1 must be 0.  (Use LRatioOddPart instead.)";
   */

   if Dimension(A) eq 0 then
      return 1;    
   end if;
   require 1 le j and j le (Weight(A)-1) : 
        "Argument 2 must be a critical integer, i.e., an integer between 1 and k-1, inclusive, where k is the weight of argument 1.";
   require BaseField(A) cmpeq RationalField() :
        "The base field of argument 1 must be RationalField().";
   require IsCuspidal(A) :
        "Argument 1 must be cuspidal.";

   if Sign(A) eq +1 then
      require IsOdd(j) :
        "The sign of argument 1 is +1, so it is only possible to compute L(A,j) for j odd.";
   elif Sign(A) eq -1 then
      require IsEven(j) :
        "The sign of argument 1 is -1, so it is only possible to compute L(A,j) for j even.";
   end if;

   M := AmbientSpace(A);

   if not assigned A`L_ratios then
      A`L_ratios := [Rationals()!-1 : i in [1..M`k-1]];
   end if;
   if A`L_ratios[j] eq -1 then
      k := Weight(A);
      // the following expression evaluates to true <==> we take
      // the image of the + part instead of the 
      // image of the - part of SkZ.
      is_plus_image := (IsOdd(j) and IsEven(k)) or (IsEven(j) and IsOdd(k));

      W := WindingLattice(M,j : Bound := Bound);
      if Rank(W) eq 0 then
         return 0;
      end if;
      Lrat := PeriodIndex(A,W,is_plus_image);

      if Sign(A) eq 0 then
         if is_plus_image then
     	    Lrat /:= RealTamagawaNumber(A);
         else
            Lrat /:= MinusTamagawaNumber(A);
         end if;
      end if;

      if Bound eq -1 then
         A`L_ratios[j] := Lrat;
      else
         return Lrat;
      end if;     
   end if;
   return A`L_ratios[j];
end intrinsic;


intrinsic LRatioOddPart(M::ModSym, j::RngIntElt : Bound := -1) -> FldRatElt
{The odd part of the rational number LRatio(M,j).
The algorithm used by LRatioOddPart may be more efficient than 
the one used by LRatio.}

   if Sign(M) eq 1 then
      require IsOdd(j) : "The sign of argument 1 is +1, so argument 2 must be odd.";
   end if;
   if Sign(M) eq -1 then
      require IsEven(j) : "The sign of argument 1 is -1, so argument 2 must be even.";
   end if;
   
   s := j;   // so it's j in the signature.
  /**********************************************************************
     Let e=e_s = -X^(s-1)Y^(k-2-s+1){0,\infty}
     Let v be the dual eigenvector with sign (-1)^(s-1).

     If <v,e> = 0, the BSD value is 0 and we are done
     so assume <v,e> =/= 0.
     
     This function computes

             Norm(<v,e>)
         ------------------ * [Z[x]:Z[alp]]
               Vol(L) plus or minus

     where L is the lattice generated by the row vectors
           (<c,v_1>,<c,v_2>,...,<c,v_n>)
     Here v = v_1 + x*v_2 + x^2*v_3 + ... + x^{n-1}*v_n, x a root of f(x),
     and c varies through enough modular symbols to generate H_1(X_0(N),Z).

     Notice that Norm(<v,e>) depends only on f and the parity of s, and
     [Z[x]:Z[alp]] depends only on f.  Thus for all but two values of
     k we need only compute Norm(<v,e>). 
     ************************************************************************/

   require 1 le s and s le (Weight(M)-1) : 
         "Argument 2 must be a critical integer, i.e., an integer between 1 and k-1, inclusive, where k is the weight of argument 1.";
   require BaseField(M) cmpeq RationalField() :
        "The base field of argument 1 must be RationalField().";
   require IsCuspidal(M): "Argument 1 must be cuspidal.";
   if Sign(M) eq +1 then
      require IsOdd(j) :
        "The sign of argument 1 is +1, so it is only possible to compute L(M,j) for j odd.";
   elif Sign(M) eq -1 then
      require IsEven(j) :
        "The sign of argument 1 is -1, so it is only possible to compute L(M,j) for j even.";
   end if;


   MM := AmbientSpace(M);
   if not assigned M`L_ratios_odd then
      M`L_ratios_odd := [BaseField(M)|-1 : i in [1..Weight(M)-1]];
   end if;
   if M`L_ratios_odd[s] eq -1 then
      eig  := EigenvectorModSymSign(M,
                 IsEven(Weight(M)) select
                    (-1)^(s-1) 
                 else
                    (-1)^s
               );
      if eig cmpeq false then
         require false : "Argument 1 must be associated to a single Galois conjugacy class of eigenforms.";
      end if;
      w    := Representation(WindingElement(MM,s));
      eigw := 0;
      for i in [1..Degree(eig)] do
         if w[i] ne 0 then
            eigw +:= w[i]*eig[i] ; 
         end if;
      end for;

      if eigw eq 0 then
         M`L_ratios_odd[s] := 0 ;
      else
         if Type(eigw) eq FldRatElt then
            Nrm := Abs(eigw);
         else
            Nrm := Abs(NormPolResElt(eigw));   // this is a number in the base field.
         end if;
         if Type(MM`F) ne FldRat then
            M`L_ratios_odd[s] := Nrm;
            if IsVerbose("ModularSymbols") then
               print "LRatio: Base field not the rationals, so L-value only computed up to =/= 0 scalar.";
            end if;
            return Nrm;
         end if;
         // Q = R/g, where R=F[x]. 
         Q := Parent(eig[1]);
         if Type(Q) eq FldRat then
            M`ZxZalp := 1;
            n        := 1;
            vi       := [eig];
            V        := VectorSpace(Rationals(), n);
         else 
            g        := Modulus(Q);
            n        := Degree(g);
            V        := VectorSpace(Rationals(), n);
            R        := PreimageRing(Q);
            if not assigned M`ZxZalp then
               sturm    := Bound eq -1 select HeckeBound(MM) else Bound;
               f        := qEigenform(M,sturm+1);   
               M`ZxZalp := Volume([ V![Coefficient(h,i): i in [0..n-1]]
                            where h is R!Coefficient(f,j) : j in [1..sturm]]);
            end if;
            // the ith entry of vi is the coefficient of x^(i-1). 
            vi := [[Coefficient(R!eig[j],i) : j in [1..Degree(eig)]] :
                      i in [0..n-1]];
         end if;                 
         if s mod 2 eq 0 then
            if not assigned M`VolLEven then
               Z := Basis(IntegralRepresentation(CuspidalSubspace(MM)));
               M`VolLEven := Volume([V| [DotProd(z,vi[i]) : i in [1..n]] : 
                                 z in Z]);
            end if;
            VolL := M`VolLEven;
         else
            if not assigned M`VolLOdd then
               Z := Basis(IntegralRepresentation(CuspidalSubspace(MM)));
               M`VolLOdd := Volume([V| [DotProd(z,vi[i]) : i in [1..n]] :  
                                   z in Z]);
            end if;
            VolL := M`VolLOdd;
         end if;
         M`L_ratios_odd[s] := Nrm * M`ZxZalp / VolL;
      end if;
   end if;
   M`L_ratios_odd[s] := OddPart(M`L_ratios_odd[s]);
   return M`L_ratios_odd[s];
end intrinsic;

/*
intrinsic pMaximalDiscriminantOfHeckeAlgebra(M::ModSym, p::RngIntElt) 
                -> RngIntElt, SeqEnum
{p-valuation of the discriminant of the normalization of the Hecke
algebra associated to the cuspidal space M.  Also the sorted lists
of p-valuations for each newform factor of M.  We assume that M is cuspidal
and the level of M is cube free and, when the weight is > 2, that
T_p is semisimple.}

   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   require Max([F[2] : F in Factorization(Level(M))]) le 2 : 
     "The level of argument 1 must be cube free.";
   require IsPrime(p) : "Argument 2 must be prime.";
   D := SortDecomposition(NewformDecomposition(M));
   ans := [];
   for A in D do
      B := AssociatedNewSpace(A);
      K := HeckeEigenvalueField(B);
      if Type(K) eq FldRat then 
         d := 0;
      else
         O := Order([K.1]);
         Op := pMaximalOrder(O,p);
         d := Valuation(Discriminant(Op),p);
         d := d*#Divisors(Level(A) div Level(B));
      end if;
      Append(~ans, d);
   end for;
   return &*ans, ans;
end intrinsic;


intrinsic pIndexInNormalizationOfHeckeAlgebra(M::ModSym, p::RngIntElt) 
                   -> RngIntElt, RngIntElt
{The valuation at p of the index of the Hecke algebra T of M in 
its normalization S, along with the valuation at p of the discriminant
of S.}
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   require Max([F[2] : F in Factorization(Level(M))]) le 2 : 
     "The level of argument 1 must be cube free.";
   require IsPrime(p) : "Argument 2 must be prime.";
   max := pMaximalDiscriminantOfHeckeAlgebra(M, p);
   dis := Valuation(DiscriminantOfHeckeAlgebra(M),p);
   a := dis - max;
   if not IsEven(a) then
      error "There is a bug somewhere.  It occurs in pIndexInNormalizationOfHeckeAlgebra(M,p) with M = ", M, " and p = ", p;
   end if;
   return a div 2, max;
end intrinsic;
*/

intrinsic HeckeAlgebraFields(M::ModSym) -> SeqEnum
{A sequence of fields K_i such that the quotient of the Hecke algebra
of M tensor Q is isomorphic to the product of the K_i.  We assume that
M is cuspidal, defined over Q, and that the level of M is square
free. The fields are in the order of 
SortDecomposition(NewformDecomposition(M)).}
   require Type(BaseField(M)) eq FldRat:
              "The base field of argument 1 must be RationalField().";
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   require SquarefreeFactorization(Level(M)) eq Level(M) :  
              "The level of argument 1 must be square free.";
   require Sign(M) ne 0 : "Argument 1 must have nonzero sign.";

   if HasAssociatedNewSpace(M) then

      k := Weight(M);
      B := AssociatedNewSpace(M);
      N := Level(M);
      L := Level(B);
      K, phi := HeckeEigenvalueField(B);      
      if N eq L then
         return [* K *];
      end if;
      // Compute the extension of K generated Sqrt(a_p^2 - 4*p^(k-1))
      // for each p dividing N/L.
      P := [F[1] : F in Factorization(N div L)];
      f := qEigenform(B,Max(P)+1);
      for p in P do
         ap := K!phi(Coefficient(f,p));  // element of K.
         w  := ap^2 - 4*p^(k-1);
         if not IsSquare(w) then
            R := PolynomialRing(K); x := R.1;
            g := x^2 - w;
            K := NumberField(g);
         end if;      
      end for;
      return [*AbsoluteField(K)*] ;
   end if;

   // RECURSION to get full answer!
   // HasAssociatedNewSpace(A) is true for each A in newdecomp, so
   // this won't lead to an infinite recursion.
   ans := [* *];
   for A in SortDecomposition(NewformDecomposition(M)) do
      for K in HeckeAlgebraFields(A) do
         Append(~ans, K);
      end for;
   end for;
   return ans;
end intrinsic;

