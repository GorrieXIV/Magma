freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                                                                            
   Author: First version by David Kohel;
           Greatly re-written and extended by William A. Stein
           Later modified by Steve Donnelly

   FILE: dirichlet.m (Dirichlet characters)                

   This is a change log.  For further details see the bottom of this file.

   2011-11   (Steve) 
             BaseRing and Modulus now stored on elements, for quicker access

   2009-05   (Steve)
             Reorganised 'eq' to save time (important cases first).
             Also changed IsTrivial.

             Now cache DecompositionParents, so don't create fresh on every 
             call to Decomposition.  

   2009-04   (Steve)
             Rewrote Conductor -- see comment there.

             Made changes so that in a GrpDrch G, when an element of G is created 
             it is stored in G`EltArray, and when that element is needed again 
             the stored copy is returned instead of creating a new copy.  
             (This avoids recomputation of attributes such as Conductor.)

             Also don't list out G`PowersOfRoot when G`OrderOfRoot is too large;
             provided alternative code in each place where G`PowersOfRoot are used.

   2009-03   (Steve) 
             Changed Exponent to be the exponent of the given group, not of (Z/N)^*.

   2007-08   (Steve)
             Changed GaloisConjugacyRepresentatives so it gets rid of repeats.

   2007-08   (Steve) 
             Reinstated DirichletCharacterFromValuesOnUnitGenerators as an intrinsic. 
             The function that does the work (and returns, rather than throws, any error) 
             is now called DirichletCharacterFromValuesOnUnitGenerators_internal.

   2007-07   (Steve) Added OrderOfRootOfUnity (as an intrinsic taking a general RngElt)
             and use it in the function OrderOfZeta.

   2007-06   (Steve) Changed '*' so that the result takes values in rationals
             when the arguments do (instead of a stupid FldCyc of order 1 or 2)
             I'm relying on UGroup and UnitsMap always being assigned in this way: 
                 G`UGroup, G`UnitsMap := UnitGroup(quo< Integers() | m>);

             Also made MinimalBaseRingCharacter, given a character of order 2 
             over a FldCyc, return a character over the rationals.

   2007-02-27: (Steve) Fixed a tricky bug in AbelianGroup. 
               The Invariants of a GrpAb are not necessarily the orders
               of its standard generators. Before the fix, this failed:
               > chi := KroneckerCharacter(35);
               > A,fromA := AbelianGroup(Parent(chi));
               > chi @@ fromA;

   2007-01-07: (Steve) Change KroneckerCharacter so if its given a non-fundamental
               discriminant it just deals with it instead of complaining.
                 
   2004-10-05: Fixed intrinsic 'eq' (G::GrpDrch,H::GrpDrch) -> BoolElt
   by comparing actual base rings instead of just their types, which makes
   more sense.

   08/15/03: (WAS) Fixed bad error messages when coercing (stack traces when
             there should be stack traces -- see end of this file.)

   08/14/03: (WAS) Add FullDirichletGroup intrinsic, as requested by Kevin Buzzard.

   02/23/03: (WAS) Added proper error checking to coercision of sequence 
             into Dirichlet Group element

   02/15/03: (WAS) Fixed some bugs with BaseExtend when the root of unity
             suddenly gets smaller.  Hopefully this makes sense.

   02/06/03: (WAS) Fixed some bugs (i.e., spurious require statement, missing coercision) 
             that appeared when user tries to create Dirichlet characters over number fields.

   11/17/02: (WAS) Fixed two bugs that Allan Steel found.  Bug 1 involved confusing a character
             and the character modulo its conductor which induces it.  The second was a special
             case in which the universe of the empty sequence wasn't defined. 
             

   10/31/02: (WAS) **MASSIVE CHANGES**  Totally changed the internal representation, which
             meant rewriting almost every command.

   10/31/02: I'm sick of RCS.  I'm not using it anymore.

   $Header: /home/was/magma/packages/ModSym/code/RCS/dirichlet.m,v 1.17 2002/09/27 19:36:16 was Exp was $ 
   $Log: dirichlet.m,v $
   Revision 1.17  2002/09/27 19:36:16  was
   finished fixing my fix.

   Revision 1.16  2002/09/27 19:35:12  was
   Replaced David's "elementary bug fix" by
         when FldCyc :
            return R!(CyclotomicField(LCM(2,r)).1), LCM(2,r);

   Revision 1.15  2002/09/26 19:35:27  was
   Improved comment in BaseExtend and fixed bug in equality test (before it didn't
   test that roots of unity are equal.)

   Revision 1.14  2002/05/06 05:10:57  was
   Fixed a problem with equality testing that appeared because, I guess,
   of a change in how abelian groups are handled by Magma V2.9.

   Revision 1.13  2001/11/20 18:02:54  was
   Speed up GaloisConjugacyRepresentatives

   Revision 1.12  2001/11/20 17:48:37  was
   nothing!

   Revision 1.11  2001/09/03 23:24:35  was
   nothing.

   Revision 1.10  2001/08/07 03:13:29  was
   Changed a require statement in DirichletGroup.

   Revision 1.9  2001/05/22 07:49:09  was
   Added AssociatedPrimitiveCharacter.

   Revision 1.8  2001/05/22 05:48:45  was
   Added IsPrimitive.

   Revision 1.7  2001/05/21 10:30:43  was
   *** empty log message ***

   Revision 1.6  2001/05/21 10:01:12  was
   Added intrinsic MinimalBaseRingCharacter(eps::GrpDrchElt) -> GrpDrchElt

   Revision 1.5  2001/05/18 04:40:52  was
   Made ValueList an intrinsic.

   Revision 1.4  2001/05/17 22:21:55  was
   Added
     GaloisConjugacyRepresentatives(S::[GrpDrchElt]) -> SeqEnum
   and
     AbelianGroup(G::GrpDrch) -> GrpAb, Map
   -- William

   Revision 1.3  2001/05/16 03:16:09  was
   Slight change to comment of '*'.

   Revision 1.2  2001/04/29 02:47:27  was
   Default Kronecker character is over the integers now.

   Revision 1.1  2001/04/20 04:46:56  was
   Initial revision

   Revision 1.15  2001/03/27 07:27:40  was
   Added a "KroneckerCharacter" intrinsic, which gives the popular Kronecker character as a
   DirichletGroup element.

   Revision 1.14  2001/02/24 04:35:32  was
   Strengthened error checking.

   Revision 1.13  2001/02/05 14:50:42  was
   Removed a require "Type(R) in " statement, so that my cusp forms with dirichlet
   character over Zp code would work.

   Revision 1.12  2001/02/05 13:58:12  was
   Fixed typo in a comment.

   Revision 1.11  2001/02/04 16:42:15  was
   Removed the Type(R) requirement from BaseExtend.

   Revision 1.10  2001/02/04 15:42:57  was
   Added uses of "ReductionMap".

   Revision 1.9  2001/02/04 15:18:33  was
   Added

      intrinsic DistinguishedRoot(G::GrpDrch) -> RngElt, RngIntElt

   Revision 1.8  2001/02/03 19:49:46  was
   Deleted a commented-out require statement.

   Revision 1.7  2000/09/01 17:08:43  was
   William,

   Here are corrections to a couple of elementary bugs in
   dirichlet.m.  First the universe needs to be defined in
   this line to avoid empty sequence bugs.

      G`Orders   := [ Integers() | GCD(r,Order(A.i)) : i in [1..Ngens(A)]];

   and the even-odd orders have to be differentiated for
   cyclotomic fields.

         when FldCyc :
            r := CyclotomicOrder(R);
            if r mod 2 eq 0 then
               return R.1, r;
            else
               return -R.1, 2*r;
            end if;

   --David

   Revision 1.6  2000/06/22 00:43:44  was
   Added BaseExtend for maps.

   Revision 1.5  2000/06/14 19:43:51  was
   Allow general DirichletGroup in general constructor; also, fixed a bug in the error message for
   DirichletGroup(m,R).

   Revision 1.4  2000/06/03 04:57:31  was
   commented out IsOdd

   Revision 1.3  2000/05/25 21:54:31  was
   fixed "IsEven" "IsOdd" comments

   Revision 1.2  2000/05/25 21:49:15  was
   added comment.

   Revision 1.1  2000/05/02 08:00:37  was
   Initial revision

                                                                            
 ***************************************************************************/


import "arith.m": ReductionMap;

forward DirichletCharacterFromValuesOnUnitGenerators_internal,
        initGrpDrchElt ;

////////////////////////////////////////////////////////////////
//                                                            //
//                  Attribute declarations                    //
//                                                            // 
////////////////////////////////////////////////////////////////


declare type GrpDrch [GrpDrchElt];

declare attributes GrpDrch:  // Call this GrpDrch object G.
   BaseRing,      // The base ring R over which the characters are defined
   RootOf1,       // A root of unity z in R^*
   PowersOfRoot,  // [z,z^2,z^3,...,z^r], where z has order r.
   OrderOfRoot,   // r = Order of z, where z is RootOf1.
   Modulus,       // The modulus N
   Exponent,      // Exponent of the group (Z/N)^*
   UGroup,        // A group such that 
   UnitsMap,      //    UnitsMap:  A -> (Z/N)^* is an isomorphism
   Elements,      // Sequence of all elements of G.
   OrdersUGroup,  // The orders of the standard generators of (Z/N)^*
   OrdersGens,    // Orders of the generators of G.
   Images,        // Images of the chosen generators of G; these are powers of z.
   Labels,        // Labels of the standard generators
   AbGrp,         // An abelian group isomorphic to this Dirichlet group,
                  // so AbGrp is the r-torsion in UGroup.
   AbGrpMap,      // Invertible homomorphism AbGrp ----> G.
   EltArray,      // Associative array indexed by G`AbGrp storing elements of G. (Added April 2009, SRD)
   NF, Pairing, Residue_map, Zeta,
   DecompositionParents, // list, used in Decomposition
   ValsAtMinus1;  // Sequence of values at -1 of the generators of the *full* group of the same modulus

declare type GrpDrchElt;

declare attributes GrpDrchElt: 
   Parent,
   BaseRing,      // = x`Parent`BaseRing
   Modulus,       // = x`Parent`Modulus
   Conductor,     // Smallest M such that (Z/N)^* --> R^* factors through (Z/M)^*.
   Element,       // Corresponding element of (Z/N)^* (see comments far below),
                  // which represents this Dirichlet group element.
   ValueList,     // [Evaluate(eps,i) : i in [1..m]];   (useful sometimes for efficiency).
   GaussSum;      



////////////////////////////////////////////////////////////////
//                   Creation functions                       // 
////////////////////////////////////////////////////////////////

function _TorsionUnitGroup(R, m)

  if ISA(Type(R), RngOrd) or ISA(Type(R), FldOrd) then
    F := NumberField(R);
    A, Amap := TorsionUnitGroup(F, m);
    return A, Amap * Coercion(R, F);
  end if;

  if m eq 1 then
    n := 1;
    z := R!1;
  elif Type(R) eq FldCyc then
    // easy case
    mm := CyclotomicOrder(R);
    n := GCD(m, mm);
    z := R.1^(mm div n);
    if IsOdd(mm) and IsEven(m) then
      z := -z;
    end if;
  else
    // recurse to prime powers
    fact := Factorization(m);
    if #fact gt 1 then
      orders := [];
      roots := [];
      for tup in fact do
        q := tup[1]^tup[2];
        Aq, Aqmap := TorsionUnitGroup(R, q);
        Append(~orders, #Aq);
        Append(~roots, Aq.1@Aqmap);
      end for;
      // combine to get a primitive root
      n := &*orders;
      z := &*roots;
    else // m is a prime power
      if IsOdd(m) then
        n := 1;
        z := R!1;
      else
        n := 2;
        z := R!-1;
      end if;
      if Type(R) notin {RngInt, FldRat} and IsTotallyComplex(R) then
        // take successive pth roots in R
        // TO DO: HasRoot should check finite fields first
        // TO DO: if passes finite field test, for large p just call TorsionUnitGroup(R)
        p := fact[1][1];
        Pol := PolynomialRing(R);
        while n lt m and IsDivisibleBy(AbsoluteDegree(R), EulerPhi(n*p)) do   
          pol := (z eq 1) select Pol! CyclotomicPolynomial(p)
                           else  Pol.1^p - z;
          bool, zz := HasRoot(pol); 
          if bool then
            n *:= p;
            z := zz;
          else 
            break;
          end if;
        end while;
      end if;
    end if;
  end if;

//assert m mod n eq 0 and z^n eq 1; 
//assert &and[ z^(n div p) ne 1 : p in PrimeDivisors(n)];

  A := AbelianGroup([n]);
  Amap := map< A -> R | a :-> z^Eltseq(a)[1] >;
  return A, Amap;
end function;

intrinsic TorsionUnitGroup(R::RngInt, m::RngIntElt) -> GrpAb, Map
{The m-torsion subgroup of the unit group of the ring R} 
   return _TorsionUnitGroup(R, m);
end intrinsic;

intrinsic TorsionUnitGroup(R::FldRat, m::RngIntElt) -> GrpAb, Map {"}//"
   return _TorsionUnitGroup(R, m);
end intrinsic;

intrinsic TorsionUnitGroup(R::RngOrd, m::RngIntElt) -> GrpAb, Map {"}//"
   return _TorsionUnitGroup(R, m);
end intrinsic;

intrinsic TorsionUnitGroup(R::FldAlg, m::RngIntElt) -> GrpAb, Map {"}//"
   return _TorsionUnitGroup(R, m);
end intrinsic;

function CyclotomicGenerator(R, m)
   case Category(R) :
      when RngInt :
         return R!-1, 2;
      when FldRat :
         return R!-1, 2;
      when FldCyc :
         r := CyclotomicOrder(R);
         return R!(CyclotomicField(LCM(2,r)).1), LCM(2,r);
      when FldFin :
         r := #R - 1;
         G, f := UnitGroup(R);
         z := f(G.1); // TO DO: Teichmueller convention
         return z,r;
      when FldQuad :
         case Discriminant(R):
            when -4:
               r := 4;
               z := R.1;
            when -3:
               r := 6;
               z := (1+R.1)/2;
            else:
               r := 2;
               z := R!-1;
         end case;         
         return z,r;
      when FldNum :
         G, f := TorsionUnitGroup(R, m);
         z := R!f(G.1);
         return z,Order(G);
      else
         if Characteristic(R) ne 2 then
            return R!-1,2;
         else
            return R!1,1;
         end if;
   end case;
end function;

function powers_of_root(z, r);
  ans := [z];
  for i := 2 to r do 
    zi := z*ans[i-1];
    Append(~ans, zi);
  end for;
  return ans;
end function;


intrinsic ValueList(eps::GrpDrchElt) -> SeqEnum
{[The values [eps(1), eps(2), ..., eps(N)], where N is the modulus.}
   if not assigned eps`ValueList then
      eps`ValueList := [Evaluate(eps,i) : i in [1..eps`Modulus]];
   end if;
   return eps`ValueList;
end intrinsic;


intrinsic DirichletGroup(m::RngIntElt) -> GrpDrch
   {The group of Dirichlet characters mod m with image 
    in RationalField(). This is a group of exponent at most 2.}
   requirege m,1;
   return DirichletGroup(m,RationalField());
end intrinsic;


intrinsic DirichletGroup(m::RngIntElt,R::Rng) -> GrpDrch
   {The group of Dirichlet characters mod m with image in the ring R.}
   require Type(R) in {RngInt, FldRat, FldCyc, FldFin, FldQuad, FldNum} :
       "Argument 2 must be of type RngInt, FldRat, FldCyc, FldFin, FldQuad, or FldNum.";
   requirege m,1;

   e := Exponent(UnitGroup(quo<Integers()|m>));
   z, r := CyclotomicGenerator(R,e);
   return DirichletGroup(m,R,z,r);
end intrinsic


intrinsic DirichletGroup(m::RngIntElt,R::Rng,z::RngElt,r::RngIntElt) -> GrpDrch
{The group of Dirichlet characters mod m with image in the order-r cyclic
 subgroup of R generated by the root of unity z.}
   // not a thorough check, but fast enough...
   require m ge 1 : "Argument 1 must be at least 1."; 
   require R cmpeq Parent(z) and z in R : "Argument 3 must lie in argument 2.";
   if not (Type(R) in {FldPad, FldCom, FldRe}) then
      require z^r eq R!1 : "Argument 3 must have order equal to argument 4.";  
   end if;

   G          := New(GrpDrch);
   G`Modulus  := m;
   G`BaseRing := R;
   G`UGroup, G`UnitsMap := UnitGroup(quo< Integers() | m>);
   G`RootOf1  := z;
   G`OrderOfRoot := r;
   if r le 1000 then
     G`PowersOfRoot := powers_of_root(z, r); end if;
   G`Exponent := Exponent(G`UGroup);
   G`OrdersUGroup := [ Order(G`UnitsMap(x)) : x in [G`UGroup.i : i in [1..Ngens(G`UGroup)]]];
   G`OrdersGens := [Integers()| GCD(r,x) : x in G`OrdersUGroup];
   G`AbGrp    := AbelianGroup(G`OrdersGens);
   G`EltArray := AssociativeArray(G`AbGrp);
   G`Labels   := ["$." cat IntegerToString(i) : i in [1..#G`OrdersUGroup] ];
   return G;
end intrinsic;

intrinsic DirichletGroupCopy(G::GrpDrch) -> GrpDrch
{Clone G}
// Only copies non-optional attributes.
// In particular, MUST not copy things like G`Elements!
   GG          := New(GrpDrch);
   GG`Modulus  := G`Modulus;
   GG`BaseRing := G`BaseRing;
   GG`UGroup   := G`UGroup;
   GG`UnitsMap := G`UnitsMap;
   GG`RootOf1  := G`RootOf1;
   GG`OrderOfRoot := G`OrderOfRoot;
   if assigned G`PowersOfRoot then GG`PowersOfRoot := G`PowersOfRoot; end if;
   GG`Exponent := G`Exponent;
   GG`OrdersUGroup := G`OrdersUGroup;
   GG`OrdersGens := G`OrdersGens;
   GG`AbGrp    := G`AbGrp;
   GG`EltArray := AssociativeArray(GG`AbGrp);
   GG`Labels   := G`Labels;
   return GG;
end intrinsic;

intrinsic DirichletGroupFull(N::RngIntElt) -> GrpDrch
{Same as FullDirichletGroup}
   return FullDirichletGroup(N);
end intrinsic;

intrinsic FullDirichletGroup(N::RngIntElt) -> GrpDrch
{The group of Dirichlet characters modulo N with values in Q(zeta_m), where
m is the exponent of (Z/N)^*.}
   requirege N, 1;
   mu := Exponent(UnitGroup(Integers(N)));
   if mu gt 2 then
      return DirichletGroup(N,CyclotomicField(mu));
   else
      return DirichletGroup(N);   
   end if;
end intrinsic;


intrinsic AbelianGroup(G::GrpDrch) -> GrpAb, Map
{An abstract abelian group A isomorphic to G, and a map A -> G}
   assert assigned G`AbGrp; // now assigned when G is created
   if not assigned G`AbGrpMap then
      r := G`OrderOfRoot;
      I := G`OrdersUGroup;
      gens := [Integers()| x div GCD(r,x) : x in I];
      assert &and [I[i] eq Order(G`AbGrp.i)*gens[i] : i in [1..#I]];
      function f(x) 
         e := Eltseq(x);
         e := [Integers()| e[i]*gens[i] : i in [1..#I]];
         g := G`UGroup!e;
         return initGrpDrchElt(G, g);
      end function;
      function g(x)
         e := Eltseq(x); 
         e := [Integers()| e[i]/gens[i] : i in [1..#I]];
         return G`AbGrp!e;
      end function;
      G`AbGrpMap := hom<G`AbGrp -> G | x :-> f(x), y :-> g(y)>;
   end if;
   return G`AbGrp, G`AbGrpMap;
end intrinsic;

// TO DO: rewrite Elements, now that we have G`EltArray

intrinsic Elements(G::GrpDrch) -> SeqEnum
   {The Dirichlet characters in G.}
   if not assigned G`Elements then
      chars := [ G!1 ];
      for i in [1..Ngens(G)] do
         chrsi := [ Gi^j : j in [0..Order(Gi)-1] ] where Gi is G.i;
         chars := [ x*y : x in chars, y in chrsi ];
      end for;
      G`Elements := chars;
   end if;
   return G`Elements;
end intrinsic;


intrinsic Random(G::GrpDrch) -> GrpDrchElt
   {A random element of G.}

   oU := G`OrdersUGroup;
   oG := G`OrdersGens;
   return G ! [Integers()| 
          (oU[i] div oG[i]) * Random(oG[i]-1) : i in [1..#oG]];
end intrinsic;


////////////////////////////////////////////////////////////////
//                                                            //
//                     Coercions                              //
//                                                            // 
////////////////////////////////////////////////////////////////


/* Elements of GrpDrch are represented as elements of (Z/N)^*,
   since there is an isomorphism between Hom((Z/N)^*, C^*) and (Z/N)^*.
   Let r be the order of the distinguished root z of unity.   We
   are interested in the subgroup of Hom((Z/N)^*, C^*) of elements
   of order dividing r.  This corresponds to the subgroup of (Z/N)^* of
   elements of order dividing r.   Suppose x in (Z/N)^* has order 
   dividing r.   Write x = prod g_i^m_i, where the g_i are fixed (once
   and for all) generators for (Z/N)^*.  Then x corresponds to the
   homomorphism which sends g_i to (z^(r/order(g_i)))^m_i.  In particular,
   the element g_i of (Z/N)^* corresponds to the homomorphism that sends
   g_j to 1 for all i=/=j and sends g_i to z^(r/order(g_i)).
 */

// The element in G`GrpAb corresponding to the element x in G with Eltseq(x) = g.
function toAbGrp(G, g) 
  A := G`AbGrp;
  I := G`OrdersUGroup;
  J := G`OrdersGens;
  a := [Integers()| g[i] div (I[i] div J[i]) : i in [1..#I]];
  return A!a;
end function;

// Changed (April 2009, SRD) to retrieve stored elements instead of initializing a new copy
// TO DO: we might not always want to store elements when #G is large
function initGrpDrchElt(G, g)
  a := toAbGrp(G, Eltseq(g));
  if not IsDefined(G`EltArray, a) then 
    x := New(GrpDrchElt);  
    x`Parent := G;
    x`BaseRing := G`BaseRing;
    x`Modulus := G`Modulus;
    x`Element := g;
    G`EltArray[a] := x;
  end if;
  return G`EltArray[a]; 
end function;


intrinsic IsCoercible(G::GrpDrch,x::.) -> BoolElt, GrpDrchElt
{}
   if Type(x) eq GrpDrchElt then
      if IsIdentical(x`Parent, G) then
         return true, x;
      elif x`Parent eq G then
         xG := G! Eltseq(x`Element);
         return true, xG;
      else
         if Modulus(G) mod Conductor(x) ne 0 then
            return false, "Invalid coercion: The given character has too large conductor";  
         end if;
         s := [];
         for g in UnitGenerators(G) do // We have to do this since GCD(g,Modulus(x)) > 1 then Eval(x,g)=0.
                                       // which is wrong. remember, we are trying to evaluate the character
                                       // modulo Conductor(x) that *induces* x, not x itself.
            h := g;
            while GCD(h,x`Modulus) ne 1 do
               h +:= Conductor(x);
            end while;
            Append(~s, Evaluate(x,h));
         end for;
         t,msg,eps := DirichletCharacterFromValuesOnUnitGenerators_internal(G,s);
         if not t then
           /* Attempt to give more informative error stymied because 
              MinimalBaseRingCharacter throws error if not over FldRat or FldCyc
           if Degree(BaseRing(MinimalBaseRingCharacter(x))) gt Degree(BaseRing(G)) then
             return false, "Invalid coercion: The values of the character are not in the coefficient ring of the group";
           end if;
           */ 
           if #msg ge 72 and msg[1..72] eq "Argument 2 must be a sequence of elements in the base ring of argument 1" then
             return false, "Invalid coercion: The values of the character are not in the coefficient ring of the group";
           end if;
           return false, "Invalid coercion"; 
         else
           return true, eps;
         end if;
      end if;
   elif Type(x) eq RngIntElt and x eq 1 then
      return true, initGrpDrchElt(G,G`UGroup!0); 
   elif Type(x) eq SeqEnum and (#x eq 0 or Type(Universe(x)) eq RngInt) and #x eq Ngens(G) then
      for i in [1..Ngens(G)] do
         m := G`OrdersUGroup[i];
         g := GCD(G`OrderOfRoot,m);
         if g*x[i] mod m ne 0 then
            return false, "Invalid coercion: The sequence does not define a valid Dirichlet character (over the given base ring).";
         end if;
      end for;
      return true, initGrpDrchElt(G,G`UGroup!x); 
   end if;
   return false, "Invalid coercion.";
end intrinsic;

intrinsic NumberOfNames(G::GrpDrch) -> RngIntElt {}
 return Ngens(G); end intrinsic;

intrinsic AssignNames(~G::GrpDrch, S::[MonStgElt])
{Assign names to the generators of G.}
   require #S eq Ngens(G) : "Argument 2 must have length", Ngens(G);
   G`Labels := S;
end intrinsic;

intrinsic Name(G::GrpDrch,i::RngIntElt) -> GrpDrchElt
   {The ith generator.}
   require i ge 0 : "Argument 2 must be nonnegative";
   require i le Ngens(G) : "Argument 2 can be at most", Ngens(G);
   return G.i;
end intrinsic;


intrinsic '.'(G::GrpDrch,i::RngIntElt) -> GrpDrchElt
   {The ith generator.}
   require i ge 0 : "Argument 2 must be nonnegative";
   require i le Ngens(G) :  "Argument 2 can be at most", Ngens(G);
   S := [ Integers() | 0 : i in [1..Ngens(G)] ]; 
   if i eq 0 then return G!S; end if;
   m := G`OrdersUGroup[i];
   r := G`OrderOfRoot;
   S[i] := Integers()!(m/GCD(r,m));
   return G!S;
end intrinsic;


////////////////////////////////////////////////////////////////
//                     Printing                               //
////////////////////////////////////////////////////////////////

intrinsic Print(X::GrpDrch, level::MonStgElt)
   {}
   printf "Group of Dirichlet characters of modulus %o over %o", 
          X`Modulus, X`BaseRing;
end intrinsic;


intrinsic Print(x::GrpDrchElt, level::MonStgElt)
   {}
   G := x`Parent;
   r := G`OrderOfRoot;
   S := Eltseq(x`Element);
   Star := "";
   if &and[ x eq 0 : x in S ] then printf IntegerToString(1); return; end if;
   if Order(x) eq 2 then m:=IdentifyKroneckerCharacter(x);
      printf "Kronecker character %o",m; return; end if;
   for i in [1..Ngens(G)] do
	 a := S[i];
         m := G`OrdersUGroup[i];
         w := (GCD(r,m)*a/m);
         e := Integers()!w mod G`OrdersGens[i];
         if e eq 1 then 
	    printf Star cat G`Labels[i];
            Star := "*";
         elif e ne 0 then
            printf Star cat G`Labels[i] cat 
                   "^" cat IntegerToString(e); 
            Star := "*";
         end if; 
      end for;
end intrinsic;



////////////////////////////////////////////////////////////////
//                                                            //
//            Membership and equality testing                 //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic 'in'(x::., X::GrpDrch) -> BoolElt
   {Returns true if x is in X.}
   if Type(x) eq GrpDrchElt then
      return x`Parent eq X;
   end if;
   return false;
end intrinsic;


intrinsic Parent(x::GrpDrchElt) -> GrpDrch
   {}
   return x`Parent;
end intrinsic;


intrinsic 'eq' (G::GrpDrch,H::GrpDrch) -> BoolElt
  {True iff the given groups of Dirichlet characters are functionally the same}
   return IsIdentical(G,H) or 
          G`Modulus eq H`Modulus and G`BaseRing cmpeq H`BaseRing
                                 and G`RootOf1 cmpeq H`RootOf1;
end intrinsic;

intrinsic 'eq' (x::GrpDrchElt,y::GrpDrchElt) -> BoolElt
   {True iff the given Dirichlet characters have the same modulus and values}
   Gx := x`Parent;
   Gy := y`Parent;
   // test the more frequent cases first
   if IsIdentical(Gx, Gy) then
      return x`Element eq y`Element; 
   elif Gx eq Gy then 
      return Eltseq(x`Element) eq Eltseq(y`Element); 
   elif Gx`Modulus ne Gy`Modulus then 
      return false;   // not sure why we want to do this
   else
      return ValuesOnUnitGenerators(x) cmpeq ValuesOnUnitGenerators(y);
   end if;
end intrinsic;


////////////////////////////////////////////////////////////////
//                                                            //
//                Attribute Access Functions                  //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic BaseRing(G::GrpDrch) -> Rng
   {The base ring of G.}
   return G`BaseRing;
end intrinsic;


intrinsic BaseRing(x::GrpDrchElt) -> Rng
   {The base ring, i.e. the codomain, of x.}
   return x`BaseRing;
end intrinsic;


intrinsic Domain(x::GrpDrchElt) -> Rng
   {The integers.}
   return Integers();
end intrinsic;


intrinsic Codomain(x::GrpDrchElt) -> Rng
{The coefficient ring in which x takes values.}
   return x`BaseRing;
end intrinsic;


intrinsic Exponent(G::GrpDrch) -> RngIntElt
{The exponent of G.}
  //return G`Exponent; // = exponent of (Z/N)^*
  return LCM(G`OrdersGens);
end intrinsic;


intrinsic Order(G::GrpDrch) -> RngIntElt
{The order of G.}
   return &*G`OrdersGens;
end intrinsic;

intrinsic '#'(G::GrpDrch) -> RngIntElt
{The order of G.}
   return Order(G);
end intrinsic;

intrinsic Order(x::GrpDrchElt) -> RngIntElt
{The order of x.}
   return Order(x`Element);
end intrinsic;


intrinsic Generators(G::GrpDrch) -> SeqEnum
{A sequence containing the generators for G}
   return [ G.i : i in [1..Ngens(G)] ];
end intrinsic;

intrinsic GeneratorsSequence(G::GrpDrch) -> SeqEnum
{"} // "
   return [ G.i : i in [1..Ngens(G)] ];
end intrinsic;


intrinsic UnitGenerators(G::GrpDrch) -> SeqEnum
{The ordered sequence of integers that reduce to 
 "canonical" generators of (Z/m)^*, where m is the modulus of G.}
   return [Integers()| G`UnitsMap(G`UGroup.i) : 
                   i in [1..Ngens(G`UGroup)]] ;
end intrinsic;


intrinsic NumberOfGenerators(G::GrpDrch) -> RngIntElt
   {The number of generators for G.}
   return #G`Labels;
end intrinsic;


intrinsic Modulus(G::GrpDrch) -> RngIntElt
   {The modulus of the group G of Dirichlet characters.}
   return G`Modulus;
end intrinsic;

intrinsic Modulus(x::GrpDrchElt) -> RngIntElt
   {The modulus of the Dirichlet character x.}
   return x`Modulus;
end intrinsic;


// Conductor rewritten April 2009, Steve Donnelly

// Note: this relies on conventions regarding the generators U.i of
// U = UnitGroup(Integers(M)) ... so if that changes, this will break.

intrinsic Conductor(x::GrpDrchElt) -> RngIntElt
   {The conductor of the Dirichlet character x.}

   if assigned x`Conductor then return x`Conductor; end if;

   M := Modulus(x);
   N := 1;
   xx := Eltseq(x`Element); 
   if M gt 1 and not &and [xi eq 0 : xi in xx] then
      // when M is even, (1+offset) = number of slots in xx devoted to p=2
      if M mod 4 eq 2 then
        offset := -1; 
      elif M mod 8 eq 0 then 
        offset := 1;
      else
        offset := 0;
      end if;
      fact := Factorization(M);
      assert #xx eq #fact + offset;
      for i := 1 to #fact do 
         p, e := Explode(fact[i]); 
         if p eq 2 then 
            if e eq 2 then
               if IsOdd(xx[1]) then  
                  N *:= 4;
               end if;
            elif e gt 2 then
               x2 := xx[2]; 
               assert x2 eq x2 mod 2^(e-2);
               if x2 ne 0 then 
                  v := Valuation(x2, 2); // v < e-2
                  N *:= 2^(e-v);
               elif IsOdd(xx[1]) then
                  N *:= 4;
               end if;
            end if;
         else // odd p 
            xi := xx[i+offset]; 
            assert xi eq xi mod ((p-1)*p^(e-1));
            if xi ne 0 then
               v := Valuation(xi, p); // v < e
               N *:= p^(e-v);
            end if;
         end if;
      end for;
   end if;
 //assert M mod N eq 0;
 //assert N eq ConductorOld(x); 
   x`Conductor := N;
   return N;
end intrinsic;
     
// This was an ***unbelievably slow way*** because Decomposition takes
// so long to initialize the parent DirichletGroups for the components
/*
intrinsic ConductorOld(x::GrpDrchElt) -> RngIntElt
   {Determines Conductor(x) in an absurdly inefficient way}
   if not assigned x`Conductor then
      M := Modulus(x);
      if M eq 1 or Order(x) eq 1 then
         x`Conductor := 1;
         return 1;
      end if;
      F := Factorization(M);
      if #F gt 1 then
         x`Conductor := 1;
         D := Decomposition(x);
         for d in D do
            x`Conductor *:= Conductor(d);
         end for;
         return x`Conductor;
      end if;
      p := F[1][1];
      // When p is odd, and x =/= 1, the conductor is the smallest p^r such that
      //   Order(x) divides EulerPhi(p^r) = p^(r-1)*(p-1).
      // For a given r, whether or not the above divisiblity holds
      // depends only on the factor of p^(r-1) on the right hand side.
      // Since p-1 is coprime to p, this smallest r such that the
      // divisibility holds equals Valuation(Order(x),p)+1. 
      x`Conductor := p^(Valuation(Order(x),p)+1);    
      if p eq 2 and F[1][2] gt 2 and Eltseq(x`Element)[2] ne 0 then
         x`Conductor *:= 2;
      end if;
   end if;
   return x`Conductor;
end intrinsic;
*/


////////////////////////////////////////////////////////////////
//         Functionality, arithmetic operations, etc.         //
////////////////////////////////////////////////////////////////

intrinsic IsIdentity(chi::GrpDrchElt) -> BoolElt
{True iff chi is the trivial character}
   return IsIdentity(chi`Element);
end intrinsic;

intrinsic IsTrivial(chi::GrpDrchElt) -> BoolElt
{"} // "
   return IsIdentity(chi`Element);
end intrinsic;

intrinsic IsEven(chi::GrpDrchElt) -> BoolElt
{True iff the Dirichlet character chi satisfies chi(-1) = 1}
   return Evaluate(chi,-1) eq 1;
end intrinsic;

intrinsic IsOdd(chi::GrpDrchElt) -> BoolElt
{True iff the Dirichlet character chi satisfies chi(-1) = -1}
   return Evaluate(chi,-1) eq -1;
end intrinsic;

intrinsic IsTotallyEven(chi::GrpDrchElt) -> BoolElt
{For a Dirichlet character chi, this is true iff 
every character in Decomposition(chi) is even.}
   return &and[ IsEven(chi_p) : chi_p in Decomposition(chi)];
end intrinsic;

intrinsic IsPrimitive(x::GrpDrchElt) -> BoolElt
  {True iff the conductor equals the modulus}
   return Modulus(x) eq Conductor(x);
end intrinsic;

intrinsic AssociatedPrimitiveCharacter(x::GrpDrchElt) -> GrpDrchElt
  {The corresponding character on Z/N where N is the conductor of x}
   return Restrict(x,Conductor(x));
end intrinsic;

function Evaluate_helper(x, n_rep)
   assert Type(x) eq GrpDrchElt;
   assert Type(n_rep) eq SeqEnum;
   G     := x`Parent;
   x_rep := Eltseq(x`Element); 
   assert #n_rep eq #x_rep;
   ords  := G`OrdersUGroup;
   r     := G`OrderOfRoot;
   power_of_root := &+[Integers()| n_rep[i]*x_rep[i]*r/ords[i] : i in [1..#n_rep]] mod r;
   if power_of_root eq 0 then
      power_of_root := r;
   end if;
   return assigned G`PowersOfRoot select G`PowersOfRoot[power_of_root]
                                   else  G`RootOf1^power_of_root;
end function;

intrinsic Evaluate(x::GrpDrchElt,n::RngIntElt) -> RngElt
{The evaluation of x at n.}

   bool, V := HasAttribute(x, "ValueList");
   if bool then
      n := (n-1) mod x`Modulus + 1;
      return V[n]; 
   end if;

   G := x`Parent;
   N := G`Modulus;
   if GCD(N,n) ne 1 then
      return 0;
   elif n mod N eq 1 then
      return BaseRing(G)! 1;
   elif n mod N eq N-1 then 
      if not assigned G`ValsAtMinus1 then 
         // precompute chi(-1) for generators of the *full* group mod N (so IsEven/IsOdd is virtually free on G)
         f     := G`UnitsMap;
         ZmodN := Codomain(f);
         n_rep := Eltseq((ZmodN!n)@@f);   // discrete log
         G`ValsAtMinus1 := [BaseRing(G) | (n_rep[i] eq 0) select 1 else -1 : i in [1..#G`Labels]];
      end if;
      return &*[BaseRing(G) | G`ValsAtMinus1[i] : i in [1..#xx] | IsOdd(xx[i])] where xx is Eltseq(x);
   end if;
   f     := G`UnitsMap;
   ZmodN := Codomain(f);
   n_rep := Eltseq((ZmodN!n)@@f);   // discrete log 
   return Evaluate_helper(x, n_rep);
end intrinsic;


intrinsic Evaluate(x::GrpDrchElt,n::RngIntResElt) -> RngElt
{Evaluation x(n).}
   return Evaluate(x, Integers()!n);
end intrinsic;

intrinsic '@'(n::RngIntElt, x::GrpDrchElt) -> RngElt
{"} // "
   return Evaluate(x,n);
end intrinsic;

intrinsic '@'(n::RngIntResElt, x::GrpDrchElt) -> RngElt
{"} // "
   return Evaluate(x,n);
end intrinsic;

intrinsic '*' (x::GrpDrchElt,y::GrpDrchElt) -> GrpDrchElt
{The product of x and y.  This is a Dirichlet character
of modulus equal to the least common multiple of the moduli of x
and y.  If the parents of x and y are not equal, then the product
lies in a new Dirichlet group.  If the base rings or roots are not 
equal then the base ring has to be cyclotomic.}
   Gx := x`Parent;
   Gy := y`Parent;

   if Gx eq Gy then
      if Parent(x`Element) cmpeq Parent(y`Element) then
         return initGrpDrchElt(Gx,x`Element+y`Element);
      end if;
      xe := Eltseq(x);
      ye := Eltseq(y);
      assert #xe eq #ye;
      return Gx![xe[i] + ye[i] : i in [1..#xe]];
   end if;

   // Construct new parent. 
   N := LCM(x`Modulus, y`Modulus);
   if BaseRing(Gx) cmpeq BaseRing(Gy) and Gx`RootOf1 eq Gy`RootOf1 then
      G := DirichletGroup(N, BaseRing(Gx), Gx`RootOf1, Gx`OrderOfRoot);
   else
      base_types := {Type(BaseRing(Gx)), Type(BaseRing(Gy))};
      require base_types subset {FldRat, RngInt, FldCyc} : 
         "The base rings of the arguments must be the integers, rationals, or cyclotomic fields.";
      case base_types :
       when {RngInt} :
         K := Integers(); 
       when {FldRat}, {RngInt,FldRat} :
         K := Rationals();
       else :
         r := LCM(Gx`OrderOfRoot, Gy`OrderOfRoot);
         K := CyclotomicField(r);
      end case;
      G := DirichletGroup(N, K);
   end if;
   
   vals := [Evaluate(x,g)*Evaluate(y,g) : g in UnitGenerators(G)];
   t,msg,eps := DirichletCharacterFromValuesOnUnitGenerators_internal(G,vals);
   require t : msg;
   return eps;
end intrinsic;

intrinsic '/' (x::GrpDrchElt,y::GrpDrchElt) -> GrpDrchElt
{The quotient of x and y.  This is a Dirichlet character
of modulus equal to the least common multiple of the moduli of x
and y.  The base rings and chosen roots of unity of 
the parents of x and y must be equal.}
   return x * y^(-1);
end intrinsic;

intrinsic '^' (x::GrpDrchElt,n::RngIntElt) -> GrpDrchElt
   {The n-th power of the Dirichlet character x}
   if n eq 1 then 
      return x;
   end if; 
   return initGrpDrchElt(x`Parent, n*x`Element);
end intrinsic;

intrinsic Extend(x::GrpDrchElt, m::RngIntElt) -> GrpDrchElt
   {Extension of x to a Dirichlet character mod m.}
   require m mod Modulus(x) eq 0 : "Argument 2 must be divisible by the modulus of argument 1.";
   G := x`Parent;
   return Extend(x,DirichletGroup(m,BaseRing(G),G`RootOf1,G`OrderOfRoot));
end intrinsic;

intrinsic Extend(x::GrpDrchElt, H::GrpDrch) -> GrpDrchElt
{Extension of x to an element of H.}
   require (Modulus(H) mod Modulus(x)) eq 0: 
          "Modulus of argument 2 must be a multiple of the modulus of argument 1.";
   vals := [Evaluate(x,g) : g in UnitGenerators(H)];
   t,msg,eps := DirichletCharacterFromValuesOnUnitGenerators_internal(H,vals);
   require t : msg;
   return eps;
end intrinsic;


intrinsic Eltseq(x::GrpDrchElt) -> SeqEnum
{For internal use}
   return Eltseq(x`Element);
end intrinsic;


intrinsic Decomposition(x::GrpDrchElt) -> List
{Decomposition of x as a product of Dirichlet characters 
of prime power modulus.}
   
   G := x`Parent;
   e := Eltseq(x`Element);
   R := BaseRing(G);
   m := Modulus(G);
   r := G`OrderOfRoot;
   s := [m/GCD(r,m) : m in G`OrdersUGroup];
   F := Factorization(m);
   if not assigned G`DecompositionParents then
      G`DecompositionParents := 
             [* DirichletGroup(a[1]^a[2], R, G`RootOf1, G`OrderOfRoot) : a in F *];
   end if;
   Gps := G`DecompositionParents;
   D := [* *];
   i := 1; // keeps track of where we are in the eltseq e
   for j := 1 to #F do 
      a := F[j];
      Gp := Gps[j]; 
      if a[1] ne 2 then 
         xp := Gp.1^(Integers()!(e[i]/s[i]));
         i +:= 1;
      elif a[1] eq 2 then
         if a[2] eq 1 then
            xp := Gp!1;
         else
            pow := Integers()!(e[i]/s[i]);
            xp := Gp.1^pow;
            i +:= 1;
            if a[2] gt 2 then
               pow := Integers()!(e[i]/s[i]);
               xp := xp * Gp.2^(Integers()!pow);
               i +:= 1;
            end if;
         end if;
      end if;
      Append(~D,xp);
   end for;
   return D;
end intrinsic;


intrinsic Restrict(x::GrpDrchElt,m::RngIntElt) -> GrpDrchElt
 {The associated mod-m Dirichlet character. The conductor 
of x must divide m.}
   require (m mod Conductor(x)) eq 0: "Conductor of argument 1 does not divide argument 2.";
   require Modulus(x) mod m eq 0: "Argument 2 must divide the modulus of argument 1.";
   G := x`Parent;
   H := DirichletGroup(m,BaseRing(G),G`RootOf1,G`OrderOfRoot);
   return Restrict(x,H);
end intrinsic;

intrinsic Restrict(x::GrpDrchElt,H::GrpDrch) -> GrpDrchElt
{The associated Dirichlet character in H.}
   require (Modulus(H) mod Conductor(x)) eq 0: 
               "Conductor of first argument must divide modulus of second.";
   require Modulus(x) mod Modulus(H) eq 0: 
               "Modulus of argument 2 must divide the modulus of argument 1.";
   m := Modulus(H);
   n := Modulus(x);
   gens := UnitGenerators(H);   // These generate (Z/m)^*.  There a map (Z/n)^* --> (Z/m)^*
   // Now we lift these to elements of (Z/n)^*.
   for i in [1..#gens] do
      while GCD(n,gens[i]) ne 1 do
         gens[i] +:= m;
      end while;
   end for;
   vals := [Evaluate(x,g) : g in gens];
   t,msg,eps := DirichletCharacterFromValuesOnUnitGenerators_internal(H,vals);
   require t : msg;
   return eps;
end intrinsic;

intrinsic BaseExtend(G::GrpDrch, R::Rng) -> GrpDrch
{Base extension of G to R.}
   require Type(R) in {RngInt, FldRat, FldCyc, FldFin, FldQuad, FldNum} :
       "Argument 1 must be of type RngInt, FldRat, FldCyc, FldFin, FldQuad, or FldNum.";

   return BaseExtend(G, R, R!G`RootOf1);
end intrinsic;

intrinsic BaseExtend(G::GrpDrch, R::Rng, z::RngElt) -> GrpDrch
{Base extension of G to R that identifies the distinguished
root of unity of the base ring of G with z.}

   require z^G`OrderOfRoot eq 1 :
           "Invalid root of unity.  The order of argument 3 must divide the order of DistinguishedRoot(argument 1).";
   // the following might be *really* stupid if the order is 
   // divisible by several primes.
   n := Min([r : r in Divisors(G`OrderOfRoot) | z^r eq 1]);   
   //return DirichletGroup(Modulus(G), R, z, G`OrderOfRoot);  
   return DirichletGroup(Modulus(G), R, z, n);  
end intrinsic;


intrinsic BaseExtend(eps::GrpDrchElt, R::Rng) -> GrpDrchElt
{Base extension of eps to R.}
   phi := ReductionMap(BaseRing(Parent(eps)),R);
   return BaseExtend(eps, R, phi(Parent(eps)`RootOf1));
end intrinsic;


intrinsic BaseExtend(eps::GrpDrchElt, R::Rng, z::RngElt) -> GrpDrchElt
{Base extension of eps to R.}
   require z^Parent(eps)`OrderOfRoot eq 1 : "Invalid root of unity.";
   H := BaseExtend(Parent(eps),R,z);
   return H!eps;
end intrinsic;


intrinsic BaseExtend(G::GrpDrch, f::Map) -> GrpDrch
{Base extension of G to Codomain(f).}
   R := Codomain(f);
   z := f(G`RootOf1);
   require z^G`OrderOfRoot eq 1 : "Invalid map f.";
   return BaseExtend(G,R,z);
end intrinsic;


intrinsic BaseExtend(eps::GrpDrchElt, f::Map) -> GrpDrchElt
{Base extension of eps to Codomain(R).}
   H := BaseExtend(Parent(eps),f);
   return H!eps;
end intrinsic;

intrinsic DistinguishedRoot(G::GrpDrch) -> RngElt, RngIntElt
{The distinguished root of unity in the base ring of G and its order.}
   return G`RootOf1, G`OrderOfRoot;
end intrinsic;


intrinsic KroneckerCharacter(D::RngIntElt) -> GrpDrchElt
   {The Kronecker character (D'/n), where D' is the fundamental discriminant 
   associated to D}

   return KroneckerCharacter(D,IntegerRing());
end intrinsic;


intrinsic KroneckerCharacter(D::RngIntElt, R::Rng) -> GrpDrchElt
   {"} // "

   if IsSquare(D) then D := 1; 
   elif not IsFundamental(D) then D := FundamentalDiscriminant(D); end if;

   eps := DirichletGroup(1,R)!1;
   for factor in Factorization(D) do
      if not (factor[1] eq 2 and factor[2] le 2) then
         G := DirichletGroup(factor[1]^factor[2],R);
         chi := G.(2-(factor[1] mod 2));
         eps := eps*(chi^(Order(chi) div 2));
	 if factor[1] mod 4 eq 3 then
            D := -D; 
         end if;
      end if;
   end for;
   if D mod 4 eq 0 and D lt 0 then
      eps := eps*DirichletGroup(4,R).1;
   end if;
   return eps;
   
end intrinsic;

intrinsic GaloisConjugacyRepresentatives(G::GrpDrch) -> SeqEnum
{Representatives for the Gal(Qbar/Q)-conjugacy classes of G.}     
   require Type(BaseRing(G)) in {FldRat, FldCyc, FldNum} : 
             "The base ring of argument 1 must be a number field.";
   return GaloisConjugacyRepresentatives(Elements(G));
end intrinsic;


intrinsic GaloisConjugacyRepresentatives(S::[GrpDrchElt]) -> SeqEnum
{Representatives for the Gal(Qbar/Q)-conjugacy classes of Dirichlet characters 
 contained in the given sequence S}  
   
   G := Universe(S);

   if #S eq 0 or Type(BaseRing(G)) eq FldRat then 
     return S;
   end if;

   require ISA(Type(BaseRing(G)), FldAlg) :
          "The base ring of argument 1 must be a number field.";

   r, n := DistinguishedRoot(G);      
   i := 1;
   U := [k : k in [1..n-1] | GCD(k,n) eq 1]; // Steve changed this, was [2..n-1]
   while i lt #S do
      x := S[i];
      for m in U do
         y := x^m;
         R := [j : j in [i+1..#S] | S[j]`Element eq y`Element];
         for j in Reverse(R) do    // important to reverse.
            Remove(~S,j);
         end for;
      end for;
      i +:= 1;
   end while;
   return S;
end intrinsic;

intrinsic MinimalBaseRingCharacter(eps::GrpDrchElt) -> GrpDrchElt
   {Return an equivalent character, but defined over a base ring 
    that is generated by the values}
   F := BaseRing(eps);
   N := Modulus(eps);
   case Type(F):
      when FldRat:
         return eps;
      when FldFin:
         if IsPrime(#BaseRing(eps)) then
            return eps; 
         end if;
      when FldCyc:
         n := Order(eps);
         if n eq 1 then
            return DirichletGroup(N)!1;
         end if;
         if n gt 2 and EulerPhi(n) eq Degree(F) then
            return eps;
         else
            if n eq 2 then
               K := RationalField();
            else
               K := CyclotomicField(n);
            end if;
            G := DirichletGroup(N,K);
            return G!eps;
         end if;
   end case;   
   require false : "The base ring of argument 1 must be the Q, F_p, or cyclotomic.";
end intrinsic;

////////////////////// NEW STUFF //////////////////////////////////

intrinsic ValuesOnUnitGenerators(x::GrpDrchElt) -> SeqEnum
{The values of x on the ordered sequence generators of (Z/m)^*, where
 m is the modulus of x.}
   U := x`Parent`UGroup;
   gens :=  [U.i : i in [1..Ngens(U)]];
   return [Evaluate_helper(x, Eltseq(g)) : g in gens];
end intrinsic;

intrinsic DirichletCharacterFromValuesOnUnitGenerators(G::GrpDrch, v::SeqEnum) -> GrpDrchElt
{Creates a Dirichlet character belonging to G whose values on the chosen generators of (Z/m)^*
 match the given sequence v}
   bool, mess, chi := DirichletCharacterFromValuesOnUnitGenerators_internal(G, v);
   if bool then return chi;
   else error mess; end if;
end intrinsic;

function DirichletCharacterFromValuesOnUnitGenerators_internal(G, v)
// Return a boolean (success = true), an error message (success = ""), 
// and a DirichletCharacter on success or 0 on failure. 

   assert Type(G) eq GrpDrch;
   assert Type(v) eq SeqEnum;

   gens := UnitGenerators(G);
   if #gens ne #v then
      return false, 
     "Argument two must be a sequence of length equal to the number of 'canonical' generators of (Z/m)^*, where m is the modulus of G.",
      0;
   end if;
   if #v eq 0 then
      return true, "", G!1;
   end if;   
   if not IsCoercible(BaseRing(G), v[1]) then
      return false,
      "Argument 2 must be a sequence of elements in the base ring of argument 1.",
      0;
   end if;
   z, n := DistinguishedRoot(G);      
   if z eq 1 then
      assert n eq 1;
      return true, "", G!1;
   end if;
   for x in v do 
      if x^n ne 1 then 
         return false,
          "Each element of argument 2 must have order dividing the"*
         " order of the chosen distinguished root of unity in the base ring of argument 1.",
         0;
      end if;
   end for;
   
   // Find discrete logs of v :
   // I[i] = minimum power m of z such that z^m = v[i]
   z := G`RootOf1;
   r := G`OrderOfRoot;
   if assigned G`PowersOfRoot then 
     I := [Index(G`PowersOfRoot, a) : a in v]; 
   else
     R := Parent(z);
     if ISA(Type(R), FldFin) then
       I := [Log(z, R!x) mod r : x in v];
       assert forall{i : i in [1..#v] | z^I[i] eq v[i]};
     else
       // TO DO
       // some kind of discrete log code for roots of 1 in cyclotomic fields?
       // at least Pohlig-Hellman reduction to the prime case
       I := [a eq 1 select 0 else -1 : a in v];
       m := 1; 
       zm := z;
       while m lt r and -1 in I do
         for j := 1 to #v do 
           if v[j] eq zm then 
             I[j] := m;
           end if;
         end for;
         m +:= 1; 
         zm *:= z;
       end while;
       assert -1 notin I;
     end if;
   end if;

   ords  := G`OrdersUGroup;
   elt   := [Integers() | I[i]*ords[i]/r : i in [1..#I]];
 
   return true, "", initGrpDrchElt(G, G`UGroup!elt);
end function;

intrinsic ApplyAutomorphism(x::GrpDrchElt, phi::.) -> GrpDrchElt
{Same as x^phi}
   t,msg,y := DirichletCharacterFromValuesOnUnitGenerators_internal(x`Parent, 
              [phi(z) : z in ValuesOnUnitGenerators(x)]); 
   require t : "Argument 2 must be an automorphism, and for some reason it didn't behave correctly ("*msg*")";
   return y;
end intrinsic;

intrinsic '^'(x::GrpDrchElt, phi::.) -> GrpDrchElt
{The image of the Dirichlet character x under the automorphism phi.}
   t,msg,y := DirichletCharacterFromValuesOnUnitGenerators_internal(x`Parent, 
              [phi(z) : z in ValuesOnUnitGenerators(x)]); 
   require t : "Argument 2 must be an automorphism, and for some reason it didn't behave correctly ("*msg*")";
   return y;
end intrinsic;

function OrderOfZeta(zeta)
   C := Parent(zeta);
   N := CyclotomicOrder(C);
   // Steve's new version (not tested!!)
   error if zeta^N ne 1, 
        "The given element 'zeta' does not seem to be a root of unity";
   return OrderOfRootOfUnity(zeta, N);
   // William's original
   for d in Sort(Divisors(N)) do
      if zeta^d eq 1 then
         return d;
      end if;
   end for;
   error "The given element 'zeta' does not seem to be a root of unity";
end function;

// Steve added this one
intrinsic OrderOfRootOfUnity(r::RngElt, n::RngIntElt) -> RngIntElt
{Given an element r of some ring, assumed to satisfy r^n = 1,
this returns the smallest integer m such that r^m = 1.}
   one := Parent(r)! 1;
   if n eq 1 or r eq one then
      return 1;
   elif n eq 2 or r eq -one then
      return 2;
   end if;
   p := Min(PrimeDivisors(n));
   nn := n div p;
   if r^nn eq one then
      return OrderOfRootOfUnity(r, nn);
   else
      return p*OrderOfRootOfUnity(r^p, nn);
   end if;
end intrinsic;

// find a square root of eps:
function RootOf1Sqrt(zeta)   
   // Given a root of unity zeta_n, with n odd, return one of the
   // two powers of -zeta_n that has square equal to zeta.
   // Let e be the multiplicative inverse of 2 modulo n.  Then
   // ((-zeta_n)^e)^2 = zeta_n, so this function should return 
   // the value (-zeta_n)^e.
   if zeta eq 1 then
      return -1;
   end if;
   e := Integers()!((Integers(OrderOfZeta(zeta))!2)^(-1));
   return (-zeta)^e;
end function;

intrinsic Sqrt(eps::GrpDrchElt) -> GrpDrchElt
{A square root of eps, where eps is a Dirichlet character of odd order.}
   require IsOdd(Order(eps)) : "Argument 1 must have odd order.";
   G := eps`Parent;
   v := ValuesOnUnitGenerators(eps);
   v := [RootOf1Sqrt(x) : x in v];
   t, msg, sqrt_eps := DirichletCharacterFromValuesOnUnitGenerators_internal(G, v);
   require t : msg;
   return sqrt_eps;   
end intrinsic;

