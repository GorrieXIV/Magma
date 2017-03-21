freeze;
 
/****-*-magma-* EXPORT DATE: 2004-10-24 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: creation.m

   2007-06 (Steve)    Allow coercion of Laurent series (with positive valution)
                      into modular forms
                      Coercion of a ModFrmElt into the 'same' space now
                      done by copying the element

   2007-05 (Steve)    Get coercion working properly for inexact base rings.

   2007-01, (Steve)   BaseExtend: don't leave the dimension of the parent
                      set to -1 (which it would be if this is called while 
                      computing the dimension of the original space). 
                      For example, here the EisensteinSeries are actually
                      constructed during (a call to Dimension inside) the
                      call to Basis:
                      > M:=ModularForms(DirichletGroup(24).3,15);
                      > b:=Basis(M);
                      > E:=EisensteinSeries(M);
                      > Parent(E[8]);

   2007-01 (Mark W)   Change coercion from series to forms so that an error
                      is returned if insufficient coefficients are given to
                      uniquely determine the form

   2004-10-24: (was)  Changed CoerceModFrmElt(M,x) so coercion
                      into the parent of an element is the identity:

   Revision 1.13  2002/09/12 15:13:41  was
   changed k to 2 in a comment.

   Revision 1.12  2002/09/11 18:18:07  was
   Changed back to keeping bad characters, so construction of zero space is possible.

   Revision 1.11  2002/09/11 18:12:09  was
   Throw out characters that don't satisfy eps(-1) = (-1)^k in modular forms constructor.

   Revision 1.10  2002/05/04 18:12:19  was
   Added CuspForms.

   Revision 1.9  2002/04/13 07:26:38  was
   *** empty log message ***

   Revision 1.8  2002/03/11 23:06:07  was
   improved intrinsic ModularForms(M::ModFrm, N::RngIntElt).

   Revision 1.7  2002/03/11 23:01:36  was
   Added intrinsic ModularForms(M::ModFrm, N::RngIntElt) -> ModFrm.

   Revision 1.6  2001/11/22 19:28:20  was
   Added some more constructors for "ModularForms".

   Revision 1.5  2001/05/30 18:54:19  was
   Created.

   Revision 1.4  2001/05/16 04:11:48  was
   *** empty log message ***

   Revision 1.3  2001/05/16 04:01:01  was
   *** empty log message ***

   Revision 1.2  2001/05/16 03:56:48  was
   *** empty log message ***

   Revision 1.1  2001/05/16 03:51:41  was
   Initial revision

      
 ***************************************************************************/

import "categories.m" : CopyOfModFrmElt;

import "predicates.m" : SpaceType,
                        SpaceTypeParam,
                        AssociatedSpaceOverZ;

import "q-expansions.m" : PowerSeriesInternal;

/* Looks like this never worked, since several attributes don't exist...
intrinsic ModularForms(R::Rng) -> ModFrm
{The space spanned by all modular forms of all weights over the ring R.}
   M := New(ModFrm);
   M`base_ring := R;
   M`is_complex := true;
   M`is_padic := false;
   M`is_modp := false;
   M`dimension := Infinity();
   M`type := "ring";
   return M;
end intrinsic;
*/

intrinsic ModularForms(N::RngIntElt) -> ModFrm
{Same as ModularForms(N,2)}
   require N ge 1: "The first argument must be at least 1.";
   return ModularForms(N,2);
end intrinsic; 

intrinsic ModularForms(N::RngIntElt, k::FldRatElt) -> ModFrm
{The space of weight k modular forms on Gamma_0(N) over the integers.}
   require N ge 1: "The level N must be at least 1.";
   if IsIntegral(k) and k ge 1 then 
      return ModularForms([DirichletGroup(N)!1], Integers()!k);
   elif IsIntegral(2*k) and k gt 0 then
      require N mod 4 eq 0 : 
        "The level must be a multiple of 4 for half-integral weight forms";
      return HalfIntegralWeightForms(N,k);
   else
      require false: "Invalid weight k given";
   end if;
end intrinsic;

intrinsic ModularForms(N::RngIntElt, k::RngIntElt) -> ModFrm
{"} // "
   require N ge 1: "The first argument must be at least 1.";
   requirege k,1;
   return ModularForms([DirichletGroup(N)!1], k);
end intrinsic;

function ModularFormsGamma1(N, k)
   assert Type(N) eq RngIntElt;
   assert Type(k) eq RngIntElt;
   M := New(ModFrm);
   M`base_ring := Integers();
   M`is_gamma1 := true;
   M`level := N;
   M`weight := k;
   M`type := "full";
   return M;
end function;

intrinsic ModularForms(G::GrpPSL2) -> ModFrm
{Same as  ModularForms(G,2)}
   require IsGamma1(G) or IsGamma0(G) : "Argument 1 must be Gamma_0(N) or Gamma_1(N).";
   return ModularForms(G,2);
end intrinsic;

intrinsic ModularForms(G::GrpPSL2, k::FldRatElt) -> ModFrm
{The space of weight k modular forms on G over the integers.}
   if IsIntegral(k) and k ge 1 then 
      return ModularForms(G, Integers()!k);
   elif IsIntegral(2*k) and k gt 0 then
      require Level(G) mod 4 eq 0 : 
        "The level must be a multiple of 4 for half-integral weight forms";
      return HalfIntegralWeightForms(G,k);
   else
      require false: "Invalid weight k given";
   end if;
end intrinsic;

intrinsic ModularForms(G::GrpPSL2, k::RngIntElt) -> ModFrm
{"} // "
   requirege k,1;
   if IsGamma1(G) then
      return ModularFormsGamma1(Level(G),k);
   elif IsGamma0(G) then
      return ModularForms(Level(G),k);
   else
      require false : "Argument 1 must be Gamma_0(N) or Gamma_1(N).";
   end if;
end intrinsic;

/*intrinsic ModularForms(eps::GrpDrchElt, k::RngIntElt) -> ModFrm
{The space M_k(N,eps) over Z.}
   require Type(BaseRing(Parent(eps))) in {FldCyc, FldRat} : 
       "The base ring of argument 1 must be the rationals or cyclotomic.";
   return ModularForms([eps],k); 
end intrinsic;
*/

intrinsic ModularForms(chars::[GrpDrchElt], k::RngIntElt) -> ModFrm
{The direct sum of the spaces ModularForms(eps,k), where eps runs through
 representatives of the Galois orbits of the characters in the
 sequence chars.}
   requirege k,1;
   require #chars gt 0 : "Argument 1 must have length at least 1.";
   t := Type(BaseRing(Parent(chars[1])));
   require t in {FldCyc, FldRat, RngInt} :
      "The base ring of the given character(s) must be the rationals or cyclotomic.";
   if t eq RngInt then
      chars := [BaseExtend(chi,Rationals()) : chi in chars]; end if;
   require Type(BaseRing(Parent(chars[1]))) in {FldCyc, FldRat} : 
      "The base ring of argument 1 must be the rationals or cyclotomic.";
   
   M := New(ModFrm);
   M`base_ring := Integers();
   M`dirichlet_character := GaloisConjugacyRepresentatives(chars);
   M`is_gamma1 := false;
   M`weight := k;
   M`type := "full";
   return M;
end intrinsic;

intrinsic ModularForms(chars::[GrpDrchElt]) -> ModFrm
{Same as ModularForms(chars,2)}
   require #chars gt 0 : "Argument 1 must have length at least 1.";
   return ModularForms(chars,2);
end intrinsic;

intrinsic ModularForms(eps::GrpDrchElt, k::FldRatElt) -> ModFrm
{The space of modular forms of weight k over the integers, which under base extension
becomes equal to the direct sum of the spaces M_k(eps'), where eps' runs over
all Galois conjugates of eps.}
   if IsIntegral(k) and k ge 1 then 
      return ModularForms([eps], Integers()!k);
   elif IsIntegral(2*k) and k gt 0 then
      require Modulus(eps) mod 4 eq 0: 
        "The level must be a multiple of 4 for half-integral weight forms";
      return HalfIntegralWeightForms(eps, k);
   else
      require false: "Invalid weight k given";
   end if; 
end intrinsic;

intrinsic ModularForms(eps::GrpDrchElt, k::RngIntElt) -> ModFrm
{"} // "
   requirege k,1;
   return ModularForms([eps],k);  
end intrinsic;

intrinsic ModularForms(eps::GrpDrchElt) -> ModFrm
{Same as ModularForms(eps,2)}
   return ModularForms([eps],2);  
end intrinsic;

// The following two intrinsic are cheats, because they don't
// have proper require statements. 
intrinsic CuspForms(x::.) -> ModFrm  
{Shorthand for CuspidalSubspace(ModularForms(x))}
   return CuspidalSubspace(ModularForms(x));
end intrinsic;

intrinsic CuspForms(x::., y::.) -> ModFrm
{Shorthand for CuspidalSubspace(ModularForms(x,y))}
   return CuspidalSubspace(ModularForms(x,y));
end intrinsic;

// Just copy the most very basic defining properties of M, not 
// things like hecke operators and so on. 
function CopyOfDefiningModularFormsObject(M)
   C := New(ModFrm);  // C for "copy"
   if assigned M`dimension then
      C`dimension := M`dimension;  
   end if;
   C`base_ring := BaseRing(M);
   C`level := Level(M);
   C`weight := Weight(M);
   C`type := SpaceType(M);
   C`type_param := SpaceTypeParam(M);
   C`is_gamma1 := IsGamma1(M);
   if assigned M`made_from_newform then
      C`made_from_newform := M`made_from_newform;
   end if;
   if assigned M`dirichlet_character then
      C`dirichlet_character := M`dirichlet_character;  
   end if;
   if assigned M`ambient_space then
      C`ambient_space := M`ambient_space;
   end if;
   if assigned M`associated_space_over_z then
      C`associated_space_over_z := M`associated_space_over_z;
   end if;
   if assigned M`default_precision then
      C`default_precision := M`default_precision;
   end if;
   return C;
end function;

intrinsic ModularForms(M::ModFrm, N::RngIntElt) -> ModFrm
{The full space of modular forms with the same defining 
weight, base ring, etc. as M, but with level N.  
If M is defined by nontrivial dirichlet characters, then
N must be a multiple at least one of the conductors 
of the characters.}
 
   // Replace M by its "full" space, for simplicity (added 04-09, SRD)
   M := AmbientSpace(M);
   assert M`type eq "full";
 
   if N eq Level(M) then
      return M;
   elif assigned M`other_levels and 
        exists(tup){tup: tup in M`other_levels | tup[1] eq N} then 
      return tup[2];
   else
      M`other_levels := [* *];
   end if;

   T := New(ModFrm);  
   T`base_ring := BaseRing(M);
   T`level := N;
   T`weight := Weight(M);
   T`is_gamma1 := IsGamma1(M);
   T`type := "full";
   if not IsGamma1(M) and assigned M`dirichlet_character then 
      chars := [];
      E := M`dirichlet_character;
      G := DirichletGroup(N,BaseRing(Parent(E[1])));
      for eps in [chi : chi in E |  N mod Conductor(chi) eq 0] do
         e1 := Restrict(eps,Conductor(eps));
         e2 := N ne Conductor(eps) select Extend(e1,N) else e1;
         Append(~chars, e2);
      end for;
      require #chars gt 0: "If M is defined by nontrivial dirichlet characters, "
         * "then N must be a multiple at least one of the conductors of the characters.";
      T`dirichlet_character := chars;
   end if;
   if assigned M`default_precision then
      T`default_precision := M`default_precision;
   end if;

   // link it with modular_symbols (added 04-09, SRD)
   if assigned M`mf_modular_symbols then 
      T`mf_modular_symbols := [* false, false, false *]; // initialize blank
      MSlist := M`mf_modular_symbols;
      for s in [1..3] do 
         if Type(MSlist[s]) eq SeqEnum then
            assert #MSlist[s] eq 1;
            MS := MSlist[s][1]; 
            assert Type(MS) eq ModSym;
            if assigned MS`other_levels and exists(tup){tup: tup in MS`other_levels | tup[1] eq N} then
               T`mf_modular_symbols[s] := [tup[2]];
            end if;
         end if;
      end for;
   end if;

   Append(~M`other_levels, <N,T>);
   return T;
end intrinsic;


/*
intrinsic ModularForms(eps::GrpDrchElt, k::RngIntElt) -> ModFrm
{This returns M_k(eps), which is the direct sum of the e parts 
of M_k(Gamma_1(N)) as e varies over the Galois conjugates of eps.} 
   requirege k,2;
   require Type(BaseRing(eps)) in {FldCyc, FldRat} : 
       "The base ring of argument 1 must be the rationals or cyclotomic.";
   return ModularForms([eps],k);
end intrinsic;
*/



function CreateModularFormFromElement(parent, element)
   assert Type(parent) eq ModFrm;
   assert Type(element) in {ModTupRngElt, ModTupFldElt};
   y := New(ModFrmElt);
   y`parent := parent;
   y`element := element;
   return y;
end function;


function create_ModFrmElt_from_theta_data(parent, theta_data)
   assert Type(parent) eq ModFrm;
   f := New(ModFrmElt);
   f`parent := parent;
   f`theta_data := theta_data;
   return f;
end function;


function CoerceRngIntElt(M,x)
   assert Type(M) eq ModFrm;
   assert Type(x) eq RngIntElt;

   if x eq 0 then
      return true, CreateModularFormFromElement(M, 
                 RSpace(BaseRing(M), Dimension(M))!0);
   else
      return false, "Can't coerce nonzero integer in.";
   end if;
  
end function;

function CoerceRngSerElt(M,x)

   Mx := Parent(x);
   RM := BaseRing(M);
   RMx := BaseRing(Mx);

   if RMx cmpne RM then
    if not &and[IsCoercible(RM,e) : e in Eltseq(x)] then
      return false, "Incompatible base rings."; end if;
   x:=PowerSeriesRing(RM,AbsolutePrecision(x))!x; end if;

   type := Type(x);
   assert ISA(type, RngSerElt);
   if ISA(type, RngSerLaurElt) then 
      if Valuation(x) lt 0 then 
         return false, "Illegal coercion -- the leading term of the given power series has negative exponent";
      end if; 
      x := PowerSeriesRing(RMx)! x;
      return CoerceRngSerElt(M,x);
   end if;
   assert ISA(type, RngSerPowElt);

   /* If x agrees with the q-expansion of some element of M, then
      this function returns that element. Otherwise, there is an error. 
      *** Mark and Steve changed this policy: the given q-expansion must 
          now uniquely determine an element of M ***
   */
   error_message := "The series does not define a modular form in the space.";

   if Dimension(M) eq 0 then 
      if x eq 0 then return M!0; 
      else return false, error_message; end if; 
   end if;

   if RelativePrecision(x) cmpeq Infinity() then
      return false, "Illegal coercion -- power series with infinite precision not accepted";
   end if;
   prec := AbsolutePrecision(x);
   if prec lt PrecisionBound(M : Exact) then
     return false, "Illegal coercion -- form not uniquely determined."; end if;

// TO DO: rewrite this rubbish starting here
   Q := [PowerSeriesInternal(f,prec) : f in Basis(M)];
   exact := IsExact(BaseRing(Universe(Q)));
   elt := [RM|];
   f := Parent(Q[1])!0;
   for n in [1..#Q] do
      if exact then
         v := Valuation(Q[n]);
      else
         // TO DO: Valuation should work here too.
         // For example, fails for Example H111E17 (during the call to pAdicEmbeddings) 
         // because Valuation gets mixed up when you feed it a power series over p-adics.
         seq := [Integers() | i : i in [0..prec-1] | not IsWeaklyZero(Coefficient(Q[n],i))];
         if #seq eq 0 then
            v := prec;
         else
            v := Min(seq);
         end if;
      end if;
         
      if v ge AbsolutePrecision(x-f) then
         Append(~elt,0);
         continue;
      end if;
     /* It's now no longer possible to work in K[x]/(f(x)) when f is irred.  
         Until this changes, working with p-adic modular forms in MAGMA 
         is essentially impossible, since generic p-adic extensions can't
         be created.   The problem is the XGCD doesn't work over p-adics,
         but I'm  sure this'll be fixed soon.  (WAS, 06/16/03). */
      coef := Coefficient(x-f,v) / Coefficient(Q[n],v);
      if not (coef in RM) then
         return false, error_message;
      end if;
      coef := RM!coef;
      f +:= coef*Q[n];
      Append(~elt,coef);
   end for;
   g := M!elt;
   if x ne PowerSeries(g,prec) then 
      // the above test doesn't work over rings like C or Qp.
      if Type(RM) in {FldRat, RngInt, FldNum, FldCyc, FldFin} then
//         print "0 =/= coerced - x = ", x - PowerSeries(g,prec);
         return false, error_message;
      end if;
   end if;
   return true, g;
end function;

function CoerceSeqEnum(M,x)
   if IsNull(x) then return false,"Illegal coercion"; end if;
   if Universe(x) cmpne BaseRing(M) then
    if not &and[IsCoercible(BaseRing(M),e) : e in x] then
      return false, "Incompatible base rings."; end if;
    x:=[BaseRing(M)!e : e in x]; end if;
   val, el := IsCoercible(RSpace(M),x);
   if val eq false then
      return false, 
          "Illegal coercion.";
   end if;
   return true, CreateModularFormFromElement(M, el);
end function;


function CoerceModFrmElt(M,x)
   Mx := Parent(x);
   if BaseRing(Mx) cmpne BaseRing(M) then
      return false, "Base rings are not the same.";
   end if;

   /* Removed ModularForms(Rng), don't want to waste time checking this anyway
   if IsRingOfAllModularForms(M) then
      y := CopyOfModFrmElt(x);
      y`parent := M;
      delete y`element;
      return true, y;
   elif IsRingOfAllModularForms(Mx) then
      return false, "Illegal coercion.";
   end if;  
   */
   if IsIdentical(M, Mx) then
      return true, x;
   elif Weight(M) ne Weight(Mx) then
      return false, "Incompatible weights.";
   end if;

   copy := false;
   if IsAmbientSpace(M) and IsAmbientSpace(Mx) and Dimension(M) eq Dimension(Mx) then
      Chi := Universe(DirichletCharacters(M));
      chars_Mx := DirichletCharacters(Mx);
      Chix := Universe(chars_Mx);
      if Chi eq Chix then
         if not IsIdentical(Chi, Chix) then
            ChangeUniverse(~chars_Mx, Chi); 
         end if;
         copy := Seqset(chars_Mx) eq Seqset(DirichletCharacters(M));
      end if;
   end if;
   if copy then
      y := CopyOfModFrmElt(x);
      y`parent := M;
      return true, y;
   end if;   

   // TO DO: revise whole function, rather not use subset (too complicated)
   // ... the PowerSeries route should be the last resort
   if Mx subset M then  
      g := PowerSeries(x, PrecisionBound(M:Exact));
      return IsCoercible(M,g);
   end if;

   N := LCM(Level(M),Level(Mx));
   if IsGamma0(M) and IsGamma0(Mx) then  
      G := Gamma0(N); 
   else
      G := Gamma1(N);
   end if;
   // if M < Parent(x), must check up to the precision bound of the larger space
   Mbig := BaseExtend(ModularForms(G,Weight(M)), BaseRing(M));
   prec := PrecisionBound(Mbig : Exact := false);
   t, z := IsCoercible(M, PowerSeries(x,prec));
   if t then
      return t, z;
   end if;

   return false, "Cannot coerce modular form.";
end function;

intrinsic IsCoercible(M::ModFrm,x::.) -> BoolElt, ModFrmElt
{Coerce x into M.}
   case Type(x):
      when RngIntElt:
         return CoerceRngIntElt(M,x);
      when ModTupRngElt, ModTupFldElt:
         return CoerceSeqEnum(M,Eltseq(x));
      when SeqEnum:
         return CoerceSeqEnum(M,x);
      when RngSerPowElt, RngSerLaurElt:
         return CoerceRngSerElt(M,x);
      when ModFrmElt:
         return CoerceModFrmElt(M,x);
      else
         return false, "Illegal coercion -- the given object has the wrong type";
   end case;
end intrinsic;


intrinsic BaseExtend(M::ModFrm, R::Rng) -> ModFrm, Map
{The base extension of M to the commutative ring R and the induced map
from M to BaseExtend(M,R).  The only requirement on R is that
there is a natural coercion map from BaseRing(M) to R.    For 
example, when BaseRing(M) is the integers then any commutative
ring R is allowed.}
   require IsCommutative(R) : "Argument 2 must be commutative.";
   if R cmpeq BaseRing(M) then
      return M;
   end if;
   phi := hom<BaseRing(M) -> R | x :-> R!x>;
   return BaseExtend(M,phi);
end intrinsic;


intrinsic BaseExtend(M::ModFrm, phi::Map) -> ModFrm, Map
{The base extension of M to R using the map phi:BaseRing(M) --> R, 
and the induced map from M to BaseExtend(M,R).}
   require IsCommutative(Codomain(phi)) : "Argument 2 must be commutative.";
   M_R := CopyOfDefiningModularFormsObject(M);
   if assigned M_R`dimension and M_R`dimension eq -1 then
      // dimension = -1 means we think we are in the middle of determining
      // the dimension of this space, which we aren't  ---  fixed by Steve.
      delete M_R`dimension; 
   end if;
   if Characteristic(Codomain(phi)) ne 0 then
      delete M_R`default_precision;
   end if;
   M_R`base_ring := Codomain(phi);
   M_R`base_extend_map := phi;
   if Type(BaseRing(M_R)) ne RngInt then
      M_R`associated_space_over_z := AssociatedSpaceOverZ(M);
   end if;
   if not IsAmbientSpace(M) then
      M_R`ambient_space := BaseExtend(AmbientSpace(M),phi);
   end if;
   psi := hom<M -> M_R | x :-> M_R![phi(a) : a in Eltseq(x)]>;
   return M_R, psi;
end intrinsic;

intrinsic DisownChildren(M::ModFrm) 
{No longer necessary -- do not use!}
   return;
end intrinsic;

intrinsic DeleteAllAssociatedData(M::ModFrm : DeleteChars:=false)
{"} // "
   return;
end intrinsic;

