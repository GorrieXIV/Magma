freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: arithmetic.m

   $Header: /home/was/magma/packages/modform/code/RCS/arithmetic.m,v 1.6 2002/04/15 07:26:44 was Exp $

   $Log: arithmetic.m,v $
   Revision 1.6  2002/04/15 07:26:44  was
   ...

   Revision 1.5  2002/04/15 07:25:00  was
   Made * more flexible for f*T.

   Revision 1.4  2001/06/30 03:12:29  was
   Changed '+' slightly.

   Revision 1.3  2001/05/30 18:53:33  was
   Done.

   Revision 1.2  2001/05/16 04:11:36  was
   *** empty log message ***

   Revision 1.1  2001/05/16 03:50:39  was
   Initial revision

      
 ***************************************************************************/

import "predicates.m" : Element;

function CreateModularFormFromOperation(op,g,h)
   assert op in {"*", "-", "+", "scalar"};
   if Type(g) eq ModFrmElt then
      assert BaseRing(Parent(g)) eq BaseRing(Parent(h));
   end if;
   assert Type(h) eq ModFrmElt;
   f := New(ModFrmElt);
   f`created_from := <op,g,h>;
   if op eq "scalar" then
      f`parent := Parent(h);
      return f;
   end if;
   Mg := Parent(g);
   Mh := Parent(h);
   N := LCM(Level(Mg), Level(Mh));
   if IsRingOfAllModularForms(Mg) then
      M := Mg;
   elif IsRingOfAllModularForms(Mh) then
      M := Mh;
   else
      case op:
         when "*":
            kg := Weight(g); kh := Weight(h);  
            k := kg + kh;   if IsIntegral(k) then k := Integers()!k; end if;
            if k eq 1 then
               // weight 1 spaces are not normally allowed, but let's sneak some in 
               M := New(ModFrm);
               M`type := "full";
               M`base_ring := Integers();
               M`weight := k;
               if IsGamma0(Mg) and IsGamma0(Mh) then
                  M`dirichlet_character := [DirichletGroup(N)! KroneckerCharacter(-1)];
                  M`is_gamma1 := false;
               elif #DirichletCharacters(Mg) eq 1 and #DirichletCharacters(Mh) eq 1 then 
                  M`dirichlet_character := [DirichletCharacters(Mg)[1] * DirichletCharacters(Mh)[1]
                                            * DirichletGroup(N)! KroneckerCharacter(-1)];
                  M`is_gamma1 := false;
               else
                  M`level := N;
                  M`is_gamma1 := true;
               end if;
            elif IsGamma0(Mg) and IsGamma0(Mh) then
               if not IsIntegral(kg) and not IsIntegral(kh) and IsOdd(k) then
                  chi := DirichletGroup(N)! KroneckerCharacter(-1);
                  M := ModularForms(chi,k);
               else
                  // if kg (resp. kh) is integral, then it is even unless g (resp. h) is zero
                  M := ModularForms(N,k);
               end if;
            elif #DirichletCharacters(Mg) eq 1 and #DirichletCharacters(Mh) eq 1 then 
               eps := DirichletCharacters(Mg)[1] * DirichletCharacters(Mh)[1];
               if not IsIntegral(kg) and not IsIntegral(kh) and IsOdd(k) or
                  not IsIntegral(k) and (IsIntegral(kg) and IsOdd(kg) or IsIntegral(kh) and IsOdd(kh))
               then
                  chi := DirichletGroup(N)! KroneckerCharacter(-1);
                  M := ModularForms(eps*chi, k);
               else
                  M := ModularForms(eps, k);
               end if;
            else
                M := ModularForms(Gamma1(N),k);
            end if;
         when "+": 
            if Weight(g) eq Weight(h) then
               if IsGamma0(Mg) and IsGamma0(Mh) then
                  M := ModularForms(N,Weight(g));
               else
                  M := ModularForms(Gamma1(N),Weight(g)); 
               end if;
            else 
               M := ModularForms();  
            end if;
         else:
            error "CreateModularFormFromOperation -- Invalid operation.";
      end case;
   end if;
   f`parent := BaseExtend(M,BaseRing(Mg));
   return f;
end function;


// TO DO
// operands should belong to the same parent,
// or to parents that have an unambiguous relationship;
// use of general coercion here is too loose 

intrinsic '+'(f::ModFrmElt,g::ModFrmElt) -> ModFrmElt 
   {Sum of modular forms}
   require BaseRing(Parent(f)) eq BaseRing(Parent(g)) : 
     "Arguments 1 and 2 have incompatible coefficient rings.";

   if AmbientSpace(Parent(f)) ne AmbientSpace(Parent(g)) then
      return CreateModularFormFromOperation("+",f,g);      
   end if;

   M := Parent(f);
   if M eq Parent(g) then
      return M!(Element(f)+Element(g));
   else
      A := AmbientSpace(M);
      return A!f + A!g;
   end if;

end intrinsic; 

intrinsic '-'(f::ModFrmElt,g::ModFrmElt) -> ModFrmElt 
   {Difference of modular forms}
   require BaseRing(Parent(f)) eq BaseRing(Parent(g)) : 
     "Arguments 1 and 2 have incompatible coefficient rings.";

   return f+ (-1)*g;
end intrinsic; 

intrinsic '-'(f::ModFrmElt, g::RngSerPowElt) -> RngSerPowElt
{"} // "
   t, _ := IsCoercible(Parent(g),PowerSeries(f,1));
   require t : "The q-expansion of argument 1 must be coercible into the parent of argument 2.";
   return f+(-g);
end intrinsic;

intrinsic '-'(g::RngSerPowElt, f::ModFrmElt) -> RngSerPowElt
{"} // "
   t, _ := IsCoercible(Parent(g),PowerSeries(f,1));
   require t : "The q-expansion of argument 1 must be coercible into the parent of argument 2.";
   return g+(-f);
end intrinsic;

intrinsic '-'(f::ModFrmElt) -> ModFrmElt
{"} // "
   return (-1)*f;
end intrinsic;

intrinsic '+'(g::RngSerPowElt, f::ModFrmElt) -> RngSerPowElt
{Sum of modular forms}
   t, _ := IsCoercible(Parent(g),PowerSeries(f,1));
   require t : "The q-expansion of argument 1 must be coercible into the parent of argument 2.";
   return f+g;
end intrinsic;

intrinsic '+'(f::ModFrmElt, g::RngSerPowElt) -> RngSerPowElt
{"} // "
   t, _ := IsCoercible(Parent(g),PowerSeries(f,1));
   require t : "The q-expansion of argument 1 must be coercible into the parent of argument 2.";
   if RelativePrecision(g) cmpne Infinity() then
      _, ff := IsCoercible(Parent(g),PowerSeries(f,AbsolutePrecision(g)));
      return ff + g;
   else
      _, ff := IsCoercible(Parent(g),PowerSeries(f));
      return ff + g; 
   end if;
end intrinsic;

intrinsic '*'(f::ModFrmElt, T::AlgMatElt) -> ModFrmElt
{Image of modular form f under the matrix T acting on Parent(f)}
   require Degree(Parent(T)) eq Dimension(Parent(Element(f))) : 
         "The degrees of arguments 1 and 2 are incompatible.";
   Rf := BaseRing(Parent(f));
   RT := BaseRing(Parent(T));
   if Type(Rf) ne Type(RT) then
      if Type(Rf) eq RngInt then
         f := BaseExtend(Parent(f),RT)!Eltseq(f);      
      end if;
      if Type(RT) eq RngInt then
         T := BaseExtend(Parent(T),Rf)!Eltseq(T);
      end if;
   end if;
   return Parent(f)!(Element(f)*T);
end intrinsic;


intrinsic '*'(f::ModFrmElt, x::RngElt) -> ModFrmElt
   {Product of modular form and scalar}
   require x in BaseRing(Parent(f)) : 
        "Argument 1 must be in the base ring of the parent of argument 2.";
   return x*f;
end intrinsic;

intrinsic '*'(x::RngElt, f::ModFrmElt) -> ModFrmElt
   {"} // "
   if x eq 1 then return f; end if;

   M := Parent(f);
   if x notin BaseRing(M) then 
      if ISA(Type(x), Mtrx) then 
         error "Invalid types Mtrx*ModFrmElt. Note that Hecke operators act from the right.";
      else 
         MR := BaseExtend(M, Parent(x));
         return x * MR!f;
      end if;
   end if;

   if Weight(f) eq 1 and assigned f`created_from and f`created_from[1] eq "*" then
      _, f1, f2 := Explode(f`created_from);
      ans := New(ModFrmElt);
      ans`parent := f`parent;
      ans`created_from := <"*", x*f1, f2>;
      return ans;
   end if;

   // Steve added this case ... maybe a bit pointless ... and possibly could cause trouble if the 
   // package doesn't know what to do with elements determined only by a q-expansion and parent ...
   if not assigned f`element then
      if assigned f`eisenstein then 
         _ := qExpansion(f);
      end if;
      if assigned f`q_expansion and AbsolutePrecision(f`q_expansion) ge PrecisionBound(Parent(f)) then
         // the element is determined by its (known) q-expansion
         ans := New(ModFrmElt);
         ans`parent := f`parent;
         ans`q_expansion := x*f`q_expansion;
         return ans;
      end if;
   end if;

   return M!(x*Element(f));
end intrinsic;

intrinsic '/'(f::ModFrmElt, x::RngElt) -> ModFrmElt
   {"} // "
   require x ne 0 : "Division by zero.";
   require 1/x in BaseRing(Parent(f)) : "Argument 2 is not in the base ring of argument 1.";
   return (1/x)*f;
end intrinsic;

intrinsic '^'(f::ModFrmElt, n::RngElt) -> ModFrmElt
   {Power of modular form, in the appropriate modular forms space}
   requirege  n, 1;
   g := f;
   for i in [2..n] do   // very bad.
      g := g * f;
   end for;
   return g;
end intrinsic;

intrinsic '*'(f::ModFrmElt,g::ModFrmElt) -> ModFrmElt 
   {Product of modular forms, in the appropriate modular forms space}
   require BaseRing(Parent(f)) eq BaseRing(Parent(g)) : 
     "Arguments 1 and 2 have incompatible coefficient rings.";
   return CreateModularFormFromOperation("*",f,g);   
end intrinsic; 

intrinsic IsZero(f::ModFrmElt) -> BoolElt
{True iff the modular form f is zero}
   return forall{x : x in Eltseq(f) | IsZero(x)};
end intrinsic;

