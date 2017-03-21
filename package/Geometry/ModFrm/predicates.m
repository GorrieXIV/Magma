freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: creation.m

   $Header: /home/was/magma/packages/ModFrm/code/RCS/predicates.m,v 1.7 2002/08/26 20:12:58 was Exp was $

   $Log: predicates.m,v $
   Revision 1.7  2002/08/26 20:12:58  was
   Deleted a comment.

   Revision 1.6  2002/04/13 07:25:51  was
   Added stuff for p-new subspaces.

   Revision 1.5  2001/05/30 19:52:22  was
   Only allow degree for certain fields.

   Revision 1.4  2001/05/30 18:56:33  was
   Created.

   Revision 1.3  2001/05/16 04:01:11  was
   *** empty log message ***

   Revision 1.2  2001/05/16 03:56:17  was
   clearing it.

   Revision 1.1  2001/05/16 03:56:03  was
   Initial revision

   Revision 1.1  2001/05/16 03:51:41  was
   Initial revision

      
 ***************************************************************************/


import "eisenstein.m" : DimensionOfEisensteinSpace;

import "q-expansions.m" : ApproximatePrecisionBound;

import "weight1.m": compute_weight1_cusp_space;

forward Element,
        WhichNewform;


function SpaceType(M)
   assert Type(M) eq ModFrm;
   return M`type;
end function;

function SpaceTypeParam(M)
   assert Type(M) eq ModFrm;
   if not assigned M`type_param then
      M`type_param := 0; 
   end if;
   return M`type_param;
end function;

intrinsic BaseRing(M::ModFrm) -> Rng
{The field over which Basis(M) is defined.  This is either the rational
numbers, a prime finite field, or a p-adic field Q_p.}
   return M`base_ring;
end intrinsic;


function DimensionOfCuspidalSpace(M)
   assert Type(M) eq ModFrm;
   assert IsAmbientSpace(M);

   k := Weight(M);
   if k eq 1 then
      compute_weight1_cusp_space(~M);
      return M`cuspidal_subspace`dimension;
   elif not (k in Integers()) then
      error "Calling the wrong function to get half integral cuspidal dimension.";
   else
      if IsGamma1(M) then
         return DimensionCuspFormsGamma1(Level(M),k);
      else
         eps := DirichletCharacters(M);
         return &+[EulerPhi(Order(e))*
                            DimensionCuspForms(e, k) : e in eps];
      end if;
   end if;
end function;

function DimensionOfNewCuspidalSpace(M, param)
   assert Type(M) eq ModFrm;
   assert IsAmbientSpace(M);
   k := Weight(M);
   if k eq 1 then
      error "Weight one new cuspidal dimension not programmed.";            
   elif not (k in Integers()) then
      error "Half integral new cuspidal dimension not programmed.";
   else
      if IsGamma1(M) then
         return DimensionNewCuspFormsGamma1(Level(M),k,param);
      elif #DirichletCharacters(M) eq 1 and IsTrivial(DirichletCharacters(M)[1]) then
         return DimensionNewCuspFormsGamma0(Level(M),k,param);
      else
         return &+[EulerPhi(Order(eps))*DimensionNewCuspForms(eps,k,param) : 
                        eps in DirichletCharacters(M)];
      end if;
   end if;
end function;


function DimensionOfNewEisensteinSpace(M, param)
   assert Type(M) eq ModFrm;
   assert IsAmbientSpace(M);
   if param ne 0 then
      error "DimensionOfNewEisensteinSpace -- nontrivial p-new subspace, not yet programmed.";
   end if;

   k := Weight(M);
   if k eq 1 then
      error "Weight one new eisenstein dimension not programmed.";            
   elif not (k in Integers()) then
      error "Half integral new eisenstein dimension not programmed.";
   else
      E := EisensteinSubspace(M);
      N := Newforms(E);
      return &+[Integers()|#f : f in N];
   end if;
end function;


function ObviouslyHasDimensionZero(M)
   k := Weight(M);
   if not IsGamma1(M) and k in Integers() then
      t := true;
      for eps in DirichletCharacters(M) do
         if not ((IsEven(k) and IsOdd(eps)) or (IsOdd(k) and IsEven(eps))) then
            t := false;
            break;
         end if;
      end for;
      if t then
         return true;
      end if;
   end if;
   if k le 0 then
      return true;
   end if;
   return false;
end function;

intrinsic Dimension(M::ModFrm) -> RngIntElt
{The dimension of the space M of modular forms. (If M is defined 
over a ring R, then M is free and this is the rank of M.)}
 
   if assigned M`dimension and M`dimension eq -1 then
      require false: 
        "There is a bug in Dimension that will result in an "* 
        "infinite recursive call of Dimension by itself.";
   end if;

   if not assigned M`dimension then
      vprint ModularForms : "ModularForms: Computing dimension.";
      if ObviouslyHasDimensionZero(M) then
         M`dimension := 0;
         return M`dimension;
      end if;
      M`dimension := -1;   // this means its being computed.
      case SpaceType(M): 
         when "full":
            E := EisensteinSubspace(M);
            S := CuspidalSubspace(M); 
            M`dimension := Dimension(E) + Dimension(S);
         when "cusp":
            M`dimension := DimensionOfCuspidalSpace(AmbientSpace(M));
         when "eis":
            M`dimension := DimensionOfEisensteinSpace(AmbientSpace(M));
         when "new":
            M`dimension := Dimension(NewSubspace(EisensteinSubspace(M),SpaceTypeParam(M)))
                             + Dimension(NewSubspace(CuspidalSubspace(M),SpaceTypeParam(M)));
         when "cusp_new":
            M`dimension := DimensionOfNewCuspidalSpace(AmbientSpace(M), SpaceTypeParam(M));
         when "eis_new":
            M`dimension := DimensionOfNewEisensteinSpace(AmbientSpace(M), SpaceTypeParam(M)); 
         when "full_half_int", "cusp_half_int":
            if Weight(M) eq 1/2 then 
               M`dimension := &+[Integers()| EulerPhi(Order(tup[1])) : tup in WeightOneHalfData(M)]; 
            else
               M`dimension := DimensionByFormula(M);  
            end if;
         else:
            error "M has an invalid type, where M = ", M;
      end case;

      // Check the Cohen-Oesterle formula. 
      formulas_okay := true;
      if Weight(M) ne 1 then
         if SpaceType(M) eq "full" and #DirichletCharacters(M) eq 1 then
            eps := DirichletCharacters(M)[1];
            num_conjs := EulerPhi(Order(eps));
            dim := DimensionByFormula( Level(M), eps, Weight(M));
            formulas_okay and:= M`dimension eq num_conjs*dim;
         elif SpaceType(M) eq "cusp" and #DirichletCharacters(M) eq 1 then
            eps := DirichletCharacters(M)[1];
            num_conjs := EulerPhi(Order(eps));
            dim1 := DimensionByFormula( Level(M), eps, Weight(M) : Cuspidal);
            dim2 := DimensionCuspForms( eps, Weight(M));
            formulas_okay and:= M`dimension eq num_conjs*dim1 and dim1 eq dim2 ;
         end if;
      end if;
      error if not formulas_okay, "Error in calculation of dimension." *
         "\nPLEASE REPORT THIS SERIOUS BUG TO US at magma-bugs@maths.usyd.edu.au";
   end if;

   if assigned M`dimension then
      return M`dimension;
   end if;

   error "Dimension -- MAGMA is currently not clever enough to "*
         "compute the dimension in this case.";  
end intrinsic;


intrinsic Level(M::ModFrm) -> RngIntElt
{The level of M.}
   if not assigned M`level then
      if assigned M`dirichlet_character then
         M`level := Modulus(M`dirichlet_character[1]);
      end if;
      require assigned M`level : "The level of argument 1 is not defined.";
   end if;
   return M`level;      
end intrinsic;

intrinsic Level(f::ModFrmElt) -> RngIntElt
{The level of f.}
   require not IsRingOfAllModularForms(Parent(f)) : 
     "The level of f is not known.";
   return Level(Parent(f));
end intrinsic;

intrinsic IsRingOfAllModularForms(M::ModFrm) -> BoolElt
{True if and only if M is the ring of all modular forms over
a given ring.}
   return not assigned M`weight;
end intrinsic;

intrinsic Weight(M::ModFrm) -> RngIntElt
{The weight of M.}
   require not IsRingOfAllModularForms(M) : 
     "The weight of f is not known or not defined.";
   return M`weight;      
end intrinsic;

intrinsic Weight(f::ModFrmElt) -> RngIntElt
{The weight of f, if it is defined.}
   if not assigned f`weight then
      require not IsRingOfAllModularForms(Parent(f)) : 
        "The weight of f is not known or not defined.";
      f`weight := Weight(Parent(f));
   end if;
   return f`weight;
end intrinsic;

intrinsic IsGamma1(M::ModFrm) -> BoolElt
{True if and only if M is explicitly a space of modular forms for Gamma_1(N).}
   if IsRingOfAllModularForms(M) then
      return false;
   end if;
   assert assigned M`is_gamma1;
   return M`is_gamma1;
end intrinsic;

intrinsic IsGamma0(M::ModFrm) -> BoolElt
{True if and only if M is a space of modular forms for Gamma_0(N).}
   if IsRingOfAllModularForms(M) then
      return false;
   end if;
   if IsGamma1(M) then
      return Level(M) le 2;
   end if;
   return #DirichletCharacters(M) eq 1 and IsTrivial(DirichletCharacters(M)[1]);
end intrinsic;

intrinsic IsAmbientSpace(M::ModFrm) -> BoolElt
{True if and only if M is an ambient space.}
   return M`type in {"full", "full_half_int"};
end intrinsic;   

intrinsic IsCuspidal(M::ModFrm) -> BoolElt
{True if M is contained in the cuspidal subspace of the ambient space of M.}
   if not assigned M`is_cuspidal then
      if assigned M`dimension and M`dimension eq 0 then
         M`is_cuspidal := true;
         return true;
      end if;
      case M`type:
         when "cusp", "cusp_new", "cusp_newform", "cusp_half_int":
            M`is_cuspidal := true;
         when "full":
            M`is_cuspidal := false;
         when "full_half_int":
            M`is_cuspidal := Dimension(M) eq Dimension(CuspidalSubspace(M));
         when "eis", "eis_new", "new", "eis_newform":
            M`is_cuspidal := false;
         else: 
            print M`type;
            error "Bug in IsCuspidal";
      end case;
   end if;

   return M`is_cuspidal;    
end intrinsic;   

intrinsic IsEisenstein(M::ModFrm) -> BoolElt
{True if M is contained in the Eisenstein subspace of the ambient space of M.}

   if not assigned M`is_eisenstein then
      if assigned M`dimension and M`dimension eq 0 then
         M`is_eisenstein := true;
         return true;
      end if;
      case M`type:
         when "eis", "eis_new", "eis_newform":
            M`is_eisenstein := true;
         when "full", "full_half_int", "cusp_half_int":
            M`is_eisenstein := false;
         when "cusp", "cusp_new", "new", "cusp_newform":
            M`is_eisenstein := false;
         else: 
            error "Bug in IsEisenstein";
      end case;
   end if;

   return M`is_eisenstein;    
end intrinsic;   


function AbsoluteDegreeOfRingGeneratedBy(gens)
   assert Type(gens) eq SeqEnum;
   if #gens eq 0 then
      return 1;
   end if;
   case Type(Universe(gens)):
      when RngInt, FldRat: 
         return 1;
      when FldNum:
         return Degree(sub< Universe(gens) | gens >);
      when FldFin:
         d := Max([Degree(sub< Universe(gens) | g >) : g in gens]);
         return d;
      when FldCyc:
         k,phi := NumberField(Universe(gens));
         return AbsoluteDegreeOfRingGeneratedBy([phi(g) : g in gens]);
      else:
         error "Invalid type.";
   end case;
end function;

intrinsic Degree(f::ModFrmElt) -> RngIntElt
{The number of Galois conjugates of f over the
prime subfield.}
   require Type(BaseRing(Parent(f))) in 
          {FldRat, FldNum, RngInt, FldFin, FldCyc, FldAlg, FldQuad} :
      "Argument 1 must be defined over a number field or a finite field.";
   if not assigned f`degree then 
      if assigned f`element then
         f`degree := AbsoluteDegreeOfRingGeneratedBy(Eltseq(f`element));
      elif assigned f`eisenstein then
         f`degree := EulerPhi(LCM(Order(f`eisenstein[1]), Order(f`eisenstein[2])));
      elif assigned f`mf_modular_symbols then
         f`degree := Dimension(f`mf_modular_symbols)*
                        Degree(BaseField(f`mf_modular_symbols));   
      else
         f`degree := AbsoluteDegreeOfRingGeneratedBy(Eltseq(Element(f)));
      end if;
   end if;
   if f`degree eq 0 then
      require false : "Unable to determine the degree of argument 1.";
   end if;
   return f`degree;
end intrinsic;


intrinsic DirichletCharacters(M::ModFrm) -> SeqEnum
{The sequence containing Galois representatives of the Dirichlet characters associated with M.}

   // Let's try having M`dirichlet_character only assigned for ambient spaces.
   // This is to avoid repeatedly creating/computing many copies of them. 
   // TO DO: Go through functions that created subspaces etc and *don't* assign it.
   //   --- Steve

   if not IsAmbientSpace(M) then 
      assert assigned M`ambient_space;
      return DirichletCharacters(M`ambient_space); 
   end if;

   if not assigned M`dirichlet_character then
      if IsGamma1(M) then
         N := Level(M);
         vprint ModularForms, 3 : 
           "Computing Galois-conjugacy classes of Dirichlet characters of level", N;
         n := EulerPhi(N);
         F := n le 2 select RationalField() else
                            CyclotomicField(n);
         G := DirichletGroup(N,F);
         M`dirichlet_character := 
                  GaloisConjugacyRepresentatives(G);
      else
         M`dirichlet_character := 
                  [DirichletGroup(Level(M))!1];
      end if;
   end if;
   return M`dirichlet_character;
end intrinsic;


intrinsic Parent(f::ModFrmElt) -> ModFrm
   {}
   return f`parent;
end intrinsic;


intrinsic 'eq' (M::ModFrm,N::ModFrm) -> BoolElt
   {True if M and N are mathematically the same space of modular forms,
    and their base rings are equal.}
   if IsIdentical(M,N) then 
      return true; 
   end if;

   if BaseRing(M) cmpne BaseRing(N) then
      return false;
   end if;
   if IsRingOfAllModularForms(M) then
      return IsRingOfAllModularForms(M);
   end if;
   if IsAmbientSpace(M) and IsAmbientSpace(N) then
      if Weight(M) eq Weight(N) and Level(M) eq Level(N) then
         if IsGamma1(M) and IsGamma1(N) or IsGamma0(M) and IsGamma0(N) then
            return true;
         end if;
         charM := DirichletCharacters(M);
         charN := DirichletCharacters(N);
         if charM cmpeq charN then
            return true;
         elif &and[ IsCoercible(charN,chi) : chi in charM ] 
               and ChangeUniverse(charN, Universe(charM)) eq charM then
            return true;
         else
            return false;
         end if;
      else
         return false;
      end if;
   elif AmbientSpace(M) eq AmbientSpace(N) then
      if SpaceType(M) ne SpaceType(N) then
         return false;
      end if;  
      if SpaceType(M) in {"cusp_newform", "eis_newform"} then
         f := M`made_from_newform;
         g := N`made_from_newform;
         if PowerSeries(f,5) cmpne PowerSeries(g,5) then
            return false;
         end if;
         d := PrecisionBound(AmbientSpace(M) : Exact := false); // bad
         return PowerSeries(f,d) eq PowerSeries(g,d);
      elif SpaceType(M) in {"full","cusp","eis","cusp_new","eis_new","full_half_int","cusp_half_int"} then 
         return true;
      else 
         require false: "Equality testing not implemented for modular forms spaces of this kind."; 
      end if;
      
   else
      return false;
   end if;
end intrinsic;

intrinsic 'eq' (f::ModFrmElt,g::ModFrmElt) -> BoolElt
   {True iff f and g are mathematically the same modular form (and their parent spaces are equal).}
   if IsIdentical(f,g) then 
      return true; 
   elif Parent(f) ne Parent(g) then 
      return false; 
   elif IsNewform(f) and IsNewform(g) then 
      return f`which_conjugate eq g`which_conjugate;
   end if;
   return Eltseq(f) cmpeq Eltseq(g);
end intrinsic;

intrinsic 'subset'(M1::ModFrm, M2::ModFrm) -> BoolElt
{True iff M1 is a subspace of M2, where these are spaces of modular 
forms with equal ambient spaces.}
   if AmbientSpace(M1) ne AmbientSpace(M2) then
      return false;
   end if;
   if Dimension(M1) eq 0 then
      return true;
   end if;
   if IsAmbientSpace(M2) then 
      return true;
   end if;
   case SpaceType(M1):
      when "ambient":
         return false;
      when "cusp":
         return SpaceType(M2) in {"cusp", "cusp_new", "cusp_newform"};
      when "eis":
         return  SpaceType(M2) in {"eis", "eis_new", "eis_newform"};
      when "new":
         return  SpaceType(M2) in {"new", "cusp_new", "eis_new", "eis_newform", "cusp_newform"}
           and (SpaceTypeParam(M2) eq 0 or SpaceTypeParam(M1) mod SpaceTypeParam(M2) eq 0);
      when "cusp_new":
         return SpaceType(M2) in {"cusp_new", "cusp_newform"}
           and (SpaceTypeParam(M2) eq 0 or SpaceTypeParam(M1) mod SpaceTypeParam(M2) eq 0);
      when "eis_new":
         return SpaceType(M2) in {"eis_new", "eis_newform"}
           and (SpaceTypeParam(M2) eq 0 or SpaceTypeParam(M1) mod SpaceTypeParam(M2) eq 0);
      when "cusp_newform":
         if SpaceType(M2) in {"cusp", "cusp_new", "new"} then
            return true;
         elif SpaceType(M2) eq "cusp_newform" then
            if WhichNewform(M1) ne 0 and WhichNewform(M2) ne 0 then
               return WhichNewform(M1) eq WhichNewform(M2);
            else  // one of the strange situations where we don't know, use q-exp
               return M1 eq M2;      
            end if;
         else
            return false;
         end if;
      when "eis_newform":
         if SpaceType(M2) in {"eis", "eis_new", "new"} then
            return true;
         elif SpaceType(M2) eq "eis_newform" then
            if WhichNewform(M1) ne 0 and WhichNewform(M2) ne 0 then
               return WhichNewform(M1) eq WhichNewform(M2);
            else  // one of the strange situations where we don't know, use q-exp
               return M1 eq M2;      
            end if;
         else
            return false;
         end if;
      else:
         return false;          
   end case;
end intrinsic;

intrinsic 'in'(f::ModFrmElt, M::ModFrm) -> BoolElt
{}
   return Parent(f) eq M;
end intrinsic;


intrinsic IsNewform(f::ModFrmElt) -> BoolElt
{True if f was created using Newform.}
   return assigned f`is_newform and f`is_newform;
end intrinsic;

intrinsic IsEisensteinSeries(f::ModFrmElt) -> BoolElt
{True if f was created using EisensteinSeries.}
   return assigned f`eisenstein;
end intrinsic;

intrinsic EisensteinData(f::ModFrmElt) -> Tup
{The data <chi, psi, t, chi', psi'> that defines the Eisenstein series f.}
   require assigned f`eisenstein : "Argument 1 is not an Eisenstein series.";
   return f`eisenstein;
end intrinsic

intrinsic IsCuspidalNewform(f::ModFrmElt) -> BoolElt
{True if f is cuspidal and was created using the Newform intrinsic.}
   return IsNewform(f) and not IsEisensteinSeries(f);
end intrinsic;


intrinsic IsNew(M::ModFrm) -> BoolElt
{True if M is contained in the new subspace of the ambient space of M.}
   if not assigned M`is_new then
      if M`type in {"new", "cusp_new", "eis_new", "eis_newform", "cusp_newform"} then
         M`is_new := true;
      elif assigned M`dimension and M`dimension eq 0 then
         M`is_new := true;
      elif Dimension(M) eq Dimension(NewSubspace(M)) then
         M`is_new := true;
      else
         M`is_new := false;
      end if;
   end if;
   return M`is_new;
end intrinsic;


intrinsic AmbientSpace(M::ModFrm) -> ModFrm
{The ambient space that contains M.}
   if IsAmbientSpace(M) then
      return M;
   end if;
   assert assigned M`ambient_space;
   return M`ambient_space;
end intrinsic;   

intrinsic VectorSpace(M::ModFrm : Ring:=BaseRing(M) ) -> ModTupRng, Map, Map
{Same as RSpace(M)}
   return RSpace(M : Ring:=Ring);
end intrinsic;

intrinsic RSpace(M::ModFrm : Ring:=BaseRing(M) ) -> ModTupRng, Map, Map
{The abstract free module isomorphic to the given space of modular forms M,
over the same base ring, and a map to M (with inverse).}
   V := RSpace(BaseRing(M), Dimension(M));
   VtoM := hom<V -> M | x :-> M!x, x :-> V!Eltseq(x) >;
   return V, VtoM, Inverse(VtoM);
end intrinsic;

function AssociatedSpaceOverZ(M)
   assert Type(M) eq ModFrm;
   if not assigned M`associated_space_over_z then
      assert Type(BaseRing(M)) eq RngInt;
      return M;
   end if;
   return M`associated_space_over_z;
end function;

intrinsic Precision(M::ModFrm) -> RngIntElt
{The default printing precision for elements of M.}
   if not IsAmbientSpace(M) then
      return Precision(AmbientSpace(M));
   end if;
   if not assigned M`default_precision or M`default_precision eq -1 then
      M`default_precision := 12;
   end if;
   return M`default_precision;
end intrinsic;

intrinsic SetPrecision(M::ModFrm, prec::RngIntElt)
{Set the default printing precision for elements of M.}
   requirege prec,1;
   if not IsAmbientSpace(M) then
      SetPrecision(AmbientSpace(M),prec);
   else
      M`default_precision := prec;
   end if;
end intrinsic;

intrinsic RaisePrecision(M::ModFrm, prec::RngIntElt)
{Set the default printing precision for elements of M to the given value 
 if this is higher than the current precision.}
   if prec gt GetPrecision(M) then SetPrecision(M,prec); end if;
end intrinsic;

intrinsic Eltseq(f::ModFrmElt) -> SeqEnum
{The sequence [a1, ..., an] such that
 f = a1*g_1 + ... + an*g_n, where
 g_1, ..., g_n is the basis of the parent of f.}
   if not assigned f`element then
      // Steve made the following change, which is necessary now that 
      // coercion requires the answer to be uniquely determined. 
      // (In any case, the coercion would have been incorrect before.)
      M := Parent(f);
      g := M! PowerSeries(f, PrecisionBound(M:Exact)); 
    //g := Parent(f)!PowerSeries(f);
      f`element := g`element;
   end if;
   return Eltseq(f`element);
end intrinsic;


function WhichNewform(M)
   assert Type(M) eq ModFrm;

   if assigned M`which_newform then
      return M`which_newform;
   else
      return 0;
   end if;
end function;

function Element(f)
   assert Type(f) eq ModFrmElt;   
   if not assigned f`element then
      dummy := Eltseq(f);
   end if;
   return f`element;
end function;
