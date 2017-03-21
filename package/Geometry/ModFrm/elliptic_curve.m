freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: elliptic_curve.m

   $Header: /home/was/magma/packages/ModFrm/code/RCS/elliptic_curve.m,v 1.2 2002/10/26 22:49:27 was Exp $

   $Log: elliptic_curve.m,v $
   Revision 1.2  2002/10/26 22:49:27  was
   .

   Revision 1.1  2001/05/30 18:51:59  was
   Initial revision

      
 ***************************************************************************/


import "newforms.m" : GiveNewformItsParent;

intrinsic ModularForm(E::CrvEll) -> ModFrmElt
{The modular form associated to E.}
   require Type(BaseRing(E)) in {FldRat, RngInt} : 
        "Argument 1 must be defined over the rationals.";
   f := New(ModFrmElt);
   M := ModularForms(Gamma0(Conductor(E)),2);
   f`parent := M;
   f`elliptic_curve := E;
   f`degree := 1;
   f`is_newform := true;
   GiveNewformItsParent(f,0);
   return f;
end intrinsic;



intrinsic EllipticCurve(f::ModFrmElt) -> CrvEll
{An elliptic curve with associated modular form f.}
   require (not IsRingOfAllModularForms(Parent(f))) and
           Type(BaseRing(Parent(f))) in {FldRat, RngInt} and
           Weight(f) eq 2 and
           IsGamma0(Parent(f)) and 
           (not IsEisensteinSeries(f)) and
           Degree(f) eq 1 and
           (IsNewform(f) or assigned f`elliptic_curve) :
           "Argument 1 must be a newform in S_2(Gamma_0(N))."; 
   if not assigned f`elliptic_curve then
      assert assigned f`mf_modular_symbols;
      f`elliptic_curve := EllipticCurve(f`mf_modular_symbols);
   end if;
   return f`elliptic_curve;
end intrinsic;
