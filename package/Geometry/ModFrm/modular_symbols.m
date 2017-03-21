freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: modular_symbols.m

   $Header: /home/was/magma/packages/ModFrm/code/RCS/modular_symbols.m,v 1.9 2002/10/26 22:49:01 was Exp $

   $Log: modular_symbols.m,v $
   Revision 1.9  2002/10/26 22:49:01  was
   .

   Revision 1.8  2002/05/06 05:31:21  was
   Added correct call to SpaceTypeParam.

   Revision 1.7  2002/04/13 05:24:31  was
   *** empty log message ***

   Revision 1.6  2002/01/18 06:44:45  was
   minor typo in ModularSymbols(modfrmelt)

   Revision 1.5  2002/01/18 06:40:50  was
   Added ModularSymbols for modular forms.

   Revision 1.4  2001/07/08 18:40:23  was
   Fixed a verbose print line in ModularSymbols.

   Revision 1.3  2001/05/30 18:55:57  was
   Created.

   Revision 1.2  2001/05/16 04:07:21  was
   *** empty log message ***

   Revision 1.1  2001/05/16 03:51:59  was
   Initial revision

      
 ***************************************************************************/

import "predicates.m": SpaceTypeParam;

forward MinimalCharacterModularSymbols,
        MF_ModularSymbols,
        MF_NewformModularSymbols;

function MinimalCharacterModularSymbols(eps, k, sign)
   assert Type(eps) eq GrpDrchElt;
   assert Type(k) eq RngIntElt;
   assert Type(sign) eq RngIntElt; 
   assert sign in {-1, 0, 1};
   assert k ge 2;
   assert Type(BaseRing(eps)) in {FldRat, FldCyc};

   e := MinimalBaseRingCharacter(eps);
   return ModularSymbols(e,k,sign);
end function;


function MF_ModularSymbols(M, sign)
   // The sequence of characteristic 0 spaces of modular symbols 
   // with given sign associated to M, when this makes sense.
   assert Type(M) eq ModFrm;
   assert Type(sign) eq RngIntElt;
   if not (Weight(M) ge 2 and Weight(M) in Integers()) then
      error "Argument 1 must have integer weight at least 2.";
   end if;
   if not (sign in {-1,0,1}) then 
      error "Argument 2 must be in {-1,0,1}.";
   end if;
   if IsAmbientSpace(M) and not assigned M`mf_modular_symbols then
      vprintf ModularForms,2 : "Computing modular symbols space with sign %o.\n", sign;
   end if;

   if not assigned M`mf_modular_symbols then
      M`mf_modular_symbols := [* false,false,false *];
   end if;
   if Type(M`mf_modular_symbols[sign+2]) eq BoolElt then
      if not IsAmbientSpace(M) and 
                        (assigned M`dimension and M`dimension eq 0) then
          return [ZeroSubspace(m) : m in MF_ModularSymbols(AmbientSpace(M),sign)];
      end if;
      param := SpaceTypeParam(M);
      case M`type: 
         when "full":
            eps := DirichletCharacters(M);
            M`mf_modular_symbols[sign+2] := 
                    [MinimalCharacterModularSymbols(e, Weight(M), sign) : e in eps];
         when "cusp":
            M`mf_modular_symbols[sign+2] := 
                 [CuspidalSubspace(m) : m in MF_ModularSymbols(AmbientSpace(M),sign)];
         when "eis":
            M`mf_modular_symbols[sign+2] := 
                 [EisensteinSubspace(m) : m in MF_ModularSymbols(AmbientSpace(M),sign)];
         when "new":
//            require false : 
//               "If argument 1 is new we require that it also be be cuspidal.";
            M`mf_modular_symbols[sign+2] := 
                 [param eq 0 select NewSubspace(m) else NewSubspace(m,param) : 
                                            m in MF_ModularSymbols(AmbientSpace(M),sign)];
         when "cusp_new":
            M`mf_modular_symbols[sign+2] := 
                 [param eq 0 select NewSubspace(m) else NewSubspace(m,param) : 
                                  m in MF_ModularSymbols(CuspidalSubspace(AmbientSpace(M)),sign)];
         when "eis_new":
//            require false : 
//               "If argument 1 is new we require that it also be be cuspidal.";
            M`mf_modular_symbols[sign+2] := 
                 [param eq 0 select NewSubspace(m) else NewSubspace(m,param) : 
                                  m in MF_ModularSymbols(EisensteinSubspace(AmbientSpace(M)),sign)];
         when "cusp_newform": 
            modsym := ChangeSign(MF_NewformModularSymbols(M`made_from_newform),sign);
            All := MF_ModularSymbols(AmbientSpace(M),sign);
            M`mf_modular_symbols[sign+2] := [DirichletCharacter(A) eq DirichletCharacter(modsym) 
                                          select modsym else ZeroSubspace(A) : A in All];
         when "eis_newform":
            error "Modular symbols of eisenstein newform parents is not yet supported.";

         else:
            assert false;
      end case;

   end if;
   return M`mf_modular_symbols[sign+2];
end function;

function MF_NewformModularSymbols(f)
   //  The space of modular symbols attached to a newform f, if there is one.
   assert Type(f) eq ModFrmElt;
   if not assigned f`mf_modular_symbols then 
      error "I don't know how to compute the associated space of modular symbols (yet).";
   end if;
   return f`mf_modular_symbols;
end function;




intrinsic ModularSymbols(M::ModFrm, sign::RngIntElt) -> ModSym
{The space of modular symbols over Q with given sign corresponding to the space M of modular forms.}
   if not (Weight(M) ge 2 and Weight(M) in Integers()) then
      error "Argument 1 must have integer weight at least 2.";
   end if;
   if not (sign in {-1,0,1}) then 
      error "Argument 2 must be in {-1,0,1}.";
   end if;
   m := MF_ModularSymbols(M,sign);
   return DirectSumRestrictionOfScalarsToQ(m);  
end intrinsic;

intrinsic ModularSymbols(M::ModFrm) -> ModSym
{The space of modular symbols over Q corresponding to the space M of modular forms.}
   return ModularSymbols(M,0);
end intrinsic;

intrinsic ModularSymbols(f::ModFrmElt, sign::RngIntElt) -> ModSym
{The space of modular symbols over Q with given sign corresponding to the newform f.}
   require IsNewform(f) : "Argument 1 must be newform.";
   require sign in {-1,0,1} : "Argument 2 must be either -1, 0, or 1.";
   require Characteristic(BaseRing(Parent(f))) eq 0 : "Argument 1 must be in characteristic 0.";

   return DirectSumRestrictionOfScalarsToQ(MF_ModularSymbols(Parent(f),sign));
end intrinsic;


intrinsic ModularSymbols(f::ModFrmElt) -> ModSym
{The space of modular symbols over Q corresponding to the newform f.}
   require IsNewform(f) : "Argument 1 must be newform.";
   return ModularSymbols(f,0);
end intrinsic;
