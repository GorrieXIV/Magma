freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: subspaces.m

   $Header: /home/was/magma/packages/ModFrm/code/RCS/subspaces.m,v 1.6 2002/06/28 04:31:34 was Exp $

   $Log: subspaces.m,v $
   Revision 1.6  2002/06/28 04:31:34  was
   Fixed caching of new subspaces.  It was totally wrong before.

   Revision 1.5  2002/05/06 05:32:52  was
   Correct access via SpaceTypeParam.

   Revision 1.4  2002/04/18 23:26:28  was
   *** empty log message ***

   Revision 1.3  2002/04/13 07:27:05  was
   Added stuff for p-new subspaces.

   Revision 1.2  2001/05/30 18:57:30  was
   Created.

   Revision 1.1  2001/05/16 03:52:12  was
   Initial revision

      
 ***************************************************************************/


import "creation.m" : CopyOfDefiningModularFormsObject;

import "predicates.m": AssociatedSpaceOverZ,
                       SpaceType, 
                       SpaceTypeParam;

import "misc.m" :       EchelonPowerSeriesSequence;

function MakeSubspace(M, type, param)
   assert Type(M) eq ModFrm;
   assert Type(type) eq MonStgElt;
   assert IsAmbientSpace(M);
   assert type in {"zero", "ambient", "cusp", "cusp_half_int", "eis", "new", "cusp_new", "eis_new"};

   if type eq "ambient" then
      return M;
   end if;

   if type eq "zero" then
      return ZeroSubspace(M);
   end if;

   function MakeSpaceWithType()
      S := CopyOfDefiningModularFormsObject(M);
      delete S`dimension;
      S`ambient_space := M;
      S`type := type;
      S`type_param := param;
      if Type(BaseRing(S)) ne RngInt then
         MZ := AssociatedSpaceOverZ(M);
         case type: 
            when "cusp", "cusp_half_int":
               A := CuspidalSubspace(MZ);
            when "eis":
               A := EisensteinSubspace(MZ);
            when "new":
               A := NewSubspace(MZ,param);
            when "cusp_new":
               A := NewSubspace(CuspidalSubspace(MZ),param);
            when "eis_new":
               A := NewSubspace(EisensteinSubspace(MZ),param);
            else
               error "Bug in subspaces.m";
         end case;
         S`associated_space_over_z := A;
      end if;
      return S;
   end function;


   case type:
      when "cusp", "cusp_half_int":
         if not assigned M`cusp then
            M`cusp := MakeSpaceWithType();
         end if;
         return M`cusp;
      when "eis":
         if not assigned M`eis then
            M`eis := MakeSpaceWithType();
         end if;
         return M`eis;

      when "new":
         if not assigned M`new then
            M`new := [* *];
         end if;
         if exists(i) { i : i in [1..#M`new] | M`new[i][1] eq param} then
            return M`new[i][2];
         end if;
         Append(~M`new,<param,MakeSpaceWithType()>);
         return M`new[#M`new][2];

      when "cusp_new":
         if not assigned M`cusp_new then
            M`cusp_new := [* *];
         end if;
         if exists(i) { i : i in [1..#M`cusp_new] | M`cusp_new[i][1] eq param} then
            return M`cusp_new[i][2];
         end if;
         Append(~M`cusp_new,<param,MakeSpaceWithType()>);
         return M`cusp_new[#M`cusp_new][2];


      when "eis_new":
         if not assigned M`eis_new then
            M`eis_new := [* *];
         end if;
         if exists(i) { i : i in [1..#M`eis_new] | M`eis_new[i][1] eq param} then
            return M`eis_new[i][2];
         end if;
         Append(~M`eis_new,<param,MakeSpaceWithType()>);
         return M`eis_new[#M`eis_new][2];

      else:
          assert false;
   end case;
   
end function;


intrinsic CuspidalSubspace(M::ModFrm) -> ModFrm
{The cuspidal subspace of M.}
   if not assigned M`cuspidal_subspace then
      if assigned M`dimension and M`dimension eq 0 then
         return M;
      end if;
      if SpaceType(M) in {"full","full_half_int","new"} then 
         vprint ModularForms : "ModularForms: Computing cuspidal subspace.";
      end if;
      A := AmbientSpace(M);
      case SpaceType(M):
         when "full":
            M`cuspidal_subspace := MakeSubspace(A, "cusp", 0);
         when "full_half_int":
            M`cuspidal_subspace := MakeSubspace(A, "cusp_half_int", 0);
         when "cusp", "cusp_new", "cusp_newform", "cusp_half_int":
            return M;
         when "eis", "eis_new", "eis_newform":
            M`cuspidal_subspace := MakeSubspace(A, "zero", 0);
         when "new":
            M`cuspidal_subspace := MakeSubspace(A, "cusp_new", 0);            
         else:
            error "Typo in CuspidalSubspace." ;
      end case;
   end if;
   if assigned M`cuspidal_subspace then
      return M`cuspidal_subspace;
   end if;
   error "CuspidalSubspace -- bug.";
end intrinsic;


intrinsic EisensteinSubspace(M::ModFrm) -> ModFrm
{The Eisenstein subspace of M.}
   if not assigned M`eisenstein_subspace then
      if assigned M`dimension and M`dimension eq 0 then
         return M;
      end if;
      A := AmbientSpace(M);
      case SpaceType(M):
         when "full":
            vprint ModularForms : "ModularForms: Computing eisenstein subspace.";
            M`eisenstein_subspace := MakeSubspace(A, "eis", 0);
         when "full_half_int":
            error "Eisenstein forms not implemented for half-integral weight";
         when "cusp", "cusp_new", "cusp_newform", "cusp_half_int":
            M`eisenstein_subspace := MakeSubspace(A, "zero", 0);
         when "eis", "eis_new", "eis_newform": 
            M`eisenstein_subspace := true;
            return M;
         when "new":
            vprint ModularForms : "ModularForms: Computing eisenstein subspace.";
            M`eisenstein_subspace := MakeSubspace(A, "eis_new", 0);      
         else:
            error "Typo in EisensteinSubspace." ;
      end case;
   end if;
   if Type(M`eisenstein_subspace) eq BoolElt then
      return M;
   end if;
   return M`eisenstein_subspace;
   error "EisensteinSubspace -- bug.";
end intrinsic;

intrinsic NewSubspace(M::ModFrm) -> ModFrm
{The new subspace of M.}
   return NewSubspace(M, 0);
end intrinsic;

intrinsic NewSubspace(M::ModFrm, p::RngIntElt) -> ModFrm
{The p-new subspace of M.}
   require IsPrime(p) or p eq 0 : "Argument 2 must be prime.";
   vprint ModularForms : "ModularForms: Computing new subspace.";
   if assigned M`dimension and M`dimension eq 0 then
      return M;
   end if;
   if not assigned M`new_subspace then
      M`new_subspace := [* *];
   end if;
   if exists(i) { i : i in [1..#M`new_subspace] | M`new_subspace[i][1] eq p} then
      return M`new_subspace[i][2];
   end if;

   A := AmbientSpace(M);
   case SpaceType(M):
      when "full":
         N := MakeSubspace(A, "new", p);
         Append(~M`new_subspace, <p,N>);
         return N;
      when "cusp":
         N := MakeSubspace(A, "cusp_new", p);
         Append(~M`new_subspace, <p,N>);
         return N;
      when "eis":
         N := MakeSubspace(A, "eis_new", p);
         Append(~M`new_subspace, <p,N>);
         return N;
      when "full_half_int", "cusp_half_int":
         error "Newforms not implemented for half-integral weight";
      when "new", "cusp_new", "eis_new":
         if SpaceTypeParam(M) eq p then
            return M;
         elif SpaceTypeParam(M) eq 0 then
            N := MakeSubspace(A,M`type, p);            
         else
            // This isn't yet fully supported, so give an error.
            error "Construction of NewSubspace of the type you asked for is not yet supported.";
            N := MakeSubspace(A,M`type, p*SpaceTypeParam(M));
         end if;
         Append(~M`new_subspace, <p,N>);
         return N;
      when "eis_newform", "cusp_newform":
         return M;
      else:
         error "Bug in NewSubspace." ;
   end case;
end intrinsic;

intrinsic ZeroSubspace(M::ModFrm)  -> ModFrm
{The trivial subspace of M.}
   S := CopyOfDefiningModularFormsObject(M);
   S`dimension := 0;
   S`type := "zero";
   S`ambient_space := (assigned M`ambient_space) select M`ambient_space else  M;
   return S;   
end intrinsic;

/*
// This is a hack by Steve ... I've decided this is a bad idea (use VectorSpace instead).
//   sub<M|fs> -> ModFrm 
// where M::ModFrm, fs::SeqEnum[ModFrmElt] or ModFrmElt or ModFrm
// These spaces are not (necessarily) intended to have full functionality.
intrinsic SubConstr(M::ModFrm, fs::. ) -> ModFrm, .
{}
   // Note: not allowed to use require/error ...
   
   // make fs a sequence
   if Type(fs) eq ModFrmElt then fs := [fs];  // so that sub<M|f> will work
   elif Type(fs) eq ModFrm then fs := Basis(fs);
   elif Type(fs) ne SeqEnum then 
      return "This data doesn't define a subspace", _; 
   end if;    
   if not &and[f in M : f in fs] then
      if not &and[IsCoercible(M,f) : f in fs] then 
         return "Forms are not contained in the given space", _; 
      else fs := [M!f : f in fs]; end if; 
   end if;

   // make fs an independent basis
   RSpaceM, toM := RSpace(M);
   gens := Basis(sub< RSpaceM | [f @@ toM : f in fs] >);
   fs := [gen @ toM : gen in gens];

   S := New(ModFrm);
   S`ambient_space := IsAmbientSpace(M) select M else M`ambient_space;
   S`is_gamma1 := M`is_gamma1;
   if assigned M`base_ring then S`base_ring := M`base_ring; end if;
   if assigned M`default_precision then S`default_precision := M`default_precision; end if;
   if assigned M`dirichlet_character then S`dirichlet_character := M`dirichlet_character; end if;
   if assigned M`is_cuspidal then S`is_cuspidal := M`is_cuspidal; end if;
   if assigned M`is_eisenstein then S`is_eisenstein := M`is_eisenstein; end if;
   if assigned M`is_new then S`is_new := M`is_new; end if;
   if assigned M`level then S`level := M`level; end if;
   if assigned M`precision_bound then S`precision_bound := M`precision_bound; end if;
   if assigned M`q_name then S`q_name := M`q_name; end if;
   if assigned M`weight then S`weight := M`weight; end if;
   S`type := "subspace"; // non-standard type, so that functions that check the type will fail
   S`dimension := #fs;
   if assigned S`default_precision and S`default_precision lt Dimension(M)+1 then 
      SetPrecision(S, Dimension(M)+1); end if;
   if assigned M`q_expansion_basis then  // it must be, due to the RSpaceM stuff above
      prec := M`q_expansion_basis[1];
      qexps := EchelonPowerSeriesSequence([ qExpansion(f) : f in fs ]);
      S`q_expansion_basis := <prec, qexps>; end if;
   S`basis := fs;  // this is quick and dirty!  The fs are ModFrmElt's in M 
   return S, _;
end intrinsic;


intrinsic 'meet'(M1::ModFrm, M2::ModFrm) -> ModFrm
{The intersection of two subspaces inside a space of modular forms}
   M := AmbientSpace(M1);
   require AmbientSpace(M2) eq M : "These two spaces do not have a common ambient space";
   V, VtoM := RSpace(M);
   V1 := sub< V | [(M!f) @@ VtoM : f in Basis(M1)] >;
   V2 := sub< V | [(M!f) @@ VtoM : f in Basis(M2)] >;
   return sub< M | [v @ VtoM : v in Basis(V1 meet V2)] >;
end intrinsic;
*/
