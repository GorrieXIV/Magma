freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: newforms.m

   $Header: /home/was/magma/packages/ModFrm/code/RCS/newforms.m,v 1.12 2002/05/30 10:03:43 was Exp was $

   $Log: newforms.m,v $

   October 2007 (Steve)
   Set AllCharacters:=true in call to EisensteinSeries in Newforms. 
   This is so that the dimension of the new Eisenstein subspace comes out right.

   Revision 1.12  2002/05/30 10:03:43  was
   ..

   Revision 1.11  2002/05/30 09:52:23  was
   but characteristic p^2 is not so easy...

   Revision 1.10  2002/05/30 09:50:49  was
   Extended "Newforms" so that it works with spaces in characteristic p.  This was dead easy!

   Revision 1.9  2002/05/30 09:36:02  was
   Newforms can only use elliptic curve database shortcut when N > 450, because
   Cremona's ordering is not the same as mine! (And I haven't typed in a conversion
   table between the two orderings.)  -- William

   Revision 1.8  2002/05/21 18:30:19  was
   nothing. (debuging "breakpoints")

   Revision 1.7  2002/05/04 18:33:43  was
   *** empty log message ***

   Revision 1.6  2002/05/04 17:37:15  was
   I removed the "bug" from GivenNewformItsParent (which makes things
   more efficient), because (1) somebody complained, and (2) setting
   the field correctly should *not* be so inefficient!  I think the reason
   it is must involve IsIrreducible being absurdly slow, which has presumbly
   been fixed.

   Revision 1.5  2002/03/11 23:19:10  was
   Working on "Eigenforms" command.

   Revision 1.4  2001/07/26 19:26:58  was
   Changed "GiveNewformItsParent" so the parent has the "wrong" base field.
   It's EXTREMELY time consuming, in some cases, to compute the right parent,
   and their is no benefit at all to having the right parent.

   Revision 1.3  2001/06/30 03:12:13  was
   Fixed a small bug in GiveNewformItsParent.

   Revision 1.2  2001/05/30 18:56:09  was
   Created.

   Revision 1.1  2001/05/16 03:52:02  was
   Initial revision

      
 ***************************************************************************/


// The following group of functions are all for modular forms spaces over Q.

forward CreateNewformsFromEisensteinSeries,
        CreateNewformsFromModularSymbolsNewform,
        CreateNewformsFrom_qExpansion;

import "misc.m" : IsogenyCodeToInteger;
import "creation.m" : CopyOfDefiningModularFormsObject;
import "modular_symbols.m" : MF_ModularSymbols;
import "predicates.m": SpaceType, AssociatedSpaceOverZ;

procedure GiveNewformItsParent(f, which_newform)
   assert Type(f) eq ModFrmElt;

   M := CopyOfDefiningModularFormsObject(Parent(f));
   M`dimension := Degree(f);
   if assigned f`mf_modular_symbols then
      M`mf_modular_symbols := [* false, false, f`mf_modular_symbols *];
   end if;
   if IsCuspidalNewform(f) then
      M`type := "cusp_newform";
   else
      M`type := "eis_newform"; 
   end if;

   R := BaseRing(Parent(PowerSeries(f,1)));
   
   MR := BaseExtend(M,R);

   MR`made_from_newform := f;

   MR`ambient_space := BaseExtend(AmbientSpace(Parent(f)), R);
//   MR`ambient_space := AmbientSpace(Parent(f));

   MR`which_newform := which_newform;
   f`parent := MR;
   delete f`element;
end procedure;

procedure GiveAllNewformsTheirParents(new_forms, first)
   
   which_newform := first;
   for orb in new_forms do
      for f in orb do
         GiveNewformItsParent(f,which_newform);
         which_newform +:= 1;
      end for;
   end for;
end procedure;

function NumberOfGalQbarOverQConjugateNewforms(A)
   assert Type(A) eq ModSym;
   assert Type(BaseField(A)) in {FldRat, FldCyc};

   // The formula is simple because the ModularSymbols(ModFrm) 
   // intrinsic is supposed to return a character defined over 
   // a field of minimal degree.
   assert EulerPhi(Order(DirichletCharacter(A))) eq Degree(BaseField(A));

   return Dimension(A) * Degree(BaseField(A));
   
end function;


function NumberOfGalQbarOverQConjugateEisensteinSeries(f)
   assert Type(f) eq ModFrmElt;
   assert IsEisensteinSeries(f);

   chi, psi := Explode(EisensteinData(f));
   m := LCM(CyclotomicOrder(BaseRing(chi)), CyclotomicOrder(BaseRing(psi)));
   return EulerPhi(m);

end function;


function CreateNewformsFromModularSymbolsNewform(M, A)
   assert Type(M) eq ModFrm;
   assert Type(A) eq ModSym;
   assert Type(BaseField(A)) in {FldRat, FldCyc};

   ans := [* *];
   for i in [1..NumberOfGalQbarOverQConjugateNewforms(A)] do
      f := New(ModFrmElt);
      f`mf_modular_symbols := A;
      f`parent := M;
      f`is_newform := true;
      f`which_conjugate := i; 
      Append(~ans, f);
   end for;
   return ans;

end function;


function CreateNewformsFrom_qExpansion()
// coefficients of the q-exp, got using hecke operators, say; e.g., weight 1.)
   error "CreateNewformsFrom_qExpansion -- Not programmed.";
end function;

function CreateNewformsFromBrandtModuleData()
   error "CreateNewformsFromBrandtModuleData -- Not programmed.";
end function;


function ComputeCuspidalNewformsUsingModuleOfSupersingularPoints(M)
   assert Type(M) eq ModFrm;

   error "ComputeCuspidalNewformsUsingModuleOfSupersingularPoints -- Not programmed.";
end function;

function ComputeCuspidalNewformsUsingBrandtModule(M)
   assert Type(M) eq ModFrm;

   error "ComputeCuspidalNewformsUsingBrandtModule -- Not programmed.";

end function;




function ComputeCuspidalNewformsUsingModularSymbols(M, Proof)
   assert Type(M) eq ModFrm;
   assert IsCuspidal(M);

   modsym := [NewSubspace(m) : m in MF_ModularSymbols(M,+1)];

   D := &cat [SortDecomposition(NewformDecomposition(m : Proof := Proof)) : m in modsym];
   ans := [* *];
   for A in D do
      Append(~ans, CreateNewformsFromModularSymbolsNewform(M, A));
   end for;
   return ans;
end function;




function DivideNewEisensteinSeriesIntoOrbits(E)
   assert Type(E) eq List;
   if #E eq 0 then
      return [* *];
   end if;
   assert Type(E[1]) eq ModFrmElt;
   assert IsEisensteinSeries(E[1]);

   ans := [* *];
   while #E gt 0 do
      f := E[1];
      Remove(~E,1);
      orbit := [* f *];
      orbit[1]`which_conjugate := 1;
      if #E gt 0 then
         chi, psi, t, chi_big, psi_big := Explode(EisensteinData(f));  
         m := LCM(Order(chi),Order(psi));
         which_conjugate := 2;
         for i in [j : j in [2..m-1] | GCD(j,m) eq 1] do
            chi_i := chi_big^i;
            psi_i := psi_big^i;
            pos := 0;
            for k in [1..#E] do
               _, _, _, chi_k, psi_k := Explode(EisensteinData(E[k]));
               if chi_i eq chi_k and psi_i eq psi_k then
                  pos := k;
                  break;
               end if;
            end for;
            assert pos ne 0;
            Append(~orbit, E[pos]);
            orbit[#orbit]`which_conjugate := which_conjugate;
            orbit[#orbit]`first_conjugate := orbit[1];
            which_conjugate +:= 1;
            Remove(~E,pos);
         end for;
      end if;
      assert #orbit eq Degree(orbit[1]);
      Append(~ans, orbit);
   end while;   
   return ans;
end function;

function ComputeEisensteinNewforms(M)
   assert Type(M) eq ModFrm;

   // Let E be the collection of new Eisenstein series.
   E := [* *];
   for f in EisensteinSeries(AmbientSpace(M) : AllCharacters) do
      chi, psi, t := Explode(EisensteinData(f));  
      if t eq 1 or (Weight(M) eq 2 and IsPrime(t) and t eq Level(M)) then
         LR := Conductor(chi)*Conductor(psi);
         if LR eq Level(M) or (Weight(M) eq 2 and LR eq 1) then
            Append(~E,[* f *]);
            E[#E][1]`is_newform := true;
         end if;
      end if;
   end for;

   return E;
//   return DivideNewEisensteinSeriesIntoOrbits(E);
end function;

function ComputeCuspidalNewformsUsingHeckeOperators(M)
   assert Type(M) eq ModFrm;
end function;

intrinsic NumberOfNewformClasses(M::ModFrm : Proof := true) -> RngIntElt
{The number of Galois conjugacy-classes of newforms associated to M.}
   require Characteristic(BaseRing(M)) eq 0 : 
           "Argument 1 must have characteristic 0.";

   return #Newforms(M : Proof := Proof);   
end intrinsic;

intrinsic Newform(M::ModFrm, i::RngIntElt,  
                  j::RngIntElt : Proof := true) -> ModFrmElt
{The jth Galois-conjugate newform in the ith orbit.}
   require Characteristic(BaseRing(M)) eq 0 : 
           "Argument 1 must have characteristic 0.";
   requirege i, 1;
   requirege j, 1;
   N := Newforms(M : Proof := Proof);
   require i le #N : "Argument 2 must be at most", #N;
   orbit := N[i];
   require j le #orbit : "Argument 3 must be at most", #orbit;
   return orbit[j];
end intrinsic;

intrinsic Newform(M::ModFrm, i::RngIntElt : Proof := true) -> ModFrmElt
{The first Galois-conjugate newform in the ith orbit.}
   require Characteristic(BaseRing(M)) eq 0 : 
           "Argument 1 must have characteristic 0.";

   requirege i, 1;
   N := Newforms(M : Proof := Proof);
   require i le #N : "Argument 2 must be at most", #N;
   return N[i][1];
end intrinsic;

intrinsic Newform(E::CrvEll) -> ModFrmElt
{Same as ModularForm(E)}
   return ModularForm(E);
end intrinsic;

intrinsic Newforms(M::ModFrm : Proof := true) -> List
{List of the newforms associated to M, divided up into Galois orbits.}

/*   require Characteristic(BaseRing(M)) eq 0 : 
           "Argument 1 must have characteristic 0.";
*/
   if SpaceType(M) in {"cusp_newform", "eis_newform"} then
      return M`made_from_newform;
   end if;

   if not assigned M`newforms then
      if Characteristic(BaseRing(M)) ne 0 then
         if not IsPrime(Characteristic(BaseRing(M))) then
            require false : "The characteristic of the base ring of argument 1 must be 0 or prime.";
         end if;
         M0 := AssociatedSpaceOverZ(M);
         ans := [* *];
         for i in [1..NumberOfNewformClasses(M0)] do
            f := Newform(M0,i);   
            fmod := Reductions(f,Characteristic(BaseRing(M)));
            for g in fmod do
               Append(~ans,g);
            end for;
         end for;
         M`newforms := ans;
         return M`newforms;
      end if;   

      if assigned M`dimension and M`dimension eq 0 then
         M`newforms := [* *];
         return M`newforms;
      end if;
      if not Weight(M) in Integers() or Weight(M) lt 2 then
         require false : "Newforms are not available yet for weight 1 and half integral weight spaces.";
      end if;
      if IsCuspidal(M) then
         new_forms := ComputeCuspidalNewformsUsingModularSymbols(M, Proof);
         GiveAllNewformsTheirParents(new_forms,1);
      elif IsEisenstein(M) then
         new_forms := ComputeEisensteinNewforms(M); 
         first := Dimension(NewSubspace(CuspidalSubspace(AmbientSpace(M)))) + 1;
         GiveAllNewformsTheirParents(new_forms, first);
      else
         new_forms := Newforms(CuspidalSubspace(M) : Proof := Proof)
                           cat 
                      Newforms(EisensteinSubspace(M) : Proof := Proof);
      end if;
      M`newforms := new_forms;
   end if;
   return M`newforms;
end intrinsic;


intrinsic Newforms(I::[Tup], M::ModFrm  : Proof := true) -> SeqEnum
{
The newforms associated to M with prespecified eigenvalues.
Here I is a sequence 
   [< p_1, f_1(x)>,...,< p_n,f_n(x)>] 
of pairs.   Each pair consists 
of a prime number that does not divide
the level of M and a polynomial.
This intrinsic returns the set of 
newforms sum a_n q^n in M 
such that f_n(a_\{p_n\})=0.
}
   require Type(BaseRing(M)) in {FldRat, RngInt} : 
         "The space must be defined over the integer ring or rational field.";
   require IsCuspidal(M) : "The space must be cuspidal.";
   require Weight(M) ge 2 : "The space must have weight >= 2.";

   // Added June 2012, SRD
   U := Universe(I);
   require ISA(Type(U), SetCart) and Type(U[1]) eq RngInt and Type(U[2]) eq RngUPol:
          "The first argument must be a sequence of tuples of the form <p_i,f_i(x)>";
   require 1 eq 0 or forall{t : t in I | GCD(t[1],N) eq 1} where N is Level(M):
          "The integers contained in the first argument must be coprime to the level";
          // TO DO: I think what's really needed is that the space is p-new for these primes
          // TO DO: must the p_i be prime, as stated in doc?  I think it handles nonprimes

   ans := [* *];
   // First find the cuspidal newforms.
   if Dimension(CuspidalSubspace(M)) gt 0 then
      S := MF_ModularSymbols(CuspidalSubspace(M),+1);
      A := [Kernel(I, s) : s in S];
      D := &cat [SortDecomposition(NewformDecomposition(m : 
                                    Proof := Proof)) : m in A];
      for nf in D do
         Append(~ans, CreateNewformsFromModularSymbolsNewform(M, nf));
      end for;
   end if;

   // Second, the Eisenstein newforms.
   E := EisensteinSubspace(M);
   if Dimension(E) gt 0 then
      error "Cutting out eisenstein newforms not yet programmed.";
   end if;

   return ans;   
end intrinsic;


function IsNumeric(s)
   assert Type(s) eq MonStgElt;
   if #s eq 0 then
      return false;
   end if;
   for i in [1..#s] do 
      if not ( (s[i] ge "0") and (s[i] le "9") ) then
         return false;
      end if;
   end for; 
   return true;
end function;

intrinsic Newform(label::MonStgElt : Proof := true)  -> ModFrmElt
{The Galois-conjugacy class(es) of newforms described
by the label.  See the handbook for a description of the
notation used for the label.}
   return Newforms(label : Proof := Proof)[1];
end intrinsic;

intrinsic Newforms(label::MonStgElt : Proof := true)  -> ModFrmElt
{"} // "
   require #label gt 0 : "Invalid label.";
   // defaults
   group := "G0"; 
   k := 2;
   N := 1;
   iso := 1;
   if label[1] eq "G" then
      require #label ge 2 : "Invalid label."; 
      if label[2] eq "0" then
         group := "G0";
      elif label[2] eq "1" then
         group := "G1";
      else
         require false : "Invalid label.";          
      end if;
      require #label ge 3 and label[3] eq "N" : "Invalid label."; 
      s := &cat[label[i] : i in [4..#label]];
   else
      s := label;
   end if;


   sN := "";
   i := 1;
   while i le #s and s[i] ge "0" and s[i] le "9" do
      sN := sN cat s[i];
      i +:= 1;
   end while;
   require IsNumeric(sN) : "The format of argument 1 is invalid.";
   N := StringToInteger(sN);
   if i le #s and s[i] eq "k" then
      i +:= 1;
      sk := "";
      while i le #s and s[i] ge "0" and s[i] le "9" do
         sk := sk cat s[i];
         i +:= 1;
      end while;
      require IsNumeric(sk) : "The format of argument 1 is invalid.";
      k := StringToInteger(sk);
   end if;
   if i gt #s then
      iso := 0;
   else
      sIso := &cat [s[j] : j in [i..#s]];
      iso := IsogenyCodeToInteger(sIso);
      require iso ge 1 : "The format of argument 1 is invalid.";
   end if;

   if k eq 2 and iso gt 0 and N gt 450 then    // condition that N > 450 because Cremona's ordering is different.
      // first check in database.
      cremona := EllipticCurveDatabase();
      if iso le LargestConductor(cremona) then
         if iso le NumberOfIsogenyClasses(cremona,N) then
            return [* ModularForm(EllipticCurve(cremona,N,iso,1)) *];
         end if;
      end if;
   end if;

   if group eq "G0" then
      M := ModularForms(N,k);   
   else
      M := ModularForms(Gamma1(N),k);         
   end if;
   if iso eq 0 then
      return Newforms(M);
   end if;
   N := Newforms(CuspidalSubspace(M));

   if iso gt #N then
      E := Newforms(EisensteinSubspace(M));
      require iso le #E + #N : "The isogeny class is too large.";
      return E[iso-#N];
   end if;
   return N[iso];   

end intrinsic;


intrinsic DirichletCharacter(f::ModFrmElt) -> GrpDrchElt
{Suppose f is a newform, created using the Newform command.
This returns a Dirichlet character that is,
up to Galois conjugacy, the Nebentypus character of f.}
   if not assigned f`nebentype then
      if IsGamma0(Parent(f)) then
         f`nebentype :=  DirichletGroup(Level(Parent(f)))!1;
      elif assigned f`mf_modular_symbols then
         f`nebentype := DirichletCharacter(f`mf_modular_symbols);
      elif assigned f`eisenstein then
         f`nebentype := f`eisenstein[4]*f`eisenstein[5];
      else
         require false : "Unable to determine nebentype of f.";
      end if;
   end if;
   return f`nebentype;
end intrinsic;

intrinsic LinearCombinationOfEigenformsOverC(f::ModFrmElt) -> SeqEnum
{Write f as a complex linear combination of eigenforms for the 
anemic Hecke algebra.}
   require Type(BaseRing(Parent(f))) in {FldRat, RngInt} : 
     "Argument 1 must be defined over the integers or rationals.";

   
end intrinsic;


/*
intrinsic Eigenforms(M::ModFrm : Proof := true) -> List
{}
   require Characteristic(BaseRing(M)) eq 0 : 
           "Argument 1 must have characteristic 0.";
   if SpaceType(M) in {"cusp_newform", "eis_newform"} then
      return M`made_from_newform;
   end if;

   if not assigned M`eigenforms then
      M`eigenforms := [* *];
      if assigned M`dimension and M`dimension eq 0 then
         return M`eigenforms;
      end if;
      if not Weight(M) in Integers() or Weight(M) lt 2 then
         require false : "Eigenforms does not support weight 1 and half integral weight spaces yet.";
      end if;
      M`eigenforms := [* *];
      if assigned M`dirichlet_characters then   
         levels := [Conductor(eps) : eps in M`dirichlet_characters];
      else
         levels := [1];
      end if;
      for d in [n : n in Divisors(Level(M)) | #[x : x in levels | n mod x eq 0] gt 0 ] do
         Md := Newforms(M,d);
         for N in Newforms(Md) do
            for r in Divisors(Level(M) div d) do 
               FrobN := 
            end for;
            Append(M`eigenforms, FrobN);
         end for;
      end for;        
   end if;
   return M`eigenforms;
end intrinsic;
*/


/*
intrinsic FlattenNewformList(L::List) -> List
{}
   ans := [* *];
   for a in L do
      for b in a do
         Append(~ans, b); 
      end for;
   end for;
   return ans;
end intrinsic;
*/
