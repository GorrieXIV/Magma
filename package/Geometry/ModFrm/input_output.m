freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: creation.m

   $Header: /home/was/magma/packages/modform/code/RCS/input_output.m,v 1.1 2001/05/30 18:52:38 was Exp $

   $Log: input_output.m,v $
   Revision 1.1  2001/05/30 18:52:38  was
   Initial revision

      
 ***************************************************************************/

function PrintSideways(s)
   assert Type(s) in {SeqEnum, List};
   ans := "[";
   for i in [1..#s] do
      ans := ans*Sprintf("%o", s[i]);
      if i lt #s then
         ans := ans*", ";
      end if;
   end for;
   ans := ans*"]";
   return ans;
end function;

intrinsic Print(M::ModFrm, level::MonStgElt)
   {}
   
   if IsRingOfAllModularForms(M) then
      printf "All modular forms over %o", BaseRing(M);
      return;
   end if;

   dim_computed := assigned M`dimension and M`dimension ne -1;
   dim_string := not dim_computed and (level cmpeq "Minimal" or Weight(M) eq 1)
                 select "" else " and dimension "*IntegerToString(Dimension(M));

   if IsGamma0(M) then
       printf "Space of modular forms on Gamma_0(%o) of weight %o%o over %o.", 
       Level(M), Weight(M), dim_string, BaseRing(M);
   elif IsGamma1(M) then
       printf "Space of modular forms on Gamma_1(%o) of weight %o%o over %o.", 
       Level(M), Weight(M), dim_string, BaseRing(M);
   elif ( #chars eq 1 and Order(chars[1]) eq 2 where chars := DirichletCharacters(M) ) then
       printf "Space of modular forms on Gamma_1(%o) with character %o, weight %o,%o over %o.", 
       Level(M), DirichletCharacters(M)[1], Weight(M), dim_string, BaseRing(M);
   else
       chars := DirichletCharacters(M);
       assert #chars gt 0;
       printf "Space of modular forms on Gamma_1(%o) with character%o all conjugates of %o, weight %o,%o over %o.", 
       Level(M), #chars eq 1 select "" else "s", PrintSideways(chars),  
           Weight(M), dim_string, BaseRing(M);
   end if;
end intrinsic;

intrinsic Print(f::ModFrmElt, level::MonStgElt)
   {}
 
   if level ne "Minimal" or assigned f`q_expansion then
      printf "%o", PowerSeries(f);
   elif assigned f`element then 
      printf "%o", f`element;
   else 
      printf "Element of %o", Parent(f);
   end if;
end intrinsic;

intrinsic AssignNames(~M::ModFrm, s::[MonStgElt])
{Assign the string in S to be the variable name 
 used to print q-expansions of elements of M}
   require #s eq 1 : "Number of names must be 1.";
   M`q_name := s[1];
   // update stored q-expansions 
   // (we don't check the name every time, any more)
   if assigned M`q_expansion_basis then
      R := Universe(M`q_expansion_basis[2]);
      assert ISA(Type(R), RngSer);
      AssignNames(~R, [M`q_name]);
   end if;
end intrinsic;

// This looks like nonsense
intrinsic Name(M::ModFrm,i::RngIntElt) -> RngSerPowElt
   {Name the ith generator.}
   require i eq 1 : "Argument 2 must be 1";
   return PowerSeriesRing(BaseRing(M)).1;
end intrinsic;


/*
intrinsic Write(M::ModFrm, file::File)
{Write the space M of modular forms to the file.}
   error "Not written";
end intrinsic;

intrinsic ReadModFrm(file::File) -> ModFrm
{Read the next space of modular forms from the file.}
   error "Not written";
end intrinsic;

intrinsic Write(f::ModFrmElt, file::File)
{Write the modular form f to the file.}
   error "Not written";
end intrinsic;

intrinsic ReadModFrmElt(file::File) -> ModFrmElt
{Read the next modular form from the file.}
   error "Not written";
end intrinsic;

*/
