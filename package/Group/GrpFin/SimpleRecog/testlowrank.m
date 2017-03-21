freeze;

/*
   basic randomized test whether
   <rho> : <X> -> classical group
   is a homomorphism modulo scalars
*/
test_map := function (X, rho)
     isit := true;
     proc := RandomProcess (X);
     for i in [1..5] do
         u := Random (proc);
         v := Random (proc);
         uu := u @ rho;
         vv := v @ rho;
         flag := IsScalar (((u * v) @ rho) * (uu * vv)^-1);
         if (not flag) then
             return false;
         end if;
     end for;
return true;
end function;

/////
// see wrap function below
/////
single_test := function (name, q)

     if (name eq "SU3") then
         G := RandomConjugate (SU (3, q));
     elif (name eq "PSU3") then
         G := RandomConjugate (PSU (3, q));
     elif (name eq "SU4") then
         G := RandomConjugate (SU (4, q));
     elif (name eq "PSU4") then
         G := RandomConjugate (PSU (4, q));
     elif (name eq "Sp4") then
         G := RandomConjugate (Sp (4, q));
         if (q mod 2 ne 0) then
             "characteristic 2 only at present";
             return false;
         end if;
     elif (name eq "PSp4") then
         G := RandomConjugate (PSp (4, q));
         if (q mod 2 ne 0) then
             "characteristic 2 only at present";
             return false;
         end if;
     else
         "inadmissible name";
         return false;
     end if;
       
     t := Cputime ();
     if (name eq "SU3") or (name eq "PSU3") then
         flag, phi := RecogniseSU3 (G, q); 
     elif (name eq "SU4") or (name eq "PSU4") then
         flag, phi := RecogniseSU4 (G, q);
     else
         flag, phi := RecogniseSp4Even (G, q); 
     end if;
     s := Cputime (t);
    
     if not flag then
        "recognition failed";
     else
         test := test_map (G, phi);
         if not test then
            Error ("map not a homomorphism mod scalars");
         end if;
     end if;
       
return flag, s;
end function;

/*
   INPUT:
      (1) <name> of the low rank group from
           "SU3", "PSU3", "SU4", "PSU4", "Sp4", "PSp4"
      (2) <q> the field size: 2-power for "Sp4" and "PSp4"
      (3) <N> the number of runs
   OUTPUT:
      (1) <S> the total number of successes
      (2) <N> the total number of runs
      (3) <t> average time for one run
*/
        
TestLowRank := function (name, q, N)
    T := 0;
    F := 0;
    for i in [1..N] do
	    //if (i mod 10 eq 0) then "i =", i; end if;
       success, runtime := single_test (name, q);
       if not success then
          F +:= 1;
       end if;
       T +:= runtime;
    end for;
    t := T / N;
    S := N - F;
 return S, N, t;
end function;
  
