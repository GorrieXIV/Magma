freeze;

/******************************************************************

  half-integral.m -- compute the space of half-integral weight
  modular forms.

  Steve Donnelly, February 2007
  
  (Evolved out of a fragment by William Stein)

 ******************************************************************/

import "misc.m" :       EchelonPowerSeriesSequence;

import "creation.m" : create_ModFrmElt_from_theta_data;

import "predicates.m":  SpaceType;

import "q-expansions.m": q_expansion_basis_using_auxiliary;


       /***********************************************
       **           COMPUTING WEIGHT 1/2             **
       ***********************************************/

/* 
   Forms of weight 1/2 are explicitly classified in Serre-Stark,
   "Modular forms of weight 1/2" (in "Modular Functions of One 
   Variable VI", Lecture Notes in Math. 627).          
   The same notation is used here.
*/

intrinsic WeightOneHalfData(M::ModFrm) -> List
{A list of tuples describing a basis of the given space of forms of weight 1/2.
Each tuple is a pair <psi, t>, which designates the theta series
obtained by summing psi(n)*q^(t*n^2) over all integers n. }

   require Weight(M) eq 1/2 : "The weight is not 1/2";
   require SpaceType(M) in {"full_half_int", "cusp_half_int"} : 
          "Currently implemented only for the full space of weight 1/2 forms";
   if assigned M`wt_half_data then 
      return M`wt_half_data; 
   elif BaseRing(M) ne Integers() then 
      M`wt_half_data := WeightOneHalfData(M`associated_space_over_z); 
      return M`wt_half_data; 
   elif SpaceType(M) eq "cusp_half_int" then
      data := WeightOneHalfData(AmbientSpace(M)); 
      M`wt_half_data := [* tup : tup in data | not IsTotallyEven(tup[1]) *];
      return M`wt_half_data;
   end if;

   N := Level(M);
   data := [*  *];  // List because characters may have different moduli
   for chi in DirichletCharacters(M) do 
      if IsOdd(chi) then continue; end if;  // shouldn't occur anyway
      for t in Divisors(N div 4) do 
         chi_t := KroneckerCharacter(t);
         psi := chi*chi_t;
         r := Conductor(psi);
         if IsDivisibleBy( N, 4*r^2*t) then
            psi := Order(psi) le 2 select DirichletGroup(r)! psi  
                                    else  DirichletGroupFull(r)! psi;
            Append( ~data, <psi,t> );  // psi MUST be primitive
         end if;
      end for;
   end for;
   M`wt_half_data := data;
   return M`wt_half_data;
end intrinsic;
   
function q_expansion_basis_weight_half(M, prec)
   assert Weight(M) eq 1/2;
   Qbasis := [];
   _<q> := PowerSeriesRing(Rationals());
   for tup in WeightOneHalfData(M) do
      psi, t := Explode(tup);
      F := CyclotomicField(Order(psi)); 
      // Note: we decompose the character values in terms of the basis of this F
      // TO DO: Another way to do it would be to take Trace(elt*zeta^k) for 0<=k<[F:Q]
      //   This would avoid creating any new fields (possibly desirable, as I'm 
      //   suspicious of FldCyc's causing memory leaks).
      nbound := Ceiling(Sqrt(prec/t));
      coeffs := [ Eltseq(F! psi(n) ) : n in [0..nbound]];
      Qbasis cat:= [ coeffs[1,i] + 2*(&+[Parent(q)| coeffs[1+n,i]*q^(t*n^2) : n in [1..nbound]]) 
                                 + O(q^prec) : i in [1..Degree(F)]];
   end for;    
   assert #Qbasis eq Dimension(M);
   return EchelonPowerSeriesSequence(Qbasis);
end function;


       /***********************************************
       **      COMPUTING WEIGHT k/2 FOR k > 1        ** 
       ***********************************************/

/* 
   METHOD: Let k = 2*wt be an odd integer.
   Basmaji gives the following algorithm on page 55 of his thesis.

   Let S = S(eps, (k+1)/2), where eps = chi*psi^((k+1)/2), where
   psi is the nontrivial mod-4 Dirichlet character.
   Let U be the subspace of S x S of elements (a,b) such that
         a*Theta_Z = b*Theta_oddZ
   (where Theta_Z and Theta_oddZ are the standard weight 1/2 forms of
    level 4 and level 16 respectively).
   Then U is isomorphic to S(chi, k/2) via the map
         (a,b) |----> a/Theta_oddZ ( = b/Theta_Z )

   Basmaji notes that Cohen-Oesterle give a dimension formula, 
   which could be invoked to check that enough precision was used,
   ie that our solutions to a*Theta_Z = b*Theta_oddZ really are solutions. 
   What we do here, though, is simply use the Sturm bound for how
   many coefficients are required to uniquely determine a given form 
   (of integral weight). This could be applied to, for example, 
   b*Theta_oddZ^2 - a*Theta_oddZ*Theta_Z of weight (k+3)/2
*/

procedure set_up_auxiliary_half_integral(M)
   if assigned M`generated_by_auxiliary then return; end if;
   
   assert SpaceType(M) in {"full_half_int", "cusp_half_int"};

   assert BaseRing(M) eq Integers();  // otherwise should go via associated_space_over_z
   k := Integers()! (2*Weight(M));
   N1 := Level(M);  // can assume 4|N1

   M`generated_by_auxiliary := [* *];   

   for chi in DirichletCharacters(M) do 
     Mchi := HalfIntegralWeightForms(chi, k/2);
     dim := DimensionByFormula(Mchi);
     if dim eq 0 then continue; end if;

     // New bit: try whether we can get the forms from below, by
     // multiplying M(N1, wt-1/2) by the simplest weight 1/2 form.

     l := Integers()! (Weight(M) - 1/2);
     if l ne 1 then 
       chi_l := IsOdd(l) select chi*KroneckerCharacter(-1) else chi;
       dim_below := DimensionByFormula(N1, chi_l, l : Cuspidal:=IsCuspidal(M) );
       if l gt 1 then vprint ModularForms,2: "dim =", dim, "    dim from below =", dim_below; end if;
       if l gt 1 and dim eq dim_below then
          vprintf ModularForms,1: "Basis can be obtained from below (weight %o times weight 1/2)\n", l;
          Ml := ModularForms( DirichletGroup(N1)! chi_l, l);
          if IsCuspidal(M) then Ml := CuspidalSubspace(Ml); end if;
          assert Dimension(Ml) eq dim;
          M`generated_by_auxiliary cat:= [* <"elts_mult_elts", 
                                             [* Basis(Ml), Basis(HalfIntegralWeightForms(4,1/2)) *]> *];
          continue;
       end if;
     end if;
       
     // Failed to obtain basis from below; try from above (see earlier comment)
     // Store a tuple <M1, M2, f1, f2> such that 
     //  M1 < M2,  M*f1 < M1,  M*f2 < M2, and M*f1 = {m in M1 : f2*m lies in f1*M2}

     if N1 mod 16 eq 0 then 
       // use Theta_Z(z) and Theta_Z(4z) where Theta_Z = Sum( q^{n^2} )
       f1 := HalfIntegralWeightForms(4, 1/2).1;
       f2 := HalfIntegralWeightForms(16, 1/2).1;
       eps := chi * KroneckerCharacter(-1)^((k+1) div 2);
       M1 := ModularForms([eps], (k+1) div 2);
       M2 := M1;
     else 
       // use Theta_Z(z) and Theta_Z(2z)
       N2 := LCM(N1, 8);
       f1 := HalfIntegralWeightForms(4, 1/2).1;
       chi8 := KroneckerCharacter(2);
       f2 := HalfIntegralWeightForms(chi8, 1/2).1;
       eps1 := chi * KroneckerCharacter(-1)^((k+1) div 2);
       eps2 := DirichletGroup(N2, CoefficientRing(eps1))! (eps1 * chi8);
       M1 := ModularForms([eps1], (k+1) div 2);
       M2 := ModularForms([eps2], (k+1) div 2);
     end if;

     if IsCuspidal(M) then
        M1 := CuspidalSubspace(M1); 
        M2 := CuspidalSubspace(M2); end if;
     if M1 eq M2 then
        vprintf ModularForms,1: "Auxiliary space used to compute forms is:\n%o\n", M1;
     else 
        vprintf ModularForms,1: "Auxiliary spaces used to compute forms are:\n%o \n%o\n", M1, M2;
     end if;
     
     M`generated_by_auxiliary cat:= [* < "space_div_elt", <M1,M2,f1,f2> > *];
   end for;
end procedure;

function q_expansion_basis_half_integral(M, prec)
   assert wt gt 1 and IsOdd(Integers()! (2*wt)) where wt is Weight(M);
       // when weight = 1/2 use q_expansion_basis_weight_half
   set_up_auxiliary_half_integral(M);
   return q_expansion_basis_using_auxiliary(M, prec);
end function;


function q_expansion_basis_via_space_div_elt(M, prec, data)

   // 'data' should be a tuple <M1, M2, f1, f2> such that 
   //  M1 < M2,  M*f1 < M1,  M*f2 < M2, and M*f1 = {m in M1 : f2*m lies in f1*M2}

   // The arguments are a bit redundant because 'data' is (usually) 
   // contained somewhere in M`generated_by_auxiliary, but we don't assume this.

   assert BaseRing(M) eq Integers();
   M1, M2, f1, f2 := Explode(data);
   assert Weight(f2) + Weight(M1) eq Weight(f1) + Weight(M2);

   // Determine a precision bound for the space where we are testing equality,
   // ie any space containing f2*M1 
   prec_bound := PrecisionBound(Parent( f2*M1.1 ));
   prec := Max(prec, prec_bound);

   Qq<q> := PowerSeriesRing(Rationals());
   vprintf ModularForms,1: 
          "Need precision %o for q-expansion bases of auxiliary spaces\n", prec;
   v1 := Valuation(PowerSeries(f1));
   v2 := Valuation(PowerSeries(f2));
   v := Max(v1,v2);
   f1 := PowerSeries(f1, prec+v);
   f2 := PowerSeries(f2, prec+v);
   bas1 := qExpansionBasis(M1, prec+v1);
   bas2 := qExpansionBasis(M2, prec+v2);
   ChangeUniverse( ~bas1, Qq);
   ChangeUniverse( ~bas2, Qq);
   
   A := ZeroMatrix(Rationals(), #bas1+#bas2, prec+v1+v2);
   for i in [1..#bas1] do 
      ff := f2*bas1[i];
      for j in [0..prec+v1+v2-1] do
         A[i,j+1] := Coefficient(ff,j);
      end for;
   end for;
   for i in [1..#bas2] do 
      ff := f1*bas2[i];
      for j in [0..prec+v1+v2-1] do
         A[#bas1+i,j+1] := - Coefficient(ff,j);
      end for;
   end for;
   B := Basis(Kernel(A));
   avec := [ &+[v[i]*bas1[i] : i in [1..#bas1]] + O(q^(prec+v1)) : v in B];       // sequence of a in M1
 //bvec := [ &+[v[#bas1+i]*bas2[i] : i in [1..#bas2]] + O(q^(prec+v2)) : v in B]; // sequence of b in M2
   bas := [ Qq! (a/f1) : a in avec];
   assert &and[ AbsolutePrecision(bb) eq prec : bb in bas];
   return bas;
end function;


       /***********************************************
       **               INTRINSICS                   **
       ***********************************************/


intrinsic HalfIntegralWeightForms(N::RngIntElt, w::FldRatElt) -> ModFrm
{The space of forms on Gamma0(N) with weight w.  
 The weight must be a positive element of Z+1/2, and N must be a multiple of 4.} 
   require N mod 4 eq 0 : "The level N must be divisible by 4.";
   return HalfIntegralWeightForms(DirichletGroup(N)!1, w); 
end intrinsic;


intrinsic HalfIntegralWeightForms(chi::GrpDrchElt, w::FldRatElt) -> ModFrm
{The space of forms with character chi and weight w, 
 which must be a positive element of Z+1/2.}

   bool, k := IsCoercible( Integers(), 2*w);
   require bool and k gt 0 and IsOdd(k) : "The weight must be in Z + 1/2 and be positive";
   N := Modulus(chi);
   require N mod 4 eq 0 : "The modulus of the character must be divisible by 4.";
   
   M := New(ModFrm);
   M`type := "full_half_int";
   M`is_cuspidal := false;
   M`base_ring := Integers();
   M`weight := k/2;
   M`level := N;
   M`is_gamma1 := false;  
   M`dirichlet_character := [chi];
   return M;
end intrinsic;

intrinsic HalfIntegralWeightForms(G::GrpPSL2, w::FldRatElt) -> ModFrm
{The space of forms on the congruence subgroup G of weight w, 
which must be a positive element of Z+1/2.}

   bool, k := IsCoercible( Integers(), 2*w);
   require bool and k gt 0 and IsOdd(k) : "The weight must be in Z + 1/2 and be positive";
   N := Level(G);
   require N mod 4 eq 0 : "The level N must be divisible by 4.";

   if IsGamma1(G) then
      M := New(ModFrm);
      M`type := "full_half_int";
      M`is_cuspidal := false;
      M`base_ring := Integers();
      M`weight := k/2;
      M`level := N;
      M`is_gamma1 := true;
      return M;
   elif IsGamma0(G) then
      return HalfIntegralWeightForms(DirichletGroup(N)!1, k/2);
   else
      require false : "Argument 1 must be a congruence subgroup, either Gamma_0(N) or Gamma_1(N).";
   end if;
end intrinsic;
