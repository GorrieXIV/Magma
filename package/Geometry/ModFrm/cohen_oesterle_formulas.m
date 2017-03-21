freeze;

/*********************************************************************

    Formulas for the dimensions of spaces of modular forms 
               and half-integral weight forms

  Taken from the Cohen-Oesterle article in 'Modular Forms in One 
  Variable, VI' (Lecture Notes in Math. 627), which is a summary 
  of known results (without proofs, and with little effort to 
  indicate where full proofs can be found).

  Steve Donnelly, January 2007.

**********************************************************************/

// All solutions of x^2+x+1 = 0 mod N, returned as integers 0 < x < N.
function primitive_cube_roots_mod(N) // RngIntElt -> [ RngIntElt ]
  if N mod 2 eq 0 or N mod 9 eq 0 then 
     return [Integers()| ]; 
  end if;
  cube_roots := [(r-1)/2 : r in AllSqrts( Integers(N)! -3)];
  return ChangeUniverse(cube_roots, Integers());
end function;

function lambda(N,chi,p) 
  r_p := Valuation(N,p);
  s_p := Valuation(Conductor(chi),p);
  if 2*s_p le r_p then
     if IsEven(r_p) then
        rr := r_p div 2;
        return p^rr + p^(rr-1);
     else 
        rr := (r_p - 1) div 2;
        return 2*p^rr;
     end if;
  else
     return 2*p^(r_p - s_p);
  end if;
end function;
 
function zeta(k,N,chi)
  r_2 := Valuation(N,2);
  s_2 := Valuation(Conductor(chi),2);
  if r_2 ge 4 then 
     return lambda(N,chi,2);
  elif r_2 eq 3 then
     return 3;
  else 
     assert r_2 eq 2;
     conditionC := exists{p : p in PrimeDivisors(N) | p mod 4 eq 3 
                              and (IsOdd(r_p) or r_p gt 0 and r_p lt 2*s_p
                                   where s_p := Valuation(Conductor(chi),p)
                                   where r_p := Valuation(N,p)) };
     if conditionC then 
        return 2;
     else
        assert s_2 in {0,2};
        bool := IsEven(Integers()! (k - 1/2));
        return (bool xor s_2 eq 0) select 5/2 else 3/2; 
     end if;
  end if;
end function;
        

function dimSk_subtract_dimM2minusk(k,N,chi) 
  term1 := (k-1)/12*N* &*[Rationals()| 1+1/p : p in PrimeDivisors(N)];
  
  if not IsIntegral(k) then 
     lambda_product := &*[Integers()| lambda(N,chi,p) : p in PrimeDivisors(N) | p ne 2];
     dim := term1 - zeta(k,N,chi)/2 * lambda_product; 
  else
     lambda_product := &*[Integers()| lambda(N,chi,p) : p in PrimeDivisors(N)];

     if IsOdd(k) then 
        epsilon_k := 0;
     elif k mod 4 eq 2 then 
        epsilon_k := -1/4;
     else 
        epsilon_k := 1/4;
     end if;
     mu_k := (1 - (k mod 3)) / 3;
     F := Parent(chi(1));
     chi_sum_over_cube_roots := &+[F| chi(n) : n in primitive_cube_roots_mod(N) ];
     chi_sum_over_4th_roots := &+[F| chi(n) : n in AllSqrts( Integers(N)! -1) ];

     dim := term1 - 1/2*lambda_product + epsilon_k*chi_sum_over_4th_roots
                                       + mu_k*chi_sum_over_cube_roots;
  end if;

  dim_is_an_integer, dim := IsCoercible( Integers(), dim); 
  assert dim_is_an_integer;
  return dim;
end function;


intrinsic DimensionByFormula(M::ModFrm) -> RngIntElt
{The dimension of the given space of modular forms 
or half-integral weight forms, 
as given by the formulas in the Cohen-Oesterle paper
(in 'Modular Forms in One Variable, VI', Lecture Notes in Math. 627).}
  require assigned M`type : "Not implemented for spaces of unknown type";
  if M`type in {"full", "full_half_int"} then 
     is_cusp_subspace := false;
  elif M`type in {"cusp", "cusp_half_int"} then
     is_cusp_subspace := true;
  else 
     require false : "Not implemented for spaces of this type";
  end if;
  chars := DirichletCharacters(M);
  if IsEmpty(chars) then 
     return DimensionByFormula(Level(M), Weight(M) : Cuspidal:=is_cusp_subspace);
  elif #chars eq 1 then 
     return EulerPhi(Order(chars[1])) * 
            DimensionByFormula(chars[1], Weight(M) : Cuspidal:=is_cusp_subspace);
  else 
     // note that all spaces are Galois invariant
     return &+[ EulerPhi(Order(chi)) * 
                DimensionByFormula(chi, Weight(M) : Cuspidal:=is_cusp_subspace)
              : chi in GaloisConjugacyRepresentatives(chars) ];
  end if;
end intrinsic;


intrinsic DimensionByFormula(chi::GrpDrchElt, k::Any : Cuspidal:=false) 
       -> RngIntElt
{The dimension of the space of modular forms of weight k 
(integral or half-integral) and character chi, 
as given by the formulas in the Cohen-Oesterle paper
(in 'Modular Forms in One Variable, VI', Lecture Notes in Math. 627).}
  return DimensionByFormula(Modulus(chi), chi, k : Cuspidal:=Cuspidal);
end intrinsic;
 
intrinsic DimensionByFormula(N::RngIntElt, k::Any : Cuspidal:=false) 
       -> RngIntElt
{The dimension of the space of modular forms of weight k 
(integral or half-integral), level N and character chi, 
as given by the formulas in the Cohen-Oesterle paper
(in 'Modular Forms in One Variable, VI', Lecture Notes in Math. 627).}
  return DimensionByFormula(N, DirichletGroup(N)! 1, k : Cuspidal:=Cuspidal);
end intrinsic;
 
intrinsic DimensionByFormula(N::RngIntElt, chi::GrpDrchElt, k::Any 
                            : Cuspidal:=false) -> RngIntElt
{"} // "
  require Type(k) in {RngIntElt, FldRatElt} and k ge 0 and IsIntegral(2*k) : 
     "The weight k should be a non-negative integer or half-integer";
  require k ne 1 : "The formulas don't determine the dimension for weight 1";
  if Conductor(chi) mod N ne 0 then N := LCM(N, Conductor(chi)); end if;
  if IsIntegral(k) then
     k := Integers()! k;
     //require chi(-1) eq (-1)^k : 
     //  "The character chi should be odd or even according to the parity of k";
     if chi(-1) ne (-1)^k then return 0; end if;
  else 
     require N mod 4 eq 0 : "The level N should be a multiple of 4";
     //require chi(-1) eq 1 : "The character chi should be even";
     if chi(-1) eq -1 then return 0; end if;
  end if;
  
  if k eq 0 then 
     dim := (not Cuspidal and chi eq Parent(chi)!1) select 1 else 0;
  elif k eq 1/2 then 
     chi_N := (Order(chi) le 2) select DirichletGroup(N)! chi 
                                 else  FullDirichletGroup(N)! chi;
     M := HalfIntegralWeightForms( chi_N, 1/2);
     if Cuspidal then M := CuspidalSubspace(M); end if;
     dim := Dimension(M);
  elif k eq 3/2 and Cuspidal then 
     dim := dimSk_subtract_dimM2minusk( 3/2, N, chi)
                  + DimensionByFormula( N, chi, 1/2);
  elif k eq 3/2 then 
     dim := - dimSk_subtract_dimM2minusk( 1/2, N, chi)
                    + DimensionByFormula( N, chi, 1/2 : Cuspidal);
  elif k ge 2 and Cuspidal then
     dim := dimSk_subtract_dimM2minusk( k, N, chi);
     if k eq 2 and chi eq Parent(chi)!1 then dim +:= 1; end if;  // because dim M_0 = 1
  elif k ge 2 then 
     dim := - dimSk_subtract_dimM2minusk( 2-k, N, chi);
  end if;

  require dim ge 0 : "The formula calculates a negative integer for the dimension";
  return dim;
end intrinsic;
