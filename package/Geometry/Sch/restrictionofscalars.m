freeze;

/*************************************************************************

  Restriction of scalars for a general affine scheme and field extension

  Steve Donnelly, November 2006
   
**************************************************************************/


intrinsic WeilRestriction(S::Sch, F::Fld : SubfieldMap:=0, ExtensionBasis:=[]) 
       -> Sch, MapSch, UserProgram, Map
{Same as RestrictionOfScalars}
  require IsAffine(S) : "Only implemented for affine schemes";
  K := BaseRing(S);
  require IsField(K): "The base ring of the scheme should be a field";
  if F eq K then return S; end if;
  return RestrictionOfScalars(S, F : SubfieldMap:=SubfieldMap, ExtensionBasis:=ExtensionBasis);
end intrinsic;


intrinsic RestrictionOfScalars(S::Sch, F::Fld : SubfieldMap:=0, ExtensionBasis:=[]) 
       -> Sch, MapSch, UserProgram, Map
{Given an affine scheme S with base field K, and a field F 
 such that K is a finite extension of F, returns the scheme over F obtained by 
 restricting scalars to F. Also returns the natural map of schemes over K, 
 and maps of pointsets S(K) -> S_res(F) and S_res(F) -> S(K)}

  require IsAffine(S) : "Only implemented for affine schemes";
  K := BaseRing(S);
  require IsField(K): "The base ring of the scheme should be a field";
  if F eq K then return S,_,_,_; end if;
  if SubfieldMap cmpne 0 then 
     FtoK := SubfieldMap;
     require Domain(FtoK) eq F and Codomain(FtoK) eq K :
            "The optional argument 'SubfieldMap' should be an inclusion map from the " *
            "given field F to the base field of the scheme";
  else
     FinK := IsSubfield(F,K);
     require FinK: "The base field of the scheme should be an extension of the given field";
     if IsFinite(K) then 
       FtoK := Coercion(F,K);
     else
       _,FtoK := IsSubfield(F,K);
     end if;
  end if;

  // Transfer everything to a copy of K that is a relative extension of F
  if BaseField(K) eq F then 
     Krel := K;
  else 
     Krel := RelativeField(F,K);  
  end if;
  deg := Degree(Krel);
  S_orig := S;  
  S := ChangeRing(S, Krel);
  if IsEmpty(ExtensionBasis) then 
     mybasis := Basis(Krel);
     standardbasis_to_mybasis := IdentityMatrix(F, deg);
  else
     require #ExtensionBasis eq deg : "ExtensionBasis is not a basis " 
             * "for the relative extension, which has degree", deg;
     mybasis := ChangeUniverse(ExtensionBasis, Krel);
     mybasis_to_standardbasis := Matrix(F, [Eltseq(b) : b in mybasis]);
     require IsInvertible(mybasis_to_standardbasis) : 
             "ExtensionBasis is not a basis for the relative extension";
     standardbasis_to_mybasis := mybasis_to_standardbasis^-1;
  end if;
  // Note: if  Sum of a_i*basis[i] = Sum of b_i*mybasis[i] 
  //      then  (a_i)*standardbasis_to_mybasis = (b_i)

  // New ambient, with nice variable names:
  l := Length(Ambient(S));
  amb := AffineSpace(F, l*deg);
  Snames := [Sprint(S_orig.i) : i in [1..l]];
  if &or[ sn[1] eq "$" : sn in Snames] then 
    if l le 8 then 
       Snames := ["a","b","c","d","e","f","g","h"][1..l];
    else 
       Snames := [ "x"*IntegerToString(i)*"_" : i in [1..l]];
    end if;
  elif &or[ #sn gt 1 : sn in Snames] then
    Snames := [ sn*"_" : sn in Snames];
  end if;
  names := &cat[[ Snames[i]*IntegerToString(j) : j in [1..deg]] : i in [1..l]]; 
  AssignNames( ~amb, names); 
  amb_Krel := ChangeRing(amb, Krel);

  // New defining equations
  vars := [ &+[ amb_Krel.(i*deg+j)*mybasis[j]  : j in [1..deg]] : i in [0..l-1]];
  eqnsK := [ Evaluate(eqn, vars) : eqn in DefiningEquations(S) ];
  new_def_eqns := [];
  for eqn in eqnsK do 
     eqns := [ &+[Eltseq(coeffs[j])[i] * mons[j] : j in [1..#mons]] : i in [1..deg]]
               where mons := Monomials(eqn) where coeffs := Coefficients(eqn);
     eqns := [ &+[ eqns[i]*standardbasis_to_mybasis[i,j] : i in [1..deg]] : j in [1..deg]]; 
     new_def_eqns cat:= eqns;
  end for;
  new_def_eqns := [ Evaluate(eqn, [amb.i : i in [1..l*deg]]) : eqn in new_def_eqns ];

  S := S_orig;
  Sres := Scheme(amb, new_def_eqns);
  known_irred := assigned S`Reduced and assigned S`GeometricallyIrreducible 
                      and S`Reduced and S`GeometricallyIrreducible;
  if known_irred then Sres`Reduced:=true; Sres`GeometricallyIrreducible:=true; end if;
  if assigned S`Nonsingular and S`Nonsingular then Sres`Nonsingular:=true; end if;
  Sres_K := BaseChange(Sres, K); amb_K := Ambient(Sres_K);
  AssignNames( ~amb_K, names);
  Sres_to_S := map< Sres_K -> S | 
                [&+[Sres_K.(i*deg+j)*K!mybasis[j] : j in [1..deg]] : i in [0..l-1]] : Check:=false>;
  Sres_to_S_pointsets := func< pt | S![&+[pt[i*deg+j]*K!mybasis[j] : j in [1..deg]] : i in [0..l-1]] >;
  SK_to_SresF := map< S(K) -> Sres(F) | pt :-> Sres(F)! &cat[ Eltseq(aa) : aa in Eltseq(pt) ] >;

  return Sres, Sres_to_S, SK_to_SresF, Sres_to_S_pointsets;
end intrinsic;
