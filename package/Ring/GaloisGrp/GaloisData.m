freeze;

declare type GaloisData;
declare attributes GaloisData : Base, Type, Ring, Roots, Prec, Prime,
                             Error, Subfields, Permutation,
                             DescentChain, max_comp, GetRoots, RootData, f;

/*
Type : p-adic, Complex, p-adic (rel), Q(t), 
	F_q(t)
f : Polynomial whose Galois group is being computed using the information 
	in this data (unscaled)
Scale : LCM(Denominators of f/LeadingCoeff(f)), in bottom coeff ring, not 
	always set!
Prime : The prime used for local computations, completions
Base : completion of coeff ring of f at Prime
BaseMap : map from coeff ring of f into Base
Ring : a splitting field for f, contains Base, a p-adic ring for number fields, 
	a series ring for global function fields and a series ring 
	over a p-adic ring for char 0 function fields
Roots : Roots of (unscaled) f in Ring 
GetRoots : function computing the roots of f in Ring to some precision and 
	assigning S`Roots
max_comp : maximum complex absolute value/infinite valuation of roots of f
	(unscaled)
Bound : function computing a bound for the evaluation of an invariant,
	at the roots of f, transformed by a tschirni, idx????
GetPrec : function computing precision necessary in the roots of f for accurate
	return of IsInt, eg, P^prec < bound, for global function fields this is
	a bound on the degrees, ie. Degree(P^prec) < bound
IsInt : function computing the inverse of BaseMap, failing if the size of the
	preimage is larger than given bound
Subfields : the subfields of the field extension defined by f. WHAT HAPPENS 
	HERE WITH SUBFIELD RECURSION? Are they the subfields of f or a larger
	field?
SubfieldLattice : subfield lattice of the field extension defined by f
DescentChain : Chain of groups from the starting group down to the Galois group
	along with a boolean indicating whether the descent step is proven or 
	not
CycleTypes : Information about cycles (lengths?) in the galois group of f
RootData : 
Prec : 
Error : 
Permutation :
RecoData : 
KnownSubgroup : a group known to be a subgroup of the galois group
Time : 
Maps : 
MinPrec : 
*/

intrinsic InternalGaloisDataCreate(p::RngIntElt) -> GaloisData
  {}
  S := New(MakeType("GaloisData"));  
  S`Prime := p;
  return S;
end intrinsic;

intrinsic IsCoercible(S::GaloisData,s::.) -> .
  {}
  return false, "Illegal coercion";
end intrinsic;

intrinsic Print(S::GaloisData, level::MonStgElt)
  {}
  if S`Type eq "p-Adic" then
    printf "GaloisData over Z_%o", S`Prime;
  elif S`Type eq "p-Adic (rel)" then
    printf "GaloisData over Z_%o - relative case", S`Prime;
  elif S`Type eq "Complex" then
    printf "GaloisData over the complex numbers\n";
  else
    printf "GaloisData of type %o\n", S`Type;
  end if;

  if level eq "Maximal" then
    //
  end if;
end intrinsic;

intrinsic 'in'(x::., y::GaloisData) -> BoolElt
  {}
  return false;
end intrinsic;

