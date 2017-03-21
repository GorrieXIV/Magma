freeze;

/******************************************************************************

     Regular models of arithmetic surfaces 

     Steve Donnelly, July 2009

******************************************************************************/

import "regularity.m": polyres, 
                       polylift,
                       lift, // only temp?
                       is_regular_at_point,
                       is_regular_fibre_FU, 
                       global_extension;

import "interface.m":  number_of_geometric_components,
                       number_of_points_on_special_fibre,
                       splitting_degree;


declare type CrvRegModel;
declare attributes Crv: RegularModels;

declare verbose RegularModel, 3;

debug := false;
debug_names := true;

/******************************************************************************

  INTRODUCTION

This computes a model of the arithmetic surface associated to a curve over a 
global field F (FldRat, FldNum or Fq(t)). The model is regular on the fibre 
above a given place P of F.  A model is a data structure containing several 
affine patches with maps between them, also storing the components of the 
special fibre, and other important data.

The patches arise as patches of successive blowups, forming a tree.
Each patch consists of local equations, the blowdown map, and other data.  
In particular, the 'domain' of a patch specifies the part of the patch that
is used.  The domains can be closed subschemes of open subschemes, and they 
cover the model disjointly: each point of the model lies in the domain of 
precisely one patch.

The model stores each component of the special fibre that occurred (including 
non-regular components that were later blown up), as an 'abstract_fibre_record'.
This contains abstract data (the multiplicity etc) and explicit equations for
the fibre on some patches.  These are stored in fibre`explicit, which is an 
array indexed by patch indices; equations are stored for precisely those patches
for which the fibre intersects the patch domain.

  DATA STRUCTURES     

A CrvRegModel holds the data of a (partially computed) regular model. 
It consists of lists of records of the following formats:

 * 'patch'          stores an affine patch of the (partially regularized) scheme, 
 * 'abstract_fibre' stores a reduced irreducible component of the special fibre 
                    of the model (possibly not regular),
 * 'fibre_on_patch' stores equations etc for an abstract_fibre on a single patch,
 * 'point'          stores an abstract point that is significant for some reason,
                    eg is non-regular or an intersection of components,
 * 'point_on_patch' stores equations etc for a point on a single patch 

*****************************************************************************/

// DECLARATIONS OF DATA STRUCTURES     

declare attributes CrvRegModel:   

  C,                        // the original curve, over a global field K

  K,                        // BaseField(C)
  R,                        // ring of integers in K 
  P, pi,                    // P = (pi) is the maximal ideal of R
  k, res,                   // res : R --> k is the map to the residue field k = R/P
  extended_res,             // list containing pairs [*F,resF*] where resF is an extension
                            // of res to F (this is used in PointOnRegularModel)

  // Data describing the (partially regularized) model:

  patches,                  // assoc array of patch records, indexed by the indices <n,i>

  points,                   // list of point records, for all interesting points
  abstract_fibres,          // list of records, for all components of special fibre
                            // (must not delete items or reorder these lists, only append) 
                             
  // Properties:

  is_regular,               // true if model is regular 
  original_is_regular,      // true if the input curve was already a regular model
  regular_fibres_indices,   // sorted, only assigned once

  // Miscellaneous caching:

  intersection_matrix,      // see functions with these names
  model_with_split_components, 
  special_points_count;        


patch_record := recformat<
 
  index : Tup,  // = <n,i> where n counts the blowups and i counts the patches of each blowup

  parent : Tup, // index of the patch from which this patch was obtained (and which it maps to) 

  map : SeqEnum,// the blowdown map to the parent patch, as a sequence of polynomials over R
  map_k,        // same polynomials reduced mod P, in kpol = polynomial ring over k

  map_inv,      // the inverse substitution, as a sequence of elements of the FieldOfFractions
                // of the polynomial ring over R

  is_FU,        // true if patch is in simple form with equations {F, pi-U}
  F, U,         // where F, U are in R[x,y,z]

  eqns,         // sequence of polynomials over R
  eqns_k,       // same polynomials reduced mod P, in kpol = polynomial ring over k
  ideal_k,      // the ideal of eqns_k
  
  singular,     // singular subscheme of the special fibre, as an ideal of kpol

  domain : Tup  // = <seq1, seq2, seq3> containing sequences of ideals in kpol. 
                // For i = 1,2,3, let D_i be the union of closed subschemes specified
                // by the ideals in seq_i.  The domain is then the set D_3 - D1 - D2.
                // Here seq2 contains the ideals that have been blownup from this patch.
                // Eg seq1 = seq2 = [], seq3 = [0] specifies the whole ambient affine space. 
>;

fibre_on_patch_record := recformat<

  patch_index,      // index of patch this record belongs to

  ideal : RngMPol,  // defining ideal of a (reduced, irreducible, 1-dimensional) subscheme 
                    // of the special fibre; must be an ideal of Universe(patch`eqns_k)
   
  geo_components    // decomposition of the ideal into geometrically irreducible components
>;

abstract_fibre_record := recformat<

  explicit : Assoc, // array indexed by patch_indices <n,i>, storing fibre_on_patch_records
                    // (for enough patches to cover the fibre)

  patch1,           // Index of the (only) patch whose domain meets this fibre with dimension 1

  is_regular,       // true if this fibre does not need to be blown up 
                    // (ie model is regular generically on this fibre, 
                    // although it may still contain non-regular points)

  blownup : SeqEnum,// contains an entry <<n0,i0>, n1> for each patch <n0,i0> that was blown up

  multiplicity,     // multiplicity with which this fibre appears in the special fibre

  geo_splitting_field // residue field extension where this decomposes into geo irreducibles
>;

point_on_patch_record := recformat<

  patch_index,      // index of patch this record belongs to

  coords, 

  ideal
>; 

point_record := recformat<

  explicit : Assoc, // array indexed by patch_indices <n,i>, storing point_on_patch_records
 
  patch : Tup,      // index of selected patch, to be used when we work with this point

  fibres,           // set of indices, indicating which model`abstract_fibres contain the point

  field,            // extension of model`k over which point is defined 

  is_regular,       // false if point is nonregular and is not contained in a nonregular fibre 
                    // (equivalently, false if the point needs to be blown up)
                    // TO DO: this is confusing, use a 3-valued flag instead?

  blownup : RngIntElt // = n, if point was blown up at the nth step (creating patches <n,i>)
>;

function blank_abstract_fibre_record()
  return rec< abstract_fibre_record | explicit := AssociativeArray(Parent(<0,0>)) >;
end function;

function blank_point_record()
  return rec< point_record | explicit := AssociativeArray(Parent(<0,0>)) >;
end function;

/***************************************************************************************
  HACKOBJ INTRINSICS
***************************************************************************************/

intrinsic Print(x::CrvRegModel, level::MonStgElt) 
{}
  K := x`K;
  P := x`P;
  printf "Model of arithmetic surface over %o, ", x`R;
  printf "regular at "; 
  if Type(P) in {RngInt, RngUPol} then
    printf "prime ideal generated by %o,", K!Generator(P);
  else
    printf "%o,", P;
  end if;
  printf " with generic fibre isomorphic to %o", x`C;
end intrinsic;
  
/***************************************************************************************
  HELPER FUNCTIONS 
***************************************************************************************/

function lift_ideal(idl, Pol, res, pi)
  return ideal< Pol | [pi] cat [polylift(f, Pol, res) : f in Basis(idl)] >;
//return [pi] cat [polylift(f, Pol, res) : f in Basis(idl)];
end function;

function pt_coords_from_ideal(I)  
  assert Dimension(I) eq 0; 
  S := Scheme(AffineSpace(Generic(I)), Basis(I));
  if Degree(S) eq 1 then
    return Eltseq(Points(S)[1]), BaseField(S);
  else
    pts, field := PointsOverSplittingField(S);
    return Eltseq(pts[1]), field;
  end if;
end function;

function special_fibre_singular_ideal(patch, kpol)
  if not assigned patch`singular then
    special_fibre_scheme := Scheme(AffineSpace(kpol), patch`eqns_k);
    SS := SingularSubscheme(special_fibre_scheme);
    patch`singular := DefiningIdeal(SS);
  end if;
  return patch`singular;
end function;

function check_regularity_on_fib(model, patch, fib)
  if Type(fib) eq Rec then 
    fib := fib`explicit[patch`index]`ideal;
  end if;
  kpol := Universe(patch`eqns_k);
  sing := special_fibre_singular_ideal(patch, kpol);
  // TO DO: probably can interchange 'if' statements here: singular test doesn't care about FU?
  if patch`is_FU then  
    // must do singular test first: is_regular_fibre_FU assumes fib is singular on special fibre
    // TO DO: more efficiently
    Groebner(fib);
    sing_meet_fib := sing + fib;
    if Dimension(sing_meet_fib) gt 0 then // fib is contained in the singular subscheme
      return is_regular_fibre_FU(patch`F, patch`U, fib, model`P, model`pi : res:=model`res, kpol:=kpol); 
    else
      // need to test singular points lying on fib
      nonreg_pts := [pt : pt in RadicalDecomposition(sing_meet_fib) 
                        | not is_regular_at_point(patch`eqns, 1, pt, model`P : res:=model`res)]; 
      return true, nonreg_pts;  
    end if;
  end if;
end function;

function dimension_of_image(idl, mapeqns)
  // TO DO: more carefully
  if debug then 
    assert Dimension(idl) le 1;
  end if;
  A := AffineSpace(Generic(idl));
  S := Scheme(A, idl);
  phi := map< A->A | mapeqns >; 
  return Dimension(phi(S));
end function;

/***************************************************************************************
  HELPER FUNCTIONS : DOMAIN STUFF
***************************************************************************************/

function excluded(model, idx)
  patch := model`patches[idx];
  kpol := Universe(patch`eqns_k);
  d := patch`domain[1] cat patch`domain[2];
  if IsEmpty(d) then 
    return ideal<kpol|1>;
  else
    return &meet d;
  end if;
end function;

// I is an ideal in kpol, patch is a patch_record

function _point_in_domain(I, patch : include_blownup:=false)
  if debug then
    assert IsPrime(I) and Dimension(I) eq 0;
  end if;
  if exists{J : J in patch`domain[1] | J subset I} then
    return false;
  elif not include_blownup and exists{J : J in patch`domain[2] | J subset I} then
    return false;
  else
    return exists{J : J in patch`domain[3] | J subset I};
  end if;
end function;

function point_in_domain(model, pt, patch_idx : include_blownup:=false) 
  return _point_in_domain(pt`explicit[patch_idx]`ideal, model`patches[patch_idx]
                          : include_blownup:=include_blownup );
end function;

// TO DO: avoid unnecessarily doing the &meet in these functions

function ideal_meets_domain(I, domain : include_blownup:=false)
  Ds := include_blownup select domain[1]
                         else  domain[1] cat domain[2];
  D := IsEmpty(Ds) select ideal<Generic(I)|1>
                    else  &meet Ds;
  for J in domain[3] do 
    IJ := I + J; 
    if D subset IJ then
       continue;
    end if;
    return true;
  end for;
  return false;
end function;

function fibre_meets_domain(I, patch)
  if debug then
    assert IsPrime(I) and Dimension(I) eq 1;
  end if;
  return ideal_meets_domain(I, patch`domain);
end function;

function fibre_meets_domain_with_dim_1(I, patch : include_blownup:=false)
  if debug then
    assert IsPrime(I) and Dimension(I) eq 1;
  end if;
  Ds := include_blownup select patch`domain[1]
                         else  patch`domain[1] cat patch`domain[2];
  D := IsEmpty(Ds) select ideal<Generic(I)|1>
                    else  &meet Ds;
  for J in patch`domain[3] do
    IJ := I + J;
    if D subset IJ or Dimension(IJ) eq 0 then
      continue;
    end if;
    return true;
  end for;
  return false;
end function;

/***************************************************************************************
  HELPER FUNCTIONS : MULTIPLICITY
***************************************************************************************/

// Degree of an affine variety

function degree(idl) 
  return Degree(Scheme(AffineSpace(Generic(idl)), Basis(idl)));
end function;

// idl is a zero-dimensional ideal, pt is a reduced zero-dimensional ideal

function multiplicity0(idl, pt)
  m := 0;
  n := 0;
  while true do
    n +:= 1;
    m0 := m;
    m := degree(idl + pt^n);
    if m eq m0 then 
      break;
    end if; 
  end while;
  return m;  
end function;  

// idl is any scheme, pt is a point_on_patch record

function multiplicity_of_point(idl, pt)
  Pol := Generic(idl);
  S := Scheme(AffineSpace(Pol), idl);
  F := Universe(pt`coords);
  d := Degree(F, BaseRing(Pol));
  m := Multiplicity(S, S(F)! pt`coords);

// TO DO: this is only temp testing
m0 := multiplicity0(idl, pt`ideal);
assert d*m eq m0;

  return d*m;
end function;

// Find the primary component of the ideal S lying above the prime ideal I.

// Should require less work than doing full PrimaryDecomposition, but the
// alternatives are even worse sometimes, especially EquidimensionalPart(?)
// Examples: for elliptic curves 14a3 and 38a2, PrimaryDecomposition is bad
// while full_component1 works well; for the 9th Fermat curve, the opposite.

function full_component1(S, I)
  m := 0;
  Im1_meet_S := I + S;
  Im1_meet_S_top := EquidimensionalPart(Im1_meet_S);
  repeat
    m +:= 1;
    Im_meet_S := Im1_meet_S;
    Im_meet_S_top := Im1_meet_S_top;
    Im1_meet_S := I^(m+1) + S;
    Im1_meet_S_top := EquidimensionalPart(Im1_meet_S);
  until Im_meet_S_top eq Im1_meet_S_top; 
  return Im_meet_S_top;
end function;

function primary_component(J, I)
  Q, P := PrimaryDecomposition(J);
  i := Index(P, I);
  assert i gt 0;
  return Q[i];
end function;

function full_component2(S, I)
  assert S subset I and IsPrime(I);
  m := 0;
  Pm1 := I;
  repeat
    m +:= 1;
    Pm := Pm1;
    Pm1 := primary_component(S + I^(m+1), I);
  until Pm eq Pm1;
  return Pm;
end function;

function full_component(S, I) 
  vprintf RegularModel, 3: "full_component: "; 
  vtime RegularModel, 3:
  return full_component2(S, I);
  return full_component1(S, I);
  return primary_component(S, I);
end function;

// fib and fib_red should be associated ideals returned by PrimaryDecomposition 

function multiplicity_primary_prime(fib, fibred)
  fib1 := Homogenization(fib);
  fibred1 := Homogenization(fibred);
  H := ideal< Generic(fib1) | Generic(fib1).1 >; // TO DO: is this the homogenizing variable ??
  fib1 := Saturation(fib1, H);
  H := ideal< Generic(fibred1) | Generic(fibred1).1 >; 
  fibred1 := Saturation(fibred1, H);
  mult := Degree(fib1) / Degree(fibred1);
  return Integers()! mult;
end function;

function multiplicity_of_component1(S, I)
  full := full_component(S, I);
  return multiplicity_primary_prime(full, I);
end function;

function multiplicity_of_component(S, I)
  // work with generic point corresponding to I
  assert S subset I;
  Pol := Generic(I);
//Pol<x,y,z> := Generic(I);
  A := AffineSpace(Pol);
  Isch := Scheme(A, I);
  Ssch := Scheme(A, S);
  pt := GenericPoint(Isch); 
//pt := GenericPoint(Isch : UseAlgorithmicFunctionField:=true); // option not in export version yet
  pt_on_S := Ssch(Ring(Parent(pt))) ! pt;
  m := Multiplicity(Ssch, pt_on_S); // TO DO: local Groebner gets stuck
/*
printf "Saturation way ... "; time
m1 := multiplicity_of_component1(S, I);
assert m eq m1;
"multiplicity_of_component =", m;
*/
  return m;
end function;

// TO DO (hopefully) : don't need multiplicity_of_component1, multiplicity, multiplicity0 
//                     or full_component etc
// Right now, we're using multiplicity_of_component1 and never multiplicity_of_component

/***************************************************************************************
  HELPER FUNCTIONS : GOING FROM PATCH TO PATCH
***************************************************************************************/

// Change of coordinates between the affine patchs of P^2 with weights w;
// writes variables on ith patch in terms of variables on jth patch.
// For use only in setting up the initial patches in the plane proj case.

function change_variables_between_P2_patches_i_to_j(pols, i, j, w)
  assert {i,j} subset {1,2,3} and i ne j;
  Pol := Universe(pols);
  assert Rank(Pol) eq 3; // Pol.1, Pol.2 are the affine coords on each patch
  assert w[i] eq 1 and w[j] eq 1; // only for the standard affine patches
  proj_vars := Insert([Pol.1, Pol.2], j, 1);
  subst := [proj_vars[ii]/proj_vars[i]^w[ii] : ii in [1..3]];
assert subst[i] eq 1;
  Remove(~subst, i);
  Append(~subst, Pol.3); // the extra variable is not involved
  return [Pol| f1*Denominator(f1) where f1 is Evaluate(f,subst) : f in pols];
end function;

// Change of coordinates between patches of the same linear blowup: 
// write variables on ith patch in terms of variables on jth patch

function change_variables_of_point_blowup_i_to_j(pols, i, j)
  assert i ne j;
  Pol := Universe(pols);
  vars := [Pol.i : i in [1..Rank(Pol)]];
  subst := [v/vars[i] : v in vars];
  subst[i] := vars[i]*vars[j];
  subst[j] := 1/vars[i];
  return [Pol| f1*Denominator(f1) where f1 is Evaluate(f,subst) : f in pols];
end function;
 
function change_variables_of_line_blowup_i_to_j(pols, i, j)
  assert i ne j;
  Pol := Universe(pols);
  vars := [Pol.i : i in [1..Rank(Pol)]];
  subst := ChangeUniverse(vars, FieldOfFractions(Pol));
  subst[i] := vars[i]*vars[j];
  subst[j] := 1/vars[i];
  return [Pol| f1*Denominator(f1) where f1 is Evaluate(f,subst) : f in pols];
end function;

// Map from patch1 to patch2, stringing together the blowup substitutions.
// Returned as sequence of elements in FieldOfFractions(Pol) where Pol
// is the polynomial ring of patch1.

function ancestors(model, patch)
  p := patch;
  inds := [p`index, p`parent];
  while p`parent ne <0,1> do 
    p := model`patches[p`parent];
    Append(~inds, p`parent);
  end while;
  return inds;
end function;

function map_between_patches(model, patch1, patch2)
  if Type(patch1) eq Tup then
    patch1 := model`patches[patch1];
    patch2 := model`patches[patch2];
  end if;

  // bottom patch = common ancestor of patch1 and patch2
  ancestors1 := ancestors(model, patch1);
  ancestors2 := ancestors(model, patch2);
  assert exists(bottom){idx: idx in ancestors1 | idx in ancestors2}; 

  assert patch1`index[1] gt 0 and patch2`index[1] gt 0; // silly case, not wanted

  // get map from patch1 down to bottom patch 
  patch := patch1;
  map_down := patch`map;
  while patch`parent[1] gt bottom[1] do
    patch := model`patches[patch`parent];
    map_down := [Evaluate(f, map_down) : f in patch`map];
  end while;
  assert patch`parent eq bottom;

  // get map from bottom patch up to patch2, working backwards
  patch := patch2;
  map_up := patch`map_inv;
  while patch`parent[1] gt bottom[1] do 
    patch := model`patches[patch`parent];
    map_up := [Evaluate(f, patch`map_inv) : f in map_up];
  end while;
  assert patch`parent eq bottom;

  patch1_to_patch2 := [Evaluate(f, map_down) : f in map_up];
  return patch1_to_patch2;
end function;

// Drag ideal across map, from patch idx1 to patch idx2

function drag_ideal(model, fib, idx1, idx2)
  Pol := Universe(model`patches[idx2]`eqns);
  idx2_to_idx1 := map_between_patches(model, idx2, idx1);
  return [Evaluate(polylift(g, Pol, model`res), idx2_to_idx1) : g in Generators(fib)];
end function;

// P is a polynomial ring over the global ring; 
// eqns is an ideal in P;
// x is in FieldOfFractions(P); 
// assume p is a *prime* ideal of P that contains eqns, and
// d is an ideal of P such that p + d has smaller dimension than p.
// Returns true if x is in p*P_d modulo eqns, where P_d 
// is the localization of P in which d becomes invertible.

// TO DO: not finished!!

function contained_in_prime_locally(eqns, x, p, d)
  if Type(x) eq SeqEnum then
    return forall{xx : xx in x | contained_in_prime_locally(eqns, xx, p, d)};
  elif Type(x) eq RngMPol then
    return forall{xx : xx in Basis(x) | contained_in_prime_locally(eqns, xx, p, d)};
  end if;

  assert eqns subset p;

  // x should be in P or FieldOfFractions(P)
  if debug then
    assert not d subset p;
  end if;
  Pol := Generic(p);
  x_is_poly, xx := IsCoercible(Pol, x);
  if x_is_poly then
    return xx in p;
  else
    f := Numerator(x);
    g := Denominator(x);
    if f notin p then
      return false;
    elif g notin p then
      return true;
    else // f, g both in p
      assert g notin eqns;
//printf "SyzygyModule: "; time
      SM := SyzygyModule([f, g] cat Basis(eqns));
      // TO DO: actually just want relations between f and g mod eqns
      // Next bit is pointless, could use syzygies := Basis(SM) instead
      SMfg := sub< EModule(Parent(f),2) | [ [b[1],b[2]] : b in Basis(SM)] >;
      // Groebner(SMfg);
      // syzygies := MinimalBasis(SMfg); 
      syzygies := Basis(SMfg); 
      for s in syzygies do
        // f/g == f1/g1 mod eqns
        g1 := s[1];
        f1 := s[2];
        if f1 notin p then
          return false;
        elif g1 notin p then
          return true;
        end if;
      end for;
      // f/g cannot be extended to (an open subset of) p
      return false;
    end if;
  end if;
end function;

/*****************************************************************************************
  SANITY CHECKS
*****************************************************************************************/

function has_been_blown_up(model, pt)
  return assigned pt`blownup
      or exists{i : i in pt`fibres | assigned model`abstract_fibres[i]`blownup};
end function;

procedure check_fibre(model, fib)
  k1 := fib`patch1; // must be assigned
  fibk1 := fib`explicit[k1]`ideal;
  assert fibre_meets_domain_with_dim_1(fibk1, model`patches[k1] : include_blownup);

  for k in Keys(fib`explicit) do
    fibk := fib`explicit[k]`ideal;
    patchk := model`patches[k];
    assert patchk`eqns_k subset fibk;
    if k ne k1 and not assigned fib`blownup then
      assert ideal_meets_domain(fibk, patchk`domain : include_blownup); 
    end if;
  end for;
end procedure;

procedure check_patch(patch)
  assert assigned patch`domain;
  assert Dimension(ideal< Universe(patch`eqns_k) | patch`eqns_k >) eq 1;
end procedure;

procedure check_model(model)
  for k in Keys(model`patches) do 
    check_patch(model`patches[k]);
  end for;
  for fib in model`abstract_fibres do 
    check_fibre(model, fib);
  end for;
  for pt in model`points do 
    idx := pt`patch;
    assert assigned pt`explicit[idx]`ideal;
    if has_been_blown_up(model, pt) then
      assert point_in_domain(model, pt, idx : include_blownup);
    else
      assert point_in_domain(model, pt, idx);
      for i in pt`fibres do 
        fib := model`abstract_fibres[i];
        assert fibre_meets_domain(fib`explicit[idx]`ideal, model`patches[idx]);
      end for; 
    end if;
  end for; 
end procedure;

/*****************************************************************************************
  SILLY STUFF FOR PRINTING
*****************************************************************************************/

function plural(n)
  return n eq 1 select "" else "s";
end function;

function grpab_to_string(C) 
  c := Invariants(C);
  if c eq [] then 
    return "trivial";
  end if;
  s := "";
  for i := 1 to #c do 
    s *:= "Z";
    if c[i] ne 0 then s *:= "/"*IntegerToString(c[i]); end if;
    if i lt #c then s *:= " + "; end if;
  end for;
  return s;
end function;

/*****************************************************************************************
  BLOWING UP POINTS AND FIBRES
*****************************************************************************************/

// This blows up model`points[pt_idx]

procedure blow_up_point(model, pt_idx)

  pt0 := model`points[pt_idx];
  idx0 := pt0`patch;
  idx1 := 1 + Max([ idx[1] : idx in Keys(model`patches) ]); // first unused index
  patch0 := model`patches[idx0];
  vprint RegularModel, 2: "Blowing up point on patch", idx0;

  k := model`k;
  res := model`res;
  P := model`P;
  pi := model`pi;

  if patch0`is_FU and pt0`field eq model`k then

    F := patch0`F;
    U := patch0`U;
    Pol := Parent(F);
    x := Pol.1;
    y := Pol.2;
    z := Pol.3;
    kpol := Universe(patch0`eqns_k);

    coords := pt0`explicit[idx0]`coords;
    x0,y0,z0 := Explode([lift(xx,res) : xx in coords]);
    blowdown_maps := [ [x+x0, x*y+y0, x*z+z0],
                       [y*x+x0, y+y0, y*z+z0],
                       [z*x+x0, z*y+y0, z+z0] ];
  //PolFF := FieldOfFractions(Pol);
    PolFF := FieldOfFractions(PolynomialRing(FieldOfFractions(BaseRing(Pol)), 3));
    xx := PolFF.1;
    yy := PolFF.2;
    zz := PolFF.3;
    blowdown_maps_inv := [ [xx-x0, (yy-y0)/(xx-x0), (zz-z0)/(xx-x0)],
                           [(xx-x0)/(yy-y0), yy-y0, (zz-z0)/(yy-y0)],
                           [(xx-x0)/(zz-z0), (yy-y0)/(zz-z0), zz-z0] ];
    /*
    blowdown_maps_inv := [ [x-x0, (y-y0)/(x-x0), (z-z0)/(x-x0)],
                           [(x-x0)/(y-y0), y-y0, (z-z0)/(y-y0)],
                           [(x-x0)/(z-z0), (y-y0)/(z-z0), z-z0] ]; // in FieldOfFractions(Pol)
    */
    vars := [x,y,z];
    vars_k := [polyres(v, kpol, res) : v in vars];  

    for i := 1 to 3 do
      v := vars[i];
      vk := vars_k[i];
      blowdown := blowdown_maps[i];
      F1 := Evaluate(F, blowdown);
      U1 := Evaluate(U, blowdown);
      // Get correct preimage: divide out powers of v from F1, so that F1 is not in (v,pi)
      while true do
        F1res := polyres(F1,kpol,res);
        if F1res notin ideal<kpol|vk> then
          break; 
        end if;
        // find a,b such that F1 = a*pi + b*v
        b := polylift(F1res div vk, Pol, res);
        a := (F1 - b*v) div pi;
        assert F1 eq a*pi + b*v;
        // use equation pi = U1, so F1 = a*pi + b*v = a*U1 + b*v
        assert (U1 div v)*v eq U1;
        F1 := a*(U1 div v) + b;
      end while;
      // Set up new patch
      patch1 := rec< patch_record | >;
      patch1`index := <idx1, i>;
      patch1`parent := patch0`index;
      patch1`map := blowdown;
      patch1`map_inv := blowdown_maps_inv[i];
      patch1`is_FU := true;
      patch1`F := F1;
      patch1`U := U1;
      patch1`eqns := [F1, pi-U1];
      patch1`eqns_k := polyres(patch1`eqns, kpol, res);
      patch1`ideal_k := ideal< kpol | patch1`eqns_k >;
      patch1`map_k := polyres(blowdown, kpol, res);
      model`patches[patch1`index] := patch1;
    end for; 

    // Don't use more patches than we need.  We take the 3rd patch by preference.
    // We only need to cover (a neighbourhood of) the blown up part of the surface,
    // and it suffices to check this for the special fibre.
    // First check 'polar points': in each patch, the point [0,0,0] is not seen on any other patch
    patches_needed := [i : i in [1..3] | 
                       forall{eqn : eqn in model`patches[<idx1,i>]`eqns_k | Evaluate(eqn, [0,0,0]) eq 0}];
    // if #patches_needed = 2 or 3, then these patches cover the scheme
    if #patches_needed le 1 then
      function surface_hits_ith_line_on_jth_patch(i, j)
        // the ith line is where vars[i] = 0, and the blown up part is where vars[j] = 0
        line := model`patches[<idx1,i>]`eqns_k cat [vars_k[j], vars_k[i]];
        return 1 notin ideal< kpol | line >;
      end function;
    end if;
    if #patches_needed eq 1 then
      // need to catch (non-polar) points not seen by this patch, ie where vars[i] = 0
      i := patches_needed[1];
      j := i ne 3 select 3 else 1;
      if surface_hits_ith_line_on_jth_patch(i,j) then
        patches_needed := Sort([i,j]);
      end if;
    elif #patches_needed eq 0 then
      // in this case, there are no polar points; 
      // use single patch if possible, otherwise any two will suffice
      if not surface_hits_ith_line_on_jth_patch(3,1) then
        patches_needed := [3];  // sufficient, since this means no points on line at infinity
      elif not surface_hits_ith_line_on_jth_patch(1,3) then   
        patches_needed := [1];
      elif not surface_hits_ith_line_on_jth_patch(2,3) then
        patches_needed := [2];
      else 
        patches_needed := [1,3];
      end if;
    end if;
    for i in [i : i in [1..3] | i notin patches_needed] do
      Remove(~model`patches, <idx1,i>);
    end for;
    assert patches_needed eq Sort(patches_needed); // assumed below

    // Compute stuff, only for the new patches that are needed
    for i in patches_needed do 
      patchi := model`patches[<idx1,i>];
      // the domains of the new patches form an open cover of the blowup 
      patchi`domain := < [PowerStructure(RngMPol)|], 
                         [PowerStructure(RngMPol)|], 
                         [ideal<kpol| [vars_k[ii] : ii in patches_needed | ii le i] >] >;
      model`patches[<idx1,i>] := patchi;
    end for;

    // Work out special fibre on new patches.

    // First pull back old components (that intersect the blowup) to each new patch
    // TO DO: avoid decomposition by calculating proper transform somehow?
    intn_pts := [];
    for old_fib_idx in pt0`fibres do 
      old_fib_rec := model`abstract_fibres[old_fib_idx];
      old_fib0 := old_fib_rec`explicit[idx0]`ideal; 
      for i in patches_needed do 
        patch := model`patches[<idx1,i>];
        full_trans := ideal< kpol | [Evaluate(b, patch`map_k) : b in Basis(old_fib0)] >;
        old_fib1 := [ff : ff in RadicalDecomposition(full_trans) | vars_k[i] notin ff]; // not inside blowup
        assert #old_fib1 le 1; // proper transform of old_fib0, if it appears on this patch
        // only if it meets the blowup, inside the patch domain:
        if #old_fib1 eq 1 and ideal_meets_domain(ideal<kpol|vars_k[i]> + old_fib1[1], patch`domain) then
          old_fib_rec`explicit[<idx1,i>] := 
                      rec< fibre_on_patch_record | patch_index := <idx1,i>, ideal := old_fib1[1] >;
          // find intersections with blowup that aren't visible on previous patches
          vanishing := ideal<kpol| [vars_k[ii] : ii in patches_needed | ii le i] >;
          intn_pts cat:= [<i,I> : I in RadicalDecomposition(vanishing + old_fib1[1])];
        end if;
      end for; // i
      assert idx1 in [k[1] : k in Keys(old_fib_rec`explicit)];
      model`abstract_fibres[old_fib_idx] := old_fib_rec;
    end for; // old_fib_idx

    // Compute new components (that lie in blow up), on every new patch
    // TO DO: avoid computing the same decomposition over and over again?
    new_fibs := [* *];
    new_fib_recs := [* *];
    nonreg_pts := [];
    for i in patches_needed do
      // find fibs that appear on ith patch but not on previous patches 
      // TO DO: could make decomposition easier by first breaking it up by factors of U1 
      patchi := model`patches[<idx1,i>];
      subscheme := ideal< kpol | [vars_k[ii] : ii in patches_needed | ii le i] cat patchi`eqns_k >; 
      assert Dimension(subscheme) le 1;
      if Dimension(subscheme) le 0 then 
        continue i;
      end if;
      fibs_red := RadicalDecomposition(subscheme);
      new_fibs cat:= [* <i, I> : I in fibs_red | Dimension(I) eq 1 *];
      // TO DO: full component is only needed if fibre turns out to be regular (tested below)
    end for; // i

    // Deal with the new fibres: 
    // get equations on other patches, find intersections, check regularity, create records...
    for tup in new_fibs do 
      i, fib := Explode(tup);
      patchi := model`patches[<idx1,i>];
      fib_on_patch := rec< fibre_on_patch_record | patch_index := <idx1,i>, ideal := fib >;
      fibab := blank_abstract_fibre_record();
      fibab`patch1 := <idx1,i>;
      fibab`explicit[<idx1,i>] := fib_on_patch;
      // find fibre on other patches 
      for j in [j: j in patches_needed | j gt i] do
        patchj := model`patches[<idx1,j>];
        // substitution introduces denominators, only involving vars[i] 
        // (but we don't care about fibres contained in vars[i] = 0 on the jth patch)
        fibsubst := ideal< kpol | change_variables_of_point_blowup_i_to_j(Basis(fib), i, j) >;
        fibsj := [ff : ff in RadicalDecomposition(fibsubst) | vars_k[i] notin ff];
        assert #fibsj le 1; // = transform of fib, if it appears on this patch
        if #fibsj ne 0 then
          fibj := fibsj[1];
          if ideal_meets_domain(fibj, patchj`domain) then
            fibab`explicit[<idx1,j>] := rec< fibre_on_patch_record | 
                                             patch_index := <idx1,j>, ideal := fibj >;
          end if;
        end if;
      end for;
      // collect intersections with other fibres
      for fibab1 in new_fib_recs do 
        for j in patches_needed do 
          if IsDefined(fibab`explicit, <idx1,j>) and IsDefined(fibab1`explicit, <idx1,j>) then
            // get intersections not appearing on previous patches
            intn := ideal< kpol | [vars_k[jj] : jj in patches_needed | jj lt j] >
                   + fibab`explicit[<idx1,j>]`ideal + fibab1`explicit[<idx1,j>]`ideal;
            assert Dimension(intn) le 0;
            intn_pts cat:= [<j,I> : I in RadicalDecomposition(intn)];
          end if;
        end for;    
      end for;    
      // test regularity along the new fibre 
      // TO DO: could test just on one patch, then check the missing points
      vprintf RegularModel, 3: "check_regularity_on_fib, i = %o : ", i; 
      vtime RegularModel, 3:
      fibab_is_reg, nonreg_ptsi := check_regularity_on_fib(model, patchi, fib);
      if assigned fibab`is_regular then
assert false; // can it be assigned?
        assert fibab`is_regular eq fibab_is_reg;
      else   
         fibab`is_regular := fibab_is_reg;
      end if;
      if fibab`is_regular then
        nonreg_pts cat:= [<i,pt> : pt in nonreg_ptsi];
      end if;
      for j in [j: j in patches_needed | j gt i and <idx1,j> in Keys(fibab`explicit)] do
        vprintf RegularModel, 3: "check_regularity_on_fib, j = %o : ", j; 
        vtime RegularModel, 3:
        bool, nonreg_ptsj := check_regularity_on_fib(model, model`patches[<idx1,j>], fibab);
        assert bool eq fibab`is_regular;
        if bool then
          for pt in nonreg_ptsj do 
            if 1 notin pt + ideal<kpol| [vars_k[ii] : ii in patches_needed | ii lt j]> then 
              // pt was not seen on previous patches
              Append(~nonreg_pts, <j,pt>);
            end if;
          end for;
        end if;
      end for;
      Append(~new_fib_recs, fibab); 
    end for; // tup in new_fibs
    model`abstract_fibres cat:= new_fib_recs;

    // Make records for the new points; check for repeated points. 
    // (We map each point across to the other patches of the blowup, 
    // although this is not actually necessary, as long as we observe
    // the convention above of listing each point on the first patch 
    // on which it appears, and not duplicating it on other patches.)
    new_pt_recs := [* *];
    new_pts := Sort(Setseq({<tup[1],tup[2],false> : tup in nonreg_pts})) cat 
               Sort(Setseq({<tup[1],tup[2],true> : tup in intn_pts | tup notin nonreg_pts}));
    for tup in new_pts do 
      i, idli := Explode(tup); assert i in patches_needed;
      // check if already have this point
      for pt1 in new_pt_recs do 
        if IsDefined(pt1`explicit, <idx1,i>) and pt1`explicit[<idx1,i>]`ideal eq idli then
          continue tup; 
        end if;
      end for;
      pt := blank_point_record();
      pt`patch := <idx1,i>;
      pt`is_regular := tup[3];
      // find point on all patches_needed where it appears
      for j in patches_needed do 
        if j eq i then
          idlj := idli;
        elif vars_k[j] notin idli then // appears on jth patch
          idlj := ideal< kpol | change_variables_of_point_blowup_i_to_j(Basis(idli), i, j) >;
          assert Dimension(idlj) eq 0 and IsPrime(idlj);
        else
          continue j;
        end if;
        coordsj := pt_coords_from_ideal(idlj);
        pt`explicit[<idx1,j>] := rec< point_on_patch_record | patch_index := <idx1,j>,
                                                              coords := coordsj,
                                                              ideal  := idlj >; 
        pt`field := Universe(coordsj);
      end for;
      // which fibres is pt contained in? (some redundant checking, for sake of simplicity)
      pt`fibres := {};
      for j := 1 to #model`abstract_fibres do
        fibj := model`abstract_fibres[j]`explicit;
        if IsDefined(fibj, pt`patch) then  // (only defined for relevant fibres)
          if fibj[pt`patch]`ideal subset pt`explicit[pt`patch]`ideal then
            pt`fibres join:= {j};
          end if;
        end if;
      end for;
      assert not pt`is_regular or #pt`fibres ge 2; // check: points are either nonreg or intersections
      Append(~new_pt_recs, pt);
    end for;
    model`points cat:= new_pt_recs;
  
  else
    error "Not implemented";
  end if;

  // Record that the point has been blown up
  model`points[pt_idx]`blownup := idx1; 
  Append(~model`patches[idx0]`domain[2], pt0`explicit[idx0]`ideal); 

end procedure;

///////////////////////////////////////////////////////////////////////////////////////////////
//  Blowing up a line 
///////////////////////////////////////////////////////////////////////////////////////////////

// decide if bas contains an element of the form c*(v-f(w)), and if so return f(w) 

function is_func(bas, v, w)
  P := Universe(bas);
  vars := {P.i : i in [1..Rank(P)]} diff {w};
  for b in bas do 
    c := MonomialCoefficient(b,v);
    cfw := c*v - b;
    if c ne 0 and forall{x: x in vars | Degree(cfw,x) le 0} then
      return true, cfw/c;
    end if;
  end for;
  return false, _;
end function;

// This blows up model`abstract_fibres[fib_idx]

procedure blow_up_line(model, fib_idx)

 fib0 := model`abstract_fibres[fib_idx];

 if debug then 
   assert 1 eq #{k : k in Keys(fib0`explicit) 
                   | fibre_meets_domain_with_dim_1(fib0`explicit[k]`ideal, model`patches[k])};
 end if;
 assert exists(idx01){k : k in Keys(fib0`explicit) 
                        | fibre_meets_domain_with_dim_1(fib0`explicit[k]`ideal, model`patches[k])};
 indices0 := [idx01];
 indices0 cat:= [k : k in Keys(fib0`explicit)
                   | k ne idx01 and fibre_meets_domain(fib0`explicit[k]`ideal, model`patches[k])];

 for idx0 in indices0 do

  idx1 := 1 + Max([ idx[1] : idx in Keys(model`patches) ]); // first unused index
  patch0 := model`patches[idx0];
  vprint RegularModel, 2: "Blowing up fibre on patch", idx0;

  k := model`k;
  res := model`res;
  P := model`P;
  pi := model`pi;

  if patch0`is_FU then

    F := patch0`F;
    U := patch0`U;
    Pol := Parent(F);
    kpol := Universe(patch0`eqns_k);
    x := Pol.1;
    y := Pol.2;
    z := Pol.3;
    xx := kpol.1;
    yy := kpol.2;
    zz := kpol.3;
    vars := [x,y,z];
    vars_k := [xx,yy,zz];
    assert vars_k eq [polyres(v, kpol, res) : v in vars];  

    // Try to transform the fibre to a line in AffineSpace(kpol), namely {yy = zz = 0}
    fib0idl := fib0`explicit[idx0]`ideal;
    Groebner(fib0idl); // do this first because easier than in "lex"
    change_vars := [];
    _kpol := PolynomialRing(k, 3, "lex");
    _vars := [_kpol.1, _kpol.2, _kpol.3];
    // does fibre have the form yy = r(xx), zz = s(xx) ?
    _zz,_yy,_xx := Explode(_vars); // (use term order in which xx is lowest)
    _fib0idl := ideal< _kpol | [Evaluate(b, [_xx,_yy,_zz]) : b in Basis(fib0idl)] >;
    bas := GroebnerBasis(_fib0idl);
    bool1, _yx := is_func(bas, _yy, _xx);
    bool2, _zx := is_func(bas, _zz, _xx);
    if bool1 and bool2 then
      yx := polylift(Evaluate(_yx, [zz,yy,xx]), Pol, res); // careful: replace _zz by zz etc
      zx := polylift(Evaluate(_zx, [zz,yy,xx]), Pol, res);
      change_vars     := [x, y-yx, z-zx];
      change_vars_inv := [x, y+yx, z+zx];
    end if;
    if change_vars eq [] then
      // does fibre have the form zz = r(yy), xx = s(yy) ?
      _xx,_zz,_yy := Explode(_vars);
      _fib0idl := ideal< _kpol | [Evaluate(b, [_xx,_yy,_zz]) : b in Basis(fib0idl)] >;
      bas := GroebnerBasis(_fib0idl);
      bool1, _zy := is_func(bas, _zz, _yy);
      bool2, _xy := is_func(bas, _xx, _yy);
      if bool1 and bool2 then
        zy := polylift(Evaluate(_zy, [xx,zz,yy]), Pol, res); // careful
        xy := polylift(Evaluate(_xy, [xx,zz,yy]), Pol, res);
        change_vars     := [y, z-zy, x-xy];
      //change_vars_inv := [z+xy, x, y+zy];
        xy1 := Evaluate(xy, [0,x,0]);
        zy1 := Evaluate(zy, [0,x,0]);
        change_vars_inv := [z+xy1, x, y+zy1];
      end if;
    end if;
    if change_vars eq [] then
      // does fibre have the form xx = r(zz), yy = s(zz) ?
      _yy,_xx,_zz := Explode(_vars);
      _fib0idl := ideal< _kpol | [Evaluate(b, [_xx,_yy,_zz]) : b in Basis(fib0idl)] >;
      bas := GroebnerBasis(_fib0idl);
      bool1, _xz := is_func(bas, _xx, _zz);
      bool2, _yz := is_func(bas, _yy, _zz);
      if bool1 and bool2 then
        xz := polylift(Evaluate(_xz, [yy,xx,zz]), Pol, res); // careful
        yz := polylift(Evaluate(_yz, [yy,xx,zz]), Pol, res);
        change_vars     := [z, x-xz, y-yz];
      //change_vars_inv := [y+xz, z+yz, x];
        xz1 := Evaluate(xz, [0,0,x]);
        yz1 := Evaluate(yz, [0,0,x]);
        change_vars_inv := [y+xz1, z+yz1, x];
      end if;
    end if;
    error if change_vars eq [],
         "Can't blow up fibre (failed to find an affine transformation to a line)";
//"change_vars", change_vars;
//"change_vars_inv", change_vars_inv;
    assert [Evaluate(c,change_vars_inv) : c in change_vars] eq [x,y,z];
    assert [Evaluate(c,change_vars) : c in change_vars_inv] eq [x,y,z];
    assert fib0idl eq ideal<kpol| [polyres(change_vars[i], kpol, res) : i in [2,3]]>; 

    blowdown_maps := [ [],                                               // place holder
                       [Evaluate(l,[x,y,y*z]) : l in change_vars_inv],   // divide by y
                       [Evaluate(l,[x,y*z,z]) : l in change_vars_inv] ]; // divide by z
    blowdown_maps_inv := [ [], 
                           [Evaluate(r,change_vars) : r in [x,y,z/y]],
                           [Evaluate(r,change_vars) : r in [x,y/z,z]] ]; // in FieldOfFractions(Pol)

// _<x,y,z> := Pol; _<xx,yy,zz> := kpol; // helpful for debugging

// Starting here, the code is copied from blow_up_point; all differences are flagged

// Unchanged except for values of i
    for i := 2 to 3 do
      v := vars[i];
      vk := vars_k[i];
      blowdown := blowdown_maps[i];
      F1 := Evaluate(F, blowdown);
      U1 := Evaluate(U, blowdown);
      // Get correct preimage: divide out powers of v from F1, so that F1 is not in (v,pi)
      while true do
        F1res := polyres(F1,kpol,res);
        if F1res notin ideal<kpol|vk> then
          break; 
        end if;
        // find a,b such that F1 = a*pi + b*v
        b := polylift(F1res div vk, Pol, res);
        a := (F1 - b*v) div pi;
        assert F1 eq a*pi + b*v;
        // use equation pi = U1, so F1 = a*pi + b*v = a*U1 + b*v
        assert (U1 div v)*v eq U1; // TO DO: why must U1 be divisible by v?
        F1 := a*(U1 div v) + b;
      end while;
      // Set up new patch
      patch1 := rec< patch_record | >;
      patch1`index := <idx1, i>;
      patch1`parent := patch0`index;
      patch1`map := blowdown;
      patch1`map_inv := blowdown_maps_inv[i];
      patch1`is_FU := true;
      patch1`F := F1;
      patch1`U := U1;
      patch1`eqns := [F1, pi-U1];
      patch1`eqns_k := polyres(patch1`eqns, kpol, res);
      patch1`ideal_k := ideal< kpol | patch1`eqns_k >;
      patch1`map_k := polyres(blowdown, kpol, res);
      model`patches[patch1`index] := patch1;
    end for; 

// New
    // Determine which patches are needed, then set domains
    patches_needed := [];
    for i in [2,3] do 
      patchi := model`patches[<idx1,i>];
      vs := [vars_k[2], vars_k[3]]; // the subscheme not visible on other patches
      domain := < [ideal<kpol| [Evaluate(b, patchi`map_k) : b in Basis(D)]> : D in patch0`domain[1] cat patch0`domain[2]],
                               [PowerStructure(RngMPol)|],
                               [ideal<kpol| vs cat [Evaluate(b, patchi`map_k) : b in Basis(D)]> : D in patch0`domain[3]] >;
      if ideal_meets_domain(ideal<kpol| patchi`eqns_k>, domain) then
        Append(~patches_needed, i);
      end if;
    end for;
    if IsEmpty(patches_needed) then // either 2 or 3 will do
      patches_needed := [3];   
    end if;
    // Set domains (not quite the same as domain above)
    for i in [2,3] do 
      if i in patches_needed then 
        patchi := model`patches[<idx1,i>];
        // The domains of the new patches form a (disjoint) cover of the blowup.
        // Conventions: each patch covers as much as possible (as i increases), 
        // and the excluded bits all come from below.
        vs := [vars_k[ii] : ii in patches_needed | ii le i];
        patchi`domain := < [ideal<kpol| [Evaluate(b, patchi`map_k) : b in Basis(D)]> : D in patch0`domain[1] cat patch0`domain[2]], 
                           [PowerStructure(RngMPol)|], 
                           [ideal<kpol| vs cat [Evaluate(b, patchi`map_k) : b in Basis(D)]> : D in patch0`domain[3]] >;
        model`patches[<idx1,i>] := patchi;
      else
        Remove(~model`patches, <idx1,i>);
      end if;
    end for;

    // Work out special fibre on new patches

    // Pull back old components that intersect the blowup (within the patch domain) to each new patch
    // TO DO: avoid decomposition by calculating proper transform somehow?
// Differences: old_fibres instead of pt0`fibres
    old_fibres := {};
    for ipt in model`points do
      if fib_idx in ipt`fibres then  // ipt lies on the blown up fibre
        if ipt`patch eq idx0 and point_in_domain(model, ipt, idx0) then
          old_fibres join:= ipt`fibres diff {fib_idx};
        end if;
      end if;
    end for;
    intn_pts := [];
    for old_fib_idx in old_fibres do 
      old_fib_rec := model`abstract_fibres[old_fib_idx];
      old_fib0 := old_fib_rec`explicit[idx0]`ideal; 
      for i in patches_needed do 
        patch := model`patches[<idx1,i>];
        full_trans := ideal< kpol | [Evaluate(b, patch`map_k) : b in Basis(old_fib0)] >;
        old_fib1 := [ff : ff in RadicalDecomposition(full_trans) | vars_k[i] notin ff]; // not inside blowup
        assert #old_fib1 le 1; // proper transform of old_fib0, if it appears on this patch
        // only if it meets the blowup, inside the patch domain:
        if #old_fib1 eq 1 and ideal_meets_domain(ideal<kpol|vars_k[i]> + old_fib1[1], patch`domain) then
          old_fib_rec`explicit[<idx1,i>] := 
                      rec< fibre_on_patch_record | patch_index := <idx1,i>, ideal := old_fib1[1] >;
          // find intersections with blowup that aren't visible on previous patches
          vanishing := ideal<kpol| [vars_k[ii] : ii in patches_needed | ii le i] >;
          intn_pts cat:= [<i,I> : I in RadicalDecomposition(vanishing + old_fib1[1])];
        end if;
      end for; // i
      assert idx1 in [k[1] : k in Keys(old_fib_rec`explicit)];
      model`abstract_fibres[old_fib_idx] := old_fib_rec;
    end for; // old_fib_idx

// Differences: added old_new_fibs_indices, domain condition
    // Compute new components (that lie in blow up), on every new patch
    // TO DO: avoid computing the same decomposition over and over again?
    new_fibs := [* *];
    new_fib_recs := [* *];
    old_new_fibs_indices := []; // index in model`abstract_fibres if fibre is identified in a remote patch
    nonreg_pts := [];
    for i in patches_needed do
      // find fibs that are visible on ith patch but not on previous patches 
      // (this relies on the conventions about the patch domains stated above)
      // TO DO: could make decomposition easier by first breaking it up by factors of U1 
      patchi := model`patches[<idx1,i>];
      subscheme := ideal< kpol | [vars_k[ii] : ii in patches_needed | ii le i] cat patchi`eqns_k >;
      assert Dimension(subscheme) le 1;
      if Dimension(subscheme) le 0 then 
        continue i;
      end if;
      fibs_red := [I : I in RadicalDecomposition(subscheme) | fibre_meets_domain(I, patchi)];
      new_fibs cat:= [* <i, I> : I in fibs_red | Dimension(I) eq 1 *];
      // TO DO: full component is only needed if fibre turns out to be regular (tested below)
    end for; // i

    // Deal with the new fibres: 
    // get equations on other patches, find intersections, check regularity, create records...
//New 
    // Distinguish between new_fibs that blow down to a point rather than the whole fibre;
    // the latter kind already showed up on other patches if idx0 is not idx01, so identify them
    if idx0 eq idx01 then
      new_fibs_in_blowup_of_idx01 := {}; // not used in this case
    end if;
    for tup in new_fibs do 
      i, fib := Explode(tup);
      patchi := model`patches[<idx1,i>];
      if idx0 ne idx01 and dimension_of_image(fib, patchi`map) eq 1 then
        // identify this fibre among the new fibres that appeared in the blow up of patch idx01;
        found := [];
        for j in new_fibs_in_blowup_of_idx01 do 
          fibj := model`abstract_fibres[j]; 
          for idxj in Keys(fibj`explicit) do 
            gens := drag_ideal(model, fib, <idx1,i>, idxj);
            fibj_idl := fibj`explicit[idxj]`ideal;
            fibj_idl_lift := lift_ideal(fibj_idl, Pol, res, pi);
            excludedj := excluded(model, idxj);
            excludedj_lift := lift_ideal(excludedj, Pol, res, pi);
            // TO DO: eqnsj
            eqnsj := Ideal(model`patches[idxj]`eqns);
            if contained_in_prime_locally(eqnsj, gens, fibj_idl_lift, excludedj_lift) then
              Append(~found, j);
              if debug then
                break idxj;
              else
                break j;
              end if;
            end if;
          end for;
        end for;
        assert #found eq 1;
        j := found[1];
        Append(~old_new_fibs_indices, j); // new_fib is the jth fibre
        fibab := model`abstract_fibres[j];
      else
        Append(~old_new_fibs_indices, 0); // new_fib is completely new
        fibab := blank_abstract_fibre_record();
        fibab`patch1 := <idx1,i>;
      end if;
      fibab`explicit[<idx1,i>] := rec< fibre_on_patch_record | patch_index := <idx1,i>, ideal := fib >;

//Differences: domain condition
      // find fibre on the other patches of this blowup
      for j in [j: j in patches_needed | j gt i] do
        patchj := model`patches[<idx1,j>];
        // substitution introduces denominators, only involving vars[i] 
        // (but we don't care about fibres contained in vars[i] = 0 on the jth patch)
        fibsubst := ideal< kpol | change_variables_of_line_blowup_i_to_j(Basis(fib), i, j) >;
        fibsj := [ff : ff in RadicalDecomposition(fibsubst) 
                     | vars_k[i] notin ff and fibre_meets_domain(ff, patchj)];
        assert #fibsj le 1; // = transform of fib, if it appears on this patch
        if #fibsj ne 0 then 
          fibj := fibsj[1];
          if ideal_meets_domain(fibj, patchj`domain) then
            fibab`explicit[<idx1,j>] := rec< fibre_on_patch_record | 
                                             patch_index := <idx1,j>, ideal := fibj >;
          end if;
        end if;
      end for;
      // collect intersections with other fibres
      for fibab1 in new_fib_recs do 
        for j in patches_needed do 
          if IsDefined(fibab`explicit, <idx1,j>) and IsDefined(fibab1`explicit, <idx1,j>) then
            // get intersections not appearing on previous patches
            intn := ideal< kpol | [vars_k[jj] : jj in patches_needed | jj lt j] >
                   + fibab`explicit[<idx1,j>]`ideal + fibab1`explicit[<idx1,j>]`ideal;
            assert Dimension(intn) le 0;
            intn_pts cat:= [<j,I> : I in RadicalDecomposition(intn)];
          end if;
        end for;    
      end for;    
      // test regularity along the new fibre 
      // TO DO: could test just on one patch, then check the missing points
      vprintf RegularModel, 3: "check_regularity_on_fib, i = %o : ", i; 
      vtime RegularModel, 3:
      fibab_is_reg, nonreg_ptsi := check_regularity_on_fib(model, patchi, fib);
      if assigned fibab`is_regular then
        assert fibab`is_regular eq fibab_is_reg;
      else   
         fibab`is_regular := fibab_is_reg;
      end if;
      if fibab`is_regular then
        nonreg_pts cat:= [<i,pt> : pt in nonreg_ptsi];
      end if;
      for j in [j: j in patches_needed | j gt i and <idx1,j> in Keys(fibab`explicit)] do
        patchj := model`patches[<idx1,j>];
        vprintf RegularModel, 3: "check_regularity_on_fib, j = %o : ", j; 
        vtime RegularModel, 3:
        bool, nonreg_ptsj := check_regularity_on_fib(model, patchj, fibab); 
        assert bool eq fibab`is_regular;
        if bool then
          for pt in nonreg_ptsj do 
            if 1 notin pt + ideal<kpol| [vars_k[ii] : ii in patches_needed | ii lt j]> then 
              // pt was not seen on previous patches
              Append(~nonreg_pts, <j,pt>);
            end if;
          end for;
        end if;
      end for;
      Append(~new_fib_recs, fibab); 
    end for; // tup in new_fibs

// New
    if idx0 eq idx01 then
      new_fibs_in_blowup_of_idx01 := [#model`abstract_fibres + 1 .. #model`abstract_fibres + #new_fib_recs];
    end if;
    assert #new_fib_recs eq #new_fibs and #old_new_fibs_indices eq #new_fibs;
    for r := 1 to #new_fib_recs do 
      rr := old_new_fibs_indices[r];
      if rr eq 0 then 
        Append(~model`abstract_fibres, new_fib_recs[r]);
      else
        model`abstract_fibres[rr] := new_fib_recs[r];
      end if;
    end for;

// Differences: change_variables_of_line_blowup_i_to_j, check domain
    // Make records for the new points; check for repeated points. 
    // (DON'T map each point across to the other patches of the blowup, 
    // although this is not actually necessary, as long as we observe
    // the convention above of listing each point on the first patch 
    // on which it appears, and not duplicating it on other patches.)
    new_pt_recs := [* *];
    new_pts := Sort(Setseq({<tup[1],tup[2],false> : tup in nonreg_pts})) cat 
               Sort(Setseq({<tup[1],tup[2],true> : tup in intn_pts | tup notin nonreg_pts}));
    new_pts := [tup : tup in new_pts | _point_in_domain(tup[2], model`patches[<idx1,tup[1]>]) ];
    for tup in new_pts do 
      i, idli := Explode(tup); assert i in patches_needed;
      // check if already have this point
      for pt1 in new_pt_recs do 
        if IsDefined(pt1`explicit, <idx1,i>) and pt1`explicit[<idx1,i>]`ideal eq idli then
          continue tup; 
        end if;
      end for;
      pt := blank_point_record();
      pt`patch := <idx1,i>;
      pt`is_regular := tup[3];
      /* NO NEED TO
      // find point on all patches_needed where it appears
      for j in patches_needed do 
      */
      for j in [i] do
        if j eq i then
          idlj := idli;
        elif vars_k[j] notin idli then // appears on jth patch
          idlj := ideal< kpol | change_variables_of_line_blowup_i_to_j(Basis(idli), i, j) >;
          assert Dimension(idlj) eq 0 and IsPrime(idlj);
        else
          continue j;
        end if;
        coordsj := pt_coords_from_ideal(idlj);
        pt`explicit[<idx1,j>] := rec< point_on_patch_record | patch_index := <idx1,j>,
                                                              coords := coordsj,
                                                              ideal  := idlj >; 
        pt`field := Universe(coordsj);
      end for;
      // which fibres is pt contained in? (some redundant checking, for sake of simplicity)
      pt`fibres := {};
      for j := 1 to #model`abstract_fibres do
        fibj := model`abstract_fibres[j]`explicit;
        if IsDefined(fibj, pt`patch) then  // (only for relevant fibres)
          if fibj[pt`patch]`ideal subset pt`explicit[pt`patch]`ideal then
            pt`fibres join:= {j};
          end if;
        end if;
      end for;
      assert not pt`is_regular or #pt`fibres ge 2; // points are either nonreg or intersections
      Append(~new_pt_recs, pt);
    end for;
    model`points cat:= new_pt_recs;

  else
    error "Not implemented";
  end if;

  // Record that the fibre has been blown up on patch idx0
  if not assigned model`abstract_fibres[fib_idx]`blownup then
    model`abstract_fibres[fib_idx]`blownup := [<idx0,idx1>];
  else
    Append(~model`abstract_fibres[fib_idx]`blownup, <idx0,idx1>);
  end if;
  // exclude the blown up fibre from the patch domain
  Append(~model`patches[idx0]`domain[2], fib0`explicit[idx0]`ideal); 

 end for; // idx0 in indices0

end procedure;

/*****************************************************************************************
  MAIN INTRINSIC
*****************************************************************************************/

// TO DO: What type should P have? Common structure for ideals in Z and F[t] would be Rng?

intrinsic RegularModel(C::Crv, P::Any: Warnings:=true) -> CrvRegModel  
{Given a curve C over a global field K, and a maximal ideal of the maximal order R of K, 
returns a model which is regular as an arithmetic surface over the localization R_(P).
The given model must be integral and its special fibre above P must have dimension 1}

  K := BaseRing(C);
  fldrat := Type(K) eq FldRat;
  fldnum := ISA(Type(K), FldAlg);
  fldfunrat := ISA(Type(K), FldFunRat);
  fldfun := ISA(Type(K), FldFunG);
  require fldrat or fldnum or fldfun:
         "The curve must be defined over the rationals, a number field, or a function field";
  
if fldrat or fldnum or fldfunrat then

  R := Integers(K);
  
  if ISA(Type(P), RngElt) then 
    bool, pi := IsCoercible(R, P);
    require bool : "The second argument is invalid";
    P := ideal<R | pi>; 
  else 
    require Type(P) in {RngInt, RngUPol} or ISA(Type(P), RngOrdIdl) :
           "The second argument should be an ideal of the ring of integers of the base field of the curve";
    if Type(P) in {RngInt, RngUPol} then
      pi := Generator(P); 
    else
      bool, pi := IsPrincipal(P);
      require bool : "Currently only for principal primes, sorry";
    end if;
    pi := R!pi;
  end if;
  require IsPrime(P) and P ne ideal<R|0> : "The second argument should be a maximal ideal";

else if Warnings then "WARNING: FldFun case probably will not work yet!!"; end if;

  require Type(P) eq RngFunOrdIdl: "Over function fields, the second argument must be an ideal";
  R := Order(P);
  bool, pi := IsPrincipal(P); // TO DO: not allowed for infinite max order
  require bool : "Currently only for principal primes, sorry";
  pi := R!pi;

end if;

  // CHECK CACHE
  if assigned C`RegularModels then
    key := fldfunrat select pi else P; // P not allowed in fldfunrat case (no hashing)
    bool, model := IsDefined(C`RegularModels, key);
    if bool then
      return model;
    end if;
  end if;
 
  AC := Ambient(C);
  coeffs := [c : c in Coefficients(eqn), eqn in DefiningEquations(C)];

  require (IsAffine(AC) or IsProjective(AC)) and Dimension(AC) eq 2 and #DefiningEquations(C) eq 1 : 
         "The given curve must be an affine or projective plane curve";
  require IsAbsolutelyIrreducible(C) : 
         "The given curve must be absolutely irreducible";
  require IsNonsingular(C) :           
         "The given curve must be nonsingular"; 
  require forall {IsCoercible(c,R) : c in coeffs} : 
         "The curve must be given by equations with integral coefficients";

  // Start with a more minimal model, if one is available
  // TO DO: CrvEll
  // TO DO: for other kinds of curves?
  // TO DO: for CrvHyp over FldAlg at primes over 2, uncomplete the square
 /* mm := 0;
  // oops, this was wrong, because the map C1 -> C is not necessarily
  // a morphism of schemes over Z
  if Type(C) eq CrvHyp and Type(K) in {FldRat, FldFunRat} then
    vD := Valuation(Discriminant(C), pi);
    assert vD ge 0;
    if vD gt 0 then
      C1, mm := pMinimalWeierstrassModel(C, pi);
      // use C1 only if it's better
      if Valuation(Discriminant(C1), pi) ge vD then
        mm := 0;
      end if;
    end if;
  end if;
  if mm cmpne 0 then
    vprintf RegularModel: "Starting with minimal model: %o\n", C1;
    model := RegularModel(C1, P);
    model`C := C;
    // compose the bottom map with mm : C -> C1
    assert Domain(mm) eq C and Codomain(mm) eq C1;
    for k in Keys(model`patches) do
      assert k[1] gt 0; // would need to adjust patch <0,1> if it exists
      if k[1] eq 1 then
        patch := model`patches[k];
        assert patch`parent eq <0,1>;
        model`patches[k]`map := [Evaluate(f,patch`map) : f in DefiningEquations(Inverse(mm))];
        if assigned patch`map_inv then
          model`patches[k]`map_inv := [Evaluate(f,DefiningEquations(mm)) : f in patch`map_inv];
        end if;
      end if;
    end for;
    return model;
  end if;*/

  k, res := ResidueClassField(P);

  model := New(CrvRegModel);
  model`C := C;
  model`K := K;
  model`R := R;
  model`P := P;
  model`pi := pi;
  model`k := k;
  model`res := res;
  model`extended_res := [* [* K,res *] *]; // can't use Assoc (no common structure)

  model`patches := AssociativeArray(Parent(<0,0>));
  model`abstract_fibres := [* *];
  model`points := [* *];

  // SET UP INITIAL PATCHES
  // Affine plane case: only one patch, the given curve
  // Projective plane case: patches are (based on) a subset of the standard affine patches
  // Non-plane case: patches are the smooth parts of several projections to the affine plane

  // These same poly rings are used throughout
  Pol := PolynomialRing(R, 3, "grevlex");
  x := Pol.1;
  y := Pol.2;
  z := Pol.3;
  kpol := PolynomialRing(k, 3, "grevlex");
  xx := kpol.1;
  yy := kpol.2;
  IdlU := PowerStructure(RngMPol);

  PolC := ChangeRing(CoordinateRing(AC), R);
  kpolC := PolynomialRing(k, Rank(PolC));
  dim := Dimension(AC);

  // To help debugging
  if debug_names then
     if not IsPrimeField(k) then
       _<a> := k;
     end if;
     _<x,y,z> := Pol;
     _<xx,yy,zz> := kpol;
     if IsAffine(AC) then
	 _<xC,yC> := PolC;
	 _<xxC,yyC> := kpolC;
     else
	 _<xC,yC,zC> := PolC;
	 _<xxC,yyC,zzC> := kpolC;
     end if;
  end if;

  if dim eq 2 then
    require #DefiningEquations(C) eq 1 :
           "Plane curve should be defined by a single equation";
    eqnC := PolC! DefiningEquations(C)[1];
    require polyres(eqnC, kpolC, res) ne 0 : 
           "The defining equations of the curve do not reduce to a curve mod P";
  else
    require Dimension(BaseChange(C, k, res)) eq 1 :
           "The defining equations of the curve do not reduce to a curve mod P";
  end if;

  if dim eq 2 and IsAffine(AC) then

    // Make sure the points at infinity on the special fibre are regular.
    // The line at infinity on C's patch is {v=0} on these patches:
    u := PolC.1; 
    v := PolC.2;
    other_affine_patches := [PolC| v^Degree(eqnC)*Evaluate(eqnC, [1/v,u/v]),
                                   v^Degree(eqnC)*Evaluate(eqnC, [u/v,1/v]) ]; 
    for g in other_affine_patches do
      // check points of special fibre intersect {v=0}
      gv := ideal< kpolC | [polyres(v,kpolC,res), polyres(g,kpolC,res)] >;
      require Dimension(gv) le 0 :
             "\nBad affine curve (the special fibre has a component at infinity)";
      for pt in RadicalDecomposition(gv) do
        require is_regular_at_point([g], 1, pt, P : res:=res) :
               "\nBad affine curve (there are nonregular points at infinity on the special fibre)";
      end for;
    end for;

    patches_needed := [1];
    patch := rec< patch_record | >; 
    patch`index := <1,1>;
    patch`parent := <0,1>; // TO DO: actually have a patch <0,1>
    patch`F := Evaluate(eqnC, [x,y]);
    patch`U := z;
    patch`is_FU := true;
    patch`eqns := [patch`F, pi - patch`U];
    patch`eqns_k := polyres(patch`eqns, kpol, res);
    patch`ideal_k := ideal< kpol | patch`eqns_k >;
    patch`map := [C.1, C.2]; 
  //patch`map_inv := // never needed? 
    patch`domain := < [IdlU|], [IdlU|], [ideal<kpol|0>] >; // domain = whole ambient
    model`patches[<1,1>] := patch;

  elif dim eq 2 and IsProjective(AC) then

    // Here, for 1<=i<=3, patch i is the affine patch where C.i = 1
    // By preference we use patch 3, then patch 2, then patch 1
    // (This ordering is assumed throughout this elif clause!)
    assert #Gradings(AC) eq 1;
    ww := Gradings(AC)[1]; 
    if ww ne [1,1,1] then 
      assert #{w: w in ww | w ne 1} eq 1;
      w, wi := Max(ww);
      pt := [0,0,0]; pt[wi] := 1;
      error if Evaluate(Equation(C), pt) eq 0, 
           "Curve contains the singular point of its (weighted projective) ambient space";
      error if R!Evaluate(Equation(C), pt) in P,
           "Reduction of the given curve contains the singular point of its (weighted projective) ambient space";
      patches_needed := [i : i in [3,2,1] | i ne wi];
    else
      if Evaluate(eqnC,[1,0,0]) notin P then
        patches_needed := [3,2];
      elif Evaluate(eqnC,[0,1,0]) notin P then
        patches_needed := [3,1];
      elif Evaluate(eqnC,[0,0,1]) notin P then
        patches_needed := [2,1];
      else 
        patches_needed := [3,2,1];
      end if;
    end if;
    vprintf RegularModel: "Choosing patches %o of the given model.\n", patches_needed;

    X,Y,Z := Explode([AC.1,AC.2,AC.3]);
    wX,wY,wZ := Explode(ww);
    for i in patches_needed do 
      // Here x,y are used as the affine variables on each patch
      // (there's no canonical way to do this, so take care!)
      if i eq 1 then
        assert wX eq 1; subi := [1,x,y]; mapi := [Y/X^wY, Z/X^wZ, pi];
      elif i eq 2 then
        assert wY eq 1; subi := [x,1,y]; mapi := [X/Y^wX, Z/Y^wZ, pi];
      elif i eq 3 then
        assert wZ eq 1; subi := [x,y,1]; mapi := [X/Z^wX, Y/Z^wY, pi];
      end if;
      eqni := Evaluate(eqnC, subi);

      // The ideal Di defines the closed subset of the special fibre 
      // not visible on previous patches; must match use of x,y above
      if i eq patches_needed[1] then
        Di := ideal<kpol| 0 >;
      elif i eq 2 then
        Di := ideal<kpol| yy >; // locus y=0 on patch 2
      elif i eq 1 then
        if patches_needed eq [3,1] then
          Di := ideal<kpol| yy >;
        elif patches_needed eq [2,1] then
          Di := ideal<kpol| xx >;
        elif patches_needed eq [3,2,1] then
          Di := ideal<kpol| xx, yy >;
        end if;
      end if;

      patch := rec< patch_record | >; 
      patch`index := <1,i>;
      patch`parent := <0,1>; // TO DO: actually make a patch <0,1>
      patch`F := eqni;
      patch`U := z;
      patch`is_FU := true;
      patch`eqns := [patch`F, pi - patch`U];
      patch`eqns_k := polyres(patch`eqns, kpol, res);
      patch`ideal_k := ideal< kpol | patch`eqns_k >;
      patch`map := subi;
      patch`map_inv := mapi;
      patch`domain := < [IdlU|], [IdlU|], [Di] >;
      model`patches[<1,i>] := patch;
    end for; // i in patches_needed

  end if; // affine, projective, non-plane 

  // Compute components of special fibre
  for i in patches_needed do 
    // find fibs that appear on ith patch but not on previous patches
    // TO DO: could make decomposition easier by first breaking it up by factors of U
    patchi := model`patches[<1,i>];
    special := patchi`ideal_k;
    if i eq patches_needed[1] then 
      assert Dimension(special) le 1;      
      fibs, fibs_red := PrimaryDecomposition(special);
      assert forall{I : I in fibs_red | Dimension(I) eq 1};
      special_fibs := [* <i, fibs_red[f], fibs[f]> : f in [1..#fibs] *];
    else
      subscheme := patchi`domain[3][1] + special;
      assert Dimension(subscheme) le 1;
      if Dimension(subscheme) le 0 then
        continue i;
      end if;
      fibs_red := RadicalDecomposition(subscheme);
      special_fibs cat:= [* <i, I> : I in fibs_red | Dimension(I) eq 1 *];
    end if;
  end for; // i

  // Deal with the special fibres:
  // get equations on other patches, find intersections, check regularity, create records...

  nonreg_pts := [];
  intn_pts := [];
  for tup in special_fibs do
    i, fib := Explode(tup);
    patchi := model`patches[<1,i>];
    fib_on_patch := rec< fibre_on_patch_record | patch_index := <1,i>, ideal := fib >;
    fibab := blank_abstract_fibre_record();
    fibab`patch1 := <1,i>;
    fibab`explicit[<1,i>] := fib_on_patch;
    // find fibre on the patches that have not yet been considered (if it is visible there)
    for j in [j: j in patches_needed | j lt i] do
      patchj := model`patches[<1,j>];
      // substitution introduces denominators, only involving vars[i]
      // (but we don't care about fibres contained in vars[i] = 0 on the jth patch)
      fibsubst := ideal< kpol | change_variables_between_P2_patches_i_to_j(Basis(fib), i, j, ww) >;
      fibsj := [ff : ff in RadicalDecomposition(fibsubst) | 1 notin patchj`domain[3][1] + ff];
      assert #fibsj le 1; // = transform of fib, if it appears on this patch
      if #fibsj ne 0 then
        fibj := fibsj[1];
assert ideal_meets_domain(fibj, patchj`domain); // already checked in defn of fibsj
        fibab`explicit[<1,j>] := rec< fibre_on_patch_record |
                                      patch_index := <1,j>, ideal := fibj >;
      end if;
    end for; // j

    // collect intersections with other fibres
    for fibab1 in model`abstract_fibres do
      for j in patches_needed do
        if IsDefined(fibab`explicit, <1,j>) and IsDefined(fibab1`explicit, <1,j>) then
          // get intersections not appearing on previous patches
          patchj := model`patches[<1,j>];
          intn := patchj`domain[3][1] + fibab`explicit[<1,j>]`ideal + fibab1`explicit[<1,j>]`ideal;
          assert Dimension(intn) le 0;
          intn_pts cat:= [<j,I> : I in RadicalDecomposition(intn)];
        end if;
      end for;
    end for;

    // Test regularity along this fibre:
    // we check it on patch i (the first patch where it is visible), 
    // and then on the other patches where it is visible.
    // TO DO: could just check patch i, then check the missing points
    vprintf RegularModel, 3: "check_regularity_on_fib, i = %o : ", i; 
    vtime RegularModel, 3:
    bool, nonreg_ptsi := check_regularity_on_fib(model, patchi, fib);
    if assigned fibab`is_regular then
assert false; // can it be assigned?
      assert fibab`is_regular eq bool;
    else
       fibab`is_regular := bool;
    end if;
    if fibab`is_regular then
      nonreg_pts cat:= [<i,pt> : pt in nonreg_ptsi];
    end if;
    for j in [j: j in patches_needed | j lt i and <1,j> in Keys(fibab`explicit)] do
      patchj := model`patches[<1,j>];
      vprintf RegularModel, 3: "check_regularity_on_fib, j = %o : ", j; 
      vtime RegularModel, 3:
      bool, nonreg_ptsj := check_regularity_on_fib(model, patchj, fibab);
      assert bool eq fibab`is_regular;
      if bool then
        for pt in nonreg_ptsj do
          if 1 notin patchj`domain[3][1] + pt then
            // pt was not seen on previous patches
            Append(~nonreg_pts, <j,pt>);
          end if;
        end for;
      end if;
    end for; // j

    Append(~model`abstract_fibres, fibab);
  end for; // tup

  // Make records for the nonreg points and intersection points, 
  // checking for repeated points.
  // (DON'T map each point across to the other patches of the blowup,
  // although this is not actually necessary, as long as we observe
  // the convention above of listing each point on the first patch
  // on which it appears, and not duplicating it on other patches.)
  bad_pts := Sort(Setseq({<tup[1],tup[2],false> : tup in nonreg_pts})) cat
             Sort(Setseq({<tup[1],tup[2],true> : tup in intn_pts | tup notin nonreg_pts}));
  for tup in bad_pts do
    i, idli := Explode(tup); assert i in patches_needed;
    // check if already have this point
    for pt1 in model`points do
      if IsDefined(pt1`explicit, <1,i>) and pt1`explicit[<1,i>]`ideal eq idli then
        continue tup;
      end if;
    end for;
    pt := blank_point_record();
    pt`patch := <1,i>;
    pt`is_regular := tup[3];
    /* NO NEED TO
    // find point on all patches_needed where it appears
    for j in patches_needed do
    */
    for j in [i] do
      if j eq i then
        idlj := idli;
      else
        idlj := ideal< kpol | change_variables_between_P2_patches_i_to_j(Basis(idli), i, j, ww) >;
        assert Dimension(idlj) le 0;
        if Dimension(idlj) le -1 then // does not appear on jth patch
          continue j;
        end if;
        assert IsPrime(idlj);
      end if;
      coordsj := pt_coords_from_ideal(idlj);
      pt`explicit[<1,j>] := rec< point_on_patch_record | patch_index := <1,j>,
                                                         coords := coordsj,
                                                         ideal  := idlj >;
      pt`field := Universe(coordsj);
    end for;
    // which fibres is pt contained in? (some redundant checking, for sake of simplicity)
    pt`fibres := {};
    for j := 1 to #model`abstract_fibres do
      fibj := model`abstract_fibres[j]`explicit;
      if IsDefined(fibj, pt`patch) then  // (only defined for relevant fibres)
        if fibj[pt`patch]`ideal subset pt`explicit[pt`patch]`ideal then
          pt`fibres join:= {j};
        end if;
      end if;
    end for;
    assert not pt`is_regular or #pt`fibres ge 2; // listed points are either nonreg or intersections
    Append(~model`points, pt);
  end for; // tup in bad_pts

  // MAIN LOOP : BLOW UP NONREGULARITIES

  while true do
    nonreg_fibs := [];
    for i := 1 to #model`abstract_fibres do
      fib := model`abstract_fibres[i];
      if not fib`is_regular and not assigned fib`blownup then
        Append(~nonreg_fibs, i);
      end if;
    end for;
    nonreg_pts := [];
    for i := 1 to #model`points do
      pt := model`points[i];
      if not pt`is_regular and not assigned pt`blownup and
        forall {j : j in pt`fibres | model`abstract_fibres[j]`is_regular}
      then
        Append(~nonreg_pts, i);
      end if;
    end for;

    if IsEmpty(nonreg_fibs) and IsEmpty(nonreg_pts) then 
      break;
    end if;

    num_fibs := #model`abstract_fibres;
    vprintf RegularModel : 
           "Current model has %o fibre%o (%o nonregular fibre%o), "*
           "and %o isolated nonregular point%o\n", 
            #model`abstract_fibres, plural(#model`abstract_fibres), 
            #nonreg_fibs, plural(#nonreg_fibs),
            #nonreg_pts, plural(#nonreg_pts);

    // Recurse to a base extension to separate non-rational points
    deg := LCM([Integers()| Degree(model`points[i]`field, k) : i in nonreg_pts]);
    if deg gt 1 then
      require not ISA(Type(K), FldFunG) : "Not implemented for extensions of function fields";
      polk := DefiningPolynomial(ext<k|deg>); assert Degree(polk) eq deg;
      KK := global_extension(K, polk, P, res : special, tries:=1000);
      if Warnings then "WARNING: Extending the base field to", KK; end if;
      CKK := BaseChange(C, KK);
      // work-around: BaseChange renormalises the equation(s)
      AKK := Ambient(CKK);
      CKK := Curve(AKK, DefiningEquations(C));
      return RegularModel(CKK, Integers(KK)!pi);
    end if;

    error if #nonreg_fibs gt 0 and ISA(Type(K), FldAlg),
         "Fibre blowups over number fields not yet implemented"; 
    // TO DO: only need to fix 'contained_in_prime_locally', and lift_ideal, and ???

    // Do linear blowups first; do fibres before points (TO DO!!)
    // (must pass indices around instead of records themselves, 
    // since not allowed to modify a record via a different identifier)
    if exists(i) {i : i in nonreg_pts | model`points[i]`field eq k} then
      // point defined over k
      blow_up_point(model, i);
    elif not IsEmpty(nonreg_fibs) then 
      blow_up_line(model, nonreg_fibs[1]);
    else
      blow_up_point(model, nonreg_pts[1]);
    end if;
    
    vprint RegularModel, 2:
          "After blowup, model has patches indexed by", Sort(Setseq(Keys(model`patches)));

    if debug then
      vprintf RegularModel, 3: "Sanity checks: "; 
      vtime RegularModel, 3:
      check_model(model); // do some cross-checking
    end if;

  end while;

  assert #nonreg_fibs eq 0 and #nonreg_pts eq 0;
  assert not assigned model`is_regular and not assigned model`regular_fibres_indices; 
  model`is_regular := true;

  model`original_is_regular := {tup[1] : tup in Keys(model`patches)} eq {1}; // no blowups were done
  if model`original_is_regular then
    vprint RegularModel: "The given curve is a regular model.";
  end if;
  num_reg_fibs := #[fib : fib in model`abstract_fibres | fib`is_regular];
  if num_reg_fibs gt 1 then
    vprintf RegularModel: "Special fibre of regular model has %o components\n", num_reg_fibs;
  end if;

  // TO DO: genera of components

  // Sanity checks: intersection matrix should be integral with correct rank
  if debug then
    vprintf RegularModel: 
      "Special fibre has %o geometric components\n", number_of_geometric_components(model);
    
    if splitting_degree(model) eq 1 then
      mat := IntersectionMatrix(model);
      vprintf RegularModel: "Intersection matrix of special fibre components:\n%o\n", mat;

      CG := ComponentGroup(model);
      vprintf RegularModel : "Component group of the jacobian is %o\n", grpab_to_string(CG);
    end if;
  end if;

  if not assigned C`RegularModels then
     C`RegularModels := AssociativeArray();
  end if;
  key := fldfunrat select pi else P;
  C`RegularModels[key] := model;

  return model;
end intrinsic;

