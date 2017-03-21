freeze;

/******************************************************************************

   Regular models of arithmetic surfaces -- user interface and applications

   Steve Donnelly, July 2009

******************************************************************************/

import "main.m" : multiplicity_of_point, 
                  multiplicity_of_component1,
                  _point_in_domain, 
                  fibre_meets_domain_with_dim_1;

import "regularity.m": is_regular_at_point,
                       global_extension;

debug := true;

please_report := 
  "\n\nPlease send this example to magma-bugs@maths.usyd.edu.au"
 *"\n\nHINT: to generate a file containing all input from this magma session, "
 *"enter the following two lines:"
 *"\n    SetOutputFile(\"__file_name__\"); \n    %P \n";


/******************************************************************************
  Components and Intersection Data
******************************************************************************/

function multiplicity(i, model)
  fib := model`abstract_fibres[i];
  if assigned fib`multiplicity then
    return fib`multiplicity;
  else
    idx := fib`patch1;
    patch_idl := model`patches[idx]`ideal_k;
    fib_idl := fib`explicit[idx]`ideal;
    m := multiplicity_of_component1(patch_idl, fib_idl);
    model`abstract_fibres[i]`multiplicity := m;
    return m;
  end if;
end function;

function regular_fibres_indices(model)
  if not assigned model`regular_fibres_indices then
    if assigned model`special_points_count then
      delete model`special_points_count; 
      // because this in the same order as the regular fibres, 
      // but the order will now change (TO DO: permute it!)
    end if;

    // Sort the components into a nice order, which remains fixed hereafter
    // (in order of multiplicity, but otherwise in the order they were found)
    inds := [i: i in [1..#allfibres] | allfibres[i]`is_regular]
                          where allfibres is model`abstract_fibres;
    mults := [multiplicity(i,model) : i in inds];
    model`regular_fibres_indices := 
          &cat [[i: i in inds | multiplicity(i,model) eq m] : m in [1..Max(mults)]];
    if #inds gt 1 then
      vprintf RegularModel: "Special fibre components have multiplicities: %o\n", 
                            [model`abstract_fibres[i]`multiplicity : i in model`regular_fibres_indices];
    end if;
  end if;
  return model`regular_fibres_indices;
end function;

intrinsic Multiplicities(model::CrvRegModel) -> SeqEnum
{Multiplicities of the components of the special fibre of the given regular model}

  inds := regular_fibres_indices(model); // this sorts model`abstract_fibres
  return [model`abstract_fibres[i]`multiplicity : i in inds];
end intrinsic;

intrinsic Components(model::CrvRegModel) -> List
{The components of the special fibre of the given regular model.
(An explicit equation for *some* affine patch of each component is provided.)}

  inds := regular_fibres_indices(model); // this sorts model`abstract_fibres
  fibres := [model`abstract_fibres[i] : i in inds];
  return [* fib`explicit[fib`patch1]`ideal : fib in fibres *];
end intrinsic;


// Geometric components of special fibres

function splitting_field(I)
  assert IsPrime(I) and Dimension(I) eq 1;
  C := Curve(AffineSpace(Generic(I)), I);
  FF := AlgorithmicFunctionField(FunctionField(C));
  return ExactConstantField(FF);
end function;

function splitting(I, F)
  PolF := PolynomialRing(F, Rank(Generic(I)));
  IF := ideal< PolF | [PolF!b : b in Basis(I)] >;
  decomp := PrimaryDecomposition(IF);
  return decomp;
end function;

function geo_splitting_field(fib)
  if not assigned fib`geo_splitting_field then
    I := fib`explicit[fib`patch1]`ideal;
    fib`geo_splitting_field := splitting_field(I);
  end if;
  return fib`geo_splitting_field;
end function;

function geometric_components(fib)
  F := geo_splitting_field(fib);
  fib1 := fib`explicit[fib`patch1];
  if not assigned fib1`geo_components then
    fib1`geo_components := splitting(fib1`ideal, F);
  end if;
  return fib1`geo_components;
end function;

function splitting_degrees(model)
  return [ Degree(geo_splitting_field(fib), model`k) 
         : fib in model`abstract_fibres | fib`is_regular ];
end function;

function splitting_degree(model)
  return LCM(splitting_degrees(model));
end function;

function number_of_geometric_components(model)
  return &+ splitting_degrees(model);
end function;


// Lazy base change!

function model_over_global_extension(model, e)
  K := model`K;
  error if ISA(Type(K), FldFunG), "Not implemented for extensions of function fields";
  polk := DefiningPolynomial(ext< model`k | e >);
  KK := global_extension(K, polk, model`P, model`res : special, tries:=1000);
  CKK := BaseChange(model`C, KK);
  return RegularModel(CKK, Integers(KK)! model`pi);
end function;

function model_with_split_components(model)
  e := splitting_degree(model);
  if e eq 1 then
    return model;
  else
    if not assigned model`model_with_split_components then
      vprint RegularModel : "Recomputing regular model over extension of degree", e;
      IndentPush();
      model`model_with_split_components := model_over_global_extension(model, e);
      IndentPop();
    end if;
    return model`model_with_split_components;
  end if;
end function;


intrinsic IntersectionMatrix(model::CrvRegModel) -> Mtrx
{Intersection pairings between components of the special fibre of the given regular model}

  if assigned model`intersection_matrix then
    return model`intersection_matrix;
  end if;

  // If components are not geometrically irreducible, recompute model over splitting field
  // TO DO: for each fibre, work out numbers of intersections between geo components 
  //       (in general, requires dragging geo components between patches)
if false and splitting_degree(model) ne 1 then
    return IntersectionMatrix(model_with_split_components(model));
  end if;

  inds   := regular_fibres_indices(model); // this sorts model`abstract_fibres
  fibres := [model`abstract_fibres[i] : i in inds];
  mults  := [fib`multiplicity : fib in fibres];

  mat := ZeroMatrix(Integers(), #fibres, #fibres);

  for i in [1..#fibres], j in [1..i-1] do
    intn_pts := [pt : pt in model`points | pt`is_regular and 
                                           pt`fibres subset inds and 
                                           {inds[i],inds[j]} subset pt`fibres];
    // Note: the (hacky) second condition is needed because an intersection point
    // may (confusingly) have pt`is_regular = true, even if the point is contained 
    // in a nonregular fibre (and is therefore not part of the regular model).
    m := 0;
    for pt in intn_pts do
      idx := pt`patch;
      intn := fibres[i]`explicit[idx]`ideal + fibres[j]`explicit[idx]`ideal;
      m +:= multiplicity_of_point(intn, pt`explicit[idx]);
    end for;
    mat[i,j] := m;
    mat[j,i] := m;
  end for;
  for i := 1 to #fibres do 
    sum := &+ [mat[i,j] * mults[j] : j in [1..#fibres]];
    bool, m := IsCoercible(Integers(), -sum/mults[i]);
    require bool : "Self-intersection numbers are not integral" * please_report;
    mat[i,i] := m;
  end for;

  // Sanity checks
  // Formula for arithmetic genus: the sum is over components F of the special fibre
  // g(curve) = g(special fibre) = 1 + Sum_F (g(F) [g(F) - 1 - F^2/2]
  // TO DO: to make this check correct, need to calculate arithmetic genus of each fibre,
  // in the form it actually has in our regular model (or else calculate loops in the graph?)
//  arithg := [];
  for f in fibres do
    assert exists(idx){idx: idx in Keys(f`explicit)};
 //   fideal := f`explicit[idx]`ideal;
  //  F := Curve(AffineSpace(Generic(fideal)), fideal);
  //Append(~arithg, ArithmeticGenus(F));
  //  Append(~arithg, Genus(F));
  end for;
//  okay := ArithmeticGenus(model`C) eq 
//          1 + &+ [mults[i]*(arithg[i]-1-mat[i,i]/2) : i in [1..#fibres]];
//error if not okay, "An error has been detected" * please_report;
  
  model`intersection_matrix := mat;
  return mat;
end intrinsic;

intrinsic ComponentGroup(model::CrvRegModel) -> GrpAb
{The component group of the Jacobian of the curve, returned as an abstract abelian group}

  geo_model := model_with_split_components(model);

  mat := IntersectionMatrix(geo_model);
  mults := Multiplicities(geo_model);
  assert Nrows(mat) eq #mults;
 
  f := #mults;
  A := FreeAbelianGroup(#mults);
  Z := FreeAbelianGroup(1);
  B := Kernel(hom< A->Z | [m*Z.1 : m in mults] >);
  C := quo< B | [B| &+[mat[i,j]*A.i : i in [1..f]] : j in [1..f]] >;

  assert IsFinite(C);
  return C;
end intrinsic;

/******************************************************************************
  Functions for use in L-series code
******************************************************************************/

// Let the 'count' of a point be the number of times the point appears 
// in the union of the affine curves returned by Components.  
// This function returns a sequence containing a tuple
//   < degree, count >  
// for each point where the count is not 1.

function special_points_count(model)
  if not assigned model`special_points_count then
    model`special_points_count := [];

    allfibres := model`abstract_fibres;
    inds := [i : i in [1..#allfibres] | allfibres[i]`is_regular];
    fibres := [allfibres[i] : i in inds];
    p1_inds := [fib`patch1 : fib in allfibres];

    // Intersection points (points possibly contained in more than one component)
    // Note: second condition for same reason as in IntersectionMatrix
    intn_pts := [pt : pt in model`points | pt`is_regular and pt`fibres subset inds];

    // pt is counted on (the affine patch of) the component for fib 
    //   <==> pt`patch = fib`patch1
    for pt in intn_pts do 
      idx := pt`patch;
//printf "%o, %o\n", pt`fibres, [i : i in pt`fibres | p1_inds[i] eq idx];
      count := #[i : i in pt`fibres | p1_inds[i] eq idx];
      Append(~model`special_points_count, <Degree(pt`field,model`k), count> );
    end for;
//"intn_points_count is   ", model`special_points_count;

    // Consider each pt in the locus at infinity of each component: 
    // if pt was already considered as an intn_pt, do nothing;
    // otherwise count = 1.
    for fib_idx in inds do
      fib := allfibres[fib_idx];
      fib_intn_pts := [pt : pt in intn_pts | fib_idx in pt`fibres];
      for p in [p: p in Keys(fib`explicit) | p ne fib`patch1] do 
        // get intersection of fib with domain of patch p 
        // as a disjoint union of 0-dimensional ideals
        dom := model`patches[p]`domain;
        fibp := [fib`explicit[p]`ideal + D : D in dom[3]];
        pts := &cat [RadicalDecomposition(I) : I in fibp];
        pts := [I : I in pts | forall{D: D in dom[1] | not D subset I}];
        if debug then
          assert forall{I: I in pts | Dimension(I) eq 0};
        end if;
        for I in pts do 
          for pt0 in fib_intn_pts do 
            if pt0`patch eq p and pt0`explicit[p]`ideal eq I then
              continue I;
            end if;
          end for;
          degI := Degree(Scheme(AffineSpace(Generic(I)), I));
          Append(~model`special_points_count, <degI, 0>);
        end for; // I
      end for; // p
    end for;      

//"special_points_count is", model`special_points_count;
  end if;
  return model`special_points_count;
end function;

function number_of_points_on_special_fibre(model, degree)

  F := ext< model`k | degree >;
  p := Characteristic(F);
  n := Ilog(p, #F);

  // Count points on each fibre's affine patch1 
  // Note: #RationalPoints code is garbage !!!

  // avoid regular_model_indices (which sorts by computing Multiplicities)
  fibres := [fib : fib in model`abstract_fibres | fib`is_regular];
  ideals := [* fib`explicit[fib`patch1]`ideal : fib in fibres *];
  comps := [* Scheme(AffineSpace(Generic(I)), I) : I in ideals *];
  affine := [ #RationalPoints(C, F) : C in comps ];
  num := &+ affine;
  vprint RegularModel, 2 : "Affine counts:", affine;

  // Adjust for intersection points appearing on more than 1 fibre, 
  // and for points at infinity not appearing

  for tup in special_points_count(model) do
    if degree mod tup[1] eq 0 then
      num +:= tup[1] * (1 - tup[2]); // has been counted tup[2] times
    end if;
  end for;

  // Adjust for blownup points (currently counted once for each fibre they lie on)
  // TO DO: is this correct?  
  // (alternative: only adjust for blownup points lying in patch1 of fibres,
  //  and above only consider points at infinity that are regular)
//"Adjust nonregular:";
  reg_fib_inds := [i : i in [1..#allfibres] | allfibres[i]`is_regular]
                                 where allfibres is model`abstract_fibres;
  for pt in model`points do 
    if not pt`is_regular then
      pt_meets := [i : i in pt`fibres | i in reg_fib_inds];
      num -:= #pt_meets;
//"pt meets", pt_meets;
    end if; 
  end for; 

  return num;
end function;


/******************************************************************************
  Lifting a global point to a regular point on the model
******************************************************************************/

function _FieldOfFractions(R)
  F := FieldOfFractions(R);
  if ISA(Type(F), FldOrd) then
    F := NumberField(F);
  end if;
  return F;
end function;

// work-around: residue maps over rationals don't accept (coprime) denominators
function myres(x, res)
  k := Codomain(res);
  if Type(x) eq FldRatElt then
    return k! (res(Numerator(x)) / res(Denominator(x)));
  end if;
  return res(x);
end function;

// Evaluate f(pt) using the map m for coercion
function _Evaluate(f, pt, m)
  try 
    // succeeds if coercion exists for coefficients of f
    // TO DO: is there no general test like HasCoercion(Str1, Str2) ??
    v := Evaluate(f, pt);
  catch ERR
    if ISA(Type(f), FldFunRatMElt) then
      return _Evaluate(Numerator(f), pt, m) / _Evaluate(Denominator(f), pt, m);
    end if;
    Pol1 := Parent(f);
    Pol2 := PolynomialRing(Universe(pt), Rank(Pol1));
    C1, M1 := CoefficientsAndMonomials(f);
    C2 := [c@m : c in C1];
    M2 := [Monomial(Pol2, Exponents(mm)) : mm in M1];
  //f2 := Polynomial(C2, M2); // fails for locals ("not a monomial" error)
    f2 := &+ [C2[i]*M2[i] : i in [1..#M2]];
    v := Evaluate(f2, pt);
  end try;
  return v;
end function;

// return a residue map from L, extending the given map res from K

function extend_res(res, K, L, PL, _L)
  // construct any residue map from L
  if IsExact(L) then
    l, resL := ResidueClassField(PL);
  else
    l, resL := ResidueClassField(Integers(L));
  end if;
  k := Codomain(res);
  Embed(k, l);

  // adjust by automorphisms of the image, so that the restriction to K equals res
  if IsPrimeField(k) then 
    return resL;
  else
    g := PrimitiveElement(k) @@ res;
    gl1 := l!res(g);
    gl := resL(g@_L);
    if gl eq gl1 then
      return resL;
    else
      _, auts := AutomorphismGroup(l, PrimeField(l));
      assert exists(a){a: a in auts | a(gl) eq gl1};
      return resL * a;
    end if;
  end if;
end function;

// point_in_domain is a clone of _point_in_domain in main.m
// Here pt is given by coords in a residue field that extends model`k

function point_in_closed_subscheme(pt, I)
  return forall{eqn: eqn in Generators(I) | Evaluate(eqn,pt) eq 0};
end function;

function point_in_domain(pt, patch : include_blownup:=false)
  if exists{J : J in patch`domain[1] | point_in_closed_subscheme(pt,J)} then
    return false;
  elif not include_blownup and 
       exists{J : J in patch`domain[2] | point_in_closed_subscheme(pt,J)} then
    return false;
  else 
    return exists{J : J in patch`domain[3] | point_in_closed_subscheme(pt,J)};
  end if;
end function;

point_on_model_record := recformat< 
  patch_index       : Tup,
  patch_eqn         : SeqEnum,
  point_coords      : SeqEnum,
  point_reduction   : SeqEnum,
  component_indices : SeqEnum,
  component_eqns    : List
>;

intrinsic PointOnRegularModel(model::CrvRegModel, pt::Pt) -> SeqEnum, SeqEnum, Tup
{Given a regular model of a curve, and a point on the curve, this finds 
the corresponding point on the regular model.  Returns three things: 
the coordinates of the point on some patch of the model, equations
for that patch, and the index that identifies the patch within the model}

  C := model`C;
  K := model`K;
  P := model`P;
  k := model`k;
  res := model`res;

  R := Ring(Parent(pt));
  require Scheme(pt) eq C : 
         "The first argument should be a regular model of a curve, "*
         "the second argument should be a point on the same curve"; 

  // Want this to work for any reasonable extension L of K (local or global)
  L := _FieldOfFractions(R);
  _L := RingMap(Parent(pt)) * Coercion(R,L);
  pi := model`pi @_L;
  if IsExact(L) then
    PL := ideal< Integers(L) | {x@_L : x in Generators(P)} >;
    factPL := Factorization(PL);
    require #factPL eq 1 : 
      "When the given point is over an extension field, the prime must extend uniquely";
    PL := factPL[1][1];
    _Valuation := func< x | Valuation(x, PL) >;
  else 
    PL := 0; // dummy
    _Valuation := func< x | Valuation(x) >;
  end if;
  // find an extension resL of res to L (if L eq K, resL is res)
  if not exists(resL){x[2] : x in model`extended_res | x[1] cmpeq L} then
    resL := extend_res(res, K, L, PL, _L);
    Append(~model`extended_res, [*L, resL*]);
  end if;
  l := Codomain(resL);

  // get pt as sequence of coords on one of the initial patches
  ptC := pt; // for debugging
  pt := ChangeUniverse(Eltseq(pt), L);
  assert Dimension(Ambient(C)) eq 2;
  if IsAffine(C) then
    require forall{c : c in pt | _Valuation(c) ge 0}:
           "The given point should have locally integral coordinates";
    idx := <1,1>;
    patch := model`patches[idx];
    pt cat:= [pi]; // patch`eqns are f = 0, z = pi
  elif IsProjective(C) then

// why did I need to do it by hand instead of using the map_inv ?
if true then
    // this assumes the patch domains were set in order of preference 3,2,1
    for i in [3,2,1] do
      idx := <1,i>;
      if idx in Keys(model`patches) then
        patch := model`patches[idx];
        assert assigned patch`map_inv; // isn't it?
        assert #pt eq #patch`map;
        if exists{j : j in [1..#pt] | patch`map[j] eq 1 and IsWeaklyZero(pt[j])} then
          continue; // not on this patch, and evaluating map_inv would get 0/0
        end if;
        pti := [_Evaluate(f, pt, _L) : f in patch`map_inv];
        if forall{c : c in pti | _Valuation(c) ge 0} then
          pt := pti; // pt lives on this patch
          break;
        end if;
      end if;
      error if i eq 1, "Failed to reach the first level (this is a bug)";
    end for;
else
    // first scale so the projective point makes sense mod PL
    // (after scaling, some weight 1 coord should be a unit)
    w := Gradings(Ambient(C))[1]; // there is only 1 grading
    mv := Min([_Valuation(pt[i]) : i in [1..#pt] | w[i] eq 1]); 
    if mv lt 0 then
      piL := _Valuation(pi) eq 1 select pi else UniformizingElement(L); 
      pt := [L| pt[i] * piL^(-mv*w[i]) : i in [1..#pt]];
      assert forall{c : c in pt | _Valuation(c) ge 0};
    end if;
    keys := Keys(model`patches);
    assert forall{i: i in [1,2,3] | w[i] eq 1 or <1,i> notin keys};
    // this assumes the patch domains were set in order of preference 3,2,1
    i := Max([i : i in [1,2,3] | <1,i> in keys and myres(pt[i],resL) ne 0]);
    pt := [pt[j]/pt[i]^w[j] : j in [1..3] | j ne i];
    pt cat:= [pi]; // patch`eqns are f = 0, z = pi
    idx := <1,i>;
    patch := model`patches[idx];
end if;

  else
    // TO DO: will need another case for nonplane curves (?)
  end if;

  // Recursively lift point to blowup patches, until point is regular.
  // The process is uniquely determined: at each step (nth blowup),
  // if preimage is not regular, go to chosen patch of that nonregular
  // point or fibre; if regular, choose patch <n,i> for smallest i
  // such that preimage point is in domain of patch, and terminate.

  respt := [myres(c,resL) : c in pt];
  reg_fib_inds := [i : i in [1..#allfibres] | allfibres[i]`is_regular]
                                 where allfibres is model`abstract_fibres;
  while true do
    assert forall{eqn: eqn in patch`eqns | IsWeaklyZero(_Evaluate(eqn,pt,_L))};
    if point_in_domain(respt, patch) then
      // in particular, it's regular on this patch
      respt := [l| myres(c,resL) : c in pt];
if false and debug then // TO DO!!!
        Lpol := PolynomialRing(Integers(L), #pt);
        eqns := ChangeUniverse(patch`eqns, Lpol);
        assert is_regular_at_point(eqns, 1, pt, PL : res:=resL);
      end if;
      // figure out which components of the special fibre pt lies on
      fib_inds := [Integers()| ];
      fib_eqns := [* *];
      for i in reg_fib_inds do 
        F := model`abstract_fibres[i];
        if idx in Keys(F`explicit) then
          Fideal := F`explicit[idx]`ideal;
          if point_in_closed_subscheme(respt, Fideal) then
            Append(~fib_inds, i);
            Append(~fib_eqns, Generators(Fideal));
          end if;
        end if;
      end for;
      return rec< point_on_model_record | 
                  patch_index        := idx,
                  patch_eqn          := patch`eqns,
                  point_coords       := pt,
                  point_reduction    := respt,
                  component_indices  := fib_inds,
                  component_eqns     := fib_eqns >;
    else
      // pt is not regular; find the nonregular point or fibre containing pt
      n := -1;
      for ptrec in model`points do
        if ptrec`patch eq idx and not ptrec`is_regular
           and point_in_closed_subscheme(respt, ptrec`explicit[idx]`ideal)
        then
          n := ptrec`blownup;
          break;
        end if;
      end for;
      if n eq -1 then // check fibres
        for fibrec in model`abstract_fibres do
          if IsDefined(fibrec`explicit, idx) and not fibrec`is_regular 
             and point_in_closed_subscheme(respt, fibrec`explicit[idx]`ideal)
          then
            assert exists(n){tup[2]: tup in fibrec`blownup | tup[1] eq idx};
            break;
          end if;
        end for;
      end if;
      error if n eq -1, "Failed to locate non-regular point (this is a bug!)";

      lifted := false;
      keys := Sort([k : k in Keys(model`patches) | k[1] eq n]);
      for idxi in keys do 
        patchi := model`patches[idxi];
        denoms := [_Evaluate(Denominator(f), pt, _L) : f in patchi`map_inv];
        if forall{d : d in denoms | not IsWeaklyZero(d)} then
          pti := [L| _Evaluate(f, pt, _L) : f in patchi`map_inv]; 
          if forall{c : c in pti | _Valuation(c) ge 0} then
            respti := [myres(c,resL) : c in pti];
            if point_in_domain(respti, patchi : include_blownup) then
              idx := idxi;
              patch := patchi;
              pt := pti;
              respt := respti;
              lifted := true;
              break idxi;
            end if;
          end if;
        end if;
      end for; // idxi 
      error if not lifted, "Something is wrong with the patch domains (this is a bug!)";
    end if;
  end while;

end intrinsic;

