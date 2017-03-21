freeze;
///////////////////////////////////////////////////////////////////
//  Main Intrinsics for Construction and Basic Functionality     //
//            of Curve Automorphism Groups.                      //
//                                                               //
//             mch - 07/09/2006                                  //
///////////////////////////////////////////////////////////////////

import "gen_crv_auto_gp.m": gen_seq;

/*
   record for storage of elements in their parent GrpAutCrv
   without using GrpAutCrvElts directly (avoiding circular refs)
*/
grpAutCrvEltRec := recformat<
  index		: RngIntElt,  // index of element in parent aut group
  ff_map	: Map, // field morphism giving corr. FF map
  crv_map	: MapAutSch  // the actual scheme isomorphism
>;

/***********
   attributes of GrpAutCrv:
  Fgens : SeqEnum, //seq of AlFF places for short auto description
  Agens : SeqEnum, //seq of generators (grpAutCrvEltRec)
  id	: grpAutCrvEltRec,     // identity element
  G	: GrpPerm, //perm grp rep
  // data giving the G <-> CG bijection
  Gelts	: SetIndx, // list of all elements of G
  Aelts	: SetIndx, // list of corr. elements of A
  invs	: SeqEnum, // int seq of length #CG giving the inverse
		   // map g -> g^-1 as a permutation of indices
  // other attributes
  //  - store some data for direct translation between AlFF elts
  //  and rational functions on the FF patch. Temporary hack for
  //  speed while there are problems with the internal conversion fns!
  ff_rat : SeqEnum, // seq of coord fn indices <-> AlFF generators
  rat_ff : SeqEnum, // seq of AlFF elts <-> coord fns on FFpatch
  //NB: for ff_rat the sequence of the AlFF generators are in the order
  // for Fgen which is the REVERSE of the order needed for 
  // FunctionFieldEvaluation!
  // new attribute - 08/11 mch: specify whether to try to find minimal
  //  degree polynomials to define the scheme map (and inverse) when
  //  reconstructing from the ff_map. In fact, look for defining polys
  //  of degree up to a given bound d if d > 0 (if none exist, stick with current).
  //  Currently only implemented for C in ordinary projective space.
  eqn_deg_bnd : RngIntElt, // the bound d (>=0) to try up to
  // new attribute - 10/11 mch: specify whether to try to remove (weighted) GCD
  //  of defining polynomials of automorphisms. not used if eqn_deg_bnd exists
  no_gcd : BoolElt
************/

declare attributes GrpAutCrv : Fgens, Agens, id, G, Gelts, Aelts, invs,
				ff_rat, rat_ff, eqn_deg_bnd, no_gcd;

/*********** 
   attributes of GrpAutCrvElt:
  ff_map	: Map, // field morphism giving corr. FF map
  index		: RngIntElt  // index of element in parent aut group
************/

declare attributes GrpAutCrvElt : ff_map, index;


function ValidBaseField(C,bPerf)
// tests whether function field morphisms can be defined over the base
// field of curve C. As Florian's functions for testing this currently 
// give errors, use current (ie at 05/06) possibilities.
// if bPerf is true also tests whether K is perfect.
    K := BaseRing(C);
    while ISA(Type(K),FldFunG) do
	K := BaseField(K);
    end while;
    if bPerf then
      return (K cmpeq Rationals()) or (ISA(Type(K),FldNum) and (Ngens(K) eq 1)) 
			or (ISA(Type(BaseRing(C)),FldFin));
    else
      return (K cmpeq Rationals()) or (ISA(Type(K),FldNum) and (Ngens(K) eq 1)) 
			or (ISA(Type(K),FldFin));
    end if;
end function;

// HACK to avoid internal FF coercions/maps
function FunctionFieldEvaluation(f,elts)

    // f an elt of alg fn fld F = k(x,alpha_1,..alpha_r).
    // elts = [e_0,e_1,..e_r], e_i in some appropriate field
    //  structure, F1.
    //  Returns phi(f) where phi is the field homomorphism
    // F -> F1, given by x |-> e_0, alpha_i |-> e_i
    
    if #elts eq 1 then
	if Type(Parent(f)) eq FldFunRat then
	    return Evaluate(f,elts[1]);
	else // Type(Parent(f)) eq FldFun - sigh!
	    return Evaluate(
		RationalFunctionField(BaseField(BaseField(Parent(f))))!f,elts[1]);
	end if;
    else // elts should be > 1!
	F1 := BaseRing(Parent(f));
	coeffs := [ FunctionFieldEvaluation(c,elts1) : c in expn ]
		where elts1 is Prune(elts) where expn is Eltseq(f);
	return Evaluate(PolynomialRing(Universe(coeffs))!coeffs,elts[#elts]);
    end if;
    
end function;

// HACK to avoid internal FF coercions/maps
function coerce_to_ff(f,seq)
    if Type(f) eq RngMPolElt then
      return Evaluate(f,seq);
    else
      return Evaluate(Numerator(f),seq)/Evaluate(Denominator(f),seq);
    end if;
end function;

//////// Functions to reduce degree of def polys of a map ////////////////

function DenomsOfDegree(f,C,d);
    R := CoordinateRing(Ambient(C));
    mons := Setseq(MonomialsOfWeightedDegree(R,d));
    K := FunctionField(C); F,fmp := AlgorithmicFunctionField(K);
    i := Rank(R)+1-FFPatchIndex(C);
    wts := VariableWeights(R);
    fs := [fmp(K!(R.j/(R.i)^wts[j])) : j in [1..Rank(R)]];
    fpows := [Evaluate(m,fs) :  m in mons];
    fpowsf := [u*v : u in fpows] where v is -fmp(f);
    rels := Relations(fpows cat fpowsf,BaseRing(R));
    N := #fpows;
    B := Basis(rels);
    B := [Eltseq(b)  : b in B | &+[Eltseq(b)[i]*fpows[i] : i in [1..N]] ne F!0];
    return [Polynomial(b[N+1..2*N],mons) : b in B];
    /*rels := Relations(fpowsf cat fpows,BaseRing(R));
    N := #fpows;
    B := Basis(rels);
    B := [Eltseq(b)  : b in B | &+[Eltseq(b)[i]*fpows[i] : i in [1..N]] ne F!0];
    return [Polynomial(b[1..N],mons) : b in B];*/

end function; 

function RatFnNum(f,den,I)
    R := Parent(den);
    assert Generic(I) eq R;
    nf := Numerator(f);
    df := Denominator(f);
    assert Parent(nf) eq R and Parent(df) eq R;
    deg := WeightedDegree(nf);
    assert deg eq WeightedDegree(df);
    assert IsHomogeneous(nf) and IsHomogeneous(df) and IsHomogeneous(den);
    n := WeightedDegree(den);
    rhs := NormalForm(den*nf,I);
    xpows := Setseq(MonomialsOfWeightedDegree(R,n));
    df1 := NormalForm(df,I);
    lhs := [NormalForm(m*df1,I):m in xpows];
    mons := Setseq(Seqset(Monomials(rhs) cat &cat[Monomials(e) : e in lhs]));
    mat := Matrix([[MonomialCoefficient(l,m) : m in mons] : l in lhs]);
    vec := Vector([MonomialCoefficient(rhs,m) : m in mons]);
    soln,ker := Solution(mat,vec);
    return &+[soln[i]*xpows[i] : i in [1..#xpows]];
end function;

function ReduceMapDegree(mp : DegreeBound := 0)
// finds minimal degree defining polys for a scheme map between 2 ordinary proj
// curves. If DegreeBound > 0, then only look for alternative defining polys
// with degree up to that bound.

    C := Domain(mp);
    Saturate(~C);
    I := Ideal(C);
    R := Generic(I);
    eqns := DefiningPolynomials(mp);
    deg := LeadingTotalDegree([e : e in eqns | e ne 0][1]);
    db := (DegreeBound le 0 select deg-1 else DegreeBound);
    db := Min(db,deg-1);
    if db le 0 then return eqns; end if;
    n := #eqns;
    zs := [i : i in [1..n] | eqns[i] eq 0];
    i0 := inds[#inds] where inds is [i : i in [1..n] | i notin zs];
    zs1 := Sort(zs cat [i0]);
    nzs := [i : i in [1..n] | i notin zs1];
    new_eqns := [R!0 : i in [1..n]];
    if #nzs eq 0 then // special case for constant map with only one non-zero entry
	i := 1;
	while R.i in I do i +:= 1; end while;
	new_eqns[i0] := R.i;
	return new_eqns;
    end if;

    F := FunctionField(C);
    fs := [F!(eqns[i]/eqns[i0]) : i in nzs];
    for d in [1..db] do
	dens := [];
	for f in fs do
	  ds := DenomsOfDegree(f,C,d);
	  if #ds eq 0 then break; end if;
	  Append(~dens,ds);
	end for;
	if #dens lt #nzs then continue; end if;
	if #nzs eq 1 then 
	  dens := dens[1];
	else
	  mons := Setseq(MonomialsOfDegree(R,d));
	  V := VectorSpace(BaseRing(R),#mons);
	  Ws := [sub<V | [V![MonomialCoefficient(f,m) : m in mons] : f in ds]> :
			ds in dens];
	  W := &meet Ws;
	  if Dimension(W) eq 0 then continue; end if;
	  dens := [Polynomial(Eltseq(b),mons) : b in Basis(W)];
	end if;
	if BaseRing(R) cmpeq RationalField() then //attempt to minimise
	    dens := [LCM([Denominator(c) : c in Coefficients(d)])*d : d in dens];
	    if #dens gt 1 then
		mons := Setseq(&join([Seqset(Monomials(d)) : d in dens]));
	 	cmat := Matrix([[MonomialCoefficient(d,m) : m in mons] : d in dens]);
		cmat := LLL(cmat);
		dens := Reverse([Polynomial(r,mons) : r in RowSequence(cmat)]);
	    end if;
	end if;
	den := R!0;
	for d in dens do
	  if d notin I then den:=d; break; end if;
	end for;
	if den ne R!0 then
	  new_eqns[i0] := den;
	  for i in nzs do
	    new_eqns[i] := RatFnNum(eqns[i]/eqns[i0],den,I);
	  end for;
	  return new_eqns;
	end if;
    end for;
    return eqns; 
end function;

function remove_GCD(mp)
// remove the weighted GCD of the map eqns
//  - simplified version for genuinely non-trivial weighted codomian ambient
    eqns := DefiningPolynomials(mp);
    wts := VariableWeights(CoordinateRing(Ambient(Codomain(mp))));
    g := GCD(eqns);
    if Degree(g) le 0 then return eqns; end if;
    eqns1 := [];
    for i in [1..#eqns] do
	boo,h := IsDivisibleBy(eqns[i],g^wts[i]);
	if not boo then return eqns; end if;
	Append(~eqns1,h);
    end for;
    return eqns1;
end function;

//////////////////////////////////////////////////////////////////////////////

procedure add_ff_rat_map_data(~CG,Fgens)
// computes the ff_rat and rat_ff sequences for CG

    C := Domain(CG);
    FC := FunctionField(C);
    KC,mpC := AlgorithmicFunctionField(FC);
    Ca := AffinePatch(C1, FFPatchIndex(C1))
	where C1 is (IsProjective(C) select C else ProjectiveClosure(C));

    CG`rat_ff := [mpC(FC.i) : i in [1..Length(Ca)]];
    if Length(Ca) eq 1 then Fgens := [Fgens[2]]; end if; //P1 case
    CG`ff_rat := [Index(seq,s): s in [mpCi(f) : f in Fgens]] where
	mpCi is Inverse(mpC) where seq is [FC.i : i in [1..Length(Ca)]];
    assert &and[i gt 0 : i in CG`ff_rat];

end procedure;

function gen_auto_data(CG,index)
// construct the ff_map and scheme isomorphism for 
// the index-th automorphism of CG

    aelt := CG`Aelts[index];
    aelt_inv := CG`Aelts[CG`invs[index]];
    binv := (CG`invs[index] eq index); //is the auto of order 1 or 2?
    bP1 := #(CG`Fgens) gt #(CG`ff_rat);

    // create the ff_map
    C := Domain(CG);
    KC := AlgorithmicFunctionField(FunctionField(C));
    if bP1 then
      aelt := [g1] cat aelt cat [g1] where g1 is(CG`Fgens)[1] ;
    end if;
    boo,mp,_ := HasMorphismFromImages(FunctionFieldCategory())
			(KC, KC, aelt);
    assert boo;
    if binv then
      mpi := mp;
    else
      if bP1 then
	aelt_inv := [g1] cat aelt_inv cat [g1] where g1 is(CG`Fgens)[1] ;
      end if;
      boo,mpi,_ := HasMorphismFromImages(FunctionFieldCategory())
			(KC, KC, aelt_inv);
      assert boo;
    end if;
    ff_map := SpecifyInverseMorphisms(FunctionFieldCategory())(mp, mpi);
    ff_map_inv := Inverse(ff_map);

    // get scheme iso
    Ca := AffinePatch(C1, FFPatchIndex(C1))
	where C1 is (IsProjective(C) select C else ProjectiveClosure(C));
    ff_seq := CG`rat_ff;
    rat_seq := [R.i : i in Reverse(CG`ff_rat)] 
			where R is CoordinateRing(Ambient(Ca));
    fns := [FunctionFieldEvaluation(ff_map(f),rat_seq) : f in ff_seq];
    fnsi := (binv select fns else 
	[FunctionFieldEvaluation(ff_map_inv(f),rat_seq) : f in ff_seq]);
    mp_aff := iso<Ca->Ca | fns, fnsi : Check := false>;
    crv_map := ProjectiveClosure(mp_aff);

    if assigned CG`eqn_deg_bnd then
	eqns := ReduceMapDegree(crv_map : DegreeBound := CG`eqn_deg_bnd);
	eqnsi := (binv select eqns else
	  ReduceMapDegree(Inverse(crv_map) : DegreeBound := CG`eqn_deg_bnd));
	crv_map := iso<C->C|eqns,eqnsi : Check := false>;
    elif (assigned CG`no_gcd) and CG`no_gcd then
	eqns := remove_GCD(crv_map);
	eqnsi := (binv select eqns else remove_GCD(Inverse(crv_map)));
	crv_map := iso<C->C|eqns,eqnsi : Check := false>;
    end if;

    return crv_map,ff_map;

end function;

function create_auto(CG,index)
// create the index-th automorphism of CG as a GrpAutCrvElt

    crv_map, ff_map := gen_auto_data(CG,index);
    g := InternalGrpAutCrvEltFromMapAutSch(CG,crv_map);
    g`index := index; g`ff_map := ff_map;
    return g;

end function;

function create_auto_rec(CG,index)
// create the index-th automorphism of CG as a grpAutCrvEltRec

    crv_map, ff_map := gen_auto_data(CG,index);
    return rec<grpAutCrvEltRec | crv_map := crv_map,
			ff_map := ff_map, index := index>;

end function;

function rec_to_auto(CG,a_rec)
// produces a GrpAutCrvElt from a grpAutCrvEltRec

    g := InternalGrpAutCrvEltFromMapAutSch(CG,a_rec`crv_map);
    g`index := a_rec`index; g`ff_map := a_rec`ff_map;
    return g;

end function;

procedure add_extra_attributes(~CG)
// add the Agens,id & PermMap attributes to CG

    // generate Agens elements
    Agens := [ create_auto_rec(CG,Index(CG`Gelts,(CG`G).i)) : 
					i in [1..Ngens(CG`G)]];
    CG`Agens := Agens;
    // and identity element
    C := Domain(CG);
    id_el := rec<grpAutCrvEltRec | crv_map := IdentityMap(C)>;
    /*id_el := InternalGrpAutCrvEltFromMapAutSch(CG,IdentityMap(C));*/
    id_el`ff_map := Identity(FunctionFieldCategory())
	(AlgorithmicFunctionField(FunctionField(C)));
    id_el`index := Index(CG`Aelts,CG`Fgens);
    CG`id := id_el;

end procedure;

procedure build_auto_group(~CG,L)
// creates the attributes of CG, the curve auto group generated
// by the list of automorphisms L

    C := Domain(CG);
    FC := AlgorithmicFunctionField(FunctionField(C));
    if IsAffine(C) then
	bP1 := Length(Ambient(C)) eq 1;
    else
	bP1 := Length(AffinePatch(Ambient(C),FFPatchIndex(C))) eq 1;
    end if;

    // generate group perm group + mapping data
    G,Gelts,Aelts,invs,Fgens := 
	GenCrvGrpData(L,  Identity(FunctionFieldCategory())(FC) : 
		Mult := Composition, bP1 := bP1);
    CG`Fgens := Fgens;
    CG`G := G;
    CG`Gelts := Gelts;
    CG`Aelts := Aelts;
    CG`invs := invs;

    if not assigned CG`ff_rat then
	add_ff_rat_map_data(~CG,Fgens);
    end if;

    add_extra_attributes(~CG);

end procedure;

////////////////// Aut group coercions ///////////////////////////////

intrinsic InternalGrpAutCrvCoerce(CG::GrpAutCrv,phi::MapSch) -> GrpAutCrvElt
{Internal function}
//try to coerce curve morphism phi into CG

    C := Domain(CG);
    //require ISA(Type(phi),MapSch) and (Domain(phi) eq C) and (Codomain(phi) eq C):
	//"Scheme map isn't an automorphism of the curve";

    FC := FunctionField(C);
    KC,mpC := AlgorithmicFunctionField(FC);
    phi := Expand(phi);

    // get corr. ff_map_ims for aelts
    // using stripped down version of Pullback
    phi_aff := RestrictionToPatch(phi,fp,fp) where fp is FFPatchIndex(C);
    ff_map_ims := [coerce_to_ff(eqns[i],CG`rat_ff) : i in CG`ff_rat] where
			eqns is DefiningEquations(phi_aff);
    
    // now do look-up of element in CG
    index := Index(CG`Aelts,ff_map_ims);
    require index ne 0: "Curve automorphism doesn't lie in the group";
    
    // get inverse data from CG and construct ff_map
    binv := (CG`invs[index] eq index); //is the auto of order 1 or 2?
    bP1 := #(CG`Fgens) gt #(CG`ff_rat);
    ff_map_inv_ims := CG`Aelts[CG`invs[index]];
    if bP1 then
      ff_map_ims := [g1] cat ff_map_ims cat [g1] where g1 is(CG`Fgens)[1] ;
    end if;
    boo,mp,_ := HasMorphismFromImages(FunctionFieldCategory())
			(KC, KC, ff_map_ims);
    assert boo;
    if binv then mpi := mp;
    else
      if bP1 then
        ff_map_inv_ims := [g1] cat ff_map_inv_ims cat [g1] where g1 is(CG`Fgens)[1] ;
      end if;
      boo,mpi,_ := HasMorphismFromImages(FunctionFieldCategory())
			(KC, KC, ff_map_inv_ims);
      assert boo;
    end if;
    ff_map := SpecifyInverseMorphisms(FunctionFieldCategory())(mp, mpi);

    if not HasKnownInverse(phi) then
    // if phi doesn't have inverse equations already, construct them now
      if binv then
	phi := iso<C->C | AllDefiningPolynomials(phi), AllDefiningPolynomials(phi)
			: Check := false>;
      else
	Ca := AffinePatch(C1, FFPatchIndex(C1))
	    where C1 is (IsProjective(C) select C else ProjectiveClosure(C));
	rat_seq := [R.i : i in Reverse(CG`ff_rat)] 
				where R is CoordinateRing(Ambient(Ca));
	fnsi := [FunctionFieldEvaluation(ff_map_inv(f),rat_seq) : f in CG`rat_ff]
			where ff_map_inv is Inverse(ff_map);
	mp_aff := iso<Ca->Ca | AllDefiningPolynomials(phi_aff), 
			fnsi : Check := false>;
	phi := ProjectiveClosure(mp_aff);
      end if;
    elif not ISA(Type(phi),MapAutSch) then
    // or convert to correct type if nec.
	phi := iso<C->C |AllDefiningPolynomials(phi),
		AllInverseDefiningPolynomials(phi) : Check := false>;	
    end if;

    if assigned CG`eqn_deg_bnd then
	eqns := ReduceMapDegree(phi : DegreeBound := CG`eqn_deg_bnd);
	eqnsi := (binv select eqns else
	  ReduceMapDegree(Inverse(phi) : DegreeBound := CG`eqn_deg_bnd));
	phi := iso<C->C|eqns,eqnsi : Check := false>;
    elif (assigned CG`no_gcd) and CG`no_gcd then
	eqns := remove_GCD(phi);
	eqnsi := (binv select eqns else remove_GCD(Inverse(phi)));
	phi := iso<C->C|eqns,eqnsi : Check := false>;
    end if;

    g := InternalGrpAutCrvEltFromMapAutSch(CG,phi);
    g`ff_map := ff_map; g`index := index;
    return g;

end intrinsic;

intrinsic InternalGrpAutCrvCoerce(CG::GrpAutCrv,phi::GrpAutCrvElt) -> GrpAutCrvElt
{Internal function}
//try to coerce gp crv auto phi into CG

    CG1 := Parent(phi);
    if CG1 eq CG then
	return phi;
    end if;
    assert Domain(CG1) eq Domain(phi);
    index := Index(CG`Aelts,CG1`Aelts[phi`index]);
    require index ne 0:
	"Automorphism doesn't lie in the group";
    phi1 := Aut(Domain(CG))!phi; // first convert back to plane scheme auto
    phi1 := InternalGrpAutCrvEltFromMapAutSch(CG,phi1);
    phi1`ff_map := phi`ff_map;
    phi1`index := index;
    return phi1;

end intrinsic;

intrinsic InternalGrpAutCrvCoerce(CG::GrpAutCrv,n::RngIntElt) -> GrpAutCrvElt
{Internal function}
//CG!1 = identity map

    assert n eq 1;
    return Id(CG);

end intrinsic;

////////// Isomorphism/Automorphism w/o group functions ////////////

function FldFunMapsToCurveMaps(phis,C,D)
//Returns the curve maps from C to D which corresponds to phis, field homomorphisms
// from the algorithmic (algebraic) function field of D to that of C.
    _,mpC := AlgorithmicFunctionField(FunctionField(C));
    _,mpD := AlgorithmicFunctionField(FunctionField(D));
    FC := Domain(mpC);
    FD := Domain(mpD);
    Da := AffinePatch(D, FFPatchIndex(D));
    coord_fns := [mpD(FD.i) : i in [1..Length(Da)]];
    Ca := AffinePatch(C, FFPatchIndex(C));
    if Length(Ca) eq 1 then //P^1 case
      Cseq := [R.1] where  R is CoordinateRing(Ambient(Ca));
    else
      Cseq := [Index(seq,s): s in [mpCi(f) : f in Fgens]] where
	mpCi is Inverse(mpC) where seq is [FC.i : i in [1..Length(Ca)]]
	where Fgens is Reverse(gen_seq(Codomain(mpC)));
      Cseq := [R.i : i in Cseq] where R is CoordinateRing(Ambient(Ca));
    end if;
    return [ProjectiveClosure(map<Ca->Da| 
	[FunctionFieldEvaluation(phi(c),Cseq) : c in coord_fns] : Check := false>) :
		phi in phis];
end function;

intrinsic Automorphisms(C::Crv : Bound := Infinity()) -> SeqEnum
{Returns a sequence of at most Bound (default: infinity) automorphisms
 of a curve.}
    require HasFunctionField(C): "Curve must have a function field";
    require (Type(BaseRing(C)) eq FldFin) or (Genus(C) gt 1):
	"Curve must be of genus greater than one or be defined over a finite field";
    require ValidBaseField(C,true):
	"Can't currently compute automorphisms over",
	"base field of curve.";

    // mch - 04/13 - clause to use the much faster code for
    //  hyperelliptic curves in that case
    if ISA(Type(C),CrvHyp) then
	G,mp := AutomorphismGroup(C);
	return [mp(g) : g in G];
    end if;

    FF := AlgorithmicFunctionField(FunctionField(C));
    c := IdentityFieldMorphism(BaseRing(C));
    try
      FFautos := Automorphisms(FF : BaseMorphism := c, Bound := Bound);
    catch e
      if Type(BaseRing(C)) cmpne FldFin then
	error e`Object;
      else
        FFautos := Automorphisms(FF : BaseMorphism := c, 
			Bound := Bound,
			Strategy := "DegOne");
      end if;
    end try;

    return FldFunMapsToCurveMaps(FFautos,C,C);
end intrinsic;

intrinsic IsIsomorphic(C::Crv,D::Crv) -> BoolElt,Map
{Tests if curves C and D are isomorphic. If so, also returns a scheme
 isomorphism between them.}
    require HasFunctionField(C) and HasFunctionField(D): 
 		"Curves must both have function fields";
    require BaseRing(C) eq BaseRing(D):
 		"Curves must be defined over the same base field.";
    if Genus(C) ne Genus(D) then return false,_; end if;
    require (Genus(C) gt 1) or (Type(BaseRing(C)) eq FldFin) :
	"For genus 0 or 1 curves the basefield must be finite.";
    require ValidBaseField(C,true):
	"Can't currently compute isomorphisms over",
	"base field of curves.";

    FFC := AlgorithmicFunctionField(FunctionField(C));
    FFD := AlgorithmicFunctionField(FunctionField(D));
    c := IdentityFieldMorphism(BaseRing(C));
    L := Isomorphisms(FFD, FFC : BaseMorphism := c, Bound := 1);
    if #L ne 0 then
	return true,(FldFunMapsToCurveMaps(L,C,D))[1];
    else 
 	return false,_;
    end if;
end intrinsic;

intrinsic Isomorphisms(C::Crv,D::Crv : Bound := Infinity()) -> SeqEnum
{Returns a sequence of at most Bound (default: infinity) isomorphisms
 between two curves.}
    require HasFunctionField(C) and HasFunctionField(D): 
 		"Curves must both have function fields";
    require BaseRing(C) eq BaseRing(D):
 		"Curves must be defined over the same base field.";
    if Genus(C) ne Genus(D) then return []; end if;
    require (Genus(C) gt 1) or (Type(BaseRing(C)) eq FldFin) :
	"For genus 0 or 1 curves the basefield must be finite.";
    require ValidBaseField(C,true):
	"Can't currently compute isomorphisms over",
	"base field of curves.";

    FFC := AlgorithmicFunctionField(FunctionField(C));
    FFD := AlgorithmicFunctionField(FunctionField(D));
    c := IdentityFieldMorphism(BaseRing(C));
    L := Isomorphisms(FFD, FFC : BaseMorphism := c, Bound := Bound);
    return FldFunMapsToCurveMaps(L,C,D);
end intrinsic;

/////////// Aut group constructors /////////////////////////////////

function InternalNewAutomorphismGroup(C)
    return InternalAutomorphismGroup(C,[]);
end function;

intrinsic AutomorphismGroup(C::Crv) -> GrpAutCrv
{ Returns the full automorphism group of curve C. }

    require HasFunctionField(C): "Curve must have a function field";
    require (Type(BaseRing(C)) eq FldFin) or (Genus(C) gt 1):
	"Curve must be of genus greater than one or be defined over a finite field";
    require ValidBaseField(C,true):
	"Can't currently compute automorphisms over",
	"base field of curve.";

    CG := InternalAutomorphismGroup(C);
    if assigned CG`G then // full auto group already built
	return CG;
    end if;

    // get list of all (AlFF) automorphisms
    FC := AlgorithmicFunctionField(FunctionField(C));
    try
      L := Automorphisms(FC : BaseMorphism := 
			IdentityFieldMorphism(BaseRing(C)));
    catch e
      if Type(BaseRing(C)) cmpne FldFin then
	error e`Object;
      else
        L := Automorphisms(FC : BaseMorphism := 
			IdentityFieldMorphism(BaseRing(C)),
			Strategy := "DegOne");
      end if;
    end try;
    build_auto_group(~CG,L);
    return CG;

end intrinsic;

intrinsic AutomorphismGroup(C::Crv, phis:: SeqEnum[MapAutSch]) -> GrpAutCrv
{ Returns the automorphism group of curve C generated by the
  sequence of scheme automorphisms in phis. }

    require HasFunctionField(C): "Curve must have a function field";
    require (Type(BaseRing(C)) eq FldFin) or (Genus(C) gt 1):
	"Curve must be of genus greater than one or be defined over a finite field";

    // if full automorphism group has already been computed,
    // compute as a subgroup of that.
    CG := InternalAutomorphismGroup(C);
    if assigned CG`G then
	return AutomorphismGroup(C,[CG | CG!phi : phi in phis]);
    end if;

    CG := InternalNewAutomorphismGroup(C);

    // convert phis to (AlFF) maps for group build
    FC := FunctionField(C);
    KC,mpC := AlgorithmicFunctionField(FC);
    Fgens := gen_seq(KC);
    add_ff_rat_map_data(~CG,Fgens);
    L := [];
    bP1 := #Fgens gt #(CG`ff_rat);
    for phi in phis do
      // get corr. ff_map_ims for aelts
      // using stripped down version of Pullback
      phi_aff := RestrictionToPatch(phi,fp,fp) where fp is FFPatchIndex(C);
      ff_map_ims := [coerce_to_ff(eqns[i],CG`rat_ff) : i in CG`ff_rat] where
			eqns is DefiningEquations(phi_aff);
      if bP1 then
	ff_map_ims := [g1] cat ff_map_ims cat [g1] where g1 is Fgens[1] ;
      end if;
      // and make AlFF morphism from it
      boo,mp,_ := HasMorphismFromImages(FunctionFieldCategory())
			(KC, KC, ff_map_ims);
      assert boo;
      Append(~L,mp);
    end for;
    if #L eq 0 then //if phis is empty, add the identity
	L := [Identity(FunctionFieldCategory())(KC)];
    end if;

    build_auto_group(~CG,L);
    return CG;

end intrinsic;

intrinsic AutomorphismGroup(C::Crv, gs:: SeqEnum[GrpAutCrvElt]) -> GrpAutCrv
{ Returns the (sub-)automorphism group of curve C generated by a
  sequence gs of elements in an automorphism group of C. }

    CG := Universe(gs);
    G := CG`G;
    if #gs eq #G then return CG; end if;

    inds := [g`index : g in gs];
    G1 := sub<G|[(CG`Gelts)[i] : i in inds]>;
    if #G1 eq #G then return CG; end if;

    Gelts_new := Transversal(G1,sub<G1|>);
    Aelts_new := {@ @};
    all_inds := [];
    for g in Gelts_new do
	ind := Index(CG`Gelts,G!g);
	Append(~all_inds,ind);
	Include(~Aelts_new,CG`Aelts[ind]);
    end for;
    invs_new := [(CG`invs)[i] : i in all_inds];
    invs_new := [Index(invs_new,i) : i in all_inds];

    CG1 := InternalNewAutomorphismGroup(C);
    CG1`Fgens := CG`Fgens;
    CG1`ff_rat := CG`ff_rat;
    CG1`rat_ff := CG`rat_ff;
    CG1`G := G1;
    CG1`Gelts := Gelts_new;
    CG1`Aelts := Aelts_new;
    CG1`invs := invs_new;

    add_extra_attributes(~CG1);
    return CG1;

end intrinsic;

//////// Aut Group Operations /////////////////////////////

intrinsic 'in'(phi :: MapSch, CG::GrpAutCrv) -> BoolElt
{Returns whether phi is equal to an automorphism in CG}
    C := Domain(CG);
    if (Domain(phi) cmpne C) or  (Codomain(phi) cmpne C) then
	return false;
    end if;
    FC := FunctionField(C);
    KC,mpC := AlgorithmicFunctionField(FC);

    // get corr. ff_map_ims for aelts
    // using stripped down version of Pullback
    phi_aff := RestrictionToPatch(phi,fp,fp) where fp is FFPatchIndex(C);
    ff_map_ims := [coerce_to_ff(eqns[i],CG`rat_ff) : i in CG`ff_rat] where
			eqns is DefiningEquations(phi_aff);
    
    // now do look-up of element in CG
    return (Index(CG`Aelts,ff_map_ims) ne 0);

end intrinsic;

intrinsic 'in'(g :: GrpAutCrvElt, CG::GrpAutCrv) -> BoolElt
{Returns whether g is equal to an automorphism in CG}
    if Parent(g) eq CG then return true; end if;
    C := Domain(CG);
    CG1 := Parent(g);
    if (Domain(CG1) cmpne C) then
	return false;
    end if;

    return (Index(CG`Aelts,CG1`Aelts[g`index]) ne 0);

end intrinsic;

intrinsic '.'(CG::GrpAutCrv,i::RngIntElt) -> GrpAutCrvElt
{ Returns the ith generator of the curve automorphism group}

    n := #CG`Agens;
    //require (i ge -n) and (i le n): "Invalid generator index";
    if not ((i ge -n) and (i le n)) then
       error_string := "Value for index (" * IntegerToString(i) *
                       ") should be in the range [" * IntegerToString(-n) * 
                       ".." * IntegerToString(n) * "]";
       require false: error_string;
    end if;
    if i gt 0 then
	return rec_to_auto(CG,CG`Agens[i]);
    elif i eq 0 then
	return rec_to_auto(CG,CG`id);
    else
	return Inverse(rec_to_auto(CG,CG`Agens[-i]));
    end if;

end intrinsic;

intrinsic 'subset'(CH::GrpAutCrv,CG::GrpAutCrv) -> BoolElt
{ Returns whether CH is a subset of CG. }

    if CH eq CG then return true; end if;
    if (Domain(CH) cmpne Domain(CG)) or
	  not IsDivisibleBy(#(CG`G),#(CH`G)) then
	return false;
    end if;

    if CG eq InternalAutomorphismGroup(Domain(CG)) then
	return true; //CG is the full group of autos
    end if;

    return &and[f in CG`Aelts : f in CH`Aelts];

end intrinsic;

//////// Aut Group accessor functions /////////////////////////////

intrinsic Curve(CG::GrpAutCrv) -> Crv
{ Returns the curve on which the automorphism group acts. }
    return Domain(CG);
end intrinsic;

// NB: Only define one of Id and Identity (the other is defined automatically)
intrinsic Id(CG::GrpAutCrv) -> GrpAutCrvElt
{ Returns the identity element of CG.}
    return rec_to_auto(CG,CG`id);
end intrinsic;

intrinsic Order(CG::GrpAutCrv) -> RngIntElt
{ Order of the curve automorphism group. }
    return Order(CG`G);
end intrinsic;

intrinsic '#'(CG::GrpAutCrv) -> RngIntElt
{ Order of the curve automorphism group. }
    return Order(CG`G);
end intrinsic;

intrinsic FactoredOrder(CG::GrpAutCrv) -> RngIntElt
{ Factored order of the curve automorphism group. }
    return FactoredOrder(CG`G);
end intrinsic;

intrinsic NumberOfGenerators(CG::GrpAutCrv) -> RngIntElt
{ The number of group generators of CG. }
    return #(CG`Agens);
end intrinsic;

intrinsic Generators(CG::GrpAutCrv) -> SeqEnum
{ The group generators of CG. }
    return [rec_to_auto(CG,g) : g in CG`Agens];
end intrinsic;

intrinsic PermutationGroup(CG::GrpAutCrv) -> GrpPerm
{ The permutation group providing the basic group representation
  of CG. }
    return CG`G;
end intrinsic;

intrinsic PermutationRepresentation(CG::GrpAutCrv) -> GrpPerm, Map
{ The permutation group G and isomorphism CG->G, providing the basic
  group representation of CG. }
    return CG`G, map<CG->CG`G| phi :-> (CG`Gelts)[phi`index],
			g :-> create_auto(CG,Index(CG`Gelts,g))>;
end intrinsic;

////////// Basic Aut group element operations /////////////////////////

intrinsic Order(g::GrpAutCrvElt) -> RngIntElt
{ Order of the curve automorphism. }
    return Order(Parent(g)`Gelts[g`index]);
end intrinsic;

intrinsic Inverse(f::GrpAutCrvElt) -> GrpAutCrvElt
{ Inverse of a curve automorphism }
    CG := Parent(f);
    finv := InternalGrpAutCrvEltFromMapAutSch(CG,
	iso<Domain(f)->Domain(f)|AllInverseDefiningPolynomials(f),
		AllDefiningPolynomials(f) : Check := false>);
    finv`ff_map := Inverse(f`ff_map);
    finv`index := CG`invs[f`index];
    return finv;
end intrinsic;

intrinsic 'eq'(g :: GrpAutCrvElt,h :: GrpAutCrvElt) -> BoolElt
{ Returns whether the curve automorphisms given by the two elements
  are equal }

    CGg := Parent(g); CGh := Parent(h);
    if CGg eq CGh then //elts of same aut group
	return g`index eq h`index;
    else
	return (Domain(CGg) cmpeq Domain(CGh)) and
		(CGg`Aelts[g`index] eq CGh`Aelts[h`index]);
    end if;

end intrinsic;

intrinsic 'ne'(g :: GrpAutCrvElt,h :: GrpAutCrvElt) -> BoolElt
{ Returns whether the curve automorphisms given by the two elements
  are unequal }

    return not (g eq h);

end intrinsic;

intrinsic '*'(f::GrpAutCrvElt,g::GrpAutCrvElt) -> GrpAutCrvElt
{ The composition of the two curve automorphisms. }

    CG := Parent(f);
    require (CG eq Parent(g)): "Automorphisms must lie in same group";
    ind_fg := Index(CG`Gelts,(CG`Gelts)[f`index]*(CG`Gelts)[g`index]);
    return create_auto(CG,ind_fg);

end intrinsic;

intrinsic '^'(f::GrpAutCrvElt,n::RngIntElt) -> GrpAutCrvElt
{ nth power of curve automorphism f. }

    CG := Parent(f);
    // special cases
    case n:
	when 0: return Id(CG);
	when 1: return f;
	when -1: return Inverse(f);
    end case;
    ind_fn := Index(CG`Gelts,(CG`Gelts)[f`index]^n);
    return create_auto(CG,ind_fn);

end intrinsic;

intrinsic SchemeMap(f::GrpAutCrvElt) -> MapAutSch
{ Returns f as a plain MapAutSch }

    C := Domain(f);
    return iso<C->C|AllDefiningPolynomials(f),AllInverseDefiningPolynomials(f)>;

end intrinsic;

/////////////////////////////////////////////////////////////////
//   Pullback and Pushforward/Image intrinsics for curve       //
//   automorphisms on points, places, divisors, functions      //
//   and differentials.                                        //
/////////////////////////////////////////////////////////////////


intrinsic '@'(pt::Pt, g::GrpAutCrvElt) -> Pt
{ The image of point pt under curve automorphism g. }

    K := Ring(Parent(pt));
    C := Scheme(pt);

    if Scheme(pt) ne Domain(g) then
	if K eq BaseRing(C) then
	    boo,pt := IsCoercible(C,pt);
	else
	    boo,pt := IsCoercible(C(K),pt);
	end if;
	require boo: 
	  "Point is not coercible into a pointset on the curve"; 
    end if;

    // first try normal image
    im_pt := [Evaluate(f,seq) : f in DefiningPolynomials(g)] where
		seq is Coordinates(pt);
    if &or[c ne 0 : c in im_pt] then
	return Parent(pt)!im_pt;
    end if;

    // now try to use places
    require IsField(K): 
	"Image of point is not computable for this automorphism";
    phi := Inverse(g`ff_map);
    pls := Places(pt);
    im_pls := [ CurvePlace(C,CommonZeros([Image(phi,a),Image(phi,b)])[1])
 	where a,b := TwoGenerators(FunctionFieldPlace(pl)) :
	  pl in pls ];
    im_pts := [RepresentativePoint(pl) : pl in im_pls];
    pt_set := Parent(pt);
    boo,pt := IsCoercible(pt_set,im_pts[1]);
    for i in [2..#im_pts] do
	if not boo then break; end if;
	boo,pt1 := IsCoercible(pt_set,im_pts[1]);
	if boo then boo := (pt1 eq pt); end if;
    end for;
    if boo then 
	return pt;
    else
	error "Map not defined at (singular) point";
    end if;
 
end intrinsic;

intrinsic '@'(pl::PlcCrvElt, g::GrpAutCrvElt) -> PlcCrvElt
{ The image of place pl under curve automorphism g. }

    require Curve(pl) eq Domain(g):
	"Place is not on the domain of the curve automorphism.";
    phi := Inverse(g`ff_map);
    return CurvePlace(Curve(pl),CommonZeros([Image(phi,a),Image(phi,b)])[1])
 	where a,b := TwoGenerators(FunctionFieldPlace(pl));

end intrinsic;

intrinsic '@@'(pl::PlcCrvElt, g::GrpAutCrvElt) -> PlcCrvElt
{ The pullback of place pl under curve automorphism g. }

    require Curve(pl) eq Domain(g):
	"Place is not on the domain of the curve automorphism.";
    phi := g`ff_map;
    return CurvePlace(Curve(pl),CommonZeros([Image(phi,a),Image(phi,b)])[1])
 	where a,b := TwoGenerators(FunctionFieldPlace(pl));

end intrinsic;

function curve_div_image(D,phi)
    // don't use above function for curve places to avoid
    // poss extra rep point computations on C places
    S,e := Support(FunctionFieldDivisor(D));
    S := [ CommonZeros([Image(phi,a),Image(phi,b)])[1]
	where a,b := TwoGenerators(s) : s in S ];
    return CurveDivisor(Curve(D),&+[e[i]*S[i] : i in [1..#S]]);
end function;

intrinsic '@'(D::DivCrvElt, g::GrpAutCrvElt) -> DivCrvElt
{ The image of divisor D under curve automorphism g. }

    require Curve(D) eq Domain(g):
	"Divisor is not on the domain of the curve automorphism.";
    return curve_div_image(D,Inverse(g`ff_map));

end intrinsic;

intrinsic '@@'(D::DivCrvElt, g::GrpAutCrvElt) -> DivCrvElt
{ The pullback of divisor D under curve automorphism g. }

    require Curve(D) eq Domain(g):
	"Divisor is not on the domain of the curve automorphism.";
    return curve_div_image(D,g`ff_map);

end intrinsic;

intrinsic '@@'(f::FldFunFracSchElt, g::GrpAutCrvElt) -> FldFunFracSchElt
{ The pullback of function f under curve automorphism g. }

    C := Curve(Parent(f));
    require C eq Domain(g):
	"Function is not on the domain of the curve automorphism.";
    phi := g`ff_map;
    KC,mpC := AlgorithmicFunctionField(FunctionField(C));
    return Inverse(mpC)(phi(mpC(f)));

end intrinsic;

intrinsic '@'(f::FldFunFracSchElt, g::GrpAutCrvElt) -> FldFunFracSchElt
{ The pushforward of function f under curve automorphism g. }

    C := Curve(Parent(f));
    require C eq Domain(g):
	"Function is not on the domain of the curve automorphism.";
    phi := Inverse(g`ff_map);
    KC,mpC := AlgorithmicFunctionField(FunctionField(C));
    return Inverse(mpC)(phi(mpC(f)));

end intrinsic;

function curve_diff_image(df,phi)
    df1 := FunctionFieldDifferential(df);
    x := SeparatingElement(Domain(phi));
    a := df1/Differential(x);
    return CurveDifferential(Curve(df),phi(a) * Differential(phi(x)));
end function;

intrinsic '@@'(df::DiffCrvElt, g::GrpAutCrvElt) -> DiffCrvElt
{ The pullback of differential df under curve automorphism g. }

    require Curve(df) eq Domain(g):
	"Differential is not on the domain of the curve automorphism.";
    return curve_diff_image(df,g`ff_map);

end intrinsic;

intrinsic '@'(df::DiffCrvElt, g::GrpAutCrvElt) -> DiffCrvElt
{ The pushforward of differential df under curve automorphism g. }

    require Curve(df) eq Domain(g):
	"Differential is not on the domain of the curve automorphism.";
    return curve_diff_image(df,Inverse(g`ff_map));

end intrinsic;

//////////////////// Trace and Norm functions /////////////////////////

intrinsic Trace(f::FldFunElt,G::GrpAutCrv) -> FldFunElt
{The trace of f under the action of G}

    KC := Parent(f);
    require KC eq AlgorithmicFunctionField(FunctionField(Curve(G))):
	"Function is not a member of the function field of the curve";
    tr := KC!0;
    ff_cat := FunctionFieldCategory();
    bP1 := #(G`Fgens) gt #(G`ff_rat);
    if bP1 then g1 := (G`Fgens)[1]; end if; //P^1 case
    for aelt in G`Aelts do
	ae := (bP1 select ([g1] cat aelt cat [g1]) else aelt);
	tr +:= (MorphismFromImages(ff_cat)(KC, KC, ae))(f);
    end for;
    return tr;
    
end intrinsic;

intrinsic Norm(f::FldFunElt,G::GrpAutCrv) -> FldFunElt
{The norm of f under the action of G}

    KC := Parent(f);
    require KC eq AlgorithmicFunctionField(FunctionField(Curve(G))):
	"Function is not a member of the function field of the curve";
    tr := KC!1;
    ff_cat := FunctionFieldCategory();
    bP1 := #(G`Fgens) gt #(G`ff_rat);
    if bP1 then g1 := (G`Fgens)[1]; end if; //P^1 case
    for aelt in G`Aelts do
	ae := (bP1 select ([g1] cat aelt cat [g1]) else aelt);
	tr *:= (MorphismFromImages(ff_cat)(KC, KC, ae))(f);
    end for;
    return tr;
    
end intrinsic;

intrinsic Trace(f::FldFunFracSchElt,G::GrpAutCrv) -> FldFunFracSchElt
{The trace of f under the action of G}
    C := Curve(Parent(f));
    require C eq Curve(G):
	"Function is not a member of the function field of the curve";
    KC,mpC := AlgorithmicFunctionField(FunctionField(C));
    return Inverse(mpC)(Trace(mpC(f),G));
    
end intrinsic;

intrinsic Norm(f::FldFunFracSchElt,G::GrpAutCrv) -> FldFunFracSchElt
{The norm of f under the action of G}
    C := Curve(Parent(f));
    require C eq Curve(G):
	"Function is not a member of the function field of the curve";
    KC,mpC := AlgorithmicFunctionField(FunctionField(C));
    return Inverse(mpC)(Norm(mpC(f),G));
    
end intrinsic;

/////////////////////////////////////////////////////////////////
//   Matrix representation of an automorphism group on the     //
//   space of global differentials.                            //
/////////////////////////////////////////////////////////////////

intrinsic MatrixRepresentation(G::GrpAutCrv) -> GrpMat, Map, SeqEnum
{ The representation (by pullback) of automorphism group G of the curve C on a
  basis B of global differentials of C. Genus(C) must be at least 2. Return
  values are the (finite) matrix group image, the map from G to this image,
  and the basis of differentials as a sequence }

    C := Curve(G);
    require Genus(C) ge 2: 
	"The genus of the curve must be >= 2";
    K := BaseRing(C);

    //get group of reps on holo diffs
    Gp,pmp := PermutationRepresentation(G);
    gens := [Inverse(pmp)(Gp.i) : i in [1..Ngens(Gp)]];
    W,mp := SpaceOfHolomorphicDifferentials(C);
    B := [mp(b) : b in Basis(W)];
    mats := [Matrix([Eltseq(Inverse(mp)(g(b))) : b in B]) :
		g in gens];
    LG := GL(#B,K);
    matgens := [LG!m : m in mats];
    Gmat := sub<LG|matgens>;
    hmptom := hom<Gp->Gmat|matgens>;
    mpGtom := pmp*hmptom;

    return Gmat,mpGtom,B;

end intrinsic;
