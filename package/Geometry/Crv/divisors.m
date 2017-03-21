
freeze;

////////////////////////////////////////////////////////////////////////
//                     Places and Divisors on Curves                  // 
//  Original file due to Gavin Brown.                                 //
//  Modification and extensions due to David Kohel.                   //
//  GDB Dec 2004:  rough update to new function field types           //
////////////////////////////////////////////////////////////////////////

declare verbose Divisors, 2;

import "fld_fun.m": no_pole_on_curve;

declare attributes Crv: ambig_plcs;

////////////////////////////////////////////////////////////////////////
//     Divisors defined by ideals, intersections, and subschemes      //
////////////////////////////////////////////////////////////////////////

intrinsic Identity(D::DivCrv) -> DivCrvElt
{The identity element of the divisor group};
    return D!0;
end intrinsic;

intrinsic Divisor(D::DivCrv, p::Pt, q::Pt) -> DivCrvElt
{The principal intersection divisor of the line through
    points p and q with the curve C of D.} 
    return Divisor(Curve(D), p, q);
end intrinsic;

intrinsic Divisor(C::Crv,p::Pt,q::Pt) -> DivCrvElt
{The principal intersection divisor of the line through
    points p and q with the curve C.} 
    L := Line(Ambient(C),{p,q});
    return Divisor(C,L);
end intrinsic;

intrinsic Divisor(D::DivCrv, X::Sch) -> DivCrvElt
{The intersection divisor of the scheme X with the curve C
    of D.}
    return Divisor(Curve(D), X);
end intrinsic;

intrinsic Divisor(C::Crv,X::Sch) -> DivCrvElt
    {The intersection divisor of the scheme X with the curve C.}
    if IsAffine(C) then
	C := ProjectiveClosure(C);
    end if;
    require IsProjective(X) and Ambient(C) cmpeq Ambient(X) :
        "Argument 2 must be a projective scheme in the " * 
        "same space as the curve of argument 1.";
    Z := Intersection(C,X);
    if IsEmpty(Z) then return DivisorGroup(C)!0; end if;
    require Dimension(Z) le 0 :
       "Argument 2 must meet the curve of argument 1 " *
       "at a subscheme of dimension zero.";
    I := Ideal(Z);
    return Divisor(C,I);
end intrinsic;

// This function should not be needed, but is kept so that the
// following intrinsic needs virtually no updating---only the
// '@ m' added---to the new ff type.
function RelativeRepresentation(K)
    // F := RationalExtensionRepresentation(K);
    F,m := AlgorithmicFunctionField(K);
    xy := [ K | (F!BaseField(F).1) @@ m, F.1  @@ m];
    u := K.1; v := K.2;
    if xy[1] eq u and xy[2] eq v then
        return F, [1,2,3], m;
    elif xy[1] eq v and xy[2] eq u then
        return F, [2,1,3], m;
    elif xy[1] eq u/v and xy[2] eq 1/v then
        return F, [1,3,2], m;
    elif xy[1] eq 1/v and xy[2] eq u/v then
        return F, [3,1,2], m;
    elif xy[1] eq v/u and xy[2] eq 1/u then
        return F, [1,3,2], m;
    elif xy[1] eq 1/u and xy[2] eq v/u then
        return F, [3,2,1], m;
    end if;
    error "Unknown transformation in RationalExtensionRepresentation.";
end function;

/*  MCH- Feb 05
    Helper function which finds all ambiguous places on C -
    that is, one's whose corresponding point lies in neither
    the function field patch or the "infinite" patch.
    Returns these along with the inifinite patch index.
*/ 
function FindAmbiguousPlaces(C)

    F := FunctionField(C);
    K,m := AlgorithmicFunctionField(F);
    ap_fin := FFPatchIndex(C);
    P := Ambient(C);
    
    /* find the projective coordinate "giving" the AlFF base element */ 
    sep_elt := SeparatingElement(K);
    A := AffinePatch(P,ap_fin);
    ind_inf := 0;
    for i in [1..Length(A)] do
	if sep_elt eq m(F!(A.i)) then
	    Xi := Numerator(InverseDefiningPolynomials(
		ProjectiveClosureMap(A))[i]);
	    ind_inf := Index([P.i : i in [1..Length(P)]],Xi);
	    break;
	end if;
    end for;
    assert ind_inf ne 0;
        
	
    /* the ambiguous places are now precisely those lying over points
       which are neither in ap_fin or ap_inf. We compute those and
       return them indexed by the first patch they lie in */
    data := [**];
    if NGrad(Ambient(C)) eq 1 then  // non multi-graded case
	wgts := Reverse(Gradings(C)[1]);
	ap_inf := #wgts+1-ind_inf;
        Xf := P.(Length(P)+1-ap_fin);
	S := Scheme(P,Xf) meet (Scheme(P,Xi) meet C);
	for k in [1..#wgts] do
	    if (wgts[k] ne 1) or (k eq ap_fin) or (k eq ap_inf) then
	        continue;
	    end if;
	    if IsEmpty(S) then break; end if;
	    X := P.(#wgts+1-k);
	    pls := Zeros(F!(Xf/X));
	    pls := [pl : pl in pls |
		(Coordinate(pt,#wgts+1-k) ne 0) and
		  (Coordinate(pt,ind_inf) eq 0) where
	   	    pt is RepresentativePoint(pl)];

	    if #data gt 0 then
		pls := [pl : pl in pls| pl notin
				&cat[data[j][2]: j in [1..#data]]];
	    end if;
	    if #pls gt 0 then
	        Append(~data,<k,pls>);
	    end if;
	    S := S meet Scheme(P,X);
	end for;
    else          // multi-graded case
        grads := Gradings(C);
	/* compute which grading the inf variable comes under. */
	grad_inf := Min([j : j in [1..#grads] | grads[j][ind_inf] eq 1]);
	/* find the corresponding "finite" variable */
	/* "infinite patch" - given by Xi != 0 and Xj != 0 for the
	   X_j vars for ap_fin for gradings != grad_inf */
        pcm := ProjectiveClosureMap(AffinePatch(Ambient(C),ap_fin));
	inf_vars := [j : j in [1..#eqs] | eqs[j] eq 1] where
		eqs is DefiningEquations(pcm);
	S := Scheme(P,&*[P.j:j in inf_vars]) meet C;
	fin_ind := Min([j : j in inf_vars | grads[grad_inf][j] eq 1]);
	Xf := P.fin_ind;
	pos := Index(inf_vars,fin_ind);
	inf_vars[pos] :=  ind_inf;
        S := Scheme(P,&*[P.j:j in inf_vars]) meet S;
	s_empty := false;
	
	for k in [1..NumberOfAffinePatches(C)] do
	    if (k eq ap_fin) then
	        continue;
	    end if;
	    s_empty := s_empty or IsEmpty(S);
	    pcm := ProjectiveClosureMap(AffinePatch(Ambient(C),k));
	    loc_vars := [j : j in [1..#eqs] | eqs[j] eq 1] where
		eqs is DefiningEquations(pcm);
	    if loc_vars eq inf_vars then 
	        ap_inf := k;
		continue;
	    end if;
	    if s_empty then
	        if ap_inf eq 0 then continue;
		else break; end if;
            end if;
	    
	    fn1 := &*[F|(P.inf_vars[j]/P.loc_vars[j]) : j in [1..#grads] |
	    						    j ne pos];
            pls := Zeros(fn1);
	    pls := [pl : pl in pls |
	      RepresentativePoint(pl) in AffinePatch(Ambient(C),k)];

            if (loc_vars[pos] ne fin_ind) and (loc_vars[pos] ne ind_inf) then
	      pls1 := Zeros(F!(Xf/P.loc_vars[pos]));
	      pls1 := [pl : pl in pls1 |
	        (pt in AffinePatch(Ambient(C),k)) and
		  (Coordinate(pt,ind_inf) eq 0) where
	   	    pt is RepresentativePoint(pl)];
	      pls := pls cat [pl : pl in pls1 | pl notin pls];
	      delete pls1;
	    end if;

	    if #data gt 0 then
		pls := [pl : pl in pls| pl notin
				&cat[data[j][2]: j in [1..#data]]];
	    end if;
	    if #pls gt 0 then
	        Append(~data,<k,pls>);
	    end if;
	    S := S meet Scheme(P,&*[P.j:j in inf_vars]);
	end for;
    end if;
    
    return <data,ap_inf>; 
end function;

/* Returns the ambiguous places of C - see function above */
function AmbiguousPlaces(C)
    if not(assigned(C`ambig_plcs)) then
	C`ambig_plcs := FindAmbiguousPlaces(C);
    end if;
    return a[1],a[2] where a is C`ambig_plcs;
end function;

intrinsic Divisor(D::DivCrv, I::RngMPol) -> DivCrvElt
{The divisor defined by the ideal I of the coordinate ring 
    of the ambient of the projective curve C of D.}
    return Divisor(Curve(D), I);
end intrinsic;

/*
MCH, Feb 05:
 Replaced with version for general (ie non-plane) curves.
 Roughly, the same as before - localising I on the function field patch
 gives a part of the divisor that comes in the finite AlFF ideal and
 localising on an "infinite" patch gives a part which comes in the
 infinite AlFF ideal. However, there are more ambiguous places:
 points that lie in neither of the two patchs, so any component of I
 corresponding to them is "killed" in either localisation.
  We need a list of these places, (only [0,1,0] in the plane case) and
 appropriate affine patchs in which they lie for localisation. This
 data is provided by a new function above and stored as an attribute.
 
NJS, Jan 05:
The example below is fixed. Just map affine ideal over into projective closure.

GDB, Dec 04:
The next intrinsic demands that I is an ideal on the projective closure.
Thus, the following failure:
    > A<x,y> := AffineSpace(Rationals(),2);
    > C := Curve(A,x^2 + y);
    > I := ideal< CoordinateRing(A) | x >;
    > Div := DivisorGroup(C);
    > Divisor(Div,I);
    >> Divisor(Div,I);
	      ^
    Runtime error in 'Divisor': Argument 2 must be an ideal in the coordinate
    ring of the ambient of the curve of argument 1.
If you note that
    > Curve(Div);
    Curve over Rational Field defined by
    $.1^2 + $.2*$.3
so that the curve of Div is regarded as the projective curve,
then this is not so opaque.  Nevertheless, we might find that
somebody would like to use this function for ideals of
coordinate rings of affine patches.

*/
intrinsic Divisor(C::Crv,I::RngMPol) -> DivCrvElt
    {The divisor defined by the ideal I of the coordinate ring 
    of the ambient of the curve C or its projective closure.}
    require HasFunctionField(C):
	"Curve must be able to have a function field created";
    R := Generic(I);
    if IsAffine(C) then
	K := FunctionField(C); //force patch index!
      if R cmpeq CoordinateRing(Ambient(C)) then
	if C eq AffinePatch(ProjectiveClosure(C), FFPatchIndex(C)) then
	// avoid projectivisation : can work simply and directly!
	    F,m := AlgorithmicFunctionField(K);
	    O1 := MaximalOrderFinite(F);
	    I1 := ideal< O1 | 1 > meet 
		ideal< O1 | [m(K!f): f in Basis(I)] >;
	    return CurveDivisor(ProjectiveClosure(C), Divisor(I1));
	else
	// otherwise, we work projectively: may pick up unwanted
	// infinite places!
	// get the homogenisation of I schemewise 
	    I := Ideal(ProjectiveClosure(Scheme(Ambient(C),I)));
	end if;
      end if;
	C := ProjectiveClosure(C);
	R := Generic(I);
    end if;
    require R cmpeq CoordinateRing(Ambient(C)) and IsHomogeneous(I) :
        "Argument 2 must be a homogeneous ideal in the coordinate ring " *
        "of the ambient of the curve of argument 1.";
    /* special check to get 0 divisor which gives error below */
    if not IsProper(I) then
	return DivisorGroup(C)!0;
    end if;
    I := ideal< R | Basis(I) cat Basis(Ideal(C))/*[ Polynomial(C) ]*/ >;
    require Dimension(Scheme(Ambient(C),I)) le 1 : // projective dimension 0!
        "Scheme of argument 2 must meet the curve of argument 1 " *
        "at a subscheme of dimension zero.";
    K := FunctionField(C);
    F,m := AlgorithmicFunctionField(K);
    ap_fin := FFPatchIndex(C);

    /* get a homogeneous basis for I */
    B := Basis(I);
    if not &and[IsHomogeneous(Ambient(C),f) : f in B] then
	B := GroebnerBasis(I);
    end if;

    // First deal with the ambiguous part of the divisor:  
    // places <-> points not lying in the function field patch(ap_fin) 
    // or the "infinite patch" (ap_inf) on which the coordinate
    // function giving the separating elt of the function field
    // is non-zero.
    
    ambig_plcs,ap_inf := AmbiguousPlaces(C);
//printf "ambs: %o\np.i.:%o\n",ambig_plcs,ap_inf;        
    D0 := DivisorGroup(C)!0;
    b_amb_mult_gt_1 := false;
    for i in [1..#ambig_plcs] do
	ap := ambig_plcs[i][1];
	plcs := ambig_plcs[i][2];
	coord_fns := ChangeUniverse(DefiningEquations(pcm), K) where pcm is
	    ProjectiveClosureMap(Ambient(AffinePatch(C,ap)));
	vals := [Min([Valuation(Evaluate(f,coord_fns),plc ) : f in B]) :
			plc in plcs];
	mv := Max(vals);
	if mv gt 0 then
	    D0 := D0 + 
	      &+[DivisorGroup(C)| vals[i]*plcs[i] : i in [1..#plcs]];
	    if mv gt 1 then b_amb_mult_gt_1 := true; end if;
	end if;
    end for;
    /* 
	NB: there's no need to remove the components from I corr.
        to the ambiguous places as these all "die" in localisation
	to the ap_fin and ap_inf patchs.
       WRONG! If an amb place shows up with multiplicity > 1 then it
       may also appear (with lower multiplicity) in one of the
       finite or infinite places. It is easiest to fix this at
       the end by doing an LCM rather than addition of divisors.
       This has now been done - mch -04/08.    
    */

    
    // The "finite" part of the divisor:
    O1 := MaximalOrderFinite(F);
    coord_fns := m(ChangeUniverse(DefiningEquations(pcm), K)) where pcm is
	    ProjectiveClosureMap(Ambient(AffinePatch(C,ap_fin)));
    B1 := [ Evaluate(f,coord_fns) : f in B ];
    I1 := ideal< O1 | 1 > meet ideal< O1 | B1 >;
    D1 := CurveDivisor(C, Divisor(I1));
    // The "infinite" part of the divisor:
    O2 := MaximalOrderInfinite(F);
    coord_fns := m(ChangeUniverse(DefiningEquations(pcm), K)) where pcm is
	    ProjectiveClosureMap(Ambient(AffinePatch(C,ap_inf)));
    B2 := [ Evaluate(f,coord_fns) : f in B ];
    I2 := ideal< O2 | 1 > meet ideal< O2 | B2 >;
    D2 := CurveDivisor(C, Divisor(I2));
    if GetVerbose("Divisors") gt 0 then
	printf "Finite/Infinite patchs: %o/%o\n", ap_fin,ap_inf;
	"D0 =", D0;
	m_inv := Inverse(m);
	"B1 =", [ m_inv(f) : f in B1 ];
	"D1 =", D1;
	"B2 =", [ m_inv(f) : f in B2 ];
	"D2 =", D2;
    end if;
    if b_amb_mult_gt_1 then
	return LCM(D0,D1+D2);
    else
	return D0 + D1 + D2;
    end if;
end intrinsic;

intrinsic Place(C::Crv, I::RngMPol) -> PlcCrvElt
{Return the place of the curve C defined by the ideal I}
    require IsPrime(I) : "Ideal must be prime";
    require HasFunctionField(C) : "Curve must be able to have a function field created";

    S, E := Support(Divisor(C, I));
    assert #S eq 1;
    assert E[1] eq 1;
    return S[1];
end intrinsic;

intrinsic Divisor(Div::DivCrv,f::RngElt) -> DivCrvElt
    {The principal divisor on the curve C of Div defined by the function f}
    return Divisor(Curve(Div),f);
end intrinsic;

intrinsic Divisor(C::Crv,f::RngElt) -> DivCrvElt
    {The principal divisor on C defined by the function f.}
    F := FunctionField(C);
    coercible,f := IsCoercible(F,f);
    require coercible:  "Second argument is not a function on the first";
    return Divisor(f);
end intrinsic;

intrinsic Divisor(f::FldFunFracSchElt[Crv]) -> DivCrvElt
    {The principal divisor on the curve of f 
    defined by the function f.}
    F := Parent(f);
    C := Scheme(F);
    _, m := AlgorithmicFunctionField(F);
    return CurveDivisor(Curve(C), Divisor(m(f)));
end intrinsic;

intrinsic PrincipalDivisor(Div::DivCrv,f::RngElt) -> DivCrvElt
    {The principal divisor on the curve C of Div defined by the function f }
    return Divisor(Div,f);
end intrinsic;

intrinsic PrincipalDivisor(C::Crv,f::RngElt) -> DivCrvElt
    {The principal divisor on C defined by the function f.}
    return Divisor(C,f);
end intrinsic;

intrinsic PrincipalDivisor(f::FldFunFracSchElt[Crv]) -> DivCrvElt
    {The principal divisor on the curve of f
    defined by the function f.}
    return Divisor(f);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                Associated Subschemes and Ideals                    //
////////////////////////////////////////////////////////////////////////

/************** OLD DIVISOR FUNCTION ***************************
  Has problem if a point at infinity on C (ie with z=0 in x,y,z
    homog coords) doesn't have (y/z)=infinity if the
    function field is given by k(Y)[X] with Y=y/z, X=x/z
    
    eg doesn't work for xy-z^2 and D = [1:0:0] + [0:1:0]
    (resulting ideal has divisor 2*[1:0:0]).
    
  also the problem of generalising to non-planar curves.
  
intrinsic Ideal(D::DivCrvElt) -> RngMPol
    {The ideal of coordinate functions which cuts out D.}
    C := ProjectiveCurve(Parent(D));
    K := FunctionField(C);
    R := CoordinateRing(Ambient(C));
    X := R.1; Y := R.2; Z := R.3;
    F, pi := RelativeRepresentation(K);
    I1, I2 := Ideals(DivisorGroup(F)!FunctionFieldDivisor(D));
    G1 := [ RationalFunction(K!f) : f in Generators(I1)];
    G2 := [ RationalFunction(K!f) : f in Generators(I2)];
    HG1 := [ Homogenization(Evaluate(Numerator(f),[X,Y]),Z) : f in G1 ];
    HG2 := [ Homogenization(Evaluate(Numerator(f),[X,Y]),Z) : f in G2 ];
    f := DefiningEquation(C);
    J1 := ideal< R | HG1 cat [ f ] >;
    if Dimension(J1) eq 0 then J1 := ideal< R | 1 >; end if;
    J2 := ideal< R | HG2 cat [ f, R.pi[3]^Degree(Divisor(I2)) ] >;
    if Dimension(J2) eq 0 then J2 := ideal< R | 1 >; end if;
    return J1 * J2;
end intrinsic;
*****************************************************************/

//Unfortunate replacement by mch - see above
intrinsic Ideal(D::DivCrvElt) -> RngMPol
    {The ideal of coordinate functions which cuts out D.}
    require IsEffective(D):
       "Argument 1 should be an EFFECTIVE divisor";
    pls := Decomposition(D);
    I := Ideal(Curve(D));
    if #pls eq 0 then return ideal<Generic(I)|1>; end if;
    J := Ideal(pls[1][1]);
    if pls[1][2] gt 1 then
	J := I + J^(pls[1][2]);
    end if;
    
    for i in [2..#pls] do
	J := I + J*(Ideal(pls[i][1])^(pls[i][2]));
    end for;
    
    return J;
end intrinsic;

intrinsic Cluster(D::DivCrvElt) -> Clstr
    {The zero dimensional scheme cut out by D.}
    return D eq 0 select EmptyScheme(Ambient(Curve(D))) 
        else Cluster(Ambient(Curve(D)),Ideal(D));
end intrinsic;

/*************************************************
 * doesn't work for, for instance, u^4 + v^4 - w^4
 * and the place Zeros(w/v)

intrinsic Ideal(p::PlcCrvElt) -> RngMPol
    {The prime ideal of coordinate functions which vanish at p.}
    C := ProjectiveCurve(Parent(p));
    K := FunctionField(C);
    F, pi := RelativeRepresentation(K);
    R := CoordinateRing(Ambient(C));
    pp := Places(F)!FunctionFieldPlace(p);
    I1, I2 := Ideals(1*pp);
    if I2 ne ideal< MaximalOrderInfinite(F) | 1 > then
	gens := [ RationalFunction(K!f) : f in Generators(I2) ];
	W := R.pi[3]; 
    else
	gens := [ RationalFunction(K!f) : f in Generators(I1) ];
	W := R!0;
    end if;
    X := R.1; Y := R.2; Z := R.3;
    eqns := [ Homogenization(Evaluate(Numerator(f),[X,Y]),Z) : f in gens ];
    return Radical(ideal< R | eqns cat [W] >);
end intrinsic;
 *************************************************/

///replacement by Nils:
intrinsic Ideal(p::PlcCrvElt) -> RngMPol
    {The prime ideal of coordinate functions which vanish at p.}
    C:=Curve(p);
    f,g:=TwoGenerators(p);
    pi:=ProjectiveMap([f,g,1]);
    //the place we're interested in is the pullback of [0,0,1]
    //of course we have to remove the base scheme from the pullback
    Z:=Difference(Scheme(Co,[Co.1,Co.2])@@pi,BaseScheme(pi))
           where Co is Codomain(pi);
    // mch - 07/14 - its not guaranteed that the ideal of Z will
    // be saturated, so force that!
    Saturate(~Z);
    return Ideal(Z);
end intrinsic;

intrinsic Cluster(p::PlcCrvElt) -> Clstr
    {The zero dimensional prime scheme cut out by p.}
    return Cluster(Curve(p),Ideal(p));
end intrinsic;

////////////////////////////////////////////////////////////////////////
//              Zeros and Poles of Functions on a Curve               //
////////////////////////////////////////////////////////////////////////

intrinsic Zeros(C::Crv,f::RngElt) -> SeqEnum
    {A sequence containing the zeros on the curve C of the
    rational function f.}
    require IsField(BaseRing(C)) : 
        "Argument 1 must be defined over a field.";
    require f ne 0 : "Second argument must not be zero";
    F := FunctionField(C);
    coercible,f := IsCoercible(F,f);
    require coercible: "Second argument is not a function on the first";
    return Zeros(f);
end intrinsic;

intrinsic Zeros(f::FldFunFracSchElt[Crv]) -> SeqEnum
    {A sequence containing the zeros (on the curve C) of the
    rational function f.}

    require f ne 0 : "Second argument must not be zero";
    F := Parent(f);
    C := Curve(F);
    require IsField(BaseRing(C)) : 
        "Argument 1 must be defined over a field.";
    _,m := AlgorithmicFunctionField(F);
    return [CurvePlace(C, p) : p in Zeros(m(f))];
end intrinsic;

intrinsic Poles(C::Crv,f::RngElt) -> SeqEnum
    {A sequence containing the zeros on the curve C of the
    rational function f.}
    require IsField(BaseRing(C)) : 
        "Argument 1 must be defined over a field.";
    require f ne 0 : "Second argument must not be zero";
    F := FunctionField(C);
    coercible,f := IsCoercible(F,f);
    require coercible: "Second argument is not a function on the first";
    return Poles(f);
end intrinsic;

intrinsic Poles(f::FldFunFracSchElt[Crv]) -> SeqEnum
    {A sequence containing the zeros (on the curve C) of the
    rational function f.}

    require f ne 0 : "Second argument must not be zero";
    F := Parent(f);
    C := Curve(F);
    require IsField(BaseRing(C)) : 
        "Argument 1 must be defined over a field.";
    _,m := AlgorithmicFunctionField(F);
    return [CurvePlace(C, p) : p in Poles(m(f))];
end intrinsic;

////////////////////////////////////////////////////////////////////////
//              Canonical Divisors and Derived Divisors               //
////////////////////////////////////////////////////////////////////////

intrinsic CanonicalDivisor(C::Crv) -> DivCrvElt
    {A canonical divisor of C.}
    require IsField(BaseRing(C)) : "Curve must be defined over a field";
    return CurveDivisor(C,w) where w is
        CanonicalDivisor(AlgorithmicFunctionField(FunctionField(C)));
end intrinsic;

intrinsic ComplementaryDivisor(D::DivCrvElt,p::Pt) -> DivCrvElt
    {The divisor obtained from D by removing all components of the
    nonsingular point p.}
    return ComplementaryDivisor(D,Place(p));
end intrinsic;

intrinsic ComplementaryDivisor(D::DivCrvElt,p::PlcCrvElt) -> DivCrvElt
    {The divisor obtained from D by removing all components of the
     place p.}
    bool, pp := IsCoercible(Parent(D),p);
    require bool: "Arguments are not coercible into the same divisor group";
    return D - Valuation(D,p)*pp;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//           Characteristic data and recovering divisors.             //
////////////////////////////////////////////////////////////////////////

intrinsic RationalFunctions(p::PlcCrvElt) -> SeqEnum
    {A sequence of rational functions which determine the place p.}
    a, b := TwoGenerators(p);
    return [a, b];
end intrinsic;

intrinsic Place(Q::SeqEnum[FldFunFracSchElt]) -> PlcCrvElt
    {The place of a curve C determined by the sequence of elements
    of the function field of C.}
    require #Q ne 0: "Sequence must define a prime ideal and must not be empty";
    F := Universe(Q);
    assert Type(F) eq FldFunFracSch;
    FF,m := AlgorithmicFunctionField(F);
    Q := [ m(f) : f in Q ];
    Mfin := MaximalOrderFinite(FF);
    Minf := MaximalOrderInfinite(FF);
    // choose an order in which to work.
    if &and[ f in Mfin : f in Q ] then
        O := MaximalOrderFinite(FF);
    elif &and[ f in Minf : f in Q ] then
        O := MaximalOrderInfinite(FF);
    else require false:
        "Elements of argument must be contained in the " *
        "maximal finite or infinite equation order.";
    end if;
    J := ideal< O | Q >;
    require IsPrime(J) :
        "Argument does not determine a prime in the coordinate ring.";
    return CurvePlace(Curve(F),Place(J));
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                      Accessory Attributes                          //
////////////////////////////////////////////////////////////////////////

intrinsic UniformizingParameter(p::Pt) -> FldFunFracSchElt
    {Given a nonsingular point p of a curve, returns
    an element of the function field of valuation one at p.}
    bool,C := IsCurve(Scheme(p));
    require bool and IsNonsingular(C,p):
        "Argument must be a nonsingular point of a curve";
    require IsField(BaseRing(C)) :
                        "Point must be of a scheme defined over a field";
    return UniformizingParameter(Place(p));
end intrinsic;

intrinsic UniformizingParameter(p::PlcCrvElt) -> FldFunFracSchElt
    {Given a place p of a curve, returns
    an element of the function field of valuation one at p.}
    A,m := AlgorithmicFunctionField(FunctionField(Curve(p)));
    return UniformizingElement(FunctionFieldPlace(p)) @@ m;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                Existence and Represenatives Places                 //
////////////////////////////////////////////////////////////////////////

intrinsic Places(C::Crv[FldFin], m::RngIntElt) -> SeqEnum
    {A sequence of places of degree m on a curve defined over
    a finite field.}
    require m ge 1: "Argument 2 must be at least 1";
    return [ CurvePlace(C,P) : P in Places(AlgorithmicFunctionField(FunctionField(C)),m) ];
end intrinsic;

intrinsic HasPlace(C::Crv[FldFin], m::RngIntElt) -> BoolElt, PlcCrvElt
    {True and a place of degree m on the curve C defined
    over a finite field if and only if there exists such;
    false otherwise.}
    require m ge 1: "Argument 2 must be at least 1.";
    bool, p := HasPlace(AlgorithmicFunctionField(FunctionField(C)),m);
    if bool then return bool, CurvePlace(C,p); end if;
    return bool, _;
end intrinsic;

intrinsic RandomPlace(C::Crv[FldFin], m::RngIntElt) -> PlcCrvElt
    {A random place of exact degree m of the curve C over
    a finite field if one exists.}
    require m ge 1: "Argument 2 must be at least 1.";
    bool, p := HasRandomPlace(AlgorithmicFunctionField(FunctionField(C)), m);
    require bool :
        "Argument 1 has no place of degree given by argument 2.";
    return CurvePlace(C,p);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                    Degree and Valuation                            //
////////////////////////////////////////////////////////////////////////

intrinsic Degree(P::PlcCrvElt) -> RngIntElt
    {Degree of place}
    return Degree(FunctionFieldPlace(P));
end intrinsic;

intrinsic Degree(D::DivCrvElt) -> RngIntElt
    {Degree of divisor.}
    return Degree(FunctionFieldDivisor(D));
end intrinsic;

intrinsic Degree(f::FldFunFracSchElt[Crv]) -> RngIntElt
    {Degree of a rational function on a curve.}
    F := Parent(f);
    _,mp := AlgorithmicFunctionField(F);
    return Degree(mp(f));
end intrinsic;

intrinsic Valuation(D::DivCrvElt,p::Pt) -> RngIntElt
    {The coefficient in D of the nonsingular point p.}
    return Valuation(D,Place(p));
end intrinsic;

intrinsic Valuation(D::DivCrvElt,p::PlcCrvElt) -> RngIntElt
    {The coefficient in D of the place p.}
    C := Curve(p);
    require IsField(BaseRing(C)) :
                "Point must be of a scheme defined over a field";
    require Curve(D) eq C:
        "The divisor is not defined on the same curve as the point";
    return Valuation(FunctionFieldDivisor(D),FunctionFieldPlace(p));
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                  Decomposition of Divisors                         //
////////////////////////////////////////////////////////////////////////

intrinsic Divisor(Div::DivCrv,S::[Tup]) -> DivCrvElt
    {The divisor with factorisation sequence S = [<p1,e1>,<p2,e2>,..],
    where p1 are places and the e1 are their multiplcities.}
    C := Curve(Div);
    require Universe(S) eq CartesianProduct(Places(C),Integers()):
	"Elements of argument 2 must be of the form <place,integer>.";
    return Divisor(S);
end intrinsic;

intrinsic Divisor(C::Crv, S::[Tup]) -> DivCrvElt
{"} // "
    require Universe(S) eq CartesianProduct(Places(C),Integers()):
	"Elements of argument 2 must be of the form <place,integer>.";
    return Divisor(S);
end intrinsic;

intrinsic Divisor(S::[Tup]) -> DivCrvElt
    {"} // "
    U := Universe(S);
    require Type(U) eq SetCart : "Elements of the sequence must be tuples of places and exponents";
    PC := Component(U, 1);
    require Type(PC) eq PlcCrv : "Elements of the sequence must be tuples of places and exponents";
    require Component(U, 2) cmpeq Integers() : "Elements of the sequence must be tuples of places and exponents";
    return &+[ DivisorGroup(Curve(PC)) | f[2]*f[1] : f in S ];
end intrinsic;

intrinsic Decomposition(D::DivCrvElt) -> SeqEnum
    {The decomposition of the divisor D on a curve, returned 
    as a sequence of the form [<place, exponent>].};
    supp, exps := Support(D);
    return [ <supp[i],exps[i]> : i in [1..#supp] ];
end intrinsic;

intrinsic SignDecomposition(D::DivCrvElt) -> DivCrvElt,DivCrvElt
    {Two effective divisors A,B such that D = A - B.}
    return Numerator(D), Denominator(D);
end intrinsic;

intrinsic Numerator(D::DivCrvElt) -> DivCrvElt
{The numerator of D}
    return CurveDivisor(Curve(D), Numerator(FunctionFieldDivisor(D)));
end intrinsic;

intrinsic Denominator(D::DivCrvElt) -> DivCrvElt
{The denominator of D}
    return CurveDivisor(Curve(D), Denominator(FunctionFieldDivisor(D)));
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                Invariants of Places and Divisors                   //
////////////////////////////////////////////////////////////////////////

intrinsic IndexOfSpeciality(D::DivCrvElt) -> RngIntElt
    {The dimension of the space L(K_C - D).}
    return IndexOfSpeciality(FunctionFieldDivisor(D));
end intrinsic;

intrinsic Dimension(D::DivCrvElt) -> RngIntElt
{The dimension of the Riemann-Roch space of D}
    return Dimension(FunctionFieldDivisor(D));
end intrinsic;

intrinsic ShortBasis(D::DivCrvElt : Reduction := true) -> 
				SeqEnum, SeqEnum, FldFunFracSchElt
{The basis of the Riemann-Roch space of D in short form. The base function
 'x' is also returned.}
    require Type(Reduction) eq BoolElt : "Reduction parameter must be a boolean";
    A, m := AlgorithmicFunctionField(FunctionField(Curve(D)));
    S,degs := ShortBasis(FunctionFieldDivisor(D) : Reduction := Reduction);
    A1 := A;
    while IsFinite(Degree(A1)) do
	A1 := BaseField(A1);
    end while;
    return [s @@ m : s in S],degs,(A!(A1.1))@@m;
end intrinsic;

intrinsic GapNumbers(p::Pt) -> SeqEnum
    {The sequence of indices for which there are gaps in
    the dimensions of the Riemann-Roch spaces L(n*p).}
    return GapNumbers(Place(p));
end intrinsic;

intrinsic GapNumbers(p::PlcCrvElt) -> SeqEnum
    {"} // "
    C := Curve(p);
    require IsNonsingular(C,RepresentativePoint(p)) :
	"Argument must be a nonsingular point of a curve.";
    K := BaseRing(C);
    require IsField(K) : 
	"Curve of argument must be defined over a field.";
    require IsField(K) and Ring(Parent(RepresentativePoint(p))) cmpeq K : 
	"Argument must be a rational point of the curve.";
    return GapNumbers(FunctionFieldPlace(p));
end intrinsic;

intrinsic IsWeierstrassPlace(P::PlcCrvElt) -> BoolElt
    {True iff the degree 1 place P is a Weierstrass place}
    require Degree(P) eq 1: "Argument 2 must have degree 1.";
    return IsWeierstrassPlace(FunctionFieldPlace(P));
end intrinsic;

intrinsic IsWeierstrassPlace(Div::DivCrvElt,P::PlcCrvElt) -> BoolElt
    {"} // "
// THINK:  i have no idea what this description means, and i
// don't see any dependence on Div in the return value.
    require Parent(Div) eq Parent(Divisor(P)):
	"Divisor and place arguments lie on different curves";
    require Degree(P) eq 1: "Argument 2 must have degree 1.";
    return IsWeierstrassPlace(FunctionFieldPlace(P));
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                 Predicates on Divisors of Curves                   //
////////////////////////////////////////////////////////////////////////

intrinsic IsZero(D::DivCrvElt) -> BoolElt
    {True iff D is the zero divisor.}
    return IsZero(FunctionFieldDivisor(D));
end intrinsic;

intrinsic IsEffective(D::DivCrvElt) -> BoolElt
    {True iff D is effective.}
    return IsEffective(FunctionFieldDivisor(D));
end intrinsic;

/* 
//IsPositive is defined to be identical to IsEffective in bind/i.b,
//so this intrinsic is superfluous.
intrinsic IsPositive(D::DivCrvElt) -> BoolElt
    {True iff D is effective.}
    return IsPositive(FunctionFieldDivisor(D));
end intrinsic;
*/

intrinsic IsSpecial(D::DivCrvElt) -> BoolElt
    {True iff D is special.}
    return IsSpecial(FunctionFieldDivisor(D));
end intrinsic;

intrinsic IsPrincipal(D::DivCrvElt) -> BoolElt,FldFunFracSchElt
    {True iff D is a principal divisor, in which case
    also return a generator.}
    _, m := AlgorithmicFunctionField(FunctionField(Curve(D)));
    bool, f := IsPrincipal(FunctionFieldDivisor(D));
    if bool then return bool, f @@ m; end if;
    return bool, _;
end intrinsic;

// NB.  the handbook documents IsLE not AreLE --- do we know
// which to choose?
intrinsic IsLinearlyEquivalent(D::DivCrvElt,E::DivCrvElt) -> BoolElt
    {True iff D - E is a principal divisor}
    require Parent(D) eq Parent(E):
	"Arguments lie in different divisor groups";
    bool, f := IsPrincipal(D-E);
    if bool then return bool, f; end if;
    return bool, _;
end intrinsic;

intrinsic AreLinearlyEquivalent(D::DivCrvElt,E::DivCrvElt) -> BoolElt
    {True iff D - E is a principal divisor}
    require Parent(D) eq Parent(E):
	"Arguments lie in different divisor groups";
    bool, f := IsPrincipal(D-E);
    if bool then return bool, f; end if;
    return bool, _;
end intrinsic;

intrinsic IsHypersurfaceDivisor(D::DivCrvElt) -> BoolElt, RngElt, RngIntElt
{ True iff effective divisor D is scheme theoretically the intersection 
of the (ordinary projective) curve C with a hypersurface. If so, returns
the equation of the hypersurface and its degree d}

    C := Curve(D);
    require IsOrdinaryProjective(C):
      "Function only for divisors on ordinary projective curves";
    if not IsEffective(D) then return false,_,_; end if;
    dC := Degree(C);
    dD := Degree(D);
    boo, d := IsDivisibleBy(dD,dC);
    if not boo then return false,_,_; end if;
    R := CoordinateRing(Ambient(C));
    n := Rank(R);
    // choose a coordinate function not vanishing on C
    i := n+1-FFPatchIndex(C);
    // if D0 = d*Divisor(xi) then D-D0 = (Q/xi^d) for
    //  Q of degree d
    D0 := d*Divisor(C,ideal<R|R.i>);
    boo,f := IsPrincipal(D-D0);
    if not boo then return false,_,_; end if;
    // must express f as Q/xi^d
    mons := Setseq(MonomialsOfDegree(R,d));
    K := FunctionField(C); F,fmp := AlgorithmicFunctionField(K);
    fs := [fmp(K!(R.j/R.i)) : j in [1..n]];
    fpows := [Evaluate(m,fs) :  m in mons];
    rels := Relations(fpows cat [-fmp(f)],BaseRing(R));
    N := #fpows+1;
    B := [b : b in Basis(rels) | b[N] ne 0];
    assert #B gt 0;
    Q := Polynomial(Eltseq(b)[1..N-1],mons)/b[N] where
		b is B[1];
    return true,Q,d;

end intrinsic;   
    
//////////////////////////////////////////////////////////////////////////////
//				Reduction				    //
//////////////////////////////////////////////////////////////////////////////

intrinsic Reduction(D::DivCrvElt) -> DivCrvElt,RngIntElt,DivCrvElt,FldFunFracSchElt
{Reduction of the divisor D on a curve}
    C := Curve(D);
    a,b,c,d := Reduction(FunctionFieldDivisor(D));
    _,m := AlgorithmicFunctionField(FunctionField(C));
    return CurveDivisor(C, a), b, CurveDivisor(C, c), d @@ m;
end intrinsic;

intrinsic Reduction(D::DivCrvElt,A::DivCrvElt)
                -> DivCrvElt,RngIntElt,DivCrvElt,FldFunFracSchElt
{Reduction of the divisor D on a curve by divisor A}
    C := Curve(D);
    a,b,c,d := Reduction(FunctionFieldDivisor(D),FunctionFieldDivisor(A));
    _,m := AlgorithmicFunctionField(FunctionField(C));
    return CurveDivisor(C, a), b, CurveDivisor(C, c), d @@ m;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//			GCD/LCM						    //
//////////////////////////////////////////////////////////////////////////////

intrinsic GCD(D1::DivCrvElt,D2::DivCrvElt) -> DivCrvElt
{The greatest common divisor of divisors D1 and D2 on a curve}
    require Parent(D2) cmpeq Parent(D1):
        "Divisor arguments must lie in the same divisor group";
    C := Curve(D1);
    return CurveDivisor(C, GCD(FunctionFieldDivisor(D1),FunctionFieldDivisor(D2)));
end intrinsic;

intrinsic LCM(D1::DivCrvElt,D2::DivCrvElt) -> DivCrvElt
{The least common multiple of divisors D1 and D2 on a curve}
    require Parent(D2) cmpeq Parent(D1):
        "Divisor arguments must lie in the same divisor group";
    C := Curve(D1);
    return CurveDivisor(C, LCM(FunctionFieldDivisor(D1),FunctionFieldDivisor(D2)));
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//			    Residue Class Field				    //
//////////////////////////////////////////////////////////////////////////////

intrinsic ResidueClassField(P::PlcCrvElt) -> Rng
{The residue class field of the place P on a curve}
    return ResidueClassField(FunctionFieldPlace(P));
end intrinsic;

intrinsic Lift(x::RngElt,P::PlcCrvElt) -> FldFunFracSchElt
{Lift the element x of the residue class field of the place P on a curve
 to an algebraic function}
    _,m := AlgorithmicFunctionField(FunctionField(Curve(P)));
    return Lift(x,FunctionFieldPlace(P)) @@ m;
end intrinsic;

intrinsic Lift(i::Infty,P::PlcCrvElt) -> FldFunFracSchElt
{Lift i = infinity in the residue class field of the place P on a curve
to an algebraic function}
    _,m := AlgorithmicFunctionField(FunctionField(Curve(P)));
    return Lift(i,FunctionFieldPlace(P)) @@ m;
end intrinsic;

