freeze;
/////////////////////////////////////////////////////////////////////////////////
///  General functions to test whether an isolated hypersurface singularity   ///
///    occurs in Arnold's classification list, determine the precise family   ///
///     and normal form and compute an explicit transformation to that        ///
///      normal form. The functions to deal with the corank 2 and 3           ///
///       cases are in other files.   mch - 11/13                             ///
///////////////////////////////////////////////////////////////////////////////// 

declare attributes RngInt: LocSingTrans;
   // 'global' variable used for passing a transformation around in certain contexts.

// Formal data record for a hypersurface singularity at the origin which expands to
// a powerseries with non-trivial quadratic part. The hypersurface might be 
// defined by an exact polynomial or an HSSData structure F. This is used to
// expand to given degree the transformed isomorphic powerseries of the form
// a1*x1^2+..ar*xr^2+f(x_(r+1),..xn). The transformation to this form up
// to some smaller degree (>=2) is stored in the 'global var' LocSingTrans.
// LocSingTrans is replaced by the new value at the end of further expansion.
HSSQuadData := recformat<
   F	 : Any  // either a polynomial in n vars defining exactly the
		// hypersurface or an HSSData to give the expansion
>;

function transform_deg2(F)
// Transforms the degree 2 part of F (in k[x1,..,xn]) to a1*x1^2+..ar*xr^2
// by linear substitution l. Returns the transform of F by l,r and l.
// Assumed that Char(k) != 2 and that all terms of F are of deg >= 2.
   
    R := Generic(Parent(F));
    n := Rank(R);
    f := &+[t : t in Terms(F) | LeadingTotalDegree(t) eq 2];
    if f eq 0 then // mult >= 3
	return F,0,[R.i : i in [1..n]];
    end if;
    f1,mat := DiagonalForm(f);
    r := #Terms(f1);
    inds := [i : i in [1..n]| MonomialCoefficient(f1,R.i^2) ne 0];
    assert #inds eq r;
    if Max(inds) gt r then
	js := inds cat [i : i in [1..n]|i notin inds];
	jsinv := [Index(js,i) : i in [1..n]];
	mat := PermutationMatrix(BaseRing(R),js)*mat;
    end if;
    subs := Eltseq(Vector([R.i : i in [1..n]])*ChangeRing(mat,R));
    F := Evaluate(F,subs);
    return F,r,subs;

end function;

function trunc_comp(s,t,d)
// s and t are sequences of multidegree polys (over the same base field)
//  with #t = # of variables of the s polys. Compute the composition
//  [Evaluate(e,t) : e in s] but truncating the resulting polys to degree <= d

    // first truncate the polys in s
    P := Universe(s);
    s1 := [&+[P|e : e in Terms(f) | LeadingTotalDegree(e) le d] : f in s];
    if &and[IsZero(f) : f in s1] then return s1; end if;
    // now work in P mod m^(d+1) where P is the poly ring of t
    //  and m is the maximal ideal
    P := Generic(Universe(t));
    P1 := quo<P|Setseq(MonomialsOfDegree(P,d+1))>;
    res := [P!(Evaluate(f,t1)) : f in s1] where t1 is [P1!e : e in t];
    return res;
    
end function;

function wtd_trunc_comp(s,t,d)
// as above except the trucation to to weighted degree <= d and
// s and t conatin polys in the same graded polynomial ring.

    // first truncate the polys in s
    P := Universe(s);
    s1 := [&+[P|e : e in Terms(f) | WeightedDegree(e) le d] : f in s];
    if &and[IsZero(f) : f in s1] then return s1; end if;
    // now work in P mod m_d where P is the poly ring of t
    //  and m_d is the monomial ideal containing all monomials
    //  of weighted degree > d
    P := Generic(Universe(t));
    grads := Grading(P);
    B := GroebnerBasis(ideal<P|&cat[Setseq(MonomialsOfWeightedDegree(P,d+i)):
		i in [1..Max(Grading(P))]]>);
    P1 := quo<P|B>;
    res := [P!(Evaluate(f,t1)) : f in s1] where t1 is [P1!e : e in t];
    return res;
    
end function;

function complete_squares(F,r,d,get_trans)
// F is a multivariate polynomial in k[x1,..,xn] with lowest degree part
// a1*x1^2+..+ar*xr^2 where 0 <= r <= n (r=0 <=> all terms of F have deg >= 3).
// It is assumed that Char(k) != 2.
// Function transforms F by xi -> xi+O(deg >= 2) substitutions (1 <= i <= r)
// into the form G = a1*x1^2+..+ar*xr^2 + f(x_(r+1),..,xn) + O(deg >= d+1)
// where f is a polynomial only in the last n-r terms (f=0 if r=n) with all
// terms of degree at least 3. Returns G and, if get_trans is true, the
// substitutions giving the transformation (up to precision d-1).
 
    R := Generic(Parent(F));
    n := Rank(R);
    subs := [R.i : i in [1..r]];
    trunc := func<f | Polynomial([LeadingCoefficient(t) : t in T],
	[LeadingMonomial(t) : t in T]) where T is
	  [t : t in Terms(f) | LeadingTotalDegree(t) le d]>;
    for i in [1..r] do
	a := MonomialCoefficient(F,R.i^2);
	assert a ne 0;
	cs := Coefficients(F-a*(R.i)^2,i);
	while #cs gt 1 do
	    if cs[2] ne 0 then
	      //a) R.i*m terms where m is a monomial not divisible by R.i.
	      //  Simple square completion used here.
	      subs1 := [R.j : j in [1..n]];
	      subs1[i] -:= (1/(2*a))*cs[2];
	    else
	      //b) R.i part is R.i^2(a+g) where g has no constant term
	      //  Simple square completion used here also.
	      g := &+[cs[j+3]*(R.i)^j : j in [0..#cs-3]];
	      subs1 := [R.j : j in [1..n]];
	      subs1[i] *:= (1-(1/(2*a))*g);
	    end if;
	    F := trunc_comp([F],subs1,d)[1];
	    if get_trans then subs := trunc_comp(subs,subs1,d-1); end if;
	    cs := Coefficients(F-a*(R.i)^2,i);
	end while;
    end for;
    return F,subs cat [R.i : i in [r+1..n]];
    
end function;

function expand_to_prec_with_quadratic_part(fdat,d,R)
// General purpose function to further expand to a precision d power series
// a polynomial defined by the data in the record fdat. The result will be
// return as an element in multivariate polynomial ring R.
//
// fdat can be a record of two types:
// 1) HSSData as defined in Geometry/Sch/singularity.m. Here it is simply
//  a case of calling HypersurfaceSingularityExpandFurther.
// 2) HSSQuadData. Here we have a hypersurface defined by
//  a polynomial or an HSSData whose singularity has a non-zero quadratic part.
//  We must expand to prec d and complete squares up to that precision to
//  give an expansion of the form a1*x1^2+..ar*xr^2+f(x_(r+1),..xn) where
//  the f is a polynomial only in the last n-r vars (with all terms of degree
//  at least 3). Here f is returned. Z`LocSingTrans gives the transformation
//  to the required form to a lower precision (>= 2) and it's value is replaced
//  by the new transformation to the higher precision at the end.

    nf := #Names(Format(fdat));
    if nf gt 1 then //fdat is HSSData
	return HypersurfaceSingularityExpandFurther(fdat,d,R);
    end if;
    //fdat should now be HSSQuadData
    assert nf eq 1;
    fd := fdat`F;
    Z := Integers();
    s1 := Z`LocSingTrans;
    R1 := Universe(s1);
    booRec := Type(fd) cmpeq Rec;
    if booRec then
	F := HypersurfaceSingularityExpandFurther(fd,d,R1);
    else
	assert (Type(fd) cmpeq RngMPol) and (Parent(fd) cmpeq R1);
	F := fd;
    end if;
    F := trunc_comp([F],s1,d)[1]; //apply current transformation
    r := #[0 : t in Terms(F) | LeadingTotalDegree(t) eq 2];
    assert &and[not IsZero(MonomialCoefficient(F,(R1.i)^2)) : i in [1..r]];
    // do transformation to prec d
    F,s2 := complete_squares(F,r,d,true);
    Z`LocSingTrans := trunc_comp(s1,s2,d-1);
    n := Rank(R1);
    assert Rank(R) eq n-r;
    F := Evaluate(F,[R!0: i in [1..r]] cat [R.i : i in [1..n-r]]);
    return F;

end function;

/*     Other potentially useful functions - not currently used
function initial_reduction(F,d)
// F should be a hypersurface equation with a singularity at the origin
// and correct up to terms of order degree d+1. Converts F to the standard
// a1*x1^2+..+ar*xr^2+f(x_(r+1),..,x_n) form mod O(deg d+1) and returns
// the result along with the x_1,..x_n substitutions for the transformation.

   F1,r,s1 := transform_deg2(F);
   if r eq 0 then return F,s1; end if;
   F2,s2 := complete_squares(F1,r,d,true);
   subs := [Evaluate(s,s2 cat seq) : s in s1] where
	seq is [R|R.i : i in [r+1..Rank(R)]] where R is Generic(Parent(F));
   return F2,subs;

end function;

function polytope_F(F)
// The convex hull of the monomial indices with non-zero coefficient in
//  multivariate polynomial F.
   return Polytope([Exponents(t) : t in Terms(F)]);
end function;

function quasi_hom_types(P)
// P is the polytope of a multivar poly F in n (>= 2) vars which has a singularity
//  at the origin of multiplicity at least 3.
// Return types (a1,..,an) with ai > 0 integers defining a quasihomogeneous part
//  of F of degree d <-> a facet of P such that the remaining part of F has degree
//  > d w.r.t. the type.

    n := Dimension(P);
    vs := Vertices(P);
    r := #Eltseq(vs[1]);
    assert r le n+1;
    if r eq n+1 then //F is quasi-homogeneous
	fs := Faces(P,n); //just get full P
	n := r;
    else
        fs := Faces(P,n-1);
    end if;
    typs := [**];
    for f in fs do
	vsf := Vertices(f);
	mat := Matrix([Eltseq(v) : v in vsf]);
	mat := ChangeRing(mat,Rationals());
	mat := HorizontalJoin(mat,
		Matrix(Nrows(mat),1,[Rationals()!1 : i in [1..Nrows(mat)]]));
	K := Kernel(Transpose(mat));
	assert Dimension(K) eq 1;
	vec := Eltseq(Basis(K)[1]);
	if vec[n+1] eq 0 then continue; end if;
	l := LCM([Denominator(e) : e in vec]);
	vec := [l*v : v in vec];
	if vec[n+1] gt 0 then vec := [-e : e in vec]; end if;
	if &or[vec[i] le 0 : i in [1..n]] then continue; end if;
	d := -vec[n+1];
	vec := vec[1..n];
	j := 1;
	while vs[j] in vsf do; j +:= 1; end while;
	p := Eltseq(vs[j]);
	if &+[p[i]*vec[i] : i in [1..n]] lt d then continue; end if;
	Append(~typs,<vec,d>);
    end for;
    return typs;

end function;

function semi_quasi_decomps(F)

    R := Generic(Parent(F)); k := BaseRing(R);
    P := Polytope([Exponents(t) : t in Terms(F)]);
    typs := quasi_hom_types(P);
    good_typ := [**];
    for t in typs do
	as := t[1]; d := t[2];
	Rw := PolynomialRing(k,ChangeUniverse(as,Integers()));
	F1 := Polynomial(Coefficients(F),
		[Monomial(Rw,Exponents(m)) : m in Monomials(F)]);
	TFd := [t : t in Terms(F1) |  WeightedDegree(t) le d];
	Fd := Polynomial([LeadingCoefficient(t) : t in TFd],
		[Monomial(R,Exponents(LeadingMonomial(t))) : t in TFd]);
	if Type(MilnorNumber(Fd)) ne Infty then //Fd is non-degenerate
	   Append(~good_typ,<Fd,as,d>); 
	end if;	
    end for;
    return good_typ;

end function;

function get_Lie_Algebra(f)

    R := Generic(Parent(f));
    K := BaseRing(R);
    ws := VariableWeights(R);
    // construct the abstract Lie algebra on basis B
    B := [<m,i> : m in MonomialsOfWeightedDegree(R,ws[i]), i in [1..Rank(R)]];
    b := #B;
    V := VectorSpace(K,b);
    cL := [s : i in [1..b^2]] where s is [K!0 : j in [1..b]];
    for i in [1..b], j in [i+1..b] do
      seq := Eltseq(
        &+[V| LeadingCoefficient(t)*BasisElement(V,Index(B,<LeadingMonomial(t),(B[j])[2]>))
          :  t in Terms(((B[i])[1])*Derivative((B[j])[1],(B[i])[2]))] -
	&+[V| LeadingCoefficient(t)*BasisElement(V,Index(B,<LeadingMonomial(t),(B[i])[2]>))
          :  t in Terms(((B[j])[1])*Derivative((B[i])[1],(B[j])[2]))] );
      cL[(i-1)*b+j] := seq;
      cL[(j-1)*b+i] := [-s : s in seq];
    end for;
    L := LieAlgebra<K,b|cL>;
    return L,B;

end function;

function get_support(R,d)

    mons := Setseq(MonomialsOfWeightedDegree(R,d));
    pts := [Exponents(m) : m in mons];
    pol := Polytope(pts);
    return pts,pol;

end function;

function get_invts(f)
// P=0 is an isolated singular point of hypersurface f. Returns a sequence of invariants
//  of singularity P: corank, degree, multiplicity, inner modality
    R := Generic(Parent(f));
    n := Rank(R);
    d := Min([LeadingTotalDegree(t) : t in Terms(f)]);
    error if d lt 2, "0 is not a singular point";
    mult := MilnorNumber(f);
    error if Type(mult) eq Infty, "0 not an isolated singularity";
    if mult eq 1 then //A1 sing
	assert d eq 2;
	return [0,2,1,0];
    end if;

    // try to get inner modality    
    f1,r,_ := transform_deg2(f);
    cork := n-r;
    assert cork gt 0; //not A1 sing
    
end function;
*/

/// Functions to transform a semiquasihomogeneous form (in Arnold's terminology) //
//          into normal form up to required precision                           ///

function term_transform(f,seq)
// used by the function below when the Groebner normal form
// polynomials need to be transformed to get Arnold normal form polys.
//
// seq should be a sequence of pairs [m,p] where m is a monomial and p a poly in R:
// the transformation is that a term t -> (t/m)*p if t is divisible by m.

    cs := Coefficients(f);
    ms := Monomials(f);
    boo := true; //no change
    ms1 := [];
    for m in ms do
      p := m;
      for s in seq do
	b,m1 := IsDivisibleBy(m,s[1]);
	if b then
	  p := m1*s[2];
	  if boo then boo := false; end if;
	  break;
	end if;
      end for;
      Append(~ms1,p);	
    end for;
    if boo then 
	return f;
    else
	return &+[cs[i]*ms1[i] : i in [1..#cs]];
    end if;
    
end function;

function qh_transform_to_normal_form(F,f0,deg : groebner_shift := [], get_trans := true,
		ord_deg := 0)
// the polynomial ring R containing F here should have the correct weighting
// for which f0 is the minimal degree non-degenerate homogeneous part of F
// (so F is semiquasihomogeneous with quasihomogeneous part f0 in Arnold's terminology).
//
// groebner_shift can used be transform the monomials that occur in NormalForm
// w.r.t. the Groebner ordering of R to ones that occur in Arnold's normal forms.
// It should have the format described for argument seq of the previous function.
//
// If ord_deg > 0 then everything is also truncated to terms of ordinary degree
// <= ord_deg, so the transformation and normal form are only computed up to
// (ordinary) degree ord_deg.

    R := Generic(Parent(F)); k := BaseRing(R);
    n := Rank(R);
    ws := VariableWeights(R);
    trans := [R.i : i in [1..n]];

    assert IsHomogeneous(f0);
    d := WeightedDegree(f0);
    assert deg ge d;
    if deg eq d then return f0,trans; end if;

    if ord_deg gt 0 then 
      trunc_to_deg := func<f,e|&+[R|t : t in Terms(f) | 
	(LeadingTotalDegree(t) le ord_deg) and (WeightedDegree(t) lt e)]>;
    else
      trunc_to_deg := func<f,e|&+[R|t : t in Terms(f) | 
				WeightedDegree(t) lt e]>;
    end if;

    Fcurr := trunc_to_deg(F,deg+1);
    f2 := Fcurr-f0;
    if IsZero(f2) then return f0,trans; end if;
    d2 := Min([WeightedDegree(t): t in Terms(f2)]);
    assert d2 gt d;
    if d2 gt deg then return R!0,trans; end if;
    dfs := [Derivative(f0,i) : i in [1..n]];
    Idf := IdealWithFixedBasis(dfs);
    

    f1 := NormalForm(f2,Idf);
    if f1 ne R!0 then
	if #groebner_shift gt 0 then
	  f1 := term_transform(f1,groebner_shift);
	end if;
        d1 := Min([WeightedDegree(t): t in Terms(f1)]);
    else
	d1 := deg+1;
    end if;

    if true then
      f2 := f2-f1;
      d2 := d;
 
      while f2 ne R!0 do
	d2n := Min([WeightedDegree(t): t in Terms(f2)]);
	assert d2n gt d2;
	d2 := d2n;
	if d2 gt deg then break; end if;
	//delta := d2-d;
	vs := Coordinates(Idf,f2);
	dv := Min([(IsZero(vs[i]) select deg+1+ws[i] else 
		Min([WeightedDegree(t): t in Terms(vs[i])]))-ws[i]:
			i in [1..n]]);
	assert 2*dv gt d2-d;
	err_d := Min([d+2*dv,d1+dv,d2+dv,deg+1]);
	vs := [trunc_to_deg(vs[i],err_d-d+ws[i]) : i in [1..n]];
	vec := [R.i-vs[i]: i in [1..n]];
	Fcurr := wtd_trunc_comp([Fcurr],vec,deg)[1];
	if ord_deg gt 0 then Fcurr := trunc_to_deg(Fcurr, deg+1); end if;
	if get_trans then
	  trans := [wtd_trunc_comp([trans[i]],vec,deg+ws[i]-d)[1] : i in [1..n]];
	end if;
	f1 := NormalForm(Fcurr-f0,Idf);
	if f1 ne R!0 then
	  if #groebner_shift gt 0 then
	    f1 := term_transform(f1,groebner_shift);
	  end if;
          d1 := Min([WeightedDegree(t): t in Terms(f1)]);
	else
	  d1 := deg+1;
	end if;
	f2 := Fcurr-f0-f1;
      end while;
    end if;

    return f0+f1,trans;

end function;

///////////////////////////////////////////////////////////

function do_ns_case(f,d)
// when f is non-zero and non-singular at 0, return susbstitution that
// takes f to x up to precision d >= 1

    R := Generic(Parent(f));
    n := Rank(R);
    l := &+[t : t in Terms(f) | LeadingTotalDegree(t) eq 1];
    assert not IsZero(l);
    if l eq R.1 then 
	subs1 := [R.i : i in [1..n]];
	f1 := f;
    else
        r := [MonomialCoefficient(l,R.i) : i in [1..n]];
        i := 1;
        while IsZero(MonomialCoefficient(l,R.i)) do i := i+1; end while;
        mat := IdentityMatrix(BaseRing(R),n);
	RemoveRow(~mat,i);
	mat := VerticalJoin(Matrix(1,n,r),mat);
	mat := mat^(-1);
	subs1 := [Polynomial(rw,seq) : rw in RowSequence(mat)] where
			seq is [R.j : j in [1..n]];
	f1 := Evaluate(f,subs1);
    end if;
    subs2 := [R.i : i in [1..n]];
    seq := [R|R.i : i in [2..n]];
    while f1 ne R.1 do
	subsn := [2*R.1-f1] cat seq;
	subs2 := trunc_comp(subs2,subsn,d);
	f1 := trunc_comp([f1],subsn,d)[1];
    end while;
    subs := [Evaluate(s,subs2) : s in subs1];
    return subs;

end function;

intrinsic NormalFormOfHypersurfaceSingularity(f::RngMPolElt : get_trans := false, d := 0,
	fData := [**], milnor_number := -1) -> BoolElt, RngMPolElt, MonStgElt, Map
{ The first argument f should be a multivariate polynomial defining an affine hypersurface
  with an isolated singularity, s, at the origin (0,0,..,0,0). Returns whether s occurs in Arnold's
  classification of isolated hypersurface singularities. If so, also returns Arnold's normal
  form for s and a string giving the name of the family in which s lies (e.g. "Y^1_{3,2\}").
  If parameter get_trans is set to true (default: false), a polynomial map giving an
  explicit transformation from f to the normal form up to a certain precision is also
  returned as a final value. The precision is the smallest required to uniquely determine the normal
  form unless integer parameter d (default:0) is positive. In that case, the transformation
  precision is such that it takes f to the normal form up to polynomial terms of degree at least d+1.
  The (analytic) hypersurface may be defined by a power series F with F=f+terms of degree fdeg+1 or
  higher. In that case, parameter fData should be used as described in the Handbook to give fdeg and
  a data structure that allows F to be expanded to higher precision if necessary.}

// NOTE: fData (when not 0) should be a list pair containing [* fdata, dmax *] where dmax
//  is the degree to which f has been expanded.

    R := Generic(Parent(f));
    n := Rank(R);
    K := BaseRing(R);
    require (not IsZero(f)) and IsField(K) : "Argument f must be a non-zero polynomial defined over a field";
    d1 :=  Min([LeadingTotalDegree(t) : t in Terms(f)]);
    require d1 ge 1: "Argument f must be 0 at the origin";

    require (Type(fData) cmpeq List) and ((#fData eq 0) or ((#fData eq 2) and
	((Type(fData[1]) cmpeq Rec) and (Type(fData[2]) cmpeq RngIntElt)))) :
	"Parameter fData is not valid";
    boofd := (#fData gt 0);
    if boofd then
	fdeg := fData[2];
	fdat := fData[1];
	if (fdeg lt 2) or (fdeg lt d) then
	  f := HypersurfaceSingularityExpandFurther(fdat,Max(2,d),R);
	  fdeg := Max(2,d);
        end if;
    end if;

    if d1 eq 1 then //non-singular
	if not get_trans then return true,R.1,"A0"; end if;
	mpeqns := do_ns_case(f,Max(d,1));
	return true,R.1,"A0",hom<R->R|mpeqns>;
    end if;
    p := Characteristic(K);
    boo2 := (d1 eq 2);
    // below, crk = corank!
    if boo2 then
	require p ne 2: 
	    "Cannot deal with this singularity in characteristic 2";
        F,rk,subs := transform_deg2(f);
    else
	F := f; rk := 0; subs := [R.i : i in [1..n]];
    end if;
    crk := n-rk;
    if crk ge 5 then return false,_,_,_,_; end if;
    if crk eq 0 then //A1 case
	assert boo2;
	if get_trans then
	    if d ge 3 then
		_,s1 := complete_squares(F,n,d,true);
		subs := trunc_comp(subs,s1,d-1);
	    end if;
	    return true,F,"A1",hom<R->R|subs>;
	else
	    return true,F,"A1";
	end if;
    end if;
    if crk eq 4 then //only the non-degenerate cubic case occurs here
	// Maybe should transform the cubic part to standard form.
	//  For the moment, don't bother!
	if d1 ge 4 then return false,_,_,_; end if;
	d1 := get_trans select Max(d,4) else 4;
	if boofd and (fdeg lt d1) then
	  f := HypersurfaceSingularityExpandFurther(fdat,d1,R);
	  F := boo2 select Evaluate(f,subs) else f;
	end if;
	if boo2 then // first get to precision 4
	  F1,s1 := complete_squares(F,n-4,4,get_trans);
	  if get_trans then 
	    F := trunc_comp([F],s1,d1);
	    subs := [Evaluate(s,s1) : s in subs];
	  end if;
	else
	  F1 := F;
	end if;
	R1 := PolynomialRing(K,4,"grevlex");
	f3 := (#seq eq 0) select R1!0 else Polynomial([e[1] : e in seq],[e[2] : e in seq])
	  where seq is [<MonomialCoefficient(t),Monomial(R1,Exponents(t)[n-3..n])> :
	  t in Terms(F1) | LeadingTotalDegree(t) eq 3];
	if IsZero(f3) or IsSingular(Scheme(Proj(R1),f3)) then
	  return false,_,_,_;	  
	else
	  F0 := R!0;
	  if boo2 then
	    F0 := &+[t : t in Terms(F1) | LeadingTotalDegree(t) eq 2];
	    F1,s1 := complete_squares(F1,n-4,d1,true);
	    subs :=  trunc_comp(subs,s1,d1-1);
	  end if;
	  F1,s1 := qh_transform_to_normal_form(Evaluate(F1,[R1!0 : i in [1..n-4]] cat
			[R1.i : i in [1..4]]),f3,d1,get_trans);
	  hm := hom<R1->R | [R.i : i in [n-3..n]]>;
	  if get_trans then
	    subs := trunc_comp(subs,[R|R.i : i in [1..n-4]] cat [hm(s) : s in s1],
	    d1-(boo2 select 1 else 2));
	  end if;
	  F1 := hm(F1)+F0;
	end if;
	if get_trans then
	  return true,F1,"O16",hom<R->R|subs>;
	else
	  return true, F1,"O16";
	end if;
    elif (crk eq 2) or (crk eq 3) then
	if milnor_number ge 0 then
	  mu := milnor_number;
	else
	  mu := boofd select MilnorNumberAnalyticHypersurface(fdat) else MilnorNumber(f);
	end if;
	assert mu gt ((crk eq 2) select 3 else 7);
	if Type(mu) cmpeq Infty then return false,_,_,_; end if;
	if boo2 then
	    Z := Integers();
	    prec := Max([6,(2*mu) div 3,d]);
	    if boofd and (fdeg lt prec) then
		f := HypersurfaceSingularityExpandFurther(fdat,prec,R);
		F := boo2 select Evaluate(f,subs) else f;
	    end if;
	    F,s1 := complete_squares(F,n-crk,prec,true);
	    subs := [Evaluate(s,s1) : s in subs];
	    Z`LocSingTrans := subs;
	    fd1 := boofd select fdat else rec<HSSQuadData | F := F>;
	    fd := [* fd1, prec *];
	    F2 := &+[t : t in Terms(F) | LeadingTotalDegree(t) eq 2];
	    R1 := PolynomialRing(K,crk);
	    F := Polynomial(Coefficients(G),
			[Monomial(R1,Exponents(t)[n-crk+1..n]) : t in Monomials(G)])
		where G is F-F2;
	elif boofd then
	    fd := [* fdat,fdeg *];
	else
	    fd := [**];
	end if;
	try
	   if get_trans then
	      if crk eq 2 then
		boo,F,typ,mp :=  Corank2Case(F: d := d, milnor_number := mu,
                                fData := fd, get_trans := true);
	      else
		boo,F,typ,mp :=  Corank3Case(F: d := d, milnor_number := mu,
                          	fData := fd, get_trans := true);
	      end if;
	    else
	      if crk eq 2 then
		boo,F,typ := Corank2Case(F: d := d, milnor_number := mu, fData := fd);
	      else
		boo,F,typ := Corank3Case(F: d := d, milnor_number := mu, fData := fd);
	      end if;
	    end if;
	catch e
	   Z := Integers();
	   if boo2 and (assigned Z`LocSingTrans) then
		delete Z`LocSingTrans;
	   end if;
	   error e;
	end try;
	if not boo then return false,_,_,_,_; end if;
	seq := [0 : i in [1..n-crk]];
	if boo2 then
	   F1 := F2+Polynomial(Coefficients(F),
		[Monomial(R,seq cat Exponents(t)) : t in Monomials(F)]);
	else
	   F1 := F;
	end if;
	if not get_trans then return boo,F1,typ; end if;
	if boo2 then
	    Z := Integers();
	    subs := Z`LocSingTrans;
	    K1 := BaseRing(Codomain(mp));
	    if IsIdentical(K,K1) then
		R2 := R;
	    else
		R2 := ChangeRing(R,K1); subs := [R2!e : e in subs];
	    end if;
	    s1 := [R2.i : i in [1..n-crk]] cat [Polynomial(Coefficients(G),
		[Monomial(R2,seq cat Exponents(t)) : t in Monomials(G)])
			where G is mp(R1.i) : i in [1..crk]];
	    // find precision for final map - rather unsatisfactory!
	    d0 := Min([LeadingTotalDegree(t) : t in Terms(F)]);
	    d1 := Max([LeadingTotalDegree(t) : t in Terms(F)]);
	    d2 := Max([Max([LeadingTotalDegree(t) : t in Terms(e)]) : e in s1]);
	    d3 := Max([Max([LeadingTotalDegree(t) : t in Terms(e)]) : e in subs]);
	    prec := Max([d,d1,d2+d0-1,d3+1]);
	    subs := trunc_comp(subs,s1,prec-1);
	    delete Z`LocSingTrans;
	    mp := hom<R->R2|subs>;
	end if;
	return boo,F1,typ,mp;	
    else //crk = 1 - Ar - r >= 2
	assert boo2 or (n eq 1);
        if milnor_number ge 0 then
          mu := milnor_number;
        else
	  mu := boofd select MilnorNumberAnalyticHypersurface(fdat) else MilnorNumber(f);
	end if;
	assert mu gt 1;
	if Type(mu) cmpeq Infty then return false,_,_,_; end if;
	d1 := get_trans select Max(d,mu+1) else mu+1;
	if boofd  and (fdeg lt d1) then
	  f := HypersurfaceSingularityExpandFurther(fdat,d1,R);
	  F := Evaluate(f,subs);
	end if;
	typstr := "A" cat IntegerToString(mu);
	if n gt 1 then
	  F,s1 := complete_squares(F,n-1,d1,get_trans);
	  if get_trans then subs := trunc_comp(subs,s1,d1-1); end if;
	end if;
	a := MonomialCoefficient(F,(R.n)^(mu+1));
	error if IsZero(a) or
		(not &and[IsZero(MonomialCoefficient(F,(R.n)^i)) : i in [2..mu]]),
	  "Bad " cat typstr cat "-like singularity in characteristic "
		cat IntegerToString(p);
	if not get_trans then return true,F,typstr; end if;
	if d1 gt mu+1 then
	  R1 := PolynomialRing(K,1);
	  F1 := &+[R|MonomialCoefficient(F,(R.i)^2)*(R.i)^2 : i in [1..n-1]];
	  fn := &+[R1|MonomialCoefficient(F,(R.n)^i)*(R1.1)^i : i in [mu+1..d1]];
	  F := F1+a*(R.n)^(mu+1);
	  _,tr1 := qh_transform_to_normal_form(fn,a*(R1.1)^(mu+1),d1);
	  subs := trunc_comp(subs,[Evaluate(e,[R.n]) : e in tr1],d1-1);
	end if;
	return true,F,typstr,hom<R->R|subs>;
    end if;

end intrinsic;
