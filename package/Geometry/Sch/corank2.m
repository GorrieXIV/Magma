freeze;

///////////////////////////////////////////////////////////////////////
///  Functions to deal with the classification and transformation   ///
///      to normal form (according to Arnold's scheme) of           ///
///        Corank 2 isolated hypersurface singularities.            ///
///                    mch - 11/13                                  ///
///////////////////////////////////////////////////////////////////////

import "norm_form_of_sing.m": qh_transform_to_normal_form, trunc_comp,
		expand_to_prec_with_quadratic_part;

function number_distinct_roots(f,d)

    if d gt Degree(f) then
	return 1+number_distinct_roots(f,Degree(f));
    end if;
    if d eq 0 then return 0; end if;
    
end function;

function normalise_deg_3_homog_poly(f)

    R := Generic(Parent(f)); k := BaseRing(R);
    x := R.1; y := R.2;
    P := PolynomialRing(k); t := P.1;
    pol := Evaluate(f,[t,1]);
    my := 3-Degree(pol);
    mx := Valuation(pol);
    if mx gt 0 then pol := pol div t^mx; end if;
    lc := LeadingCoefficient(pol);
    fact := Factorisation(pol);
    fs := [[fac : fac in fact | Degree(fac[1]) eq i] : i in [1..3]];

    if (#fs[3] ne 0) or (#fs[2] ne 0) then
      if #fs[3] ne 0 then
	// f irreducible - base change to get a root
	K<a> := ext<k|fs[3][1][1]>;
	R1 := ChangeRing(R,K); x := R1.1; y := R1.2;
	tr := [y+a*x,x];
	f := R1!f;
      elif #fs[2] ne 0 then 
	if #fs[1] ne 0 then
	  a := Coefficient(fs[1][1][1],0);
	  tr := [y-a*x,x];
	elif mx gt 0 then // swap x and y
	  tr := [y,x];
	else
	  tr := [x,y];
	end if;
      end if;
      f := Evaluate(f,tr);
      assert IsDivisibleBy(f,y);
      u,v := Explode([MonomialCoefficient(f,m) : m in [x^2*y,x*y^2]]);
      seq := [x-(v/(2*u^2))*y,(1/u)*y];
      f := Evaluate(f,seq);	
      tr := [Evaluate(e,seq) : e in tr];
      return f,tr,1;   // f=y*(x^2+A*y^2), A != 0
    else // f splits into linear forms over k
      if mx+my eq 3 then
	mf := 0;
      else
        mf,i := Max([fac[2] : fac in fs[1]]);
	a := Coefficient(fs[1][i][1],0);
      end if;
      if Max([mx,my,mf]) le 1 then //distinct linear forms
	if my eq 1 then
	  if mx eq 1 then
	    tr := [x-(a/(2*lc))*y,(1/lc)*y];
	  else
	    assert #(fs[1]) eq 2;
	    b := Coefficient(fs[1][(i eq 1) select 2 else 1][1],0);
	    tr := [x-((a+b)/(2*lc))*y,(1/lc)*y];
	  end if;
	elif mx eq 1 then
	  assert #(fs[1]) eq 2;
	  b := Coefficient(fs[1][(i eq 1) select 2 else 1][1],0);
	  tr := [c*y,x-((lc*c^2*(a+b))/2)*y] where
			c is 1/(lc*a*b);
	else
	  assert #(fs[1]) eq 3;
	  b,c := Explode([Coefficient(fs[1][j][1],0) : j in [1..3] | j ne i]);
	  if (k cmpeq Rationals()) and &and[IsIntegral(lc*e): e in [a,b,c]] then
	    a1,b1,c1 := Explode([Integers()!e : e in Sort([lc*a,lc*b,lc*c])]);
	    if b1-a1 le c1-b1 then
		a := (a1/lc); b := (b1/lc); c := (c1/lc);
	    else
		a := (b1/lc); b := (c1/lc); c := (a1/lc);
	    end if;
	  end if;
	  tr := [(a/(a-c))*x-(1/lc)*(((a*(b+c)/2)-b*c)/(a-b)^2)*y,
        		-(1/(a-c))*x+(1/lc)*((a-(b+c)/2)/(a-b)^2)*y];
	end if;
	return Evaluate(f,tr),tr,1;     // f=y*(x^2+A*y^2), A != 0
      else // repeated factor
	if mx ge 2 then
	  if mx eq 3 then return f,[x,y],3; end if;
	  if my eq 1 then
	    tr := [x,(1/lc)*y];
	  else //#fs[1] eq 1
	    tr := [x,(1/a)*(-x+(1/lc)*y)];
	  end if;
        elif my ge 2 then
	  if my eq 3 then return lc*x^3,[y,x],3; end if;
	  if mx eq 1 then
	    tr := [(1/lc)*y,x];
	  else //#fs[1] eq 1
	    tr := [-a*x+(1/lc)*y,x];
	  end if;
        else
	  assert mf ge 2;
	  if mf eq 3 then
	    return lc*x^3,[x-a*y,y],3;
	  end if;
	  if my gt 0 then
	    tr := [x-(a/lc)*y,(1/lc)*y];
	  elif mx gt 0 then
	    tr := [(1/lc)*y,(1/a)*(x-(1/lc)*y)];
	  else
	    assert #(fs[1]) eq 2;
	    b := Coefficient(fs[1][(i eq 1) select 2 else 1][1],0);
	    c := 1/(a-b);
	    tr := [c*(-b*x+(a/lc)*y),c*(x-(1/lc)*y)];
	  end if;	  
	end if;
	return x^2*y,tr,2;	  
      end if;
    end if;
	      
end function;

function normalise_deg_4_homog_poly(f)

    R := Generic(Parent(f)); k := BaseRing(R);
    x := R.1; y := R.2;
    P := PolynomialRing(k); t := P.1;
    pol := Evaluate(f,[t,1]);

    // f splits into distinct linear factors/ alg closure of k
    if (not IsZero(Discriminant(pol))) and (Degree(pol) ge 3) then
	error if Characteristic(k) eq 2,
		"X9-like singularity in characteristic 2";
	// transform f to a*x^4+b*x^2*y^2+c*y^4, ac != 0, b^2 != 4ac.
	// might need a field extension of degree up to 6.
	if Degree(pol) eq 4 then
	  e,d,c,b,a := Explode(Coefficients(pol));
	else
	  e,d,c,b := Explode(Coefficients(pol));
	  a := k!0;
	end if;
	if IsZero(b) and IsZero(d) then
	  return f,[x,y],1;
	end if;

	if IsZero(b^3-4*a*b*c+8*a^2*d) then
	  tr := [x-(b/(4*a))*y,y];	  
	elif IsZero(d^3-4*c*d*e+8*e^2*b) then
	  tr := [x,y-(d/(4*e))*x];	  
	else
	  pol1 := P![-8*b*e^2+4*c*d*e-d^3, -32*a*e^2-4*b*d*e+8*c^2*e-2*c*d^2,
	   -40*a*d*e+20*b*c*e-5*b*d^2, -20*a*d^2+20*b^2*e, 40*a*b*e-20*a*c*d+5*b^2*d,
	   32*a^2*e+4*a*b*d-8*a*c^2+2*b^2*c, 8*a^2*d-4*a*b*c+b^3];
	  // In this case pol1 is a degree 6 polynomial that is relatively prime
	  //  to pol2 = b*t^3+2*c*t^2+3*d*t+4*e. If pol1(A)=0 and 
	  //  B := -(4*a*A^3+3*b*A^2+2*c*A+d)/pol2(A) then the transformation
	  // [x,y] -> [Ax+y,x+By] (AB != 1 in this case) takes f to normal form
	  fact := Factorisation(pol1);
	  deg,i := Min([Degree(f[1]) : f in fact]);
	  pol2 := fact[i][1];
	  if deg gt 1 then
	    K := ext<k|pol2>;
	    R := ChangeRing(R,K); x := R.1; y := R.2;
	    f := R!f;
	    A := K.1;
	  else
	    A := -Coefficient(pol2,0);
	  end if;
	  B := -(4*a*A^3+3*b*A^2+2*c*A+d)/(b*A^3+2*c*A^2+3*d*A+4*e);
	  tr := [A*x+y,x+B*y];
	end if;
	return Evaluate(f,tr),tr,1;
    end if;

    // repeated root cases
    errstr1 := "X_{1,p}-like singularity in characteristic 2";
    errstr2 := "Bad corank 2, order 4 singularity in characteristic 2";
    bchar2 := (Characteristic(k) eq 2);
    my := 4-Degree(pol);
    mx := Valuation(pol);
    if mx gt 0 then pol := pol div t^mx; end if;
    lc := LeadingCoefficient(pol);
    fact := Factorisation(pol);
    fs := [[fac : fac in fact | Degree(fac[1]) eq i] : i in [1..4]];
    error if (#(fs[4]) gt 0) or (#(fs[2]) ge 2),errstr2;
    error if #(fs[3]) gt 0, 
	"Bad corank 2, order 4 singularity in characteristic 3";
    if #(fs[2]) gt 0 then
	f2 := fs[2][1][1];
	binsep := IsZero(Discriminant(f2));
	if binsep then assert bchar2; end if;
	if fs[2][1][2] eq 2 then
	  // f = lc*Q^2, Q an irred quadratic form - linearly transform
	  //  to a*x^2*y^2 over a quadratic extension
	  error if binsep, errstr2;
	  K<a> := ext<k|f2>;
	  b := -Coefficient(f2,0)-a;
	  R := ChangeRing(R,K); x := R.1; y := R.2;
	  tr := [c*(b*x-a*y),c*(x-y)] where c is 1/(b-a);
	  return lc*x^2*y^2,tr,3;
	end if;
	error if (not binsep) and bchar2, errstr1;
	if mx eq 2 then
	  if binsep then
	    tr := [x,y];
	  else
	    a := Coefficient(f2,1); b := Coefficient(f2,0);
	    tr := [x,y-(a/(2*b))*x];
	  end if;
	elif my eq 2 then
	  if binsep then
	    tr := [y,x];
	  else;
	    a := Coefficient(f2,1); b := Coefficient(f2,2);
	    tr := [y-(a/(2*b))*x,y];
	  end if;
	else
	  if (#(fs[1]) eq 0) or (fs[1][1][2] ne 2) then
	    assert binsep;
	    error errstr2;
	  end if;
	  f1 := fs[1][1][1];
	  v := Coefficient(f1,0);
	  if binsep then
	    tr := [x-v*y,y];
	  else
	    c,b,a := Explode(Coefficients(f2)); 
	    tr := [(1+u*v)*x-v*y,-u*x+y] where u is 
		(b-2*a*v)/(2*(a*v^2-b*v+c));
	  end if;
	end if;
	return Evaluate(f,tr),tr,2;
    end if;

    // case of repeated root and all linear factors
    fs := fs[1];
    if mx+my eq 4 then
      mf := 0;
    else
      mf,i := Max([fac[2] : fac in fs]);
      a := Coefficient(fs[i][1],0);
    end if;
    maxm := Max([mx,my,mf]);
    if maxm eq 2 then
      if (mx eq 2) and (my eq 2) then
	tr := [x,y]; typ := 3;
      elif mx eq 2 then
	if mf eq 2 then
	  typ := 3;
	  tr := [x,(y-x)/Coefficient(fs[1][1],0)];
	else
	  typ := 2;
	  error if bchar2, errstr1;
	  if my eq 1 then
	    tr := [x,y-(1/(2*Coefficient(fs[1][1],0)))*x];
	  else
	    a,b := Explode([Coefficient(fs[i][1],0) : i in [1..2]]);
	    tr := [x,y-((a+b)/(2*a*b))*x];
	  end if;
	end if;
      elif my eq 2 then
	if mf eq 2 then
	  typ := 3;
	  tr := [y-Coefficient(fs[1][1],0)*x,x];
	else
	  typ := 2;
	  error if bchar2, errstr1;
	  if mx eq 1 then
	    tr := [y-(Coefficient(fs[1][1],0)/2)*x,x];
	  else
	    a,b := Explode([Coefficient(fs[i][1],0) : i in [1..2]]);
	    tr := IsZero(a+b) select [x,y] else [y-((2*a*b)/(a+b))*x,x];
	  end if;
	end if;
      else //mf = 2
	if #[0 : fac in fs | fac[2] eq 2] eq 2 then
	  a,b := Explode([Coefficient(fs[i][1],0) : i in [1..2]]);
	  tr := [c*(b*x-a*y),c*(y-x)] where c is 1/(b-a);
	  typ := 3;
	else
	  typ := 2;
	  error if bchar2, errstr1;
	  if (mx eq 1) and (my eq 1) then
	    tr := [(x+y)/2,(x-y)/(2*Coefficient(fs[1][1],0))];
	  else
	    if mx eq 1 then
	      a,b := Explode([Coefficient(fs[j][1],0) : j in [i,3-i]]);
	      u := (b-2*a)/(2*a*(b-a));
	    elif my eq 1 then
	      a,b := Explode([Coefficient(fs[j][1],0) : j in [i,3-i]]);
	      u := (2*b-a)/(2*(b-a));
	    else
	      a := Coefficient(fs[1][i],0);
	      b,c := Explode([Coefficient(fs[j][1],0) : j in [1..3] | j ne i]);
	      u := (2*a-b-c)/(2*(b-a)*(c-a));
	    end if;
	    tr := [(1-a*u)*x-a*y,u*x+y];
	  end if;
	end if;
      end if;
      return Evaluate(f,tr),tr,typ;
    elif maxm eq 3 then
      u := 1/lc;
      if mx eq 3 then
	tr := (my eq 1) select [x,u*y] else [x,(u*y-x)/Coefficient(fs[1][1],0)];
      elif my eq 3 then
	tr := (mx eq 1) select [u*y,x] else [u*y-Coefficient(fs[1][1],0)*x,x];
      else //mf eq 3
	if my eq 1 then
	  tr := [x-Coefficient(fs[1][1],0)*u*y,u*y];
	elif mx eq 1 then
	  tr := [u*y,(x-u*y)/Coefficient(fs[1][1],0)];
	else
	  a,b := Explode([Coefficient(fs[j][1],0) : j in [i,3-i]]);
	  tr := [c*(b*x-a*u*y),c*(u*y-x)] where c is 1/(b-a);
	end if;
      end if;
      return Evaluate(f,tr),tr,4;
    else //maxm eq 4
      if mx eq 4 then
	tr := [x,y];
      elif my eq 4 then
	tr := [y,x];
      else //mf eq 4
	tr := [x-Coefficient(fs[1][1],0)*y,y];
      end if;
      return Evaluate(f,tr),tr,5;
    end if;
    
end function;

function derivs_to_mon_trans(f,seq)
// turns the derivatives of f into a sequence of monomomial transformation rules
// <[m,p],[a1,..,an]> where m is the smallest term of df/dxi, p = m-df/dxi and
// all aj are 0 except ai=1. the order of derivatives in the sequence of rules
// is given by the sequence seq which contains 1,..,n in the desired order (n=rank(R))

    m_t := []; R := Generic(Parent(f));
    n := Rank(R);
    as0 := [R!0 : i in [1..n]];
    for i in seq do
	df := Derivative(f,i);
	t := Min(Terms(df));
	lc := LeadingCoefficient(t);
	e := [LeadingMonomial(t),(1/lc)*(t-df)];
	as1 := as0; as1[i] := R!((1/lc));
	Append(~m_t,<e,as1>);
    end for;
    return m_t;
	    
end function; 

function special_nf_function(f,mon_trans,deg : get_coords := true) 

    red := [m[1] : m in mon_trans];
    min_terms := [m[1] : m in red];
    cs1 := [m[2] : m in mon_trans];

    R := Parent(f);
    f0 := R!0; g := f;
    cs := [R!0 : i in [1..Rank(R)]];
    d := Min([LeadingTotalDegree(t) : t in Terms(g)]);
    t := seq[#seq] where seq is [t : t in Terms(g)| LeadingTotalDegree(t) eq d];
   
    while d le deg do
	i := 0;
	for j in [1..#min_terms] do
	    boo,q := IsDivisibleBy(t,min_terms[j]);
	    if boo then i := j; break; end if;
	end for;
	if i ne 0 then
	    if get_coords then 
	      for j in [1..Rank(R)] do cs[j] +:= q*cs1[i][j]; end for;
	    end if;
	    g -:= q*(red[i][1]-red[i][2]);
	else	  
	    f0 +:= t;
	    g -:= t;
	end if;
	if IsZero(g) then break; end if;
	d := Min([LeadingTotalDegree(t) : t in Terms(g)]);
	t := seq[#seq] where seq is [t : t in Terms(g)| LeadingTotalDegree(t) eq d];
    end while;

    return f0,cs;

end function;

function special_transform_to_normal_form(F,f0,deg,mon_trans : get_trans := true)
// this is a general function to find the transformation to normal form
// (up to degree deg) in the non-sesquihomogeneous cases when f0 satisfies
// Arnolds condition A for a Newton filtration (or is close to satisfying cond. A!).
// f0 should again be a non-degenerate 'leading' term (usually w.r.t. a Newton
// filtration function that doesn't come from a single weighting) and it
// is assumed that if we take the smallest term of a derivative of f
// (with respect to the Groebner ordering of R, which should be a degree ordering)
// and 'reduce' w.r.t. it by replacing it by minus the remainder in monomials
// divisible by it, then reiteration will lead to a normal form (based on fin. many monomials)
// + terms of arbitrarily high degree.
//
// however, we really need something like a Groebner basis of relations for an appropriate
// ordering to get some relations that are derived in several stages from the derivative
// relations and involve first lowering degrees before raising them again. A
// 'Coordinates' type intrinsic is also needed to express the relations in terms
// of derivative relations. As this is not as readily available with existing magma
// functionality for local polynomial rings, this function takes a precomputed
// set of reduction relations in the mon_trans argument, which is usually computable
// by hand in the cases that occur here. The format for mon_trans is as follows.
//
// mon_trans should be a sequence all relations required in the reduction, relations
// lying in the ideal generated by the derivatives of f0. 
// Elements should be of the form <[m,p],[a1,..,an]> where m is a
// monomial and p is a polynomial, with terms larger than m for the ordering, s.t.
// m = p mod the ideal of derivatives and m-p = sum ai (df0/dxi). These are used in the
// normal form/coordinates function above.

    R := Generic(Parent(F)); k := BaseRing(R);
    n := Rank(R);
    trans := [R.i : i in [1..n]];

    d := Min([LeadingTotalDegree(t): t in Terms(f0)]);
    assert deg ge d;
    if deg eq d then return f0,trans; end if;

    trunc_to_deg := func<f,e|&+[R|t : t in Terms(f) | 
				LeadingTotalDegree(t) lt e]>;
    Fcurr := trunc_to_deg(F, deg+1);
    f2 := Fcurr-f0;
    if IsZero(f2) then return f0,trans; end if;
    f1 := 0;
 
    while f2 ne R!0 do
	d2 := Min([LeadingTotalDegree(t): t in Terms(f2)]);
//printf "d2: %o\n",d2;
//printf "f2: %o\n",&+[t : t in Terms(f2) | LeadingTotalDegree(t) eq d2];
	if d2 gt deg then break; end if;
	d12is := [(#T eq 0) select deg+1 else Min([LeadingTotalDegree(t): t in T])-1
	  where T is [t : t in Terms(f1+f2) | Exponents(t)[i] ne 0] :
				i in [1..n]];
	f1n,vs := special_nf_function(f2,mon_trans,deg);
	f1 +:= f1n;
	vsdegs := [(IsZero(vs[i]) select deg+2 else 
		Min([LeadingTotalDegree(t): t in Terms(vs[i])])):
			i in [1..n]];
	err1 := Min(Min([d12is[i]+vsdegs[i] : i in [1..n]]),deg+1);
	Ftmp := trunc_comp([f0],[R.i-vs[i]: i in [1..n]],err1-1)[1];
	err2 := IsZero(G) select err1 else Min([LeadingTotalDegree(t): t in Terms(G)])
		where G is f2+Ftmp-f1n-f0;
	err2 := Min(err1,err2);
//if not IsZero(f2+Ftmp-f1n-f0) then
// printf "G min deg: %o\n",&+[R|t : t in Terms(f2+Ftmp-f1n-f0) | LeadingTotalDegree(t) eq err2];
//end if;
//printf "err2:%o\n",err2;
//printf "vs:%o\n",vs;
	vs := [trunc_to_deg(vs[i],err2-d+1) : i in [1..n]];
//printf "vs:%o\n",vs;
	vec := [R.i-vs[i]: i in [1..n]];
	Fcurr := trunc_comp([Fcurr],vec,deg)[1];
	if get_trans then
	  trans := trunc_comp(trans,vec,deg+1-d);
	end if;
	f2 := Fcurr-f0-f1;
    end while;

    return f0+f1,trans;

end function;

function general_transform_to_normal_form(F,f0,deg,mon_trans : get_trans := true)
// This is a variant of special_transform_to_normal_form that applies to 
// non-sesquihomogeneous f0 for which the simple iteration of
// special_transform_to_normal_form can fail, ending in a infinite loop.
//
// This function is basically the same, with similar arguments and return
// values, but if the normal form computation leads to v(f) = sum vi*(df0/dxi)
// where v is the differential operator sum vi*(d/dxi), then instead of
// the simple transformation xi -> xi-vi (each i), we use xi -> 
// xi + sum_{1<=r<=m} (-1)^r/(r!) v^(r-1)(vi) where v^j is v applied j times
// in succession (the identity if j = 0) and m is sufficiently large such
// that higher terms vanish to the precision needed at that stage. In char 0,
// this formal substitution when m=infinity into f0 exactly cancels the f2-f1n
// term. In char p, the function throws an error if we get to an m >= p at any stage,
// so this differs from the special function in that char p failure for small p
// can occur here, depend on the precision to which the transformation is required
// and not be so easily predictable a priori.

    R := Generic(Parent(F)); k := BaseRing(R);
    p := Characteristic(k);
    n := Rank(R);
    ws := VariableWeights(R);
    trans := [R.i : i in [1..n]];

    dw := Min([WeightedDegree(t): t in Terms(f0)]);
    d := Min([LeadingTotalDegree(t): t in Terms(f0)]);
    assert deg ge d;
    if deg eq d then return f0,trans; end if;

    trunc_to_deg := func<f,e|&+[R|t : t in Terms(f) | 
				LeadingTotalDegree(t) lt e]>;
    Fcurr := trunc_to_deg(F, deg+1);
    f2 := Fcurr-f0;
    if IsZero(f2) then return f0,trans; end if;
    f1 := 0;
 
    while f2 ne R!0 do
	d2 := Min([LeadingTotalDegree(t): t in Terms(f2)]);
	if d2 gt deg then break; end if;
	d12is := [(#T eq 0) select deg+1 else Min([LeadingTotalDegree(t): t in T])
	  where T is [t : t in Terms(f1+f2) | Exponents(t)[i] ne 0] :
				i in [1..n]];
	f1n,vs := special_nf_function(f2,mon_trans,deg);
	f1 +:= f1n;
	vsdegs := [(IsZero(vs[i]) select deg+1 else 
		Min([LeadingTotalDegree(t): t in Terms(vs[i])]))-1:
			i in [1..n]];
	err1 := Min(Min([d12is[i]+vsdegs[i] : i in [1..n]]),deg+1);

	// 'Differential solution'
	assert (Min(vsdegs) ge 0);
	vst := [trunc_to_deg(v,err1-d+2) : v in vs];
	vs1 := [];
	for i in [1..n] do
	  v := vst[i]; m := 1;
	  w := v;
	  while not IsZero(v) do
	    m := m+1;
	    error if m eq p,"Characteristic error";
	    v := (-1/k!m)*trunc_to_deg(&+[vst[i]*Derivative(v,i) : i in [1..n]],err1-d+2);
	    w +:= v;
	  end while;
	  Append(~vs1,w);
	end for;	   
	vec := [R.i-vs1[i]: i in [1..n]];
	Fcurr := trunc_comp([Fcurr],vec,deg)[1];
	if get_trans then
	  trans := trunc_comp(trans,vec,deg+1-d);
	end if;
	f2 := Fcurr-f0-f1;
    end while;

    return f0+f1,trans;

end function;

/******************** Functions for the f=x^4+O(deg 5) cases **********************/

function Xk0case(f,k,deg,get_trans)
  
    R0 := Generic(Parent(f));
    K := BaseRing(R0);
    tr := [R0.1,R0.2];
    wts := [k,1];

    // transform quasi-hom part to (almost) normal form
    // (over an extn of degree <= 4)
    // ax^4+b*x^3*y^k+c*x^2*y^2k+d*x*y^3k with a,d != 0, bc != 9ad

    P := PolynomialRing(K);
    ft := P![MonomialCoefficient(f,Monomial(R0,[i,(4-i)*k])) : i in [0..4]];
    a := LeadingCoefficient(ft);
    fact := Factorisation(ft);
    rts := [-Coefficient(g[1],0) : g in fact | Degree(g[1]) eq 1];
    boo := false;
    for r in rts do
	ft1 := Evaluate(ft,P.1+r);
	cs := Coefficients(ft1);
	if not (cs[3]*cs[4] eq 9*a*cs[2]) then
	  tr := [R0.1+r*(R0.2)^k,R0.2];
	  f := trunc_comp([f],tr,deg)[1];
	  f0 := Polynomial(Prune(Reverse(cs)),[Monomial(R0,[4-i,i*k]) : i in [0..3]]);
	  R := R0;
	  boo := true; break;
	end if;
    end for;
    if not boo then
      assert #rts le 2;
      fact := [g[1] : g in fact | Degree(g[1]) gt 1];
      bspec := false;
      if #fact ge 2 then
	assert (#fact eq 2) and &and[Degree(f) eq 2 : f in fact];
	bspec := true;
      end if;
      for g in fact do
	K<u> := ext<K|g>;
	R := ChangeRing(R0,K);
	tr := [R.1+u*(R.2)^k,R.2];
	f1 := trunc_comp([R!f],tr,deg)[1];
	f0 := Polynomial([MonomialCoefficient(f,Monomial(R,[4-i,i*k])) : i in [0..3]],
		[Monomial(R,[4-i,i*k]) : i in [0..3]]);
	if bspec then  // check bc=9ad condition
	  if 9*(K!a)*MonomialCoefficient(f1,Monomial(R,[1,3*k])) ne
		MonomialCoefficient(f1,Monomial(R,[3,k]))*
		  MonomialCoefficient(f1,Monomial(R,[2,2*k])) then
	    a := K!a; f := f1; break;
	  end if;
	else
	  f := f1;
	end if;
      end for;
    end if;
    assert IsZero(MonomialCoefficient(f,Monomial(R,[0,4*k])));
    b := MonomialCoefficient(f,Monomial(R,[3,k]));
    c := MonomialCoefficient(f,Monomial(R,[2,2*k]));
    d := MonomialCoefficient(f,Monomial(R,[1,3*k]));
    assert 9*a*d ne b*c;

    R1<x,y> := PolynomialRing(BaseRing(R),wts,"grevlexw",wts);
    a1 := -(2*c)/(3*d); b1 := -b/(3*d);
    a2 := (4*c^2-9*b*d)/(3*d^2); b2 := (2*(b*c-6*a*d))/(3*d^2);
    c1 := (2*(3*a*c-b^2))/(b*c-9*a*d);
    gs := [[x^2*y^(3*k-1),c1*x^3*y^(2*k-1)],
	   [x*y^(4*k-1),(b1+a1*c1)*x^3*y^(2*k-1)],
	   [y^(5*k-1),(b2+a2*c1)*x^3*y^(2*k-1)],
	   [x*y^(3*k),a1*x^2*y^(2*k)+b1*x^3*y^k],
	   [y^(4*k),a2*x^2*y^(2*k)+b2*x^3*y^k]];
    F,tr1 := qh_transform_to_normal_form(R1!f,R1!f0,deg : get_trans := get_trans,
				groebner_shift := gs);
    if get_trans then
	tr := trunc_comp(tr,[R!a : a in tr1],deg-3);
    end if;
    return R!F,tr;
	
end function;


function Xkrcase(f,k,r,deg,get_trans)

    R0 := Generic(Parent(f));
    tr := [R0.1,R0.2];
    wts := [k,1];
    R1 := PolynomialRing(BaseRing(R0),wts,"grevlexw",wts);
    f := R1!f;
    x := R1.1; y := R1.2;
    f0 := &+[MonomialCoefficient(f,m)*m : m in [x^(4-i)*y^(k*i) : i in [0..4]]];
    assert IsZero(MonomialCoefficient(f0,x*y^(3*k))) and
		IsZero(MonomialCoefficient(f0,y^(4*k)));
    a := MonomialCoefficient(f0,x^4);
    b := MonomialCoefficient(f0,x^3*y^k);
    c := MonomialCoefficient(f0,x^2*y^(2*k));

    // first transform to ax^4+bx^3y^k+cx^2y^2k+dy^(4k+r)+x^3*y^(k+1)*(a0+a1*y+..)
    gs := [[x^2*y^k,(-b/(2*c))*x^3],[x*y^(2*k),((3*b^2-8*a*c)/(4*c^2))*x^3]];
    _,tr1 := qh_transform_to_normal_form(f,f0,4*k+r : 
				groebner_shift := gs);
    f := trunc_comp([f],tr1,deg)[1];
//printf "f: %o\n",f;
    if get_trans then tr := [R0!a : a in tr1]; end if;
    tf0 := [t : t in Terms(f) | Exponents(t)[1] eq 0];
    boo := (#tf0 gt 0);
    if boo then
	t0 := Min(tf0);
	boo := (Exponents(t0) eq [0,4*k+r]);
    end if;
//printf "tf0: %o\nt0: %o\n",tf0,t0;
    error if not boo, "Bad";
//printf "got to here\n";
    f0 +:= t0;
    d := LeadingCoefficient(t0);

    c1 := c^2*(4*a*c-b^2); b1 := 8*a*c-3*b^2; d1 := ((4*k+r)*d)/k;
    assert not IsZero(c1) and not IsZero(d1);
    m_t := [ <[x^4,-(3*b/(4*a))*x^3*y^k-(c/(2*a))*x^2*y^(2*k)],[(1/(4*a))*x,0]>,
     <[x^3*y^(2*k-1),-(3*b/(4*a))*x^2*y^(3*k-1)-(c/(2*a))*x*y^(4*k-1)],
			[(1/(4*a))*y^(2*k-1),0]>,
     <[x^2*y^(2*k-1),(-b/(2*c))*x^3*y^(k-1)-(d1/(2*c))*y^(4*k+r-1)],
			[0,R1!(1/(2*c*k))]>,
     <[x*y^(4*k-1),(d1/(8*c1))*(4*a*b1*x*y^(4*k+r-1)+b*(32*a*c-9*b^2)*y^(5*k+r-1))],
        [(1/(8*c1))*b*b1*x*y^(k-1)+(1/(2*c))*y^(2*k-1),
		(1/(8*k*c1))*(-4*a*b1*x+b*(9*b^2-32*a*c)*y^k)]>,
     <[x*y^(3*k-1),(1/(2*c)^2)*(-b1*x^3*y^(k-1)+3*b*d1*y^(4*k+r-1))],
			[(1/(2*c))*y^(k-1),(-3*b/(k*(2*c)^2))*R1!1]>,
     <[y^(6*k+r-1),(1/(16*c*c1*d1))*(d1^2*(3*b1^2-64*a^2*c^2)*y^(6*k+2*r-1)-
		(4*a*d1)^3*y^(6*k+3*r-1))],
        [(1/(16*c*c1*d1))*y^(k-1)*(4*a*b*b1*d1*x^2*y^r-8*b*c1*x^2+
	d1*(b1^2-8*a*b^2*c)*x*y^(k+r)-16*c*c1*x*y^k-12*b*(c1/c)*d1*y^(2*k+r)-
	16*a^2*b*d1^2*y^(2*(k+r))),
   	(1/(16*c*c1*d1*k))*(-16*a^2*b1*d1*x^2*y^r+32*a*c1*x^2+32*a^2*b*c*d1*x*y^(k+r)+
	24*b*c1*x*y^k+64*a^3*d1^2*y^(2*(k+r))-d1*(3*b1^2-64*a^2*c^2)*y^(2*k+r)        
        +16*c*c1*y^(2*k))]>   ];

    if not IsZero(b1) then
	Insert(~m_t,3,<[x^2*y^(3*k-1),(2/b1)*(b*c*x*y^(4*k-1)-2*a*d1*y^(5*k+r-1))],
		[-(b/b1)*y^(2*k-1),(4*a/(b1*k))*y^k]>);
    else
	assert not IsZero(b);
	Insert(~m_t,3,m_t[5]); Remove(~m_t,6); Remove(~m_t,5);
    end if;
//printf "f:%o\nf0:%o\n",f,f0;
//printf "m_t: %o\n",m_t;
    f,tr1 := special_transform_to_normal_form(f,f0,deg, m_t : get_trans := get_trans);
    f := R0!f;
    if not get_trans then
	return f,tr;
    else
	tr := trunc_comp(tr,[R0!a : a in tr1],deg-3);
	return f,tr;
    end if;
     
end function;

function Ykrscase(f,k,dmax,boofd,get_trans : fd, deg)
  error "Not implemented yet.";
end function;

    ///////////// Functions for Zk cases ///////////////////////////
    /// Unfortunately, had difficulties with trying to normalise ///
    /// into the product form using the 3 existing transforation ///
    /// functions. So, Zk still needs to be done. Probably will  ///
    /// have to write special case transformation code for this  ///
    /// and the even nastier Ykrs product cases.                 ///

function Zk_rcase1(f,k,d,typ,deg,get_trans)
// Handles the Z^k_{12k+2d-3} cases with d != 0 mod 3. On entry, 
// f is an x,y poly in a weight [k,1] grevlexw ring that has
// been transformed to ax^4+bx^3y^k+bcy^(4k+d)+O(y^(4k+d+1))+
// (x^ry^s)-terms with r>0, s>=0 lying above the broken
// 2-segment polygon connecting the leading 3 terms.
// abc != 0. char does not divide 6k(4k+d).

  R := Generic(Parent(f));
  x := R.1; y := R.2;

  // TO DO! Unfortunately the method below does not work using either
  // general_transform_to_normal_form or special_transform_to_normal_form.
  // Will have to write specific code for the transformation in this
  // and the Ykrs product normal form cases. 
   
  // Method (e=d mod 3):
  // 1) Transform to f1 = (ax+by^k)(x^3+cy^(3k+d)) + y^(4k+d+1)*(A0+..A(k-3)*y^(k-3))
  //     + x*y^(3k+(2d+e)/3)*(B0+..+(B*)*y^(2k-2+(d-e)/3)) + O(high deg)
  //  using spectral sequence reduction
  // 2) solve for a1,..a_(k-2), b0,..b* s.t f1 ~ 
  //  [ax+b*y^k+y^(k+1)*(a1+..+a_(k-2)*y^(k-3))]*
  //    [x^3+c*y^(3k+d)+x*y^(2k+(2d+e)/3)*(b0+..(b*)*y^(2k-2+(d-e)/3)]
  //  up to reduction rules and find the explicit transformation to
  //  take f1 to this form (if get_trans is true)

  a := MonomialCoefficient(f,Monomial(R,[4,0]));
  b := MonomialCoefficient(f,Monomial(R,[3,k]));
  c := MonomialCoefficient(f,Monomial(R,[0,4*k+d]));
  assert not IsZero(a*b*c);
  c := c/b;
  f0 := a*x^4+b*x^3*y^k+(b*c)*y^(4*k+d);

  a1 := (4*a)/(3*b); b1 := k/((4*k+d)*c); c1 := 1/(k*b);
  m_t := [<[x^3,-(1/a1)*x^2*y^k],[R!(1/(4*a)),0]>,
   <[x^2*y^(2*k),(a1/b1)*y^(4*k+d)],[(1/(3*b))*y^k,-(a1*c1)*y]>,
   <[x*y^(5*k+d-1),-(a1^2/b1)*y^(6*k+2*d-1)],[(-1/(3*b*a1))*y^(k-1)*((a1*b1)*x^2+
		a1^2*y^(2*k+d)), c1*((a1*b1)*x^2+b1*x*y^k+a1^2*y^(2*k+d))]>,
   <[y^(6*k+d-1),(a1^3/b1)*y^(6*k+2*d-1)],[(1/(3*b))*y^(k-1)*((a1*b1)*x^2-b1*x*y^k+
		a1^2*y^(2*k+d)),-c1*((a1^2*b1)*x^2-b1*y^(2*k)+a1^3*y^(2*k+d))]>,
   <[y^(5*k+d-1),-a1*x*y^(4*k+d-1)],[(-b1/(3*b))*x*y^(k-1),(b1*c1)*(a1*x+y^k)]> ];
  f,tr := special_transform_to_normal_form(f,f0,deg,m_t : get_trans := get_trans);
  //printf "f_new: %o\n",f;
  //error "stop";
  return 0;

end function;

function Zk_rcase2(f,k,d,typ,deg,get_trans)
  error "Not implemented yet.";
end function;

function Zk_r_0case(f,k,d,typ,deg,get_trans)
  error "Not implemented yet.";
end function;

function Zk_r_pcase(f,k,d,r,typ,deg,get_trans)
  error "Not implemented yet.";
end function;

function Zkcases(f,k,i,dmax,boofd,get_trans : fd, deg)
// On entry, f is of the form ax^4+bx^3y^k +(higher degree terms)
// for the [k,1] (x,y)-weighting where k >= 2, ab != 0.
// i is such that mu(f) = 12k+i-3
  
  //NB. The function is incomplete and currently only returns
  //  the exact type string for the singularity - not the normal form.

    //First determine the subtype: Z^k_r or Z^k_{r,s}
    R0 := Generic(Parent(f));
    p := Characteristic(BaseRing(R0));
    typ := "Z^" cat IntegerToString(k) cat "_";
    tr := [R0.1,R0.2];
    wts := [k,1];
    R1<x,y> := PolynomialRing(BaseRing(R0),wts,"grevlexw",wts);
    a := MonomialCoefficient(f,Monomial(R0,[4,0]));
    b := MonomialCoefficient(f,Monomial(R0,[3,k]));
    assert (not IsZero(a)) and (not IsZero(b));
    f := R1!f;
      // 4 basic subtypes: 1) Z^k_{12k+2d-3}, d != 0 mod 3, i=2d
      //  2) Z^k_{12k+3d-3}, d != 0 mod 2, i=3d
      //  3) Z^k_{p,0}, i=6p (p>0)
      //  4) Z^k_{p,r}. i=6p+r (p,r>0)
      // Determine type from i, up to being type 4.
    boor := false; 
    bodd := IsOdd(i);
    bdiv3 := IsDivisibleBy(i,3);
    if bodd then
      if bdiv3 then typ1 := 2; else
      boor := true; // definitely of Z^k_{u,v} type with v > 0
      typ1 := 4;
      end if;
    else
      typ1 := bdiv3 select 3 else 1;      
    end if;
      // transform to ax^4+bx^3y^k+x(a1*y^(3k+1)+a2*..)+(b1*y^(4k+1)+b2..)
      //  + high degree terms
    d := i div 2;
    deg1 := 4*k+d;
    f0 := x^3*(a*x+b*y^k);  
    _,tr1 := qh_transform_to_normal_form(f,f0,deg1); 
    f := trunc_comp([f],tr1,deg)[1];
    if get_trans then tr := [R0!a : a in tr1]; end if;
      // fully determine type
    assert f ne f0;
    tf := [t : t in Terms(f-f0) | WeightedDegree(t) le deg1];
    assert #tf gt 0;
    assert &and[Exponents(t)[1] le 1 : t in tf];
    mindeg := Min([WeightedDegree(t) : t in tf]);
    fd := &+[t : t in tf | WeightedDegree(t) eq mindeg];
    v := MonomialCoefficient(fd,Monomial(R1,[0,mindeg]));
    u := MonomialCoefficient(fd,Monomial(R1,[1,mindeg-k]));
    if mindeg eq deg1 then
      assert not IsZero(v);
      if IsDivisibleBy(d,3) then
	typ cat:= "{" cat IntegerToString(d div 3) cat ",0}";
	assert typ1 eq 3;
      else
	typ cat:= IntegerToString(4*k+2*deg1-3);
	assert typ1 eq 1;
      end if;		   
    else
      assert IsZero(v); // need a characteristic check here!
      d := mindeg-4*k;
      assert d ge 1;
      yts := [j : j in [1..(d div 2)] | 
		not IsZero(MonomialCoefficient(f,[0,mindeg+i]))];
      if #yts eq 0 then
        if IsOdd(d) then // Z^k_(12*k+3*d-3)
	  typ cat:= IntegerToString(12*k+3*d-3);
	  typ1 eq 2;
	else // Z^k_{d/2,0}
	  typ cat:= "{" cat IntegerToString(d div 2) cat ",0}";
	  typ1 := 3;
	end if;
	error if i ne 3*d, "blah1";
      elif IsOdd(d) or (Min(yts) lt (d div 2)) then
	j := Min(yts);
	boo,dplusjby3 := IsDivisibleBy(d+j,3);
	if boo then // Z^k_{(d+j)/3,0}
	  typ cat:= "{" cat IntegerToString(dplusjby3) cat ",0}";
	  typ1 := 3;
	else // Z^k_(12*k+2*(d+j)-3)
	  typ cat:= IntegerToString(12*k+2*(d+j)-3);
	  typ1 := 1;
	end if;
	error if i ne 2*(d+j), "blah2";
      else
	//here d is even and Min(yts) = d/2
	ad := MonomialCoefficient(f,[0,mindeg+(d div 2)]);
	pol := PolynomialRing(BaseRing(R0))![ad/b,u/b,0,1];
	if not IsZero(Discriminant(pol)) then // Z^k_{d/2,0}
	  typ cat:= "{" cat IntegerToString(d div 2) cat ",0}";
	  typ1 := 3;
	  error if i ne 3*d, "blah3";
	else //Z^k_{d/2,r} for some r>0
	  r := i-3*d;
	  assert r gt 0;
	  typ cat:= "{" cat IntegerToString(d div 2) cat "," cat
			IntegerToString(r) cat "}";
	  typ1 := 4;
	  // do preliminary transformation and check!
	end if;
      end if;
    end if;

    // NORMAL FORM CODE STILL TO BE DONE. For the moment, just return
    // the type string
    return typ;

    if typ1 eq 1 then
      f,tr1 := Zk_rcase1(f,k,d,typ,deg,get_trans);
    elif typ1 eq 2 then
      f,tr1 := Zk_rcase2(f,k,d,typ,deg,get_trans);
    elif typ1 eq 3 then
      f,tr1 := Zk_r_0case(f,k,d,typ,deg,get_trans);
    else //typ1 = 4
      f,tr1 := Zk_r_pcase(f,k,d,r,typ,deg,get_trans);
    end if;

end function;

/******************** Main intrinsic **********************/

intrinsic Corank2Case(f::RngMPolElt : d := 0, milnor_number := -1,
   fData := [**], get_trans := false) -> BoolElt, RngMPolElt, MonStgElt, Map
{ f should be a two-variable non-zero polynomial defining a corank 2 singularity
 at (0,0). That is, f contains no terms of degree < 3. Returns whether the
 singularity is one that occurs in Arnold's classification. If so, also
 returns the normal form f0 of the equation for the singularity and a string
 containing a label for the family that it lies in. If parameter get_trans
 is true (default: false), a fourth return value is a polynomial map giving
 the truncation to a certain precision of an analytic isomorphism from f
 to f0. This precision is the maximum of parameter d (default: 0) and the
 default precision for the singularity type as described in the Handbook.
 The argument f may be the polynomial truncation up to degree fdeg of a power
 series F that defines the singularity. In this case, data for expanding
 f to higher degree if necessary should be given by setting parameter
 fData to the 2-element list [* dat, fdeg *] where dat is a data object
 of the type described in the Handbook. }

// NOTE: fData (when not 0) should be a list pair containing [* fdata, dmax *] where dmax
//  is the degree to which f has been expanded.

    R0 := Generic(Parent(f));
    require (f ne 0) and Rank(R0) eq 2: "f not a non-zero two variable polynomial";
    K := BaseRing(R0);
    p := Characteristic(K);
    // check K is a field - maybe of a certain type
    ord := Min([TotalDegree(t) : t in Terms(f)]);
    require ord ge 3:
       "f does not have a zero or does not have a corank 2 singularity at (0,0)";

    if ord ge 6 then return false,_,_,_; end if;

    boofd := (#fData gt 0);
    if boofd and (fData[2] lt d) then 
	return Corank2Case(expand_to_prec_with_quadratic_part(fData[1],d,R0):
		d := d, fData := [* fData[1],d *], get_trans := get_trans, 
			milnor_number := milnor_number);
    end if;
    if boofd then
	fdata := fData[1];
	dmax := fData[2];
        //assert dmax ge Max([TotalDegree(t) : t in Terms(f)]);
    else
      dmax := Max([TotalDegree(t) : t in Terms(f)]);
    end if;

    if milnor_number lt 0 then
	mu := boofd select MilnorNumberAnalyticHypersurface(fdata) else MilnorNumber(f);
	if Type(mu) cmpeq Infty then return false,_,_,_; end if;
    else
	mu := milnor_number;
    end if;
    assert mu ge 4;

    trans := [R0.1,R0.2];
    P := PolynomialRing(K); t := P.1;
    f_orig := f;
    expnstr := "Char. p error while trying to transform to normal form ";
    pstr := IntegerToString(p);
    errstr := "-like singularity in characteristic " cat pstr;

    j3f := &+[R0|t : t in Terms(f) | LeadingTotalDegree(t) eq 3];

    if j3f ne 0 then
      j3f1,tr,typ := normalise_deg_3_homog_poly(j3f);
      f := Evaluate(f,tr);
      if typ eq 1 then //D4
	error if p eq 3, "D4" cat errstr;
	assert mu eq 4;
	if get_trans then
	  if d gt 3 then
	    _,tr1 := qh_transform_to_normal_form(R1!f,R1!j3f1,d)
		where R1 is PolynomialRing(K,2,"grevlex");
	    tr := trunc_comp(tr,[R0!e : e in tr1],d-2);
	  end if;
	  tr := hom<R0->Parent(f)|tr>;
	  return true,j3f1,"D4",tr;
	else
	    return true,j3f1,"D4";
	end if;
      elif typ eq 2 then  //Dk - k >= 5
	// char ne 2 check!
	k := mu;
	assert k ge 5;
	if boofd and (dmax lt k-1) then //need to expand further?
	  f := expand_to_prec_with_quadratic_part(fdata,k-1,R0);
	  f := Evaluate(f,tr);
	end if;
	typstr := "D" cat IntegerToString(k);
        // preliminary transform to x^2*y+Ay^k-1 form
	f1,tr1 := qh_transform_to_normal_form(R1!f,R1!j3f1,k-1: get_trans := get_trans)
			where R1 is PolynomialRing(K,2,"grevlex");
	f1 := R0!f1;
	if get_trans then tr1 := [R0!e : e in tr1]; end if;
	// check the result - might be low characteristic error
	ts := [t : t in Terms(f1) | ((dt gt 3) and (dt lt k-1)) where
			dt is TotalDegree(t)];
	if #ts gt 0 then 
	  assert &+[(Exponents(t))[1] eq 0 : t in ts];
	  assert (p gt 0) and &and[IsDivisibleBy((Exponents(t))[1],p) : t in ts];
	  error typstr cat errstr;
	end if;
	assert (#ts eq 1) and (Exponents(ts[1]) eq [0,k-1]) where 
		ts is [t : t in Terms(f1) | TotalDegree(t) eq k-1];
	// f1 is x^2*y+A*y^(k-1), A != 0
	if get_trans then
	  tr := [Evaluate(e,tr1) : e in tr];
	  wts := (IsEven(k) select [(k div 2)-1,1] else [k-2,2]);
	  d1 := wts[1]*d;
	  if d1 gt wts[2]*(k-1) then
	    f := Evaluate(f,tr1);
	    R1 := PolynomialRing(K,wts,"grevlexw",wts);
	    _,tr1 := qh_transform_to_normal_form(R1!f,R1!f1,d1: ord_deg := Max(d,k-1));
	    tr := trunc_comp(tr,[R0!a : a in tr1],Max(d,k-1)-2);
	  end if;
	  tr := hom<R0->R0|tr>;
	  return true,f1,typstr,tr;
	else
	  return true,f1,typstr;
	end if;
      end if;

      // typ = 3, f = a*x^3+O(deg 4)

      error if p eq 3, "x^3+O(deg 4) singularity in characteristic 3";
      x := R0.1; y := R0.2;
      // Singularity in the E or J families. First determine the family.
      while true do
        exps := [Exponents(t) : t in Terms(f)];
        e012 := [e : e in exps | e[1] le 2];
        assert #[0: e in e012 | e[1] le 1] gt 0;
        k := Min([(e[1]^2+2)*e[2] : e in e012]);
	assert k-2 le mu;
        es := [e : e in e012 | (e[1]^2+2)*e[2] eq k];
        f0 := MonomialCoefficient(f,R0.1^3)*(R0.1^3)+
	  &+[MonomialCoefficient(f,m)*m where m is Monomial(R0,e) : e in es];
	pol := Evaluate(f0,[PolynomialRing(K).1,1]);
	a := Coefficient(pol,2); lc := LeadingCoefficient(pol);
	if not (pol eq  lc*((Parent(pol).1)+(a/(3*lc)))^3) then break; end if;
	assert IsDivisibleBy(k,6);
	tr1 := [x-(a/(3*lc))*y^(k div 6),y];
	f := Evaluate(f,tr1); tr := [Evaluate(e,tr1) : e in tr];
      end while;

      if IsDivisibleBy(k,6) then // Types J_{k/6,j} some j >=0
	j := mu+2-k;
	typstr := "J_{" cat IntegerToString(k div 6) cat "," cat
		IntegerToString(j) cat "}";
      else // types E_{6r+i} i = 5,6,7
	assert #es eq 1;
	typstr := "E" cat IntegerToString(k-2);
	wts := (IsEven(k) select [k div 2, 3] else [k div 3, 2]);
	error if (p gt 0) and IsDivisibleBy(wts[1],p), typstr cat errstr;
      end if;

      // Now convert to normal form
      if typstr[1] eq "E" then
        assert k-2 eq mu;
	if (not get_trans) and (k le 10) then return 
	  true,f0,typstr;
	end if;
	R1 := PolynomialRing(K,wts,"grevlexw",wts);
	d1 := Max(3*wts[1],4*wts[1]-(IsEven(k) select 6 else 4));
	dord := (IsEven(k) select wts[1] else 2*wts[1]-2);
	dord1 := (IsEven(k) select ((4*wts[1]) div 3)-2 else 2*wts[1]-2);
	dord1 := Max(dord1,wts[1]); //Get E6, E8 right!
	// need to expand more?
	if boofd then
	  if dmax lt dord1 then
	    f := expand_to_prec_with_quadratic_part(fdata,dord1,R0);
	    f := Evaluate(f,tr);
	  end if;
	end if;
	if get_trans and (d gt 3) then d1 := d*wts[1]; end if;
	f,tr1 := qh_transform_to_normal_form(R1!f,R1!f0,d1 : get_trans := get_trans,
			ord_deg := Max(d,dord1));
	if not get_trans then
	  return true,R0!f,typstr;
	else
	  tr := trunc_comp(tr,[R0!a : a in tr1],Max(d,dord)-2);
	  return true,R0!f,typstr,hom<R0->R0|tr>;
	end if;	
      else //J families
	// handle J_{k,0} first, which is a semiquasihomogeneous case
	k := k div 6;
	error if (p gt 0) and ( IsDivisibleBy(k,p) or 
			((j gt 0) and IsDivisibleBy(2*(3*k+j),p)) ),
	    typstr cat errstr;
	// do we need to expand further?
	if boofd and (dmax lt (4*k+j-2)) then
	  f := expand_to_prec_with_quadratic_part(fdata,4*k+j-2,R0);
	  f := Evaluate(f,tr);
	  f0 := MonomialCoefficient(f,R0.1^3)*(R0.1^3)+
	       &+[MonomialCoefficient(f,m)*m where m is Monomial(R0,[i,(3-i)*k]) : 
			i in [0..2]];
	end if;
	pol := Evaluate(f0,[PolynomialRing(K).1,1]);

	if j eq 0 then
	  if Discriminant(pol) eq 0 then
	    assert p eq 2;
	    error "Bad " cat typstr cat errstr;
	  end if;
          // Usual Arnold normal form transforms f0 to x^3+b*x^2*y^k+y^3k. To
          // avoid unnecessary field extns we will generally use the alternative
	  // a*x^3+b*x*y^2k+c*y^3k, a,c != 0 (which when x,y are appropriately scaled
	  // -> x^3+b*x*y^2k+y^3k). In a single case, (when we transform to the above
	  // and c = 0), we use the first form (unscaled as a*x^3+ b*x^2*y^k+c*y^3k)
	  // after a possible quadratic extension of the base field.
	  // This is always with char != 2 and -> the single isomorphism class
	  // x^3+(3/u)*x^2*y^k+y^3k where u^3=2.
	  b,a := Explode(Coefficients(pol)[3..4]);
	  u := (b ne 0) select -b/(3*a) else K!0;
	  boo := true; boo1 := true;
	  if Evaluate(pol,u) eq 0 then
	    boo1 := false;
	    c := Coefficient(pol,1);
	    v := -(c+b*u)/(3*a);
	    boo,u1 := IsSquare(v);
	    if boo then u +:= u1;
	    else
	      K1 := ext<K|PolynomialRing(K)![-v,0,1]>;
	      u := (K1!u)+K1.1;
	    end if;
	  end if;
	  R1 := boo select R0 else ChangeRing(R0,K1);
	  if not IsZero(u) then	    
	    seq := [(R1.1)+u*(R1.2)^k,R1.2];
            f := Evaluate(f,seq);
	    f0 := Evaluate(f0,seq);
	    tr := [Evaluate(e,seq) : e in tr];
	  end if;
	  // get "Groebner shift" data for transformation to normal forms
	  R2 := PolynomialRing(BaseRing(R1),[k,1],"grevlexw",[k,1]);
	  c := MonomialCoefficient(f,Monomial(R1,[0,3*k]));
	  assert not IsZero(c);
	  if boo1 then
	    b := MonomialCoefficient(f,Monomial(R1,[1,2*k]));
	    gs := [];
	    if not IsZero(2*b) then
	      gs := [[Monomial(R2,[0,3*k]),-((2*b)/(3*c))*Monomial(R2,[1,2*k])]];
	    end if;
	  else
	    b := MonomialCoefficient(f,Monomial(R1,[2,k]));
	    assert not IsZero(2*b);
	    gs := [[Monomial(R2,[0,3*k]),((2*b^2)/(9*a*c))*Monomial(R2,[1,2*k])]];
	  end if;
	  d1 := 4*k-2;
	  if get_trans and (d gt 3) then d1 := d*k; end if;
	  f,tr1 := qh_transform_to_normal_form(R2!f,R2!f0,d1 : groebner_shift := gs, get_trans := get_trans, ord_deg := Max(d,4*k-2));
	  if not get_trans then
	    return true,R1!f,typstr;
	  else
	    tr := trunc_comp(tr,[R1!a : a in tr1],Max(d,4*k-2)-2);
	    return true,R1!f,typstr,hom<R0->R1|tr>;
	  end if;		  
	end if;
	// j > 0 cases not semiquasihomogeneous!
	if not IsZero(Discriminant(pol)) then
	    error "Bad " cat typstr cat errstr;
	end if;
	// transform weight 3*k (for (x,y) wts (k,1)) part to ax^3+bx^2y^k
	a := LeadingCoefficient(pol);
	pol1 := GCD(pol,Derivative(pol));
	assert Degree(pol1) eq 1;
	p0 := Coefficient(pol1,0); //NB: pol1 is monic
	if not IsZero(p0) then
	  tr1 := [x-p0*y^k,y];
	  f := Evaluate(f,tr1); tr := [Evaluate(e,tr1) : e in tr];
	end if;
	f0 := a*x^3+MonomialCoefficient(f,m)*m where m is Monomial(R0,[2,k]);
	R1 := PolynomialRing(BaseRing(R0),[k,1],"grevlexw",[k,1]);
	_,tr1 := qh_transform_to_normal_form(R1!f,R1!f0,3*k+j);
	f := Evaluate(f,[R0!a : a in tr1]);
	if get_trans then tr := [Evaluate(e,[R0!a : a in tr1]) : e in tr]; end if;
	// f should now be in the form ax^3+bx^2y^k+cy^(3k+j)+O(deg 3k+j+1)
	//  for the weighted degree where the (x,y) weights are (k,1)
	tf0 := [t : t in Terms(f) | Exponents(t)[1] eq 0];
	boo := (#tf0 gt 0);
	if boo then
	  t0 := Min(tf0);
	  boo := (Exponents(t0) eq [0,3*k+j]);
	end if;
	error if not boo, "Bad " cat typstr cat errstr;
	f0 +:= t0;
	b := MonomialCoefficient(f0,Monomial(R0,[2,k])); c := LeadingCoefficient(t0);
	R1 := PolynomialRing(BaseRing(R0),2,"grevlex");
	x := R1.1; y := R1.2;
	m_t := derivs_to_mon_trans(R1!f0,[1]);
	u := 1/((3*k+j)*c); v := (3*a/(2*b)); w := 1/(k*b);
	m_t cat:= [ <[x*y^(3*k-1),v*w*(3*k+j)*c*y^(4*k+j-1)],[(k/2)*w*y^(2*k-1),-v*w*y^k]>,
	  <[y^(4*k+j-1),-v^2*w*(3*k+j)*c*y^(4*k+2*j-1)], [-(k/2)*(u*x*y^(k-1)+w*v*y^(2*k+j-1)),
		v*(u*x+v*w*y^(k+j))+u*y^k]> ];
	f,tr1 := special_transform_to_normal_form(R1!f,R1!f0,Max(d,4*k+j-2), 
			m_t : get_trans := get_trans);
	f := R0!f;
	if not get_trans then
	  return true,f,typstr;
	else
	  tr := trunc_comp(tr,[R0!a : a in tr1],Max(d,4*k+j-2)-2);
			//[Evaluate(e,[R0!a : a in tr1]) : e in tr];
	  return true,f,typstr,hom<R0->R0|tr>;
	end if;
      end if;	    
    end if;

    j4f := &+[R0|t : t in Terms(f) | LeadingTotalDegree(t) eq 4];

    if j4f ne 0 then
      j4f1,tr,typ := normalise_deg_4_homog_poly(j4f);
      f := Evaluate(f,tr);
      if typ eq 1 then // X9 = X_{1,0}
	assert mu eq 9;
	if get_trans then
	  R1 := Parent(f);
	  if d gt 4 then
	    _,tr1 := qh_transform_to_normal_form(R2!f,R2!j4f1,d)
			where R2 is PolynomialRing(BaseRing(R1),2,"grevlex");
	    tr := [Evaluate(e,[R1!u : u in tr1]) : e in tr];
	  end if;
	  tr := hom<R0->R1|tr>;
	  return true,j4f1,"X9",tr;
	else
	  return true,j4f1,"X9";
	end if;
      elif typ eq 2 then // X_{1,r}, r > 0
	// here j4f1 := ax^4+bx^2y^2,  a,b != 0       
	error if p eq 2, "X_{1,r}" cat errstr;
	r := mu-9;
	assert r gt 0;
	typstr := "X_{1," cat IntegerToString(r) cat "}";        
	error if (p gt 0) and IsDivisibleBy(4+r,p), typstr cat errstr;
	// do we need to expand further?
	if boofd and (dmax lt 4+r) then
	  f := expand_to_prec_with_quadratic_part(fdata,4+r,R0);
	  f := Evaluate(f,tr);
	end if;
	R1 := PolynomialRing(BaseRing(R0),2,"grevlex");
	_,tr1 := qh_transform_to_normal_form(R1!f,R1!j4f1,4+r);
	f := Evaluate(f,[R0!a : a in tr1]);
	if get_trans then tr := [Evaluate(e,[R0!a : a in tr1]) : e in tr]; end if;
	// f should now be in the form ax^4+bx^2y^2+cy^(4+r)+O(deg 4+r+1)
	tf0 := [t : t in Terms(f) | LeadingTotalDegree(t) le 4+r];
	boo := (#tf0 eq 3);
	a := MonomialCoefficient(f,Monomial(R0,[4,0]));
	b := MonomialCoefficient(f,Monomial(R0,[2,2]));
	c := MonomialCoefficient(f,Monomial(R0,[0,4+r]));
	error if (not boo) or IsZero(a*b*c), "Bad " cat typstr cat errstr;
	if get_trans and (d gt 4+r) then
	  x := R1.1; y := R1.2;
	  f0 := a*x^4+b*(x*y)^2+c*y^(4+r);
	  a1 := (4+r)*c/(2*b); b1 := b/(2*a); c1 := 1/((4+r)*c);
	  m_t := [ <[x^3,-b1*x*y^2],[R1!(1/(4*a)),R1!0]>,
	   <[x^2*y,-a1*y^(3+r)], [R1!0,R1!(1/(2*b))]>,
	   <[x*y^3,(a1/b1)*x*y^(3+r)],[(1/(2*b))*y,-(a/b^2)*x]>,
	   <[y^(5+r),(a1/b1)*y^(5+2*r)],[-c1*x*y,c1*(2*a/b)*(x^2+b1*y^2-a1*y^(2+r))]> ];
	  f,tr1 := special_transform_to_normal_form(R1!f,f0,d,
			m_t : get_trans := get_trans);
	  f := R0!f;
	  tr := trunc_comp(tr,[R0!a : a in tr1],d-3);//[Evaluate(e,[R0!a : a in tr1]) : e in tr];
	else
	  f := &+tf0;
	end if;
	if not get_trans then
	  return true,f,typstr;
	else
	  return true,f,typstr,hom<R0->R0|tr>;
	end if;	
      elif typ eq 3 then // Y^1_{r,s}, r >= s > 0
	// here j4f1 := bx^2y^2,  b != 0, poss. over a quad. extn. of K
	error if (p eq 2), "Y^1{r,s}" cat errstr;
	rpluss := mu-9;
	assert rpluss ge 2;
	// we look to transform f to ax^(4+r)+bx^2y^2+cy^(4+s) with
	// r >= s >= 1, r+s=rpluss. First, must determine s (and r)
	s1 := rpluss div 2;
	R1 := Generic(Parent(f));
	R2 := PolynomialRing(BaseRing(R1),2,"grevlex");
	_,tr1 := qh_transform_to_normal_form(R2!f,R2!j4f1,4+s1);
	f := Evaluate(f,[R1!a : a in tr1]);
	if get_trans then tr := [Evaluate(e,[R1!a : a in tr1]) : e in tr]; end if;
	sxy := [0,0];
	exps := [[Exponents(t)[i] : t in Terms(f-j4f1) | Exponents(t)[3-i] eq 0] :
			i in [1..2]];
	for i in [1..2] do
	  if #(exps[i]) gt 0 then 
	    s := Min(exps[i])-4;
	    assert s gt 0;
	    sxy[i] := s;
	  end if;
	end for;
	assert (&+sxy) gt 0;
	if (sxy[2] eq 0) or ((sxy[1] gt 0) and (sxy[1] lt sxy[2])) then
	  //reverse vars
	  f := Evaluate(f,[R1.2,R1.1]);
	  if get_trans then tr := [Evaluate(e,[R1.2,R1.1]) : e in tr]; end if;
	  Reverse(~sxy);
	end if;
	s := sxy[2];
	assert s le s1;
	if sxy[1] gt 0 then
	  r := sxy[1];
	  if r+s ne rpluss then
	    assert IsDivisibleBy((4+r)*(4+s),p);
	  end if;
	else
	  r := rpluss-s;
	end if;
	typstr := "Y^1_{" cat IntegerToString(r) cat "," cat IntegerToString(s) cat "}";
	error if (p gt 0) and IsDivisibleBy((4+r)*(4+s),p), typstr cat errstr;
	// do we need to expand further?
	if boofd and (dmax lt 4+r) then
	  f := expand_to_prec_with_quadratic_part(fdata,4+r,R0);
	  f := Evaluate(f,tr);
	end if;
	if r gt s1 then // normalise further up to x^(4+r) term
	  _,tr1 := qh_transform_to_normal_form(R2!f,R2!j4f1,4+r);
	  f := Evaluate(f,[R1!a : a in tr1]);
	  if get_trans then tr := trunc_comp(tr,[R1!a : a in tr1],Max(d-3,r+1)); end if;
	  //if get_trans then tr := Evaluate(e,[R1!a : a in tr1]) : e in tr]; end if;
	  error if IsZero(MonomialCoefficient(f,Monomial(R1,[4+r,0]))) or
	    not &and[IsZero(MonomialCoefficient(f,Monomial(R1,[i,0]))) : i in [4..3+r]],
	    "Bad " cat typstr cat errstr;
	end if;
	a := MonomialCoefficient(f,Monomial(R1,[4+r,0]));
	b := MonomialCoefficient(f,Monomial(R1,[2,2]));
	c := MonomialCoefficient(f,Monomial(R1,[0,4+s]));
	f0 := a*Monomial(R1,[4+r,0])+b*Monomial(R1,[2,2])+c*Monomial(R1,[0,4+s]);
	if not get_trans then 
	  return true,f0,typstr;
	end if;
	// do the final transformation
	x := R2.1; y := R2.2;
	m_t := derivs_to_mon_trans(R2!f0,[1,2]);
	a1 := (4+r)*a/(2*b); b1 := (4+s)*c/(2*b);
	r1 := 1/((4+r)*a); s1 := 1/((4+s)*c);
	m_t cat:= [ <[y^(5+s),-a1*x^(2+r)*y^(3+s)],
		[-s1*x*y,s1*(y^2+a1*x^(2+r))]>,
	   <[x^(5+r),-b1*x^(3+r)*y^(2+s)],
		[r1*(x^2+b1*y^(2+s)),-r1*x*y]> ];
	f,tr1 := special_transform_to_normal_form(R2!f,R2!f0,Max(d,4+r),
			m_t : get_trans := get_trans);
	f := R1!f;
	tr := trunc_comp(tr,[R1!a : a in tr1],Max(d-3,r+1)); //[Evaluate(e,[R1!a : a in tr1]) : e in tr];
	return true,f,typstr,hom<R0->R1|tr>;
      elif typ eq 4 then // Z-family singularity
	// here j4f1 := x^3y
	error if p eq 3, "x^3*y+O(deg 5) singularity in characteristic 3";
        x := R0.1; y := R0.2;
        // First determine the family.
        while true do
          exps := [Exponents(t) : t in Terms(f)];
          e012 := [e : e in exps | e[1] le 2];
          assert #[0: e in e012 | e[1] le 1] gt 0;
          k := Min([(e[1]^2+2)*(e[2]-1) : e in e012]);
	  assert k+3 le mu;
          es := [e : e in e012 | (e[1]^2+2)*(e[2]-1) eq k];
          f0 := (R0.1^3)*R0.2+
	    &+[MonomialCoefficient(f,m)*m where m is Monomial(R0,e) : e in es];
	  pol := Evaluate(f0,[PolynomialRing(K).1,1]);
	  a := Coefficient(pol,2); lc := LeadingCoefficient(pol);
	  if not (pol eq  ((Parent(pol).1)+(a/3))^3) then break; end if;
	  assert IsDivisibleBy(k,6);
	  tr1 := [x-(a/3)*y^(k div 6),y];
	  f := Evaluate(f,tr1); tr := [Evaluate(e,tr1) : e in tr];
        end while;
        if IsDivisibleBy(k,6) then // Types Z_{(k/6)-1,j} some j >=0
	  j := mu-3-k;
	  typstr := "Z_{" cat IntegerToString((k div 6)-1) cat "," cat
		IntegerToString(j) cat "}";
        else // types Z_{6r+i} i = -1,0,1
	  assert #es eq 1;
	  typstr := "Z" cat IntegerToString(k+3);
	  wts := (IsEven(k) select [k div 2, 3] else [k div 3, 2]);
	  error if (p gt 0) and IsDivisibleBy((IsEven(k) select wts[1] else k+1)+1,p),
		typstr cat errstr;
        end if;

	// Now convert to normal form
        if not IsDivisibleBy(k,6) then
          assert k+3 eq mu;
	  if (not get_trans) and (k le 10) then return 
	    true,f0,typstr;
	  end if;
	  R1 := PolynomialRing(K,wts,"grevlexw",wts);
	  d1 := 4*wts[1];
	  dord := (IsEven(k) select wts[1]+1 else 2*wts[1]);
	  dord1 := (IsEven(k) select (4*wts[1]) div 3 else 2*wts[1]);
	  // need to expand more?
	  if boofd then
	    if dmax lt dord1 then
	      f := expand_to_prec_with_quadratic_part(fdata,dord1,R0);
	      f := Evaluate(f,tr);
	    end if;
	  end if;
	  if get_trans and (d gt 3) then d1 := d*wts[1]; end if;
	  f,tr1 := qh_transform_to_normal_form(R1!f,R1!f0,d1 : get_trans := get_trans,
				ord_deg := Max(d,dord1));
	  if not get_trans then
	    return true,R0!f,typstr;
	  else
	    tr := trunc_comp(tr,[R0!a : a in tr1],Max(d,dord)-3);
	    return true,R0!f,typstr,hom<R0->R0|tr>;
	  end if;	
        else //Z_{k,j} families
	  // handle Z_{k-1,0} first, which is a semiquasihomogeneous case
	  k := k div 6;
	  error if (p gt 0) and ( IsDivisibleBy(3*k+1,p) or 
			((j gt 0) and IsDivisibleBy(2*(3*k+j+1),p)) ),
	    typstr cat errstr;
	  // do we need to expand further?
	  if boofd and (dmax lt (4*k+j)) then
	    f := expand_to_prec_with_quadratic_part(fdata,4*k+j,R0);
	    f := Evaluate(f,tr);
	    f0 :=(R0.1^3)*R0.2+
	       &+[MonomialCoefficient(f,m)*m where m is Monomial(R0,[i,(3-i)*k+1]) : 
			i in [0..2]];
	  end if;
	  pol := Evaluate(f0,[PolynomialRing(K).1,1]);

	  if j eq 0 then
	    if Discriminant(pol) eq 0 then
	      assert p eq 2;
	      error "Bad " cat typstr cat errstr;
	    end if;
            // Usual Arnold normal form transforms f0 to y(x^3+b*x^2*y^k+y^3k). To
            // avoid unnecessary field extns we will generally use the alternative
	    // y(x^3+b*x*y^2k+c*y^3k), c != 0 (which when x,y are appropriately scaled
	    // -> y(x^3+b*x*y^2k+y^3k)). In a single case, (when we transform to the above
	    // and c = 0), we use the first form (unscaled as y(x^3+ b*x^2*y^k+c*y^3k))
	    // after a possible quadratic extension of the base field.
	    // This is always with char != 2 and -> the single isomorphism class
	    // y(x^3+(3/u)*x^2*y^k+y^3k) where u^3=2.
	    b := Coefficient(pol,2);
	    u := (b ne 0) select -b/3 else K!0;
	    boo := true; boo1 := true;
	    if Evaluate(pol,u) eq 0 then
	      boo1 := false;
	      c := Coefficient(pol,1);
	      v := -(c+b*u)/3;
	      boo,u1 := IsSquare(v);
	      if boo then u +:= u1;
	      else
	        K1 := ext<K|PolynomialRing(K)![-v,0,1]>;
	        u := (K1!u)+K1.1;
	      end if;
	    end if;
	    R1 := boo select R0 else ChangeRing(R0,K1);
	    if not IsZero(u) then	    
	      seq := [(R1.1)+u*(R1.2)^k,R1.2];
              f := Evaluate(f,seq);
	      f0 := Evaluate(f0,seq);
	      tr := [Evaluate(e,seq) : e in tr];
	    end if;
	    // get "Groebner shift" data for transformation to normal forms
	    R2 := PolynomialRing(BaseRing(R1),[k,1],"grevlexw",[k,1]);
	    c := MonomialCoefficient(f,Monomial(R1,[0,3*k+1]));
	    assert not IsZero(c);
	    if boo1 then
	      b := MonomialCoefficient(f,Monomial(R1,[1,2*k+1]));
	      gs := [];
	      if not IsZero(2*b) then
	        gs := [[Monomial(R2,[0,3*k+1]),-((2*b)/(3*c))*Monomial(R2,[1,2*k+1])]];
	      end if;
	    else
	      b := MonomialCoefficient(f,Monomial(R1,[2,k]));
	      assert not IsZero(2*b);
	      gs := [[Monomial(R2,[0,3*k+1]),((2*b^2)/(9*c))*Monomial(R2,[1,2*k+1])]];
	    end if;
	    d1 := 4*k;
	    if get_trans and (d gt 3) then d1 := d*k; end if;
	    f,tr1 := qh_transform_to_normal_form(R2!f,R2!f0,d1 : groebner_shift := gs, get_trans := get_trans, ord_deg := Max(d,4*k));
	    if not get_trans then
	      return true,R1!f,typstr;
	    else
	      tr := trunc_comp(tr,[R1!a : a in tr1],Max(d,4*k)-3);
	      return true,R1!f,typstr,hom<R0->R1|tr>;
	    end if;		  
	  end if;
	  // j > 0 cases not semiquasihomogeneous!
	  if not IsZero(Discriminant(pol)) then
	    error "Bad " cat typstr cat errstr;
	  end if;
	  // transform weight 3*k+1 (for (x,y) wts (k,1)) part to y(x^3+bx^2y^k)
	  pol1 := GCD(pol,Derivative(pol));
	  assert Degree(pol1) eq 1;
	  p0 := Coefficient(pol1,0); //NB: pol1 is monic
	  if not IsZero(p0) then
	    tr1 := [x-p0*y^k,y];
	    f := Evaluate(f,tr1); tr := [Evaluate(e,tr1) : e in tr];
	  end if;
	  f0 := x^3*y+MonomialCoefficient(f,m)*m where m is Monomial(R0,[2,k+1]);
	  R1 := PolynomialRing(BaseRing(R0),[k,1],"grevlexw",[k,1]);
	  _,tr1 := qh_transform_to_normal_form(R1!f,R1!f0,3*k+j+1);
	  f := Evaluate(f,[R0!a : a in tr1]);
	  if get_trans then tr := [Evaluate(e,[R0!a : a in tr1]) : e in tr]; end if;
	  // f should now be in the form y(x^3+ax^2y^k+by^(3k+j))+O(deg 3k+j+2)
	  //  for the weighted degree where the (x,y) weights are (k,1)
	  tf0 := [t : t in Terms(f) | Exponents(t)[1] eq 0];
	  boo := (#tf0 gt 0);
	  if boo then
	    t0 := Min(tf0);
	    boo := (Exponents(t0) eq [0,3*k+j+1]);
	  end if;
	  error if not boo, "Bad " cat typstr cat errstr;
	  f0 +:= t0;
	  a := MonomialCoefficient(f0,Monomial(R0,[2,k+1])); b := LeadingCoefficient(t0);
	  R1 := PolynomialRing(BaseRing(R0),2,"grevlex");
	  x := R1.1; y := R1.2;
	  a1 := (2*a)/3; b1 := (k+1)*a; c1 := (3*k+j+1)*b; u := a1*(b1-a1);
	  m_t := [ <[x^3,a1*b1*x*y^(2*k)-c1*y^(3*k+j)],[(-b1/3)*y^(k-1),R1!1]>,
		<[x^2*y,-a1*x*y^(k+1)],[R1!(1/3),0]>,
	    <[x*y^(2*k+1),(c1/u)*y^(3*k+j+1)], [(1/u)*((1/3)*(x+(b1-a1)*y^k)),(-1/u)*y]>,
	    <[y^(4*k+j+1),(-c1/(u*a1))*y^(4*k+2*j+1)],[(-1/(3*a1*c1*u))*(u*x^2+b1*u*x*y^k+
		c1*x*y^(k+j)+c1*(b1-a1)*y^(2*k+j)),
		(1/(a1*c1*u))*(u*x*y+a1*u*y^(k+1)+c1*y^(k+j+1))]> ];
	  f,tr1 := special_transform_to_normal_form(R1!f,R1!f0,Max(d,4*k+j), 
			m_t : get_trans := get_trans);
	  f := R0!f;
	  if not get_trans then
	    return true,f,typstr;
	  else
	    tr := trunc_comp(tr,[R0!a : a in tr1],Max(d,4*k+j)-3);
	    return true,f,typstr,hom<R0->R0|tr>;
	  end if;
	end if;
      end if;
      // typ = 5 : f = ax^4+O(deg 5)
      error if p eq 2, "x^4+O(deg 5) singularity in characteristic 2";
      x := R0.1; y := R0.2;
      // First determine the family.
      while true do
	exps := [Exponents(t) : t in Terms(f)];
	e0123 := [e : e in exps | e[1] le 3];
	assert #[0: e in e0123 | e[1] le 1] gt 0;
	k := Min([(12 div (4-e[1]))*e[2] : e in e0123]);
	assert k le mu+3;
	es := [e : e in e0123 | (12 div (4-e[1]))*e[2] eq k];
	f0 := MonomialCoefficient(f,R0.1^4)*R0.1^4+
	    &+[MonomialCoefficient(f,m)*m where m is Monomial(R0,e) : e in es];
	pol := Evaluate(f0,[PolynomialRing(K).1,1]);
	a := Coefficient(pol,3); lc := LeadingCoefficient(pol);
	if not (pol eq  lc*((Parent(pol).1)+(a/(4*lc)))^4) then break; end if;
	assert IsDivisibleBy(k,12);
	tr1 := [x-(a/(4*lc))*y^(k div 12),y];
	f := Evaluate(f,tr1); tr := [Evaluate(e,tr1) : e in tr];
      end while;
      if IsDivisibleBy(k,12) then // X_{k,i}, Y^k{i,j} and Z^k_{i,j} families
	//error "Sorry. This appears to be an X_{k,i}, Y^k_{i,j}, Z^k_i or Z^k_{i,j} ",
	 //"(k >= 2) corank 2 singularity. We haven't fully implemented these families yet.";
	// determine family
	i := mu+3-k;
	k := k div 12;
	Rp := Parent(pol);
	R := R0;
	deg := Max(d,6*k+i-2);
	if not IsZero(Discriminant(pol)) then // X_{k,0}
	  typstr := "X_{" cat IntegerToString(k) cat "," cat "0}";
	  error if (i gt 0) or ((p gt 0) and IsDivisibleBy(3*k,p)), typstr cat errstr;
	  if boofd and (dmax lt 6*k-2) then
	    f := expand_to_prec_with_quadratic_part(fdata,6*k+i-2,R0);
	    f := Evaluate(f,tr);
	  end if; 
	  f,tr1 := Xk0case(f,k,Max(d*k,6*k-2),get_trans);
	  R :=Parent(f); // base field may have been extended
	else
	  rts := Roots(pol);
	  if #rts eq 0 then // Y^k_{r,s} - p(x)^2 case for p irred of degree 2
	    assert pol eq a*(Rp.1^2+b*Rp.1+c)^2 where 
		c is ((Coefficient(pol,2)/a)-b^2)/2 where
		b is Coefficient(pol,3)/(2*a) where a is LeadingCoefficient(pol);
	    try
	      f,tr1 := Ykrscase(f,k,i,dmax,boofd 
	  		  : fd := fdata, get_trans := get_trans);
	    catch e
	      error expnstr cat typstr cat errstr;
	    end try; 	    
	  else
	    if #[1: r in rts | r[2] ge 2] gt 1 then
		//Y^k_{r,s} - split leading polynomial
		assert (#rts eq 2);
		tr1 := [x+rts[1][1]*y^k,y];
		f := Evaluate(f,tr1); tr := [Evaluate(e,tr1) : e in tr];
	    	/*try
	          f,tr1 := Ykrscase(f,k,i,dmax,boofd 
	  		  : fd := fdata, get_trans := get_trans);
	    	catch e
	          error expnstr cat typstr cat errstr;
	    	end try;*/
		error "Sorry. This is a (Y^" cat IntegerToString(k) cat 
			")-family singularity for which we don't",
			"yet have normal form code";
	    else
		m,ind := Max([r[2] : r in rts]);
		if (m eq 1) or ((m eq 3) and (p eq 3)) then // char 3 bad case
		  assert p eq 3;
		  error "Bad Z^" cat IntegerToString(k) cat "_.." cat errstr;
		end if;
		assert m le 3;
		tr1 := [x+rt[1]*y^k,y] where rt is [r : r in rts | r[2] eq m][1];
		f := Evaluate(f,tr1); tr := [Evaluate(e,tr1) : e in tr];
		if m eq 2 then //X_{k,i} case
	    	  typstr := "X_{" cat IntegerToString(k) cat "," cat IntegerToString(i)
				cat "}";
		  error if ((p gt 0) and IsDivisibleBy(k*(4*k+i),p)), typstr cat errstr;
	    	  // need to expand more?
	    	  if boofd and (dmax lt 6*k+i-2) then
	      	    f := expand_to_prec_with_quadratic_part(fdata,6*k+i-2,R0);
	      	    f := Evaluate(f,tr);
	    	  end if; 
	    	  try
	            f,tr1 := Xkrcase(f,k,i,deg,get_trans); 
	    	  catch e
	            error "Bad " cat typstr cat errstr;
	    	  end try;
		else // m eq 3, char != 3 - Z^k families
		  // normal form code not ready yet
		  error "Sorry. This is a (Z^"cat IntegerToString(k) cat 
			")-family singularity for which we don't",
			"yet have normal form code";
	    	  /*try
	            f,tr1 := Zkcases(f,k,i,dmax,boofd,get_trans 
	  		  : fd := fData, deg := 6*k+i);
	    	    catch e
	              error e; //expnstr cat typstr cat errstr;
	    	    end try;*/
		end if;
	    end if; 	 		
	  end if;
	end if;
	if not get_trans then
	    return true,f,typstr;
	else
	    tr := trunc_comp(tr,tr1,deg-3);
	    return true,f,typstr,hom<R->R|tr>;
	end if;
      elif IsDivisibleBy(k,6) then  // W_{k,i} families
	i := mu+3-k;
	wts := [k div 6,2];
	// 3 possible cases: W_{k,0}, W_{k,i}, W#_{k,i} i > 0
	//  - the index k here is s.t. wts[1]=2k+1
	a := MonomialCoefficient(f0,Monomial(R0,[2,wts[1]]));
	b := MonomialCoefficient(f0,Monomial(R0,[0,2*wts[1]]));
	c := MonomialCoefficient(f0,Monomial(R0,[4,0]));
	// f0 = c*x^4+a*x^2*y^(2k+1)+b*y^(4k+2)
	R1 := PolynomialRing(K,wts,"grevlexw",wts);
	k := wts[1] div 2;
	if IsZero(b) then // W_{k,i}
	  assert not IsZero(a) and (i gt 0);
	  typstr := "W_{" cat IntegerToString(k) cat "," cat
				IntegerToString(i) cat "}";
	  error if (p gt 0) and IsDivisibleBy((2*wts[1]+i)*wts[1],p), typstr cat errstr;
	  // need to expand more?
	  d1 := Max(d,3*wts[1]+i-2);
	  if boofd and (dmax lt d1) then
	    f := expand_to_prec_with_quadratic_part(fdata,d1,R0);
	    f := Evaluate(f,tr);
	  end if; 
	  // first transform: to cx^4+ax^2y^(2k+1)+x^3y^(k+1)(a0+..+a(k-2)y^(k-2)) 
	  //   +by^(4k+2+i) mod deg 4k+3+i
	  gs := [[Monomial(R1,[1,wts[1]]),(-2*c/a)*Monomial(R1,[3,0])]];
	  _,tr1 := qh_transform_to_normal_form(R1!f,R1!f0,4*wts[1]+2*i : 
				groebner_shift := gs, ord_deg := 2*wts[1]+i);
	  f := trunc_comp([f],[R0!a : a in tr1],d1)[1];
	  if get_trans then tr := trunc_comp(tr,[R0!a : a in tr1],d1-3); end if;
	  // f should now be in the form cx^4+ax^2y^(2k+1)+by^(4k+2+i)+
	  //  x^3y^(k+1)(a0+..+a(k-2)y^(k-2))+O(deg 4k+i+2)
	  //  for the weighted degree where the (x,y) weights are (2k+1,2)
	  tf0 := [t : t in Terms(f) | Exponents(t)[1] eq 0];
	  boo := (#tf0 gt 0);
	  if boo then
	    t0 := Min(tf0);
	    boo := (Exponents(t0) eq [0,2*wts[1]+i]);
	  end if;
	  error if not boo, "Bad " cat typstr cat errstr;
	  f0 +:= t0;
	  b := LeadingCoefficient(t0);
	  R1 := PolynomialRing(BaseRing(R0),2,"grevlex");
	  x := R1.1; y := R1.2;
	  a1 := a/(2*c); b1 := ((4*k+i+2)*b)/((2*k+1)*a); u := 1/((2*k+1)*a);
	  m_t := [ <[x^4,-a1*x^2*y^(2*k+1)],[(1/(4*c))*x,0]>,
		<[x^2*y^(2*k),-b1*y^(4*k+i+1)],[0,R1!u]>,
	    <[x*y^(4*k+1),(b1/a1)*x*y^(4*k+i+1)], [(1/(2*a))*y^(2*k),(-u/a1)*x]>,
	    <[x*y^(2*k+1),(-1/a1)*x^3],[R1!(1/(2*a)),0]>,
	    <[y^(6*k+i+2),(b1/a1)*y^(6*k+2*i+2)],[(-1/(2*a*b1))*x*y^(2*k),
		(u/(a1*b1))*(x^2+a1*y^(2*k+1)-b1*y^(2*k+i+1))]> ];
	  f,tr1 := special_transform_to_normal_form(R1!f,R1!f0,d1, 
			m_t : get_trans := get_trans);
	  f := R0!f;
	  if not get_trans then
	    return true,f,typstr;
	  else
	    tr := trunc_comp(tr,[R0!a : a in tr1],d1-3);
	    return true,f,typstr,hom<R0->R0|tr>;
	  end if;
	elif not IsZero(a^2-4*b*c) then // W_{k,0}
	  typstr := "W_{" cat IntegerToString(k) cat ",0}";
	  error if (p gt 0) and IsDivisibleBy(wts[1],p), typstr cat errstr;
	  assert i eq 0;
	  // need to expand more?
	  if boofd and (dmax lt 2*wts[1]) then
	    f := expand_to_prec_with_quadratic_part(fdata,2*wts[1],R0);
	    f := Evaluate(f,tr);
	  end if; 
	  gs := IsZero(a) select [] else
		[[Monomial(R1,[0,4*k+1]),(-a/(2*b))*Monomial(R1,[2,2*k])]];
	  d1 := 6*wts[1]-4;
	  if get_trans and (d gt 4) then d1 := Max(d*wts[1],d1); end if;
	  f,tr1 := qh_transform_to_normal_form(R1!f,R1!f0,d1 : get_trans := get_trans, 
				groebner_shift := gs, ord_deg := Max(d,3*wts[1]-2));
	  if not get_trans then
	    return true,R0!f,typstr;
	  else
	    tr := trunc_comp(tr,[R0!a : a in tr1],Max(d,2*wts[1])-3);
	    return true,R0!f,typstr,hom<R0->R0|tr>;
	  end if;
	else // W#_{k,i}
	  // f0 = c(x^2+(a/(2c))y^(2k+1))^2
	  assert i gt 0;
	  typstr := "W#_{" cat IntegerToString(wts[1] div 2) cat "," cat
				IntegerToString(i) cat "}";
	  error if (p gt 0) and IsDivisibleBy((4*wts[1]+i)*wts[1],p), typstr cat errstr;
	  q := (i+1) div 2;
	  // need to expand more?
	  d1 := Max(d,IsEven(i) select 6*k+1+q else 5*k+1+Max(k,q));
	  if boofd and (dmax lt d1) then
	    f := expand_to_prec_with_quadratic_part(fdata,d1,R0);
	    f := Evaluate(f,tr);
	  end if; 
	  // first transform: to c(x^2+(a/(2c))y^(2k+1))^2+(by^(3k+1+q)[i odd])
	  //   (+bx^2y^(2k+1+q))[i even]) + higher deg for the [2k+1,2] weights
	  if IsEven(i) then 
	    gs := [[Monomial(R1,[0,4*k+1]),(-2*c/a)*Monomial(R1,[2,2*k])]];
	  else gs := [];
	  end if;
	  _,tr1 := qh_transform_to_normal_form(R1!f,R1!f0,4*wts[1]+i : 
		groebner_shift := gs, ord_deg := 4*k+2+(i div 2));
	  f := trunc_comp([f],[R0!a : a in tr1],d1)[1];
	  if get_trans then tr := trunc_comp(tr,[R0!a : a in tr1],d1-3); end if;
	  // f should now be in the form as given above
	  tf0 := [t : t in Terms(R1!(f-f0)) | WeightedDegree(t) le 4*wts[1]+i];
	  boo := (#tf0 eq 1);
	  if boo then
	    t0 := tf0[1];
	    boo := (Exponents(t0) eq (IsEven(i) select [2,wts[1]+q] else [1,wts[1]+k+q]));
	  end if;
	  error if not boo, "Bad " cat typstr cat errstr;
	  f0 +:= R0!t0;
	  b := LeadingCoefficient(t0);
	  x := R1.1; y := R1.2;
	  if IsEven(i) then
	    a1 := a/(2*c); b1 := b/(2*c); c1 := (wts[1]+q)*b/(wts[1]*a); u := 1/(a1*c1+b1);
	    m_t := [ <[x^3,-a1*x*y^(2*k+1)-b1*x*y^(2*k+1+q)],[R1!(1/(4*c)),0]>,
		<[x*y^(4*k+1+q),(-b1*c1*u)*x*y^(4*k+1+2*q)],
		  [(u/(4*c))*(y^(2*k)+c1*y^(2*k+q)),(-u/((2*k+1)*a))*x]>,
		<[y^(4*k+1+q),(-1/a1)*x^2*y^(2*k+q)-(c1/a1)*x^2*y^(2*k+2*q)],
		  [R1!0,((2*c)/((2*k+1)*a^2))*y^q]> ];
	  else
	    a1 := a/(2*c); b1 := b/(4*c); c1 := (3*k+1+q)*b/((2*k+1)*a); u := 1/(a1*c1+b1);
	    m_t := [<[x^3,-a1*x*y^(2*k+1)-b1*y^(3*k+1+q)],[R1!(1/(4*c)),0]>,
		<[x^2*y^(2*k),-c1*x*y^(3*k+q)-a1*y^(4*k+1)],[0,R1!(1/((2*k+1)*a))]>,
		<[x*y^(5*k+1+q),u^2*b1*c1^3*x*y^(5*k+3*q)],
		[(u^2/(4*c))*((1/u)*x*y^(2*k)+a1*c1^2*y^(3*k+q)),(u^2/((2*k+1)*a))*
		  (-(1/u)*x^2+b1*c1*x*y^(k+q)-b1*c1^2*y^(2*k+2*q))]>,
		<[y^(5*k+1+q),-u*c1^2*x*y^(4*k+2*q)],[(u/(4*c))*y^(2*k),
		  (-u/((2*k+1)*a))*(x-c1*y^(k+q))]> ];
	  end if;
	  try
	    f,tr1 := general_transform_to_normal_form(R1!f,R1!f0,d1, 
	  		m_t : get_trans := get_trans);
	  catch e
	    error expnstr cat typstr cat errstr;
	  end try;
	  f := R0!f;
	  if not get_trans then
	    return true,f,typstr;
	  else
	    tr := trunc_comp(tr,[R0!a : a in tr1],d1-3);
	    return true,f,typstr,hom<R0->R0|tr>;
	  end if;
	end if;
      else // W_k family
	assert #es eq 1;
	typstr := "W" cat IntegerToString(k-3);
	wts := (IsEven(k) select [k div 4, 3] else [k div 3, 4]);
	error if (p gt 0) and IsDivisibleBy(wts[1],p), typstr cat errstr;
	assert k eq mu+3;
	// need to expand more?
	dord := (IsOdd(k) select wts[1] else 2*(wts[1]-1));
	dord1 := (IsOdd(k) select 3*(wts[1] div 2) else 2*(wts[1]-1));
	if IsEven(k) and boofd then
	  if dmax lt dord1 then
	    f := expand_to_prec_with_quadratic_part(fdata,dord1,R0);
	    f := Evaluate(f,tr);
	  end if;
	end if;
	R1 := PolynomialRing(K,wts,"grevlexw",wts);
	d1 := 6*wts[1]-(IsEven(k) select 6 else 8);
	if get_trans and (d gt 4) then d1 := Max(d*wts[1],d1); end if;
	f,tr1 := qh_transform_to_normal_form(R1!f,R1!f0,d1 : get_trans := get_trans,
			ord_deg := Max(d,dord1));
	if not get_trans then
	  return true,R0!f,typstr;
	else
	  tr := trunc_comp(tr,[R0!a : a in tr1],Max(d,dord)-3);
	  return true,R0!f,typstr,hom<R0->R0|tr>;
	end if;
      end if;
    end if;

    j5f := &+[R0|t : t in Terms(f) | LeadingTotalDegree(t) eq 5];

    if j5f ne 0 then
	if mu ne 16 then return false,_,_,_; end if;
	// j5f is non-degenerate - for the moment, don't bother
	//  linearly transforming it to a particular form.
	
	// need to expand more?
	if boofd and (dmax lt 6) then
	    f := expand_to_prec_with_quadratic_part(fdata,6,R0);
	end if;
	R1 := PolynomialRing(K,2,"grevlex");
	f1,tr := qh_transform_to_normal_form(R1!f,R1!j5f,Max(d,6) : 
			get_trans := get_trans);
	if get_trans then
	  return true,R0!f1,"N16",hom<R0->R0|[R0!e : e in tr]>;
	else
	  return true,R0!f1,"N16";
	end if;
    end if;
      
end intrinsic;

