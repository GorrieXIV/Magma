freeze;

///////////////////////////////////////////////////////////////////////
///  Functions to deal with the classification and transformation   ///
///      to normal form (according to Arnold's scheme) of           ///
///        Corank 3 isolated hypersurface singularities.            ///
///                    mch - 11/14                                  ///
///////////////////////////////////////////////////////////////////////

import "norm_form_of_sing.m": qh_transform_to_normal_form, trunc_comp,
		expand_to_prec_with_quadratic_part;
import "corank2.m": normalise_deg_3_homog_poly,special_transform_to_normal_form;

function hyperbolic_case_relations(f)
// f should be a*x^p1+b*y^p2+c*z^p3+xyz with abc != 0 and
// 3<= p1 <= p2 <= p3, p3 > 3 in k[x,y,z], char(k) not dividing p1*p2*p3
// (and, ideally, with x,y,z weighted : wt(x)=p2p3, wt(y)=p1p3, wt(z)=p1p2.
// Returns the appropriate mon_trans data for transformation to normal form.

    R := Generic(Parent(f));
    x,y,z := Explode([R.i : i in [1..3]]);
    p1,p2,p3 := Explode([(#Coefficients(f,R.i))-1 : i in [1..3]]);
    assert &and[p ge 3: p in [p1,p2,p3]] and (#Terms(f) eq 4)
	and IsOne(MonomialCoefficient(f,x*y*z));
    a,b,c := Explode([MonomialCoefficient(f,m) : m in [x^p1,y^p2,z^p3]]);
    assert not IsZero(a*b*c);

    tr1 := [<[x*y,-(p3*c)*z^(p3-1)],[R|0,0,1]>,
	    <[x*z,-(p2*b)*y^(p2-1)],[R|0,1,0]>,
	    <[y*z,-(p1*a)*x^(p1-1)],[R|1,0,0]>];

    tr2 := [<[x^(p1+1),-((p2*b)*(p3*c)/(p1*a))*(y^(p2-1)*z^(p3-1))],
		[(1/(p1*a))*x^2,((p3*c)/(p1*a))*z^(p3-1),(-1/(p1*a))*(x*z)]>,
	    <[y^(p2+1),-((p1*a)*(p3*c)/(p2*b))*(x^(p1-1)*z^(p3-1))],
		[((p3*c)/(p2*b))*z^(p3-1),(1/(p2*b))*y^2,(-1/(p2*b))*(y*z)]>,
	    <[z^(p3+1),-((p1*a)*(p2*b)/(p3*c))*(x^(p1-1)*y^(p2-1))],
		[((p2*b)/(p3*c))*y^(p2-1),(-1/(p3*c))*(y*z),(1/(p3*c))*z^2]>];

    // note that all relations give m1 -> m2 where wt(m2)-wt(m1)=
    // p1p2p3-p1p2-p1p3-p2p3>0 for the ideal weighting.

    tr := (p2 gt p1) select [tr2[1],tr1[1]] else [tr1[1],tr2[1]];
    if p1+p3 gt 2*p2 then
	tr cat:= [tr2[2],tr1[2],tr1[3],tr2[3]];
    else
      if p2 eq p3 then
	 tr cat:= [tr1[2],tr1[3],tr2[2],tr2[3]];
      else
	 tr cat:= [tr1[2],tr2[2],tr1[3],tr2[3]];
      end if;
    end if;
    return tr;
	   
end function;

function move_sing_pt(f,J)
// f is a homogeneous cubic in x,y,z which is an irreducible conic+tangent line
// or three lines (maybe conjugate over an extension of the base field)
// that all meet in one point. J is the Jacobian ideal of f.
// Apply a linear trans phi to move the singular point to [0,1,0]
// and return phi(f),[phi(x),phi(y),phi(z)]

    R := Generic(Parent(f)); k := BaseRing(R);
    x := R.1; y := R.2; z := R.3;	
    P := ProjectiveSpace(k,2);
    supp := Support(Cluster(P,[CoordinateRing(P)!e : e in Basis(J)]));
    assert #supp eq 1;
    p := Eltseq(Representative(supp));
    if IsZero(p[2]) then
	if IsZero(p[3]) then
	  tr := [y,x,z]; f := Evaluate(f,tr);
	  p := [k|0,1,0]; 
	else
	  tr := [x,z,y]; f := Evaluate(f,tr);
	  p[2] := p[3]; p[3] := k!0;
	end if;
    else
	tr := [x,y,z];
    end if;
    seq := [x+(p[1]/p[2])*y,y,z+(p[3]/p[2])*y];
    tr := [Evaluate(t,seq) : t in tr]; f := Evaluate(f,seq);
    return f,seq;
  
end function;

function crk3_normalise_deg_3_homog_poly(f)
// char(k) !=2,3, f a homogeneous degree 3 poly in k[x,y,z].
// Returns f1,tr,typ where tr = [L(x),L(y),L(z)] for a linear
// isomorphism L (possibly over a finite extn. k1 of k) s.t.
// f1=f(L(x),L(y),L(z)) is a normal form of type typ.

    R := Generic(Parent(f)); k := BaseRing(R);
    x := R.1; y := R.2; z := R.3;
    J := ideal<R|[f] cat [Derivative(f,i) : i in [1..3]]>;

    if Dimension(J) eq 0 then //f a non-singular homog. cubic
      // normal form should be ax^3+by^3+cz^3+dxyz. However,
      // we won't transform it here.
      return f,[x,y,z],1;
    elif Dimension(J) eq 1 then //Z(f) < P^2 has finitely many singular points
	d := Integers()!(Coefficient(HilbertPolynomial(J),0));
	assert d le 4;
	if d eq 1 then //irreducible with one node
	  f,tr := move_sing_pt(f,J); // translate singular point to [0,1,0]
	  // then to [0,0,1]
	  seq := [x,z,y];
	  f := Evaluate(f,seq); tr := [Evaluate(e,seq) : e in tr];
	  a,b,c := Explode([MonomialCoefficient(f,m*z) : m in [x^2,x*y,y^2]]);
	  boo,u := IsSquare(b^2-4*a*c);
	  assert not (boo and IsZero(u));
	  if boo then
	    R1 := R;
	  else
	    k1<u> := ext<k|PolynomialRing(k)![4*a*c-b^2,0,1]>;
	    R1 := ChangeRing(R,k1); f := R1!f; tr := [R1!e : e in tr];
	    x,y,z := Explode([R1.i : i in [1..3]]);
	  end if;
	  if IsZero(a*c) then
	    if IsZero(c) then
	      seq := [x,y-(a/b)*x,z];
	    else
	      seq := [x-(c/b)*y,y,z];
	    end if;
	  else
	    seq := [(1/(2*a))*((x+y)-(b/u)*(x-y)),(1/u)*(x-y),z];
	  end if;
	  f := Evaluate(f,seq); tr := [Evaluate(e,seq) : e in tr];
	  a,b,c := Explode([MonomialCoefficient(f,m*x*y) : m in [z,x,y]]);
	  assert not IsZero(a);
	  seq := [x,y,(1/a)*(z-b*x-c*y)];
	  f := Evaluate(f,seq); tr := [Evaluate(e,seq) : e in tr];
	  assert #Terms(f) eq 3;
	  return f,tr,2; // f=A*x^3+B*y^3+x*y*z, A,B != 0
	elif d eq 2 then
	  J1 := Saturation(J);
	  if IsRadical(J1) then //conic+non-tangent line
	    // first transform the 2 singular points to [0,1,0] and [0,0,1],
	    // after a quadratic field change if necessary
	    P := ProjectiveSpace(k,2);
	    pts := Cluster(P,[CoordinateRing(P)!e : e in Basis(J1)]);
            if #Support(pts) eq 0 then
		B := MinimalBasis(Saturation(EliminationIdeal(J1,1)));
	        assert #B eq 1;
	        pol := Evaluate(B[1],[1,S.1,1]) where S is PolynomialRing(k);
	        k := SplittingField(pol);
		R1 := ChangeRing(R,k); f := R1!f;
		x,y,z := Explode([R1.i : i in [1..3]]);
		P := ProjectiveSpace(k,2);
		pts := Cluster(P,[CoordinateRing(P)!e : e in Basis(J1)]);
	    end if;
	    supp := Support(pts);
	    assert #supp eq 2;
	    pts := [Eltseq(p) : p in supp];
	    seq := [k|0,0];
	    for i in [1..3] do 
	      mat := Matrix([Insert(seq,i,k!1)] cat pts);
	      if not IsZero(Determinant(mat)) then break; end if;
	    end for;
	    tr := [Polynomial(r,[x,y,z]) : r in RowSequence(Transpose(mat))];
	    f := Evaluate(f,tr);
	    a,b,c := Explode([MonomialCoefficient(f,m*x) : m in [y*z,x*y,x*z]]);
	    assert not IsZero(a);
	    seq := [x,y-(c/a)*x,(1/a)*(z-b*x)];
	    f := Evaluate(f,seq); tr := [Evaluate(e,seq) : e in tr];
	    assert (#Terms(f) eq 2) and (not IsZero(MonomialCoefficient(f,x^3))) and
			IsOne(MonomialCoefficient(f,x*y*z));
	    return f,tr,3; // f=A*x^3+x*y*z, A != 0
	  else //irreducible with one cusp
	    f,tr := move_sing_pt(f,J1); // translate singular point to [0,1,0]
	    a,b,c := Explode([MonomialCoefficient(f,m*y) : m in [x^2,x*z,z^2]]);
	    assert IsZero(b^2-4*a*c);
	    if not IsZero(a) then
	      if IsZero(c) then
		seq := [z,y,x];
	      else
		seq := [x,y,z-(b/(2*c))*x];
	      end if;
	      f := Evaluate(f,seq); tr := [Evaluate(e,seq) : e in tr];
	    end if;
	    // f is now c*y*z^2+p(x,z) where p is homogeneous of degree 3.
	    // First remove the x^2*z term
	    a := MonomialCoefficient(f,x^3);
	    assert not IsZero(a); // a=0 => f=z*F is not irreducible
	    b := MonomialCoefficient(f,x^2*z);
	    if not IsZero(b) then
	      seq := [x-(b/(3*a))*z,y,z];
	      f := Evaluate(f,seq); tr := [Evaluate(e,seq) : e in tr];
	    end if;
	    a,b,c := Explode([MonomialCoefficient(f,m*z^2) : m in [y,x,z]]);
	    seq := [x,(1/a)*(y-b*x-c*z),z];
	    f := Evaluate(f,seq); tr := [Evaluate(e,seq) : e in tr];
	    return f,tr,5; // f=A*x^3+y*z^2, A != 0
	  end if;
	elif d eq 3 then
	  if IsRadical(J) then //3 distinct non-concurrent lines (maybe Galois conj)
	    // first get a splitting field over which all lines are defined
	    // J defines the three intersection points of the lines in P^2.
	    //  Get the field by 'projecting to a line'.
	    B := MinimalBasis(Saturation(EliminationIdeal(J,1)));
	    assert #B eq 1;
	    pol := Evaluate(B[1],[1,S.1,1]) where S is PolynomialRing(k);
	    k1 := SplittingField(pol);
	    if not (k cmpeq k1) then
	      R1 := ChangeRing(R,k1); f := R1!f;
	    else R1 := R; end if;
	    ls := [e[1] : e in Factorisation(f)];
	    assert #ls eq 3;
	    lc := f div &*ls;
	    tr_mat := Matrix([[MonomialCoefficient(l,R1.i) : i in [1..3]] : l in ls]);
	    tr_mat := tr_mat^-1; 
	    for i in [1..3] do tr_mat[i,1] *:= lc; end for;
	    tr := [Polynomial(r,[R1.i : i in [1..3]]) : r in RowSequence(tr_mat)];
	    return &*[R1.i : i in [1..3]],tr,4; // f=x*y*z    
	  else //conic+tangent line
	    f,tr := move_sing_pt(f,J); // translate singular point to [0,1,0]
	    fs := [f[1] : f in Factorisation(f)];
	    assert #fs eq 2;
	    if Degree(fs[1]) gt Degree(fs[2]) then
	      Reverse(~fs);
	    end if;
	    assert (Degree(fs[1]) eq 1) and (Degree(fs[2]) eq 2);
	    F := fs[2]; l := f div F;
	    cs := [MonomialCoefficient(l,R.i) : i in [1..3]];
	    j := [i : i in [1..3] | not IsZero(cs[i])][1];
	    mat := Matrix(RowSequence(RemoveRow(IdentityMatrix(k,3),j))
				cat [cs])^-1;
	    seq := [Polynomial(r,[x,y,z]) : r in RowSequence(mat)];
	    assert Evaluate(l,seq) eq z;
	    F := Evaluate(F,seq); tr := [Evaluate(e,seq) : e in tr];
	    // F is now the equation of an irreducible conic through
	    // [0,1,0] where the tangent line is z=0
	    a,b,c := Explode([MonomialCoefficient(F,m) : m in [y*z,x*z,z^2]]);
	    assert not IsZero(a);
	    seq := [x,(y-b*x-c*z)/a,z];
	    F := Evaluate(F,seq); tr := [Evaluate(e,seq) : e in tr];
	    a := MonomialCoefficient(F,x^2);
	    assert (#Terms(F) eq 2) and (not IsZero(a)) and
			IsOne(MonomialCoefficient(F,y*z));
	    tr := [Evaluate(e,[x,a*y,(1/a)*z]) : e in tr];
	    return x^2*z+y*z^2,tr,6;
	  end if;
	else //3 distinct concurrent lines (maybe Galois conj)
	  f,tr := move_sing_pt(f,J); // translate singular point to [0,1,0]
	  assert f eq Evaluate(f,[x,0,z]); //f should be a cubic in x and z
	  f1,tr1,typ1 := normalise_deg_3_homog_poly(Evaluate(f,[R1.2,0,R1.1]))
			where R1 is PolynomialRing(k,2);
	  assert typ1 eq 1;
	  k1 := BaseRing(Parent(f1));
	  R1 := (k cmpeq k1) select R else ChangeRing(R,k1);
	  f := Evaluate(f1,[R1.3,R1.1]);
	  tr := [Evaluate(e,seq) : e in tr] where seq is 
			[Evaluate(tr1[1],[R1.3,R1.1]),R1.2,Evaluate(tr1[2],[R1.3,R1.1])];
	  return f,tr,7; // f=A*x^3+x*z^2, A != 0
	end if;
    else // f non-reduced
      d := Integers()!(Coefficient(HilbertPolynomial(J),1));
      assert (d eq 1) or (d eq 2);
      if d eq 1 then //double line+line
	B := MinimalBasis(J);
	assert #B eq 2;
	l1 := GCD(B[1],B[2]);
	l2 := f div l1^2;
	rows := [[MonomialCoefficient(l,R.i) : i in [1..3]] : l in [l1,l2]];
	seq := [k|0,0];
	for i := 3 to 1 by -1 do 
	  mat := Matrix(rows cat [Insert(seq,i,k!1)]);
	  if not IsZero(Determinant(mat)) then break; end if;
	end for;
	tr := [Polynomial(r,[x,y,z]) : r in RowSequence(mat^-1)];
	assert Evaluate(f,tr) eq x^2*y;
	return x^2*y,tr,8;
      else //treble line
	B := MinimalBasis(J);
	assert #B eq 1;
	l := (3*f) div B[1];
	cs := [MonomialCoefficient(l,R.i) : i in [1..3]];
	j := [i : i in [1..3] | not IsZero(cs[i])][1];
	mat := Matrix([cs] cat RowSequence(RemoveRow(IdentityMatrix(k,3),j)))^-1;
	tr := [Polynomial(r,[x,y,z]) : r in RowSequence(mat)];
	assert Evaluate(l,tr) eq x;
	f := Evaluate(f,tr);
	assert #Terms(f) eq 1;
	return f,tr,9; // f=A*x^3, A != 0
      end if;
    end if;
	      
end function;

intrinsic Corank3Case(f::RngMPolElt : d := 0, milnor_number := -1,
   fData := [**], get_trans := false) -> BoolElt, RngMPolElt, MonStgElt, Map
{ f should be a three-variable non-zero polynomial defining a corank 3 singularity
 at (0,0,0). That is, f contains no terms of degree < 3. Returns whether the
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
    require (f ne 0) and Rank(R0) eq 3: "f not a non-zero three variable polynomial";
    p := Characteristic(BaseRing(R0));
    // should check BaseRing(R0) is a field - maybe of a certain type
    ord := Min([TotalDegree(t) : t in Terms(f)]);
    require ord ge 3:
       "f does not have a zero or does not have a corank 3 singularity at (0,0,0)";

    if ord ge 4 then return false,_,_,_; end if;
    error if (p ne 0) and (p le 3), 
	"Cannot deal with corank 3 singularities in characteristic 2 or 3";

    boofd := (#fData gt 0);
    if boofd and (fData[2] lt d) then 
	return Corank3Case(expand_to_prec_with_quadratic_part(fData[1],d,R0):
		d := d, fData := [* fData[1],d *], get_trans := get_trans, 
			milnor_number := milnor_number);
    end if;
    if boofd then
	fdata := fData[1];
	dmax := fData[2];
        assert dmax ge Max([TotalDegree(t) : t in Terms(f)]);
    else
      dmax := Max([TotalDegree(t) : t in Terms(f)]);
    end if;

    if milnor_number lt 0 then
	mu := boofd select MilnorNumberAnalyticHypersurface(fdata) else MilnorNumber(f);
	if Type(mu) cmpeq Infty then return false,_,_,_; end if;
    else
	mu := milnor_number;
    end if;
    assert mu ge 8;

    expnstr := "Char. p error while trying to transform to normal form ";
    pstr := IntegerToString(p);
    errstr := "-like singularity in characteristic " cat pstr;

    j3f := &+[R0|t : t in Terms(f) | LeadingTotalDegree(t) eq 3];
    j3f1,tr,typ := crk3_normalise_deg_3_homog_poly(j3f);
    f := Evaluate(f,tr);
    R1 := Generic(Parent(f));
    K := BaseRing(R1);
    if typ eq 1 then // P8 singularity
      // NB. In this case f can be transformed into a non-singular (as a homogeneous equation)
      // cubic of standard form x^3+y^3+z^3+axyz over an algebraically closed field.
      // Here, we transform to a cubic but do not put it into that normal form.   
      assert mu eq 8;
      if get_trans then
	if d gt 3 then
	  _,tr1 := qh_transform_to_normal_form(f,j3f1,d);
	  tr := trunc_comp(tr,tr1,d-2);
	end if;
	tr := hom<R0->Parent(f)|tr>;
	return true,j3f1,"P8",tr;
      else
	return true,j3f1,"P8",_;
      end if;
    elif typ eq 2 then // Pn singularity, n > 8
      //j3f1 = ax^3+by^3+xyz, a,b != 0
      // First, get z^r term after transformation
      r := mu-5;
      assert r ge 4;
      typstr := "P" cat IntegerToString(mu);
      error if (p gt 0) and IsDivisibleBy(r,p), typstr cat errstr;
      if boofd and (dmax lt r) then //need to expand further?
	  f := expand_to_prec_with_quadratic_part(fdata,r,R0);
	  f := Evaluate(f,tr);
      end if;
      R2 := PolynomialRing(BaseRing(R1),3,"grevlex");
      F,tr1 := qh_transform_to_normal_form(R2!f,R2!j3f1,r);
      if get_trans then tr := [Evaluate(e,[R1!a : a in tr1]) : e in tr]; end if;
      error if &or[not IsZero(MonomialCoefficient(F,R1.3^i)) : i in [3..r-1]]
		or IsZero(MonomialCoefficient(F,R1.3^r)), typstr cat errstr;
      f0 := R1!F;//j3f1+MonomialCoefficient(F,R1.3^r)*(R1.3^r);
      if get_trans and (d gt r) then
	f := trunc_comp([f],[R1!a : a in tr1],d)[1];
	R2 := PolynomialRing(BaseRing(R1),seq,"grevlexw",seq) where seq is
		[r,r,3];
	m_t := hyperbolic_case_relations(R2!f0);
	_,tr1 := special_transform_to_normal_form(R2!f,R2!f0,d, 
			m_t : get_trans := get_trans);
	tr := trunc_comp(tr,[R1!a : a in tr1],d-2);
      end if;
      if get_trans then
	return true,f0,typstr,hom<R1->R1|tr>;
      else
	return true,f0,typstr;
      end if;
    elif typ eq 3 then //R_{m,n} singularity
      // j3f1=a*x^3+x*y*z, a != 0
      // First, get y^m and z^n terms after transformation
      // 4 <= m,n   mu=m+n+2
      assert mu ge 10;
      if boofd and (dmax lt mu-6) then //need to expand further?
	  f := expand_to_prec_with_quadratic_part(fdata,mu-6,R0);
	  f := Evaluate(f,tr);
      end if;
      R2 := PolynomialRing(BaseRing(R1),3,"grevlex");
      F,tr1 := qh_transform_to_normal_form(R2!f,R2!j3f1,mu-6);
      F := R1!F; 
      if get_trans then tr1 := [R1!a : a in tr1]; end if;
      yexps := [i : i in [4..mu-6] | not IsZero(MonomialCoefficient(F,R1.2^i))];
      zexps := [i : i in [4..mu-6] | not IsZero(MonomialCoefficient(F,R1.3^i))];
      boo := (#yexps gt 0) and (#zexps gt 0);
      if boo then
	yn := yexps[1]; zn := zexps[1];
	m := Min(yn,zn); n := Max(yn,zn);
	typstr := "R_{" cat IntegerToString(m) cat "," cat IntegerToString(n)
			cat "}";
	boo := (p eq 0) or (not IsDivisibleBy(m*n,p));
      end if;
      error if not boo, typstr cat errstr;
      assert mu eq m+n+2; 
      if yn gt m then //swap y and z
	F := Polynomial(Coefficients(F),[Monomial(R1,[e[1],e[3],e[2]]) where
		e is Exponents(t) : t in Monomials(F)]);
	if get_trans then
	    tr1 := [Polynomial(Coefficients(pol),[Monomial(R1,[e[1],e[3],e[2]]) where
		e is Exponents(t) : t in Monomials(pol)]) : pol in tr1];
	end if;
      end if;
      if get_trans then tr := trunc_comp(tr,tr1,Max(d,n)-2); end if;
      f0 := j3f1+MonomialCoefficient(F,R1.2^m)*(R1.2^m)+
			MonomialCoefficient(F,R1.3^n)*(R1.3^n);
      if get_trans and ((d gt n) or (m lt n)) then
	f := trunc_comp([f],tr1,Max(d,n))[1];
	R2 := PolynomialRing(BaseRing(R1),seq,"grevlexw",seq) where seq is
		[m*n,3*n,3*m];
	m_t := hyperbolic_case_relations(R2!f0);
	_,tr1 := special_transform_to_normal_form(R2!f,R2!f0,Max(d,n), 
			m_t : get_trans := get_trans);
	tr := trunc_comp(tr,[R1!a : a in tr1],Max(d,n)-2);
      end if;
      if get_trans then
	return true,f0,typstr,hom<R1->R1|tr>;
      else
	return true,f0,typstr;
      end if;
    elif typ eq 4 then //T_{l,m,n} singularity
      // j3f1=x*y*z
      // First, get x^l, y^m and z^n terms after transformation
      // 4 <= l,m,n   mu=l+m+n-1
      assert mu ge 11;
      if boofd and (dmax lt mu-7) then //need to expand further?
	  f := expand_to_prec_with_quadratic_part(fdata,mu-7,R0);
	  f := Evaluate(f,tr);
      end if;
      R2 := PolynomialRing(BaseRing(R1),3,"grevlex");
      F,tr1 := qh_transform_to_normal_form(R2!f,R2!j3f1,mu-7);
      F := R1!F;
      if get_trans then tr1 := [R1!a : a in tr1]; end if;
      xexps := [i : i in [4..mu-7] | not IsZero(MonomialCoefficient(F,R1.1^i))];
      yexps := [i : i in [4..mu-7] | not IsZero(MonomialCoefficient(F,R1.2^i))];
      zexps := [i : i in [4..mu-7] | not IsZero(MonomialCoefficient(F,R1.3^i))];
      boo := (#xexps gt 0) and (#yexps gt 0) and (#zexps gt 0);
      if boo then
	xn := xexps[1]; yn := yexps[1]; zn := zexps[1];
	l,m,n := Explode(Sort([xn,yn,zn]));
	typstr := "T_{" cat IntegerToString(l) cat "," cat IntegerToString(m) cat ","
	    cat IntegerToString(n) cat "}";
	boo := (p eq 0) or (not IsDivisibleBy(l*m*n,p));
      end if;
      error if not boo, typstr cat errstr;
      assert mu eq l+m+n-1;
      seq := [xn,yn,zn]; prm := 0; Sort(~seq,~prm);
      if not IsIdentity(prm) then //permute x,y,z
        prm := [i^prm : i in [1..3]];
	F := Polynomial(Coefficients(F),[Monomial(R1,[e[i] : i in prm]) where
		e is Exponents(t) : t in Monomials(F)]);
	if get_trans then
	    tr1 := [Polynomial(Coefficients(pol),[Monomial(R1,[e[i] : i in prm]) where
		e is Exponents(t) : t in Monomials(pol)]) : pol in tr1];
	end if;
      end if;
      if get_trans then tr := trunc_comp(tr,tr1,Max(d,n)-2); end if;
      f0 := j3f1+MonomialCoefficient(F,R1.1^l)*(R1.1^l)+
	MonomialCoefficient(F,R1.2^m)*(R1.2^m)+MonomialCoefficient(F,R1.3^n)*(R1.3^n);
      if get_trans and ((d gt n) or (l lt n)) then
	f := trunc_comp([f],tr1,Max(d,n))[1];
	R2 := PolynomialRing(BaseRing(R1),seq,"grevlexw",seq) where seq is
		[m*n,l*n,l*m];
	m_t := hyperbolic_case_relations(R2!f0);
	_,tr1 := special_transform_to_normal_form(R2!f,R2!f0,Max(d,n), 
			m_t : get_trans := get_trans);
	tr := trunc_comp(tr,[R1!a : a in tr1],Max(d,n)-2);
      end if;
      if get_trans then
	return true,f0,typstr,hom<R1->R1|tr>;
      else
	return true,f0,typstr;
      end if;
    elif typ eq 5 then //Q-family singularity
      // j3f1=a*x^3+y*z^2, a != 0
      // First, determine the Q-family type
      assert mu ge 10;
      // need to expand more?
      if boofd and dmax lt ((mu-2) div 2) then
	dmax := (mu-2) div 2;
	f := expand_to_prec_with_quadratic_part(fdata,dmax,R0);
        f := Evaluate(f,tr);
      end if;
      while true do
        exps := [Exponents(t) : t in Terms(f-j3f1)];
        e01 := [e : e in exps | (e[3] le 1) and (e[1] le 2)];
	e01 := [e : e in e01 | (e[3] eq 0) or (e[1] le 1)];
        assert #e01 gt 0;
	e0 := [e : e in e01 | e[3] eq 0];
	e1 := [e : e in e01 | e[3] eq 1];
        k := (#e0 eq 0) select 0 else Min([(e[1]^2+2)*e[2] : e in e0]);
	k1 := (#e1 eq 0) select 0 else Min([(4*e[1]+2)*(2*e[2]-1) : e in e1]);
	if (k1 gt 0) and (k1 le k) then
	  e1min := [e : e in e1 | (4*e[1]+2)*(2*e[2]-1) eq k1];
	  seq := [R1.1,R1.2,R1.3-(&+[MonomialCoefficient(f,Monomial(R1,e))*
			Monomial(R1,[e[1],e[2]-1,0]) : e in e1min])/2];
	  f := Evaluate(f,seq);
	  tr := [Evaluate(u,seq) : u in tr];
	  continue;
	end if;
	assert k+2 le mu;
        es := [e : e in e0 | (e[1]^2+2)*e[2] eq k];
        f0 := j3f1+
	  &+[MonomialCoefficient(f,m)*m where m is Monomial(R1,e) : e in es];
	pol := Evaluate(f0,[PolynomialRing(K).1,1,0]);
	a := Coefficient(pol,2); lc := LeadingCoefficient(pol);
	if not (pol eq  lc*((Parent(pol).1)+(a/(3*lc)))^3) then break; end if;
	assert IsDivisibleBy(k,6);
	tr1 := [R1.1-(a/(3*lc))*(R1.2)^(k div 6),R1.2,R1.3];
	f := Evaluate(f,tr1); tr := [Evaluate(e,tr1) : e in tr];
      end while;

      if not IsDivisibleBy(k,6) then
        assert #es eq 1;
        typstr := "Q" cat IntegerToString(k+2);
	if IsEven(k) then
          wts := IsOdd(k2) select [k2,3,3*((k2-1) div 2)] else
			[k,6,3*(k2-1)] where k2 is (k div 2);
	else
	  wts := [2*(k div 3), 4, k-2];
	end if;
        error if (p gt 0) and IsDivisibleBy(wts[1],p), typstr cat errstr;
	assert mu eq k+2;
      else
	// mainly relevant for j=0
	wts := [k div 3,2,(k div 2)-1];
	if IsEven(wts[3]) then wts := [k div 6,1,wts[3] div 2]; end if;
      end if;
      R2 := PolynomialRing(BaseRing(R1),wts,"grevlexw",wts);
      d1 := wts[1]+2*wts[3];
      if get_trans and (d ge 3) then d1 := d*wts[3]; end if;

      if IsDivisibleBy(k,6) then // Types Q_{k/6,j} some j >=0
	j := mu-2-k;
	typstr := "Q_{" cat IntegerToString(k div 6) cat "," cat
                IntegerToString(j) cat "}";
	kd6 := k div 6;
	error if (p gt 0) and IsDivisibleBy(kd6*(3*kd6+j),p), typstr cat errstr;
	// do we need to expand further?
	if boofd and (dmax lt (4*kd6+j-1)) then
	  f := expand_to_prec_with_quadratic_part(fdata,4*kd6+j-1,R0);
	  f := Evaluate(f,tr);
	end if;
	// First, transform the ax^3+bx^2y^m+.. part
	fact := Factorisation(pol);
	if not IsZero(Discriminant(pol)) then //j=0 quasi-hom case
	  error if j gt 0, "Bad " cat typstr cat errstr;
	  if #fact gt 1 then //root over K
	    if IsZero(Evaluate(pol,K!0)) then
	      u := K!0;
	    else
	      u := -Coefficient(fct,0) where fct is 
			[fc[1] : fc in fact | Degree(fc[1]) eq 1][1];
	    end if;
	  else
	    K<u> := ext<K|fact[1][1]>;
	    R1 := ChangeRing(R1,K); f := R1!f; j3f1 := R1!j3f1;
	  end if;
	else
	  assert (j gt 0) and (#fact gt 1);
	  u := -Coefficient(fct,0) where fct is 
			[fc[1] : fc in fact | fc[2] eq 2][1];
	end if;
	if not IsZero(u) then	    
	  seq := [(R1.1)+u*(R1.2)^kd6,R1.2,R1.3];
          f := Evaluate(f,seq);
	  f0 := Evaluate(f0,seq);
	  if get_trans then tr := trunc_comp(tr,seq,Max(d,4*kd6+j-1)-2); end if;
	end if;
	assert IsZero(MonomialCoefficient(f,Monomial(R1,[0,3*kd6,0]))); //no y^{3m} term
	assert IsZero(MonomialCoefficient(f,Monomial(R1,[1,2*kd6,0]))) eq
			(j gt 0); //no xy^{2m} term iff j > 0

	// Now, f = ax^3+bx^2y^m+cxy^(2m)+yz^2, ac !=0 if j=0, and c=0, ab !=0 if j>0
	if j eq 0 then
	  a,b,c := Explode([MonomialCoefficient(f,Monomial(R1,[3-i,i*kd6,0])) :
					i in [0..2]]);
	  de := b^2-4*(a*c); de1 := de+(a*c);
	  assert not IsZero(de);
	  if IsZero(de1) then
	      gs :=[[Monomial(R2,[1,2*kd6,0]),(-b/(2*c))*Monomial(R2,[2,kd6,0])]];
	  else
	      gs :=[[Monomial(R2,[0,3*kd6,0]),(de1/c^2)*Monomial(R2,[2,kd6,0])]];
	  end if;
	  Append(~gs,[Monomial(R2,[1,0,2]),((kd6*de)/(2*a))*Monomial(R2,[2,2*kd6-1,0])]);
	  w1 := 2*kd6+1; w2 := 4*kd6-1;
	  //now just continue to the Q_i quasi-hom transformation step
	else //j > 0
	  // First normalise to the y^(3k+j) term
	  _,tr1 := qh_transform_to_normal_form(R2!f,R2!f0,(3*kd6+j)*wts[2]);
	  f := trunc_comp([f],[R1!a : a in tr1],Max(d,4*kd6+j-1))[1];
	  if get_trans then 
	    tr := trunc_comp(tr,[R1!a : a in tr1],Max(d,4*kd6+j-1)-2);
	  end if;
	  // f should now be in the form ax^3+bx^2y^m+yz^2+cy^(3m+j)+O(deg 6m+2j+1)
	  // for the weighted degree where the (x,y,z) weights are (2m,2,3m-1) [m=kd6]
	  tf0 := [t : t in Terms(f) | (Exponents(t)[1] eq 0) and 
			(Exponents(t)[3] eq 0)];
	  boo := (#tf0 gt 0);
	  if boo then
	    t0 := Min(tf0);
	    boo := (Exponents(t0) eq [0,3*kd6+j,0]);
	  end if;
	  error if not boo, "Bad " cat typstr cat errstr;
	  f0 +:= t0;
	  a := MonomialCoefficient(f0,Monomial(R1,[3,0,0]));
	  b := MonomialCoefficient(f0,Monomial(R1,[2,kd6,0]));
	  c := LeadingCoefficient(t0);
	  R2 := PolynomialRing(BaseRing(R1),3,"grevlex");
	  x,y,z := Explode([R2.i : i in [1..3]]);
	  a1 := (2*kd6*b^2)/((3*kd6+j)*c); b1 := 1/((4*kd6)*b^2);
	  m_t := [ <[y*z,0],[R2|0,0,1/2]>,
	    <[x^2*z,0],[(1/(3*a))*z,0,-(b/(3*a))*x*y^(kd6-1)]>,
	    <[z^2,-((kd6*b)*x^2*y^(kd6-1)+((3*kd6+j)*c)*y^(3*kd6+j-1))],[R2|0,1,0]>,
	    <[x^2,-((2*b)/(3*a))*x*y^kd6],[R2!(1/(3*a)),0,0]>,
	    <[x*y^(2*kd6),(6*(3*kd6+j))*(a*c*b1)*y^(3*kd6+j)],[(1/(2*b))*y^kd6,
		-(6*a*b1)*y,(3*a*b1)*z]>,
	    <[y^(4*kd6+j),-(9*(3*kd6+j)*(a^2*c*b1)/b)*y^(4*kd6+2*j)],
	       [-((3*kd6*a)*y^(2*kd6+j)+kd6*a1*x*y^kd6)*b1,
		(3*(a*a1/b)*x+2*a1*y^kd6+9*(a^2/b)*y^(kd6+j))*b1*y,
	       -((3*(a*a1)*x+2*(b*a1)*y^kd6+9*a^2*y^(kd6+j))/(2*b))*b1*z]> ];
	  f,tr1 := special_transform_to_normal_form(R2!f,R2!f0,Max(d,4*kd6+j-1), 
			m_t : get_trans := get_trans);
	  f := R1!f;
	  if not get_trans then
	    return true,f,typstr;
	  else
	    tr := trunc_comp(tr,[R1!a : a in tr1],Max(d,4*kd6+j-1)-2);
	    return true,f,typstr,hom<R1->R1|tr>;
	  end if;
	end if; 
      elif IsDivisibleBy(k,3) then // Q_{k+2}, k+2 = 5 mod 6
	// here f0 is the quasi-homog. poly ax^3+zy^2+bxy^(k/3).
	// Higher degree part in the normal form is 
	// y^(2*(k/3)-m)*(b0+..b_{m-1}*y^(m-1)) where m = (k div 6)
	kd3 := k div 3;
	w1 := wts[1]-1; w2 := w1;
	// do we need to expand further?
	if boofd and (dmax lt w1) then
	  f := expand_to_prec_with_quadratic_part(fdata,w1,R0);
	  f := Evaluate(f,tr);
	end if;
	a := MonomialCoefficient(f0,(R1.1)^3);
	b := MonomialCoefficient(f0,(R1.1)*(R1.2)^kd3);
	gs := [[Monomial(R2,[1,0,2]),((kd3*b^2)/(3*a))*Monomial(R2,[0,w1,0])]];
      else // Q_{k+2}, k+2 = 0,4 mod 6
	// here f0 is the quasi-homog. poly ax^3+zy^2+by^(k/2).
	// Higher degree part in the normal form is 
	// x*y^((k/2)-m)*(b0+..b_{m-1}*y^(m-1)) where m = (k div 6)
	assert IsEven(k);
	kd2 := k div 2;
	b := -MonomialCoefficient(f0,(R1.2)^kd2);
	gs := [[Monomial(R2,[1,0,2]),(kd2*b)*Monomial(R2,[1,kd2-1,0])]];
	w1 := kd2; w2 := ((5*w1) div 3)-1;
	if boofd and (dmax lt w2) then
	  f := expand_to_prec_with_quadratic_part(fdata,w2,R0);
	  f := Evaluate(f,tr);
	end if;
      end if;
      // transformation and return for the Q_i{,0} cases
      f,tr1 := qh_transform_to_normal_form(R2!f,R2!f0,d1 : 
	groebner_shift := gs, get_trans := get_trans, ord_deg := Max(d,w2));
      if not get_trans then
          return true,R1!f,typstr;
      else
          tr := trunc_comp(tr,[R1!a : a in tr1],Max(d,w1)-2);
          return true,R1!f,typstr,hom<R1->R1|tr>;
      end if;
    elif typ eq 6 then // S-family singularity
      // j3f1=x^2*z+y*z^2
      // First, determine the S-family type
      assert mu ge 11;
      error "Sorry, this is a corank 3 S-family singularity that has not yet",
		"been implemented";
    elif typ eq 7 then // U-family singularity
      // j3f1=a*x^3+x*z^2, a != 0
      error "Sorry, this is a corank 3 U-family singularity that has not yet",
		"been implemented";
    elif typ eq 8 then // V-family singularity
      // j3f1=x^2*y
      error "Sorry, this is a corank 3 V-family singularity that has not yet",
		"been implemented";
    else // j3f1=a*x^3, a != 0
      return false,_,_,_;
    end if;

end intrinsic;
