freeze;
///////////////////////////////////////////////////////////////////
//  Intrinsics for Computation of Quotients of curves of         //
//     genus >=2 by an arbitrary group of automorphisms.         //
//                                                               //
//             mch - 06/2007                                     //
///////////////////////////////////////////////////////////////////


/***** Some special routines for expressing rational functions *******/
/************* in the form A^2*B with B "square-free" ****************/

function sub_fact(f)
// f is a monic poly over a field of characteristic p.
//  returns [f1,..,fr],[n1,..nr],g where f1,..,fr are
//  relatively prime square free monic polys, g' = 0 and
//  f = g* f1^n1 * f2^n2 * .. * fr^nr and
//   (g,fi)=1, (ni,p)=1 for all i
    facts := [];
    mults := [];
    P := Parent(f);
    fd := Derivative(f);
    if fd eq 0 then
	return [f],[1],Parent(f)!1;
    end if;
    
    g := GCD(f,fd);
    if Degree(g) eq 0 then
	return [f],[1],Parent(f)!1;
    end if;
    sf := f div g;

    // now f = f1^n1 * .. * fr^nr * R^p (ni prime to p &
    //  (fi,R)=1 for each i) and sf = f1*..*fr 
    while Degree(sf) gt 0 do
	m := 0; r := f div sf;
	repeat
	    f := r;
	    m +:= 1;
	    boo,r := IsDivisibleBy(f,sf);
	until not boo;
	r := sf;
	sf := GCD(f,r);
	Append(~facts,r div sf);
	Append(~mults,m);
    end while;
    
    return facts,mults,f;

end function;

function SquareFreePart(f)
// factors poly f as u*v^2 where u is squarefree and v is monic
    if Degree(f) le 1 then return f,Parent(f)!1; end if;
    lc := LeadingCoefficient(f);
    f := Normalize(f);

    facts,mults,f := sub_fact(f);
    if Degree(f) gt 0 then
        p := Characteristic(BaseRing(Parent(f))); // p!=2 !!
	// get pth root of f
	f := Parent(f)![(c eq 0 select c else Root(c,p))
		where c is Coefficient(f,r*p) :
		 r in [0..Degree(f) div p]];
	u,v := SquareFreePart(f);
	facts cat:= [u,v];
	mults cat:= [p,2*p];
    end if;
    
    u := lc * &*[Parent(f)|facts[i] : i in [1..#facts] |
    			IsOdd(mults[i])];
    v := &*[facts[i]^(mults[i] div 2) : i in [1..#facts]];
    return u,v;
end function;

function FFSquareFreePart(f,Ca)
// Ca is an affine non-singular non-split conic with coord ring Ra
// (which is a UFD) and f is a polynomial in the ambient
//  coordinate ring, R, of Ca. We factor Ra!f as U*V^2
//  for U squarefree and return R!U,R!V. Work in the FF of Ca.
    R := CoordinateRing(Ambient(Ca));
    K := FunctionField(Ca);
    F,mp := AlgorithmicFunctionField(K);
    if mp(K.2) eq BaseField(F).1 then // usually true
	Y := R.2; X := R.1;
    else
	Y := R.1; X := R.2;
    end if;
    f1 := mp(K!(CoordinateRing(Ca)!f));
    D := Divisor(f1);
    pls,es := Support(D);
    assert #[e : e in es | e lt 0] eq 1;
    _,i_inf := Min(es);
    pl_inf := pls[i_inf];
    Remove(~pls,i_inf); Remove(~es,i_inf);
    DV := &+[Parent(D)|(es[i] div 2)*pls[i]: i in [1..#es] | es[i] gt 1];
    boo,m :=  IsDivisibleBy(Degree(DV),Degree(pl_inf));
    assert boo;
    DV := DV - m*pl_inf;
    boo,v := IsPrincipal(DV);
    assert boo;
    u := f1/(v^2);
    U := R!Evaluate(e[1],Y) + (R!Evaluate(e[2],Y))*X 
		where e is Eltseq(u);
    V := R!Evaluate(e[1],Y) + (R!Evaluate(e[2],Y))*X 
		where e is Eltseq(v);
    assert CoordinateRing(Ca)!(f-U*V^2) eq 0;
    return U,V;
end function;

/****** Some hack code to avoid FF coercions ****************/

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
		RationalFunctionField(BaseField(Parent(f)))!f,elts[1]);
	end if;
    else // elts should be > 1!
	F1 := BaseRing(Parent(f));
	coeffs := [ FunctionFieldEvaluation(c,elts1) : c in expn ]
		where elts1 is Prune(elts) where expn is Eltseq(f);
	return Evaluate(PolynomialRing(Universe(coeffs))!coeffs,elts[#elts]);
    end if;
    
end function;

/* 
   Temporary(?) hack to quickly build the map from C -> CQ
   coming from the sequence of AlFF (of C) elements.
    This avoids the slow coercion problems to rat. functions.
   G is an automorphism group of C which already contains
   some of the data needed.
*/
function GetMap(ff_elts,G,CQ)
    C := Curve(G);
    Ca := AffinePatch(C1, FFPatchIndex(C1))
	where C1 is (IsProjective(C) select C else ProjectiveClosure(C));
    rat_seq := [R.i : i in Reverse(G`ff_rat)] 
			where R is CoordinateRing(Ambient(Ca));
    fns := [FunctionFieldEvaluation(f,rat_seq) : f in ff_elts];
    mp_aff := map<Ca->CQ | fns : Check := false>;
    if IsProjective(C) then
	return ProjectiveClosure(mp_aff);
    elif Ambient(C) eq Ambient(Ca) then //C eq Ca
	return mp_aff;	
    else
        mp := ProjectiveClosure(mp_aff);
	return Expand(a_mp * mp) where a_mp is
	  Restriction(ProjectiveClosureMap(Ambient(C)),
	      C,ProjectiveClosure(C));
    end if;
end function;

/******* Canonical image using AlFF elements directly ****************/ 

function FFCanonicalImage(Fs,K)

    g := #Fs;
    if g eq 2 then
 	return Curve(ProjectiveSpace(K,1)), true;
    end if;;

    F2s := [Fs[i]*Fs[j]: j in [i..g], i in [1..g]];
    quad_coeffs := Basis(Relations(F2s,K)); //get all quadratic relations
    delete F2s;
    if #quad_coeffs eq ((g-2)*(g-3)) div 2 then //non-hyperelliptic case
	bHyp := false;
    elif  #quad_coeffs eq ((g-1)*(g-2)) div 2 then //hyperelliptic case
	bHyp := true;
    else
	error "The equations didn't define the canonical map";
    end if;
    
    Pg<[x]> := ProjectiveSpace(K,g-1);
    CRg := CoordinateRing(Pg);
    v2 :=  [x[i]*x[j]: j in [i..g], i in [1..g]];   
    Qs := [&+[r[i]*v2[i] : i in [1..#v2]] : r in quad_coeffs];
		
    I2 := ideal<CRg | Qs>;
    P := PolynomialRing(Rationals());
    H := P!HilbertPolynomial(I2);
    H1 := (bHyp select (g-1)*P.1 + 1 else (g-1)*(2*P.1-1));
    
    if (H ne H1) and (g gt 3) then // need to include cubics
	error if bHyp, "The equations didn't define the canonical map";
	F3s := [Fs[i]*Fs[j]*Fs[k]: k in [j..g], j in [i..g], i in [1..g]];    
	ter_coeffs := Relations(F3s,K); //get all ternary relations
	delete F3s;
        assert Dimension(ter_coeffs) eq ((g-3)*(g^2+6*g-10)) div 6;

        // now get space of cubics not coming from quadrics
	v3 := [x[i]*x[j]*x[k]: k in [j..g], j in [i..g], i in [1..g]];
        V3 := Generic(ter_coeffs);//KSpace(K,#v3);	
	//W1 := sub<V3|[V3!vec:vec in ter_coeffs]>;
	W2 := sub<V3|[V3![MonomialCoefficient(q*x[i],m): m in v3] :
			i in [1..g],q in Qs]>;
	//assert W2 subset W1
	W := Complement(ter_coeffs,W2);//Complement(W1,W2);
	Cs :=  [&+[r[i]*v3[i] : i in [1..#v3]] where r is
		Eltseq(v) : v in Basis(W)];
		
	I2 := ideal<CRg | Qs cat Cs>;
	assert P!HilbertPolynomial(I2) eq H1;
	
	return Curve(Pg,Qs cat Cs : Saturated := true),false;
    elif H ne H1 then // g=3, non-hyperelliptic -> quartic
	F4s := [Fs[i]*Fs[j]*Fs[k]*Fs[l]: l in [k..g], k in [j..g],
						j in [i..g], i in [1..g]];    
	quar_coeffs := Basis(Relations(F4s,K)); //get all quartic relations
	delete F4s;
	assert #quar_coeffs eq 1;
	v4 := [x[i]*x[j]*x[k]*x[l]: l in [k..g], k in [j..g],
						j in [i..g], i in [1..g]];    
	quar := quar_coeffs[1];
	return Curve(Pg,&+[quar[i]*v4[i] : i in [1..#v4]]),false;
    else
	return Curve(Pg,Qs : Saturated := true),bHyp;
    end if;

end function;

/***** Hyperelliptic case helper functions **************************/

function char2xtoy(G,vec,gG)
// In the char 2 case, when C is hyperelliptic and x is a generator of
//  the sub-function field of C/<G,w> (w = hyperelliptic involution),
//  compute a y function s.t. C/G has fn fld gen by x and y and 
//  CQ : y^2+h(x)y=f(x) is a Weierstrass form for C/G (genus gG).
//  Finds a y by computing G-invariants of RR space of fns with restricted
//  poles over those of x.
//  vec is a sequence containing the powers 1,x,x^2,..,x^(2gG+2)
// Return CQ and y. NB: Also works for char != 2!

    x := vec[2];
    K := BaseRing(Curve(G));
    Dx := Denominator(Divisor(x));
    V,mp := RiemannRochSpace((gG+1)*Dx);
    // get G-invariants
    mats := [Matrix([Eltseq(Inverse(mp)((g`ff_map)(mp(b)))) : 
	       b in Basis(V)]) : g in Generators(G)];
    VG := &meet[Kernel(H!(m - I)) : m in mats] where H is Hom(V,V)
     	    where I is IdentityMatrix(K,Dimension(V));
    assert Dimension(VG) eq gG+3;
    xy_fns := [mp(b) : b in Basis(VG)];
    // now xy_fns should have basis {1,x,..x^(gG+1),y}
    //  - now get complement to {1,x,..,x^(gG+1)}
    XG := sub<VG|[VG!Inverse(mp)(xp) : xp in [vec[i] : i in [1..gG+2]]]>;
    y := mp(Basis(Complement(VG,XG))[1]);
    // get equation
    vec := [y^2] cat [y*vec[i]:i in [1..gG+2]] cat vec;
    rels := Basis(Relations(vec,K));
    assert #rels eq 1;
    rel := rels[1];
    assert rel[1] ne 0;
    A := PolynomialRing(K); X:=A.1;
    h := A![rel[i]/rel[1]:i in [2..gG+3]];
    f := A![rel[i]/rel[1]:i in [gG+4..3*gG+6]];
    CQ := HyperellipticCurve([-f,h]);
    assert Genus(CQ) eq gG;
    return CQ,y;

end function;

/***** Special case code for quotients of genus 0 or 1 **************/

function hypToGen0Case(G,Crat,fs)
// Case when C is hyperelliptic and C/G has genus 0 but G doesn't contain the
// hyperelliptic involution, w. The code below has found the rational
// quotient Crat = C/<G,w> as P^1 or a plane conic, with fs the set of rational
// functions on C giving the map C -> Crat.
// Function finds and returns a model for C/G and the projection map C -> C/G

    K := BaseRing(Curve(G));
    //first try to convert Crat to P^1 if it's a conic
    if Type(Crat) eq CrvCon then
	boo,pt := HasRationalPoint(Crat);
	if boo then
	    prm_con := Parametrization(Crat,pt,
			Curve(ProjectiveSpace(K,1)));
	    Crat := Domain(prm_con);
	    fs := [Evaluate(f,fs) : f in InverseDefiningPolynomials(prm_con)];
	end if;
    end if;

    //handle P^1 case
    if #fs eq 2 then
      x := fs[1]/fs[2];
      H,y := char2xtoy(G,[1,x,x^2],0);
      fs := [x,y,1];
      f,h := HyperellipticPolynomials(H);
      hc := [Coefficient(h,i) : i in [0..1]];
      fc := [Coefficient(f,i) : i in [0..2]];
      P<x,y,z> := ProjectiveSpace(K,2);
      CG := Conic(P,y^2+hc[2]*x*y+hc[1]*z*y-fc[3]*x^2-fc[2]*x*z-fc[1]*z^2);
      return CG,GetMap(fs,G,CG);
    else    // Crat = conic case
      // case gives C/G -> Crat a degree 2 separable cover of one non-paramatrisable
      // smooth genus 0 curve by another. Cannot occur (except poss. over imperfect
      // fields of char 2 ?)
      error "This code branch should never occur!";
    end if;

end function;

function hypToGen1Case(G,Crat,fs,diffG)
// Case when C is hyperelliptic and C/G has genus 1 (when G cannot contain the
// hyperelliptic involution, w!). The code below has found the rational
// quotient Crat = C/<G,w> as P^1 or a plane conic, with fs the set of rational
// functions on C giving the map C -> Crat. diffG is a G-invariant differential
// on C that gives a canonical differential on C/G.
// Function finds and returns a model for C/G and the projection map C -> C/G

    K := BaseRing(Curve(G));
    //first try to convert Crat to P^1 if it's a conic
    if Type(Crat) eq CrvCon then
	boo,pt := HasRationalPoint(Crat);
	if boo then
	    prm_con := Parametrization(Crat,pt,
			Curve(ProjectiveSpace(K,1)));
	    Crat := Domain(prm_con);
	    fs := [Evaluate(f,fs) : f in InverseDefiningPolynomials(prm_con)];
	end if;
    end if;

    //handle P^1 case
    if #fs eq 2 then
      x := fs[1]/fs[2];
      if Characteristic(K) ne 2 then
      // get y-coordinate from the differential
	y := Differential(x)/FunctionFieldDifferential(diffG);
	eqns := Basis(Relations([x^4,x^3,x^2,x,1,-y^2],K));
	assert #eqns eq 1/* or #eqns eq 2*/;
	/*if #eqns eq 2 then
	  mat := Matrix(eqns);
	  mat := EchelonForm(mat);
	  eqn := Eltseq(mat[2]);
	  assert (eqn[1] eq K!0) and (eqn[2] ne K!0) and (eqn[6] ne K!0);*/
	eqn := Eltseq(eqns[1]);
	if eqn[1] eq K!0 then
	  eqn := eqn[2..6];
	else
	  eqn := Eltseq(eqns[1]);
	  //assert (eqn[1] ne K!0) and (eqn[6] ne K!0);
	end if;
	assert (eqn[1] ne K!0) and (eqn[#eqn] ne K!0);
	RK := PolynomialRing(K); X := RK.1;
	if #eqn eq 6 then // try to convert to elliptic form
	  pol :=RK!(Reverse(Prune(eqn)));
	  rts := Roots(pol);
	  if #rts ne 0 then
	    r := rts[1][1];
	    pol := Evaluate(pol,(RK.1)+r);
	    y := y/(x-r)^2; x := 1/(x-r);
	    eqn := (Coefficients(pol)[2..5]) cat [eqn[6]];
	    assert eqn[1] ne K!0;
	  elif IsSquare(eqn[1]/eqn[6]) then
	    pol := pol/eqn[6];
	    H := HyperellipticCurve(pol);
	    ptinf := Representative(PointsAtInfinity(H));
	    E,mp := EllipticCurve(H,ptinf);
	    E,mp1 := SimplifiedModel(E);
	    mp := Expand(mp*mp1);
	    x,y := Explode([Evaluate(def[1],seq)/v,Evaluate(def[2],seq)/v])
		where v is Evaluate(def[3],seq) where seq is [x,y,1] where
		   def is DefiningPolynomials(mp);
	    return E,GetMap([x,y,1],G,E);
	  end if;
	end if;
	if #eqn eq 5 then //already in elliptic Weierstrass form
	  v := eqn[1]/eqn[5];
	  y := y*v; x := x*v;
	  E := EllipticCurve([K|0,eqn[2]/eqn[5],0,(eqn[3]/eqn[5])*v,
				(eqn[4]/eqn[5])*v^2]);
	  if Type(K) eq FldRat then // return minimal model
	    E,mp := MinimalModel(E);
	    x,y := Explode([Evaluate(def[1],seq)/v,Evaluate(def[2],seq)/v])
		where v is Evaluate(def[3],seq) where seq is [x,y,1] where
		   def is DefiningPolynomials(mp);
	  end if;
	  return E,GetMap([x,y,1],G,E);
	end if;
	// only have y^2=pol=deg 4 equation: convert to proj normal curve in P^3
	//  embedding by 1,x,x^2,y
 	pol := pol/eqn[6];
	as := Coefficients(pol);
	fs := [1,x,x^2,y];
	P<[x]> := ProjectiveSpace(K,3);
	E := Curve(P,[x[2]^2-x[1]*x[3],
	  x[4]^2-as[5]*x[3]^2-as[4]*x[2]*x[3]-as[3]*x[2]^2-as[2]*x[1]*x[2]-as[1]*x[1]^2]
		: Saturated := true);
	return E,GetMap(fs,G,E);
      else // char(K) eq 2
	// As in gen case, We revert to looking at all G invariant functions
	//  in the finite Riemann-Roch space of functions with poles
	//  of restricted degree over the poles of x.
	H,y := char2xtoy(G,[1,x,x^2,x^3,x^4],1);
	// try to convert to elliptic form or do P^3 embedding
	ninf := NumberOfPointsAtInfinity(H);
	if (Type(K) eq FldFin) or (ninf gt 0) then
	  pt := (ninf gt 0) select PointsAtInfinity(H)[1] else Random(H);
	  E,mp := EllipticCurve(H,pt);
	  x,y := Explode([Evaluate(def[1],seq)/v,Evaluate(def[2],seq)/v])
	    where v is Evaluate(def[3],seq) where seq is [x,y,1] where
		   def is DefiningPolynomials(mp);
	  return E,GetMap([x,y,1],G,E);
	end if;
	f,h := HyperellipticPolynomials(H);
	hc := [Coefficient(h,i) : i in [0..2]];
        fc := [Coefficient(f,i) : i in [0..4]];
	fs := [1,x,x^2,y];
	P<[x]> := ProjectiveSpace(K,3);
	E := Curve(P,[x[2]^2-x[1]*x[3],
	  x[4]^2 + &+[hc[i]*x[4]*x[i]: i in [1..3]] +
	  fc[5]*x[3]^2+fc[4]*x[2]*x[3]+fc[3]*x[2]^2+fc[2]*x[1]*x[2]+fc[1]*x[1]^2]
		: Saturated := true);
	return E,GetMap(fs,G,E);		
      end if;
    else // Crat = conic case
      error if Characteristic(K) eq 2,
	    "Quotient of hyperelliptic curve is genus 1 w/o rational point over a ",
	    "char 2 function field. Sorry, can't handle this case!";
      // (Affine) conic Crat is Q(X,Y)=0. Z exists s.t. 
      //  Z^2=R(X,Y) for R(X,Y) of total degree 1 or 2 &
      //  a holomorphic differentials is of the form
      //  a*dX/(Z*Qy(X,Y)) for some constant a [  Qy(X,Y) = dQ/dY(X,Y) ]
      // Homogenised this gives a projectve normal embedding in P^3
      Ca := AffinePatch(Crat,1);
      CR<X,Y> := CoordinateRing(Ambient(Ca));
      x := fs[1]/fs[3];
      y := fs[2]/fs[3];
      Qy := Evaluate(Derivative(Equation(Ca),2),[x,y]);
      z := Differential(x)/FunctionFieldDifferential(diffG);
      z := z/Qy;
      // find R(X,Y)
      mons := [X^2,X*Y,Y^2,X,Y,1];
      vec := [Evaluate(m,[x,y]) : m in mons] cat [-z^2];
      rels := Basis(Relations(vec,K));
      assert #rels eq 2;
      rel := [r : r in rels | r[7] ne K!0][1];
      R := &+[rel[i]*mons[i] : i in [1..6]]/rel[7];
      // homogenise to degree 2 and return result
      fs := [x,y,1,z];
      P<[x]> := ProjectiveSpace(K,3);
      R := Homogenization(Evaluate(R,[x[1],x[2]]),x[3],2);
      E := Curve(P, [Evaluate(DefiningPolynomial(Crat),[x[1],x[2],x[3]]),
			x[4]^2-R] : Saturated := true);
      return E,GetMap(fs,G,E);
    end if;
   
end function;

function gradedPiece(B,fs,d)
// B is a minimal basis for a homogeneous ideal I in a graded
// polynomial ring R=K[x1,..xn]. The xi <-> functions in an
// AlFF F given by fs  and I gives some but possibly not all
// relations between the fs - the full relation ideal being
// I1, say. For d>=1 function returns a basis in F for
// (R/I1)_d (the dth graded piece) if this has dim >=2 or
// and returns a set of polynomial generators for I1_d/I_d 
// also. Only called when dim (R_d/I_d) is >= 2

    R := Universe(B);
    K := BaseRing(R);
    mon_d := Setseq(MonomialsOfWeightedDegree(R,d));
    V := KSpace(K,#mon_d);
    mpToV := map<R->V | f :-> V![MonomialCoefficient(f,mon):mon in mon_d]>;

    // first quotient out by I_d
    Wvecs := [V|];
    for b in B do
	wb := WeightedDegree(b);
	if wb le d then
	    Wvecs cat:= [mpToV(b*m): m in 
		MonomialsOfWeightedDegree(R,d-wb)];
	end if;
    end for;
    W := sub<V|Wvecs>;
    V1 := Complement(V,W);

    // now find extra relations from I1, working in F
    V1pols := [&+[v[i]*mon_d[i] : i in [1..#mon_d]] where v is Eltseq(b):
		b in Basis(V1)];
    vec := [Evaluate(p,fs) : p in V1pols];
    rels := Basis(Relations(vec,K));
    rels := [&+[v[i]*V1pols[i] : i in [1..#V1pols]] where v is Eltseq(r):
		r in rels];
    V2 := Complement(V,W+sub<V|[mpToV(r) : r in rels]>);

    if Dimension(V2) ge 2 then
	V2pols := [&+[v[i]*mon_d[i] : i in [1..#mon_d]] where v is Eltseq(b):
		b in Basis(V2)];
	return [Evaluate(p,fs) : p in V2pols],rels;
    else
        return [],rels;
    end if;

end function;

function gen0_1_Common(G,diffs,mats,n)
// Common function for the genToGen0/1 cases. Finds a space
//  of linearly indep functions of dim >= n in an r-graded
//  piece of the invariant ring which will give an embedding
//  of the quotient of C by G onto a proj. normal variety in
//  ordinary projective space.
 
    C := Curve(G); K := BaseRing(C);
    F,ff_map := AlgorithmicFunctionField(FunctionField(C));
    diffs := [ff_map(d) : d in diffs];

    // now get the invariant ring of "multi-differentials"
    Gdiff := sub<GL(#diffs,K)|mats>;
    R := InvariantRing(Gdiff);
    A := Algebra(R);
    I := RelationIdeal(R);
    fs := [Evaluate(p,diffs) : p in PrimaryInvariants(R)] cat
	[Evaluate(s,diffs) : s in IrreducibleSecondaryInvariants(R)];

    // Want a graded component of Pcan^G/I_can^G of dim >= n.
    // Pcan^G/I_can^G is IM as a graded ring to A/I quotiented
    // out by additional relations from I_can^G which haven't
    // been taken into account in the invariants computation.
    // We consider graded parts of A/I, computing additional
    // relations and adding them to I as we go along.
    prec := 50;
    PS<T> := PowerSeriesRing(Integers():Precision := prec);
    r := 1;
    while true do
	r +:= 1;
        B := MinimalBasis(I);
	h := HilbertSeries(I);
	hT := PS!h;
	while Max(Coefficients(hT)) lt n do
	    prec *:=2;
	    AssertAttribute(PS,"Precision",prec);
	    hT := PS!h;
	end while;
	coeffs := Coefficients(hT);
	while coeffs[r] lt n do r +:=1; end while;
	fr,Iplus := gradedPiece(B,fs,r-1);
	if #fr ge n then return fr; end if;
	I := ideal<A|B cat Iplus>;
    end while;

end function;

function genToGen0Case(G,diffs,mats)

    fs := gen0_1_Common(G,diffs,mats,2);

    // get the rational normal embedding of CQ by functions fs
    CQ := FFCanonicalImage(fs,BaseRing(Curve(G)));
    // project down to a conic or P^1
    if #fs gt 3 then
	prm_CQ := ParametrizeRationalNormalCurve(CQ);
        CQ := Domain(prm_CQ);
        fs := [Evaluate(f,fs) :
		f in InverseDefiningPolynomials(prm_CQ)];
    end if;
    // Fix for the C hyperelliptic case: if w=hyp inv of C the CQ
    // with the above projection actually gives C/<G,w>. If w isn't
    // in G then the result is a degree 2 extension of CQ and we
    // must do more work. Test if this is the case by computing the
    // degree of the projection to CQ and comparing with #G
    d := Degree(fs[2]/fs[1]);
    if #fs eq 3 and Ambient(CQ)![0,0,1] notin CQ then
	assert IsEven(d);
	d := d div 2;
    end if;
    if d ne #G then
	assert d eq 2*(#G);
	return hypToGen0Case(G,CQ,fs);
    end if;
    return CQ,GetMap(fs,G,CQ);

end function;

function genToGen1Case(G,diffs,mats,diffG)

    fs := gen0_1_Common(G,diffs,mats,3);

    // get the projective normal embedding of CQ by functions fs
    // - this is gen by quadrics, but a different number than for
    //   canonical or rat normal embeddings, so compute here.
    K := BaseRing(Curve(G));
    d := #fs;
    Pd<[x]> := ProjectiveSpace(K,d-1);
    CRd := CoordinateRing(Pd);
    if d eq 3 then // cubic embedding in P^2
	// first check whether fs generate a conic: true if C is hyperelliptic
	//  and G doesn't contain the hyperelliptic involution. Then need
	//  to do extra work as in the general hyperelliptic quotient case
	//  to find a "y" coordinate
	f2s := [fs[i]*fs[j]: j in [i..d], i in [1..d]];
	quad_coeffs := Basis(Relations(f2s,K)); //get quadric relations
	delete f2s;
	if #quad_coeffs gt 0 then
	  assert #quad_coeffs eq 1;
	  v2 :=  [x[i]*x[j]: j in [i..d], i in [1..d]];
	  conQ := Conic(Pd,&+[(quad_coeffs[1])[i]*v2[i] : i in [1..#v2]]);
	  return hypToGen1Case(G,conQ,fs,diffG);  
	end if;
	f3s := [fs[i]*fs[j]*fs[k]: k in [j..d], j in [i..d], i in [1..d]];
	ter_coeffs := Basis(Relations(f3s,K)); //get all ternary relations
	delete f3s;
        assert #ter_coeffs eq 1;
        v3 := [x[i]*x[j]*x[k]: k in [j..d], j in [i..d], i in [1..d]];
	F :=  &+[r[i]*v3[i] : i in [1..#v3]] where r is ter_coeffs[1];
	CQ := Curve(Pd,F);
    else // proj normal embedding in P^(d-1), d > 3, gen by quadrics
	f2s := [fs[i]*fs[j]: j in [i..d], i in [1..d]];
	quad_coeffs := Basis(Relations(f2s,K)); //get all quadratic relations
	delete f2s;
	v2 :=  [x[i]*x[j]: j in [i..d], i in [1..d]];   
	Qs := [&+[r[i]*v2[i] : i in [1..#v2]] : r in quad_coeffs];
	CQ := Curve(Pd,Qs : Saturated := true);
	if #quad_coeffs eq ((d-1)*(d-2)) div 2 then
	  // CQ is a rational normal curve: true if C is hyperelliptic
	  //  and G doesn't contain the hyperelliptic involution. Then need
	  //  to do extra work as in the general hyperelliptic quotient case
	  //  to find a "y" coordinate
	  prm_CQ := ParametrizeRationalNormalCurve(CQ);
          CQ := Domain(prm_CQ);
          fs := [Evaluate(f,fs) : f in InverseDefiningPolynomials(prm_CQ)];
	  return hypToGen1Case(G,CQ,fs,diffG);
	end if;
	assert #quad_coeffs eq (d*(d-3)) div 2;
    end if;
    return CQ,GetMap(fs,G,CQ);

end function;


/********** MAIN FUNCTION ******************************************/

intrinsic CurveQuotient(G::GrpAutCrv) -> Crv, MapSch
{ If G is a group of automorphisms of a curve C of genus >= 2, computes
  the quotient of C by G, C/G, as an algebraic curve along with the
  projection map C -> C/G. }


    C := Curve(G);
    require Genus(C) ge 2: 
	"The genus of the curve to be quotiented must be >= 2";
    K := BaseRing(C);

    //handle trivial case
    if #G eq 1 then
	return C, IdentityMap(C);
    end if;

    //get group of reps on holo diffs
    gens := Generators(G);
    W,mp := SpaceOfHolomorphicDifferentials(C);
    mats := [Matrix([Eltseq(Inverse(mp)(g(mp(b)))) : b in Basis(W)]) :
		g in gens];

    // subspace of invariant global holo diffs
    WG := &meet[Kernel(H!(m - I)) : m in mats] where H is Hom(W,W)
     where I is IdentityMatrix(K,Dimension(W));

    // low genus cases
    gG := Dimension(WG);
    if gG le 1 then
	W1 := [mp(w)/w1 : w in Basis(W)] where w1 is mp(Basis(W)[1]);
	if gG eq 0 then
	    return genToGen0Case(G,W1,mats);
	else //gG eq 1
	    return genToGen1Case(G,W1,mats,mp(Basis(WG)[1]));
	end if;
    end if;

    // general case: WG gives canonical embedding of the quotient
    //  curve. Must still do some extra work if it's hyperelliptic!
    diffG := [mp(b) : b in Basis(WG)];
    PG<[x]> := ProjectiveSpace(K,gG-1);
    //canG := map<C->PG | [d/diffG[1] : d in diffG]>;
    F,ff_map := AlgorithmicFunctionField(FunctionField(C));
    ff_can := [ff_map(d/diffG[1]) : d in diffG];
    CQ,bHyp := FFCanonicalImage(ff_can,K);

    if not bHyp then // CQ is the quotient
	prj := GetMap(ff_can,G,CQ);
	return CQ,prj;
    end if;

    // hyperelliptic quotient case. 
    // First get map to P1 or conic
    if gG le 3 then //CQ already P^1 or a plane conic
	if gG eq 2 then
	    CQrat := CQ;
	else
	    CQrat := Conic(Ambient(CQ),DefiningEquation(CQ));
	end if;
        ff_rat := ff_can;
    else
        prm_CQ := ParametrizeRationalNormalCurve(CQ);
        CQrat := Domain(prm_CQ);
        ff_rat := [Evaluate(f,ff_can) : f in InverseDefiningPolynomials(prm_CQ)];
    end if;
    // See if  conic is split
    bSpl := true;
    if Type(CQrat) eq CrvCon then
	boo,pt := HasRationalPoint(CQrat);
	if boo then
	    prm_con := Parametrization(CQrat,pt,
			Curve(ProjectiveSpace(K,1)));
	    CQrat := Domain(prm_con);
	    ff_rat := [Evaluate(f,ff_rat) : f in InverseDefiningPolynomials(prm_con)];
	    bSpl := true;
	else
	    bSpl := false;
	end if;
    end if;
    // now get "y"-coordinate by considering differentials
    if bSpl then
	x := ff_rat[1]/ff_rat[2];
        A := PolynomialRing(K); X:=A.1;
	d := 2*gG+2;
	vec := [F!1,x];
	for i in [2..d] do
	    Append(~vec,x*vec[i]);
	end for;
	if Characteristic(K) ne 2 then
	    v := FunctionFieldDifferential(diffG[1])/Differential(x);
	    // v = P(x)/y for a polynomial P of degree <= gG-1
	    //  and y st y^2=Q(x), Q square free of deg 2gG+1or2
	    // - we find P and Q by getting K-linear relations in F
	    vec := [w*e : e in Reverse(vec)] cat
	      [vec[i] : i in [1..2*gG]] where w is v^2;
	    rels := Basis(Relations(vec,K));
	    delete vec;
	    assert #rels gt 0;
	    rels := EchelonForm(Matrix(rels));
	    rel := Eltseq(rels[Nrows(rels)]);
	    // this gives the relation R*v^2-S=0 with
	    //  R of smallest degree
	    r := 1;
	    while rel[r] eq K!0 do r +:= 1; end while;
	    assert r le gG+1;
	    R := &+[rel[i]*X^(d+1-i) : i in [r..d+1]];
	    S := - &+[rel[i+d+2]*X^i : i in [0..d-3]];
	    //assert Degree(GCD(R,S)) eq 0;
	    // Now S = U*V^2 with U square free and then
	    //  Q := U*R and P=U*V
	    U,V := SquareFreePart(S);
	    Q := U*R; P := U*V;
	    assert (Degree(Q) eq d) or (Degree(Q) eq d-1);
	    CQ := HyperellipticCurve(Q);
	    ff_CQ := [x,Evaluate(P,x)/v,F!1];

	else
	    // Char = 2 : In this case, unfortunately, we can't get
	    //  y from x and the holomorphic differentials [all the
            //  holo diffs on the hyp curve come from K(x)dx].
	    // We revert to looking at all G invariant functions in
	    //  the finite Riemann-Roch space of functions with poles
	    //  of restricted degree over the poles of x.
	    CQ,y := char2xtoy(G,vec,gG);
	    ff_CQ := [x,y,F!1];
	end if;
    else // geometrically hyperelliptic but not hyperelliptic over K
	assert IsOdd(gG);
	error if Characteristic(K) eq 2,
	    "Quotient is hyperelliptic w/o rational point over a ",
	    "char 2 function field. Sorry, can't handle this case!";
	// Similar to the 'split' case, though a little fiddlier.
	// (Affine) conic is Q(X,Y)=0. Z exists s.t. 
	//  Z^2=P(X,Y) for P(X,Y) of total degree gG+1 or gG &
	//  a basis for holomorphic differentials is
	//  U(X,Y)*dX/(Z*Qy(X,Y)) with total deg U(X,Y) <= (gG-1)/2
	//    [  Qy(X,Y) = dQ/dY(X,Y) ]
	CQa := AffinePatch(CQrat,1);
	CR<X,Y> := CoordinateRing(Ambient(CQa));
	x := ff_rat[1]/ff_rat[3];
	y := ff_rat[2]/ff_rat[3];
	Qy := Evaluate(Derivative(Equation(CQa),2),[x,y]);
	v := FunctionFieldDifferential(diffG[1])/Differential(x);
	// v = U(x,y)/(z*Qy(x,y)) for U as above.
	// v^2=U(x,y)^2/(P(x,y)*Qy(x,y)^2)
	// - we find U and P by getting K-linear relations in F
	d := gG+1;
	vec := [F!1,x];
	for i in [2..d+1] do
	    Append(~vec,x*vec[i]);
	end for;
	vec1 := [vec[i]*y : i in [1..d]];
	vec2 :=&cat[[vec1[d-i],vec[d+1-i]] : i in [0..d-1]] cat [vec[1]];
	vec := [w*e : e in vec2] cat [-vec[i]:i in [1..gG]] cat
	      [-vec1[i]:i in [1..gG-1]] where w is (Qy*v)^2;
	rels := Basis(Relations(vec,K));
	delete vec,vec1,vec2;
	assert #rels gt 0;
	rels := EchelonForm(Matrix(rels));
	rel := Eltseq(rels[Nrows(rels)]);
	// this gives the relation R*v^2-S=0 with
	//  R of smallest total degree
	R := &+[rel[2*i]*X^(d+1-i) : i in [1..d]] +
	  Y*&+[rel[2*i-1]*X^(d-i) : i in [1..d]] + rel[2*d+1];
	S := &+[rel[i]*X^(i-2*d-2) : i in [2*d+2..3*d]] +
	  Y*&+[rel[i]*X^(i-3*d-1) : i in [3*d+1..4*d-2]];	;
	// Now S(x,y) = A(x,y)*B(x,y)^2 with B "square free" and then
	//  P := A*R and U=A*B. As we are now working in the affine
	//  ring of CQa (still a UFD!) rather than K[X] we compute
	//  the square free decomposition in the FF of CQa
	A,B := FFSquareFreePart(S,CQa); // A,B lifted to CR
	P := A*R; U := A*B;
	assert (TotalDegree(P) eq gG+1) or (TotalDegree(P) eq gG);
	A3 := AffineSpace(K,3);
	CQ := ProjectiveClosure(Curve(A3,[
		Evaluate(Equation(CQa),[A3.1,A3.2]),
		A3.3^2-Evaluate(P,[A3.1,A3.2])]));
	ff_CQ := [x,y,Evaluate(U,[x,y])/(v*Qy),F!1];
    end if;
    //simplify the model if possible
    if Type(CQ) eq CrvHyp and K cmpeq Rationals() then
	CQ,mp := ReducedMinimalWeierstrassModel(CQ);
	ff_CQ := [Evaluate(f,ff_CQ) : f in DefiningPolynomials(mp)];
    end if;
    return CQ,GetMap(ff_CQ,G,CQ);

end intrinsic;
