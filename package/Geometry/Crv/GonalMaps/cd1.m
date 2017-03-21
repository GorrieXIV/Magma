freeze;
////////////////////////////////////////////////////////////////
//      Trigonal Maps (or isomorphism to plane quintic) for   //
//        non-hyperelliptic curves of Clifford index 1.   //
//      Adapted from J. Schicho's code to parametrise scrolls //
//       and Veronese surfaces. Uses Schicho and Sevilla's    //
//               method based on Lie algebras.                //
//            mch - 02/12                                     //
////////////////////////////////////////////////////////////////

import "../../SrfHyp/quadratic.m":PointOnQuadric;
import "../../SrfDP/dp6/geom_proj.m":LinearSpaceProjection;

function conic_point(C)
// returns a point on plane conic C defined over a quadratic extension
//  of the base (assumed that C has no points over the basefield)
  k := BaseRing(C);
  R := PolynomialRing(k);
  f := Evaluate(DefiningPolynomial(C),[R.1,0,1]);
  assert Degree(f) eq 2;
  K := ext<k|f>;
  return [K.1,0,1];  
end function;

function quadric_point(Q)
// returns a point on nonsingular quadric surface Q in P^3 defined over a
// quadratic extension of the base if necessary
  k := BaseRing(Q);
  if Type(k) cmpeq FldFin then
    pts := RationalPointsByFibration(Q : Max := 1);
    assert #pts gt 0;
    return Eltseq(pts[1]);
  end if;
  if k cmpeq Rationals() then
    boo,pt := PointOnQuadric(DefiningPolynomial(Q));
    if boo then return Eltseq(pt); end if;
  end if;
  //default: get point over quadratic extension
  R := PolynomialRing(k);
  f := Evaluate(DefiningPolynomial(Q),[R.1,0,0,1]);
  rts := Roots(f);
  if #rts gt 0 then
    return [rts[1][1],0,0,1];
  end if;
  K := ext<k|f>;
  return [K.1,0,0,1];  
end function;

function quartic_point(C)
// returns a point on nonsingular quartic curve C in P^2 defined over an
// extension (of deg <= 4) of the base if necessary
  k := BaseRing(C);
  if Type(k) cmpeq FldFin then
    pts := RationalPointsByFibration(C : Max := 1);
    if #pts gt 0 then
      return Eltseq(pts[1]);
    end if;
  end if;
  if k cmpeq Rationals() then
    pts := PointSearch(C,100);
    if #pts gt 0 then
      return Eltseq(pts[1]);
    end if;
  end if;
  //default
  P := Ambient(C);
  pts := Scheme(C,P.1);
  pts := PrimeComponents(pts);
  degs := [Degree(p) : p in pts];
  m := Min(degs);
  pt := pts[Index(degs,m)];
  if m eq 1 then
    pt := Support(pt)[1];
    return Eltseq(pt);
  end if;
  D := Divisor(C,Ideal(pt));
  pls,es := Support(D);
  assert es eq [1];
  pl := pls[1];
  pt := RepresentativePoint(pl);
  return Eltseq(pt); 
end function;

function FindXH(L)
// Lie algebra L is isomophic to a twist of sl2. Returns a generator h of a Cartan
// subalgebra and an x s.t. [h,x]=2x, over a quadratic extension if necessary

  k := CoefficientRing(L);
  P2<u,v,w> := ProjectiveSpace(k,2);
  Nilp := Conic(KillingForm(L));
  bsoln, pt := HasRationalPoint(Nilp);
  if not bsoln then //extend to a quadratic field
    seq := conic_point(Nilp);
    L := ChangeRing(L,Universe(seq));
    x := L!seq;
  else
    x := L!Coordinates(pt);
  end if;
  h := L!Eltseq(Solution(Matrix([ L.i*x : i in [1..3]]),2*x));
  return x,h;

end function;

function quadric_scroll_map(X)
// X is an irreducible quadric surface in P^3. Computes
//  a fibre map to P^1, over a quadratic or biquadratic extension
//  if necessary.

    S := SingularSubscheme(X);
    if Dimension(S) ge 0 then
	assert (Dimension(S) eq 0) and (Degree(S) eq 1);
	pt := Eltseq(Support(S));
	assert #pt eq 1;
	pt := pt[1];
	_,prj := Projection(P3,P3!Eltseq(pt)) where
		P3 is Ambient(X);
	P2 := Ambient(Codomain(prj));
	prj := map<X->P2|DefiningPolynomials(prj)>;
	C := Conic(Image(prj));
	prj := map<X->C|DefiningPolynomials(prj) : Check := false>;
  	bsoln, pt := HasRationalPoint(C);
  	if not bsoln then //extend to a quadratic field
    	  pt_seq := conic_point(C);
	  K := Universe(pt_seq);
	  _,prj1 := Projection(P2K,P2K!pt_seq) where 
			P2K is BaseChange(P2,K);
	  defs := [R!f : f in DefiningPolynomials(prj)] where
		R is CoordinateRing(BaseChange(Ambient(X)),K);
	else
	  _,prj1 := Projection(P2,P2!Coordinates(pt));
	  defs := DefiningPolynomials(prj);
    	end if;
    else
	k := BaseRing(X);
	P3 := Ambient(X);
	pt_seq := quadric_point(X);
	K := Universe(pt_seq);
	if K cmpeq k then
	  prj := LinearSpaceProjection(X,Cluster(P3!pt_seq),2);
	  XK := X;
	else
	  XK := BaseChange(X,K);
	  P3K := Ambient(XK);
	  prj := LinearSpaceProjection(XK,Cluster(P3K!pt_seq),2);
	end if;
	bs := BaseScheme(Inverse(prj));
	assert Degree(bs) eq 2;
	// must project to P^1 from one of the points in bs
        supp := Setseq(Support(bs));
	P2K := Ambient(Codomain(prj));
	if #supp gt 0 then
	  pt1 := supp[1];
	  _,prj1 := Projection(P2K,P2K!Coordinates(pt1));
	  defs := DefiningPolynomials(prj);
	else //must take another quadratic extension!
	  i := 3;
	  bsa := AffinePatch(bs,1);
	  if IsEmpty(bsa) then
	    i := 2; bsa := AffinePatch(bs,2);
	  end if;
	  GB := GroebnerBasis(Ideal(bsa));
	  R1 := Generic(Universe(GB));
	  if Degree(GB[2],R1.2) eq 1 then
	     e := -MonomialCoefficient(GB[2],R1!1)/
			MonomialCoefficient(GB[2],R1.2);
	     f := UnivariatePolynomial(GB[1]);
	     assert Degree(f) eq 2;
	     K1 := ext<K|f>;
	     pt1_seq := [K1.1,e];
	  else //GB[2] a quadric in R1.2
	     f := UnivariatePolynomial(GB[2]);
	     assert Degree(f) eq 2;
	     K1 := ext<K|f>;
	     P := PolynomialRing(K1);
	     f1 := Evaluate(GB[1],[P.1,K1.1]);
	     e := -Coefficient(f1,0)/Coefficient(f1,1);
	     pt1_seq := [e,K1.1];
	  end if;
	  Insert(~pt1_seq,i,1);
	  P2K1 := ProjectiveSpace(K1,2);
	  _,prj1 := Projection(P2K1,P2K1!pt1_seq);
	  defs := [R!f : f in DefiningPolynomials(prj)] where
		R is CoordinateRing(BaseChange(Ambient(XK),K1));
	end if;
    end if;
    vs := [Evaluate(f,defs) : f in DefiningPolynomials(prj1)];
    return vs;
end function;

function parametrize_veronese(X,L,Repr)
// Copy of Schicho's code to parametrize the Veronese surface X in P^5
// where the Lie algebra is L. Inefficient to copy the code but
// avoids recomputing L and Levi subalgebra ls (=L)!

    I := Ideal(X);
    R := Generic(I);
    n := Rank(R); //n=6!
    k := CoefficientRing(I);
    P2<s,t,u> := ProjectiveSpace(k,2);
    Par:= CoordinateRing(P2);
    Vn := VectorSpace(k,n);

    standardpar := [ Par | s^2, s*t, t^2, s*u, t*u, u^2 ];
    inv := Transpose(Matrix([Vn.1,Vn.2,Vn.4]));

    cs:=CartanSubalgebra(L);
    C1t := Transpose(Repr(L!cs.1));
    C2t := Transpose(Repr(L!cs.2));

    // get an element with generic minimal polynomial 
    // (final output is still deterministic)
    cc:= [-100..100];
    found:= false;
    while not found do
      Rant:= C1t + Random(cc)*C2t;
      Mpol := MinimalPolynomial(Rant);
      facts:= Factorization(Mpol);
      multiplicities := { v[2] : v in facts};
      if (multiplicities eq {1}) then
        found:= true;
      end if;
    end while;

    // get matrices and split the cs-module
    // (depends only on cs and not on Rant)
    Polrng<t> := Parent(Mpol);
    subst := hom<Polrng ->Polrng | -2*t>;
    Mpol1 := &* [v[1] : v in facts | IsDivisibleBy(Mpol,subst(v[1])) ];
    _,Mpol2 := IsDivisibleBy(Mpol,Mpol1);
    Matn := MatrixAlgebra(k,6);
    subst := hom<Polrng ->Matn | Matn!Rant>;
    Vsub1 := Nullspace(subst(Mpol1));
    Vsub2 := Nullspace(subst(Mpol2));
    T := VerticalJoin(Morphism(Vsub2,Vn),Morphism(Vsub1,Vn));
    E := HorizontalJoin(ScalarMatrix(k,3,1),ZeroMatrix(k,3,3));
    TO := E*T; OT := T^-1*Transpose(E);

    // construct a 3D module of L
    Mat3 := MatrixAlgebra(k,3);
    getblock := map< L -> Mat3 | x :-> TO*Transpose(Repr(x))*OT >;
    rho := map< L -> Mat3 | 
      x :-> getblock(x)-2*getblock(ProjKilling(x,cs)) >;
    
    // get some Chevalley basis elements
    V9 := VectorSpace(k,9);
    sys := Matrix([ V9!(Eltseq(rho(L.i))) : i in [1..8] ]);

    solh := Solution(sys,V9![0,0,0,0,-1,0,0,0,1]);
    h := &+ [ solh[i] * L.i : i in [1..8] ];
    solx := Solution(sys,V9![0,0,0,0,0,1,0,0,0]);
    x := &+ [ solx[i] * L.i : i in [1..8] ];
    solz := Solution(sys,V9![0,0,1,0,0,0,0,0,0]);
    z := &+ [ solz[i] * L.i : i in [1..8] ];

    Ht := Transpose(Repr(h));
    Xt := Transpose(Repr(x));
    Zt := Transpose(Repr(z));

    space := Eigenspace(Ht,2);
    assert Dimension(space) eq 1;
    v1 := space.1;
    v2 := v1 * Xt;
    v3 := 1/2 * v2 * Xt;
    v4 := v1 * Zt;
    v5 := v4 * Xt;
    v6 := 1/2 * v4 * Zt;

    Rows := [v1,v2,v3,v4,v5,v6];
    M := Matrix(Rows);
    Mi := M^-1*inv;
    para := Eltseq(Vector(standardpar) * ChangeRing(M,Par));
    back := Vector([R.i: i in [1..n]]) * ChangeRing(Mi,R);
    parai := Eltseq(back);
    phi := map<P2 -> X | para, parai>;

    return phi;

end function;

// Generate fibre-map for rational scroll X to P^1, possibly over a
// quadratic extension of the base. Adapted from J. Schicho's
// scroll parametrisation code and using his and David Sevilla's
// application of the Lie algebra method to compute the linear
// pencil on X giving the required map to P^1 via appropriate
// eigenvectors. L and ls are the Lie algebra of X and a Levi
// subalgebra that have already been computed.
function scroll_map(X,L,ls,Repr)

  I := Ideal(X);
  R := Generic(I);
  n := Rank(R);
  k := CoefficientRing(I);
  Vn := VectorSpace(k,n);

  if (Dimension(ls) eq 3) then // scroll with distinguished section
    
    // identification
    adL := AdjointRepresentation(L);
    space := &meet [Nullspace(adL(L!ls.i)) : i in [1..3]];
    assert (Dimension(space) eq 1);
    sep := L!Basis(space)[1];
    Sept := Transpose(Repr(sep));
    ev := Eigenvalues(Sept);
    mults := [ v[2] : v in ev ];
    m1 := Maximum(mults);
    m2 := Minimum(mults);

    // now get a Chevalley basis. For efficiency reasons,
    // get an irreducible representation of even degree if possible
    if IsEven(m1*m2) and (Characteristic(k) eq 0) then
      // decompose the module
      val1 := [v[1] : v in ev | v[2] eq m1 ][1]; 
      val2 := [v[1] : v in ev | v[2] eq m2 ][1]; 
      T1 := Morphism(Eigenspace(Sept,val1),Vn);
      T2 := Morphism(Eigenspace(Sept,val2),Vn);
      // project to an evendimensional submodule (smaller preferred)
      if IsEven(m2) then
        Tboth := VerticalJoin(T2,T1);
        One := ScalarMatrix(k,m2,1);
        E := HorizontalJoin(One,ZeroMatrix(k,m2,m1));
        Mat := RMatrixSpace(k,m2,m2);
      else // m1 must be even
        Tboth := VerticalJoin(T1,T2);
        One := ScalarMatrix(k,m1,1);
        E := HorizontalJoin(One,ZeroMatrix(k,m1,m2));
        Mat := RMatrixSpace(k,m1,m1);
      end if;
      TO := E*Tboth; OT := Tboth^-1*Transpose(E);
      Corr := TO*Sept*OT;
      Detrace := map< Mat -> Mat | 
             x :-> x - Trace(x)/m1 * One >;
      Rep := map< ls -> Mat | 
             x :-> -Detrace(TO*Transpose(Repr(L!x))*OT) >;
      _, CB := RepChevalleyBasis(Rep);
      h := L!CB[3];
      x := L!CB[1];
    else // this branch requires conic solving over k
      x,h := FindXH(ls);
      if Parent(h) cmpeq ls then //no basefield extension required
         x := L!x; h := L!h;
      else
	 x := Eltseq(x); h := Eltseq(h);
	 LK := ChangeRing(L,Universe(h));
	 B := Matrix([ChangeUniverse(Eltseq(L!b),K) : b in Basis(ls)])
		where K is Universe(h);
	 x := Eltseq(Vector(x)*B);
	 h := Eltseq(Vector(h)*B);
      end if;
    end if;

    if Parent(h) cmpeq L then //no basefield extension required
       Ht := Repr(h);
       Xt := Repr(x);
       K := k;
    else
       seqs := [x,h];
       K := Universe(h);
       Xt,Ht := Explode([&+[seq[i]*ChangeRing(Repr(L.i),K):i in [1..#seq]]:
			seq in seqs]);
    end if;
    
    // get required eigenvectors
    space := Eigenspace(Ht,m1-1);
    assert (Dimension(space) eq 1);
    v := Basis(space)[1];
    w := /*(1/K!(m1-1))*/(v*Xt);   
  elif (Dimension(ls) eq 6) then // product of two P1s  

    dsd := DirectSumDecomposition(L);
    assert (#dsd eq 2);

    // separate the two summands rightly:
    // L2 has the module of degree 2
    L1 := dsd[1]; L2 := dsd[2];
    C1 := CartanSubalgebra(L1);
    ar := L!Basis(C1)[1];
    Art := Transpose(Repr(ar));
    if (Degree(MinimalPolynomial(Art)) eq 2) then
      L1 := dsd[2]; L2 := dsd[1];
    end if;

    // Chevalley basis of L1 
    // requires conic solving over k
    x,h := FindXH(L1);
    if Parent(h) cmpeq ls then //no basefield extension required
         x := L!x; h := L!h;
    else
	 x := Eltseq(x); h := Eltseq(h);
	 LK := ChangeRing(L,Universe(h));
	 B := Matrix([ChangeUniverse(Eltseq(L!b),K) : b in Basis(L1)])
		where K is Universe(h);
	 x := Eltseq(Vector(x)*B);
	 h := Eltseq(Vector(h)*B);
    end if;

    if Parent(h) cmpeq L then //no basefield extension required
       Ht := Repr(h);
       Xt := Repr(x);
       K := k;
    else
       seqs := [x,h];
       K := Universe(h);
       Xt,Ht := Explode([&+[seq[i]*ChangeRing(Repr(L.i),K):i in [1..#seq]]:
			seq in seqs]);
    end if;
    // get eigenvectors
    Smod := Eigenspace(Ht,n/2-1);
    assert (Dimension(Smod) eq 2);
    v := Basis(Smod)[1];
    w := /*(1/K!((n/2)-1))*/(v*Xt);  
  else
    error "surface is not of minimal degree";
  end if;
  
  // the result 
  Xs := [A.i : i in [1..n]] where A is
	((K cmpeq k) select Ambient(X) else BaseChange(Ambient(X),K));
  return [Polynomial(Eltseq(v),Xs),Polynomial(Eltseq(w),Xs)];

end function;

intrinsic CliffordIndexOne(C::Crv) -> MapSch
{C is a genus g curve canonically embedded in P^(g-1) which is either trigonal
or is isomorphic to a smooth plane quintic (g=6).
Returns a degree 3 map to P^1 over an extension field in the trigonal case,
or an isomorphism onto a plane quintic in the other case.  }

  k := BaseRing(C);
  P := Ambient(C);
  g := Rank(CoordinateRing(P));
  if g gt 4 then
    require Characteristic(k) ne 2: 
      "The characteristic of the base field cannot be 2";
  end if;
  nquads := ((g-2)*(g-3)) div 2;
  B := [f : f in DefiningPolynomials(C) | TotalDegree(f) eq 2];
  if #B eq nquads then
    X := Scheme(P,B);
  else
    Saturate(~C);
    B := [f : f in Basis(Ideal(C)) | TotalDegree(f) eq 2];
    if #B ne nquads then
      B := [f : f in MinimalBasis(Ideal(C)) | TotalDegree(f) eq 2];
      error if (#B ne nquads), "C is not a canonical curve";
    end if;
    X := Scheme(P,B);
  end if;
  return CliffordIndexOne(C,X);

end intrinsic;
    

intrinsic CliffordIndexOne(C::Crv, X::Sch) -> MapSch
{C is a genus g curve canonically embedded in P^(g-1) which is either trigonal
or is isomorphic to a smooth plane quintic (g=6). X is the rational scroll
surface containing C defined by the degree 2 polynomials in the ideal of C.
Returns a degree 3 map to P^1 over an extension field in the trigonal case,
or an isomorphism onto a plane quintic in the other case.  }

  I := Ideal(X);
  R := Generic(I);
  k := BaseRing(C);
  n := Rank(R);
  if n gt 4 then
    require Characteristic(k) ne 2: 
      "The characteristic of the base field cannot be 2";
  end if;

  if n eq 3 then //g=3 case - smooth plane quartic
    pt_seq := quartic_point(C);
    K := Universe(pt_seq);
    P2K := (K cmpeq k) select Ambient(C) else BaseChange(Ambient(C),K);
    _,prj := Projection(P2K,P2K!pt_seq);
    vs := DefiningPolynomials(prj);
  elif n eq 4 then
    //X is a quadric surface in P3
    vs := quadric_scroll_map(X);
  else
    Repr := myFindLieAlgebra(I);
    L := Domain(Repr);
    boo, ls := HasLeviSubalgebra(L);
    error if not boo, "Characteristic " cat IntegerToString(Characteristic(k)) cat
	" problem. Sorry, the implementation could not carry out a required Lie algebra" cat
	" splitting in this characteristic.";
    if Dimension(ls) eq 8 then // X is Veronese, C is IM to a smooth plane quintic
	phi := parametrize_veronese(X,L,Repr);
	defs := DefiningPolynomials(Inverse(phi));
	C5 := Image(map<C->Domain(phi)|defs>);
	phi := iso<C->C5|defs,DefiningPolynomials(phi) : Check := false>;
	return phi;
    else // X a rational scroll and C has gonality 3
	vs := scroll_map(X,L,ls,Repr);
    end if;
  end if;
  if Universe(vs) cmpeq R then //no base change
    P1 := Curve(ProjectiveSpace(k,1));
    trig := map<C->P1|vs : Check := false>;
  else // base change
    K := BaseRing(Universe(vs));
    C1 := BaseChange(C,K);
    vs := [R1!v : v in vs] where R1 is CoordinateRing(Ambient(C1));
    P1 := Curve(ProjectiveSpace(K,1));
    trig := map<C1->P1|vs : Check := false>;
  end if;
  return trig;

end intrinsic;

/* twisted sl2 corr to the quat alg (d,e)
> d := -1; e := -1;
> mat1 := Matrix(Q,3,3,[0,0,0,0,0,2,0,2*d,0]);
> mat1;
[ 0  0  0]
[ 0  0  2]
[ 0 -2  0]
> mat2 := Matrix(Q,3,3,[0,0,-2,0,0,0,-2*e,0,0]);  
> mat2;
[ 0  0 -2]
[ 0  0  0]
[ 2  0  0]
> mat3 := Matrix(Q,3,3,[0,-2*d,0,2*e,0,0,0,0,0]);   
> mat3;
[ 0  2  0]
[-2  0  0]
[ 0  0  0]
> L := LieAlgebra<Q,3|[RowSequence(m) : m in [mat1,mat2,mat3]]>;
*/
