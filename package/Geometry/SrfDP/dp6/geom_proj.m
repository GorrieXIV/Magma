freeze;

/* 
      Functions to perform geometric projections from points
	or tangent spaces of projective varieties.
	    mch - 05/06
*/

function LinearSpaceProjection(X,T,deg)
/* 
   X is a projective variety and T a linear subspace of its
   ambient s.t. projection from T gives a birational IM from
   X to Y and s.t. the birational inverse of the projection
   is given by polynomials of degree deg (in the ambient of Y).
   Function computes Y and returns the birational isomorphism
   prj.
*/
    P := Ambient(X);
    assert P eq Ambient(T);
    R := CoordinateRing(P);

    //change coords so that th tangent space is given by the
    // last r coords being 0
    V := KSpace(BaseRing(X),Rank(R));
    B := [[MonomialCoefficient(f,R.i):i in [1..Rank(R)]] :
		f in DefiningEquations(T)];
    W := sub<V|[V!b : b in B]>;
    M := Matrix([Eltseq(w): w in Basis(Complement(V,W))] cat B);
    lin_mp := Automorphism(P,Transpose(M));
    X1 := lin_mp(X);
    lin_mp := iso<X->X1|DefiningPolynomials(lin_mp),
		    InverseDefiningPolynomials(lin_mp) : Check := false>;

    n := Rank(R); r := #B;

    // first project by elimination
    I1 := ChangeOrder(Ideal(X1),"elim",n-r);
    R := Generic(I1);
    B := GroebnerBasis(I1);
    RY := PolynomialRing(BaseRing(X),r,"grevlex");
    Rhm := hom<R->RY | [RY|0 : i in [1..n-r]] cat [RY.i : i in [1..r]]>;
    IY := ideal<RY|[b : b in B | LeadingMonomial(b) lt R.(n-r)]@Rhm>;
    MarkGroebner(IY);
//printf "IY: %o\n",IY;
    Y := Scheme(Proj(RY),IY);

    // now we find the inverse map from Y -> X1 of the form
    //  [f1,..,fn] where the fi are homog of degree deg in
    //  x_(n-r+1)..xd.
    //  Need to solve xi*fn = xn*fi mod I1 for i = 1..n-1.
    //  We find fn by linear algebra.
    Rhm1 := hom<RY->R | [R.i:i in [n-r+1..n]]>;
    deg_fms := Setseq(MonomialsOfDegree(RY,deg))@Rhm1;
		//all degree deg forms in the last r variables.
    mat := Matrix([[NormalForm(f*R.i,I1) : f in deg_fms] : i in [1..n-1]]);
    mons := Setseq(&join[Seqset(Monomials(f)) : f in Eltseq(mat)]);
     // remove monomials in the last r vars which are divisible by R.n
    mons := [m : m in mons | m ge R.(n-1)^(deg+1)];
    mat1 := Transpose(Matrix([[MonomialCoefficient(f,m):f in r] : 
			r in RowSequence(mat), m in mons]));
    delete mons;
    B := Basis(Kernel(mat1));
     // any vector in B now gives the coefficients of a form fn
     // -need to find one where fn not in I1
    delete mat1;
//printf "#B: %o\n",#B;
    assert #B gt 0;
    Reverse(~B);
    fn := 0;
    for b in B do
	vec := b;
	fn := &+[vec[i]*deg_fms[i] : i in [1..#deg_fms]];
	if NormalForm(fn,I1) ne 0 then break; end if;
    end for;
    assert fn ne 0;
//printf "bs: %o\n",[NormalForm(&+[ve[i]*deg_fms[i] : i in [1..#deg_fms]],I1):ve in B];
//printf "fn: %o\nfs : %o\n",fn,Eltseq(vec*Transpose(mat));
    fs := [f div R.n : f in seq] cat [fn] where seq is
		Eltseq(vec*Transpose(mat));

    // finish off
    prj := iso<X1->Y| [CoordinateRing(P).i : i in [n-r+1..n]], fs@Rhm :
			Check := false>;
    return Expand(lin_mp * prj);

end function;

function TangentSpaceProjection(X,pt,deg)
// LinearSpaceProjection applied with T = tangent space of point pt
    return LinearSpaceProjection(X,TangentSpace(pt),deg);
end function;

function PointProjection(X,pt,deg)
// LinearSpaceProjection applied with T = point pt
    return LinearSpaceProjection(X,Cluster(Ambient(X)!pt),deg);
end function;

function GeometricProjectionMethodDeg6(X,pt,pt1)
/*
   X is a degree 6 del pezzo surface with distinct points
   pt & pt1 in it's big open orbit.
   Computes and returns the birational isomorphism phi: P^2 -> X
   whose inverse is projection from the tangent plane of pt
   followed by projection from the image of pt1.
*/
   mp_to_quad := TangentSpaceProjection(X,pt,3);
   Q := Codomain(mp_to_quad);
   mp_to_pln := PointProjection(Q,mp_to_quad(pt1),2);
   mp := Expand(mp_to_quad*mp_to_pln);
   return Inverse(mp);
end function;
