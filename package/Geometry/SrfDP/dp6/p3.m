freeze;

/*
    Functions for degree 6 Del Pezzo parametrisation that handle
     the cases when the torus comes from a degree 3 extension
                  of the base field.
			mch - 05/06
*/

import "loc_sol.m" : LocSolEverywhereDeg3;
import "geom_proj.m": GeometricProjectionMethodDeg6;

function FindInverses(eqs,P2,X)
/* 
   eqs give a rational parametrisation of deg 6 Del Pezzo X,
   phi: P2->X by cubics.
   This function finds a basis for the linear projections
   giving an inverse to phi and returns the isomorphism
   (with everwhere defined inverse equations).
*/
    R := CoordinateRing(P2);
    mat := Matrix(R,[[e*R.i : e in eqs]: i in [2,3]]);
    mons := Setseq(&join[Seqset(Monomials(f)): f in Eltseq(mat)]);
    mons := [m : m in mons | Exponents(m)[1] eq 0];
    mat1 := Matrix([[MonomialCoefficient(f,m):f in r]:
    		r in RowSequence(mat), m in mons]);
    B := Basis(Kernel(Transpose(mat1)));
    assert #B eq 3;
    
    invs := [];
    cubs := Setseq(MonomialsOfDegree(R,3));
    V := KSpace(BaseRing(R),10);
    W := VectorSpaceWithBasis(
	[V![MonomialCoefficient(f,cub):cub in cubs] : f in eqs]);
    R7 := CoordinateRing(Ambient(X));
    for b in B do
	c0 := &+[b[i]*R7.i:i in [1..7]];
	cs := mat*Matrix(R,7,1,Eltseq(b));
	cs := [Coordinates(W,V![MonomialCoefficient(q div R.1,cub):
			cub in cubs]) : q in Eltseq(cs)];
	Append(~invs,[c0] cat [&+[c[i]*R7.i:i in [1..7]] : c in cs]);
    end for;
    
    return iso<Proj(R)->X|eqs,invs : Check := false>;

end function;

function D3ParamGalois(K,Dsqrt,pt,X,M)
/*
   When K/k is Galois, finds a birational parametrisation of
   the homogeneous space directly.
   K := k(y) and Dsqrt should be a square root of the disc of
   the minimal polynomial of y.
   
   If R:K* -> GL3(k) is the regular rep of K [wrt 1,y,y^2 basis]
   and s is a generator of G(K/k) then the param (of Xa in A^6) is 
     P^2 -> (K*)/k* -> diag(R(su/u),R(u/su))*vec(pt) = Xa <= A6
     followed by M: A6 -> A6
*/
    y := K.1;
    k := BaseField(K);
    c,b,a := Explode(Coefficients(MinimalPolynomial(y)));
    My := Matrix(k,3,3,[0,0,-c,1,0,-b,0,1,-a]);
    My2 := My^2;

    rep := hom<K->MatrixAlgebra(k,3) | My>;

    sy := -(1/2)*(y+a+Dsqrt/(3*y^2+2*a*y+b));
    Msy := rep(sy);
    Msy2 := Msy^2;
    s2y := -(a+y+sy);
    Ms2y := rep(s2y);
    Ms2y2 := Ms2y^2;

    R := PolynomialRing(k,3);
    u := R.1 + R.2*ChangeRing(My,R)+R.3*ChangeRing(My2,R);
    su := R.1 + R.2*ChangeRing(Msy,R)+R.3*ChangeRing(Msy2,R);
    s2u := R.1 + R.2*ChangeRing(Ms2y,R)+R.3*ChangeRing(Ms2y2,R);

    nrm := (u*su*s2u)[1,1];
    M1 := su^2*s2u;
    M2 := u^2*s2u;
    eqs := Eltseq(ChangeRing(M,R)*DiagonalJoin(M1,M2)*Matrix(R,6,1,pt));
    Insert(~eqs,1,nrm);
    
    return FindInverses(eqs,Proj(R),X);

end function;

function D3ParamProj(K,pt,X,M)
/*
   In this case K/k is non-galois and we have the degree 3
   parametrisation of Xa (using the above notation)
     P^2 -> (K*)/k* -> diag(R(u^3/N(u)),R(N(u)/u^3))*vec(pt) = Xa <= A6
     followed by M: A6 -> A6
   We use this to find a point on Xa disticnt from pt and then use
   geometric projection for the birational parametrisation
*/

    y := K.1;
    k := BaseField(K);
    c,b,a := Explode(Coefficients(MinimalPolynomial(y)));
    My := Matrix(k,3,3,[0,0,-c,1,0,-b,0,1,-a]);
    My2 := My^2;
    rep := hom<K->MatrixAlgebra(k,3) | My>;

    // now find a smallish element u != 1 of norm 1 - use
    // elements of the form v^3/N(v), v in K*
    if (a eq 0) and (b eq 0) then // use v=y+1
	u := ((y+1)^3)/(1-a+b-c);
    else // use v = y
	u := (y^3)/(-c);
    end if;
    
    pt1 := Eltseq(DiagonalJoin(ru,ru^-1)*Matrix(6,1,pt))
	  where ru is rep(u);
    pts := RowSequence(Matrix([pt,pt1])*Transpose(M));
    return GeometricProjectionMethodDeg6(X,
		X!([1] cat pts[1]),X!([1] cat pts[2]));
end function;

/*
   X is a degree 6 Del Pezzo surface whose "7th" affine patch
   is the big open orbit (and with associated Lie algebra L).

   [Case where L generates a 6-dimensional commutative
   matrix algebra A IM to K plus K where K is a degree 3 field.]

   gen in L is a generator of A of trace 0 and facts are the
   irreducible factors of its characteristic polynomial.

   Determines whether X is parametrisable.

   If bParam is false, then only check for EXISTENCE of a
   parametrisation.
   Otherwise return a parametrisation is parametrisable.
*/
function D3Case(gen,facts,X,bParam)

    I := Ideal(AffinePatch(X,7));
    k := BaseRing(gen);
    assert (k cmpeq Rationals()) or ISA(Type(k), FldAlg);
    P := Generic(I);
    assert Rank(P) eq 6;
    assert BaseRing(P) eq k;

    // first we determine K from the characteristic poly
    // of gen. Note that gen should embed as (u,-u) for
    // a field generator, u, of K/k. So the char poly
    // should split as f(x)f(-x).
    assert Parent(f)!(&*facts) eq f where 
			f is CharacteristicPolynomial(gen);
    assert (#facts eq 2) and (Degree(facts[1]) eq 3)
              and (Degree(facts[2]) eq 3);
    f1 := facts[1]; f2 := facts[2];
    assert f2 eq -Evaluate(f1,-Parent(f1).1);

    // first change coords to block diagonalise gen
    M := Matrix(k,[Eltseq(b): b in Basis(Kernel(Evaluate(f1,gen)))]
	cat [Eltseq(b): b in Basis(Kernel(Evaluate(f2,gen)))]);
    Minv := M^(-1);
    gen := M*gen*Minv;
    assert &and[(gen[i,j] eq 0) and (gen[j,i] eq 0) : 
    			i in [1,2,3], j in [4,5,6]];

    boo,T := IsSimilar(Submatrix(gen,4,4,3,3),-Submatrix(gen,1,1,3,3));
    assert boo;
    M := DiagonalJoin(ScalarMatrix(3,k!1),T)*M;
    Minv := Minv*DiagonalJoin(ScalarMatrix(3,k!1),T^-1);
    //InsertBlock(~gen,-Submatrix(gen,1,1,3,3),4,4);
    gen1 := Submatrix(gen,1,1,3,3);

    K := ext<k|f1>;
    // if k is Q then attempt to get a simpler representative
    //  for the generator of K than the root of f1 and replace
    //  gen1 accordingly
    if k cmpeq Rationals() then // should do for general k ??
	K,mp := OptimisedRepresentation(K);
	gen1 := Evaluate(pol,gen1) where pol is
	  PolynomialRing(k)!Eltseq(Inverse(mp)(K.1));
	f1 := MinimalPolynomial(K.1);
        delete mp;
    end if;

    // find the transpose of matrix M1 taking the usual basis
    // [1,g,g^2,] of K (g is K.1) to basis [1=b1,b2,b3]
    // where the reg embedding of K by mult wrt bi basis takes
    // g to gen1.
    M1inv := Matrix(k,[[e[j,1]: j in [1..3]] where e is gen1^i :
			i in [0..2]]);
    M1inv := Transpose(M1inv);
    M1 := M1inv^(-1);
    M := DiagonalJoin(M1,M1)*M;
    Minv := Minv*DiagonalJoin(M1inv,M1inv);

    /* 
       now the coordinate change x_i -> sum_j M[i,j]*x_j puts
       the toric action into the required diagonal form, the
       torus embedding into GL_3(k) being wrt the basis
       1,g,g^2 of K.

       Now if the coordinates are x1..x6 and  C(a,b,c) is the
       cubic norm form N_(K/k)(a+bg+cg^2) then the equations
       of the affine part will be (over splitting field L of K)

           C(x1,x2,x3)=u  C(x4,x5,x6)=v
         X1*X4=s1(w) X2*X5=s2(w) X3*X6=s3(w)

       where s1,s2,s3 are the 3 embeddings of K into L
        u,v in k, w in K with u*v=N_(K/k)(w)
         X1=x1+s1(g)x2+s1(g^2)x3  X2= x1+s2(g)x2+s2(g^2)x3
                 X1=x1+s3(g)x2+s3(g^2)x3
        and X4,X5,X6 are X1,X2,X3 with [x1,x2,x3] replaced by
        [x4,x5,x6].
     */


    // define norm forms C1 and C2 wrt g^i basis ..
    Pt := PolynomialRing(P); t := Pt.1;
    f1R := &+[c[i+1]*t^i:i in [0..3]] where c is 
			Coefficients(f1);
    X1 := P.1+t*P.2+t^2*P.3;
    X4 := P.4+t*P.5+t^2*P.6;
    C1 := Resultant(X1,f1R);
    C2 := Evaluate(C1,[P.4,P.5,P.6,0,0,0]);
    Cs := [C1,C2];
    // now define X1*X4 in K[...]
    PK := PolynomialRing(K,6);
    X14 := hm(X1*X4) where hm is hom<Pt->PK|[K.1]>;
    // .. and define the 3 quadratic forms over k:
    //  Q1,Q2,Q3 in P s.t. X14 = Q1+g*Q2+g^2*Q3
    Qs := [ &+[Eltseq(LeadingCoefficient(t))[i]*
	   Monomial(P,Exponents(t)): t in Terms(X14)] : i in [1..3] ];


   // now change variables to get the forms wrt the original
   // x_i basis
   hm := hom<P->P| [&+[M[i,j]*P.j:j in [1..6]]:i in [1..6]]>;
   Q1s := Qs@hm;
   C1s := Cs@hm;

   // now there exist u,v in k and w in K by normal form comps
   // u = C1s[1] mod I, v = C1s[2] mod I and
   // if [r,s,t] = [Q1s mod I]
   // then w is determined by [Trace(w*g^i) i in [0,1,2]]=[r,s,t]
   //
   // we convert to a potentially easier GroebnerBasis
   
   J := EasyIdeal(I);
   PJ := Generic(J);

   us := [NormalForm(PJ!C,J) : C in C1s];
   assert &and[u in k: u in us];
   u := k!us[1]; v := k!us[2];

   ws := [NormalForm(PJ!Q,J) : Q in Q1s];
   assert &and[w in k: w in ws];
   ChangeUniverse(~ws,k);
   w := K!ws;

   delete J; delete PJ;

   assert Norm(w) eq (u*v);

   if bParam then
   	boo,soln := NormEquation(K,u);
   else
	return LocSolEverywhereDeg3(K,u),_;
   end if;

   if not boo then return false,_; end if;

   soln := soln[1];
   /* if soln = x1+x2g+x3g^2 this gives the first three coords.
      the others come from X1*X4=w => x4+x5g+x6g^2=w/soln */
   xs := Eltseq(soln) cat Eltseq(w/soln);

   boo,Dsqrt := IsSquare(Discriminant(f1));
   return true,(boo select D3ParamGalois(K,Dsqrt,xs,X,Minv)
   		else D3ParamProj(K,xs,X,Minv));

end function;
