freeze;

/*
    Functions for degree 6 Del Pezzo parametrisation that handle
     the cases when the splitting field of the torus is of
                 degree 2 over the base field.
			mch - 05/06
*/

import "loc_sol.m" : LocSolEverywhereDeg2;

/*
   X is a degree 6 Del Pezzo surface whose "7th" affine patch
   is the big open orbit (and with associated Lie algebra L).

   Case where L generates a 6-dimensional commutative matrix
   algebra A IM to K plus K plus k plus k
   where K is a degree 2 field over basefield k & the torus
   is K*.

   gen in L is a generator of A of trace 0 and facts are the
   irreducible factors of its characteristic polynomial.

   Determines whether X is parametrisable.

   If bParam is false, then only check for EXISTENCE of a
   parametrisation (trivially true in this case!).
   Otherwise return a parametrisation is parametrisable.
*/
function D2Case1(gen,facts,X,bParam)

    if not bParam then // in this case X always parametrisable!
	return true,_;
    end if;

    I := Ideal(AffinePatch(X,7));
    k := BaseRing(gen);
    assert (k cmpeq Rationals()) or ISA(Type(k), FldAlg);
    P := Generic(I);
    assert Rank(P) eq 6;
    assert BaseRing(P) eq k;

    // first we determine K from the characteristic poly
    // of gen. Note that gen should embed as
    // (u,-u,trace(u),-trace(u)) for a field generator, u,
    // of K/k [with non-zero trace]. So the char poly
    // should split as f(x)f(-x)L(x)L(-x).
    assert Parent(f)!(&*facts) eq f where
			f is CharacteristicPolynomial(gen);
    assert (#facts eq 4) and 
		(Sort([Degree(f) :f in facts]) eq [1,1,2,2]);
    f1,f2 := Explode([f : f in facts | Degree(f) eq 2]);
    assert f2 eq Evaluate(f1,-Parent(f1).1);
    L1,L2 := Explode([f : f in facts | Degree(f) eq 1]);
    assert L2 eq -Evaluate(L1,-Parent(L1).1);
    if Coefficient(L1,0) ne Coefficient(f1,1) then
	assert Coefficient(L1,0) eq Coefficient(f2,1);
	L := L2; L2 := L1; L1 := L;
    end if;

    // first change coords to block diagonalise gen
    M := Matrix(k,[Eltseq(b): b in Basis(Kernel(Evaluate(f1,gen)))]
	cat [Eltseq(b): b in Basis(Kernel(Evaluate(f2,gen)))] cat
	[Eltseq(b): b in Basis(Kernel(Evaluate(L1,gen)))] cat
	[Eltseq(b): b in Basis(Kernel(Evaluate(L2,gen)))] );
    Minv := M^(-1);
    gen := M*gen*Minv;
    assert &and[(gen[i,j] eq 0) and (gen[j,i] eq 0) :
    			i in [1,2], j in [3,4,5,6]] and
	   &and[(gen[i,j] eq 0) and (gen[j,i] eq 0) :
    			i in [3,4], j in [5,6]] and
	   (gen[5,6] eq 0) and (gen[6,5] eq 0);

    boo,T := IsSimilar(Submatrix(gen,3,3,2,2),-Submatrix(gen,1,1,2,2));
    assert boo;
    M := DiagonalJoin(DiagonalJoin(ScalarMatrix(2,k!1),T),ScalarMatrix(2,k!1))*M;
    Minv := Minv*
	DiagonalJoin(DiagonalJoin(ScalarMatrix(2,k!1),T^-1),ScalarMatrix(2,k!1));
    gen1 := Submatrix(gen,1,1,2,2);

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
    // [1,g] of K (g is K.1) to basis [1=b1,b2]
    // where the reg embedding of K by mult wrt bi basis takes
    // g to gen1.
    M1inv := Matrix(k,[[e[j,1]: j in [1..2]] where e is gen1^i :
			i in [0..1]]);
    M1inv := Transpose(M1inv);
    M1 := M1inv^(-1);
    M := DiagonalJoin(DiagonalJoin(M1,M1),ScalarMatrix(2,k!1))*M;
    Minv := Minv*DiagonalJoin(DiagonalJoin(M1inv,M1inv),ScalarMatrix(2,k!1));

    /* 
       now the coordinate change x_i -> sum_j M[i,j]*x_j puts
       the toric action into the required diagonal form, the
       torus embedding into GL_3(k) being wrt the basis
       1,g of K.

       Now if the coordinates are x1..x6 and  Q(a,b) is the
       quadratic norm form N_(K/k)(a+bg) then the equations
       of the affine part will be (over K)

           x6*Q(x1,x2)=u  x5*Q(x3,x4)=N_(K/k)(w)*v
         X1*X3=w   X2*X4=s(w)   x5*x6=u*v

       where G(K/k) = <s>, u,v in k, w in K,
           X1=x1+g*x2  X2= x1+s(g)*x2
        and X3,X4 are X1,X2 with [x1,x2] replaced by [x3,x4].
     */


    // get cubics & quadratics wrt g^i basis ..
    e1 := Trace(K.1); e2 := Norm(K.1);
    Cs := [P.6*(P.1^2+e1*P.1*P.2+e2*P.2^2),
		P.5*(P.3^2+e1*P.3*P.4+e2*P.4^2)];
    Qs := [P.1*P.3-e2*P.2*P.4,
		(P.2*P.3+P.1*P.4)+e1*P.2*P.4,P.5*P.6];

    // now change variables to get the forms wrt the original
    // x_i basis
    hm := hom<P->P| [&+[M[i,j]*P.j:j in [1..6]]:i in [1..6]]>;
    Q1s := Qs@hm;
    C1s := Cs@hm;

    // now if a = C1s[1] mod I, b = C1s[2] mod I and
    // if [r,s,t] = [Q1s mod I]
    // then u,v,w det by u=a, w = r+s*g, v = t/u &
    //  we should get b = v*N_(K/k)(w)
    //
    // we convert to a potentially easier GroebnerBasis

    J := EasyIdeal(I);
    PJ := Generic(J);

    us := [NormalForm(PJ!C,J) : C in C1s];
    assert &and[u in k: u in us];
    u := k!us[1]; b := k!us[2];
    assert u ne 0;

    ws := [NormalForm(PJ!Q,J) : Q in Q1s];
    assert &and[w in k: w in ws];
    ChangeUniverse(~ws,k);
    w := K![ws[1],ws[2]];
    v := ws[3]/u;

    delete J; delete PJ;

    assert b eq (v*Norm(w));

    // now we can just write down a degree 4 parametrisation of X
    // from the data
    R := PolynomialRing(k,3);
    P := CoordinateRing(Ambient(X));
    Q := R.1^2+e1*R.1*R.2+e2*R.2^2;
    f := e1*ws[1]+e2*ws[2];
    L1 := ws[1]*R.1+f*R.2;
    L2 := ws[2]*R.1-ws[1]*R.2;

    mp1 := [Q*R.1*R.3,Q*R.2*R.3,L1*R.3^3,L2*R.3^3,v*Q^2,u*R.3^4];
    mp1 := [Q*R.3^2] cat Eltseq(ChangeRing(Minv,R)*Matrix(R,6,1,mp1));
    vars := [P.1] cat Eltseq(ChangeRing(M,P)*Matrix(P,6,1,[P.i : i in [2..7]]));
    mp2 := [vars[2],vars[3],vars[1]];
    mp3 := [u*(ws[1]*vars[4]+f*vars[5]),u*(ws[2]*vars[4]-ws[1]*vars[5]),
		(ws[2]*f+ws[1]^2)*vars[7]];

    return true,iso<Proj(R)->X|mp1,[mp2,mp3] : Check := false>;

end function;

/*
   X is a degree 6 Del Pezzo surface whose "7th" affine patch
   is the big open orbit (and with associated Lie algebra L).

   Case where L generates a 6-dimensional commutative matrix
   algebra A IM to K plus K plus K
   where K is a degree 2 field over basefield k and the torus
   is K*.

   gen in L is a generator of A of trace 0 and facts are the
   irreducible factors of its characteristic polynomial.

   Determines whether X is parametrisable.

   If bParam is false, then only check for EXISTENCE of a
   parametrisation (trivially true in this case!).
   Otherwise return a parametrisation is parametrisable.
*/
function D2Case2(gen,facts,X,bParam)

    if not bParam then // in this case X always parametrisable!
	return true,_;
    end if;

    I := Ideal(AffinePatch(X,7));
    k := BaseRing(gen);
    assert (k cmpeq Rationals()) or ISA(Type(k), FldAlg);
    P := Generic(I);
    assert Rank(P) eq 6;
    assert BaseRing(P) eq k;

    // first we determine K from the characteristic poly
    // of gen. Note that gen should embed as 
    // (u,-u,2u-trace(u)) for a field generator, u,
    // of K/k [with non-zero trace]. So the char poly
    // should split as f(x)f(-x)R(x) where if
    // f(x) = x^2+ax+b (a,b != 0), R(x)=x^2+(2b-a^2).
    assert Parent(f)!(&*facts) eq f where
			f is CharacteristicPolynomial(gen);
    assert (Sort([Degree(f) :f in facts]) eq [2,2,2]) and
	    (#[f : f in facts | Coefficient(f,1) eq 0] eq 1);
    f1,f2 := Explode([f : f in facts | Coefficient(f,1) ne 0]);
    assert f2 eq Evaluate(f1,-Parent(f1).1);
    R := [f : f in facts | Coefficient(f,1) eq 0][1];
    assert Coefficient(R,0) eq
		4*Coefficient(f1,0)-Coefficient(f1,1)^2;

    // first change coords to block diagonalise gen
    M := Matrix(k,[Eltseq(b): b in Basis(Kernel(Evaluate(f1,gen)))]
	cat [Eltseq(b): b in Basis(Kernel(Evaluate(f2,gen)))] cat
	[Eltseq(b): b in Basis(Kernel(Evaluate(R,gen)))] );
    Minv := M^(-1);
    gen := M*gen*Minv;
    assert &and[(gen[i,j] eq 0) and (gen[j,i] eq 0) : 
    			i in [1,2], j in [3,4,5,6]] and
	   &and[(gen[i,j] eq 0) and (gen[j,i] eq 0) : 
    			i in [3,4], j in [5,6]];

    boo,T := IsSimilar(Submatrix(gen,3,3,2,2),-Submatrix(gen,1,1,2,2));
    assert boo;
    M := DiagonalJoin(DiagonalJoin(ScalarMatrix(2,k!1),T),ScalarMatrix(2,k!1))*M;
    Minv := Minv*
	DiagonalJoin(DiagonalJoin(ScalarMatrix(2,k!1),T^-1),ScalarMatrix(2,k!1));
    gen1 := Submatrix(gen,1,1,2,2);
    boo,T := IsSimilar(Submatrix(gen,5,5,2,2),2*gen1-Trace(gen1)*ScalarMatrix(2,k!1));
    if not boo then
        boo,T := IsSimilar(Submatrix(gen,5,5,2,2),-2*gen1+Trace(gen1)*ScalarMatrix(2,k!1));
	assert boo;
	// swap 1st 2 blocks
	mat := DiagonalJoin(Matrix(k,[[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]]),
				ScalarMatrix(2,k!1));
	M := mat*M; Minv := Minv*mat;
	gen1 := -gen1;
    end if;
    M := DiagonalJoin(ScalarMatrix(4,k!1),T)*M;
    Minv := Minv*DiagonalJoin(ScalarMatrix(4,k!1),T^-1);

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
    // [1,g] of K (g is K.1) to basis [1=b1,b2]
    // where the reg embedding of K by mult wrt bi basis takes
    // g to gen1.
    M1inv := Matrix(k,[[e[j,1]: j in [1..2]] where e is gen1^i :
			i in [0..1]]);
    M1inv := Transpose(M1inv);
    M1 := M1inv^(-1);
    M := DiagonalJoin(DiagonalJoin(M1,M1),M1)*M;
    Minv := Minv*DiagonalJoin(DiagonalJoin(M1inv,M1inv),M1inv);

    /* 
       now the coordinate change x_i -> sum_j M[i,j]*x_j puts
       the toric action into the required diagonal form, the
       torus embedding into GL_3(k) being wrt the basis
       1,g of K.

       Now if the coordinates are x1..x6 then the equations
       of the affine part will be (over K)

           X2*X3*X5=u*v  X1*X4*X6=s(u)*s(v)
         X1*X3=u   X2*X4=s(u)   X5*X6=v*s(v)

       where G(K/k) = <s>, u,v in k, w in K,
           X1=x1+g*x2  X2= x1+s(g)*x2
       X3,X4 are X1,X2 with [x1,x2] replaced by [x3,x4] and
       X5,X6 are X1,X2 with [x1,x2] replaced by [x5,x6].
     */


    // get cubics & quadratics wrt g^i basis ..
    e1 := Trace(K.1); e2 := Norm(K.1);
    Cs := [A*P.3-e2*B*P.4,A*P.4+B*(P.3+e1*P.4)] where
	A is P.1*P.5+e2*P.2*P.6+e1*P.2*P.5 where
	B is P.1*P.6-P.2*P.5;
    Qs := [P.1*P.3-e2*P.2*P.4,
		P.2*P.3+P.1*P.4+e1*P.2*P.4,
		P.5^2+e1*P.5*P.6+e2*P.6^2];

    // now change variables to get the forms wrt the original
    // x_i basis
    hm := hom<P->P| [&+[M[i,j]*P.j:j in [1..6]]:i in [1..6]]>;
    Q1s := Qs@hm;
    C1s := Cs@hm;

    // now if a = C1s[1] mod I, b = C1s[2] mod I and
    // if [r,s,t] = [Q1s mod I]
    // then u,v det by u*v=a+b*g, u = r+s*g &
    //  we should get t = N_(K/k)(v)
    //
    // we convert to a potentially easier GroebnerBasis

    J := EasyIdeal(I);
    PJ := Generic(J);

    ws := [NormalForm(PJ!C,J) : C in C1s];
    assert &and[w in k: w in ws];
    ChangeUniverse(~ws,k);
    uv := K!ws;

    us := [NormalForm(PJ!Q,J) : Q in Q1s];
    assert &and[u in k: u in us];
    ChangeUniverse(~us,k);
    u := K![us[1],us[2]];

    delete J; delete PJ;

    assert Norm(uv) eq (us[3]*Norm(u));
    v := uv/u;
    vs := Eltseq(v);

    // now we can just write down a degree 3 parametrisation of X
    // from the data
    R := PolynomialRing(k,3);
    P := CoordinateRing(Ambient(X));
    Q := R.1^2+e1*R.1*R.2+e2*R.2^2;
    mat := Matrix(k,[[us[1],e1*us[1]+e2*us[2]],[us[2],-us[1]]]);
    //L3 := us[1]*R.1-e2*us[2]*R.2;
    //L4 := us[2]*R.1+(us[1]+e1*us[2])*R.2;
    L3,L4 := Explode(Eltseq(ChangeRing(mat,R)*Matrix(R,2,1,[R.1,R.2])));
    L5,L6 := Explode([R.1*l3-e2*R.2*l4,R.1*l4+R.2*(l3+e1*l4)]) where
	l3 is vs[1]*R.1-e2*vs[2]*R.2 where
	l4 is vs[2]*R.1+(vs[1]+e1*vs[2])*R.2;

    mp1 := [Q*R.1,Q*R.2,L3*R.3^2,L4*R.3^2,L5*R.3,L6*R.3];
    mpf := [Q*R.3] cat Eltseq(ChangeRing(Minv,R)*Matrix(R,6,1,mp1));

    vars := [P.1] cat Eltseq(ChangeRing(M,P)*Matrix(P,6,1,[P.i : i in [2..7]]));
    mp2 := [vars[2],vars[3],vars[1]];
    // to get alternative inverse eqns, express 
    //   R.1*R.3^2,R.2*R.3^2 in terms of L3*R.3^2,L4*R.3^2 &
    //  R.1^2*R.3,R.1*R.2*R.3,R.2^2*R.3 in terms of 
    //    Q*R.3,L5*R.3,L6*R.3
    R133,R233 := Explode(Eltseq(ChangeRing(mat^-1,P) *
			Matrix(P,2,1,[P.4,P.5])));
    mat := Matrix(k,[[MonomialCoefficient(f,m) : m in 
	[R.1^2*R.3,R.1*R.2*R.3,R.2^2*R.3]] : f in [mpf[1],mp1[5],mp1[6]]]);
    boo,mat := IsInvertible(mat);
    assert boo;
    R113,R123,R223 := Explode(Eltseq(ChangeRing(mat,P) *
			Matrix(P,3,1,[P.1,P.6,P.7])));
    mp3 := [Evaluate(f,vars) : f in [R113,R123,R133]];
    mp4 := [Evaluate(f,vars) : f in [R123,R223,R233]];

    return true,iso<Proj(R)->X|mpf,[mp2,mp3,mp4] : Check := false>;

end function;

/*
   X is a degree 6 Del Pezzo surface whose "7th" affine patch
   is the big open orbit (and with associated Lie algebra L).

   Case where L generates a 6-dimensional commutative matrix
   algebra A IM to K plus K plus K
   where K is a degree 2 field over basefield k and the torus
   is K*_(norm=1) x K*_(norm=1).

   gen in L is a generator of A of trace 0 and facts are the
   irreducible factors of its characteristic polynomial.

   Determines whether X is parametrisable.

   If bParam is false, then only check for EXISTENCE of a
   parametrisation.
   Otherwise return a parametrisation is parametrisable.
*/
function D2Case3(gen,facts,X,bParam)

    I := Ideal(AffinePatch(X,7));
    k := BaseRing(gen);
    assert (k cmpeq Rationals()) or ISA(Type(k), FldAlg);
    P := Generic(I);
    assert Rank(P) eq 6;
    assert BaseRing(P) eq k;

    // first we determine K from the characteristic poly
    // of gen. Note that gen should embed as 
    // (u,v,u+v) for field generators, u,v,
    // of K/k with zero trace. So the char poly
    // should split as f1(x)f2(x)f3(x) where if
    // f1(x) = x^2-a, f2(x) = x^2-d^2*a,
    // f3(x)=x^2-(d+1)^2*a, a != 0, d != 0,1,-1,-2,-1/2
    // with suitable choice of signs for squareroots,
    // true for any pemutation of the polys!
    assert Parent(f)!(&*facts) eq f where
			f is CharacteristicPolynomial(gen);
    assert (#facts eq 3) and ([Degree(f) :f in facts] eq [2,2,2]);
    assert &and[Coefficient(f,1) eq 0 : f in facts];
    a,b,c := Explode([-Coefficient(f,0) : f in facts]);
    assert a*b*c ne 0;
    boo,rt_ba := IsSquare(b/a);
    error if not boo, "Degree 2 torus case: something's gone wrong!";
    if (c/a) ne (1+rt_ba)^2 then
	error if (c/a) ne (1-rt_ba)^2,
		"Degree 2 torus case: something's gone wrong!";
	rt_ba := - rt_ba;
    end if;
    f1,f2,f3 := Explode(facts);

    // first change coords to block diagonalise gen
    M := Matrix(k,[Eltseq(b): b in Basis(Kernel(Evaluate(f1,gen)))]
	cat [Eltseq(b): b in Basis(Kernel(Evaluate(f2,gen)))] cat
	[Eltseq(b): b in Basis(Kernel(Evaluate(f3,gen)))] );
    Minv := M^(-1);
    gen := M*gen*Minv;
    assert &and[(gen[i,j] eq 0) and (gen[j,i] eq 0) : 
    			i in [1,2], j in [3,4,5,6]] and
	   &and[(gen[i,j] eq 0) and (gen[j,i] eq 0) : 
    			i in [3,4], j in [5,6]];

    boo,T := IsSimilar(Submatrix(gen,3,3,2,2),rt_ba*Submatrix(gen,1,1,2,2));
    assert boo;
    M := DiagonalJoin(DiagonalJoin(ScalarMatrix(2,k!1),T),ScalarMatrix(2,k!1))*M;
    Minv := Minv*
	DiagonalJoin(DiagonalJoin(ScalarMatrix(2,k!1),T^-1),ScalarMatrix(2,k!1));
    gen1 := Submatrix(gen,1,1,2,2);
    boo,T := IsSimilar(Submatrix(gen,5,5,2,2),(1+rt_ba)*gen1);
    assert boo;
    M := DiagonalJoin(ScalarMatrix(4,k!1),T)*M;
    Minv := Minv*DiagonalJoin(ScalarMatrix(4,k!1),T^-1);

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
    // [1,g] of K (g is K.1) to basis [1=b1,b2]
    // where the reg embedding of K by mult wrt bi basis takes
    // g to gen1.
    M1inv := Matrix(k,[[e[j,1]: j in [1..2]] where e is gen1^i :
			i in [0..1]]);
    M1inv := Transpose(M1inv);
    M1 := M1inv^(-1);
    M := DiagonalJoin(DiagonalJoin(M1,M1),M1)*M;
    Minv := Minv*DiagonalJoin(DiagonalJoin(M1inv,M1inv),M1inv);

    /* 
       now the coordinate change x_i -> sum_j M[i,j]*x_j puts
       the toric action into the required diagonal form, the
       torus embedding into GL_3(k) being wrt the basis
       1,g of K.

       Now if the coordinates are x1..x6 then the equations
       of the affine part will be (over K)
         X1*X2=N(u)   X3*X4=N(v)   X5*X6=N(w)
           X1*X2*X6=u*v*s(w)  X3*X4*X5=s(u)*s(v)*w

       where G(K/k) = <s>, u,v,w in k*,
           X1=x1+g*x2  X2= x1+s(g)*x2
       X3,X4 are X1,X2 with [x1,x2] replaced by [x3,x4] and
       X5,X6 are X1,X2 with [x1,x2] replaced by [x5,x6].
     */


    // get cubics & quadratics wrt g^i basis ..
    e1 := Trace(K.1); e2 := Norm(K.1);
    Cs := [P.1*P.3*P.5+e1*P.1*P.3*P.6+
		e2*(P.1*P.4*P.6+P.2*P.3*P.6-P.2*P.4*P.5),
	   P.1*P.4*P.5+P.2*P.3*P.5-P.1*P.3*P.6+
	   	e1*P.2*P.4*P.5+e2*P.2*P.4*P.6];
    Qs := [P.1^2+e1*P.1*P.2+e2*P.2^2,
	   P.3^2+e1*P.3*P.4+e2*P.4^2,
	   P.5^2+e1*P.5*P.6+e2*P.6^2];

    // now change variables to get the forms wrt the original
    // x_i basis
    hm := hom<P->P| [&+[M[i,j]*P.j:j in [1..6]]:i in [1..6]]>;
    Q1s := Qs@hm;
    C1s := Cs@hm;

    // now if a = C1s[1] mod I, b = C1s[2] mod I and
    // if [r,s,t] = [Q1s mod I]
    // then N(u)=r,N(v)=s,N(w)=t and u*v*s(w)=a+gb
    //  we should get r*s*t = N_(K/k)(a+gb)
    //
    // we convert to a potentially easier GroebnerBasis

    J := EasyIdeal(I);
    PJ := Generic(J);

    ws := [NormalForm(PJ!C,J) : C in C1s];
    assert &and[w in k: w in ws];
    ChangeUniverse(~ws,k);
    uvsw := K!ws;

    us := [NormalForm(PJ!Q,J) : Q in Q1s];
    assert &and[u in k: u in us];
    ChangeUniverse(~us,k);
    r,s,t := Explode(us);

    delete J; delete PJ;

    assert Norm(uvsw) eq r*s*t;

    // We now have to check solubility of N(u)=r & N(v)=s
    //  Can then determine u,v,w from the data - note that
    //  u,v are both arbitrary up to elts of K of norm 1
    //  but once they are fixed then w is determined from uvsw
    if bParam then
	boo,soln := NormEquation(K,r);
	if not boo then return false,_;end if;
	u := soln[1];
	boo,soln := NormEquation(K,s);
	if not boo then return false,_;end if;
	v := soln[1];
	w := uvsw/(u*v);
	w := Trace(w)-w;
    else
	return (LocSolEverywhereDeg2(K,r) and 
				LocSolEverywhereDeg2(K,s)),_;
    end if;

    // now we can just write down a degree 4 parametrisation of X
    // from the data
    R := PolynomialRing(k,3);
    P := CoordinateRing(Ambient(X));

     //easiest to work over K in this case
    R1 := ChangeRing(R,K);
    hm1 := hom<R1->R|map<K->R|x :-> R!(Eltseq(x)[1])>,[R.1,R.2,R.3]>;
    hm2 := hom<R1->R|map<K->R|x :-> R!(Eltseq(x)[2])>,[R.1,R.2,R.3]>;
    Q1 := R.1^2+e1*R.1*R.3+e2*R.3^2;
    Q2 := R.2^2+e1*R.2*R.3+e2*R.3^2;
    f1 := (R1.1+K.1*R1.3)^2;
    f2 := (R1.2+K.1*R1.3)^2;

    mp1 := [hm1(A)*Q2,hm2(A)*Q2,hm1(B)*Q1,hm2(B)*Q1,hm1(C),hm2(C)]
	where A is u*f1 where B is v*f2 where C is w*(f1*f2);
    mpf := [Q1*Q2] cat Eltseq(ChangeRing(Minv,R)*Matrix(R,6,1,mp1));

    P1 := ChangeRing(P,K);
    hm1 := hom<P1->P|map<K->P|x :-> P!(Eltseq(x)[1])>,[P.i : i in [1..7]]>;
    hm2 := hom<P1->P|map<K->P|x :-> P!(Eltseq(x)[2])>,[P.i : i in [1..7]]>;
    vars := [P1.1] cat Eltseq(ChangeRing(M,P1)*Matrix(P1,6,1,[P1.i : i in [2..7]]));
    A := (vars[2]+K.1*vars[3])/u;
    B := (vars[4]+K.1*vars[5])/v;
    C := (vars[6]+K.1*vars[7])/w;
    z := (C+vars[1]-A-B)/(2*K.1-e1);
    x := C-A-z*K.1;
    y := C-B-z*K.1;
    // first inverse map
    mp2 := [hm1(x),hm1(y),hm1(z)];
    // second inverse map
    mp3 := [hm2(x),hm2(y),hm2(z)];

    return true,iso<Proj(R)->X|mpf,[mp2,mp3] : Check := false>;

end function;
