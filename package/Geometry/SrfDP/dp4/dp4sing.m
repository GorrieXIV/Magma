freeze;
/////////////////////////////////////////////////////////////////////////////////
//          PARAMETRISATION OF DEGREE 4 DEL PEZZO SURFACES                     //
//                    SPECIAL SINGULAR CASE				       //
//                 Main function. mch - 03/10                                  //
/////////////////////////////////////////////////////////////////////////////////

import "../dp6/geom_proj.m": LinearSpaceProjection,PointProjection;

/*
function MyHasPoint(C)
// remove later!
    R := CoordinateRing(Ambient(C));
    k := BaseRing(R);
    eqn := Equation(C);
    a := MonomialCoefficient(eqn,R.1^2);
    b := MonomialCoefficient(eqn,R.2^2);
    c := MonomialCoefficient(eqn,R.3^2);
    
    L := ext<k|PolynomialRing(k)![b/a,0,1]>;
    boo,u := NormEquation(L,-c/a);
    if not boo then return boo,_; end if;
    u1, u2 := Explode(Eltseq(u));
    return boo,C![u1,u2,1];        
end function;
*/

function BasicCheck(I)
    H,d := HilbertPolynomial(EasyIdeal(I));
    return (Coefficients(H) eq [Rationals()|1,2,2]) and (d eq 0);
end function;

//////// Functions for Toric cases: use the Lie algebra method //////////

/*
   X is a degree 4 Del Pezzo surface whose "5th" affine patch
   is the big open orbit (and with associated Lie algebra L).

   Case where L generates a 4-dimensional commutative matrix
   algebra A IM which splits completely over basefield k
   <-> the split torus.

   gen in L is a generator of A and facts are the (1 dim.)
   irreducible factors of its characteristic polynomial.

   Determines whether X is parametrisable.

   If bParam is false, then only check for EXISTENCE of a
   parametrisation (trivially true in this case!).
   Otherwise return a parametrisation is parametrisable.
*/
function D1case(gen,facts,X,bParam)

    if not bParam then // in this case X always parametrisable!
	return true,_;
    end if;

    I := Ideal(AffinePatch(X,5));
    k := BaseRing(gen);
    assert (k cmpeq Rationals()) or ISA(Type(k), FldAlg);
    P := Generic(I);
    assert Rank(P) eq 4;
    assert BaseRing(P) eq k;

    // first we determine find the correct ordering for the
    // char poly factors of gen. Note that gen should embed as
    // (a,b,-a,-b) for elements a = b of k
    // s.t. all entries are distinct.
    cs := [-Coefficient(f,0):f in facts];
    // can take any eigenvalue as a & then there are just
    // 2 possibilities for b by symmetry
    a := cs[1];
    assert a ne 0;
    assert -a in cs;
    cs1 := [b : b in cs | (b ne a) and (b ne -a)];
    assert #cs1 eq 2;
    b := cs1[1];
    assert (b ne 0) and (cs1[2] eq -b);
    cs1 := [a,-a,b,-b];
    facts := [x-e : e in cs1] where x is Parent(facts[1]).1;

    // first find coord change to diagonalise gen
    M := Matrix(k,
     [Eltseq(Basis(Kernel(Evaluate(f,gen)))[1]): f in facts]);
    Minv := M^(-1);
    gen := M*gen*Minv;
    assert IsDiagonal(gen);

    /*
       now the coordinate change x_i -> sum_j M[i,j]*x_j puts
       the toric action into the required diagonal form, the
       (split) torus embedding into GL_6(k) via characters
       u,u^-1,v,v^-1 where u,v generate the
       character group of the torus.

       Now if the coordinates are x1..x4 then the equations
       of the affine part will be

         x1*x2=a  x3*x4=b for some a,b in k*
     */


    // get quadratic parts of the equations ..
    Qs := [P.1*P.2, P.3*P.4];

    // now change variables to get the forms wrt the original
    // x_i basis
    hm := hom<P->P| [&+[M[i,j]*P.j:j in [1..4]]:i in [1..4]]>;
    Q1s := Qs@hm;

    // we convert to a potentially easier GroebnerBasis to compute a,b
    J := EasyIdeal(I);
    PJ := Generic(J);
    vec := [NormalForm(PJ!f,J) : f in Q1s];
    assert &and[u in k: u in vec];
    a := k!vec[1]; b := k!vec[2];
    assert a*b ne 0;
    delete J; delete PJ;

    // now we can just write down the standard degree 3 
    //  parametrisation of X from the data
    R := PolynomialRing(k,3);
    P := CoordinateRing(Ambient(X));
    //first get the forward map equations
    mp1 := [R.1^2*R.2,a*R.3^2*R.2,R.1*R.2^2,b*R.3^2*R.1];
    mp1 := [R.1*R.2*R.3] cat Eltseq(ChangeRing(Minv,R)*Matrix(R,4,1,mp1));
    //and a maximal set of reverse ones
    vars := [P.1] cat Eltseq(ChangeRing(M,P)*Matrix(P,4,1,[P.i : i in [2..5]]));
    mp2 := [vars[2],vars[4],vars[1]];
    mp3 := [a*vars[1]*vars[5],b*vars[1]*vars[3],vars[3]*vars[5]];

    return true,iso<Proj(R)->X|mp1,[mp2,mp3] : Check := false>;

end function;

/*
   X is a degree 4 Del Pezzo surface whose "5th" affine patch
   is the big open orbit (and with associated Lie algebra L).

   Case where L generates a 2-dimensional commutative matrix
   algebra A IM to K where K is a degree 2 field over basefield k
   & the torus is K* [acting on 4-space as u -> (pu, (pu)^-1)
   with u->pu its natural 2d rep].

   gen in L is a generator of A of trace 0 to K and f is
   its minimal polynomial.

   Determines whether X is parametrisable.

   If bParam is false, then only check for EXISTENCE of a
   parametrisation.
   Otherwise returns a parametrisation if parametrisable.
*/
function D2case1(gen,facts,X,bParam)

    if not bParam then // in this case X always parametrisable!
	return true,_;
    end if;

    I := Ideal(AffinePatch(X,5));
    k := BaseRing(gen);
    assert (k cmpeq Rationals()) or ISA(Type(k), FldAlg);
    P := Generic(I);
    assert Rank(P) eq 4;
    assert BaseRing(P) eq k;

    // first we determine K from the characteristic poly
    // of gen. Note that gen should embed as
    // (u,-u) for a field generator u
    // of K/k [with non-zero trace]. So the char poly
    // should split as f(x)f(-x).
    f1,f2 := Explode(facts);
    assert f2 eq Evaluate(f1,-Parent(f1).1);

    // first change coords to block diagonalise gen
    M := Matrix(k,[Eltseq(b): b in Basis(Kernel(Evaluate(f1,gen)))]
	cat [Eltseq(b): b in Basis(Kernel(Evaluate(f2,gen)))] );
    Minv := M^(-1);
    gen := M*gen*Minv;

    boo,T := IsSimilar(Submatrix(gen,3,3,2,2),-Submatrix(gen,1,1,2,2));
    assert boo;
    M := DiagonalJoin(ScalarMatrix(2,k!1),T)*M;
    Minv := Minv*DiagonalJoin(ScalarMatrix(2,k!1),T^-1);
    gen1 := Submatrix(gen,1,1,2,2);

    //K := ext<k|f1>;
    // if k is Q then attempt to get a simpler representative
    //  for the generator of K than the root of f1 and replace
    //  gen1 accordingly
    if k cmpeq Rationals() then // should do for general k ??
	K,mp := OptimisedRepresentation(ext<k|f1>);
	gen1 := Evaluate(pol,gen1) where pol is
	  PolynomialRing(k)!Eltseq(Inverse(mp)(K.1));
	f1 := MinimalPolynomial(K.1);
        delete mp,K;
    end if;

    // find the transpose of matrix M1 taking the usual basis
    // [1,g] of K (g is K.1) to basis [1=b1,b2]
    // where the reg embedding of K by mult wrt bi basis takes
    // g to gen1.
    M1inv := Matrix(k,[[e[j,1]: j in [1..2]] where e is gen1^i :
			i in [0..1]]);
    M1inv := Transpose(M1inv);
    M1 := M1inv^(-1);
    M := DiagonalJoin(M1,M1)*M;
    Minv := Minv*DiagonalJoin(M1inv,M1inv);

    /* 
       now the coordinate change x_i -> sum_j M[i,j]*x_j puts
       the toric action into the required diagonal form, the
       torus embedding into GL_2(k) being wrt the basis
       1,g of K.

       Now if the coordinates are x1..x4 and  Q(a,b) is the
       quadratic norm form N_(K/k)(a+bg) then the equations
       of the affine part will be (over K)

       X1*X3=w  X2*X4=s(w) for G(K/k)=<s> and some w in K^*
        where X1=x1+g*x2  X2= x1+s(g)*x2 and X3,X4 are X1,X2 with 
        [x1,x2] replaced by [x3,x4].
     */


    // get Qs wrt g^i basis ..
    e1 := -Coefficient(f1,1); e2 := Coefficient(f1,0); //Tr(g) & N(g)
    Qs := [P.1*P.3-e2*P.2*P.4,P.2*P.3+P.1*P.4+e1*P.2*P.4];

    // now change variables to get the forms wrt the original
    // x_i basis
    hm := hom<P->P| [&+[M[i,j]*P.j:j in [1..4]]:i in [1..4]]>;
    Q1s := Qs@hm;

    // we convert to a potentially easier GroebnerBasis
    J := EasyIdeal(I);
    PJ := Generic(J);

    us := [NormalForm(PJ!Q,J) : Q in Q1s];
    assert &and[u in k: u in us];
    u := k!us[1]; v := k!us[2];
    assert not((u eq 0) and (v eq 0));

    delete J; delete PJ;

    // now we can just write down a degree 3 parametrisation of X
    // from the data
    R := PolynomialRing(k,3);
    P := CoordinateRing(Ambient(X));
    Q := R.1^2+e1*R.1*R.2+e2*R.2^2;
    f := e1*u+e2*v;
    L1 := u*R.1+f*R.2;
    L2 := v*R.1-u*R.2;

    mp1 := [Q*R.1,Q*R.2,L1*R.3^2,L2*R.3^2];
    mp1 := [Q*R.3] cat Eltseq(ChangeRing(Minv,R)*Matrix(R,4,1,mp1));
    vars := [P.1] cat Eltseq(ChangeRing(M,P)*Matrix(P,4,1,[P.i : i in [2..5]]));
    mp2 := [vars[2],vars[3],vars[1]];
    mp3 := [(u*vars[4]+f*vars[5])*vars[1],(v*vars[4]-u*vars[5])*vars[1],
		Evaluate(Q,[vars[4],vars[5],0])];

    return true,iso<Proj(R)->X|mp1,[mp2,mp3] >;

end function;

/*
   X is a degree 4 Del Pezzo surface whose "5th" affine patch
   is the big open orbit (and with associated Lie algebra L).

   Case where L generates a commutative matrix algebra A IM to
   K+L where K,L are degree 2 fields over basefield k
   & the torus is K*[N=1] x L*[N=1] acting in the natural way.
   K = L is a possibility.

   gen in L is a generator of A of trace 0 to k and its char poly
   is f1*f2 where facts = [f1,f2].

   Determines whether X is parametrisable.

   If bParam is false, then only check for EXISTENCE of a
   parametrisation.
   Otherwise returns a parametrisation if parametrisable.
*/
function D2case2(gen,facts,X,bParam)

    I := Ideal(AffinePatch(X,5));
    k := BaseRing(gen);
    assert (k cmpeq Rationals()) or ISA(Type(k), FldAlg);
    P := Generic(I);
    assert Rank(P) eq 4;
    assert BaseRing(P) eq k;

    // first we determine K,L from the characteristic poly
    // of gen. Note that gen should embed as 
    // (u,v) for field generators, u,v, of K/k
    // and L/k with zero trace. So the char poly
    // should split as f1(x)f2(x) where if
    // f1(x) = x^2-a, f2(x) = x^2-b,
    // K = k(sqrt(a)), L = k(sqrt(b))
    assert &and[Coefficient(f,1) eq 0 : f in facts];
    a,b := Explode([-Coefficient(f,0) : f in facts]);
    LeqK,rt_ba := IsSquare(b/a);
    f1,f2 := Explode(facts);

    // first change coords to block diagonalise gen
    M := Matrix(k,[Eltseq(b): b in Basis(Kernel(Evaluate(f1,gen)))]
	cat [Eltseq(b): b in Basis(Kernel(Evaluate(f2,gen)))] );
    Minv := M^(-1);
    gen := M*gen*Minv;

    /*boo,T := IsSimilar(Submatrix(gen,3,3,2,2),rt_ba*Submatrix(gen,1,1,2,2));
    assert boo;
    M := DiagonalJoin(DiagonalJoin(ScalarMatrix(2,k!1),T),ScalarMatrix(2,k!1))*M;
    Minv := Minv*
	DiagonalJoin(DiagonalJoin(ScalarMatrix(2,k!1),T^-1),ScalarMatrix(2,k!1));*/
    gen1 := Submatrix(gen,1,1,2,2);
    gen2 := Submatrix(gen,3,3,2,2);

    //K := ext<k|f1>;
    // if k is Q then attempt to get a simpler representatives
    //  for the generators of K,L than the roots of f1,f2 and replace
    //  gen1,gen2 accordingly
    if k cmpeq Rationals() then // should do for general k ??
	K,mp := OptimisedRepresentation(ext<k|f1>);
	gen1 := Evaluate(pol,gen1) where pol is
	  PolynomialRing(k)!Eltseq(Inverse(mp)(K.1));
	f1 := MinimalPolynomial(K.1);
        delete mp,K;
	L,mp := OptimisedRepresentation(ext<k|f2>);
	gen2 := Evaluate(pol,gen2) where pol is
	  PolynomialRing(k)!Eltseq(Inverse(mp)(L.1));
	f2 := MinimalPolynomial(L.1);
        delete mp,L;
    end if;

    // find the transpose of matrix M1 taking the usual basis
    // [1,g] of K (g is K.1) to basis [1=b1,b2] and
    // [1,h] of L (h is L.1) to basis [1=b3,b4] and
    // where the reg embedding of K,L by mult wrt bi basis takes
    // g to gen1, h to gen2.
    M1inv := Matrix(k,[[e[j,1]: j in [1..2]] where e is gen1^i :
			i in [0..1]]);
    M2inv := Matrix(k,[[e[j,1]: j in [1..2]] where e is gen2^i :
			i in [0..1]]);    
    M1inv := Transpose(M1inv); M2inv := Transpose(M2inv);
    M1 := M1inv^(-1); M2 := M2inv^(-1);
    M := DiagonalJoin(M1,M2)*M;
    Minv := Minv*DiagonalJoin(M1inv,M2inv);

    /* 
       now the coordinate change x_i -> sum_j M[i,j]*x_j puts
       the toric action into the required diagonal form, the
       torus embedding into GL_2(k) being wrt the basis
       1,g of K and 1,h of L.

       Now if the coordinates are x1..x4 then the equations
       of the affine part will be (over K.L)
         X1*X2=N(u)   X3*X4=N(v)
       where G(K/k)=<s>, u in K*, G(L/k)=<s1>, v in L*
           X1=x1+g*x2  X2= x1+s(g)*x2
       X3,X4 are X1,X2 with [x1,x2] replaced by [x3,x4] and
       s replaced by s1, g by h.
     */


    // get quadrics wrt g^i, h^i basis
    e1 := -Coefficient(f1,1); e2 := Coefficient(f1,0); //Tr(g) & N(g)
    e3 := -Coefficient(f2,1); e4 := Coefficient(f2,0); //Tr(h) & N(h)
    Qs := [P.1^2+e1*P.1*P.2+e2*P.2^2, P.3^2+e3*P.3*P.4+e4*P.4^2];

    // now change variables to get the forms wrt the original
    // x_i basis
    hm := hom<P->P| [&+[M[i,j]*P.j:j in [1..4]]:i in [1..4]]>;
    Q1s := Qs@hm;

    // we convert to a potentially easier GroebnerBasis

    J := EasyIdeal(I);
    PJ := Generic(J);

    rs := [NormalForm(PJ!Q,J) : Q in Q1s];
    assert &and[w in k: w in rs];
    r := k!(rs[1]);
    s := k!(rs[2]);

    delete J; delete PJ;

    // We now have to check solubility of N(u)=r & N(v)=s
    //  Can then determine u,v from the data - note that
    //  u,v are both arbitrary up to elts of K,L of norm 1
    if true /*bParam*/ then
	R := PolynomialRing(k,3);
	C1 := Conic(Proj(R),R.1^2+e1*R.1*R.2+e2*R.2^2-r*R.3^2);
	boo,soln := HasPoint(C1);
	if not boo then return false,_;end if;
	assert soln[3] ne 0;
	u := soln[1]/soln[3];
	v := soln[2]/soln[3];
	C2 := Conic(Proj(R),R.1^2+e3*R.1*R.2+e4*R.2^2-s*R.3^2);
	boo,soln := HasPoint(C2);
	if not boo then return false,_;end if;
	assert soln[3] ne 0;
	u1 := soln[1]/soln[3];
	v1 := soln[2]/soln[3];
    else
	return true;//return LocSolEverywhereDeg2(L,nu),_;
    end if;

    // now we can just write down a degree 4 parametrisation of X
    // from the data
    R := PolynomialRing(k,3);
    P := CoordinateRing(Ambient(X));

    Q1 := R.3^2+e1*R.1*R.3+e2*R.1^2;
    Q2 := R.3^2+e3*R.2*R.3+e4*R.2^2;
    f1 := u*R.3^2-2*v*e2*R.3*R.1-e2*(e1*v+u)*R.1^2;
    f2 := v*R.3^2+2*(e1*v+u)*R.3*R.1+(v*(e1^2-e2)+u*e1)*R.1^2;
    f3 := u1*R.3^2-2*v1*e4*R.3*R.2-e4*(e3*v1+u1)*R.2^2;
    f4 := v1*R.3^2+2*(e3*v1+u1)*R.3*R.2+(v1*(e3^2-e4)+u1*e3)*R.2^2;

    mp1 := [f1*Q2,f2*Q2,f3*Q1,f4*Q1];
    mpf := [Q1*Q2] cat Eltseq(ChangeRing(Minv,R)*Matrix(R,4,1,mp1));

    vars := [P.1] cat Eltseq(ChangeRing(M,P)*Matrix(P,4,1,[P.i : i in [2..5]]));
    mat1 := Adjoint(Matrix(k,3,3,[1,e1,e2,u,-2*v*e2,-e2*(e1*v+u),v,2*(u+e1*v),
		e1^2*v-v*e2+u*e1]));
    mat2 := Adjoint(Matrix(k,3,3,[1,e3,e4,u1,-2*v1*e4,-e4*(e3*v1+u1),v1,2*(u1+e3*v1),
		e3^2*v1-v1*e4+u1*e3]));
    L1,L2,L3 := Explode(Eltseq(ChangeRing(mat1,P)*Matrix(P,3,1,[vars[i]:i in [1..3]])));
    E1,E2,E3 := Explode(Eltseq(ChangeRing(mat2,P)*Matrix(P,3,1,[vars[i]:i in [1,4,5]])));
    // inverse maps
    mp2 := [L2*E1,L1*E2,L1*E1];
    mp3 := [L2*E2,L1*E3,L1*E2];
    mp4 := [L3*E1,L2*E2,L2*E1];

    //return true,iso<Proj(R)->X|mpf,[mp2,mp3,mp4,mp5] : Check := false>;
    return true,iso<Proj(R)->X|mpf,[mp2,mp3,mp4]>;

end function;


/*
   X is a degree 4 Del Pezzo surface whose "5th" affine patch
   is the big open orbit (and with associated Lie algebra L).

   Case where L generates a 4-dimensional commutative matrix
   algebra A IM to L where L is a degree 4 extension of 
   basefield k with unique quadratic subfield K (<=> the
   Galois closure of L is a C4 or D8 extension of k).
   The torus is L*_(Norm(L/K)=1) and the action on 4-space is given
   by L* with its normal action.

   gen in L is a generator of A of trace 0 to K and f is
   its minimal polynomial.

   Determines whether X is parametrisable.

   If bParam is false, then only check for EXISTENCE of a
   parametrisation.
   Otherwise returns a parametrisation if parametrisable.
*/
function D4case(gen,f,X,bParam)

    I := Ideal(AffinePatch(X,5));
    k := BaseRing(gen);
    assert (k cmpeq Rationals()) or ISA(Type(k), FldAlg);
    P := Generic(I);
    assert Rank(P) eq 4;
    assert BaseRing(P) eq k;

    // first we determine L,K from the characteristic poly
    // of gen. Note that gen should embed as a field generator
    // u of L/k with zero trace to K
    // So the char poly should be of the form
    // f(x) = x^4-2*a*x^2+(a^2-b^2*d)
    // where K=k(sqrt(d)), L=k(sqrt(a+b*sqrt(d))) and 
    // gen <-> sqrt(a+b*sqrt(d)) - can replace d with
    //  b^2*d and let b=1.
    assert Degree(f) eq 4;
    assert (Coefficient(f,1) eq 0) and (Coefficient(f,3) eq 0);
    a := -Coefficient(f,2)/2;
    d :=  (a^2)-Coefficient(f,0);

    // first change coords to "K-diagonalise" gen
    gen_st := Matrix(k,4,4,[0,0,a,d,0,0,1,a,1,0,0,0,0,1,0,0]);
    boo,T := IsSimilar(gen,gen_st);
    assert boo;
    M := T;
    Minv := T^-1;

    K := ext<k|PolynomialRing(k)![-d,0,1]>;
    // if k is Q then attempt to get simpler representatives
    //  for the generator of K and replace gen accordingly.
    if k cmpeq Rationals() then // should do for general k ??
	K,mp := OptimisedRepresentation(K);
	u,v := Explode(Eltseq(Inverse(mp)(K.1)));
	assert v ne 0;
	beta := a+((K.1-u)/v);
	// L now repd as K(sqrt(beta))
	M := DiagonalJoin(mat,mat)* M where mat is 
	    Matrix(k,2,2,[1,-u/v,0,1/v]);
	Minv := Minv * DiagonalJoin(mat,mat) where mat is
	    Matrix(k,2,2,[1,u,0,v]);
    else
	beta := a+K.1;
    end if;
//printf "beta: %o  es: %o\n",beta,Eltseq(beta);

    /* 
       now the coordinate change x_i -> sum_j M[i,j]*x_j puts
       the toric action into the required diagonal form, the
       torus embedding into GL_4(k) being wrt the basis
       1,g,b,b*g of L (b = sqrt(beta)) and 1,g of K.

       Now if the coordinates are x1..x4 then the equations
       of the affine part will be (over K)
        X1^2-beta*X2^2=u  X3^2-s(beta)*X4^2=s(u)
       where G(K/k) = <s>, u in K*,
           X1=x1+g*x2  X2= x3+g*x4 X3=x1+s(g)*x2
	       X4=x3+s(g)*x4
     */


    // get cubics & quadratics wrt the chosen basis ..
    t1 := Trace(K.1); t2 := Trace(K.1^2);
    u,v := Explode(Eltseq(beta));
    e0 := Trace(beta); e1 := Trace(beta*K.1); e2 := Trace(beta*K.1^2);
    Qs := [(2*P.1^2+2*t1*P.1*P.2+t2*P.2^2)-
		(e0*P.3^2+2*e1*P.3*P.4+e2*P.4^2),
	   (2*P.1*P.2+t1*P.2^2)-
		(v*P.3^2+(e0+v*t1)*P.3*P.4+(v/2)*(t2+t1^2)*P.4^2)];

    // now change variables to get the forms wrt the original
    // x_i basis
    hm := hom<P->P| [&+[M[i,j]*P.j:j in [1..4]]:i in [1..4]]>;
    Q1s := Qs@hm;
//printf "Qs: %o\nQ1s: %o\n",Qs,Q1s;
    // now if a = Q1s[1] mod I, b = Q1s[2] mod I and
    // then Tr_(K/k)(u)=a and (s(u)-u)/(s(g)-g) = b
    //
    // we convert to a potentially easier GroebnerBasis
    J := EasyIdeal(I);
    PJ := Generic(J);

    us := [NormalForm(PJ!Q,J) : Q in Q1s];
    assert &and[u in k: u in us];
    ChangeUniverse(~us,k);
//printf "us: %o\n",us;
    u := ((us[1]-t1*us[2])/2)+(us[2]*K.1);

    delete J; delete PJ;

    // We now have to check solubility of N_(L/K)(v)=u
    if true /*bParam*/ then
	R := PolynomialRing(K,3);
	C := Conic(Proj(R),R.1^2-beta*R.2^2-u*R.3^2);
//printf "K: %o\nbeta: %o\nu: %o\n",K,beta,u;
//assert false;
	boo,soln := HasPoint(C);//MyHasPoint(C);
	if not boo then return false,_;end if;
	assert soln[3] ne 0;
	u := soln[1]/soln[3];
	v := soln[2]/soln[3];
    else
	return true;//return LocSolEverywhereDeg2(L,nu),_;
    end if;

    // now we can just write down a degree 4 parametrisation of X
    // from the data
    R := PolynomialRing(k,3);
    P := CoordinateRing(Ambient(X));

    //easiest to work over K and transform back to k at the end
    R1 := ChangeRing(R,K);
    hms := [hom<R1->R|
 	map<K->R|x :-> R!(Eltseq(x)[i])>,[R.1,R.2,R.3]> :
		i in [1..2]];
    bs := e0-beta; gs := t1-K.1;//conjugates of beta and K.1
    L := R1.1+K.1*R1.2;
    Ld := R1.1+gs*R1.2;
    
    //NL := R1.1^2+t1*R1.1*R1.2+Norm(K.1)*R1.2^2;
    //TL := 2*R1.1+t1*R1.2;
    Q1 := L^2-beta*R1.3^2;
    Q2 := Ld^2-bs*R1.3^2;
    F := Q2*(u*(L^2+beta*R1.3^2)-2*v*beta*L*R1.3);
    G := Q2*(v*(L^2+beta*R1.3^2)-2*u*L*R1.3);

    mp1 := [hms[1](F),hms[2](F),hms[1](G),hms[2](G)];
    mpf := [hms[1](Q1*Q2)] cat Eltseq(ChangeRing(Minv,R)*Matrix(R,4,1,mp1));

    P1 := ChangeRing(P,K);
    hm1 := hom<P1->P|
	map<K->P|x :-> P!(Eltseq(x)[1])>,[P.i : i in [1..5]]>;
    hm2 := hom<P1->P|
	map<K->P|x :-> P!(Eltseq(x)[2])>,[P.i : i in [1..5]]>;    
    vars := [P1.1] cat Eltseq(ChangeRing(M,P1)*Matrix(P1,4,1,[P1.i : i in [2..5]]));
    su := Trace(u)-u; sv := Trace(v)-v;
    // first inverse map
    L1 := u*vars[1]-vars[2]-K.1*vars[3];
    L1d := su*vars[1]-vars[2]-gs*vars[3];
    L2 := v*vars[1]+vars[4]+K.1*vars[5];
    x := beta*L2*L1d;
    mp2 := [hm1(x),hm2(x),hm1(L1*L1d)];
    // second inverse map
    L1 := v*vars[1]-vars[4]-K.1*vars[5];
    L1d := sv*vars[1]-vars[4]-gs*vars[5];
    L2 := u*vars[1]+vars[2]+K.1*vars[3];
    x := L2*L1d;   
    mp3 := [hm1(x),hm2(x),hm1(L1*L1d)];

    //return true,map<Proj(R)->X|mpf,[mp2,mp3] : Check := false>;
    return true,map<Proj(R)->X|mpf,[mp2,mp3]>;
    //return true,map<Proj(R)->X|mpf>;

end function;

intrinsic ParamDeg4DPSingLie(X::Sch :
 	ExistenceOnly := false) -> BoolElt, MapIsoSch
{Determines whether a degree 4 DelPezzo surface is parametrisable.
 If so, it returns a parametrisation.}

    P4 := Ambient(X);
    k := BaseRing(X);
    require (k cmpeq Rationals()) or ISA(Type(k), FldAlg):
	"Surface should be defined over Q or a number field.";
    require IsOrdinaryProjective(X) and (Dimension(P4) eq 4):
	"Scheme is not a degree 4 Del Pezzo.";
    Qs := DefiningEquations(X);
    if (#Qs ne 2) or &or[TotalDegree(f) ne 2 : f in Qs] then
	Saturate(~X);
    end if;
    require BasicCheck(Ideal(X)):
	"Scheme is not a degree 4 Del Pezzo.";

    L := FindLieAlgebra(Ideal(X));
    assert Dimension(L) eq 2;
    L := Basis(L);

    // first find "distinguished" hyperplane whose coefficients
    // are given by non-zero vector in the (1-D) intersection of
    // the kernels of matrices in L
    vecs := &meet[Kernel(Transpose(b)) : b in L];
    assert Dimension(vecs) eq 1;
    //change coords so that hyperplane is x0=0 and restrict to
    //affine patch x0 != 0
    W := sub<V|[e*Transpose(L[1]) : e in Basis(V)] cat
	  [e*Transpose(L[2]) : e in Basis(V)]> where V is Generic(vecs);
    M := Transpose(Matrix(Basis(vecs) cat Basis(W)));
    Minv := M^(-1);
    L := [Minv*l*M : l in L];
    L := [Submatrix(l,2,2,4,4) : l in L];
    mp1 := iso<P4->P4|[&+[Minv[i,j]*P4.j:j in [1..5]]: i in [1..5]],
	[&+[M[i,j]*P4.j:j in [1..5]]: i in [1..5]] : Check := false>;
    X1 := mp1(X);
    mp1 := iso<X1->X|InverseDefiningPolynomials(mp1),
		DefiningPolynomials(mp1) : Check := false>;

    // We now want to find the associative subalgebra of M_4(k)
    // generated by L. The decomposition of this (commutative, semisimple)
    // algebra into simple factors determines the torus type of T
    // where T is the connected component of the automorphism gp of the
    // surface. In fact, we know for the possible types, the algebra
    // generated by any single, non-zero elt of L is the full algebra
    // except in some cases, when either l1,l2 or l1+l2 will
    // generate the full algebra (L=[l1,l2]) unless T is the product
    // of 2 1D tori. In this case either l1+2l2 or l1-2l2 works.
    // Thus we can work directly with the Jordan decomposition of a
    // single elt of L
    for rs in [[1,0],[0,1],[1,1],[1,2],[1,-2]] do
	Lgen := rs[1]*L[1]+rs[2]*L[2];
	_,_,facts := JordanForm(Lgen);
	if &or[facts[i][1] eq facts[j][1]: j in [i+1..#facts], 
			i in [1..#facts]] then
             continue;
	end if;
	break;
    end for;
    assert &and[facts[i][1] ne facts[j][1]: j in [i+1..#facts],i in [1..#facts]];
    assert &and[f[2] eq 1: f in facts]; // Lgen is semi-simple
    facts := [f[1] : f in facts];
    // probably good to check that L[1] & L[2] are both in the algebra
    // generated by this semi-simple elt. !

    //now deal with the individual cases
    degs := [Degree(f): f in facts];
    case degs:
	when [1,1,1,1]: // split torus case
	    boo,prm := D1case(Lgen,facts,X1,not ExistenceOnly);	
	when [2,2]: //(K*)[norm=1] x (K*)[norm=1] [K:k]=2
		    // OR (K*)[norm=1] x (L*)[norm=1] [L:k]=[K:k]=2
		    // OR K* [K:k]=2
	    if Coefficient(facts[1],1) ne 0 then //K* case
	      boo,prm := D2case1(Lgen,facts,X1,not ExistenceOnly);
	    else // other two cases
	      boo,prm := D2case2(Lgen,facts,X1,not ExistenceOnly);
	    end if;
	when [4]:   //(L*)[normL/K=1] [L:K]=[K:k]=2
	    boo,prm := D4case(Lgen,facts[1],X1,not ExistenceOnly);
    else //default
	error "Unknown problem occurred with the Lie algebra of the surface.";
    end case;
    if ExistenceOnly or (not boo) then 
	return boo,_;
    else
	return true,Expand(prm*mp1);
    end if;

end intrinsic;

/////// End of code for Toric cases ////////////////////////////////////

/// MAIN INTRINSIC /////////////////////////////////////////////////////

intrinsic ParametrizeSingularDegree4DelPezzo(X::Sch,P2::Prj)
-> BoolElt, MapSch
{ Determines whether a singular, anticanonically-embedded degree 4 Del Pezzo surface X
  is parametrizable over the base field. If so,
  also returns a parametrization from P2 (2D projective space) to X. }

    Xsng := ReducedSubscheme(SingularSubscheme(X));
    require Dimension(Xsng) eq 0 : "First argument should be a SINGULAR degree 4 Del Pezzo";

    d := Degree(Xsng);
    if d eq 4 then //toric case
	boo,prm := ParamDeg4DPSingLie(X);
	if boo then 
	    prm := Expand(im*prm) where im := iso<P2->D|[P2.1,P2.2,P2.3],[D.1,D.2,D.3]>
		where D is Domain(prm);
	    return true,prm;
	else
	    return false,_;
	end if;
    end if;
    
    ksngs := Support(Xsng);
    // any k-rational singular points?
    if #ksngs gt 0 then //project from singular point to quadric surface Y in P3
	sng_pt := Representative(ksngs);
	prj := PointProjection(X,sng_pt,2);
	Y := Codomain(prj);
	boo,prm2 := ParametrizeQuadric(Y,P2);
	if boo then 
	    prm := Expand(prm2*Inverse(prj));
	    return true,prm;
	else
	    return false,_;
	end if;
    end if;

    // remaining cases should be 2 conjugate A1 singularities P1 & P2.
    //  two cases: the k-rational line joining P1 & P2 is a -1 line in
    //  X or it intersects X only in P1 and P2.
    assert Degree(Xsng) eq 2;
    // get eqns for the line
    P4 := Ambient(X);
    L := LinearSystem(P4,1);
    Leqns := Sections(LinearSystem(L,Xsng));
    L := Scheme(P4,Leqns);
    if L subset X then // case 1
	// projection from line is birational to P2!
	prm := Inverse(LinearSpaceProjection(X,L,3));
	prm := Expand(im*prm) where im := iso<P2->D|[P2.1,P2.2,P2.3],[D.1,D.2,D.3]>
		where D is Domain(prm);
	return true,prm;	
    else // case 2
	// projection from line to a conic makes X a conic fibration
	prj := map<X->P2|Leqns>;
	return ParametrizePencil(prj,P2);
    end if;

end intrinsic;
