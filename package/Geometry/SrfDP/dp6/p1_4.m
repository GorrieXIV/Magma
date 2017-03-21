freeze;

/*
    Functions for degree 6 Del Pezzo parametrisation that handle
     the cases when the splitting field of the torus is of
              degree 1 or 4 over the base field.
			mch - 05/06
*/

import "loc_sol.m" : LocSolEverywhereDeg2;

/*
   X is a degree 6 Del Pezzo surface whose "7th" affine patch
   is the big open orbit (and with associated Lie algebra L).

   Case where L generates a 6-dimensional commutative matrix
   algebra A IM which splits completely over basefield k
   <-> the split torus.

   gen in L is a generator of A and facts are the (1 dim.)
   irreducible factors of its characteristic polynomial.

   Determines whether X is parametrisable.

   If bParam is false, then only check for EXISTENCE of a
   parametrisation (trivially true in this case!).
   Otherwise return a parametrisation is parametrisable.
*/
function D1Case(gen,facts,X,bParam)

    if not bParam then // in this case X always parametrisable!
	return true,_;
    end if;

    I := Ideal(AffinePatch(X,7));
    k := BaseRing(gen);
    assert (k cmpeq Rationals()) or ISA(Type(k), FldAlg);
    P := Generic(I);
    assert Rank(P) eq 6;
    assert BaseRing(P) eq k;

    // first we determine find the correct ordering for the
    // char poly factors of gen. Note that gen should embed as
    // (a,b,a+b,-a,-b,-a-b) for elements a = b of k
    // s.t. all entries are distinct.
    assert Parent(f)!(&*facts) eq f where
			f is CharacteristicPolynomial(gen);
    assert (#facts eq 6) and
		&and[Degree(f) eq 1 :f in facts];
    cs := [-Coefficient(f,0):f in facts];
    // can take any eigenvalue as a & then there are just
    // 2 possibilities for b by symmetry
    a := cs[1];
    assert a ne 0;
    cs1 := [b : b in cs | a+b in cs];
    assert #cs1 eq 2;
    b := cs1[1];
    assert (a+2*b ne 0) and (b notin [0,a,-a,-2*a]);
    cs1 := [a,b,a+b,-a,-b,-a-b];
    assert Seqset(cs1) eq Seqset(cs);
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
       u,v,u*v,u^-1,v^-1,(u*v)^-1, where u,v generate the
       character group of the torus.

       Now if the coordinates are x1..x6 then the equations
       of the affine part will be

         x1*x4=a  x2*x5=b  x3*x6=c x1*x2*x6=d x3*x4*x5=e
              for some a,b,c,d,e in k*, abc=de
     */


    // get cubics & quadratics of the equations ..
    Cs := [P.1*P.2*P.6, P.3*P.4*P.5];
    Qs := [P.1*P.4, P.2*P.5, P.3*P.6];

    // now change variables to get the forms wrt the original
    // x_i basis
    hm := hom<P->P| [&+[M[i,j]*P.j:j in [1..6]]:i in [1..6]]>;
    Q1s := Qs@hm;
    C1s := Cs@hm;

    // now if d = C1s[1] mod I, e = C1s[2] mod I and
    // if [a,b,c] = [Q1s mod I] then these will be
    // the defining constants for the affine equations.
    //
    // we convert to a potentially easier GroebnerBasis

    J := EasyIdeal(I);
    PJ := Generic(J);

    us := [NormalForm(PJ!C,J) : C in C1s];
    assert &and[u in k: u in us];
    d := k!us[1]; e := k!us[2];
    assert d*e ne 0;

    ws := [NormalForm(PJ!Q,J) : Q in Q1s];
    assert &and[w in k: w in ws];
    a,b,c := Explode(ChangeUniverse(ws,k));

    assert a*b*c eq d*e;

    delete J; delete PJ;

    // now we can just write down the standard degree 3 
    //  parametrisation of X from the data
    R := PolynomialRing(k,3);
    P := CoordinateRing(Ambient(X));
    //first get the forward map equations
    mp1 := [R.2^2*R.3,R.1^2*R.2,(c/d)*R.1*R.2^2,a*R.1^2*R.3,
    			b*R.2*R.3^2,d*R.1*R.3^2];
    mp1 := [R.1*R.2*R.3] cat Eltseq(ChangeRing(Minv,R)*Matrix(R,6,1,mp1));
    //and a maximal set of reverse ones
    vars := [P.1] cat Eltseq(ChangeRing(M,P)*Matrix(P,6,1,[P.i : i in [2..7]]));
    mp2 := [b*vars[1],b*vars[2],vars[6]];
    mp3 := [d*vars[5],a*d*vars[1],a*vars[7]];
    mp4 := [c*vars[3],d*vars[4],c*vars[1]];

    return true,iso<Proj(R)->X|mp1,[mp2,mp3,mp4] : Check := false>;

end function;

/*
   X is a degree 6 Del Pezzo surface whose "7th" affine patch
   is the big open orbit (and with associated Lie algebra L).

   Case where L generates a 6-dimensional commutative matrix
   algebra A IM to L plus K1 where L is a C2xC2 extension of 
   basefield k, and K1 is a quadratic subfield. The torus
   is L*_(Norm(L/K)=1) where K is another quadratic subfield
   and the action on 6-space is given by L* with its normal
   action on 4-space + Norm(L*->K1*) and action on 2-space.

   gen in L is a generator of A of trace 0 and facts are the
   irreducible factors of its characteristic polynomial.

   Determines whether X is parametrisable.

   If bParam is false, then only check for EXISTENCE of a
   parametrisation.
   Otherwise returns a parametrisation if parametrisable.
*/
function D4Case(gen,facts,X,bParam)

    I := Ideal(AffinePatch(X,7));
    k := BaseRing(gen);
    assert (k cmpeq Rationals()) or ISA(Type(k), FldAlg);
    P := Generic(I);
    assert Rank(P) eq 6;
    assert BaseRing(P) eq k;

    // first we determine L,K,K1 from the characteristic poly
    // of gen. Note that gen should embed as 
    // (u,trace(L/K1)(u)) for field generator u of L/k
    // with zero trace to K. So the char poly should split
    // as f1(x)*f2(x) with f1(x) = x^4-2*(a^2+b^2)*d1*x^2
    // +(d1*(a^2-b^2*d))^2 and f2(x) = x^2-4*a^2*d1
    // where K=k(sqrt(d)), K1=k(sqrt(d1)) and 
    // gen <-> (a+b*sqrt(d))*sqrt(d1)
    assert Parent(f)!(&*facts) eq f where
			f is CharacteristicPolynomial(gen);
    assert (#facts eq 2) and (Sort([Degree(f) :f in facts]) eq [2,4]);
    assert &and[Coefficient(f,1) eq 0 : f in facts];
    f1 := [f : f in facts|Degree(f) eq 4][1];
    f2 := [f : f in facts|Degree(f) eq 2][1];
    assert Coefficient(f1,3) eq 0;
     // find d1 and d - note can assume a,b=1 by changind d & d1
    d1 := -Coefficient(f2,0)/4;
    assert d1 ne 0;
    u :=  -Coefficient(f1,2)/(2*d1); // 1+d
    boo,v := IsSquare(Coefficient(f1,0));
    assert boo;
    v /:= d1;  // +- (1-d)
    d := (u+v)/2;
    if d eq 1 then
	d := (u-v)/2;
    else
	assert (u-v)/2 eq 1;
    end if;


    // first change coords to block diagonalise gen
    M := Matrix(k,[Eltseq(b): b in Basis(Kernel(Evaluate(f1,gen)))]
	cat [Eltseq(b): b in Basis(Kernel(Evaluate(f2,gen)))]);
    Minv := M^(-1);
    gen := M*gen*Minv;
    assert &and[(gen[i,j] eq 0) and (gen[j,i] eq 0) : i in [1,2,3,4], j in [5,6]];

    gen2 := Submatrix(gen,5,5,2,2);
    gen1 := (1/2)*VerticalJoin(HorizontalJoin(gen2,d*gen2),HorizontalJoin(gen2,gen2));
    boo,T := IsSimilar(Submatrix(gen,1,1,4,4),gen1);
    assert boo;
    M := DiagonalJoin(T,ScalarMatrix(2,k!1))*M;
    Minv := Minv*DiagonalJoin(T^-1,ScalarMatrix(2,k!1));

    K := ext<k|PolynomialRing(k)![-d,0,1]>;
    K1 := ext<k|f2>;
    // if k is Q then attempt to get simpler representatives
    //  for the generators of K,K1 and replace gen1, gen2 accordingly.
    if k cmpeq Rationals() then // should do for general k ??
	K1,mp := OptimisedRepresentation(K1);
	pol := PolynomialRing(k)!Eltseq(Inverse(mp)(K1.1));
	gen2 := Evaluate(pol,gen2);
	f2 := MinimalPolynomial(K1.1);
        K,mp := OptimisedRepresentation(K);
	// actually just need to record the transformation matrix here
	A,B := Explode(Eltseq(mp(Domain(mp).1)));
	idmat := IdentityMatrix(k,2);
	M := DiagonalJoin(VerticalJoin(HorizontalJoin(idmat,A*idmat),
	  HorizontalJoin(ZeroMatrix(k,2,2),B*idmat)),idmat) * M;
	Minv := Minv * DiagonalJoin(VerticalJoin(
	  HorizontalJoin(idmat,-(A/B)*idmat),
	  HorizontalJoin(ZeroMatrix(k,2,2),(1/B)*idmat)),idmat);

	L := ext<K|PolynomialRing(K)!f2>;
    end if;

    // find the transpose of matrix M1 taking the usual basis
    // [1,g1] of K1 (g1 is K1.1) to basis [1=b1,b2]
    // where the reg embedding of K by mult wrt bi basis takes
    // g1 to gen2.
    M1inv := Matrix(k,[[e[j,1]: j in [1..2]] where e is gen2^i :
			i in [0..1]]);
    M1inv := Transpose(M1inv);
    M1 := M1inv^(-1);
    M := DiagonalJoin(DiagonalJoin(M1,M1),M1)*M;
    Minv := Minv*DiagonalJoin(DiagonalJoin(M1inv,M1inv),M1inv);

    /* 
       now the coordinate change x_i -> sum_j M[i,j]*x_j puts
       the toric action into the required diagonal form, the
       torus embedding into GL_3(k) being wrt the basis
       1,g1,g,g*g1 of L and 1,g1 of K1 [g = K.1].

       Now if the coordinates are x1..x6 then the equations
       of the affine part will be (over K)
        X1*X2=N_(L/K)(u)  X3*X4=s1(N_(L/K)(u)) X5*X6=N_(K1/k)(v)
         X1*X2*X6=N_(L/K1)(u)*s(v)  X3*X4*X5=s(N_(L/K1)(u))*v

       where G(L/K) = G(K1/k) = <s>, G(L/K1) = G(K/k) = <s1>,
       			u in L*, v in K1*,
           X1=L1+g*L2  X2= L3+g*L4 X3=L1+s1(g)*L2
	   X4=L3+s1(g)*L4 X5=x5+g1*x6 X6=x5+s(g1)*x6
       with     L1=x1+g1*x2 L2=x3+g1*x4 L3=x1+s(g1)*x2
       			L4=x3+s(g1)*x4.
     */


    // get cubics & quadratics wrt the chosen basis ..
    e1 := Trace(K.1); e2 := Norm(K.1);
    f1 := Trace(K1.1); f2 := Norm(K1.1);
    Cs := [

    P.1*P.3*P.6*e1*f1+(P.1*P.4*P.6+P.2*P.3*P.6-P.2*P.4*P.5)*e1*f2+
    P.1*P.3*P.5*e1+P.3^2*P.6*e2*f1+(2*P.3*P.4*P.6-P.4^2*P.5)*e2*f2+
    P.3^2*P.5*e2+P.1^2*P.6*f1 +(2*P.1*P.2*P.6-P.2^2*P.5)*f2+P.1^2*P.5,

    P.2*P.4*P.5*e1*f1+P.2*P.4*P.6*e1*f2+(-P.1*P.3*P.6+P.1*P.4*P.5+
    P.2*P.3*P.5)*e1+P.4^2*P.5*e2*f1+P.4^2*P.6*e2*f2 +(-P.3^2*P.6+
    2*P.3*P.4*P.5)*e2+P.2^2*P.5*f1+P.2^2*P.6*f2-P.1^2*P.6+
    2*P.1*P.2*P.5

    ];
    Qs := [(P.1^2+f1*P.1*P.2+f2*P.2^2)-
		e2*(P.3^2+f1*P.3*P.4+f2*P.4^2),
	   e1*(P.3^2+f1*P.3*P.4+f2*P.4^2)+
		(2*P.1*P.3+f1*(P.2*P.3+P.1*P.4)+2*f2*P.2*P.4),
	   P.5^2+f1*P.5*P.6+f2*P.6^2];

    // now change variables to get the forms wrt the original
    // x_i basis
    hm := hom<P->P| [&+[M[i,j]*P.j:j in [1..6]]:i in [1..6]]>;
    Q1s := Qs@hm;
    C1s := Cs@hm;

    // now if a = C1s[1] mod I, b = C1s[2] mod I and
    // if [r,s,t] = [Q1s mod I]
    // then N_(L/K)(u)=r+g*s, N_(K1/k)(v)=t and N_(L/K1)(u)*s(v)=a+g1*b
    //  we should get N_(K/k)(r+g*s)*t = N_(K1/k)(a+g1*b)
    //
    // we convert to a potentially easier GroebnerBasis

    J := EasyIdeal(I);
    PJ := Generic(J);

    ws := [NormalForm(PJ!C,J) : C in C1s];
    assert &and[w in k: w in ws];
    ChangeUniverse(~ws,k);
    n1usv := K1!ws;

    us := [NormalForm(PJ!Q,J) : Q in Q1s];
    assert &and[u in k: u in us];
    ChangeUniverse(~us,k);
    nu := K![us[1],us[2]];
    nv := us[3];

    delete J; delete PJ;

    assert Norm(n1usv) eq Norm(nu)*nv;

    // We now have to check solubility of N_(L/K)(u)=nu
    //  Can then determine u,v from the data
    if bParam then
	boo,soln := NormEquation(L,nu);
	if not boo then return false,_;end if;
	u := soln[1];
	v := n1usv/(Norm(a)-f2*Norm(b)+(f1*Norm(b)+Trace(a*(Trace(b)-b)))*K1.1)
	   where a,b := Explode(Eltseq(u));
	v := Trace(v)-v;
    else
	return LocSolEverywhereDeg2(L,nu),_;
    end if;

    // now we can just write down a degree 4 parametrisation of X
    // from the data
    R := PolynomialRing(k,3);
    P := CoordinateRing(Ambient(X));

     //easiest to work over L in this case
    v := L![K!seq[1],K!seq[2]] where seq is Eltseq(v);
    R1 := ChangeRing(R,L);
    hms := [hom<R1->R|
 	map<L->R|x :-> R!(Eltseq(Eltseq(x)[i])[j])>,[R.1,R.2,R.3]> :
		i in [1..2], j in [1..2] ];
    Q1 := (L.1*R1.1+R1.2+(e1-K.1)*R1.3)*((f1-L.1)*R1.1+R1.2+(e1-K.1)*R1.3);
    Q2 := ((f1-L.1)*R1.1+R1.2+(e1-K.1)*R1.3)*((f1-L.1)*R1.1+R1.2+K.1*R1.3);
    Q3 := (L.1*R1.1+R1.2+K.1*R1.3)*(L.1*R1.1+R1.2+(e1-K.1)*R1.3);
    F := u*Q1*((f1-L.1)*R1.1+R1.2+K.1*R1.3)^2;
    G := v*Q2^2;

    mp1 := [hms[1](F),hms[2](F),hms[3](F),hms[4](F),hms[1](G),hms[2](G)];
    mpf := [hms[1](Q2*Q3)] cat Eltseq(ChangeRing(Minv,R)*Matrix(R,6,1,mp1));

    P1 := ChangeRing(P,L);
    hm1 := hom<P1->P|
	map<L->P|x :-> P!(Eltseq(Eltseq(x)[1])[1])>,[P.i : i in [1..7]]>;
    hm2 := hom<P1->P|
	map<L->P|x :-> P!(Eltseq(Eltseq(x)[2])[1])>,[P.i : i in [1..7]]>;
    
    vars := [P1.1] cat Eltseq(ChangeRing(M,P1)*Matrix(P1,6,1,[P1.i : i in [2..7]]));
    //su := Trace(u)-u;
    tu := Trace(c[1])-c[1]+(Trace(c[2])-c[2])*L.1 where c is Eltseq(u);
    //stu := Trace(c[1])-c[1]+(Trace(c[2])-c[2])*L.1 where c is Eltseq(su);
    //sv := Trace(v)-v;
    A := (vars[2]+L.1*vars[3]+K.1*vars[4]+L.1*K.1*vars[5])/u;
    //As := (vars[2]+(f1-L.1)*vars[3]+K.1*vars[4]+(f1-L.1)*K.1*vars[5])/su;
    At := (vars[2]+L.1*vars[3]+(e1-K.1)*vars[4]+L.1*(e1-K.1)*vars[5])/tu;
    //Ast := (vars[2]+(f1-L.1)*vars[3]+(e1-K.1)*vars[4]+
    			//(f1-L.1)*(e1-K.1)*vars[5])/stu;
    B := (vars[6]+L.1*vars[7])/v;
    //Bs := (vars[6]+(f1-L.1)*vars[7])/sv;
    x := (B+vars[1]-A-At)/(f1-2*L.1);
    z := (At-A)/(2*K.1-e1);
    y := B-A-x*(f1-L.1)-z*K.1;
    // first inverse map
    mp2 := [hm1(x),hm1(y),hm1(z)];
    // second inverse map
    mp3 := [hm2(x),hm2(y),hm2(z)];

    return true,iso<Proj(R)->X|mpf,[mp2,mp3] : Check := false>;

end function;
