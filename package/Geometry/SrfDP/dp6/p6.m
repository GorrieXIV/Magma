freeze;

/*
    Functions for degree 6 Del Pezzo parametrisation that handle
     the cases when the torus comes from a degree 6 extension
                  of the base field.
			mch - 05/06
*/

import "p3.m": FindInverses;
import "loc_sol.m" : SimLocSolEverywhere;
import "geom_proj.m": GeometricProjectionMethodDeg6;

function  MatrixRepresentation(K)
/*
   K is a FldAlg, a simple extension of field k of degree d.
   returns the natural (left) k-algebra rep K -> M_d(k) given by the
   action of K on itself wrt the k-basis {1,x,x^2,..x^(d-1)}
   where x is K.1
*/
    x := K.1;
    k := BaseField(K);
    coeffs := Prune(Coefficients(MinimalPolynomial(x)));
    coeffs := [-c : c in coeffs];
    d := #coeffs;
    if d eq 1 then
	return hom<K->MatrixAlgebra(k,1)| Matrix(1,1,coeffs)>;
    end if;
    M := HorizontalJoin(ZeroMatrix(k,d-1,1),IdentityMatrix(k,d-1));
    M := VerticalJoin(M,Matrix(1,d,coeffs));
    return hom<K->MatrixAlgebra(k,d)| Transpose(M)>;
end function;

function D6ParamD6(K,K3,Dsqrt,rtd,pt,X,M)

    y := K3.1;
    k := BaseField(K);
    P := PolynomialRing(k,3);
    f := MinimalPolynomial(y);
    d := k!(rtd^2);

    rep := MatrixRepresentation(K3);

    My := rep(y);
    M1 := (-1/2)*rep(y+Coefficient(f,2));
    M2 := (-1/2)*rep(Dsqrt/Evaluate(Derivative(f),y));

    A1 := P.1+P.2*ChangeRing(My,P)+P.3*ChangeRing(My^2,P);
    U := P.1+P.2*ChangeRing(M1,P)+P.3*ChangeRing(d*M2^2+M1^2,P);
    V := P.2*ChangeRing(M2,P)+2*P.3*ChangeRing(M1*M2,P);

    nrm := P!Determinant(A1);
    A := A1*(U^2+(P!d)*(V^2));
    B := 2*A1*U*V;

    M1 := VerticalJoin(HorizontalJoin(A,d*B),HorizontalJoin(B,A));
    
    tr := Transpose(Matrix(k,[Eltseq(a*b): 
			a in [K|1,y,y^2], b in [K|1,rtd]]));
    M1 := ChangeRing(tr,P)*M1*ChangeRing(tr^-1,P);
    eqs := [nrm] cat Eltseq(ChangeRing(M,P)*M1*Matrix(P,6,1,pt));
    
    return FindInverses(eqs,Proj(P),X);

end function;


function D6ParamProj(K,K3,K2,pt,X,M)
/*
   In this case we have a (degree 3) unirational parametrisation
   of Xa (where R : K* -> GL6(k) is the natural embedding, T is
   a k-rational dim 4 subtorus of K*, N2,N3,N are the norms down to
   the quadratic subfield K2, cubic subfield K2,k)
     (K*)/T -> R(v^6*N(v)/N2(v)^2*N3(v)^3)*vec(pt) = Xa <= A6
     followed by M: A6 -> A6
   We use this to find a point on Xa disticnt from pt and then use
   geometric projection for the birational parametrisation
*/
     R2 := RelativeField(K2,K);
     N2 := map<K->K | x :-> K!Norm(R2!x)>;
     R3 := RelativeField(K3,K);
     N3 := map<K->K | x :-> K!Norm(R3!x)>;

     // use v of the form K.1+r - there are at most 3 values of r for which
     //  this gives a trivial element
     y := K.1;
     for r in [0,1,-1,2] do
	u := ((y+r)^6*K!Norm(y+r))/(N2(y+r)^2*N3(y+r)^3);
	if u ne K!1 then break; end if;
     end for;
     assert u ne K!1;

     rep := MatrixRepresentation(K);
     pt1 := Eltseq(rep(u)*Matrix(6,1,pt));
     pts := RowSequence(Matrix([pt,pt1])*M);
     return GeometricProjectionMethodDeg6(X,
		X!([1] cat pts[1]),X!([1] cat pts[2]));

end function;

/* 
   case where the Lie algebra L generates an irreducible
   6-dimensional commutative matrix algebra A IM to a
   deg 6 field K. gen in L is a generator of A of trace 0.
   Xa is the "big orbit" affine patch of the Del Pezzo.
   If bParam is false, then only check for EXISTENCE of a
   parametrisation.
*/
function D6Case(gen,X,bParam)

    I := Ideal(AffinePatch(X,7));
    k := BaseRing(gen);
    assert (k cmpeq Rationals()) or ISA(Type(k), FldAlg);
    P := Generic(I);
    assert Rank(P) eq 6;
    assert BaseRing(P) eq k;

    // first we determine K as a field extn of the base
    // and cubic (resp. quadratic) subfield K3 (resp. K2)
    //  - NB. We use here the fact that the elements of
    //  the Lie algebra <-> elements with trace 0 down to
    //  K3 and K2. This => any non-zero such generates
    //  the whole of K over k and that its minimal poly
    //  must be of the special form used below.
    f := MinimalPolynomial(gen);
    assert Degree(f) eq 6;
    assert (Coefficient(f,5) eq 0) and (Coefficient(f,3) eq 0)
              and (Coefficient(f,1) eq 0);
    a := Coefficient(f,4)/2;
    assert Coefficient(f,2) eq a^2;
    d := -Coefficient(f,0);
    // f = x^6+2a*x^4+a^2*x^2-d
    P1 := PolynomialRing(k);
    K := ext<k|f>;
    K3 := ext<k|P1.1^3+2*a*P1.1^2+a^2*P1.1-d>;
    Embed(K3,K,K.1^2);
    K2 := ext<k|P1.1^2-d>;
    Embed(K2,K,K.1^3+a*K.1);

    // get type - ie is the galois group of the splitting field of K/k
    // 1. D6
    // 2. C6
    // 3. D12
    //  In case 1, the surface is not minimal & we can blow down 3
    // lines & get a "degree 3" parametrisation. The other 2 cases are
    // minimal and we use projection to get a "degree 6" param, if 
    // a param exists.
    disc := -(4*a^3+27*d); // discriminant K3 = disc*d
    boo,Dsqrt := IsSquare(disc);
    if boo then
	typ := 1;
    elif IsSquare(disc*d) then
	typ := 2;
    else 
	typ := 3;
    end if;

    // if k is Q then attempt to get a simpler representative
    //  for the generator of K than the root of f and replace
    //  gen accordingly
    if k cmpeq Rationals() then // should do for general k ??
	L,mp := OptimisedRepresentation(K);
	gen := Evaluate(pol,gen) where pol is
	  PolynomialRing(k)!Eltseq(Inverse(mp)(L.1));
	f := MinimalPolynomial(L.1);
	Embed(K3,L,mp(K3.1));
	Embed(K2,L,mp(K2.1));
        delete mp; delete K;
	K := L;
	if typ eq 1 then // optimise K3 also
	    K3n,mp := OptimisedRepresentation(K3);
	    pol := PolynomialRing(k)!Eltseq(Inverse(mp)(K3n.1));
	    Embed(K3n,K,Evaluate(pol,K!(K3.1)));
	    Dsqrt *:= (Coefficient(pol,1)*seq[3]-Coefficient(pol,2)*seq[2])
		where seq is Eltseq(Inverse(mp)((K3n.1)^2));
	    delete mp; delete K3;
//assert Discriminant(MinimalPolynomial(K3n.1)) eq d*Dsqrt^2; 
	    K3 := K3n;
//printf "L: %o\n\nK3: %o\n\nK2: %o\n\n",L,K3,K2;
	end if;
    end if;

    // find the matrix M taking the usual basis [1,g,g^2,g^3,g^4,g^5]
    // of K (g is K.1) to basis [1=b1,b2,b3,b4,b5,b6]
    // where the reg embedding of K by mult wrt bi basis takes
    // g to gen.
    Minv := Matrix(k,[[e[j,1]: j in [1..6]] where e is gen^i :
			i in [0..5]]);
    M := Minv^(-1);

    // define norm form Q to K3 wrt g^i basis ..
    PK := PolynomialRing(K3,6);
    rF := RelativeField(K3,K);
    Q := Determinant(&+[PK.(i+1)*ChangeRing(mat^i,PK):i in [0..5]]) where
		mat is Matrix(K3,2,2,[0,1,-s[1],-s[2]]) where
		s is Coefficients(MinimalPolynomial(rF!(K.1)));
    // .. and define the 3 quadratic forms over k:
    //  Q1,Q2,Q3 in P s.t. Q = Q1+(K3.1)*Q2+(K3.1)^2*Q3
    Qs := [ &+[Eltseq(LeadingCoefficient(t))[i]*
	   Monomial(P,Exponents(t)): t in Terms(Q)] : i in [1..3] ];

    // define norm form C to K2 wrt g^i basis ..
    PK := PolynomialRing(K2,6);
    rF := RelativeField(K2,K);
    C := Determinant(&+[PK.(i+1)*ChangeRing(mat^i,PK):i in [0..5]]) where
		mat is Matrix(K2,3,3,[0,1,0,0,0,1,-s[1],-s[2],-s[3]]) where
		s is Coefficients(MinimalPolynomial(rF!(K.1)));
    // .. and define the 2 cubic forms over k:
    //  C1 = (1/2)Trace(K2/k,C), C2 = (C-C1)/K2.1,
    Cs := [ &+[Eltseq(LeadingCoefficient(t))[i]*
           Monomial(P,Exponents(t)): t in Terms(C)] : i in [1..2] ];

   // now change variables to get these norm forms wrt the original
   // field basis [b1,..,b6]
   hm := hom<P->P| [&+[M[j,i]*P.j:j in [1..6]]:i in [1..6]]>;
   Qs := Qs@hm;
   Cs := Cs@hm;

   // now there exist u in K3 and v in K2 st Norm(K3/k,u)=Norm(K2/k,v)
   // and st the torus T is given by
   // Norm(K/K3,x)=Norm(K/K2,x)=1 x in K*
   // and the big orbit is the homogeneous space of T given by
   // Norm(K/K3,x)=u Norm(K/K2,x)=v x in K*
   //
   // u is determined by Qi = Trace(K3/k,u*K3.1^(i-1)) mod I, i in 1..3
   // v=a1+a2*K2.1 is determined by Ci = ai mod I, i in 1..2
   //
   // We use a normal form computation where it is often better to
   // convert to a potentially easier GroebnerBasis
   
   J := EasyIdeal(I);
   PJ := Generic(J);
   us := [NormalForm(PJ!Q,J) : Q in Qs];
   assert &and[u in k: u in us];
   ChangeUniverse(~us,k);
   u := K3!us;

   vs := [NormalForm(PJ!C,J) : C in Cs];
   assert &and[v in k: v in vs];
   ChangeUniverse(~vs,k);
   v := vs[1]+vs[2]*K2.1;

   delete J; delete PJ;

   assert Norm(u) eq Norm(v);

   b_sol := SimLocSolEverywhere(K,u,v);
   if not(b_sol and bParam) then
      return b_sol,_;
   end if;

   boo,soln := SimNEQ(K,u,v: HasSolution := true);
   assert boo;

   pt := Eltseq(K!soln[1]);
   return true,((typ ne 1) select D6ParamProj(K,K3,K2,pt,X,Minv)
   	else D6ParamD6(K,K3,Dsqrt,K!K2.1,pt,X,Transpose(Minv)));

end function;
