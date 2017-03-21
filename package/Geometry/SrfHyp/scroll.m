// *********************************************************************
// * Package: scroll.mag                                               *
// * =============================                                     *
// *                                                                   *
// * Author: Josef Schicho                                             *
// *                                                                   *
// * Email : Josef.Schicho@oeaw.ac.at                                  *
// *                                                                   *
// * Date  : March  2008                                               *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// * Lie algebra method for rational scrolls and Veronese surface      *
// *                                                                   *
// *                                                                   *
// * Dependencies:                                                     *
// * rnc.mag, quadratic.mag                                            *
// *                                                                   *
// *********************************************************************
freeze;

// ======================
// = Exported functions =
// ======================


// parametrize rational scrolls or Veronese surfaces
intrinsic ParametrizeScroll(X::Sch, P2::Prj) -> BoolElt, MapSch
{
find a parametrization of rational scrolls or Veronese surfaces.
These are the surfaces of minimal degree.
}
  I := Ideal(X);
  R := Generic(I);
  n := Rank(R);
  Q := CoefficientRing(I);
  Par<s,t,u> := CoordinateRing(P2);
  Vn := VectorSpace(Q,n);

  // first trap P2 and quadric surfaces
  if (n eq 3) then
    para := [s,t,u];
    parai := [R.1,R.2,R.3];
    phi := map<P2 -> X | para,parai>;
    return true,phi;
  elif (n eq 4) then
    return ParametrizeQuadric(X, P2);
  end if;
  //print "computing Lie algebra ...";
  Repr := myFindLieAlgebra(I);
  //print "done!";
  L := Domain(Repr);
  _, ls := HasLeviSubalgebra(L);
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

    // standard parametrization
    standardpar := [ Par | s^(m1-i)*t^(i-1) : i in [1..m1]] 
         cat [ Par | s^(m1-i-1)*t^(i-1)*u : i in [1..m2]];
    inv := Transpose(Matrix([Vn.1,Vn.2,Vn.(m1+1)]));

    // now get a Chevalley basis. For efficiency reasons,
    // get an irreducible representation of even degree if possible
    if IsEven(m1*m2) then
      // decompose the module
      val1 := [v[1] : v in ev | v[2] eq m1 ][1]; 
      val2 := [v[1] : v in ev | v[2] eq m2 ][1]; 
      T1 := Morphism(Eigenspace(Sept,val1),Vn);
      T2 := Morphism(Eigenspace(Sept,val2),Vn);
      // project to an evendimensional submodule (smaller preferred)
      if IsEven(m2) then
        Tboth := VerticalJoin(T2,T1);
        One := ScalarMatrix(Q,m2,1);
        E := HorizontalJoin(One,ZeroMatrix(Q,m2,m1));
        Mat := RMatrixSpace(Q,m2,m2);
      else // m1 must be even
        Tboth := VerticalJoin(T1,T2);
        One := ScalarMatrix(Q,m1,1);
        E := HorizontalJoin(One,ZeroMatrix(Q,m1,m2));
        Mat := RMatrixSpace(Q,m1,m1);
      end if;
      TO := E*Tboth; OT := Tboth^-1*Transpose(E);
      Corr := TO*Sept*OT;
      Detrace := map< Mat -> Mat | 
             x :-> x - Trace(x)/m1 * One >;
      Rep := map< ls -> Mat | 
             x :-> -Detrace(TO*Transpose(Repr(L!x))*OT) >;
      _, CB := RepChevalleyBasis(Rep);
    else // this branch requires integer factorization
      isom, CB := FindXYH(ls);
      if not isom then
        return false, _;
      end if;
    end if;

    x := L!CB[1]; y := L!CB[2]; h := L!CB[3];
    Xt := Transpose(Repr(x));
    Yt := Transpose(Repr(y));
    Ht := Transpose(Repr(h));
    
    // big submodule
    space := Eigenspace(Ht,m1-1);
    assert (Dimension(space) eq 1);
    v := Basis(space)[1];
    Rows := [ Vn | v ];
    for i := 1 to m1-1 do
      Rows[i+1] := 1/i * Rows[i] * Yt;
    end for; 

    // map between the two modules
    nr := Nilradical(L);
    adL := AdjointRepresentation(L);
    space := Nullspace(adL(y)) meet Image(Morphism(nr,L));
    assert (Dimension(space) eq 1); 
    z := L!Basis(space)[1];
    Zt := Transpose(Repr(z));

    // small submodule
    for i := 1 to m2 do
      Rows[m1+i] := Rows[i] * Zt;
    end for;

  elif (Dimension(ls) eq 6) then // product of two P1s  
    // standard parametrization
    nhalf := Integers()!(n/2);
    standardpar := [ Par | s^(nhalf+1-i)*t^(i-1) : i in [1..nhalf]] 
         cat [ Par | s^(nhalf-i)*t^(i-1)*u : i in [1..nhalf]];
    inv := Transpose(Matrix([Vn.1,Vn.2,Vn.(nhalf+1)]));

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
    // requires integer factorization
    isom, CB := FindXYH(L1);
    if not isom then
      return false, _;
    end if;
    x1 := L!CB[1]; y1 := L!CB[2]; h1 := L!CB[3];
    X1t := Transpose(Repr(x1));
    Y1t := Transpose(Repr(y1));
    H1t := Transpose(Repr(h1));

    // Chevalley basis of L2, using a submodule 
    Smod := Eigenspace(H1t,n/2-1);
    assert (Dimension(Smod) eq 2);
    sys1 := Matrix([Smod.1*Transpose(Repr(L!L2.i)) : i in [1..3] ]);
    sys2 := Matrix([Smod.2*Transpose(Repr(L!L2.i)) : i in [1..3] ]);
    sys := HorizontalJoin(sys1,sys2);
    rhs := HorizontalJoin(Smod.1,-Smod.2);
    solh := Solution(sys,rhs);
    h2 := L!( &+ [ solh[1][i] * L2.i : i in [1..3] ] );
    rhs := HorizontalJoin(Smod!0,Smod.1);
    solx := Solution(sys,rhs);
    x2 := L!( &+ [ solx[1][i] * L2.i : i in [1..3] ] );
    rhs := HorizontalJoin(Smod.2,Smod!0);
    soly := Solution(sys,rhs);
    y2 := L!( &+ [ soly[1][i] * L2.i : i in [1..3] ] );
    X2t := Transpose(Repr(x2));
    Y2t := Transpose(Repr(y2));
    H2t := Transpose(Repr(h2));

    // construct matrix
    space := Eigenspace(H1t,n/2-1) meet Eigenspace(H2t,1);
    assert (Dimension(space) eq 1);
    Rows := [ Vn | space.1 ];
    for i := 1 to (nhalf-1) do
      Rows[i+1] := 1/i * Rows[i] * Y1t;
    end for;
    for i := 1 to nhalf do
      Rows[nhalf+i] := Rows[i] * Y2t;
    end for;


  elif (Dimension(ls) eq 8) then // Veronese
    assert (n eq 6);
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
    Matn := MatrixAlgebra(Q,6);
    subst := hom<Polrng ->Matn | Matn!Rant>;
    Vsub1 := Nullspace(subst(Mpol1));
    Vsub2 := Nullspace(subst(Mpol2));
    T := VerticalJoin(Morphism(Vsub2,Vn),Morphism(Vsub1,Vn));
    E := HorizontalJoin(ScalarMatrix(Q,3,1),ZeroMatrix(Q,3,3));
    TO := E*T; OT := T^-1*Transpose(E);

    // construct a 3D module of L
    Mat3 := MatrixAlgebra(Q,3);
    getblock := map< L -> Mat3 | x :-> TO*Transpose(Repr(x))*OT >;
    rho := map< L -> Mat3 | 
      x :-> getblock(x)-2*getblock(ProjKilling(x,cs)) >;
    
    // get some Chevalley basis elements
    V9 := VectorSpace(Q,9);
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
  else
    error "surface is not of minimal degree";
  end if;
  
  // the result 
  M := Matrix(Rows);
  Mi := M^-1*inv;
  para := Eltseq(Vector(standardpar) * ChangeRing(M,Par));
  back := Vector([R.i: i in [1..n]]) * ChangeRing(Mi,R);
  parai := Eltseq(back);
  phi := map<P2 -> X | para, parai>;

  return true,phi; 
end intrinsic;

