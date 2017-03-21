freeze;

//////////////////////////////////////////////////////////////////////
//
// Uses weak-Popov-form lattice-reduction to search for points up to
// a given height (degree) bound on a quadric-intersection over F_q(T)
//
// Author: David Roberts
//
//////////////////////////////////////////////////////////////////////

function degree(x); if x eq 0 then return 0; else return Degree(x); end if; end function;

function pivotindex(M,i);
  n:=NumberOfColumns(M);
  return n+1-j where _,j:=Max([Degree(x): x in Reverse(Eltseq(M[i]))]);
  end function;

///////////////////////////////////////////////////////////////////

function pivotelement(M,i);
  j:=pivotindex(M,i);
  return M[i][j];
  end function;
///////////////////////////////////////////////////////////////////

function pivotdegree(M,i);
  return Degree(pivotelement(M,i));
  end function;
function rowdegree(r);
  return Max([Degree(f): f in Eltseq(r)]);
  end function;
///////////////////////////////////////////////////////////////////

function carrierset(M);
  n:=NumberOfRows(M);
  return {i: i in [1..n]|pivotindex(M,i) ne 0};
  end function;
///////////////////////////////////////////////////////////////////

function IsWPF(M); // "is weak Popov form"
  C:=carrierset(M);
  K:={pivotindex(M,i): i in C};
  if #K eq #C then return true; end if;
  return false;
  end function;
///////////////////////////////////////////////////////////////////

intrinsic WeakPopovForm(M::Mtrx : count:=false) -> Mtrx,Mtrx,RngIntElt
{Returns a weak Popov form matrix N together with the transformation matrix taking M to N}

  if count then j:=0; end if;
    k:=BaseRing(M); if IsField(k) then
      M:=Matrix(Integers(k),M); end if;
  N:=M; PN:=Parent(N); R:=BaseRing(PN);
  T:=Identity(PN);
  while not IsWPF(N) do
    if count then j+:=1; end if;
    C:=carrierset(N);
    CI:=[<c,pivotindex(N,c)>: c in C|#[x: x in C|pivotindex(N,x) eq pivotindex(N,c)] gt 1];
    pi:=CI[1][2]; pii:=c[1] where c is [C: C in CI|(C ne CI[1]) and (C[2] eq pi)];
    if Degree(N[CI[1][1]][pi]) ge Degree(N[pii[1]][pi]) then
      l:=CI[1][1]; k:=pii[1];
    else
      k:=CI[1][1]; l:=pii[1]; end if;
    /* if N[k][pi] eq 0 then return M,Zero(PN),-1; end if; */
    a:=LeadingCoefficient(N[k][pi]); b:=LeadingCoefficient(N[l][pi]);
    m:=Degree(N[k][pi]);
    n:=Degree(N[l][pi]);
    TM:=Identity(PN);
    TM[l][k]:=(-b/a)*R.1^(n-m); O:=N;
    T:=TM*T; N:=TM*N;
    end while;
  if count then return N,T,j; end if;
  return N,T,_;
  end intrinsic;
////////////////////////////////////////////////////////////////////

function randpol(a,b)
R := PolynomialRing(Rationals()); x := R.1;
return R!Polynomial([Random(0,a): i in [0..Random(0,b)]]);
end function;


function randmat(R,n,a,b) // "random" matrix generator for testing.
  M:=Identity(MatrixAlgebra(R,n));
  for i,j in [1..n] do
    M[i][j]:=randpol(a,b);
    end for;
  return M;
  end function;
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

function rand_elt(K,n)
  F:=BaseRing(K);
  return K!Polynomial([Random(F): i in [1..Random([1..n+1])]]);
  end function;


function QI_ex(pt,n)
  K:=Universe(pt);

  repeat
    entsA:=[0] cat [rand_elt(K,n): i in [1..9]];
    A:=SymmetricMatrix(entsA); until not IsSingular(A);
  repeat
    entsB:=[0] cat [rand_elt(K,n): i in [1..9]];
    B:=SymmetricMatrix(entsB); until not IsSingular(B);

  x0T:=Matrix([[K|1,0,0,0]]);
  x0:=Transpose(x0T);

  R:=Integers(K);
  v:=Transpose(Matrix(R,[pt]));
  _,C,_:=SmithForm(v);
  // assert v eq ColumnSubmatrix(C^-1,1,1);

  C:=Matrix(K,C);
  CT:=Transpose(C);
  A1:=CT*A*C; B1:=CT*B*C;

  return QuadricIntersection([A1,B1]);
  end function;

function bad_QI(K,H); // returns a quadric-intersection over K that's
                      // singular mod p for all primes p of degree H
  f:=K.1^((#BaseRing(K)^H)-1)-1;
  A:=SymmetricMatrix([K|0,0,-1,0,0,0,1/2,0,0,0]);
  B:=SymmetricMatrix([K|f,0,1,0,0,-1,0,0,0,1]);
  return QuadricIntersection([A,B]);
  end function;
////////////////////////////////////////////////////////////////

procedure wait(t); // for debugging purposes
  x:=Cputime(); repeat _:=1; until Cputime(x) gt 1; end procedure;

function deg_seq(M); // M a matrix. Requires "rowdegree" from "WPF.m"
  return [rowdegree(Eltseq(M[i])): i in [1..4]];
  end function;

function scale(l,v); // multiplication of whole sequence v by l
  return [l*x: x in Eltseq(v)];
  end function;

function add(a,b); // adding two sequences
  return [a[i]+b[i]: i in [1..#a]];
  end function;

function VtoC3(pt,degs,rows,C,K); // needed for the "long, skinny lattice" case
                                  // converts points from a variety over F_q
                                  // to points on C
  u1:=&+[pt[i]*K.1^(i-1): i in [1..degs[1]+1]];
  u2:=&+[pt[i]*K.1^(i-degs[1]-2): i in [degs[1]+2..degs[1]+degs[2]+2]];
  u3:=&+[pt[i]*K.1^(i-degs[1]-degs[2]-3): i in [degs[1]+degs[2]+3..&+degs+3]];
  Cpt:=C!add(add(scale(u1,rows[1]),scale(u2,rows[2])),scale(u3,rows[3]));
  return Cpt;
  end function;

function VtoC4(pt,degs,rows,C,K); // as above with 4 rows.
  u1:=&+[pt[i]*K.1^(i-1): i in [1..degs[1]+1]];
  u2:=&+[pt[i]*K.1^(i-degs[1]-2): i in [degs[1]+2..degs[1]+degs[2]+2]];
  u3:=&+[pt[i]*K.1^(i-degs[1]-degs[2]-3): i in [degs[1]+degs[2]+3..degs[1]+degs[2]+degs[3]+3]];
  u4:=&+[pt[i]*K.1^(i-degs[1]-degs[2]-degs[3]-4): i in [degs[1]+degs[2]+degs[3]+4..&+degs+4]];
  Cpt:=C!add(add(add(scale(u1,rows[1]),scale(u2,rows[2])),scale(u3,rows[3])),scale(u4,rows[4]));
  return Cpt;
  end function;


// For points of height 0 or 1 we need a separate treatment.

function deg0pts(QI:OO:=false);

  if IsSingular(QI) then
    return SingularPoints(QI);
    end if;

  e1,e2:=Explode(DefiningEquations(QI));
  K:=BaseRing(Parent(e1)); F:=BaseRing(K);
  FF<a,b,c,d>:=PolynomialRing(F,4); KK:=FunctionField(FF);
  RR:=Integers(KK); KK4:=PolynomialRing(KK,4);
  ev1:=Evaluate(KK4!e1,[a,b,c,d]); ev2:=Evaluate(KK4!e2,[a,b,c,d]);
  eqns:=Coefficients(RR!ev1) cat Coefficients(RR!ev2);
  S:=Scheme(ProjectiveSpace(FF),eqns);
  ptS:=Points(S);
  ptQI:={@ QI!Eltseq(pt): pt in ptS @};
  if (OO and #ptQI ne 0) then return {@ ptQI[1] @}; end if;
  return ptQI;
  end function;


function deg1pts(QI:OO:=false);

  if IsSingular(QI) then
    return SingularPoints(QI);
    end if;

  e1,e2:=Explode(DefiningEquations(QI));
  K:=BaseRing(Parent(e1)); F:=BaseRing(K);
  FF<a1,a2,a3,a4,a5,a6,a7,a8>:=PolynomialRing(F,8);
  KK:=FunctionField(FF); RR:=Integers(KK); KK4:=PolynomialRing(KK,4);
  a:=[a1+a2*KK.1,a3+a4*KK.1,a5+a6*KK.1,a7+a8*KK.1];
  ev1:=Evaluate(KK4!e1,a); ev2:=Evaluate(KK4!e2,a);
  eqns:=Coefficients(RR!ev1) cat Coefficients(RR!ev2);
  S:=Scheme(ProjectiveSpace(FF), eqns);
  ptS:=Points(S);
  ptQI:={@ QI![p[2*i-1]+p[2*i]*K.1: i in [1..4]] where p is Eltseq(pt): pt in ptS @};
  if OO then return ptQI[1]; end if;
  return ptQI;
  end function;


function pointsmodp(C); // see above
  DEC:=DefiningEquations(C);
  F4:=Universe(DEC);
  F:=BaseRing(F4);
  F0:=[x: x in F];
  F2<y,z>:=PolynomialRing(F,2);
  F1 := PolynomialRing(F,1); u := F1.1;
  A:=AffineSpace(F2);
  B:=AffineSpace(F1);
  K4:=PolynomialRing(F2,4);
  L4:=PolynomialRing(F1,4);
  pts:={@ @};

  e1,e2:=Explode([K4!x: x in DEC]);
  for x in F0 do
    yz:=[1,x,y,z];
    S:=Scheme(A,[Evaluate(e1,yz),Evaluate(e2,yz)]);
    assert Dimension(S) eq 0;
    pS:=Points(S);
    if #pS gt 0 then pts join:={@ C![F|1,x,Y,Z] where Y,Z is Explode(Eltseq(p)) : p in pS @};
    end if;
    end for;

  yz:=[0,1,y,z];
  S:=Scheme(A,[Evaluate(e1,yz),Evaluate(e2,yz)]);
  assert Dimension(S) eq 0;
  pS:=Points(S);
  if #pS gt 0 then pts join:={@ C![F|0,1,Y,Z] where Y,Z is Explode(Eltseq(p)) : p in pS @};
  end if;

  yz:=[0,0,1,u];
  S:=Scheme(B,[Evaluate(e1,yz),Evaluate(e2,yz)]);
  assert Dimension(S) le 0;
  pS:=Points(S);
  if #pS gt 0 then pts join:={@ C![F|0,1,Y,Z] where Y,Z is Explode(Eltseq(p)) : p in pS @};
  end if;

  if IsCoercible(C,[0,0,0,1]) then pts join:={@ C![F|0,0,0,1] @}; end if;

  return pts;
  end function;

////////////////////////////////////////////////////////////////////////

function numberofpointsmodp_ecmethod(C);

  F:=BaseRing(C);
  R := PolynomialRing(F); t := R.1;
  A,B:=Explode(AB) where _,AB is IsQuadricIntersection(C);
  q:=Determinant(A-t*B);
  zero_ends:=false;
  if Coefficient(q,4) eq 0 then if Coefficient(q,0) ne 0 then
      q:=Determinant(B-t*A);
      else zero_ends:=true; end if;
    end if;
  if zero_ends then b,c,d:=Explode([Coefficient(q,i): i in [1..3]]);
    I:=-3*b*d+c^2; J:=9*b*c*d-2*c^3;
  else
    I:=QuarticIInvariant(q);
    J:=QuarticJInvariant(q);
    end if;
  E:=EllipticCurve([0,0,0,-27*I,-27*J]);
  return #E;
  end function;

//////////////////////////////////////////////////////////////////////

function QI_pts(C,H: only_one:=false,exact_bound:=false,debug:=false,ChooseH0:=0,gpselect:=100);
              // C - quadric intersection; H - height bound
              // requires "WeakPopovForm" from "WPF.m"
              // set only_one to true to find just one point.
              // set ExactBound to true to ignore points of height
              // greater than H (can happen in case 2 of the lattice analysis).
              // ChooseH0 - if zero runs the program as normal. Otherwise H0
              // is the value given to this parameter. This can lead to there
              // being 4 "good rows" in the matrix defining the lattice.

    if debug then tim:=Cputime(); end if;

  if H eq 0 then 
    if debug then print "calling deg0pts"; end if;
  return deg0pts(C:OO:=only_one); end if;


   if IsSingular(C) then
    if debug then print "Curve is singular!"; end if;
    return "CurveisSingular"; end if;

  if ChooseH0 eq 0 then H0:=1+(2*H div 3);
    else H0:=ChooseH0; end if;

  eqns:=DefiningEquations(C);
  e1:=eqns[1]; e2:=eqns[2];
  Fa:=[Derivative(e1,i): i in [1..4]]; Fb:=[Derivative(e2,i): i in [1..4]];

  K4:=Universe(eqns); P3:=AmbientSpace(C);
  K:=BaseRing(K4); R<t>:=Integers(K); F:=BaseRing(K); K1:=PolynomialRing(K);

  allirr:=AllIrreduciblePolynomials(F,H0);
  AA,BB:=Explode(AB) where _,AB is IsQuadricIntersection(C);
  disc:=R!Discriminant(Determinant(AA-K1.1*Matrix(K1,BB)));
  bad_primes:={f[1]: f in Factorization(disc)};
  good_primes:={@ f: f in allirr|not f in bad_primes @};
  if #good_primes eq 0 then print "All primes of degree",H0,"are bad. Recursive call with H =",H+1;
    return $$(C,H+1); end if;         // This rather extreme case would be unfortunate.

  function reduceC(p)
      G:=ext<F|p>;
      R1,m1:=quo<R|p>; R2,m2:=quo<R|p^2>; R3,m3:=quo<R|p^3>;
      P3_1:=ProjectiveSpace(R1,3); P3_2:=ProjectiveSpace(R2,3); P3_3:=ProjectiveSpace(R3,3);
      RR1,RR2,RR3:=Explode([CoordinateRing(x): x in [P3_1,P3_2,P3_3]]);
      h1:=hom<K4->RR1|hom<K->RR1|R1.1>,RR1.1,RR1.2,RR1.3,RR1.4>;

      P1<s1,s2>:=ProjectiveSpace(K,1);
      CP1:=CoordinateRing(P1);
      CP1_4:=PolynomialRing(CP1,4);
      Chom:=hom<K4->CP1_4|CP1_4.1,CP1_4.2,CP1_4.3,CP1_4.4>;
      e1a:=Chom(e1); e2a:=Chom(e2);

      C1:=Curve(P3_1,[h1(x): x in eqns]);
      phi:=hom<G->R1|R1.1>;
      RG:=PolynomialRing(G,4);
      h2:=hom<RR1->RG|hom<R1->RG|G.1>,RG.1,RG.2,RG.3,RG.4>;
      S:=Scheme(ProjectiveSpace(G,3),[h2(h1(x)): x in eqns]);
      return Curve(S); end function;

  np:=[numberofpointsmodp_ecmethod(reduceC(good_primes[i])): i in [1..Ceiling(#good_primes/gpselect)]];
  _,j:=Min(np);
  p:=good_primes[j];
  if debug then print "p = ",p; end if;

  G:=ext<F|p>;
  R1,m1:=quo<R|p>; R2,m2:=quo<R|p^2>; R3,m3:=quo<R|p^3>;
  P3_1:=ProjectiveSpace(R1,3); P3_2:=ProjectiveSpace(R2,3); P3_3:=ProjectiveSpace(R3,3);
  RR1,RR2,RR3:=Explode([CoordinateRing(x): x in [P3_1,P3_2,P3_3]]);
  h1:=hom<K4->RR1|hom<K->RR1|R1.1>,RR1.1,RR1.2,RR1.3,RR1.4>;

  P1<s1,s2>:=ProjectiveSpace(K,1);
  CP1:=CoordinateRing(P1);
  CP1_4:=PolynomialRing(CP1,4);
  Chom:=hom<K4->CP1_4|CP1_4.1,CP1_4.2,CP1_4.3,CP1_4.4>;
  e1a:=Chom(e1); e2a:=Chom(e2);

  C1:=Curve(P3_1,[h1(x): x in eqns]);
  phi:=hom<G->R1|R1.1>;
  RG:=PolynomialRing(G,4);
  h2:=hom<RR1->RG|hom<R1->RG|G.1>,RG.1,RG.2,RG.3,RG.4>;
  S:=Scheme(ProjectiveSpace(G,3),[h2(h1(x)): x in eqns]);

  pts:={@ @};
  first_column:=1;

  // Internal function taking one specific point mod p and searching for
  // points on C that are congruent to it (mod p).
  function IQI(pt1);

    // we need to permute the variables if the first coordinate of pt1 is zero
    // or if A3*B4-A4*B3 = 0

    perm:=[1,2,3,4];
    if pt1[1] eq 0 then
      j:=Min([i: i in [2,3,4] | pt1[i] ne 0]);
      perm[1]:=j; perm[j]:=1;
      end if;
    temp:=C1![phi(x): x in Eltseq(pt1)];
    pt1:=[K!(a/temp[perm[1]]): a in Eltseq(temp)];
    A:=[Evaluate(x,pt1): x in Fa]; B:=[Evaluate(x,pt1): x in Fb];
    if debug then print "A =",A,"B= ",B; end if;

    while m1(A[perm[3]]*B[perm[4]]-A[perm[4]]*B[perm[3]]) eq 0 do
      if debug then print "changing permutation"; end if;
      perm:=[perm[1],perm[3],perm[4],perm[2]];
      end while;

    if perm ne [1,2,3,4] then if debug then
        print "permuted variables. permutation selected =",perm;
        end if;
      end if;


    // matrix row r1:
    M1:=Matrix(R1,[[m1(A[perm[3]]),m1(A[perm[4]])],[m1(B[perm[3]]),m1(B[perm[4]])]]);
    m_1:=Matrix([[-m1(Evaluate(e1,pt1)/p)],[-m1(Evaluate(e2,pt1)/p)]]);
    v:=[K!x: x in Eltseq((M1^-1)*m_1)];
    pt2:=pt1;
    pt2[perm[3]]+:=p*v[1]; pt2[perm[4]]+:=p*v[2];
    M2:=Matrix(R2,[[m2(A[perm[3]]),m2(A[perm[4]])],[m2(B[perm[3]]),m2(B[perm[4]])]]);
    m_2:=Matrix([[-m2(Evaluate(e1,pt2)/p)],[-m2(Evaluate(e2,pt2)/p)]]);
    v:=[K!x: x in Eltseq((M2^-1)*m_2)];
    pt3:=pt2;
    pt3[perm[3]]+:=v[1]*p; pt3[perm[4]]+:=v[2]*p;
    r1:=pt3; if debug then print "r1 =",r1,"over",Universe(r1); end if;

    // matrix row r2:
    m_3:=Matrix([[-m1(Evaluate(e1,pt1)/p+A[perm[2]])],[-m1(Evaluate(e2,pt1)/p+B[perm[2]])]]);
    v:=[K!x: x in Eltseq((M1^-1)*m_3)];
    pt2a:=pt1;
    pt2a[perm[3]]+:=v[1]*p; pt2a[perm[4]]+:=v[2]*p; pt2a[perm[2]]+:=p;
    m_4:=Matrix([[-m2(Evaluate(e1,pt2a)/p)],[-m2(Evaluate(e2,pt2a)/p)]]);
    v:=[K!x: x in Eltseq((M2^-1)*m_4)];
    pt3a:=pt2a;
    pt3a[perm[3]]+:=v[1]*p; pt3a[perm[4]]+:=v[2]*p;
    r2:=Eltseq(Vector(pt3a)-Vector(r1));

    // matrix row r3:
    m_5:=Matrix([[-m1(Evaluate(e1,pt1)/p-A[perm[2]])],[-m1(Evaluate(e2,pt1)/p-B[perm[2]])]]);
    v:=[K!x: x in Eltseq((M1^-1)*m_5)];
    pt2b:=pt1;
    pt2b[perm[2]]-:=p; pt2b[perm[3]]+:=v[1]*p; pt2b[perm[4]]+:=v[2]*p;
    m_6:=Matrix([[-m2(Evaluate(e1,pt2b)/p)],[-m2(Evaluate(e2,pt2b)/p)]]);
    v:=[K!x: x in Eltseq((M2^-1)*m_6)];
    pt3b:=pt2b;
    pt3b[perm[3]]+:=v[1]*p; pt3b[perm[4]]+:=v[2]*p;
    r3a:=Eltseq(Vector(pt3b)-Vector(r1));
    lc:=LeadingCoefficient(R!r3a[perm[2]]); r3a:=[x/lc: x in r3a];
    r3b:=Eltseq(Vector(r3a)-Vector(r2));
    l:=r3b[perm[3]]/p^2;

    r3:=[K|0,0,0,0]; r4:=[K|0,0,0,0];

    if m1(l) eq 0 then if debug then print "switching columns in r3"; end if;
      r4[perm[4]]:=p^2; r3[perm[3]]:=p^3;
      else
      m:=r3b[perm[4]]/p^2; k:=K!(m1(m)/m1(l));
      r3[perm[3]]:=p^2; r3[perm[4]]:=k*p^2;
      r4[perm[4]]:=p^3;
      end if;

    M:=Matrix(R,[r1,r2,r3,r4]);
    if debug then print "matrix before WPF =",M; end if;
    N:=WeakPopovForm(M);
    if debug then print "matrix after WPF = ",N; end if;

    // we can only get a solution from this lattice if some rows have degree less than H.
    // here we throw away the "bad" lattices:
    // if debug then print "from local point ",pt1; end if;

    ds:=deg_seq(N);
      if #[x: x in ds| x le H] eq 0 then
      return {@ @}; end if;

    good_rows:=[i: i in [1..4] |ds[i] le H];
    if debug then print ds; end if;


    // before we split into separate cases, first check whether each of the
    // "good" rows gives a point by itself. This should automatically
    // We only need do this when searching for one point.

    if only_one then
      for g in good_rows do
        b:=Eltseq(N[g]);
        a,pt:=IsCoercible(C,b); if a then return {@ pt @}; end if;
        end for;
      end if; // end if only_one
    // now split into cases depending on the number of "good" rows.

    // Case 1: one good row. This is the simplest - we see if this row is a point on C.
    if #good_rows eq 1 then
      if debug then print "1 good row"; end if;
      b:=Eltseq(N[good_rows[1]]);
      a,pt:=IsCoercible(C,b); if a then
        joinpoints:={@ pt @};
      if only_one then if #joinpoints gt 0 then return {@ joinpoints[1] @}; end if; end if;
      if debug then if #joinpoints gt 0 then print "****** points available ******"; wait(1); end if; end if;
      return joinpoints; end if;
      else

      // Case 2: two good rows. Here we evaluate e1 and e2 at a general linear combination
      // of the two rows s1*b1+s2*b2. We then solve for s1 and s2.
      // Note that this method may return points of height greater than H
      if #good_rows eq 2 then
        if debug then print "2 good rows:",[N[j]:j in good_rows]; end if;
        b1:=N[good_rows[1]]; b2:=N[good_rows[2]];
        b:=add(scale(s1,b1),scale(s2,b2));
        ev1:=Evaluate(e1a,b); ev2:=Evaluate(e2a,b);
        S:=Scheme(P1,[ev1,ev2]); // if debug then print "Dimension(S) =",Dimension(S); end if;
        DS:=Dimension(S); if DS eq -1 then return {@ @}; end if; assert DS eq 0;
        ptS:=Points(S);
        ptS1:=[scale(l,r) where l is LCM([Denominator(s): s in Eltseq(r)]): r in ptS];
        ptsC1:={@ add(scale(r[1],b1),scale(r[2],b2)): r in ptS1 @};
        ptsC:={@ C!x: x in ptsC1 @};
        joinpoints:=ptsC;
        if only_one then if #joinpoints gt 0 then return {@ joinpoints[1] @}; end if; end if;
        if debug then if #joinpoints gt 0 then print "****** points available ******"; wait(1); end if; end if;
        return joinpoints;
        else

        // If we are only searching for one point:
        // before considering combinations of all 3 or 4 good rows, we check first whether
        // two out of the three give a point on C. If this is the case then when searching
        // for only one point the calculations in MAGMA will be a lot faster. We use the
        // same technique as for the two good rows case.
        if only_one then
          if debug then print "Checking combinations of 2 rows in case 3 or 4"; end if;
          assert #good_rows in [3,4];
          if #good_rows eq 3 then combs:=[[1,2],[2,3],[1,3]];
            else combs:=[[1,2],[1,3],[1,4],[2,3],[2,4],[3,4]]; end if;
          for ij in combs do
            i,j:=Explode(ij);
            b1:=N[good_rows[i]]; b2:=N[good_rows[j]];
            b:=add(scale(s1,b1),scale(s2,b2));
            ev1:=Evaluate(e1a,b); ev2:=Evaluate(e2a,b);
            S:=Scheme(P1,[ev1,ev2]);
            DS:=Dimension(S); if DS eq -1 then continue; end if; assert DS eq 0;
            ptS:=Points(S);
            ptS1:=[scale(l,r) where l is LCM([Denominator(s): s in Eltseq(r)]): r in ptS];
            ptsC1:={@ add(scale(r[1],b1),scale(r[2],b2)): r in ptS1 @};
            ptsC:={@ C!x: x in ptsC1 @};
            if #ptsC gt 0 then
              return {@ ptsC[1] @};
              else continue; end if;
            end for;
          end if; // end if only_one

        // Case 3: three good rows. This is a "long, skinny" lattice.
        if #good_rows eq 3 then
          if debug then print "3 good rows"; end if;
          b1,b2,b3:=Explode([N[good_rows[i]]: i in [1..3]]);
          db1,db2,db3:=Explode([rowdegree(Eltseq(b)): b in [b1,b2,b3]]);
          d1,d2,d3:=Explode([H-rowdegree(Eltseq(b)): b in [b1,b2,b3]]);
          FF:=PolynomialRing(F,3+d1+d2+d3);
          KK:=FunctionField(FF);
          RR:=Integers(KK);
          KK4:=PolynomialRing(KK,4);
          bb1,bb2,bb3:=Explode([ChangeUniverse(Eltseq(x),KK): x in [b1,b2,b3]]);
          ee1:=KK4!e1; ee2:=KK4!e2;
          u1:=&+[FF.i*KK.1^(i-1): i in [1..d1+1]];
          u2:=&+[FF.i*KK.1^(i-d1-2): i in [d1+2..d1+d2+2]];
          u3:=&+[FF.i*KK.1^(i-d1-d2-3): i in [d1+d2+3..d1+d2+d3+3]];
          X:=add(add(scale(u1,bb1),scale(u2,bb2)),scale(u3,bb3));
          FX:=[Evaluate(e,X): e in [ee1,ee2]];
          cFX:=&cat[Coefficients(RR!f): f in FX];
          V:=Scheme(AffineSpace(FF),cFX);
          ptsV:=Points(V); ptsV:={@ pt: pt in ptsV |#[x: x in Eltseq(pt)|x ne 0] gt 0 @};
          ptsC:={@ VtoC3(pt,[d1,d2,d3],[b1,b2,b3],C,K): pt in ptsV @};
          joinpoints:=ptsC;
          if only_one then if #joinpoints gt 0 then return {@ joinpoints[1] @}; end if; end if;
          if debug then if #joinpoints gt 0 then print "****** points available ******"; wait(1); end if; end if;
          return joinpoints;

          else assert #good_rows eq 4; // we are only in this case if H0 has been set manually.
          // this is very slow, even for small H0 so it would be best to avoid this case. If a
          // chosen H0 gives rise to many WPF matrices with 4 good rows then it will be better
          // to choose another. With this in mind, the following lines of code will not be called
          // by the outer function if "OnePoint" is set to true.


          if debug then print "4 good rows"; end if;
          if not only_one then
          b1,b2,b3,b4:=Explode([N[i]: i in [1..4]]);
          db1,db2,db3,db4:=Explode([rowdegree(Eltseq(b)): b in [b1,b2,b3,b4]]);
          d1,d2,d3,d4:=Explode([H-rowdegree(Eltseq(b)): b in [b1,b2,b3,b4]]);
          FF:=PolynomialRing(F,4+d1+d2+d3+d4);
          KK:=FunctionField(FF);
          RR:=Integers(KK);
          KK4:=PolynomialRing(KK,4);
          bb1,bb2,bb3,bb4:=Explode([ChangeUniverse(Eltseq(x),KK): x in [b1,b2,b3,b4]]);
          ee1:=KK4!e1; ee2:=KK4!e2;
          u1:=&+[FF.i*KK.1^(i-1): i in [1..d1+1]];
          u2:=&+[FF.i*KK.1^(i-d1-2): i in [d1+2..d1+d2+2]];
          u3:=&+[FF.i*KK.1^(i-d1-d2-3): i in [d1+d2+3..d1+d2+d3+3]];
          u4:=&+[FF.i*KK.1^(i-d1-d2-d3-4): i in [d1+d2+d3+4..d1+d2+d3+d4+4]];
          X:=add(add(add(scale(u1,bb1),scale(u2,bb2)),scale(u3,bb3)),scale(u4,bb4));
          FX:=[Evaluate(e,X): e in [ee1,ee2]];
          cFX:=&cat[Coefficients(RR!f): f in FX];
          V:=Scheme(AffineSpace(FF),cFX);
          ptsV:=Points(V); ptsV:={@ pt: pt in ptsV |#[x: x in Eltseq(pt)|x ne 0] gt 0 @};
          ptsC:={@ VtoC4(pt,[d1,d2,d3,d4],[b1,b2,b3,b4],C,K): pt in ptsV @};
          joinpoints:=ptsC;
          if only_one then if #joinpoints gt 0 then return {@ joinpoints[1] @}; end if; end if;
          if debug then if #joinpoints gt 0 then print "****** points available ******"; wait(1); end if; end if;
          return joinpoints;
          end if; // end if not only_one

          end if;
        end if;
      end if;
    return {@ @};
  end function; // end function IQI

  //////////////////////////////////
  es1,es2:=Explode(DefiningEquations(S));

  if IsCoercible(S,[0,0,0,1]) then
    pt1:=S![0,0,0,1];
    if debug then print "calling IQI with mod p point",pt1; end if;
    joinpts:=IQI(pt1);
    if #joinpts gt 0 then
      if only_one then return joinpts[1]; end if;
      pts join:=joinpts; end if; end if;

  F1 := PolynomialRing(G,1); u := F1.1;
  B:=AffineSpace(F1);
  L4:=PolynomialRing(F1,4);

  yz:=[0,0,1,u];
  S1:=Scheme(B,[Evaluate(L4!es1,yz),Evaluate(L4!es2,yz)]);
  assert Dimension(S1) le 0;
  S1pts:=Points(S1);
  if #S1pts gt 0 then
    for pt in S1pts do
      pt1:=[0,0,1,U] where U is Explode(Eltseq(pt));
      assert IsCoercible(S,pt1);
      if debug then print "calling IQI with mod p point",pt1; end if;
      joinpts:=IQI(pt1);
      if #joinpts gt 0 then
        if only_one then return {@ joinpts[1] @}; end if;
        pts join:=joinpts; end if;
      end for;
    end if;

  F2<y,z>:=PolynomialRing(G,2);
  A:=AffineSpace(F2);
  K4:=PolynomialRing(F2,4);

  yz:=[0,1,y,z];
  e1,e2:=Explode([K4!x: x in [es1,es2]]);
  S2:=Scheme(A,[Evaluate(e1,yz),Evaluate(e2,yz)]);
  assert Dimension(S2) le 0;
  S2pts:=Points(S2);
  if #S2pts gt 0 then
    for pt in S2pts do
      pt1:=[0,1,Y,Z] where Y,Z is Explode(Eltseq(pt));
      assert IsCoercible(S,pt1);
      if debug then print "calling IQI with mod p point",pt1; end if;
      joinpts:=IQI(pt1);
      if #joinpts gt 0 then
        if only_one then return {@ joinpts[1] @}; end if;
        pts join:=joinpts; end if;
      end for;
    end if;

  for X in G do
    yz:=[1,X,y,z];
    S3:=Scheme(A,[Evaluate(e1,yz),Evaluate(e2,yz)]);
    assert Dimension(S3) le 0;
    S3pts:=Points(S3);
    if #S3pts gt 0 then
      for pt in S3pts do
        pt1:=[1,X,Y,Z] where Y,Z is Explode(Eltseq(pt));
        assert IsCoercible(S,pt1);
        if debug then print "calling IQI with mod p point",pt1; end if;
        joinpts:=IQI(pt1);
        if #joinpts gt 0 then
          if only_one then return {@ joinpts[1] @}; end if;
          pts join:=joinpts; end if;
        end for;
      end if;
    end for;

  return pts;
  end function; // end function QI_pts




//////////////////////////////////////////////////////////////////////////////////////
//
// ... and the main function:

intrinsic PointsQI(C::Crv[FldFunRat], H::RngIntElt : OnlyOne:=false, ExactBound:=false, varH0:=0, 
                                                     best_p:=100) -> SetIndx
  {Returns all points of degree <= H on the quadric-intersection C (over a rational function field).}
K:=BaseRing(C); F:=BaseRing(K);
require Rank(K) eq 1: "Curve must be defined over a univariate rational function field over a finite field";
require Type(F) eq FldFin: "Curve must be defined over a univariate rational function field over a finite field";
require IsQuadricIntersection(C): "C is not a quadric-intersection";
require H ge 0: "H must be a non-negative integer";
require best_p in [1..100]: "Please select an integer between 1 and 100 for the parameter best_p";

  if H eq 0 then return deg0pts(C: OO:=OnlyOne); end if;
  if H eq 1 then return QI_pts(C,1:only_one:=OnlyOne,exact_bound:=ExactBound,
                                   debug:=false,ChooseH0:=2,gpselect:=best_p); end if;
  assert H gt 1;
  if varH0 eq 0 then
    if OnlyOne then
      return QI_pts(C,H: only_one:=true, exact_bound:=ExactBound, debug:=false,ChooseH0:=0,gpselect:=best_p);
      end if; // end if OnlyOne
    return QI_pts(C,H: only_one:=false, exact_bound:=ExactBound, debug:=false,ChooseH0:=0,gpselect:=best_p);
    end if; // end if varH0 eq 0

  assert varH0 ge 2;
  if OnlyOne then
    return QI_pts(C,H: only_one:=true, exact_bound:=ExactBound, debug:=false,ChooseH0:=varH0,gpselect:=best_p);
    // might change this to loop over h0 in [2..varH0];
    end if;
  return QI_pts(C,H: only_one:=false, exact_bound:=ExactBound, debug:=false,ChooseH0:=varH0,gpselect:=best_p);

  end intrinsic;

////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////

function points_of_degree_H(f,H:debug:=0);
KUV:=Parent(f); K:=BaseRing(KUV); R:=Integers(K); F:=BaseRing(K);
d:=TotalDegree(f);
P2<X,Y,Z>:=ProjectivePlane(K);
R3:=CoordinateRing(P2);
h:=hom<KUV->R3|X,Z>;
q:=Y^2*Z^(d-2)-h(f);
C:=Curve(P2,q);

G:=ext<F|H>;
p:=MinimalPolynomial(G.1,F);
R_p,m1:=quo<R|p>;
R3_p<x1,y1,z1>:=PolynomialRing(R_p,3);
R_p2,m2:=quo<R|p^2>;
R3_p2<x2,y2,z2>:=PolynomialRing(R_p2,3);
m1a:=hom<K->R3_p|m1(K.1)>;
m2a:=hom<K->R3_p2|m2(K.1)>;
h1:=hom<R3->R3_p|m1a,x1,y1,z1>;
h2:=hom<R3->R3_p2|m2a,x2,y2,z2>;
q_p:=h1(q);
F1:=Derivative(q,1); F2:=Derivative(q,2); F3:=Derivative(q,3);
F1_p:=h1(F1); F2_p:=h1(F2); F3_p:=h1(F3);

step1list:=[];
Ry := PolynomialRing(R_p); y := Ry.1;
hy:=hom<R3_p->Ry|0,y,0>;
for X1 in R_p do if debug ge 2 then print X1; end if;
  qX1:=hy(Evaluate(q_p,[X1,y1,1]));
  rts:=Roots(qX1);
  if #rts gt 0 then
    step1list cat:=[[X1,rts[1][1]]]; end if;
  end for;

P2<r1,r2,r3>:=ProjectiveSpace(F,2);
  CP2:=CoordinateRing(P2);
  K1 := FunctionField(CP2); T1 := K1.1;
  RK1:=Integers(K1);
  K1_3:=PolynomialRing(K1,3);
  FX_a:=K1_3!q;
P1<s1,s2>:=ProjectiveSpace(K,1);
  CP1:=CoordinateRing(P1);
  CP1_3:=PolynomialRing(CP1,3);
  FX_b:=CP1_3!q;

list:=[]; listC:=[];
if debug ge 1 then print "looping over x12 in step1list..."; end if;
  for x12 in step1list do
  vx:=Append(x12,1);
  vy:=[R_p2|0,0,1];
  if Evaluate(F1_p,vx) ne 0 then
    vy[2]:=m2(R!vx[2]);
    b:=1/Evaluate(F1_p,vx); b:=m2(R!b);
    a:=m2(Evaluate(q,[R!v: v in vx]));
    c:=m2(R!vx[1]);
    vy[1]:=c-a*b;
  else vy[1]:=m2(R!vx[1]);
    b:=1/Evaluate(F2_p,vx); b:=m2(R!b);
    a:=m2(Evaluate(q,[R!v: v in vx]));
    c:=m2(R!vx[2]);
    vy[2]:=c-a*b;
    end if;
  if Evaluate(F1_p,[m1(R!v): v in vy]) eq 0 then
    o:=0;
  else o:=1; alpha:=R!(-Evaluate(F2_p,[m1(R!v): v in vy])/Evaluate(F1_p,[m1(R!v): v in vy]));
    end if;
  if o eq 0 then L:=Matrix([[R!v: v in vy],[p,0,0],[0,p^2,0]]);
  else
    L:=Matrix([[R!v: v in vy],[p*alpha,p,0],[p^2,0,0]]);
    end if;
  M:=WeakPopovForm(L);
  RSM:=RowSequence(M);
  Sort(~RSM,func<a,b|rowdegree(a)-rowdegree(b)>);
  b1:=RSM[1]; b2:=RSM[2]; b3:=RSM[3];
  ptS_1:={};
  if rowdegree(b3) gt H then if debug ge 2 then print Index(step1list,x12),"Degree of b3 > H"; end if;
    f1:=Evaluate(FX_b,[s1*b1[i]+s2*b2[i]: i in [1..3]]);
    S:=Scheme(P1,f1);
    ptS:=Points(S);
    ptS1:=[[R|r[1]*l,r[2]*l] where l is LCM([Denominator(s): s in Eltseq(r)]): r in ptS];
    if #ptS gt 0 then if debug ge 1 then print "found some points: ",ptS1,"RSM = ",RSM; end if; end if;
    ptsC:=[C![r[1]*b1[i]+r[2]*b2[i]: i in [1..3]]: r in ptS1];
    ptsC:=[pt: pt in ptsC|Eltseq(pt) ne [0,1,0]];
    listC cat:=ptsC;
    if debug ge 1 then
      if #ptsC gt 0 then print "from",Index(step1list,x12),"of",#step1list,"found",#Set(ptsC),"points: ",Set(ptsC); end if;
    end if;
  else
    assert [rowdegree(b): b in RSM] eq [H,H,H]; if debug ge 2 then print Index(step1list,x12),"all rows have degree = H"; end if;
    c1,c2,c3:=Explode([ChangeUniverse(b,K1): b in RSM]);
    f1:=Evaluate(FX_a,[r1*c1[i]+r2*c2[i]+r3*c3[i]: i in [1..3]]);
    eqns:=Coefficients(RK1!f1);
    S:=Scheme(P2,eqns); ptS:=Points(S);
    if #ptS gt 0 then if debug ge 1 then print "found some points: ",ptS,"RSM = ",RSM; end if; end if;
    ptsC:=[C![r[1]*b1[i]+r[2]*b2[i]+r[3]*b3[i]: i in [1..3]]: r in ptS];
    ptsC:=[pt: pt in ptsC|Eltseq(pt) ne [0,1,0]];
    listC cat:=ptsC;
    if debug ge 1 then
      if #ptsC gt 0 then print "from",Index(step1list,x12),"of",#step1list,"found",#Set(ptsC),"points: ",Set(ptsC); end if;
      end if;
    end if;
  end for;
return listC;
// return {[l*pt[1],l*pt[3]] where l is LCM([Denominator(pt[i]): i in [1,3]]): pt in listC};
end function;

//////////////////////////////////////////////////////////////////////////////////////

// TO DO: + only seems to return one point for each +/- pair
//        + understand whether using a QI is always more efficient in deg 4

function PointsOfDegreeH(f,H)
// (f::RngMPolElt,H::RngIntElt) -> SeqEnum[Pt]
// {Returns all points of degree <= H on the curve
//  given by y^2 = f(U,V) for a homogenous polynomial f of degree > 2}

  assert Rank(Parent(f)) eq 2 and Type(BaseRing(Parent(f))) eq FldFunRat;
  // "f must be homogeneous in 2 variables over a univariate function field";
  assert TotalDegree(f) gt 2 and IsHomogeneous(f);
  // "f must be homogeneous of degree > 2";

return points_of_degree_H(f,H);
end function;

intrinsic RationalPoints(C::CrvHyp[FldFunRat] : Bound:=-1, OnlyOne:=false) -> SeqEnum[Pt]
{Same as Points}
  return Points(C : Bound:=Bound, OnlyOne:=OnlyOne);
end intrinsic;

intrinsic Points(C::CrvHyp[FldFunRat] : Bound:=-1, OnlyOne:=false) -> SeqEnum[Pt]
{Search for points on the hyperelliptic curve C (defined over a rational function field).
 The 'Bound' MUST be given; the routine searches for points whose affine x-coordinates have
 height (= degree) at most this bound (however it may not find all such points)}
  require Bound ge 0: "A non-negative integer MUST be given for the (non-optional) argument 'Bound'";
  f,h := HyperellipticPolynomials(C);
  assert IsZero(h);  // TO DO: convert to SimplifiedModel

  // In degree 4, convert to a QI  
  if Degree(f) eq 4 then
    c0,c1,c2,c3,c4:=Explode(Coefficients(f));
    P3<R,S,T,U>:=ProjectiveSpace(BaseField(C),3);  // R=XZ, S=X^2, T=Y, U=Z^2
    QI:=Curve(P3, [T^2-c4*S^2-c3*R*S-c2*R^2-c1*R*U-c0*U^2, R^2-S*U]);
    ptsQI:=PointsQI(QI, 2*Bound : OnlyOne:=OnlyOne);
    ptsC := [PointSet(C,BaseRing(C))| ];
    for pt in ptsQI do 
      r,s,t,u:=Explode(Eltseq(pt));
      if not IsZero(u) then 
        Append( ~ptsC, C![r/u,t/u,1] );
      else
        Append( ~ptsC, C![1,t/s,r/s] );
      end if;
    end for;
    return ptsC;
  end if;

  P2 := PolynomialRing(BaseField(C),2);
  F := P2!( P2.2^Degree(f)*Evaluate(f, P2.1/P2.2) );
  pts := PointsOfDegreeH(F,Bound);
  return [C! Eltseq(pt) : pt in pts];
end intrinsic;
