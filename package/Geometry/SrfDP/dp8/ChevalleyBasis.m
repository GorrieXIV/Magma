freeze;
//  ######################################################
//  ##  Chevalley basis of an algebra L over Q
//  ##  isomorphic to sl2(Q)
//  ##  algorithm: reduction to Cremona-Simon algorithm
//  ##  for finding a rational point on a conic
//  ##    W. A. de Graaf & J. Pilnikova.
//  ######################################################
intrinsic FindChevalleyBasisDiagonal(L::AlgLie) -> 
  AlgLieElt, AlgLieElt, AlgLieElt
{ find a Chevalley basis of sl2 over rationals by finding
  a rational point on a conic in diagonal shape}

  //  Chevalley basis of sl2 in the representation
  //  wrt. the "standard conic":
  //  (the curve x*z-y^2, i.e. parametrized by (s^2:st:t^2)):
  X := Matrix(Rationals(),3,3,[0,2,0, 0,0,1, 0,0,0]);
  Y := Matrix(Rationals(),3,3,[0,0,0, 1,0,0, 0,2,0]);
  H := Matrix(Rationals(),3,3,[2,0,0, 0,0,0, 0,0,-2]);

  CS := CartanSubalgebra(L);

  //  whether CS is is split
  mp := MinimalPolynomial(L ! CS.1);
  fac := [ u[1] : u in Factorization(mp) ];
  splits := true;
  for i := 1 to #fac do
     if Degree(fac[i]) gt 1 then
       splits := false;
       break i;
     end if;
  end for;

  if splits then 
    xx, yy, hh := ChevalleyBasis(L);
    return xx[1], yy[1], -hh[1];
  end if;


  h := L ! CS.1;
  x := h * L.1;
  if IsZero(x) then x := h * L.2; end if;
  y := h * x;

  //  now the multiplication table wrt basis 
  //  x,y,h looks as follows:
  //    [h,x] = y
  //    [h,y] = a*x
  //    [x,y] = b*h
  //  need to find a, b

  hy := h * y;
  cn := Eltseq(L ! hy);
  cd := Eltseq(L ! x);
  if cn[1] eq 0 then
    if cn[2] eq 0 then
      a := cn[3]/cd[3];
    else
      a := cn[2]/cd[2];
    end if;
  else
    a := cn[1]/cd[1];
  end if;

  xy := x * y;
  cn := Eltseq(L ! xy);
  cd := Eltseq(L ! h);
  if cn[1] eq 0 then
    if cn[2] eq 0 then
      b := cn[3]/cd[3];
    else
      b := cn[2]/cd[2];
    end if;
  else
    b := cn[1]/cd[1];
  end if;

  //  the Lie algebra L is the Lie algebra of the 
  //  following conic:
  //  -b*x^2 + a*b*y^2 + a*z^2
  //  it has 3x3 representation:
  Hm := Hom(VectorSpace(Rationals(),3), VectorSpace(Rationals(),3));

  xrep := Hm ! [0,0,0, 0,0,-1, 0,b,0];
  yrep := Hm ! [0,0,-a, 0,0,0, -b,0,0];
  hrep := Hm ! [0,a,0, 1,0,0, 0,0,0];

  Lrep := KMatrixSpaceWithBasis([xrep,yrep,hrep]);

  P2<xc,yc,zc> := ProjectivePlane(Rationals());
  C := Conic(P2, -b*xc^2 + a*b*yc^2 + a*zc^2);
  vprintf ParamDP: "Solving the conic: %o\n", C;
  vtime ParamDP: bool, pt := HasRationalPoint(C);


  if not bool then
    return L!0, L!0, L!0;
  end if;

  //  for the conic A*x^2 + B*y^2 + C*y^2 
  //  with the point (xx : yy : zz) on it
  //  M gives a parametrization of the conic:
  //    x         s^2
  //    y  =  M * s*t
  //    z         t^2
  //  where M is the following matrix
  //  if zz is non-zero: [  A*xx  2*B*yy -B*xx 
  //                       -A*yy  2*A*xx  B*yy 
  //                        A*zz  0       B*zz]
  //  or
  //  if yy is non-zero: [  A*xx  2*C*zz -C*xx
  //                        A*yy  0       C*yy
  //                       -A*zz  2*A*xx  C*zz
  //  
  //  (I have the feeling Cremona-Simon always finds a solution
  //   with zz nonzero, but who knows...)

  if (pt[3] ne 0) then
    M := Matrix(Rationals(),3,3,
      [ -b*pt[1],  2*a*b*pt[2], -a*b*pt[1], 
         b*pt[2],  -2*b*pt[1],  a*b*pt[2], 
        -b*pt[3],  0,           a*b*pt[3] ]);
  else
    M := Matrix(Rationals(),3,3,
      [ -b*pt[1],  2*a*pt[3], -a*pt[1],
        -b*pt[2],  0,          a*pt[2],
         b*pt[3], -2*b*pt[1],  a*pt[3]]);
  end if;
  rM := M^-1;
    
  //  ##  test the parametrizaion of the conic - to be omitted later
  //  R<s,t> := PolynomialRing(Rationals(), 2);
  //  xcor := M[1][1]*s^2 + M[1][2]*s*t + M[1][3]*t^2;
  //  ycor := M[2][1]*s^2 + M[2][2]*s*t + M[2][3]*t^2;
  //  zcor := M[3][1]*s^2 + M[3][2]*s*t + M[3][3]*t^2;
  //  check := -b*xcor^2 + a*b*ycor^2 + a*zcor^2;
  //  if (check eq 0) then
  //    print("parametrization ok");
  //  else
  //    print("bad parametrization of the conic!");
  //  end if;
  //  ##  end of the test

  Xrep := Hm ! M * X * rM;
  Yrep := Hm ! M * Y * rM;
  Hrep := Hm ! M * H * rM;

  c := Coordinates(Lrep, Xrep);
  ChX := c[1]*x + c[2]*y + c[3]*h;
  c := Coordinates(Lrep, Yrep);
  ChY := c[1]*x + c[2]*y + c[3]*h;
  c := Coordinates(Lrep, Hrep);
  ChH := c[1]*x + c[2]*y + c[3]*h;

  return ChX, ChY, ChH;

end intrinsic;


//  ######################################################
//  ##  Chevalley basis of an algebra L over Q
//  ##  isomorphic to sl2(Q)
//  ##  algorithm: reduction to Cremona-Simon algorithm
//  ##  for finding a rational point on a conic
//  ######################################################
//  ##  like the previous function, just the conic is not
//  ##  constructed in the diagonal form
//  ######################################################
intrinsic FindChevalleyBasis(L::AlgLie) -> 
  AlgLieElt, AlgLieElt, AlgLieElt
{ find a Chevalley basis of sl2 over rationals() by finding
  a rational point on a conic}

  //  Chevalley basis of sl2 in the representation
  //  wrt. the "standard conic":
  //  (the curve x*z-y^2, i.e. parametrized by (s^2:st:t^2)):
  X := Matrix(Rationals(),3,3,[0,2,0, 0,0,1, 0,0,0]);
  Y := Matrix(Rationals(),3,3,[0,0,0, 1,0,0, 0,2,0]);
  H := Matrix(Rationals(),3,3,[2,0,0, 0,0,0, 0,0,-2]);

  CS := CartanSubalgebra(L);

  //  whether CS is is split
  mp := MinimalPolynomial(L ! CS.1);
  fac := [ u[1] : u in Factorization(mp) ];
  splits := true;
  for i := 1 to #fac do
     if Degree(fac[i]) gt 1 then
       splits := false;
       break i;
     end if;
  end for;

  if splits then 
    xx, yy, hh := ChevalleyBasis(L);
    return xx[1], yy[1], -hh[1];
  end if;


  S := ZeroMatrix(Rationals(), 18, 6);
  M3 := MatrixAlgebra(Rationals(), 3);
  Brep := [ M3 | ];
  for i := 1 to 3 do
    B := -Transpose(M3 ! AdjointMatrix(L, Basis(L)[i]));
    Brep[i] := B;

    j := 1+6*(i-1);
    //  order of the variables :
    //  a11, a12, a13, a22, a23, a33
    S[j][1] := B[1][1]; S[j][2] := B[2][1]; S[j][3] := B[3][1];
    j +:= 1;
    S[j][2] := B[1][2]; S[j][4] := B[2][2]; S[j][5] := B[3][2];
    j +:= 1;
    S[j][3] := B[1][3]; S[j][5] := B[2][3]; S[j][6] := B[3][3];
    j +:= 1;
    S[j][1] := B[1][2]; S[j][2] := B[2][2]; S[j][3] := B[3][2];
    S[j][2] +:= B[1][1]; S[j][4] := B[2][1]; S[j][5] := B[3][1];
    j +:= 1;
    S[j][1] := B[1][3]; S[j][2] := B[2][3]; S[j][3] := B[3][3];
    S[j][3] +:= B[1][1]; S[j][5] := B[2][1]; S[j][6] := B[3][1];
    j +:= 1;
    S[j][2] := B[1][3]; S[j][4] := B[2][3]; S[j][5] := B[3][3];
    S[j][3] := B[1][2]; S[j][5] +:= B[2][2]; S[j][6] := B[3][2];
  end for;
  NS := NullSpace(Transpose(S));
  b := Basis(NS)[1];
  A := Matrix(Rationals(), 3,3, 
       [b[1],b[2],b[3], b[2],b[4],b[5], b[3],b[5],b[6]]);


  Hm := Hom(VectorSpace(Rationals(),3), VectorSpace(Rationals(),3));

  b1rep := Hm ! Brep[1];
  b2rep := Hm ! Brep[2];
  b3rep := Hm ! Brep[3];

  Lrep := KMatrixSpaceWithBasis([b1rep,b2rep,b3rep]);

  P2<xc,yc,zc> := ProjectivePlane(Rationals());
  C := Conic(P2, b[1]*xc^2 + 2*b[2]*xc*yc + 2*b[3]*xc*zc + 
                 b[4]*yc^2 + 2*b[5]*yc*zc + b[6]*zc^2);
  vprintf ParamDP: "Solving the conic: %o\n", C;
  vtime ParamDP: bool, pt := HasRationalPoint(C);

  if not bool then
    return L!0, L!0, L!0;
  end if;

  //  for the conic 
  //    a11*x^2 + 2*a12*x*y + 2*a13*x*z + a22*y^2 + 2*a23*y*z + a33*z^2 
  //  with the point (xx : yy : zz) on it
  //  M gives a parametrization of the conic:
  //    x         s^2
  //    y  =  M * s*t
  //    z         t^2
  //  where M is the following matrix
  //  if zz is non-zero: 
  //    [  a11*xx+2*a12*yy+2*a13*zz  2*a22*yy+2*a23*zz  -a22*xx 
  //       -a11*yy  2*a11*xx+2*a13*zz  2*a12*xx+a22*yy+2*a23*zz 
  //       -a11*zz  -2*a12*zz  -a22**zz  ]
  //  or if yy is non-zero:
  //    [  a11*xx+2*a12*yy+2*a13*zz  2*a23*yy+2*a33*zz -a33*xx
  //       -a11*yy  -2*a13*yy  -a33*yy
  //       -a11*zz  2*a11*xx+2*a12*yy  2*a13*xx+2*a23*yy+a33*zz  ]
  //  or if xx is non-zero:
  //    [  -a22*xx  -2*a23*xx  -a33*xx
  //       2*a12*xx+a22*yy+2*a23*zz  2*a13*xx+2*a33*zz  -a33*yy
  //       -a22*zz  2*a12*xx+2*a22*yy  2*a13*xx+2*a23*yy+a33*zz  ]

  if (pt[3] ne 0) then
    M := Matrix(Rationals(),3,3,
      [ b[1]*pt[1] + 2*b[2]*pt[2] + 2*b[3]*pt[3],  
            2*b[4]*pt[2] + 2*b[5]*pt[3], 
            -b[4]*pt[1], 
        -b[1]*pt[2],  
            2*b[1]*pt[1] + 2*b[3]*pt[3],  
            2*b[2]*pt[1] + b[4]*pt[2] + 2*b[5]*pt[3], 
        -b[1]*pt[3], -2*b[2]*pt[3], -b[4]*pt[3] ]);
  elif (pt[2] ne 0) then
    M := Matrix(Rationals(),3,3,
      [ b[1]*pt[1] + 2*b[2]*pt[2] + 2*b[3]*pt[3],  
            2*b[5]*pt[2] + 2*b[6]*pt[3], 
            -b[6]*pt[1],
        -b[1]*pt[2], -2*b[3]*pt[2], -b[6]*pt[2], 
        -b[1]*pt[3], 
            2*b[1]*pt[1] + 2*b[2]*pt[2], 
            2*b[3]*pt[1] + 2*b[5]*pt[2] + b[6]*pt[3]]);
  else 
    M := Matrix(Rationals(),3,3,
      [ -b[4]*pt[1], -2*b[5]*pt[1], -b[6]*pt[1],
            2*b[2]*pt[1] + b[4]*pt[2] + 2*b[5]*pt[3], 
            2*b[3]*pt[1] + 2*b[6]*pt[3],
            -b[6]*pt[2],
        -b[4]*pt[3],
            2*b[2]*pt[1] + 2*b[4]*pt[2],
            2*b[3]*pt[1] + 2*b[5]*pt[2] + b[6]*pt[3]]);
  end if;
  rM := M^-1;
    
  //  ##  test the parametrizaion of the conic - to be omitted later
  //  R<s,t> := PolynomialRing(Rationals(), 2);
  //  xcor := M[1][1]*s^2 + M[1][2]*s*t + M[1][3]*t^2;
  //  ycor := M[2][1]*s^2 + M[2][2]*s*t + M[2][3]*t^2;
  //  zcor := M[3][1]*s^2 + M[3][2]*s*t + M[3][3]*t^2;
  //  check := b[1]*xcor^2 + 2*b[2]*xcor*ycor+ 2*b[3]*xcor*zcor + 
  //           b[4]*ycor^2 + 2*b[5]*ycor*zcor + b[6]*zcor^2;
  //  if (check eq 0) then
  //    print("parametrization ok");
  //  else
  //    print("bad parametrization of the conic!");
  //  end if;
  //  ##  end of the test

  Xrep := Hm ! M * X * rM;
  Yrep := Hm ! M * Y * rM;
  Hrep := Hm ! M * H * rM;

  c := Coordinates(Lrep, Xrep);
  ChX := &+[c[k]*Basis(L)[k] : k in [1..3]];
  c := Coordinates(Lrep, Yrep);
  ChY := &+[c[k]*Basis(L)[k] : k in [1..3]];
  c := Coordinates(Lrep, Hrep);
  ChH := &+[c[k]*Basis(L)[k] : k in [1..3]];


  return ChX, ChY, ChH;

end intrinsic;

