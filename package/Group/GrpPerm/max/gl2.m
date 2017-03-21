freeze;

// Code to produce various decorations of L(n,q)
// Written by Derek Holt - 2002

MatToQ := function(A,q)
// raise every element of matrix A to q-th power
  B := MatrixAlgebra(BaseRing(A),Nrows(A))!0;
  for i in [1..Nrows(A)] do for j in [1..Ncols(A)] do
    B[i][j] := A[i][j]^q;
  end for; end for;
  return B;
end function;

GL2 := function(n,q)
// Extension of GL(n,q) by graph isomorphisms - degree is twice as large.
local G, gens, mat, G2;
  if n lt 3 then error "n must be at least 3 in GL2"; end if;
  G := GL(n,q);
  gens := [GL(2*n,q) | DirectSum(g,Transpose(g^-1)) : 
                        g in [G.i: i in [1..Ngens(G)]] ];
  mat := MatrixAlgebra(GF(q),2*n)!0;
  InsertBlock(~mat,Identity(G),1,n+1); InsertBlock(~mat,Identity(G),n+1,1);
  Append(~gens,mat);
  G2 := sub< GL(2*n,q) | gens >;
  AssertAttribute(G2,"Order",2*#G);
  return G2;
end function;

SL2 := function(n,q)
// Extension of SL(n,q) by graph isomorphisms - degree is twice as large.
local G, gens, mat, G2;
  if n lt 3 then error "n must be at least 3 in SL2"; end if;
  G := SL(n,q);
  gens := [GL(2*n,q) | DirectSum(g,Transpose(g^-1)) : 
                        g in [G.i: i in [1..Ngens(G)]] ];
  mat := MatrixAlgebra(GF(q),2*n)!0;
  InsertBlock(~mat,Identity(G),1,n+1); InsertBlock(~mat,Identity(G),n+1,1);
  Append(~gens,mat);
  G2 := sub< GL(2*n,q) | gens >;
  AssertAttribute(G2,"Order",2*#G);
  return G2;
end function;

GammaL := function(n,q)
  f := Factorisation(q);
  p := f[1][1]; e := f[1][2];
  X := GL(n,q);
  if e eq 1 then return X; end if;

  gens := [ GL(n*e,q) | ];

  for gen in [X.i : i in [1..Ngens(X)]] do
    Append(~gens, DiagonalJoin([ MatToQ(gen,p^j) : j in [0..e-1] ]) );
  end for;

  mat := MatrixAlgebra(GF(q),n*e)!0;
  for j in [1..e-1] do
    InsertBlock(~mat,Identity(X),(j-1)*n+1,j*n+1);
  end for;
  InsertBlock(~mat,Identity(X),(e-1)*n+1,1);
  Append(~gens,mat);
  
  return sub< GL(n*e,q) | gens >;
end function;

GammaL2 := function(n,q)
  f := Factorisation(q);
  p := f[1][1]; e := f[1][2];
  X := GL2(n,q);
  if e eq 1 then return X; end if;

  gens := [ GL(2*n*e,q) | ];

  for gen in [X.i : i in [1..Ngens(X)]] do
    Append(~gens, DiagonalJoin([ MatToQ(gen,p^j) : j in [0..e-1] ]) );
  end for;

  mat := MatrixAlgebra(GF(q),2*n*e)!0;
  for j in [1..e-1] do
    InsertBlock(~mat,Identity(X),(j-1)*2*n+1,j*2*n+1);
  end for;
  InsertBlock(~mat,Identity(X),(e-1)*2*n+1,1);
  Append(~gens,mat);
  
  return sub< GL(2*n*e,q) | gens >;
end function;

GU2 := function(n,q)
// Extension of GU(n,q) by frobenius isomorphism - degree is twice as large.
local G, gens, mat, G2;
  if n lt 3 then error "n must be at least 3 in GU2"; end if;
  G := GU(n,q);
  gens := [GL(2*n,q^2) | DirectSum(g,MatToQ(g,q)) : 
                        g in [G.i: i in [1..Ngens(G)]] ];
  mat := MatrixAlgebra(GF(q^2),2*n)!0;
  InsertBlock(~mat,Identity(G),1,n+1); InsertBlock(~mat,Identity(G),n+1,1);
  Append(~gens,mat);
  G2 := sub< GL(2*n,q^2) | gens >;
  AssertAttribute(G2,"Order",2*#G);
  return G2;
end function;

SU2 := function(n,q)
// Extension of SU(n,q) by frobenius isomorphism - degree is twice as large.
local G, gens, mat, G2;
  if n lt 3 then error "n must be at least 3 in SU2"; end if;
  G := SU(n,q);
  gens := [GL(2*n,q^2) | DirectSum(g,MatToQ(g,q)) :
                        g in [G.i: i in [1..Ngens(G)]] ];
  mat := MatrixAlgebra(GF(q^2),2*n)!0;
  InsertBlock(~mat,Identity(G),1,n+1); InsertBlock(~mat,Identity(G),n+1,1);
  Append(~gens,mat);
  G2 := sub< GL(2*n,q^2) | gens >;
  AssertAttribute(G2,"Order",2*#G);
  return G2;
end function;


GammaU := function(n,q)
  f := Factorisation(q);
  p := f[1][1]; e := f[1][2];
  X := GU(n,q);

  gens := [ GL(2*n*e,q^2) | ];

  for gen in [X.i : i in [1..Ngens(X)]] do
    Append(~gens, DiagonalJoin([ MatToQ(gen,p^j) : j in [0..2*e-1] ]) );
  end for;

  mat := MatrixAlgebra(GF(q^2),2*n*e)!0;
  for j in [1..2*e-1] do
    InsertBlock(~mat,Identity(X),(j-1)*n+1,j*n+1);
  end for;
  InsertBlock(~mat,Identity(X),(2*e-1)*n+1,1);
  Append(~gens,mat);
  
  return sub< GL(2*n*e,q^2) | gens >;
  
end function;

SigmaU := function(n,q)
  f := Factorisation(q);
  p := f[1][1]; e := f[1][2];
  X := SU(n,q);

  gens := [ GL(2*n*e,q^2) | ];

  for gen in [X.i : i in [1..Ngens(X)]] do
    Append(~gens, DiagonalJoin([ MatToQ(gen,p^j) : j in [0..2*e-1] ]) );
  end for;

  mat := MatrixAlgebra(GF(q^2),2*n*e)!0;
  for j in [1..2*e-1] do
    InsertBlock(~mat,Identity(X),(j-1)*n+1,j*n+1);
  end for;
  InsertBlock(~mat,Identity(X),(2*e-1)*n+1,1);
  Append(~gens,mat);
  
  return sub< GL(2*n*e,q^2) | gens >;
  
end function;

PGL2 := function(n,q)
// Extension of PGL(n,q) by graph isomorphisms - degree is twice as large.
  local G, V;
  if n lt 3 then error "n must be at least 3 in PGL2"; end if;
  G := GL2(n,q);
  V:=VectorSpace(G);
  return OrbitImage(G,sub<V|V.1>);
end function;

PSL2 := function(n,q)
// Extension of PGL(n,q) by graph isomorphisms - degree is twice as large.
  local G, V;
  if n lt 3 then error "n must be at least 3 in PSL2"; end if;
  G := SL2(n,q);
  V:=VectorSpace(G);
  return OrbitImage(G,sub<V|V.1>);
end function;

PGammaL2 := function(n,q)
//Extension of PGammaL by graph automorphism
  local p, np, w, F, G, ng, perms, perm, lv, V, v, vi, d, c, ct, g, gti,
        NF, VNO, Z;
  if n lt 3 then error "n must be at least 3 in PGammaL2"; end if;
  Z := Integers();
  p := Factorisation(q)[1][1];
  if p eq q then
    return PGL2(n,q);
  end if;
  np := (q^n - 1) div (q-1);
  F := GF(q); w := F.1; 
  G := GL(n,F);
  ng := Ngens(G);
  perms := [ [] : i in [1..ng+2] ];
  lv := w^(q-2);
  V := VectorSpace(G);
  NF := func < x | x eq 0 select 0 else Log(x)+1 >;
  VNO := function(v)
    local d, vv, vn;
    d := Depth(v);
    vv := v*v[d]^-1;
    vn := 1 + (q^(n-d) - 1) div (q-1) +
             &+ [Z|q^(n-i)*NF(vv[i]) : i in [d+1..n] ];
    return vn;
  end function;

  //loop through point and determine action of generators
  
  v := V!([0: i in [1..n-1]] cat [1]);
  d := n;
  ct := 1;
  while true do
    for i in [1..ng] do
      g := G.i; gti := Transpose(g^-1);
      perms[i][ct] := VNO(v^g);
      perms[i][ct+np] := VNO(v^gti)+np;
    end for;

    // field automorphism:
    vi := VNO(V![v[i]^p : i in [1..n]]);
    perms[ng+1][ct] := vi; perms[ng+1][ct+np] := vi+np;
    
    // graph automorphism:
    perms[ng+2][ct] := ct+np; perms[ng+2][ct+np] := ct;

    //move on to next vector
    ct +:= 1;
    c:=n;
    while c gt d and v[c] eq lv do v[c]:=0; c-:=1; end while;
    if c eq d then
      if d eq 1 then break; end if;
      v[d]:=0; d-:=1; v[d]:=1;
    else v[c] := v[c] eq 0 select 1 else v[c]*w;
    end if;
  end while;


  return sub< Sym(2*np) | perms >;
end function;

PGammaLD2 := function(q)
//This is a version of PGammaL2 in dimension 2, where we have no
//graph isomorphism, and the result has degree q+1 as normal.
//We need this because it allows us easily to set
//up a monomorphism GL(2,q) -> PGammaL(2,q).
  local p, np, w, F, G, ng, perms, perm, lv, V, v, vi, d, c, ct, g, gti,
        NF, VNO, Z;
  Z := Integers();
  p := Factorisation(q)[1][1];
  if p eq q then error "q must be a proper prime power in PGammaLD2"; end if;
  np := q + 1;
  F := GF(q); w := F.1; 
  G := GL(2,F);
  ng := Ngens(G);
  perms := [ [] : i in [1..ng+1] ];
  lv := w^(q-2);
  V := VectorSpace(G);
  NF := func < x | x eq 0 select 0 else Log(x)+1 >;
  VNO := function(v)
    local d, vv, vn;
    d := Depth(v);
    vv := v*v[d]^-1;
    vn := 1 + (q^(2-d) - 1) div (q-1) +
             &+ [Z|q^(2-i)*NF(vv[i]) : i in [d+1..2] ];
    return vn;
  end function;

  //loop through point and determine action of generators
  
  v := V!([0,1]);
  d := 2;
  ct := 1;
  while true do
    for i in [1..ng] do perms[i][ct] := VNO(v^G.i); end for;

    // field automorphism:
    vi := VNO(V![v[i]^p : i in [1..2]]);
    perms[ng+1][ct] := vi;

    //move on to next vector
    ct +:= 1;
    c:=2;
    while c gt d and v[c] eq lv do v[c]:=0; c-:=1; end while;
    if c eq d then
      if d eq 1 then break; end if;
      v[d]:=0; d-:=1; v[d]:=1;
    else v[c] := v[c] eq 0 select 1 else v[c]*w;
    end if;
  end while;

  return sub< Sym(np) | perms >;
end function;

ModToQ := function(M,q)
// same as MatToQ for GModule M
  local G;
  G := Group(M);
  return GModule(G,
        [ MatToQ(m,q): m in [ActionGenerator(M,i): i in [1..Ngens(G)]] ] );
end function;

GLT2 := function(n,q)
// Extension of GL(n,q^2) by twisted .2 - embeds in U(2*n,q)
local G, gens, mat, G2, A;
  G := GL(n,q^2);
  A := MatrixAlgebra(GF(q^2),n);
  gens := [GL(2*n,q^2) | DirectSum(g,MatToQ(A!Transpose(g^-1),q)) :
                        g in [G.i: i in [1..Ngens(G)]] ];
  mat := MatrixAlgebra(GF(q^2),2*n)!0;
  InsertBlock(~mat,Identity(G),1,n+1); InsertBlock(~mat,Identity(G),n+1,1);
  Append(~gens,mat);
  G2 := sub< GL(2*n,q^2) | gens >;
  AssertAttribute(G2,"Order",2*#G);
  return G2;
end function;

// Code to produce various decorations of Sp(n,q)

GSp := function(n,q)
// Extension of Sp(n,q) by diagonal isomorphism (and scalar matrices)
local G, w, m, o;
  G := Sp(n,q);
  if q mod 2 eq 0 then return G; end if;
  w := PrimitiveElement(GF(q));
  m := n div 2;
  o:=GL(n, q)!DiagonalMatrix([w:i in [1..m]] cat [1:i in [1..m]]);
  return sub<GL(n,q) | G.1, G.2, o >;
end function;

GammaSp := function(n,q)
//Extension of Sp(n,q) by diagonal isomorphism and field autos
  local f, p, e, w, m, o, X, gens, mat;
  assert IsEven(n);
  f := Factorisation(q);
  p := f[1][1]; e := f[1][2];
  if q mod 2 eq 0 then 
    X := Sp(n,q);
  else
    w := PrimitiveElement(GF(q));
    m := n div 2;
    o:=GL(n, q)!DiagonalMatrix([w:i in [1..m]] cat [1:i in [1..m]]);
    X := sub<GL(n,q) | Sp(n,q).1, Sp(n,q).2, o >;
  end if;

  gens := [ GL(n*e,q) | ];
  for gen in [X.i : i in [1..Ngens(X)]] do
    Append(~gens, DiagonalJoin([ MatToQ(gen,p^j) : j in [0..e-1] ]) );
  end for;

  mat := MatrixAlgebra(GF(q),n*e)!0;
  for j in [1..e-1] do
    InsertBlock(~mat,Identity(X),(j-1)*n+1,j*n+1);
  end for;
  InsertBlock(~mat,Identity(X),(e-1)*n+1,1);
  Append(~gens,mat);

  return sub< GL(n*e,q) | gens >;
end function;

GammaOPlus := function(n,q)
//Extension of GO+(n,q) by diagonal isomorphism and field autos
  local f, p, e, w, m, o, X, gens, mat;
  assert IsEven(n);
  f := Factorisation(q);
  p := f[1][1]; e := f[1][2];
  w := PrimitiveElement(GF(q));
  if q mod 2 eq 0 then 
    X := GOPlus(n,q);
  else
    m := n div 2;
    o:=GL(n, q)!DiagonalMatrix([w:i in [1..m]] cat [1:i in [1..m]]);
    X := sub<GL(n,q) | GOPlus(n,q), o >;
  end if;

  gens := [ GL(n*e,q) | ];
  for gen in [X.i : i in [1..Ngens(X)]] do
    Append(~gens, DiagonalJoin([ MatToQ(gen,p^j) : j in [0..e-1] ]) );
  end for;

  mat := MatrixAlgebra(GF(q),n*e)!0;
  for j in [1..e-1] do
    InsertBlock(~mat,Identity(X),(j-1)*n+1,j*n+1);
  end for;
  InsertBlock(~mat,Identity(X),(e-1)*n+1,1);
  Append(~gens,mat);

  return sub< GL(n*e,q) | gens >;
end function;

GammaOMinus := function(n,q)
//Extension of GO-(n,q) by diagonal isomorphism and field autos- this is harder
  local f, p, e, w, m, o, X, gens, mat;
  assert IsEven(n);
  f := Factorisation(q);
  p := f[1][1]; e := f[1][2];
  w := PrimitiveElement(GF(q));
  gom := GOMinus(n,q);
  if q mod 2 eq 0 then 
    X := gom;
  else
    AandB := function(q,z)
      //find elements of GF(q) with a^2+b^2=z.
      for b in GF(q) do
        bool, a:= IsSquare(z-GF(q)!b^2);
        if bool then return a, b; end if;
      end for;
      error "ERROR: couldn't find a and b in GF(", q, ")";
    end function;
    a,b := AandB(q,w);
    m := n div 2;
    o := n mod 4 eq 0 or (q-1) mod 4 eq 0 select
    DiagonalJoin( [Matrix(GF(q),2,2,[a,-b,b,a]):i in [1.. m-1]]
       cat [Matrix(GF(q),2,2,[0,-1,w,0])] ) else
    DiagonalJoin( [Matrix(GF(q),2,2,[a,-b,b,a]):i in [1.. m]]);
    isit, form := SymmetricBilinearForm(GOMinus(n,q));
    mat := CorrectForm(form, n, q, "orth-");
    o := GL(n,q)!(mat * o * mat^-1);
    X := sub<GL(n,q) | gom, o >;
  end if;

  //work out correcting matrix to follow field automorphism
  GC := sub< GL(n,q) | [ MatToQ(g,p) : g in [gom.i:i in [1..Ngens(gom)]]] >;
  cmat := TransformForm(GC);
  //identify (gal*cmat)^e
  gensc1:=[]; gensc2:=[];
  for i in [1..Ngens(gom)] do
    g := gom.i;
    for i in [1..e-1] do
      g := cmat^-1 * MatToQ(g,p) * cmat;
    end for;
    Append(~gensc1, g);
    g := gom.i;
    g := MatToQ(cmat * g * cmat^-1, p^(e-1));
    Append(~gensc2, g);
  end for;
  M1:=GModule(gensc1); M2:=GModule(gom, gensc2);
  isit, mate := IsIsomorphic(M1,M2); assert isit;

  gens := [ GL(n*e,q) | ];
  for gen in [X.i : i in [1..Ngens(X)]] do
    comps := [GL(n,q) | gen];
    for i in [2..e] do
       comps[i] := cmat^-1 * MatToQ(comps[i-1],p) * cmat;
    end for;
    Append(~gens, DiagonalJoin( comps ) );
  end for;

  mat := MatrixAlgebra(GF(q),n*e)!0;
  for j in [1..e-1] do
    InsertBlock(~mat,Identity(X),(j-1)*n+1,j*n+1);
  end for;
  InsertBlock(~mat,mate,(e-1)*n+1,1);
  Append(~gens,mat);

  return sub< GL(n*e,q) | gens >, cmat;
end function;

PGSp := function(n,q)
// Extension of PSp(n,q) by diagonal isomorphism
  local G, V;
  G := GSp(n,q);
  V:=VectorSpace(G);
  return OrbitImage(G,sub<V|V.1>);
end function;

PGammaSp := function(n,q)
//Extension of PGSp by field automorphism
  local p, np, w, F, G, ng, perms, perm, lv, V, v, vi, d, c, ct, g, gti,
        NF, VNO, Z;
  Z := Integers();
  p := Factorisation(q)[1][1];
  if p eq q then
    return PGSp(n,q);
  end if;
  np := (q^n - 1) div (q-1);
  F := GF(q); w := F.1; 
  G := GSp(n,q);
  ng := Ngens(G);
  perms := [ [] : i in [1..ng+1] ];
  lv := w^(q-2);
  V := VectorSpace(G);
  NF := func < x | x eq 0 select 0 else Log(x)+1 >;
  VNO := function(v)
    local d, vv, vn;
    d := Depth(v);
    vv := v*v[d]^-1;
    vn := 1 + (q^(n-d) - 1) div (q-1) +
             &+ [Z|q^(n-i)*NF(vv[i]) : i in [d+1..n] ];
    return vn;
  end function;

  //loop through point and determine action of generators
  
  v := V!([0: i in [1..n-1]] cat [1]);
  d := n;
  ct := 1;
  while true do
    for i in [1..ng] do
      g := G.i;
      perms[i][ct] := VNO(v^g);
    end for;
    // field automorphism:
    vi := VNO(V![v[i]^p : i in [1..n]]);
    perms[ng+1][ct] := vi;
    
    //move on to next vector
    ct +:= 1;
    c:=n;
    while c gt d and v[c] eq lv do v[c]:=0; c-:=1; end while;
    if c eq d then
      if d eq 1 then break; end if;
      v[d]:=0; d-:=1; v[d]:=1;
    else v[c] := v[c] eq 0 select 1 else v[c]*w;
    end if;
  end while;

  return sub< Sym(np) | perms >;
end function;

AutSp4 := function(q)
// Full automorphism group of PSp(4,q) for q=2^e.
// Socle quotient is cyclic, and it has PSigmaSp(4,q) with index 2.
  local K, X, w, diag, gens, imgens, G, act, im, id, h, h2, sp2rep, im2, d,
        S, op2, isc, g, x, op, j;

  assert q mod 2 eq 0;
  fac:=Factorisation(q);
  e := fac[1][2];
  K:=GF(q);
  X:=GL(4,q);
  w := PrimitiveElement(K);
  diag := [<i,i,1> : i in [1..4]];
  //make Chevalley generators of Sp(4,q)
  gens := [
  X!Matrix(K,4,4,diag cat [<1,2,w>, <3,4,-w>]),  //a
  X!Matrix(K,4,4,diag cat [<4,3,-w>, <2,1,w>]),  //-a
  X!Matrix(K,4,4,diag cat [<1,3,w>, <2,4,w>]), //a+b
  X!Matrix(K,4,4,diag cat [<4,2,w>, <3,1,w>]),//-a-b
  X!Matrix(K,4,4,diag cat [<1,4,w>]), //2a+b
  X!Matrix(K,4,4,diag cat [<4,1,w>]), //-2a-b
  X!Matrix(K,4,4,diag cat [<2,3,w>]), //b
  X!Matrix(K,4,4,diag cat [<3,2,w>]) //-b
  ];
  
  //images under graph automorphism (q even)
  imgens := [
  X!Matrix(K,4,4,diag cat [<2,3,w^2>]), //b
  X!Matrix(K,4,4,diag cat [<3,2,w^2>]), //-b
  X!Matrix(K,4,4,diag cat [<1,4,w^2>]), //2a+b
  X!Matrix(K,4,4,diag cat [<4,1,w^2>]), //-2a-b
  X!Matrix(K,4,4,diag cat [<1,3,w>, <2,4,w>]), //a+b
  X!Matrix(K,4,4,diag cat [<4,2,w>, <3,1,w>]),//-a-b
  X!Matrix(K,4,4,diag cat [<1,2,w>, <3,4,-w>]),  //a
  X!Matrix(K,4,4,diag cat [<4,3,-w>, <2,1,w>])  //-a
  ];

  agens := [ GL(8*e,q) | ];
  for i in [1..#gens] do
    comps := [ X | gens[i], imgens[i] ];
    for j in [1..e-1] do
       comps[2*j+1] :=  MatToQ(comps[2*j-1], 2);
       comps[2*j+2] :=  MatToQ(comps[2*j], 2);
    end for;
    Append(~agens, DiagonalJoin(comps) );
  end for;

  mat := MatrixAlgebra(GF(q),8*e)!0;
  for j in [1..2*e-1] do
    InsertBlock(~mat,Identity(X),(j-1)*4+1,j*4+1);
  end for;
  InsertBlock(~mat,Identity(X),(2*e-1)*4+1,1);
  Append(~agens,mat);

  return sub< GL(8*e,q) | agens >;
end function;


AutPSp4 := function(q)
// Full automorphism group of PSp(4,q) for q=2^e.
// Socle quotient is cyclic, and it has PSigmaSp(4,q) with index 2.
  local K, X, w, diag, gens, imgens, G, act, im, id, h, h2, sp2rep, im2, d,
        S, op2, isc, g, x, op, j;

  assert q mod 2 eq 0;
  K:=GF(q);
  X:=GL(4,q);
  w := PrimitiveElement(K);
  diag := [<i,i,1> : i in [1..4]];
  //make Chevalley generators of Sp(4,q)
  gens := [
  X!Matrix(K,4,4,diag cat [<1,2,w>, <3,4,-w>]),  //a
  X!Matrix(K,4,4,diag cat [<4,3,-w>, <2,1,w>]),  //-a
  X!Matrix(K,4,4,diag cat [<1,3,w>, <2,4,w>]), //a+b
  X!Matrix(K,4,4,diag cat [<4,2,w>, <3,1,w>]),//-a-b
  X!Matrix(K,4,4,diag cat [<1,4,w>]), //2a+b
  X!Matrix(K,4,4,diag cat [<4,1,w>]), //-2a-b
  X!Matrix(K,4,4,diag cat [<2,3,w>]), //b
  X!Matrix(K,4,4,diag cat [<3,2,w>]) //-b
  ];
  
  //images under graph automorphism (q even)
  imgens := [
  X!Matrix(K,4,4,diag cat [<2,3,w^2>]), //b
  X!Matrix(K,4,4,diag cat [<3,2,w^2>]), //-b
  X!Matrix(K,4,4,diag cat [<1,4,w^2>]), //2a+b
  X!Matrix(K,4,4,diag cat [<4,1,w^2>]), //-2a-b
  X!Matrix(K,4,4,diag cat [<1,3,w>, <2,4,w>]), //a+b
  X!Matrix(K,4,4,diag cat [<4,2,w>, <3,1,w>]),//-a-b
  X!Matrix(K,4,4,diag cat [<1,2,w>, <3,4,-w>]),  //a
  X!Matrix(K,4,4,diag cat [<4,3,-w>, <2,1,w>])  //-a
  ];
  
  G := sub< GL(4,q) | gens >; //Sp(4,q)
  act,im := OrbitAction(G,sub<RSpace(K,4)|[1,0,0,0]>);
  id:=hom<im->im | [im.i : i in [1..Ngens(im)]] >;
  h:=hom<im->im | [act(i): i in imgens] >;
  h2:=h^2;
  //make PSp(4,q).2 as permutation group with normal gens of PSp first
  sp2rep := RepresentationSum(im, [id, h] );
  im2 := Image(sp2rep);
  d := Degree(im);
  //construct permutation op inducing outer automorphism
  //first get action of op^2 on [1..d]
  S := Stabiliser(im,1);
  x := Random(S);
  while #Fix(x) gt 1 do x := Random(S); end while;
  op2 := [];
  for i in [1..d] do
    isc,g := IsConjugate(im,1,i);
    op2[i] := Representative(Fix((x^g)@h2));
  end for;
  op := [];
  for i in [1..d] do
    isc,g := IsConjugate(im,1,i);
    j := d + 1^(g @ h2);
    op[i] := j;
    op[j] := op2[i];
  end for;
  op := Sym(2*d)!op;
    
  return
    sub< Sym(2*d) | [ (Sp(4,q).i) @ act @ sp2rep : i in [1,2] ] cat [op] >;

end function;

intrinsic AutPSp(n::RngIntElt, q::RngIntElt) -> GrpPerm
{The full automorphism group of PSp(n,q)};
    require n ge 4 and IsEven(n):"First argument must be even and >= 4";
    require q ge 2 :"Second argument must be a finite field size";
    fl, p, k := IsPrimePower(q);
    require fl:"Second argument must be a finite field size";
    if IsOdd(p) then
	if k eq 1 then
	    return PGSp(n,q);
	else 
	    return PGammaSp(n,q);
	end if;
    else
	if n eq 4 then
	    return AutPSp4(q);
	else
	    return PGammaSp(n,q);
	end if;
    end if;
end intrinsic;
