freeze;

import "spin8m.m": Spin8Minus;
import "orthreds.m": NonDegenStabOmega, IsotropicStabOmega;
import "classicals.m": SOMinusOmega, GOMinusSO, NormGOMinusGO;
import "spinor.m": InOmega;
import "reds.m": GLStabOfNSpace;
import "imp_and_gamma.m" : GammaL1;
import "superfield.m" : BlockPowers, MatToQ;

TwoOminus8 := function(q)
/* 2.O^-(8,q) as C9-subgroup of O^+(8,q^2) */
  local G;
  G := Spin8Minus(q);
  G := ActionGroup(Constituents(GModule(G))[1]);
  return G^TransformForm(G);
end function;

TwoO7 := function(q)
/* 2.O^7(q) as C9-subgroup of O^+(8,q) */
  local G;
  G := Spin8Minus(q);
  G := ActionGroup(Constituents(GModule(G))[1]);
  H := q eq 2 select sub< G | G.1*G.5, G.3, G.4, G.6 >
                else sub< G | G.1*G.5, G.3, G.4, G.6, G.7 >;
  t, H := IsOverSmallerField(H); assert t;
  return H^TransformForm(H);
end function;

MatrixTensorFactors := function(A,m,n)
/* A should be an (mn) x (mn) matrix of form KroneckerProduct(B,C),
 * for mxm and nxn matrices B,C. Return B,C (up to multiplication by scalar).
 */
 local K, B, C, haveC, BC, ni, nj, fac;
 K := BaseRing(A);
 B := ZeroMatrix(K,m,m);
 C := ZeroMatrix(K,n,n);
 haveC := false;
 ni:=0; nj:=0; fac:=0;
 for i in [1..m] do for j in [1..m] do
   BC := ExtractBlock(A,(i-1)*n+1, (j-1)*n+1,n,n);
   if haveC then
     B[i][j] := BC[ni][nj] * fac;
   elif BC ne ZeroMatrix(K,n,n) then
     C := BC;
     haveC := true;
     for k in [1..n] do for l in [1..n] do
       if C[k][l] ne 0 then
          ni:=k; nj:=l; fac:=C[k][l]^-1;
          break k;
       end if;
     end for; end for;
     B[i][j] := BC[ni][nj] * fac;
   end if;
 end for; end for;

 assert A eq KroneckerProduct(B,C);
 return B,C;
end function;

O8qMapToCover := function(q)
/* return map from Magma rep of O^-(8,q) to 2.O^-(8,q) over GF(q^2), q odd.
 * may be wrong by scalar factor -1, but correct on elements of odd order.
 */
  local G, G1, G2, C, ng, T, AT, ATtoG1, isf, form, formi, CT, M8, M56,
        imM8, imM56, trans64, G8, G8g, inds, SG8, M8g, M8b, isit, M8btoM8,
        TT, M28, imM28, V, extbas, trans28, trans28i, M28g, M56b, imM56b,
        trans56, trans56i, M56bg, M56btoM56, SG8toG1, G56, SG56, SM56, gh;
  assert IsOdd(q);
  G := Spin8Minus(q);
  C := Constituents(GModule(G));
  G1 := ActionGroup(C[1]); //domain of returned map
  G2 := ActionGroup(C[2]);
  ng := Ngens(G);
  //form tensor product of two 8-dimensional modules
  T := GModule(G, [KroneckerProduct(G1.i,G2.i): i in [1..ng]] );
  AT := ActionGroup(T);
  //first construct map from AT to G1
  isf, form := SymmetricBilinearForm(G1); assert isf;
  formi := form^-1;
  ATtoG1 := function(m)
    local x,y,mum,mu;
    x,y := MatrixTensorFactors(m,8,8);
    //x should fix form mod scalars
    formx := x * form * Transpose(x);
    mum := formx * formi^-1; 
    mu := mum[1][1]; assert mum eq ScalarMatrix(8,mu);
    x *:= ScalarMatrix(8, SquareRoot(mu^-1));
    if IsOdd(Order(m)) and IsEven(Order(x)) then
      x *:= ScalarMatrix(8, -1);
    end if;
    return x;
  end function;

  MT := MinimalSubmodules(T);
  M8 := [ m : m in MT | Dimension(m) eq 8 ][1];
  M56 := [ m : m in MT | Dimension(m) eq 56 ][1];
  imM8 := Morphism(M8,T);
  imM56 := Morphism(M56,T);
  trans64 := Matrix( [imM8[i] : i in [1..8]] cat [imM56[i] : i in [1..56]] );
  
  //Need horrible hack to deal with case when some action generators
  //of M8 are trivial or equal.
  G8 := ActionGroup(M8);
  G8g := [ MatrixAlgebra(GF(q^2),8) | G8.i : i in [1..Ngens(G8)]];
  inds := [ ag eq IdentityMatrix(GF(q^2),8) select 0 else Position(G8g,ag)
                    where ag := ActionGenerator(M8,i) : i in [1..ng]];
  isf, SG8 := IsOverSmallerField(G8); assert isf;
  SG8 := SG8^TransformForm(SG8); //should not be standard copy of O^-(8,q);
  M8g := [ MatrixAlgebra(GF(q^2),8) |
            inds[i] eq 0 select IdentityMatrix(GF(q^2),8) else SG8.inds[i] :
             i in [1..ng]];
  M8b := GModule(G, M8g);
  isit, M8btoM8 := IsIsomorphic(M8b, M8); assert isit;
  //more efficient to go back to working over GF(q)
  M8g := [ MatrixAlgebra(GF(q),8) |
            inds[i] eq 0 select IdentityMatrix(GF(q),8) else SG8.inds[i] :
             i in [1..ng]];

  //Our next aim is to construct the homomorphism SG8 -> SG56
  //We construct SG56 from SG8 in following.
  TT := GModule(G, [KroneckerProduct(M8g[i],M8g[i]): i in [1..ng]] );
  CT := Constituents(TT);
  M28 := [ c : c in CT | Dimension(c) eq 28 ][1];
  M28 := MinimalSubmodules(TT, M28)[1];
  imM28 := Morphism(M28,TT);
  V:=VectorSpace(GF(q),64);
  extbas := Matrix(ExtendBasis( [ V!imM28[i] : i in [1..28]], V));
  trans28 := ExtractBlock(extbas,1,1,28,64);
  trans28i := ExtractBlock(extbas^-1,1,1,64,28);
  // Get from element g in SG8 to element in action group of M28 by
  // g -> trans28 * KroneckerProduct(g,g) * trans28i
  // and extracting  
  M28g := [ ActionGenerator(M28,i): i in [1..ng]];
  TT := GModule(G, [KroneckerProduct(M8g[i],M28g[i]): i in [1..ng]] );
  //get 56-dimensional module M56 over GF(q)
  G56 := ActionGroup(M56);
  isf, SG56 := IsOverSmallerField(G56); assert isf;
  SM56 := GModule(G, 
      [ MatrixAlgebra(GF(q),56) |
            inds[i] eq 0 select IdentityMatrix(GF(q),56) else SG56.inds[i] :
             i in [1..ng]] );
  gh := GHom(SM56,TT);
  //time CT := Constituents(TT);
  //M56b := [ c : c in CT | Dimension(c) eq 56 ][1];
  //time M56b := MinimalSubmodules(TT, M56b)[1];
  M56b := Image(gh.1);
  imM56 := Morphism(M56b,TT);
  V:=VectorSpace(GF(q),224);
  extbas := Matrix(ExtendBasis( [ V!imM56[i] : i in [1..56]], V));
  trans56 := ExtractBlock(extbas,1,1,56,224);
  trans56i := ExtractBlock(extbas^-1,1,1,224,56);
  // Get from element g in G8 mapping to gg in action group of M28
  // to action group of M56 by
  // g -> trans56 * KroneckerProduct(g,gg) * trans56i; 

  //now need to get M56b back over to GF(q^2)
  M56bg := [ MatrixAlgebra(GF(q^2),56) | ActionGenerator(M56b,i): i in [1..ng]];
  M56b := GModule(G, M56bg);
  isit, M56btoM56 := IsIsomorphic(M56b, M56); assert isit;

  //Now we are ready to define the required map!
  SG8toG1 := function(g) //g in SG8 = Omega^-(8,q)
    local gg, ggg, m64;
    gg := trans28 * KroneckerProduct(g,g) * trans28i;
    ggg := trans56 * KroneckerProduct(g,gg) * trans56i;
    g := MatrixAlgebra(GF(q^2),8)!g;
    ggg := MatrixAlgebra(GF(q^2),56)!ggg;
    m64 :=
       DiagonalJoin(M8btoM8^-1 * g * M8btoM8, M56btoM56^-1 * ggg * M56btoM56);
    m64 := trans64^-1 * m64 * trans64;
    return ATtoG1(m64);
  end function;

  return SG8toG1;
end function;

TwoO72 := function(q)
/* 2.O^7(q).2 as C9-subgroup of normaliser in GL(8,q) of O^+(8,q) */
  local H, phi;
  H := NonDegenStabOmega(8,q,-1,7,0);
  phi := O8qMapToCover(q);
  H := sub< GL(8,q^2) | [ phi(H.i): i in [1..Ngens(H)]] >;
  t, H := IsOverSmallerField(H:Scalars:=true); assert t;
  H := H^TransformForm(H:Scalars:=true);
  return sub< GL(8,q) | H, ScalarMatrix(8, PrimitiveElement(GF(q))) >;
end function;

TwoOminus82 := function(q)
/* 2.O^-(8,q).2 as C9-subgroup of normaliser in GL(8,q^2) of O^+(8,q^2) */
  local go, ngo, G;
  go := GOMinusSO(8,q,-1);
  ngo := NormGOMinusGO(8,q,-1);
  G := OmegaMinus(8,q);
  //need generating set of odd order elements
  repeat
    g := Random(G);
    f := Factorisation(Order(g));
  until #f gt 1 or (#f eq 1 and f[1][1] ne 2);
  if f[1][1] eq 2 then
    g := g^(2^f[1][2]);
  end if;
  H := sub< GL(8,q) | g, g^Random(G) >;
  while not IsAbsolutelyIrreducible(H) do
    H := sub< GL(8,q) | H, g^Random(G) >;
  end while;
  while not RecogniseClassical(H) do
    H := sub< GL(8,q) | H, g^Random(G) >;
  end while;
  Hg := [ H.i : i in [1..Ngens(H)] ];
  Hgc := [ h^ngo : h in Hg ];

  //now map over to 2.O^-(8,q) in GO^+(8,q^2)
  phi := O8qMapToCover(q);
  Hgi := [ phi(h) : h in Hg ];
  Hgci := [ phi(h) : h in Hgc ];
  G := sub< GL(8,q^2) | Hgi >;
  M := GModule(G);
  Mi := GModule(G, Hgci);
  isi, x := IsIsomorphic(M,Mi);
  if not isi then
    "try other one";
     Hgc2 := [ h^(ngo*go) : h in Hg ];
     Hgc2i := [ phi(h) : h in Hgc2 ];
     M2i := GModule(G, Hgc2i);
     isi, x := IsIsomorphic(M,M2i); assert isi;
  end if;
  G := sub< GL(8,q^2) | Hgi, x >;
  G := G^TransformForm(G:Scalars:=true);
  return sub< GL(8,q^2) | G, ScalarMatrix(8, PrimitiveElement(GF(q^2))) >;
end function;

function KlLine4(q : special:=false, general:=false, normaliser:=false )
//P_2 In IsotropicStabOmega(8, q, 3, 1) replace
//GL(3,q) by q^2:(GL(1,q)xGL(2,q))
  local t,u,v,x,y,z,go,stab;

  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  d:=8; k:=3; sign:=1;
  Om := OmegaPlus;

  //We need an element go in SO(d-2*k,q) - Omega.
  go := SOMinusOmega(d-2*k, q, sign);

  z:= PrimitiveElement(GF(q));
  form:= GL(k,q)!Matrix(GF(q), k, k, [<i, k-i+1, 1> : i in [1..k]]);
  diag:= [<i,i,1>: i in [1..d]];
  gens := [GL(d,q)|];
 
  //q^2:(GL(1,q)xGL(2,q)) on <e_1..e_k>, balanced on <f_k..f_1>.
  gens := [GL(d,q)| ];
  stab := GLStabOfNSpace(3,q,1);
  for i in [1..Ngens(stab)] do
    gen := stab.i;
    elt := DiagonalJoin(< gen, IdentityMatrix(GF(q),d-2*k),
                                  form*Transpose(gen^-1)*form > );
    if IsEven(q) or ( IsOdd(q) and IsSquare(Determinant(gen)) or
            InOmega(elt,d,q,sign) or special ) then
      Append(~gens, elt);
      continue;
    end if;
    if d - 2*k gt 1 then
      elt := DiagonalJoin(< gen, go, form*Transpose(gen^-1)*form > );
//gen didn't work with IdentityMatrix in middle section, so 
//will work with element from SO\Omega.
      Append(~gens, elt );
    elif elt^2 ne elt^0 then
      Append(~gens, elt^2 );
//square will be in Omega
    //elif i ne Ngens(GL(k,q)) then //only for case q=3, k>1
    //  gen := (GL(k,q).(i+1))^gen;
    //  elt := DiagonalJoin(< gen, IdentityMatrix(GF(q),d-2*k),
     //                               form*Transpose(gen^-1)*form > );
    //  Append(~gens, elt );
    end if;
  end for;

  if d - 2*k gt 1 then
    // orthogonal group acting on a (d-2k) space.
    gens cat:=
       [ DiagonalJoin(<IdentityMatrix(GF(q), k), Om(d-2*k, q).i,
             IdentityMatrix(GF(q), k)>) : i in [1..Ngens(Om(d-2*k, q))] ];
    if special then
       Append( ~gens, DiagonalJoin(<IdentityMatrix(GF(q), k),
             SOMinusOmega(d-2*k, q, sign), IdentityMatrix(GF(q), k)>) );
    end if;
    if general and IsOdd(q) then
       Append( ~gens, DiagonalJoin(<IdentityMatrix(GF(q), k),
             GOMinusSO(d-2*k, q, sign), IdentityMatrix(GF(q), k)>) );
    end if;
  end if;

  //don't know where I got the generators below from - did I calculate them?
  if k gt 1 then
    Append(~gens,
       GL(d, q)!Matrix(GF(q), d, d, [<d-1,1,1>, <d,2,-1>] cat diag) );
  end if;
  if (d gt 2*k+2) or (d eq 2*k+2 and sign eq 1) then
    Append(~gens,
     GL(d, q)!Matrix(GF(q), d, d, [<k+1, 1, 1>, <d, d-k, -1>] cat diag) );
    if d eq 2*k+2 and sign eq 1 then
      Append(~gens,
       GL(d, q)!Matrix(GF(q), d, d, [<k+2, 1, 1>, <d, d-k-1, -1>] cat diag) );
    end if;
  end if;

  if normaliser then
    if IsOdd(q) and IsEven(d) and d ne 2*k then
       Append( ~gens, DiagonalJoin(<ScalarMatrix(k, z),
             NormGOMinusGO(d-2*k, q, sign), IdentityMatrix(GF(q), k)>) );
    elif q gt 3 then
      Append(~gens, ScalarMatrix(d,z) );
    end if; 
  end if;

  return sub<GL(d, q)| gens >;
  //c=1. 
end function;

//Line 6: R_{s3} = IsotropicStabOmega(d, q, 3, sign)

function KlLine7(q : special:=false, general:=false, normaliser:=false )
//P_1 In IsotropicStabOmega(8, q, 1, 1) replace
//OmegaPlus(6,q) by q^3:(GL(3,q)) = IsotropicStabOmega(6,q,3,1).
  local t,u,v,x,y,z,go,stab;

  if normaliser then general:=true; end if;
  if general then special:=true; end if;
  d:=8; sign:=1; k:=1;
  Om := OmegaPlus;

  z:= PrimitiveElement(GF(q));
  form:= GL(k,q)!Matrix(GF(q), k, k, [<i, k-i+1, 1> : i in [1..k]]);
  diag:= [<i,i,1>: i in [1..d]];
  gens := [GL(d,q)|];
  //will also need form for constructing IsotropicStabOmega(6,q,3,1)
  form3 := GL(3,q)!Matrix(GF(q), 3, 3, [<i, 3-i+1, 1> : i in [1..3]]);
  //element go in SOPlus(6,q)-OmegaPlus(6,q) in IsotropicStabOmega(6,q,3,1)
  if IsOdd(q) then 
    gen := GL(3,q).1;
    go := DiagonalJoin(< gen, form3*Transpose(gen^-1)*form3 > );
  end if;
 
  //GL(k, q) on <e_1..e_k>, balanced on <f_k..f_1>.
  gens := [GL(d,q)| ];
  for i in [1..Ngens(GL(k,q))] do
    gen := GL(k,q).i;
    elt := DiagonalJoin(< gen, IdentityMatrix(GF(q),d-2*k),
                                  form*Transpose(gen^-1)*form > );
    if IsEven(q) or ( IsOdd(q) and IsSquare(Determinant(gen)) or
            InOmega(elt,d,q,sign) or special ) then
      Append(~gens, elt);
      continue;
    end if;
    assert IsOdd(q);
    elt := DiagonalJoin(< gen, go, form*Transpose(gen^-1)*form > );
    assert  InOmega(elt,d,q,sign);
//gen didn't work with IdentityMatrix in middle section, so 
//will work with element from SO\Omega.
    Append(~gens, elt );
  end for;

  if d - 2*k gt 1 then
    //IsotropicStabOmega(6,q,3,1) acting on a (d-2k) space.
    stab := IsotropicStabOmega(6,q,3,1);
    gens cat:=
       [ DiagonalJoin(<IdentityMatrix(GF(q), k), stab.i,
             IdentityMatrix(GF(q), k)>) : i in [1..Ngens(stab)] ];
    if special and IsOdd(q) then
       Append( ~gens, DiagonalJoin(<IdentityMatrix(GF(q), k),
             go, IdentityMatrix(GF(q), k)>) );
    end if;
  end if;

  //don't know where I got the generators below from - did I calculate them?
  Append(~gens,
    GL(d, q)!Matrix(GF(q), d, d, [<k+1, 1, 1>, <d, d-k, -1>] cat diag) );

  if normaliser then
    if IsOdd(q) then
       Append( ~gens, DiagonalJoin(<ScalarMatrix(k, z),
             NormGOMinusGO(6, q, sign), IdentityMatrix(GF(q), k)>) );
    elif q gt 3 then
      Append(~gens, ScalarMatrix(d,z) );
    end if; 
  end if;

  return sub<GL(d, q)| gens >;
  //c=2, so (q even), go-so (q odd)
end function;

function KlLine15(q : special:=false, general:=false, normaliser:=false )
//G_2(q)
  d:=8;  sign:=1; type:="orth+";
  if normaliser then general:=true; end if;
  if general then special:=true; end if;
  if IsOdd(q) then
    k := 7;
    sign1 := 0; sign2 := 0;
    gp1 :=  G2(q);
    gp2 :=  sub<GL(1,q) | [-1] >;
    isf, form1 := SymmetricBilinearForm(gp1);
    form2 := Matrix(GF(q),1,1,[1]);

  //We need elements of ggl1/2, gsl1/2 in sl-omega (d-k>1) and gl-sl(p odd) 
    ggl1 :=  GL(k,q)!(-GL(k,q).0);
    ggl2 := GOMinusSO(d-k, q, sign2);
    gp1 := sub< GL(k,q) | gp1, ggl1 >;
    
    w := PrimitiveElement(GF(q));
    formt := MatrixAlgebra(GF(q),k)!1;
    cmat1 := CorrectForm(form1,k,q,"orth"); 
    cmat2 := CorrectForm(formt,k,q,"orth"); 
    gp1 := gp1^(cmat1*cmat2^-1);
    form1 := formt;
  
    //We will need to transform our generators to fix Magma's quadratic form.
    tmat := TransformForm(DiagonalJoin(form1,form2), type);
  
    //Now we can start constructing the generators
    gens := [GL(d,q)|];
  
    for gen in [gp1.i : i in [1..Ngens(gp1)]] do
      if Determinant(gen) ne 1 then
        if general then
          newgen := GL(d,q)!DiagonalJoin(gen,Id(gp2))^tmat;
          Append(~gens,newgen);
        end if;
        newgen := GL(d,q)!DiagonalJoin(gen,ggl2)^tmat;
        assert InOmega(newgen,d,q,sign);
        Append(~gens,newgen);
      else
        newgen := GL(d,q)!DiagonalJoin(gen,IdentityMatrix(GF(q),d-k))^tmat;
        assert InOmega(newgen,d,q,sign);
        Append(~gens,newgen);
      end if;
    end for;
  
    if normaliser and q gt 3 then
      Append(~gens, ScalarMatrix(d, PrimitiveElement(GF(q))) );
    end if;
  
    return sub<GL(d,q) | gens>;
  end if;

  //q even
  QF := func< v,qf | (Matrix(v) * qf * Transpose(Matrix(v)))[1][1] >;
   //QF(v) = value of quadratic form on vector v

  if normaliser then special:=true; end if;

  //find action of G2(q) on 6 dimensional space
  C := Constituents(GModule(G2(q)));
  C:=[c: c in C | Dimension(c) eq 6];
  g2:=ActionGroup(C[1]);

  Omdq := OmegaPlus(d,q);
  isf, qf := QuadraticForm(Omdq);
  isf, bf := SymmetricBilinearForm(Omdq);
  //normalize qf and bf
  qf := qf[1][d]^-1 * qf;
  bf := bf[1][d]^-1 * bf;
  V := VectorSpace(GF(q),d);
  U := VectorSpace(GF(q),d-2);
  W := VectorSpace(GF(q),d-1);
  v := V!([1] cat [0:i in [1..d-2]] cat [1]);
   //(1, 0, ... 0, 1) - this is the ns fixed vector of the group constructed
  assert QF(v,qf) eq 1;

  cmat := GL(d,q)!Matrix(GF(q),d,d,
             [<1,d,1>, <d,1,1>] cat [ <i,i,1> : i in [2..d-1] ] );
  //cmat = element centralising group to be constructed that is SO - Omega
  //called  r_omega in KL Prop 4.1.7
  gens := [GL(d,q)|];
  // Now we calculate embedding of g2 into G.
  //Unfortunately bf is not always just antidiagonal 1, so need to transform
  //generators of g2 to make them fix bf
  //when bf is not antidiagonal 1, it's the cetnral 2 \times 2 that's wrong
  mat := GL(d-2,q)!DiagonalMatrix(GF(q),
         [bf[i][d+1-i]^-1 : i in [2..d div 2] ] cat [1 : i in [2..d div 2] ] );
  for gen in [(g2.i)^mat : i in [1..Ngens(g2)] ] do
    ims := [V|];
    for i in [1..d-2] do
      w := V!([0] cat Eltseq(U.i^gen) cat [0]);
//next line from KL Prop 4.1.7
      c := (QF(V.(i+1),qf) + QF(w,qf))^(q div 2); //^(q div 2) = sqrt.
      w := w + c*v; //image of V.(i+1) under generator
      assert QF(w,qf) eq QF(V.(i+1),qf);
      Append(~ims,w);
    end for;
//did I do next few lines?
    eqns := Transpose(Matrix(ims cat [v]));
    z := Solution(bf*eqns,W.(d-1));
    P := PolynomialRing(GF(q)); x := P.1;
    rts := Roots(x^2+x+QF(z,qf));
    if rts eq [] then error "Cannot solve quadratic"; end if;
    z := z + rts[1][1]*v;
    newgen := GL(d,q)!Matrix([z] cat ims cat [z+v]);
    if not special and not InOmega(newgen,d,q,sign) then
      newgen *:= cmat;
    end if;
    Append(~gens, newgen );
  end for;
  if special then Append(~gens, cmat); end if;
  if normaliser and q gt 2  then
    Append(~gens, ScalarMatrix(d, PrimitiveElement(GF(q))) );
  end if;

  return sub<GL(d,q) | gens >;
  //c=1 (q even), 4 (q odd) (ngo-go, so-omega) 
end function;

function KlLine22(q : special:=false, general:=false, normaliser:=false )
//NonDegenStabOmega(8,q,1,2,1) with Omega^+(6,2) replaced by maximal
//imprimitive subgroup of type GL(3,q). 
  d:=8;  sign:=1; type:="orth+";
  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  k:=2; sign1:=1; sign2:=1;

  gp1 :=  GOPlus(k,q);
  gp2 :=  GOPlus(d-k,q);

  //Note that we use GO  (rather than SO, Omega) to calculate the forms
  //to ensure absolute irreducibility of gp1, gp2 in dimension 2.
  if IsEven(q) then
    if q eq 2 and k eq 2 then
      form1 := Matrix(GF(q),2,2,[0,1,0,0]);
    else isf, form1 := QuadraticForm(gp1);
    end if;
    isf, form2 := QuadraticForm(gp2);
  else
    if q eq 3 then
      form1 := Matrix(GF(q),2,2,[0,1,1,0]);
    else isf, form1 := SymmetricBilinearForm(gp1);
    end if;
    isf, form2 := SymmetricBilinearForm(gp2);
  end if;

  //Now construct imprimitive subgp of OmegaPlus(6,q) of type GL(3,q).
  z:= PrimitiveElement(GF(q));
  DJ := function(mat,f,q)
    local cb;
    cb := GL(f, q)!Matrix(GF(q),f,f,[<i,f+1-i,1>:i in [1..f]]);
    return DiagonalJoin(mat,Transpose(cb*mat^-1*cb));
  end function;

  //want matrices to generate GL(d,q) for q even or GL(d,q)/2
  //for q odd (see KL (4.2.7)).
  mat1:= q eq 3 select DJ(SL(3,q).1,3,q) else IsEven(q)
                  select DJ(GL(3,q).1,3,q) else DJ((GL(3,q).1)^2,3,q); 
  mat2:= q eq 3 select DJ(SL(3,q).2,3,q) else DJ((GL(3,q).2),3,q);

  //also will need elements of so-omega and (for q>2) go-so
  swapmat := GL(6,q)!Matrix(GF(q),6,6,[<i,7-i,1>:i in [1..6]]);//antidiag
  if IsOdd(q) then
    gsl2 := DJ(GL(3,q).1,3,q);
    ggl2 := swapmat;
  else gsl2 := swapmat;
  end if;

  //We need elements of ggl1/2, gsl1/2 in sl-omega (d-k>1) and gl-sl(p odd) 
  //WE laready have ggl2, gsl2
  gsl1 := SOMinusOmega(k, q, sign1);
  if IsOdd(q) then
    ggl1 := GOMinusSO(k, q, sign1);
  end if;
  
  //now redefine gp1, gp2 to include generators of Omega + gsl, ggl 
  //"fewer adjusting elements": Omega, gsl1, ggl1, ggl1 \times gsl1
  
  gp1 := OmegaPlus(k,q);
  gp1 := sub < GL(k,q) | gp1, gsl1 >;
  if IsOdd(q) then
    gp1 := sub < GL(k,q) | gp1, ggl1 >;
  end if;

  gp2 := sub < GL(d-k,q) | mat1, mat2, gsl2 >;

  //We will need to transform our generators to fix Magma's quadratic form.
  tmat := TransformForm(DiagonalJoin(form1,form2), type);

  //Now we can start constructing the generators
  gens := [GL(d,q)|];

  for gen in [gp1.i : i in [1..Ngens(gp1)]] do
    if Determinant(gen) ne 1 then
      if general then
        newgen := GL(d,q)!DiagonalJoin(gen,Id(gp2))^tmat;
        Append(~gens,newgen);
      end if;
      //use ggl2 to adjust it and make determinant 1
      newgen := GL(d,q)!DiagonalJoin(gen,ggl2)^tmat;
      if special or InOmega(newgen,d,q,sign) then
        Append(~gens,newgen);
      elif d-k gt 1 then
        //adjust again using gsl2.
        newgen := GL(d,q)!DiagonalJoin(gen,ggl2*gsl2)^tmat;
        assert InOmega(newgen,d,q,sign);
        Append(~gens,newgen);
      end if;
    else
      newgen := GL(d,q)!DiagonalJoin(gen,IdentityMatrix(GF(q),d-k))^tmat;
      if special or InOmega(newgen,d,q,sign) then
        Append(~gens,newgen);
      elif d-k gt 1 then
        //adjust using gsl2.
        newgen := GL(d,q)!DiagonalJoin(gen,gsl2)^tmat;
        assert InOmega(newgen,d,q,sign);
        Append(~gens,newgen);
      end if;
    end if;
  end for;

  for gen in [gp2.i : i in [1..Ngens(gp2)]] do
    newgen := GL(d,q)!DiagonalJoin(IdentityMatrix(GF(q),k),gen)^tmat;
    if special or InOmega(newgen,d,q,sign) then
      Append(~gens,newgen);
    end if;
  end for;

  if normaliser then
    if IsOdd(q) and IsEven(d) then
      gnl1 := NormGOMinusGO(k, q, sign1);
      gnl2 := NormGOMinusGO(d-k, q, sign2);
      newgen := (GL(d,q)!DiagonalJoin(gnl1,gnl2))^tmat;
      Append(~gens,newgen);
    elif q gt 3 then
      Append(~gens, ScalarMatrix(d, PrimitiveElement(GF(q))) );
    end if;
  end if;

  return sub<GL(d,q) | gens>;
  //c=1
end function;

function KlLine26(q : special:=false, general:=false, normaliser:=false )
//NonDegenStabOmega(8,q,1,2,-1) with Omega^-(6,2) replaced by maximal
//imprimitive subgroup of type GU(3,q). 
  d:=8;  sign:=1; type:="orth+";
  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  k:=2; sign1:=-1; sign2:=-1;

  gp1 :=  GOMinus(k,q);
  gp2 :=  GOMinus(d-k,q);

  //Note that we use GO  (rather than SO, Omega) to calculate the forms
  //to ensure absolute irreducibility of gp1, gp2 in dimension 2.
  if IsEven(q) then
    isf, form1 := QuadraticForm(gp1);
    isf, form2 := QuadraticForm(gp2);
  else
    isf, form1 := SymmetricBilinearForm(gp1);
    isf, form2 := SymmetricBilinearForm(gp2);
  end if;

  //Now construct semilinear subgp of OmegaMinus(6,q) of type GU(3,q).

  gammal1:= GammaL1(2, q);
  epsilon:= gammal1.1;
  frob:= gammal1.2;
  zero:= Matrix(GF(q), 2, 2, []);

  gu1:= GU(3, q).1;  //generates GU mod SU
  gu2:= GU(3, q).2;

  gu1e:= GL(6, q)!BlockPowers(epsilon, gu1, 1);
  gu2e:= GL(6, q)!BlockPowers(epsilon, gu2, 1);
  //all of the above have determinant 1

  //now we want to extend by the field automorphism x->x^q,
  frob_diag:= GL(6,q)!DiagonalJoin([frob : i in [1..3]]);
  grp := sub<GL(6,q)|gu1e, gu2e, frob_diag>;
  //We will need to transform our generators to fix Magma's quadratic form.
  tmat := TransformForm(grp);

  //Now just need to intersect with Omega.
  if IsEven(q) then
    mat1 := gu1e^tmat; mat2 := gu2e^tmat;
  else
    mat1 := (gu1e^tmat)^2; mat2 := gu2e^tmat;
  end if;
  assert InOmega(mat1,6,q,-1) and InOmega(mat2,6,q,-1);
  frob_diag := frob_diag^tmat;
  if normaliser then
    gun:= ScalarMatrix(3, PrimitiveElement(GF(q^2)) );
    gune:= GL(6, q)!BlockPowers(epsilon, gun, 1);
    gune := gune^tmat;
  end if;

  //also will need elements of so-omega and (for q>2) go-so
  if IsOdd(q) then
    gsl2 := gu1e^tmat;
    ggl2 := frob_diag;
  else gsl2 := frob_diag;
  end if;

  //We need elements of ggl1/2, gsl1/2 in sl-omega (d-k>1) and gl-sl(p odd) 
  //WE laready have ggl2, gsl2
  gsl1 := SOMinusOmega(k, q, sign1);
  if IsOdd(q) then
    ggl1 := GOMinusSO(k, q, sign1);
  end if;
  
  //now redefine gp1, gp2 to include generators of Omega + gsl, ggl 
  //"fewer adjusting elements": Omega, gsl1, ggl1, ggl1 \times gsl1
  
  gp1 := OmegaMinus(k,q);
  gp1 := sub < GL(k,q) | gp1, gsl1 >;
  if IsOdd(q) then
    gp1 := sub < GL(k,q) | gp1, ggl1 >;
  end if;

  gp2 := sub < GL(d-k,q) | mat1, mat2, gsl2 >;

  //We will need to transform our generators to fix Magma's quadratic form.
  tmat := TransformForm(DiagonalJoin(form1,form2), type);

  //Now we can start constructing the generators
  gens := [GL(d,q)|];

  for gen in [gp1.i : i in [1..Ngens(gp1)]] do
    if Determinant(gen) ne 1 then
      if general then
        newgen := GL(d,q)!DiagonalJoin(gen,Id(gp2))^tmat;
        Append(~gens,newgen);
      end if;
      //use ggl2 to adjust it and make determinant 1
      newgen := GL(d,q)!DiagonalJoin(gen,ggl2)^tmat;
      if special or InOmega(newgen,d,q,sign) then
        Append(~gens,newgen);
      elif d-k gt 1 then
        //adjust again using gsl2.
        newgen := GL(d,q)!DiagonalJoin(gen,ggl2*gsl2)^tmat;
        assert InOmega(newgen,d,q,sign);
        Append(~gens,newgen);
      end if;
    else
      newgen := GL(d,q)!DiagonalJoin(gen,IdentityMatrix(GF(q),d-k))^tmat;
      if special or InOmega(newgen,d,q,sign) then
        Append(~gens,newgen);
      elif d-k gt 1 then
        //adjust using gsl2.
        newgen := GL(d,q)!DiagonalJoin(gen,gsl2)^tmat;
        assert InOmega(newgen,d,q,sign);
        Append(~gens,newgen);
      end if;
    end if;
  end for;

  for gen in [gp2.i : i in [1..Ngens(gp2)]] do
    newgen := GL(d,q)!DiagonalJoin(IdentityMatrix(GF(q),k),gen)^tmat;
    if special or InOmega(newgen,d,q,sign) then
      Append(~gens,newgen);
    end if;
  end for;

  if normaliser then
    if IsOdd(q) and IsEven(d) then
      gnl1 := NormGOMinusGO(k, q, sign1);
      newgen := (GL(d,q)!DiagonalJoin(gnl1,gune))^tmat;
      Append(~gens,newgen);
    elif q gt 3 then
      Append(~gens, ScalarMatrix(d, PrimitiveElement(GF(q))) );
    end if;
  end if;

  return sub<GL(d,q) | gens>;
  //c=1
end function;

function KlLine51(q : special:=false, general:=false, normaliser:=false )
//2^9:L_3(2) as subgp of imrprimitive group 2^6:A_8. 
  assert IsOdd(q) and IsPrime(q);
  d:=8;  sign:=1; type:="orth+";
  if normaliser then general:=true; end if;
  if general then special:=true; end if;
  k:=1; sign1:=0;

  t := d div k;
  //Check parameters are compatible.
  
  gp1 :=  sub<GL(k,q)|[-1]>;
  
  //Note that we use GO  (rather than SO, Omega) to calculate the forms
  //to ensure absolute irreducibility of gp1, gp2 in dimension 2.
  isf, form1 := SymmetricBilinearForm(gp1);

  ggl1 := GOMinusSO(k, q, sign1);
  
  //We will need to transform our generators to fix Magma's quadratic form.
  tmat := TransformForm(DiagonalJoin([form1: i in [1..t]]), type);
  id := GL(k,q)!IdentityMatrix(GF(q),k);

  //Now we can start constructing the generators
  gens := [GL(d,q)|];

  for gen in [gp1.i : i in [1..Ngens(gp1)]] do
    assert Determinant(gen) ne 1;
   //use ggl1 to adjust it and make determinant 1
    if general then
        newgen := GL(d,q)!DiagonalJoin([gen] cat [id: i in [1..t-1]])^tmat;
        Append(~gens,newgen);
    end if;
    newgen := GL(d,q)!DiagonalJoin([gen,ggl1] cat [id: i in [1..t-2]])^tmat;
    if special or InOmega(newgen,d,q,sign) then
        Append(~gens,newgen);
    end if;
  end for;

  //Now generators of 2^3.L_3(2)
  sgens:=[ Sym(8) | (1,2,6,8,3,5,4), (2,6,8,7,4,5,3) ];
  for gen in sgens do
    newgen :=
     GL(d,q)!PermutationMatrix(GF(q),gen)^tmat;
    assert InOmega(newgen,d,q,sign);
    Append(~gens,newgen);
  end for;

  if normaliser and q gt 3  then
    Append(~gens, ScalarMatrix(d, PrimitiveElement(GF(q))) );
  end if;

  return sub<GL(d,q) | gens>;
  //c=4 so-omega, ngo-go
end function;

function KlLine61(q : special:=false, general:=false, normaliser:=false )
//(D_2(q^2+1)xD_2(q^2+1).2^2) as subgp of imprim OmegaMinus(4,2) wr 2.
  d:=8;  sign:=1; type:="orth+";
  if normaliser then general:=true; end if;
  if general then special:=true; end if;
  k := 4;
  sign1 := -1;

  t := d div k;
  
  gp1 :=  GOMinus(k,q);
  
  //Note that we use GO  (rather than SO, Omega) to calculate the forms
  //to ensure absolute irreducibility of gp1, gp2 in dimension 2.
  if IsEven(q) then
    isf, form1 := QuadraticForm(gp1);
  else isf, form1 := SymmetricBilinearForm(gp1);
  end if;

  //now construct semilinear subgroup
  s := 2;
  dim:= 2;

  bigsgp1 := GOMinus(dim,q^s);
  sgp1 := OmegaMinus(dim,q^s);

  //In the -1 case, the field automorphism will change the form, so
  //we will need to conjugate it back.
  if IsEven(q) then
      isf, sform := QuadraticForm(bigsgp1);
  else
      isf, sform := SymmetricBilinearForm(bigsgp1);
  end if;
  cform := MatToQ(sform,q);
  cmat1 := TransformForm(cform,"orth-");
  
  //We need elements of ggl, gsl in sl-omega
  sgsl := SOMinusOmega(dim, q^2, sign1);
  if IsOdd(q) then
    sggl := GOMinusSO(dim, q^2, sign1);
  end if;

  gammal1:= GammaL1(s, q);
  singer:= gammal1.1;
  frob:= gammal1.2;

  sgens := [ GL(k,q) | BlockPowers(singer, sgp1.i, 1 ) :
                                                    i in [1..Ngens(sgp1)] ];
  bigsgens := [ BlockPowers(singer, bigsgp1.i, 1  ) :
                                               i in [1..Ngens(bigsgp1)] ];
  sgsl2 := GL(k,q)!BlockPowers(singer, sgsl, 1 );
  if IsOdd(q) then
    sggl2 := GL(k,q)!BlockPowers(singer, sggl, 1 );
  end if;
  frobgen:= GL(k,q)!DiagonalJoin([frob: i in [1..dim]]);
  //det(frobgen) = det(frob)^2 = 1.
  frobgen := frobgen * GL(k,q)!BlockPowers(singer, cmat1, 1 );
  assert Determinant(frobgen) eq GF(q)!(-1);
  bigsgrp:=  sub<GL(k, q)| bigsgens, frobgen>;

  //We will need to transform our generators to fix Magma's quadratic form.
  tmat := TransformForm(bigsgrp);
  csgens := [ g^tmat : g in sgens ];

  sgsl2 := sgsl2^tmat;
  //find extra generator in Omega
  if IsOdd(q) then
    sggl2 := sggl2^tmat;
    if InOmega(sggl2,k,q,sign1) then
      Append(~csgens,sggl2);
    else assert InOmega(sggl2*sgsl2,k,q,sign1);
      Append(~csgens,sggl2*sgsl2);
    end if;
    gsl1 := sgsl2;
  else assert InOmega(sgsl2,k,q,sign1);
    Append(~csgens,sgsl2);
  end if;
  frobgen := frobgen^tmat;
  if IsOdd(q) then
    ggl1 := frobgen;
  else gsl1 := frobgen;
  end if;

  if normaliser and IsOdd(q) then
    scal := ScalarMatrix( GF(q^2), dim, PrimitiveElement(GF(q^2)) );
    ngo := BlockPowers(singer, scal, 1);
    ngo := (GL(k,q)!ngo)^tmat;
    ngo := ngo ^ ((q+1) div 2);
  end if;

  //We have already defined elements of in sl-omega and gl-sl(p odd) 
  
  //now redefine gp1
  gp1 := sub < GL(k,q) | csgens, gsl1 >;
  if IsOdd(q) then
    gp1 := sub < GL(k,q) | gp1, ggl1 >;
  end if;

  //We will need to transform our generators to fix Magma's quadratic form.
  tmat := TransformForm(DiagonalJoin([form1: i in [1..t]]), type);
  id := GL(k,q)!IdentityMatrix(GF(q),k);

  //Now we can start constructing the generators
  gens := [GL(d,q)|];

  for gen in [gp1.i : i in [1..Ngens(gp1)]] do
    if Determinant(gen) ne 1 then
      //use ggl1 to adjust it and make determinant 1
      if general then
        newgen := GL(d,q)!DiagonalJoin([gen] cat [id: i in [1..t-1]])^tmat;
        Append(~gens,newgen);
      end if;
      newgen := GL(d,q)!DiagonalJoin([gen,ggl1] cat [id: i in [1..t-2]])^tmat;
      if special or InOmega(newgen,d,q,sign) then
        Append(~gens,newgen);
      else
        //adjust again using gsl1.
        newgen :=
           GL(d,q)!DiagonalJoin([gen,ggl1*gsl1] cat [id: i in [1..t-2]])^tmat;
        assert InOmega(newgen,d,q,sign);
        Append(~gens,newgen);
      end if;
    else
      newgen := GL(d,q)!DiagonalJoin([gen] cat [id: i in [1..t-1]])^tmat;
      if special or InOmega(newgen,d,q,sign) then
        Append(~gens,newgen);
      elif k gt 1 then
        //adjust using gsl1.
        newgen :=
           GL(d,q)!DiagonalJoin([gen,gsl1] cat [id: i in [1..t-2]])^tmat;
        assert InOmega(newgen,d,q,sign);
        Append(~gens,newgen);
      end if;
    end if;
  end for;

  //Now generators of S_n 
  for gen in [Alt(t).i : i in [1..Ngens(Alt(t))] ] do
    newgen :=
     GL(d,q)!KroneckerProduct( PermutationMatrix(GF(q),gen), id )^tmat;
    assert InOmega(newgen,d,q,sign);
    Append(~gens,newgen);
  end for;

  newgen :=
    GL(d,q)!KroneckerProduct( PermutationMatrix(GF(q),Sym(t)!(1,2)), id )^tmat;
  //if Determinant(newgen) neq 1: the ggl1 matrix always has det -1
  if Determinant(newgen) ne 1 then
    newgen *:= GL(d,q)!DiagonalJoin([ggl1] cat [id: i in [1..t-1]])^tmat;
  end if;
  if special or InOmega(newgen,d,q,sign) then
    Append(~gens,newgen);
  else
    //gsl1 has det 1 spinor +1
    newgen *:= GL(d,q)!DiagonalJoin([gsl1] cat [id: i in [1..t-1]])^tmat;
    assert InOmega(newgen,d,q,sign);
    Append(~gens,newgen);
  end if;

  if normaliser  then
    if IsOdd(q) then
      newgen := GL(d,q)!DiagonalJoin([ngo : i in [1..t]])^tmat;
      Append(~gens,newgen);
    elif q gt 2 then
      Append(~gens, ScalarMatrix(d, PrimitiveElement(GF(q))) );
    end if;
  end if;

  return sub<GL(d,q) | gens>;
  //c=1
end function;
