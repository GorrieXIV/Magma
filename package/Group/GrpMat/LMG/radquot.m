freeze;

import "outers.m": GLMinusSL, GUMinusSU, CSpMinusSp, SOMinusOmega,
                   GOMinusSO, CGOMinusGO;
import "autinfo.m": InitialiseAutInfoC, InitialiseAutInfoG,
                    AutTuple, IdentifyAutG, IdentifyEmbeddedAut;
import "graphauts.m": GAutSp, GAutO8Plus;
/* We attempt to construct a homomorphism from G to a permutation group
 * isomorphic to G/Radical(G) for LMG group.
 */
MatToQ := function(A,q)
// raise every element of matrix A to q-th power
   local B;
   B := MatrixAlgebra(BaseRing(A),Nrows(A))!0;
   for i in [1..Nrows(A)] do for j in [1..Ncols(A)] do
      B[i][j] := A[i][j]^q;
   end for; end for;
   return B;
end function;

/* We need to know the automorphism groups of the classical groups
 * We return permutation representations of these on given generating
 * generating set + other generators given by functions in outers,
 * standard field automorphisms, etc.
 * the input "gens" are nice generators of the quasisimple classical
 * matrix group. The list gens with generators of conformal group
 * appended is output for later use in the "IT" functions.
 */
AutSL := function(n,p,e,gens : graph := true)
  local mat, glgens, glgens2, G, Z, q, np, F, w, V, ng, v,  d, ct, perms, vi;
  assert n ge 2;
  if n eq 2 then graph := false; end if;
  q:=p^e;
  glgens := GCD(n,p^e-1) gt 1 select gens cat [GLMinusSL(n,q)] else gens;
  G := sub< GL(n,q) | glgens >;
  V := VectorSpace(G);
  if e eq 1 then
      if not graph then
         return OrbitImage(G,sub<V|V.1>), glgens;
      end if;
      glgens2 := [GL(2*n,q) | DirectSum(g,Transpose(g^-1)) : g in glgens ];
      mat := MatrixAlgebra(GF(q),2*n)!0;
      InsertBlock(~mat,Identity(GL(n,q)),1,n+1);
      InsertBlock(~mat,Identity(GL(n,q)),n+1,1);
      Append(~glgens2,mat);
      G := sub< GL(2*n,q) | glgens2 >;
      V := VectorSpace(G);
      return OrbitImage(G,sub<V|V.1>), glgens;
  end if;

  Z := Integers();
  np := (q^n - 1) div (q-1);
  F := GF(q); w := F.1;
  ng := Ngens(G);
  perms := graph select [ [] : i in [1..ng+2] ] else [ [] : i in [1..ng+1] ];
  lv := w^(q-2);
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
      if graph then perms[i][ct+np] := VNO(v^gti)+np; end if;
    end for;

    // field automorphism:
    vi := VNO(V![v[i]^p : i in [1..n]]);
    perms[ng+1][ct] := vi;
    if graph then perms[ng+1][ct+np] := vi+np; end if;

    if graph then
      // graph automorphism:
      perms[ng+2][ct] := ct+np;
      perms[ng+2][ct+np] := ct;
    end if;

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
  if graph then return sub< Sym(2*np) | perms >, glgens; end if;
  return sub< Sym(np) | perms >, glgens;
end function;

AutSU := function(n,p,e,gens)
  local q, np, G, ng, gugens, perms, V, v, vi;
  assert n ge 2;
  q := p^e;
  gugens := GCD(n,p^e+1) gt 1 select gens cat [GUMinusSU(n,q)] else gens;
  G := sub< GL(n,q^2) | gugens >;
  _,form := UnitaryForm(G);
  ng := Ngens(G);
  perms := [ [] : i in [1..ng+1] ];
  V := VectorSpace(G);
  D := &join[ {@ V!([0: i in [1..t-1]] cat [1] cat Eltseq(v)) :
                      v in VectorSpace(GF(q^2),n-t) @} : t in [1..n] ];
  D := {@ v : v in D |
                 Matrix(v) * form * MatToQ(Transpose(Matrix(v)),q) eq 0 @};
  np := #D;
  //loop through point and determine action of generators
  for ct in [1..np] do
    v := D[ct];
    for i in [1..ng] do
      g := G.i;
      vi := v^g;
      vi := vi[Depth(vi)]^-1 * vi;
      perms[i][ct] := Position(D,vi);
    end for;
    // field automorphism:
    vi := V![v[i]^p : i in [1..n]];
    perms[ng+1][ct] := Position(D,vi);
  end for;

  return sub< Sym(np) | perms >, gugens;
end function;

AutSp := function(n,p,e,gens : graph := n eq 4 and p eq 2 )
  local q, np, w, F, G, ng, perms, perm, lv, V, v, vi, d, c, ct, g, gti,
        NF, VNO, Z, cgens, cimgens, gaut;

  q := p^e;
  assert IsEven(n) and not (n eq 4 and q eq 2);
  F := GF(q); w := F.1;
  cspgens := GCD(2,p^e-1) gt 1 select gens cat [CSpMinusSp(n,q)] else gens;
  G := sub< GL(n,q) | cspgens >;
  if e eq 1 then //no field (not allowing Sp(4,2))
    return OrbitImage(G,sub<V|V.1>), cspgens where V:=VectorSpace(G);
  end if;
  if graph then gaut := GAutSp(q); end if;

  Z := Integers();
  np := (q^n - 1) div (q-1);
  ng := Ngens(G);
  perms := graph select [ [] : i in [1..ng+2] ] else [ [] : i in [1..ng+1] ];
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
      if graph then perms[i][ct+np] := np + VNO(v^(gaut(g))); end if;
    end for;
    // field automorphism:
    vi := VNO(V![v[i]^p : i in [1..n]]);
    perms[ng+1][ct] := vi;
    if graph then perms[ng+1][ct+np] := vi+np; end if;
  
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

  if graph then
    for i in [1..np] do
      perms[ng+2][i] := np+perms[ng+1][i];;
      perms[ng+2][np+i] := i;
    end for;
  end if;

  if graph then  return sub< Sym(2*np) | perms >, cspgens; end if;
  return sub< Sym(np) | perms >, cspgens;
end function;

AutO := function(n,p,e,gens)
  local q, np, G, ng, ogens, perms, V, v, vi;
  assert n ge 3 and IsOdd(n) and IsOdd(p);
  q := p^e;
  ogens := gens cat [SOMinusOmega(n,q,0)];
  G := sub< GL(n,q) | ogens >;
  _,form := SymmetricBilinearForm(G);
  ng := Ngens(G);
  perms := e eq 1 select [ [] : i in [1..ng] ] else [ [] : i in [1..ng+1] ];
  V := VectorSpace(G);
  D := &join[ {@ V!([0: i in [1..t-1]] cat [1] cat Eltseq(v)) :
                      v in VectorSpace(GF(q),n-t) @} : t in [1..n] ];
  D := {@ v : v in D | Matrix(v) * form * Transpose(Matrix(v)) eq 0 @};
  np := #D;
  //loop through points and determine action of generators
  for ct in [1..np] do
    v := D[ct];
    for i in [1..ng] do
      g := G.i;
      vi := v^g;
      vi := vi[Depth(vi)]^-1 * vi;
      perms[i][ct] := Position(D,vi);
    end for;
    if e gt 1 then
      // field automorphism:
      vi := V![v[i]^p : i in [1..n]];
      perms[ng+1][ct] := Position(D,vi);
    end if;
  end for;

  return sub< Sym(np) | perms >, ogens;
end function;

AutOPlus := function(n,p,e,gens : graph := n eq 8 )
  local q, w, np, G, ng, cgogens, perms, V, v, vi, genct, gag, gagag, pos,
        temp;
  assert n ge 6 and IsEven(n);
  q := p^e;
  cgogens := gens;
  if not graph and (n mod 4 eq 0 or q mod 4 ne 3) then
     cgogens cat:= [SOMinusOmega(n,q,1)];
  end if;
  if not graph and IsOdd(q) then
     cgogens cat:= [GOMinusSO(n,q,1)];
     cgogens cat:= [CGOMinusGO(n,q,1)];
  end if;
    
  G := sub< GL(n,q) | cgogens >;
  if IsEven(q) then
    _,form := QuadraticForm(GOPlus(n,q));
  else
    _,form := SymmetricBilinearForm(GOPlus(n,q));
  end if;
  ng := Ngens(G);
  genct := ng;
  if e gt 1 then genct +:= 1; end if;
  if graph then genct +:= 2; end if;
  if graph and IsOdd(q) then genct +:= 1; end if;
  perms := [ [] : i in [1..genct] ];
  V := VectorSpace(G);
  D := &join[ {@ V!([0: i in [1..t-1]] cat [1] cat Eltseq(v)) :
                      v in VectorSpace(GF(q),n-t) @} : t in [1..n] ];
  D := {@ v : v in D | Matrix(v) * form * Transpose(Matrix(v)) eq 0 @};
  np := #D;
  if graph then
    gaut := GAutO8Plus(q);
    w := PrimitiveElement(GF(q));
    gag := [gaut(G.i) : i in [1..Ngens(G)]];
    gagag := [gaut(x) : x in gag];
  end if;
  //loop through points and determine action of generators
  for ct in [1..np] do
    v := D[ct];
    for i in [1..ng] do
      g := G.i;
      vi := v^g;
      vi := vi[Depth(vi)]^-1 * vi;
      perms[i][ct] := Position(D,vi); assert perms[i][ct] ne 0;
      if graph then
        vi := v^gag[i];
        vi := vi[Depth(vi)]^-1 * vi;
        perms[i][ct+np] := Position(D,vi)+np; assert perms[i][ct+np] ne np;
        vi := v^gagag[i];
        vi := vi[Depth(vi)]^-1 * vi;
        perms[i][ct+2*np] := Position(D,vi)+2*np;
                                           assert perms[i][ct+2*np] ne 2*np;
      end if;
    end for;
    genct := ng+1;
    if graph and IsOdd(q) then //diag
      g := GL(8,q)!DiagonalMatrix(GF(q),[w,w,w,w,1,1,1,1]);
      cgogens[ng+3] := g;
      vi := v^g;
      vi := vi[Depth(vi)]^-1 * vi;
      perms[genct][ct] := Position(D,vi); assert perms[genct][ct] ne 0;
      g := GL(8,q)!DiagonalMatrix(GF(q),[w,1,1,1,1,1,1,w^-1]);
      vi := v^g;
      vi := vi[Depth(vi)]^-1 * vi;
      perms[genct][ct+np] := Position(D,vi)+np;
                                             assert perms[genct][ct+np] ne np;
      g := GL(8,q)!DiagonalMatrix(GF(q),[1,1,1,w^-1,1,w^-1,w^-1,w^-1]);
      vi := v^g;
      vi := vi[Depth(vi)]^-1 * vi;
      perms[genct][ct+2*np] := Position(D,vi)+2*np;
                                          assert perms[genct][ct+2*np] ne 2*np;
      genct +:= 1;
    end if;
    if e gt 1 then
      // field automorphism:
      vi := V![v[i]^p : i in [1..n]];
      perms[genct][ct] := Position(D,vi); assert perms[genct][ct] ne 0;
      if graph then
        perms[genct][ct+np] := Position(D,vi)+np;
                                             assert perms[genct][ct+np] ne np;
        perms[genct][ct+2*np] := Position(D,vi)+2*np;
                                          assert perms[genct][ct+2*np] ne 2*np;
      end if;
      genct +:= 1;
    end if;
  end for;
  if graph then
    //order 2 graph
    g := GL(8,q)!PermutationMatrix(GF(q), Sym(8)!(4,5));
    if IsEven(q) then
      cgogens[ng+1] := g;
    else
      cgogens[ng+2] := g;
      cgogens[ng+1] := (cgogens[ng+2],cgogens[ng+3]);
    end if;
    for ct in [1..np] do
      v := D[ct];
      vi := v^g;
      vi := vi[Depth(vi)]^-1 * vi;
      pos := Position(D,vi); assert pos ne 0;
      perms[genct][ct] := pos;
      perms[genct][ct+np] := pos+2*np;
      perms[genct][ct+2*np] := pos+np;
    end for;
    genct +:= 1;
    //triality
    for i in [1..np] do perms[genct][i] := i+2*np; end for;
    for i in [np+1..3*np] do perms[genct][i] := i-np; end for;
  end if;
  if graph then
    //rearrange generators to get into standard order
    G := sub< Sym(3*np) | perms >;
    perms := [ G.i : i in [1..genct] ];
    if p eq 2 then 
      if e gt 1 then
        temp := perms[genct-2];
        perms[genct-2] := perms[genct-1];
        perms[genct-1] := temp;
      end if;
    else
      perms[genct+1] := perms[genct]; 
      if e eq 1 then
        perms[genct] := perms[genct-2];
        perms[genct-2] := (perms[genct-1],perms[genct]);
      else
        perms[genct] := perms[genct-2];
        perms[genct-2] := perms[genct-1];
        perms[genct-1] := perms[genct-3];
        perms[genct-3] := (perms[genct-2],perms[genct-1]);
      end if;
    end if;
    return sub< Sym(3*np) | perms >, cgogens;
  end if;
  return sub< Sym(np) | perms >, cgogens;
end function;

AutOMinus := function(n,p,e,gens,cmat)
  local q, np, G, ng, cgogens, perms, V, v, vi;
  assert n ge 4 and IsEven(n);
  q := p^e;
  cgogens := gens;
  if IsEven(q) or (n mod 4 eq 2 and q mod 4 eq 3) then
     cgogens cat:= [SOMinusOmega(n,q,-1)];
  end if;
  if IsOdd(q) then
     cgogens cat:= [GOMinusSO(n,q,-1)];
     cgogens cat:= [CGOMinusGO(n,q,-1)];
  end if;
    
  G := sub< GL(n,q) | cgogens >;
  if IsEven(q) then
    _,form := QuadraticForm(GOMinus(n,q));
  else
    _,form := SymmetricBilinearForm(GOMinus(n,q));
  end if;
  ng := Ngens(G);
  perms := e eq 1 select [ [] : i in [1..ng] ] else [ [] : i in [1..ng+1] ];
  V := VectorSpace(G);
  D := &join[ {@ V!([0: i in [1..t-1]] cat [1] cat Eltseq(v)) :
                      v in VectorSpace(GF(q),n-t) @} : t in [1..n] ];
  D := {@ v : v in D | Matrix(v) * form * Transpose(Matrix(v)) eq 0 @};
  np := #D;
  //loop through points and determine action of generators
  for ct in [1..np] do
    v := D[ct];
    for i in [1..ng] do
      g := G.i;
      vi := v^g;
      vi := vi[Depth(vi)]^-1 * vi;
      perms[i][ct] := Position(D,vi);
    end for;
    if e gt 1 then
      // field automorphism:
      vi := (V![v[i]^p : i in [1..n]])^cmat;
      vi := vi[Depth(vi)]^-1 * vi;
      perms[ng+1][ct] := Position(D,vi); assert perms[ng+1][ct] ne 0;
    end if;
  end for;

  return sub< Sym(np) | perms >, cgogens;
end function;

/* Suppose that the above "Aut" function returns A and gens.
 * The following IT (identify triple) functions take input a triple t returned
 * by AutTuple. Also input are gens (as above) imgens (generators of A),
 * factoword function for classical group, and graph, which indicates
 * whether a graph automorphism may be present among aggens.
 * Result returned is an element of A. 
 */

ITSL := function(t,n,p,e,gens,imgens,factoword,graph)
  local ng,w,lg,dc,elt,mat,wd;
  if n eq 2 then graph:=false; end if;
  ng := #imgens;
  elt := Identity(Parent(imgens[1]));
  if t[1] eq 1 then elt *:= imgens[ng]; end if;
  if graph then ng -:= 1; end if;
  if e gt 1 then
    if t[2] ne 0 then elt *:= imgens[ng]^t[2]; end if;
    ng -:= 1;
  end if;
  w := PrimitiveElement(GF(p^e));
  lg := Log(w, Determinant(t[3]));
  dc := lg mod GCD(n,p^e-1);
  if dc ne 0 then
    elt *:= imgens[ng]^dc;
    t[3] := gens[ng]^-dc * t[3];
  end if;
  isp, scalrt := IsPower(Determinant(t[3]),n); assert isp;
  t[3] := t[3] * GL(n,p^e)!ScalarMatrix(n,scalrt^-1);
  assert Determinant(t[3]) eq 1;
  wd := factoword(t[3]);
  elt *:= Evaluate(wd,imgens);
  return elt;
end function;

ITSU := function(t,n,p,e,gens,imgens,factoword)
  //make t[3] fix form
  q := p^e;
  isf, form := UnitaryForm(GU(n,q));
  formim := t[3] * form * MatToQ(Transpose(t[3]), q);
  for i in [1..n] do if form[1][i] ne 0 then
    scal := formim[1][i]/form[1][i];
    assert formim eq scal * form;
    break;
  end if; end for;
  isp, scalrt := IsPower(scal,q + 1); assert isp;
  t[3] := t[3] * ScalarMatrix(n, scalrt^-1);

  ng := #imgens;
  elt := Identity(Parent(imgens[1]));
  if t[2] ne 0 then elt *:= imgens[ng]^t[2]; end if;
  ng -:= 1;
  w := PrimitiveElement(GF(q^2));
  lg := Log(w, Determinant(t[3]));
  assert lg mod (q - 1) eq 0;
  lg := lg div (q - 1);
  dc := lg mod GCD(n,q+1);
  if dc ne 0 then
    elt *:= imgens[ng]^dc;
    t[3] := gens[ng]^-dc * t[3];
  end if;
  //Need to get determinant 1 while fixing form. Let's be lazy.
  l := Log(Determinant(t[3])); assert l mod (-1) eq 0;
  l := l div (q-1);
  found := false;
  for k in [0..q] do if k*n mod (q+1) eq l then
    kk:=k; found:=true; break;
  end if; end for;
  assert found;
  scalrt := w^( (q-1)*kk );  //scalrt^n eq det(t[3])  
  t[3] := t[3] * GL(n,q^2)!ScalarMatrix(n,scalrt^-1);
  assert Determinant(t[3]) eq 1;
  wd := factoword(t[3]);
  elt *:= Evaluate(wd,imgens);
  return elt;
end function;

ITSp := function(t,n,p,e,gens,imgens,factoword,graph)
  if n ne 4 or p ne 2 then graph:=false; end if;
  ng := #imgens;
  elt := Identity(Parent(imgens[1]));
  if t[1] eq -1 then elt *:= imgens[ng]; end if;
  if graph then ng -:= 1; end if;
  if e gt 1 then
    if t[2] ne 0 then elt *:= imgens[ng]^t[2]; end if;
    ng -:= 1;
  end if;
  //find form scaling factor
  isit, form := SymplecticForm(Sp(n,p^e));
  formim := t[3] * form * Transpose(t[3]);
  for i in [1..n] do if form[1][i] ne 0 then
    scal := formim[1][i]/form[1][i];
    assert formim eq scal * form;
    break;
  end if; end for;
  isp, scalrt := IsPower(scal,2);
  if not isp then
    elt *:= imgens[ng];
    t[3] := gens[ng]^-1 * t[3];
    formim := t[3] * form * Transpose(t[3]);
    for i in [1..n] do if form[1][i] ne 0 then
      scal := formim[1][i]/form[1][i];
      assert formim eq scal * form;
      break;
    end if; end for;
    isp, scalrt := IsPower(scal,2); assert isp;
  end if;
  t[3] := t[3] * GL(n,p^e)!ScalarMatrix(n,scalrt^-1);
  wd := factoword(t[3]);
  elt *:= Evaluate(wd,imgens);
  return elt;
end function;

ITO := function(t,n,p,e,gens,imgens,factoword : gp:=GO )
  ng := #imgens;
  elt := Identity(Parent(imgens[1]));
  if e gt 1 then
    if t[2] ne 0 then elt *:= imgens[ng]^t[2]; end if;
    ng -:= 1;
  end if;
  isit, form := SymmetricBilinearForm(gp(n,p^e));
  formim := t[3] * form * Transpose(t[3]);
  for i in [1..n] do if form[1][i] ne 0 then
    scal := formim[1][i]/form[1][i];
    assert formim eq scal * form;
    break;
  end if; end for;
  isp, scalrt := IsPower(scal,2); assert isp;
  t[3] := t[3] * GL(n,p^e)!ScalarMatrix(n,scalrt^-1);
  if IsOdd(p) and Determinant(t[3]) eq -1 then
    t[3] := GL(n,p^e) ! (-t[3]);
  end if;
  assert Determinant(t[3]) eq 1;
  if SpinorNorm(GL(n,p^e)!t[3],form) eq 1 then
    elt *:= imgens[ng];
    t[3] := gens[ng]^-1 * t[3];
  end if;
  wd := factoword(t[3]);
  elt *:= Evaluate(wd,imgens);
  return elt;
end function;

ITOPlus := function(t,n,p,e,gens,imgens,factoword,graph)
  if n ne 8 then graph := false; end if;
  t1 := t[1];
  if t1 ne 0 then
    t[1]:=0;
    elt := $$(t,n,p,e,gens,Prune(imgens),factoword,false);
    if t1 eq 3 then return imgens[#imgens]*elt; end if;
    return imgens[#imgens]^2*elt;
  end if;
  if graph then Prune(~imgens); end if;
  if p eq 2 then
    return ITO(t,n,p,e,gens,imgens,factoword : gp:=GOPlus);
  end if;
  ng := #imgens;
  elt := Identity(Parent(imgens[1]));
  if e gt 1 then
    if t[2] ne 0 then elt *:= imgens[ng]^t[2]; end if;
    ng -:= 1;
  end if;
  //find form scaling factor
  isit, form := SymmetricBilinearForm(GOPlus(n,p^e));
  formim := t[3] * form * Transpose(t[3]);
  for i in [1..n] do if form[1][i] ne 0 then
    scal := formim[1][i]/form[1][i];
    assert formim eq scal * form;
    break;
  end if; end for;
  isp, scalrt := IsPower(scal,2);
  if not isp then
    elt *:= imgens[ng];
    t[3] := gens[ng]^-1 * t[3];
    formim := t[3] * form * Transpose(t[3]);
    for i in [1..n] do if form[1][i] ne 0 then
      scal := formim[1][i]/form[1][i];
      assert formim eq scal * form;
      break;
    end if; end for;
    isp, scalrt := IsPower(scal,2); assert isp;
  end if;
  t[3] := t[3] * GL(n,p^e)!ScalarMatrix(n,scalrt^-1);
  ng -:= 1;

  if Determinant(t[3]) ne 1 then
    elt *:= imgens[ng];
    t[3] := gens[ng]^-1 * t[3];
  end if;
  ng -:= 1;
  
  d8 := n mod 4 eq 0 or p^e mod 4 eq 1;
  if SpinorNorm(GL(n,p^e)!t[3], form) eq 1 then
    if d8 then
      elt *:= imgens[ng];
      t[3] := gens[ng]^-1 * t[3];
    else t[3] := -t[3];
    end if;
  end if;
  wd := factoword(t[3]);
  elt *:= Evaluate(wd,imgens);
  return elt;
end function;

ITOMinus := function(t,n,p,e,gens,imgens,factoword)
  if p eq 2 then
    return ITO(t,n,p,e,gens,imgens,factoword : gp:=GOMinus);
  end if;
  ng := #imgens;
  elt := Identity(Parent(imgens[1]));
  if e gt 1 then
    if t[2] ne 0 then elt *:= imgens[ng]^t[2]; end if;
    ng -:= 1;
  end if;
  //find form scaling factor
  isit, form := SymmetricBilinearForm(GOMinus(n,p^e));
  formim := t[3] * form * Transpose(t[3]);
  for i in [1..n] do if form[1][i] ne 0 then
    scal := formim[1][i]/form[1][i];
    assert formim eq scal * form;
    break;
  end if; end for;
  isp, scalrt := IsPower(scal,2);
  if not isp then
    elt *:= imgens[ng];
    t[3] := gens[ng]^-1 * t[3];
    formim := t[3] * form * Transpose(t[3]);
    for i in [1..n] do if form[1][i] ne 0 then
      scal := formim[1][i]/form[1][i];
      assert formim eq scal * form;
      break;
    end if; end for;
    isp, scalrt := IsPower(scal,2); assert isp;
  end if;
  t[3] := t[3] * GL(n,p^e)!ScalarMatrix(n,scalrt^-1);
  ng -:= 1;

  if Determinant(t[3]) ne 1 then
    elt *:= imgens[ng];
    t[3] := gens[ng]^-1 * t[3];
  end if;
  ng -:= 1;
  
  d8 := n mod 4 eq 2 and p^e mod 4 eq 3;
  if SpinorNorm(GL(n,p^e)!t[3], form) eq 1 then
    if d8 then
      elt *:= imgens[ng];
      t[3] := gens[ng]^-1 * t[3];
    else t[3] := -t[3];
    end if;
  end if;
  wd := factoword(t[3]);
  elt *:= Evaluate(wd,imgens);
  return elt;
end function;

PermRepSum := function(G,reps)
/* reps should be a list of homomorphisms from group G to permutation
 * groups (subgroups of Sym(n_i)). The summed permutation representation
 * reps[1]+..resp[r] of degree n_1+n_2+..n_r is returned, together
 * with the image group.
 */
  local nreps, degrees, phi, cdphi, img, sumdeg, deg, im;
  nreps := #reps;
  degrees := [];
  sumdeg := 0;
  for j in [1..nreps] do
    phi:=reps[j];
    cdphi :=  Codomain(phi);
    degrees[j]:=Degree(cdphi);
    sumdeg +:= degrees[j];
  end for;
  deg:=sumdeg;

  //The codomain of the summed representation will be the direct product of the
  //codomains of the given maps.

  ImRep := function(g)
    local img, sumdeg, r;
    img:=[];
    sumdeg:=0;
    for j in [1..nreps]  do
      r := g @ reps[j];
      for k in [1..degrees[j]] do
        img[sumdeg+k] := sumdeg + k^r;
      end for;
      sumdeg +:= degrees[j];
    end for;
    return Sym(deg)!img;
  end function;

  im := sub< Sym(deg) | [ ImRep(G.i) : i in [1..Ngens(G)]] >;
  return map< Generic(G) -> im  | g :-> ImRep(g) >, im;

end function;

//forward GetRQRadModActions;
GetRadquot := procedure(G : warning:=false )
  local r, factortype, socperm, Gtosocperm, sfclass, fromfacs, tofacs, ims,
   cslen, socfacs, O, homs, oa, oi, opts, T, isc, g, sfno, sf, ai, sfc,
   d, q, fac, p, e, imgp, injb, injt, m, im, wg, iwm, factoword, aggens,
   graph, P, em, oa2, oi2, imm, fromfac, tofac, factowd, Y, totdeg;
  if warning then
    vprint LMG, 1:
 "Warning: we will need to find a permutation reptn of the radical quotient!";
  end if;

  r := G`LMGNode;
  factortype := r`factortype;
  socperm := r`socperm;
  Gtosocperm := r`Gtosocperm;
  sfclass := r`sfclass;
  fromfacs := r`fromfacs;
  tofacs := r`tofacs;
  factoword := r`factoword;
  ims := r`ims;
  Y := r`Y;
  cslen := #factortype;
  socfacs := [ i : i in [1..cslen] | factortype[i] eq 2 ];
  if socfacs eq [] then
    im := Sym(1);
    G`LMGNode`radquot := im;
    G`LMGNode`Gtoradquot := map< Generic(G)->im | g :-> Id(im), g:-> Id(G) >;
    G`LMGNode`iwmrq := InverseWordMap(im);
  /* won't always do commands below at this stage, but do it for now */
    _:=LMGChiefSeries(G);
    if warning then
      vprint LMG, 1:
       "Found permutation reptn of radical quotient of degree", Degree(im);
    end if;
    return;
  end if;
  O := Orbits(socperm);
  homs := [* *];
  totdeg := 0;
  for o in O do
    oa, oi := OrbitAction(socperm, o);
    //We will order the points on o to correspond to those in oi
    opts := [ i @@ oa : i in [1..#o] ];
    T := [ Generic(G) | Id(G)];
    for i in [2..#o] do
      isc, g := IsConjugate(socperm, opts[1], opts[i]);
      T[i] := g @@ Gtosocperm;
    end for;
    //construct target group for homomorphism
    sfno := socfacs[ o[1] ];
    sf := ims[sfno]; //the socle factor for this orbit
    if not assigned sf`AutInfo then
      if Type(sf) eq GrpMat and RecogniseClassical(sf) cmpeq true then
        InitialiseAutInfoC(sf);
      else InitialiseAutInfoG(sf);
      end if;
    end if;
    ai := sf`AutInfo;
    sfc := sfclass[ o[1] ];
    if sfc then //classical type
      vprint LMG, 1: "Classical type composition factor";
      vprint LMG, 1: "Classical type composition factor";
      if ai`type ne "L" then
        //put it into Magma's form
        mat := TransformForm(ims[sfno]);
        sf := ims[sfno]^mat;
        tofac := map< Domain(tofacs[sfno])->sf |
                                   x :-> (x @ Function(tofacs[sfno]))^mat >;
        fromfac := map< sf->Codomain(fromfacs[sfno]) |
                            x :-> (x^(mat^-1)) @ Function(fromfacs[sfno]) >;
        factowd := map< sf->Codomain(factoword[sfno]) |
                           x :-> (x^(mat^-1)) @ Function(factoword[sfno]) >;
      else 
        tofac := map< Domain(tofacs[sfno])->sf |
                                      x :-> x @ Function(tofacs[sfno]) >;
        fromfac := map< sf->Codomain(fromfacs[sfno]) |
                                    x :-> x @ Function(fromfacs[sfno]) >;
        factowd := map< sf->Codomain(factoword[sfno]) |
                                   x :-> x @ Function(factoword[sfno]) >;
      end if;
      InitialiseAutInfoC(sf);
      sf`AutInfo`fmat := (sf`AutInfo`fmat)^0;
      //we have already made it fix Magma's form, and this makes life easier.
      ai := sf`AutInfo;
      d := Dimension(sf);
      q := #BaseRing(sf);
      if q^d gt 10^9 then
       error "Degree of permutation representation of radical quotient too big";
      end if;
      fac := Factorisation(q);
      p := fac[1][1]; e := fac[1][2];
      if ai`type eq "U" then e := e div 2; end if;
      gens := [GL(d,q) | sf.i : i in [1..Ngens(sf)]];
      cmat := ai`type eq "O-" and e gt 1 select ai`cmat[1] else Id(GL(d,q));
      case ai`type:
        when "L": ag, gens := AutSL(d,p,e,gens);
        when "U": ag, gens := AutSU(d,p,e,gens);
        when "S": ag, gens := AutSp(d,p,e,gens);
        when "O": ag, gens := AutO(d,p,e,gens);
        when "O+": ag, gens := AutOPlus(d,p,e,gens);
        when "O-": ag, gens := AutOMinus(d,p,e,gens,cmat);
      end case;
    else
      ag := Image(ai`atopgp); 
      d:=0; p:=0; e:=0; gens:=0; //not sure why that should be necessary!
      tofac := tofacs[sfno];
      fromfac := fromfacs[sfno];
      factowd := factoword[sfno];
    end if;
    aggens := [ ag.i : i in [1..Ngens(ag)] ];
    totdeg +:= Degree(ag) * Degree(oi);
    if totdeg ge 2^31 then
      error "Degree of permutation representation of radical quotient too big";
    end if;
    imgp, injb, injt := WreathProduct(ag, oi);
    ImElt := function(g) //image of an element g in G under map to imgp
      local im, el, atup, genims, o8plus, gaut, gsfi, genims1, genims2,
            SS, rq, A, em, P, Strip;
      Strip := function(x,g)
          //x in sf. g should normalise sf, but x^g could have higher terms
          //in comp series, that have fallen through to the radical
          //so we need to strip them off
        local conx, imnode, ww;
        conx := x^g;
        imnode := CompositionTreeFactorNumber( G, conx ) - 1;
        assert factortype[imnode] le 2;
        while factortype[imnode] eq 1 do
            ww := (conx^-1) @
                Function(tofacs[imnode]) @ Function(factoword[imnode]);
            conx *:= Evaluate( ww, Y[imnode] );
            imnode := CompositionTreeFactorNumber( G, conx ) - 1;
            assert factortype[imnode] le 2;
        end while;
        return conx;
      end function;

      im := g @ Gtosocperm @ oa @ injt;
      for i in [1..#o] do
        el := (T[i] * g^-1) @ Gtosocperm @ oa;
        el := T[ 1^el ] * g * T[i]^-1;
         //should normalise socle factor after stripping
        genims :=
     [ Strip(sf.i @ Function(fromfac),el) @ Function(tofac) :
                                                        i in [1..Ngens(sf)] ];
        if sfc then
          o8plus := ai`type eq "O+" and Dimension(sf) eq 8;
           if o8plus then
            gaut := ai`gaut;
            gsfi := [ gaut(sf.i) @ Function(fromfac)
                     : i in [1..Ngens(sf)] ];
            genims1 := [ Strip(x,el) @ Function(tofac) : x in gsfi ];
            gsfi := [ gaut(gaut(sf.i)) @ Function(fromfac)
                     : i in [1..Ngens(sf)] ];
            genims2 := [ Strip(x,el) @ Function(tofac) : x in gsfi ];
          else genims1:=[]; genims2:=[];
          end if;
          atup := AutTuple(sf, genims : genims1:=genims1, genims2:=genims2);
          case ai`type:
           when "L": gaut := ITSL(atup,d,p,e,gens,aggens,factowd,true);
           when "U": gaut := ITSU(atup,d,p,e,gens,aggens,factowd);
           when "S": gaut := ITSp(atup,d,p,e,gens,aggens,factowd,true);
           when "O": gaut := ITO(atup,d,p,e,gens,aggens,factowd);
           when "O+":gaut := ITOPlus(atup,d,p,e,gens,aggens,factowd,true);
           when "O-":
                     if atup[2] ne 0 then
                        atup[3] := ai`cmat[atup[2]]^-1 * atup[3];
                     end if;
                     gaut := ITOMinus(atup,d,p,e,gens,aggens,factowd);
          end case;
        else
          if Type(sf) eq GrpMat then
             SS := sf`AutInfo`radquot;
             rq := sf`AutInfo`radhom;
             genims := [ x@rq : x in genims ];
           else
             SS := sf;
           end if;
           A := sf`AutInfo`autgp;
           if assigned sf`AutInfo`gtopgp then
             em := sf`AutInfo`gtopgp;
             P := sf`AutInfo`pgp;
             gaut := IdentifyEmbeddedAut(
       sub< P | [SS.i @ em : i in [1..Ngens(SS)]] >, P, [g@em : g in genims] );
           else gaut := A!hom< SS -> SS | genims >;
           end if;
           gaut := gaut @ sf`AutInfo`atopgp;
        end if;
        im *:= gaut @ injb[i];
      end for;
      return im;
    end function;

    //if image intransitive go to orbit
    m := hom< Generic(G) -> imgp | g :-> ImElt(g) >;
    imm :=  sub< imgp | [m(G.i) : i in [1..Ngens(G)]] >;
    if not IsTransitive(imm) then
      oa2, oi2 := OrbitAction( imm, Orbits(imm)[1] );
      Append( ~homs, map< Generic(G)->oi2 | g :-> ImElt(g) @ oa2 > );
    else Append( ~homs, map< Generic(G)->imgp | g :-> ImElt(g) > );
    end if;
  end for; //for o in O do

  m, im := PermRepSum(G,homs);
  //also need inverse map
  wg := WordGroup(im); iwm := InverseWordMap(im);
  G`LMGNode`Gtoradquot := map< Generic(G)->im | g :-> m(g),
                      g :-> Evaluate( iwm(g), [G.i : i in [1..Ngens(G)]] ) >;
  G`LMGNode`radquot := im;
  G`LMGNode`iwmrq := iwm;
  /* won't always do commands below at this stage, but do it for now */
  _:=LMGChiefSeries(G);
  if warning then
    vprint LMG, 1:
     "Found permutation reptn of radical quotient of degree", Degree(im);
  end if;
end procedure;

/* This doesn't seem to help much!
GetRQRadModActions := procedure(G)
  local r, iwmrq, Gtorq, rm, gmacts, radtoPC, rqmacts, len, ff;
  r := G`LMGNode;
  iwmrq := r`iwmrq;
  Gtorq := r`Gtoradquot;
  rm := r`radmods;
  gmacts := r`genmodactions;
  radtoPC := r`radtoPC;
  rqrmacts := [**];
  len := #(r`cseriesrad);
  for i in [1..len-1] do
    ff := function(g:im:=0 )
      local wd, ans, img, gg;
      img := im cmpeq 0 select Gtorq(g) else im;
      wd := iwmrq(img);
      ans := Evaluate(wd, gmacts[i] );
      if rm[i][4] then //trivial action of rad on module
         return ans;
      end if;
      gg := Evaluate(wd, [G.i: i in [1..Ngens(G)]]);
      ans *:= Generic(Parent(ans))!( (gg^-1*g) @ radtoPC @ rm[i][3] );
      return ans;
    end function;
    Append(~rqrmacts, ff);
  end for;

  G`LMGNode`rqradmodactions := rqrmacts;
end procedure;
*/

GetRadquotPermGp := function(G,N)
//perm rep of G/NRad(G)
  local r, factortype, socperm, Gtosocperm, sfclass, fromfacs, tofacs, socfacs,
   im, ims, cslen,  O, homs, oa, oi, opts, T, isc, g, sfno, sf, ai, sfc,
   d, q, fac, p, e, imgp, injb, injt, m,  wg, iwm, factoword, aggens, mat,
   graph, P, em, oa2, oi2, imm, fromfac, tofac, factowd, Q, pQ, S, QN, SA;

  Q, pQ := RadicalQuotient(G);
  if #Q eq 1 then
    im := Sym(1);
    return im, map<G->im | x:->im.0, x:->G.0>;
  end if;
  QN := pQ(N);
  S := Socle(Q);
  socfacs := SocleFactors(Q);
  SA, socperm := SocleAction(Q);
  Gtosocperm := pQ*SA;

  O := Orbits(socperm);
  homs := [* *];
  for o in O do
    if socfacs[o[1]] subset QN then continue; end if;
    oa, oi := OrbitAction(socperm, o);
    //We will order the points on o to correspond to those in oi
    opts := [ i @@ oa : i in [1..#o] ];
    T := [ Generic(G) | Id(G)];
    for i in [2..#o] do
      isc, g := IsConjugate(socperm, opts[1], opts[i]);
      T[i] := g @@ Gtosocperm;
    end for;
    //construct target group for homomorphism
    sfno := o[1];
    socfac := socfacs[sfno];
    _ := CompositionTree(socfac);
    _, tofacs, fromfacs, factoword := CompositionTreeSeries(socfac);
    assert #tofacs eq 1;
    ims := [* Codomain(t) : t in tofacs *];
    sf := ims[1];
    
    if Type(sf) eq GrpMat and RecogniseClassical(sf) cmpeq true then
      vprint LMG, 1: "Classical type composition factor";
      //put it into Magma's form
      sfc:=true; InitialiseAutInfoC(sf);
      ai := sf`AutInfo;
      if ai`type ne "L" then
        mat := TransformForm(ims[1]);
        sf := ims[1]^mat;
        tofac := map< socfac->sf | x :-> (x @ Function(tofacs[1]))^mat >;
        fromfac :=
          map< sf->socfac | x :-> (x^(mat^-1)) @ Function(fromfacs[1]) >;
        factowd := map< sf->Codomain(factoword[1]) |
                           x :-> (x^(mat^-1)) @ Function(factoword[1]) >;
        InitialiseAutInfoC(sf);
        sf`AutInfo`fmat := (sf`AutInfo`fmat)^0;
      //we have already made it fix Magma's form, and this makes life easier.
      else
        tofac := map< socfac->sf | x :-> x @ Function(tofacs[1]) >;
        fromfac :=
               map< sf->socfac | x :-> x @ Function(fromfacs[1]) >;
        factowd := map< sf->Codomain(factoword[1]) |
                                x :-> x @ Function(factoword[1]) >;
      end if;
    else vprint LMG, 1: "Non classical type composition factor"; 
      sf := ims[1];
      tofac := tofacs[1];
      fromfac := fromfacs[1];
      factowd := factoword[1];
      sfc:=false; InitialiseAutInfoG(sf);
    end if;
    ai := sf`AutInfo;
    if sfc then //classical type
      ai := sf`AutInfo;
      d := Dimension(sf);
      q := #BaseRing(sf);
      fac := Factorisation(q);
      p := fac[1][1]; e := fac[1][2];
      if ai`type eq "U" then e := e div 2; end if;
      gens := [GL(d,q) | sf.i : i in [1..Ngens(sf)]];
      cmat := ai`type eq "O-" and e gt 1 select ai`cmat[1] else Id(GL(d,q));
      case ai`type:
        when "L": ag, gens := AutSL(d,p,e,gens);
        when "U": ag, gens := AutSU(d,p,e,gens);
        when "S": ag, gens := AutSp(d,p,e,gens);
        when "O": ag, gens := AutO(d,p,e,gens);
        when "O+": ag, gens := AutOPlus(d,p,e,gens);
        when "O-": ag, gens := AutOMinus(d,p,e,gens,cmat);
      end case;
    else
      ag := Image(ai`atopgp); 
      d:=0; p:=0; e:=0; gens:=0; //not sure why that should be necessary!
    end if;
    aggens := [ ag.i : i in [1..Ngens(ag)] ];
    imgp, injb, injt := WreathProduct(ag, oi);
    ImElt := function(g) //image of an element g in G under map to imgp
      local im, el, atup, genims, o8plus, gaut, gsfi, genims1, genims2,
            SS, rq, A, em, P;
      im := g @ Gtosocperm @ oa @ injt;
      for i in [1..#o] do
        el := (T[i] * g^-1) @ Gtosocperm @ oa;
        el := (T[ 1^el ] * g * T[i]^-1) @ pQ; //should normalise socle factor
        genims :=
     [ ((sf.i @ Function(fromfac))^el) @ Function(tofac) :
                                                        i in [1..Ngens(sf)] ];
        if sfc then
          o8plus := ai`type eq "O+" and Dimension(sf) eq 8;
           if o8plus then
            gaut := ai`gaut;
            gsfi := [ gaut(sf.i) @ Function(fromfac)
                     : i in [1..Ngens(sf)] ];
            genims1 := [ (x^el) @ Function(tofac) : x in gsfi ];
            gsfi := [ gaut(gaut(sf.i)) @ Function(fromfac)
                     : i in [1..Ngens(sf)] ];
            genims2 := [ (x^el) @ Function(tofac) : x in gsfi ];
          else genims1:=[]; genims2:=[];
          end if;
          atup := AutTuple(sf, genims : genims1:=genims1, genims2:=genims2);
          case ai`type:
           when "L": gaut := ITSL(atup,d,p,e,gens,aggens,factowd,true);
           when "U": gaut := ITSU(atup,d,p,e,gens,aggens,factowd);
           when "S": gaut := ITSp(atup,d,p,e,gens,aggens,factowd,true);
           when "O": gaut := ITO(atup,d,p,e,gens,aggens,factowd);
           when "O+":gaut := ITOPlus(atup,d,p,e,gens,aggens,factowd,true);
           when "O-":
                     if atup[2] ne 0 then
                        atup[3] := ai`cmat[atup[2]]^-1 * atup[3];
                     end if;
                     gaut := ITOMinus(atup,d,p,e,gens,aggens,factowd);
          end case;
        else
          if Type(sf) eq GrpMat then
             SS := sf`AutInfo`radquot;
             rq := sf`AutInfo`radhom;
             genims := [ x@rq : x in genims ];
           else
             SS := sf;
           end if;
           A := sf`AutInfo`autgp;
           if assigned sf`AutInfo`gtopgp then
             em := sf`AutInfo`gtopgp;
             P := sf`AutInfo`pgp;
             gaut := IdentifyEmbeddedAut(
       sub< P | [SS.i @ em : i in [1..Ngens(SS)]] >, P, [g@em : g in genims] );
           else gaut := A!hom< SS -> SS | genims >;
           end if;
           gaut := gaut @ sf`AutInfo`atopgp;
        end if;
        im *:= gaut @ injb[i];
      end for;
      return im;
    end function;

    //if image intransitive go to orbit
    m := hom< Generic(G) -> imgp | g :-> ImElt(g) >;
    imm :=  sub< imgp | [m(G.i) : i in [1..Ngens(G)]] >;
    if not IsTransitive(imm) then
      oa2, oi2 := OrbitAction( imm, Orbits(imm)[1] );
      Append( ~homs, map< Generic(G)->oi2 | g :-> ImElt(g) @ oa2 > );
    else Append( ~homs, map< Generic(G)->imgp | g :-> ImElt(g) > );
    end if;
  end for; //for o in O do

  if #QN gt 1 then
    //also need socle quotient
    SQ, SQact := SocleQuotient(Q); 
    SQN := SQact(pQ(N));
    if #SQN eq 1 then Append(~homs,pQ*SQact);
    else _,SQQact := quo< SQ | SQN >;
      Append(~homs,pQ*SQact*SQQact);
    end if;
  end if;

  m, im := PermRepSum(G,homs);
  //also need inverse map
  iwm := InverseWordMap(im);
  return im, map< Generic(G)->im | g :-> m(g),
                      g :-> Evaluate( iwm(g), [G.i : i in [1..Ngens(G)]] ) >;
end function;
