freeze;

/* This is a new version of LowIndexNormalSubgroups, revised by Derek Holt,
 * which uses Homomorphisms rather than LowIndexSubgroups to find minimal
 * TF-images.
 * Recall, a TF-group is one with trivial soluble radical, and a minimal
 * TF-group is one with a unique minimal normal subgroup, which is
 * necessarily a direct product of isomorphic nonabelian simple groups.
 * MaxLINSIndex is the largest index for which the program is guaranteed to
 * find all normal subgroups up to that index.
 * To extend the range of the function to larger indexes, it is necessary
 * (i) to adjoin extra Homomorphism commands in the procedure FindTs
 *     for the new minimal TF-groups with indexes less than MaxLINSIndex.
 * (ii) For the simple groups in the minimal TF-groups that have nontrivial
 *      Schur multipliers, adjoin their orders to the lists of such groups
 *      in the procedure MustCheckP.
 */

MaxLINSIndex := 500000;

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


GModuleH:=function(G,K,p)
//K normal in FP-group G, p prime. Alternative version of GModule.
  local P, phi, d, mats, mat, vec, M, psi, Z;

  P, phi := pQuotient(K, p, 1);
  // P, phi := ElementaryAbelianQuotient(K, p);
  d := #P eq 1 select 0 else FactoredOrder(P)[1][2];
  mats := [];
  for g in [G.i : i in [1..Ngens(G)]] do
    mat := [];
    for i in [1..d] do
      vec := (g^-1*(P.i@@phi)*g)@phi;
      Append(~mat, ElementToSequence(vec));
    end for;
    Append(~mats, Matrix(GF(p), d, d, mat));
  end for;
  Z := Integers();
  M := GModule(G, mats);
  psi := map<K->M | k :-> M!(ElementToSequence(k@phi)),
                  m :-> (&*[P.i^(Z!m[i]) : i in [1..d]]) @@ phi>;
  return M, psi;
end function;

PullBackH:=function(psi,S)
//Inverse image of submodule S under map psi returned by GModuleH
  local K, M, Q, rho, O, d, h;
  K:=Domain(psi);
  M:=Codomain(psi);
  Q, rho:=quo<M|S>;
  O:={@ q:q in Q @};
  d:=#O;
  h:=hom<K->Sym(d)|
[[Position(O,O[j]+(K.i@psi@rho)) : j in [1..d]] : i in [1..Ngens(K)]]>;
  return sub<K|h>;
end function;

MaximalSubmodulesH := function(M, r)
//submodules of M of codimension up to r such that quotient is irreducible
  D := Dual(M);
  S := Socle(D);
  C := Constituents(S);
  V := VectorSpace(D);
  subs := [];
  for c in [c: c in C | Dimension(c) le r] do
    min := MinimalSubmodules(S,c);
    for m in min do
      mr := Morphism(m,D);
      U := sub<V| [V| mr(m.i): i in [1..Dimension(m)]] >;
      OU:=OrthogonalComplement(V,U);
      Append(~subs, sub<M|OU>);
    end for;
  end for;
  return subs;
end function;

AddGroup:=procedure(~GroupsFound, H, Supers, ~place, PrintLevel, Simplify)
  local G, i, j, new, NewGroup, A, B;
  G:=GroupsFound[1]`Group;
  if Simplify eq "No" then
    H:=Rewrite(G, H:Simplify:=false);
  elif Simplify eq "Yes" then
    H:=Rewrite(G, H:Simplify:=true);
  elif Simplify eq "LengthLimit" then
  //"Putting it in:",Index(G,H);
    H:=Rewrite(G, H:LengthLimit:=Index(G,H));
  else
    H:=Rewrite(G,H);
  end if;
  i:=Index(G,H);
  if PrintLevel gt 1 then
    "  Adding group of index", i;
  end if;
  j:=1;
  new:=true;
//subgroups are ordered by index. Insert new subroup in correct place.
  while (j le #GroupsFound) and (GroupsFound[j]`Index le i) do
    if (GroupsFound[j]`Index eq i) then
      if GroupsFound[j]`Group eq H then
        new:=false;
        if PrintLevel gt 1 then
          "  Group had already been found";
        end if;
        GroupsFound[j]`Supergroups:=GroupsFound[j]`Supergroups join Supers;
        place:=j;
        return;
      end if;
    end if;
    j:=j+1;
  end while;
  if new then
    NewGroup:=rec< recformat<Group,Index,Supergroups,TriedPrimes> |
                Group:=H,Index:=i,Supergroups:=Supers,TriedPrimes:={}>;
    place:=j;
    Insert(~GroupsFound, j, j-1, [NewGroup]);
//adjust lists of supergroups now that numbering has changed
    while j le #GroupsFound do
      A:={i:i in [1..place-1] | i in GroupsFound[j]`Supergroups};
      B:={i+1:i in (GroupsFound[j]`Supergroups diff A)};
      GroupsFound[j]`Supergroups:=A join B;
      j:=j+1;
    end while;
//find supergroups of new subgroup
    for i:=1 to (place - 1) do
      if not(i in GroupsFound[place]`Supergroups) then
        if forall{x: x in Generators(GroupsFound[place]`Group) |
                     x in GroupsFound[i]`Group} then
          Include(~GroupsFound[place]`Supergroups, i);
        end if;
      end if;
    end for;
//find groups for which new entry is a supergroup
    for i:=(place+1) to #GroupsFound do
      if not(place in GroupsFound[i]`Supergroups) then
        if(GroupsFound[i]`Index mod GroupsFound[place]`Index eq 0) then
          if forall{x: x in Generators(GroupsFound[i]`Group) |
                       x in GroupsFound[place]`Group} then
            Include(~GroupsFound[i]`Supergroups, place);
          end if;
        end if;
      end if;
    end for;
  end if;
end procedure;

FindTs:=procedure(~GroupsFound, n, PrintLevel, Simplify)
  local G, targets, place, hh, L, LL, X, M, Q, phi, S;
  /* targets is a list of triples <I,A,i> where I is a minimal TF-group,
   * A=Aut(I), i = #I. For those targets with i <= index, we will call
   * Homomorphisms(G, I, A) and their kernels will be new normal subgroups.
   * To extend range of algorithm add new entries to targets.
   */
  targets := [ < Alt(5), Sym(5), 60 >,
               < Sym(5), Sym(5), 120 >,
               < PSL(2,7), PGL(2,7), 168 >,
               < PGL(2,7), PGL(2,7), 336 > ];
  L := LowIndexSubgroups(PGammaL(2,9),<2,2>);
  targets cat:= [ < PSL(2,9), PGammaL(2,9), 360 >,
                  < L[1], PGammaL(2,9), 720 >,
                  < L[2], PGammaL(2,9), 720 >,
                  < L[3], PGammaL(2,9), 720 >,
                  < PGammaL(2,9), PGammaL(2,9), 1440 >,
                  < PSL(2,8), PGammaL(2,8), 504>,
                  < PGammaL(2,8), PGammaL(2,8), 1512>,
                  < PSL(2,11), PGL(2,11), 660 >,
                  < PGL(2,11), PGL(2,11), 1320 >,
                  < PSL(2,13), PGL(2,13), 1092 >,
                  < PGL(2,13), PGL(2,13), 2184 >,
                  < PSL(2,17), PGL(2,17), 2448 >,
                  < PGL(2,17), PGL(2,17), 4896 >,
                  < Alt(7), Sym(7), 2520 >,
                  < Sym(7), Sym(7), 5040 >,
                  < PSL(2,19), PGL(2,19), 3420 >,
                  < PGL(2,19), PGL(2,19), 6840 > ];
  L := LowIndexSubgroups(PGammaL(2,16), <2,2>);
  targets cat:= [ < PSL(2,16), PGammaL(2,16), 4080 >,
                  < L[1], PGammaL(2,16), 8160 >,
                  < PGammaL(2,16), PGammaL(2,16), 16320 > ];
  X := WreathProduct(Sym(5),CyclicGroup(2));
  L := LowIndexSubgroups(X, <4,4>);
  targets cat:= [ < l, Normaliser(X,l), 7200 > : l in L |
                                             #MinimalNormalSubgroups(l) eq 1 ];
  L := LowIndexSubgroups(X, <2,2>);
  targets cat:= [ < l, X, 14400 > : l in L | #MinimalNormalSubgroups(l) eq 1 ];
  targets cat:= [ < X, X, 28800 >,
                  < Socle(PSL2(3,3)), PSL2(3,3), 5616 >,
                  < PSL2(3,3), PSL2(3,3), 11232>,
                  < PSU(3,3), PGammaU(3,3), 6048>,
                  < PGammaU(3,3), PGammaU(3,3), 12096>,
                  < PSL(2,23), PGL(2,23), 6072 >,
                  < PGL(2,23), PGL(2,23), 12144 > ];
  L := LowIndexSubgroups(PGammaL(2,25),<2,2>);
  targets cat:= [ < PSL(2,25), PGammaL(2,25), 7800 >,
                  < L[1], PGammaL(2,25), 15600 >,
                  < L[2], PGammaL(2,25), 15600 >,
                  < L[3], PGammaL(2,25), 15600 >,
                  < PGammaL(2,25), PGammaL(2,25), 31200 > ];
G:=PermutationGroup<11 | \[10,8,11,4,7,6,5,2,9,1,3],
\[4,11,3,7,5,1,6,8,2,9,10]>;
  L := LowIndexSubgroups(PGammaL(2,27), <3,3>);
  LL := LowIndexSubgroups(PGammaL(2,27), <2,2>);
  targets cat:= [ < G, G, 7920 >, //M11
                  < PSL(2,27), PGammaL(2,27), 9828 >,
                  < L[1], PGammaL(2,27), 19656 >,
                  < LL[1], PGammaL(2,27), 29484 >,
                  < PGammaL(2,27), PGammaL(2,27), 58968 >,
                  < PSL(2,29), PGL(2,29), 12180 >,
                  < PGL(2,29), PGL(2,29), 24360 >,
                  < PSL(2,31), PGL(2,31), 14880 >,
                  < PGL(2,31), PGL(2,31), 29760 > ];
 if n ge 20000 then
  targets cat:= [ < Alt(8), Sym(8), 20160 >,
                  < Sym(8), Sym(8), 40320 > ];
  X := PGammaL2(3,4);
  targets cat:= [ < Socle(X), X, 20160 > ];
  L := LowIndexSubgroups(X, <6,6>);
  targets cat:= [ < l, Normaliser(X,l), 40320 > : l in L ];
  L := LowIndexSubgroups(X, <4,4>);
  targets cat:= [ < L[1], X, 60480 > ];
  L := LowIndexSubgroups(X, <3,3>);
  targets cat:= [ < L[1], Normaliser(X,L[1]), 80640 > ];
  L := LowIndexSubgroups(X, <2,2>);
  targets cat:= [ < l, X, 120960 > : l in L ];
  targets cat:= [ < X, X, 241920 >,
                  < PSL(2,37), PGL(2,37), 25308 >,
                  < PGL(2,37), PGL(2,37), 50616 >,
                  < PSU(4,2), PGammaU(4,2), 25920>,
                  < PGammaU(4,2), PGammaU(4,2), 51480> ];
  X:=PermutationGroup(AutomorphismGroup(PSz(8)));
  X:=CosetImage(X,Normaliser(X,Sylow(X,2)));
  targets cat:= [ < Socle(X), X, 29120 >,
                  < X, X, 87360>,
                  < PSL(2,32), PGammaL(2,32), 32736>,
                  < PGammaL(2,32), PGammaL(2,32), 163680>,
                  < PSL(2,41), PGL(2,41), 34440 >,
                  < PGL(2,41), PGL(2,41), 68880 >,
                  < PSL(2,43), PGL(2,43), 39732 >,
                  < PGL(2,43), PGL(2,43), 79464 >,
                  < PSL(2,47), PGL(2,47), 51888 >,
                  < PGL(2,47), PGL(2,47), 103776 > ];
 if n ge 52000 then
  X := WreathProduct(PGL(2,7),CyclicGroup(2));
  L := LowIndexSubgroups(X, <4,4>);
  targets cat:= [ < l, Normaliser(X,l), 56448 > : l in L |
                                             #MinimalNormalSubgroups(l) eq 1 ];
  L := LowIndexSubgroups(X, <2,2>);
  targets cat:= [ < l, X, 112896 > : l in L | #MinimalNormalSubgroups(l) eq 1 ];
  targets cat:= [ < X, X, 225792 > ];
  L := LowIndexSubgroups(PGammaL(2,49),<2,2>);
  targets cat:= [ < PSL(2,49), PGammaL(2,49), 58800 >,
                  < L[1], PGammaL(2,49), 117600 >,
                  < L[2], PGammaL(2,49), 117600 >,
                  < L[3], PGammaL(2,49), 117600 >,
                  < PGammaL(2,49), PGammaL(2,49), 235200 > ];
  X := PGammaU(3,4);
  L := LowIndexSubgroups(X, <2,2>);
  targets cat:= [ < Socle(X), X, 62400 >,
                  < L[1], X, 124800 >,
                  < X, X, 249600 >,
                  < PSL(2,53), PGL(2,53), 74412 >,
                  < PGL(2,53), PGL(2,53), 148824 > ];
  G:=sub<Sym(24)|(1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,24),
    (2,16,9,6,8)(3,12,13,18,4)(7,17,10,11,22)(14,19,21,20,15),
  (1,22)(2,11)(3,15)(4,17)(5,9)(6,19)(7,13)(8,20)(10,16)(12,21)(14,18)(23,24)>;
  M:=MaximalSubgroups(G);
  X:=[m`subgroup: m in M|m`order eq 190080][1];
  targets cat:= [ < Socle(X), X, 95040 >,
                  < X, X, 190080 > ];
 if n ge 100000 then
  targets cat:= [ < PSL(2,59), PGL(2,59), 102660 >,
                  < PGL(2,59), PGL(2,59), 205320 >, 
                  < PSL(2,61), PGL(2,61), 113460 >,
                  < PGL(2,61), PGL(2,61), 226920 >, 
                  < PSU(3,5), PGammaU(3,5), 126000 >,
                  < PSigmaU(3,5), PSigmaU(3,5), 252000 >,
                  < PGU(3,5), PGammaU(3,5), 378000 >,
                  < PGammaU(3,5), PGammaU(3,5), 756000 > ];
  targets cat:= [ < PSL(2,67), PGL(2,67), 150348 >,
                  < PGL(2,67), PGL(2,67), 300696 > ]; 
G := PermutationGroup<266 |  //J1  
\[262,107,21,213,191,22,133,234,232,151,139,176,202,253,222,
16,195,206,68,55,3,6,179,217,216,256,87,70,131,44,105,170,
77,104,198,137,243,56,124,223,134,42,174,30,45,51,128,94,
250,264,46,183,231,115,20,38,85,233,261,95,235,177,249,91,
247,155,67,19,219,28,237,211,84,192,130,251,33,78,260,112,
193,156,242,73,57,238,27,143,168,148,64,119,212,48,60,150,
199,140,189,180,147,111,159,34,31,162,2,194,166,200,102,80,
120,141,54,182,181,225,92,113,254,125,146,39,122,208,221,47,
210,75,29,255,7,41,135,175,36,207,11,98,114,240,88,172,185,
123,101,90,224,96,10,169,241,190,66,82,214,161,103,236,158,
106,239,229,230,109,188,89,152,32,258,144,186,43,136,12,62,
245,23,100,117,116,52,205,145,173,228,167,99,154,5,74,81,
108,17,196,203,35,97,110,252,13,197,204,184,18,138,126,248,
129,72,93,4,157,259,25,24,246,69,227,127,15,40,149,118,226,
220,187,164,165,53,9,58,8,61,160,71,86,163,142,153,83,37,
244,178,218,65,209,63,49,76,201,14,121,132,26,263,171,215,
79,59,1,257,50,266,265],
\[146,132,3,156,242,107,125,245,174,241,264,248,36,116,47,
178,170,197,233,121,1,228,48,201,15,136,212,6,175,77,237,30,
226,31,129,44,161,232,219,78,139,9,211,13,222,97,25,173,70,
153,186,29,203,35,169,140,260,91,199,108,208,206,11,55,103,
65,95,73,151,131,41,221,225,18,143,7,32,159,217,93,181,2,
258,163,154,182,38,133,117,33,243,191,122,27,205,20,135,98,
229,138,61,194,66,104,149,62,28,164,123,17,137,16,69,37,238,
128,247,57,167,134,96,80,193,185,76,83,218,14,54,8,49,82,
215,189,46,190,183,188,71,230,231,239,202,224,158,21,119,214,
184,250,113,72,200,213,22,166,102,220,40,92,114,257,177,60,
179,4,147,168,64,110,171,148,23,42,52,195,84,112,246,19,252,
196,111,105,265,209,24,100,120,26,160,39,109,157,266,86,74,
204,227,50,187,75,216,207,67,106,198,101,51,141,251,94,85,
172,88,53,254,261,192,145,152,240,262,249,68,90,59,155,263,
56,210,87,180,12,115,142,34,235,236,45,244,253,58,10,130,
165,89,234,144,259,43,81,5,79,223,162,256,126,150,118,127,
255,99,63,124,176]>;
  targets cat:= [ < G, G, 175560 >,
                  < PSL(2,71), PGL(2,71), 178920 >,
                  < PGL(2,71), PGL(2,71), 357840 >, 
                  < Alt(9), Sym(9), 181440 >,
                  < Sym(9), Sym(9), 362880 >,
                  < PSL(2,73), PGL(2,73), 194472 >,
                  < PGL(2,73), PGL(2,73), 388944 >, 
                  < PSL(2,79), PGL(2,79), 246480 >,
                  < PGL(2,79), PGL(2,79), 492960 > ];
  X := WreathProduct(PGammaL(2,9),CyclicGroup(2));
  Q, phi := SocleQuotient(X);
  S := Subgroups(Q);
  S := [ s`subgroup @@ phi : s in S ];
  S := [ s : s in S | #MinimalNormalSubgroups(s) eq 1 ];
  targets cat:= [ < l, Normaliser(X,l), #l > : l in Reverse(S) ];
  X := PGammaL(2,64);
  L := LowIndexSubgroups(X, <3,3>);
  LL := LowIndexSubgroups(X, <2,2>);
  targets cat:= [ < PSL(2,64), X, 262080 >,
                  < L[1], X, 524160 >,
                  < LL[1], X, 786240 >,
                  < X, X, 1572480 > ];
  X := PGammaL(2,81);
  L := LowIndexSubgroups(X, <4,4>);
  LL := LowIndexSubgroups(X, <2,2>);
  targets cat:= [ < PSL(2,81), X, 265680 >,
                  < L[1], X, 531360 >,
                  < L[2], X, 531360 >,
                  < L[3], X, 531360 >,
                  < LL[1], X, 1062720 >,
                  < LL[2], X, 1062720 >,
                  < LL[3], X, 1062720 >,
                  < X, X, 2125440 >,
                  < PSL(2,83), PGL(2,83), 282852 >,
                  < PGL(2,83), PGL(2,83), 571704 >,
                  < PSL(2,89), PGL(2,89), 352440 >,
                  < PGL(2,89), PGL(2,89), 704800 >,
                  < Socle(PSL2(3,5)), PSL2(3,5), 372000 >,
                  < PSL2(3,5), PSL2(3,5), 744000 > ];
  X := PermutationGroup<24 |  
\[1,2,8,11,14,13,19,16,7,21,17,20,22,18,5,6,10,4,23,15,12,24,3,9],
\[2,1,7,11,10,21,3,6,4,17,8,19,15,5,12,9,23,22,20,14,24,16,13,18]>;
  targets cat:= [ < Socle(X), X, 443520>, //M_22
                  < X, X, 887040 >,
                  < PSL(2,97), PGL(2,97), 456288 >,
                  < PGL(2,97), PGL(2,97), 912576 > ];
  end if; end if; end if;

  if PrintLevel gt 0 then "Made list of targets"; end if;
  G := GroupsFound[1]`Group;
  for t in targets do if t[3] le n then
    hh := Homomorphisms(G, t[1], t[2] );
    for h in hh do
      AddGroup(~GroupsFound, Kernel(h), {1}, ~place, PrintLevel, Simplify);
    end for;
  end if; end for;

end procedure;

OldFindTs:=procedure(~GroupsFound, n, PrintLevel, Simplify) //no longer used
  local G, L, I, A, B;
  if n lt 60 then return; end if;
  if n lt 168 then max:=5;
  elif n lt 336 then max:=7;
  elif n lt 504 then max:=8;
  elif n lt 660 then max:=9;
  elif n lt 1092 then max:=11;
  elif n lt 2448 then max:=14;
  elif n lt 3420 then max:=18;
  elif n lt 6048 then max:=20;
  elif n lt 9828 then max:=26;
  elif n lt 12180 then max:=28;
  elif n lt 14880 then max:=30;
  elif n lt 25308 then max:=32;
  elif n lt 29120 then max:=38;
  else max:=65;
  end if;
  G:=GroupsFound[1]`Group;
  if PrintLevel gt 1 then 
    "  Searching for Low Index Subgroups of index up to", max;
  end if;
  L:=LowIndexSubgroups(G, <5, max>);
  I:={<60,5>,<120,5>,					//A5
      <168,7>,<336,8>,                  		//L2_7
      <360,6>, <720,6>, <720,10>, <1440,10>,		//A6
      <504,9>, <1512,9>,				//L2_8
      <660,11>, <1320,12>,				//L2_11
      <1092,14>, <2184,14>,                     	//L2_13
      <2448,18>, <4896,18>,				//L2_17
      <2520,7>, <5040,7>,				//A7
      <3420,20>, <6840,20>,				//L2_19
      <7200,10>, <14400,10>, <28800,10>,		//A5xA5
      <4080,17>, <8160,17>, <16320,17>,			//L2_16
      <5616,13>, <11232,26>,				//L3_3
      <6048,28>, <12096,28>,				//U3_3
      <6072,24>, <12144,24>,				//L2_23
      <7800,26>, <15600,26>, <31200,26>,		//L2_25
      <7920,11>,					//M11
      <9828,28>, <19656,28>, <29484,28>, <58968,28>,	//PSL2_27
      <12180,30>, <24360,30>,				//PSL2_29
      <14880,32>, <29760,32>,				//PSL2_31
      <20160,8>, <40320,8>,				//A8
      <20160,21>, <40320,21>, <40320,42>, <60480,21>,
      <80640,42>, <120960,21>, <120960,42>, <241920,42>,//L3_4
      <25308,38>, <50616,38>,				//L2_37
      <25920,27>, <51840,27>,				//U4_2
      <29120,65>, <87360,65>,				//Sz8
      <32736,33>, <163680,33>,				//L2_32
      <34440,42>, <68880,42>,				//L2_41
      <39732,44>, <79464,44>,				//L2_43
      <51888,48>, <103776,48>,				//L2_47
      <56448,14>, <112896,16>, <225792,16>,		//L2_7xL2_7
      <58800,50>, <117600,50>, <235200,50>,		//L2_49
      <62400,65>, <124800,65>, <249600,65>,		//U3_4
      <74412,54>, <148824,54>,				//L2_53
      <95040,12>, <190080,24>				//M12
     };
  for i in I do
    if n lt i[1] then continue i; end if;
    A:={l : l in L | Index(G,l) eq i[2]};
    B:={Core(G,l) : l in A | #CosetImage(G,l) eq i[1]};
    for b in B do
      AddGroup(~GroupsFound, b, {1}, ~place, PrintLevel, Simplify);
    end for;
  end for;
  return;
end procedure;

FindIntersections:=procedure(~GroupsFound, n, Current, PrintLevel, Simplify)
  local j, k, S, T;
  //find intersections of current group with earlier ones in list
  if PrintLevel gt 1 then
    "  Looking for intersections with group", Current, ", of index",
     GroupsFound[Current]`Index;
  end if;
  if Current eq 1 then return; end if;
  for i:=2 to (Current - 1) do
    if i in GroupsFound[Current]`Supergroups then
      continue i;
    end if;
    j:=Max(GroupsFound[i]`Supergroups meet GroupsFound[Current]`Supergroups);
    k:=GroupsFound[i]`Index*GroupsFound[Current]`Index div GroupsFound[j]`Index;
//k is the index of the intersection
    if k gt n then continue i; end if;
    S:={m : m in GroupsFound[i]`Supergroups | m gt j};
    T:={m : m in GroupsFound[Current]`Supergroups | m gt j};
    if #S gt 1 and #T gt 1 then continue i; end if;
      //in that case, the same intersection will be found in another way.
    for l in {m : m in [Current..#GroupsFound] | GroupsFound[m]`Index eq k} do
      if {i, Current} subset GroupsFound[l]`Supergroups then continue i; end if;
      //we already have the intersection
    end for;
    if PrintLevel gt 1 then
      "  Adding intersection with group", i;
    end if;
    AddGroup(~GroupsFound,
             (GroupsFound[i]`Group meet GroupsFound[Current]`Group),
             {i, Current}, ~place, PrintLevel, Simplify);
  end for;
  return;
end procedure;

MinSubgroupSizes:=function(GroupsFound, Current)
  //Set of orders |K/H| of minimal supergroups K of current group H 
  local Sizes;
  MinSubgroups:=GroupsFound[Current]`Supergroups;
  for i in GroupsFound[Current]`Supergroups do
    MinSubgroups:=MinSubgroups diff GroupsFound[i]`Supergroups;
  end for;
  Sizes:={};
  for i in MinSubgroups do
    Include(~Sizes, GroupsFound[Current]`Index div GroupsFound[i]`Index);
  end for;
  return Sizes;
end function;

OGL:=func< r, p | &*[(p^r - p^i) : i in [0 .. r-1] ] >; //Order of GL(r,p).

MustCheckP:=function(p, Index, minSubgroupSizes, r)
  local twoList, threeList, l;
  for i in minSubgroupSizes do
    if IsPowerOf(i, p) then return false; end if;
  end for;
/* The following are lists of the orders of those imple groups with Schur
 * multipliers having order divisible by 2 or 3.
 * (No higher primes arise as yet.)
 */
  twoList:={60, 168, 360, 660, 1092, 2448, 2520, 3420, 3600, 6072, 7800, 9828,
       12180, 14880, 20160, 25308, 25920, 28224, 29120, 34440, 39732, 51888,
       58800, 74412, 95040, 102660, 113460, 150348, 178920, 181440, 194472,
       246480, 265680, 282852, 352440, 443520, 456288 };
  threeList:={360, 2520, 20160, 126000, 443520};
  if p eq 2 and (twoList meet minSubgroupSizes ne {}) then
    l := &*[ Integers() | m : m in minSubgroupSizes | not m in twoList ]; 
  elif p eq 3 and (threeList meet minSubgroupSizes ne {}) then 
    l := &*[ Integers() | m : m in minSubgroupSizes | not m in threeList ]; 
  else l := Index;
  end if;
  return OGL(r, p) mod l eq 0;
end function;

forward TryPModules;
TryPModules:=procedure(~GroupsFound, n, Current, p, r, PrintLevel, Simplify)
  //For current group H, find irreducible GF(p)H-modules that are
  //quotients of H/[H,H]H^p and have ordr within required range.
  local G, M, map, MM, idx;
  if p in GroupsFound[Current]`TriedPrimes then return; end if;
  Include(~GroupsFound[Current]`TriedPrimes, p);
  G:=GroupsFound[1]`Group;
  M, map:=GModuleH(G,GroupsFound[Current]`Group, p);
  //"TryPModules",GroupsFound[Current]`Index,p;
  if PrintLevel gt 1 then
    "  Module has dimension",Dimension(M);
  end if;
  if Dimension(M) eq 0 then return; end if;
  if PrintLevel gt 1 then
     "  Calling submodules, dimension",Dimension(M),"codim limit",r;
  end if;
/* various old attempts
  time MM := Submodules(M : CodimensionLimit := r);
  MM := [ m: m in MM | (m ne M) and IsIrreducible( quo<M|m> ) ];
  MM:=[m:m in MaximalSubmodules(M) |
         (Dimension(M) - Dimension(m) le r) and (m ne M)];
*/
  MM := MaximalSubmodulesH(M,r);
  if PrintLevel gt 1 then "  ",#MM,"submodules"; end if;
  for SM in MM do
    if (Dimension(SM) gt 0) then SG:=PullBackH(map,SM);
    else SG:=Kernel(map);
    end if;
    idx:=Index(G,SG);
    cl := 1000000;
    while idx eq 0 do cl*:=2; idx:=Index(G,SG:CosetLimit:=cl); end while;
    if idx le n then
      AddGroup(~GroupsFound, SG, {Current}, ~place, PrintLevel, Simplify);
      if (place ne 0) and (idx * p le n) then
//"recursive call";
        TryPModules(~GroupsFound, n, place, p, r-Dimension(M)+Dimension(SM),
                         PrintLevel, Simplify);
      end if;
    end if;
  end for;
  return;
end procedure;

FindPQuotients:=procedure(~GroupsFound, n, Current, PrintLevel, Simplify)
//For current group H find all normal subgroups K of G withing the range
//such that H < H and H/K is a p-group
  local maxQuotient, r;
  if PrintLevel gt 1 then
    "  Looking for p-Quotients from group", Current, ", of index",
        GroupsFound[Current]`Index;
  end if;
  maxQuotient:= n div GroupsFound[Current]`Index;
  if maxQuotient lt 2 then return; end if;
  if  maxQuotient gt 50 then
    primes := AQPrimes(GroupsFound[Current]`Group);
  else primes := [0];
  end if;
  if primes eq [0] then
     primes := [ i : i in [2..maxQuotient] | IsPrime(i) ];
  end if;
  Sizes := MinSubgroupSizes(GroupsFound, Current);
  if PrintLevel gt 1 then
    "  Indices of minimal overgroups:",Sizes;
  end if;
  if PrintLevel gt 1 then
    "  Minimal overgroup indices:", Sizes;
  end if;
  for p in primes do
    r:=0;
    while p^(r+1) le maxQuotient do r+:=1; end while;
    if r gt 0 and MustCheckP(p, GroupsFound[Current]`Index, Sizes, r) then
/*
    if r gt 0 then
      for i in Sizes do
        if IsPowerOf(i, p) then continue p; end if;
      end for;
*/
      if PrintLevel gt 1 then
        "  Looking for ",p, "-quotients";
      end if;
      TryPModules(~GroupsFound, n, Current, p, r, PrintLevel, Simplify);
    end if;
  end for;
  return;
end procedure;

intrinsic LowIndexNormalSubgroups
     (G::GrpFP, n::RngIntElt : Print:=0, Simplify:="No", Limit:=0 ) -> SeqEnum
{Compute normal subgroups of FPGroup G up to index n}
  local GroupsFound, Current, NewGroupsFound, shortrf;
  if n gt MaxLINSIndex then
    "Warning: this implementation is only valid for n no greater than",
                                                             MaxLINSIndex;
    "         For larger values of  n, some normal subgroups may not be found";
  end if;
  PrintLevel := Print;
  SubgroupsLimit := Limit;

  rf:=recformat<Group, Index, Supergroups, TriedPrimes>;
  GroupsFound:=[];
  GroupsFound[1]:=rec<rf|Group:=G, Index:=1, Supergroups:={}, TriedPrimes:={}>;
  Current:=1;
  FindTs(~GroupsFound,n, PrintLevel, Simplify);
  if SubgroupsLimit eq 0 or #GroupsFound lt SubgroupsLimit then
   while n div GroupsFound[Current]`Index gt 1 do
    if PrintLevel gt 0 then
      "Group Number", Current, ", of Index", GroupsFound[Current]`Index,
         " - Maximum size of quotient ", n div GroupsFound[Current]`Index;
    end if;
    FindPQuotients(~GroupsFound, n, Current, PrintLevel, Simplify);
    if SubgroupsLimit gt 0 and #GroupsFound ge SubgroupsLimit then
      break;
    end if;
    if Current gt 1 then
      FindIntersections(~GroupsFound, n, Current, PrintLevel, Simplify);
    end if;
    if SubgroupsLimit gt 0 and #GroupsFound ge SubgroupsLimit then
      break;
    end if;
    Current:=Current+1;
    if Current gt #GroupsFound then break; end if;
   end while;
  end if;
  shortrf:=recformat<Group, Index, Supergroups>;
  NewGroupsFound:=[];
  for i:=1 to #GroupsFound do
    NewGroupsFound[i]:=rec<shortrf|Group:=GroupsFound[i]`Group,
       Index:=GroupsFound[i]`Index,
       Supergroups:=GroupsFound[i]`Supergroups diff{i}>;
  end for;
  return NewGroupsFound;
end intrinsic;


