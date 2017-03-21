freeze;

import "Reduce.m" : GetX, InduceAut;

/*
  <example>
     G := SmallGroup(8,4);
     X := CharacterTable(G);
     c := X[5];
     SchurIndices(c);
     R := Representations(X[5])[1][1];
     // now R is over a minimal degree field (Q(i)), so everything is fine.
     // BUT: we can rewrite R over any field where -1 = a^2+b^2
     // and there exists some where no quadratic subfield will split the
     // representation: Q(z_5), Q(z_17)
     // (Actually: Q(z_p) for p a prime dividing (2^(2^k))+1 we have that
     //  - there is a suitable subfield of Q(z_p) which is cyclic of order
     //    2^n>2^(k+1)
     //  - is a minimal splitting field)
     // So we can use the NonCyclicReduction (or the CyclicReduction even)
     // to find all minimal reps over Q(4*5)...
     // using old code:
     r := ChangeRing(R, CyclotomicField(20));
     q := TheLot(r:All);
     // then q[4] is over Q(zeta_5) and cannot be reduced!
  </example>
    example with p=17 shows that CyclotomicAutomorphismGroup needs fixing
      (as well as the need to write AutomorphimGroup(FldCyc))
*/

_Automorphisms := Automorphisms;
intrinsic Compositum(K::FldAlg, A::FldAb:Automorphisms := false) -> FldAlg
  {The compositum of the two number fields.}

  require IsAbsoluteField(K) : "The 1st field must be over Q";
  require BaseField(A) subset K : "The abelian field must be defined over
     a subfield of the 1st field";

  KA := NumberField(A);   
  if IsSimple(KA) then
    l := [DefiningPolynomial(KA)];
  else
    l := DefiningPolynomial(KA);
  end if;
  if Gcd(Norm(Discriminant(A)), Discriminant(K)) eq 1 then
    // linear disjoint, easy case
    An := NumberField([Polynomial(K, f) : f in l] : Check := false);
    if #l eq 1 then
      KC := CoefficientField(KA);
      if IsSimple(KC) then
        Embed(CoefficientField(KA), An, An!CoefficientField(KA).1);
      else
        Embed(CoefficientField(KA), An, ChangeUniverse(GeneratorsSequence(KC), An));
      end if;
      Embed(KA, An, An.1);
    else
      Embed(KA, An, [An.i : i in [1..#l]]);
    end if;
    An :=  AbsoluteField(An);
    Z_A := MaximalOrder(A);
    Z_K := MaximalOrder(K);
    CI := CoefficientIdeals(Z_A);
    if IsSimple(K) then
      if AbsoluteDegree(CoefficientField(A)) eq 1 then
        KR := ext<CoefficientField(A)|DefiningPolynomial(K)>;
        Embed(KR, K, K.1);
      else
        KR := RelativeField(NumberField(CoefficientField(A)), K);
      end if;
      MR := MaximalOrder(KR);
      DI := CoefficientIdeals(MR);
      I := [c*d : c in CI, d in DI];
      B := [An!Z_A.i*An!MR.j : i in [1..Degree(Z_A)], j in [1..Degree(MR)]];
      B_A := &cat [[B[i] * x : x in Basis(I[i], An)] : i in [1..#I]];
      R := Order(B_A:Verify := false, Order);
    else
      B_A := &cat [[Z_A.i * x : x in Basis(CI[i])] : i in [1..#CI]];
      R := Order(ChangeUniverse(Basis(Z_K, K), An) cat ChangeUniverse(B_A, An));
    end if;
    assert IsMaximal(R);
    SetOrderMaximal(R, true);
  else
    KA := SimpleExtension(KA);
    lf := Factorisation(Polynomial(K, DefiningPolynomial(KA)));
    An :=  NumberField(lf[1][1]);
    Embed(KA, An, An.1);
    An :=  AbsoluteField(An);
    Z_A := MaximalOrder(A);
    Z_K := MaximalOrder(K);
    CI := CoefficientIdeals(Z_A);
    B_A := &cat [[Z_A.i * x : x in Basis(CI[i])] : i in [1..#CI]];
    R := Order(ChangeUniverse(Basis(Z_K, K), An) cat ChangeUniverse(B_A, An));
    for p in Factorisation(Gcd(Norm(Discriminant(A)), Discriminant(K))) do
      R := pMaximalOrder(R, p);
    end for;
    assert IsMaximal(R);
    SetOrderMaximal(R, true);
  end if;
  if Automorphisms then
    aK := _Automorphisms(K);
    aA := _Automorphisms(A:All);
    bK := AbsoluteBasis(K);
    bA := AbsoluteBasis(NumberField(A));
    nbK := ChangeUniverse(bK, An);
    nbA := ChangeUniverse(bA, An);
    bC := [x*y : x in nbK, y in nbA];
    f, n := IsConsistent(Matrix([Eltseq(x) : x in bC]), Matrix([Eltseq(An.1)]));
    assert f;
    pB := [<x,y> : x in bK, y in bA];
    n := Eltseq(n);
    assert #n eq #pB and #n eq #bC;
    pB := [pB[i] : i in [1..#n] | n[i] ne 0];
    n  := [ n[i] : i in [1..#n] | n[i] ne 0];
    pB := [<[An|x[1]@ s : s in aK], [An|x[2]@t : t in aA]> : x in pB];
    pe := PrimitiveElement(BaseField(A));

    for s in [1..#aK], t in [1..#aA] do
      if An!((K!pe)@aK[s]) ne An!(pe@aA[t]) then
        continue;
      end if;
      x := &+ [((pB[x][1][s]))*((pB[x][2][t]))*n[x] : x in [1..#n]];
      if Evaluate(DefiningPolynomial(An), x) eq 0 then
        InternalAutomorphismAdd(x);
      end if;
    end for;
 end if;
 return An;
end intrinsic;

intrinsic Compositum(K::FldAlg, L::FldAlg:Automorphisms := false) -> FldAlg
  {The compositum of the two absolute number fields, one of which must be normal.}
  require IsAbsoluteField(K) and IsAbsoluteField(L) :
    "Both fields must be defined over Q";

  make_monic := function(X)
    f := DefiningPolynomial(X);
    if Type(f) eq RngUPolElt and not IsMonic(f) then
      f := Polynomial(Rationals(), f);
      l := LeadingCoefficient(f);
      f := Evaluate(f, Polynomial([0, 1/l]))*l^(Degree(f)-1);
      KK := NumberField(f);
      Embed(X, KK, KK.1/l);
      Embed(KK, X, X.1*l);
      return KK;
    else
      return X;
    end if;
  end function;

  K := make_monic(K);
  L := make_monic(L);


  if Type(K) eq FldCyc then
    N := K;
    M := L;
  elif Type(L) eq FldCyc then
    N := L;
    M := K;
  elif Degree(K) le 2 or IsNormal(K) then
    N := K;
    M := L;
  elif Degree(L) le 2 or IsNormal(L) then
    N := L;
    M := K;
  else
    require false: "At least one of the fields must be normal for the
      composite to be well defined. Use CompositeFields in the other case";
  end if;

  if Degree(K) eq 1 then
    return L;
  elif Degree(L) eq 1 then
    return K;
  end if;  

  if K cmpeq L then
    return K;
  end if;

  //if both fields are cyclos then the embedding is easy
  if Type(K) eq FldCyc and Type(L) eq FldCyc then
    c := Lcm(Conductor(K), Conductor(L));
    if IsSimple(K) and IsSimple(L) then
      return CyclotomicField(c);
    elif not IsSimple(K) and not IsSimple(L) then
      return CyclotomicField(c:Sparse);
    elif IsSimple(K) then
      C := CyclotomicField(c);
      X := CyclotomicField(Conductor(L));
      Embed(L, C, [C!X!L.i : i in [1..Ngens(L)]]);
      delete X;
      return C;
    else
      C := CyclotomicField(c);
      X := CyclotomicField(Conductor(K));
      Embed(K, C, [C!X!K.i : i in [1..Ngens(K)]]);
      delete X;
      return C;
    end if;
  end if;
      
  if IsSimple(M) then
    if Gcd(Discriminant(N), Discriminant(M)) eq 1 then
      C := NumberField(Polynomial(N, DefiningPolynomial(M)):Check := false, DoLinearExtension);
    else
      lf := Factorisation(Polynomial(N, DefiningPolynomial(M)));
      assert forall{x : x in lf | x[2] eq 1 and Degree(x[1]) eq Degree(lf[1][1])};
      C := NumberField(lf[1][1]:Check := false, DoLinearExtension);
    end if;
  else
    if Gcd(Discriminant(N), Discriminant(M)) eq 1 then
      C := NumberField([Polynomial(N, x) : x in DefiningPolynomials(M)]:Abs, DoLinearExtension, Check := false);
      Embed(M, C, [C.i : i in [1..Ngens(C)]]);
    else
      M := SimpleExtension(M);
      lf := Factorisation(Polynomial(N, DefiningPolynomial(X)));
      assert forall{x : x in lf | x[2] eq 1 and Degree(x[1]) eq Degree(lf[1][1])};
      C := NumberField(lf[1][1]:Check := false, DoLinearExtension);
    end if;
  end if;
  A := AbsoluteField(C);
  Embed(M, A, A!C.1);
  return A;
end intrinsic;

function MYNgens(G)
  if Type(G) eq GrpPC then
    return #PCGenerators(G);
  else
    return Ngens(G);
  end if;
end function;

function RepToCocylce(L1, A:ReduceX := "Auto")

  redClg := false;
  redDet := true;
  if ReduceX cmpeq "Auto" then
    if Degree(CoefficientRing(L1[1])) gt 20 then
      redClg := false;
    else
      redClg := true;
    end if;
    redX1 := true;
    redX2 := true;
  elif ReduceX cmpeq "All" then
    redClg := true;
    redX1 := true;
    redX2 := true;
  elif ReduceX cmpeq 1 or ReduceX cmpeq true then
    redX1 := true;
    redX2 := false;
  else
    redX1 := false;
    redX2 := false;
  end if;

  vprint Reduce, 1: "Reduction strategy:", redClg, redX1, redX2, ReduceX;

  //step 1:
  //find all s in Aut(K) which have some X_s sth. R X_s = X_s R^s
  // they should form a subgroup...
  // Also, since the rep corresponds to an algebra over the character field,
  // we need only the part of Aut(K) fixing the char. field.
  //OK: if we KNOW X_s, and X_t we can derive X_(s*t):
  //  R X_s = X_s R^s =>
  //  R X_t = X_t R^t =>
  //  R^t X_s^t = X^s_t R^st
  //  R^t = X_t^-1 R X_t thus
  //  X_t^-1 R X_t X_s^t = X_s^t R^st
  //  and finally:
  //  R X_t X_s^t = X_t X_s^t R^st
  //  induction will give it for all powers of s for example.
  //  For weird resons we DONT want it for s^n=1, instead we define X_1 = 1.
  //
  // step 2:
  // for all (s,t) in GxG find
  // l(s,t) such that
  // X_s^t X_t = l(s,t) X_st
  // if one transposeses enough, it should be a 2-cocyle.

  K := CoefficientRing(L1[1]);
  AA, _, mA := AutomorphismGroup(K);
  assert A subset AA;
  delete AA;

  function ReduceX(X)
    if redClg then
      vprint Reduce, 2: "Reduce contents with class group";
      vtime Reduce, 2: c := Content(X);
      vtime Reduce, 2: _, f := ClassRepresentative(c);
      vtime Reduce, 2: X := X/f;
      vprint Reduce, 2: "done (times are Content, ClassRep, scaling)";
    else
      vprint Reduce, 2: "Reduce contents with LLL";
      vtime Reduce, 2: c := Content(X);
      vtime Reduce, 2: d := c^-1;
      vtime Reduce, 2: L := InternalExactLattice(d);
      vtime Reduce, 2: e := ShortestVectors(L)[1];
      f := &+ [ e[i]*b[i] : i in [1..n]] where n := #b where b := Basis(d);
      vtime Reduce, 2: X := X*f;
      vprint Reduce, 2: "done (times are Content, Inverse, Lat, SVP, scaling)";
    end if;
    if redDet then
      d := Determinant(X);
      fl, r := IsPower(d, Ncols(X));
      if fl then
        vprint Reduce, 2:"Reduction by square-root successful";
        X := X/r;
      end if;
    end if;
    return X;
  end function;

  n := Ncols(L1[1]);
  a := [[*A.0, IdentityMatrix(K, n)*]];
  C := cop<Booleans(), KMatrixSpace(K, n, n)>;
  //TODO:
  // - use the coproduct rather than [* *]
  // - use a form of Dimino's algorithm here. It should save on calls to
  //   getX
  // - build up as much of l(s,t) during this procedure as possible  
  while #a lt #A do
    vprint Reduce, 2: "#a now", #a, "going for", #A;
    assert #a eq #{x[1] : x in a};
    s := Set(A) diff {x[1] : x in a};
    s := SetToSequence(s);
    so := [Order(x) : x in s];
    _, p := Maximum(so);
    sigma := s[p]@mA;
    L2 := [InduceAut(j, sigma) : j in L1];
    vprint Reduce, 2: "Get X...";
    vtime Reduce, 2: X := GetX(L1, L2);
    o := Order(s[p]);
    if X cmpeq false then
      vprint Reduce, 2: "X gave nothing";
      a cat:= [[*s[p]^i, false*] : i in [1..o] | Gcd(i, o) eq 1];
    else
      Y := X;
      t := s[p];
      if redX1 then
        vprint Reduce, 2: "reducing X";
        X := ReduceX(X);
      end if;
      for i in [1..o-1] do
        if not t in [x[1] : x in a] then
          Append(~a, [*t, X*]);
        else
          vprint Reduce, 2: "possibly duplicate found for i=", i, "in ", [1..o-1];
        end if;
        if i lt o-1 then
          Y := InduceAut(Y, sigma);
          X *:= Y;
          if redX2 then
            vprint Reduce, 2: "reducing power", i+1;
            X := ReduceX(X);
          end if;
          t := t*s[p];
        end if;
      end for;
    end if;
  end while;

  a := [x : x in a | x[2] cmpne false];
  X := function(x)
    return a[Position([t[1] : t in a], x[1])][2];
  end function;
  U := sub<A|[x[1] : x in a]>;
  U := sub<A|FewGenerators(U)>;

  C := CartesianPower(U, 2);
  l := [];
  for c in C do
    s := c[1]@mA;
    t := c[2]@mA;
    X_s := X(<c[1]>);
    X_t := X(<c[2]>);
    X_st := X(<c[1]*c[2]>);
    //now X_t * X_s^t = l(s,t) X_st
    // and, I think I should be able to get l from looking at one row only.
    Xts := InduceAut(X_s, t);
    x := X_t[1]*Xts;
    y := X_st[1];
    _ := forall(p){p : p in [1..n]|IsZero(y[p])};
    Append(~l, <c, x[p]/y[p]>);
    assert X_t*Xts eq l[#l][2]*X_st;
  end for;

  function lambda(x)
    return l[Position([x[1] : x in l], x)][2];
  end function;

  return lambda, X, U;
end function;

intrinsic Cocycle(r::Map) -> UserProgram, Grp
  {Given an abs. irr.  representation r, find the corresponding cocycle}
  G := Domain(r);
  L1 := [r(G.i) : i in [1..MYNgens(G)]];
  A := AutomorphismGroup(CoefficientRing(L1[1]));
  return a,b where a, _, b := RepToCocylce(L1, A);
end intrinsic;    

intrinsic Cocycle(M::ModGrp) -> UserProgram, Grp
  {Given an abs. irr. G-Module, find the corresponding cocycle}
  L1 := ActionGenerators(M);
  A := AutomorphismGroup(CoefficientRing(L1[1]));
  return a,b, c where a, c, b := RepToCocylce(L1, A);
end intrinsic;    

intrinsic Cocycle(A::AlgAss) -> UserProgram, Grp
  {}
  L1 := [RepresentationMatrix(x) : x in Generators(A)];
  A := AutomorphismGroup(CoefficientRing(L1[1]));
  return a,b where a, _, b := RepToCocylce(L1, A);
end intrinsic;    



function NonCyclicReduction(L1, G :DoNice := false, All := false, Char := false, ReduceX := "Auto", FindSmallest := false, OptimizeField := true,
  Contains := false,
  WriteOver := false, Subfield := true, UseMultGrp := true) 
// intrinsic NonCyclicReduction(L::[Mtrx], G::Grp:DoNice := false, All := false, Char := false, ReduceX := 1, FindSmallest := false, OptimizeField := true) -> [**] 
//  {}
  // R:G.i -> L1[i]
  // should be a representation of some group over some abelian field  
  // we try to reduce it to a representation over a smaller field.
  // Currently, we're only trying to find the field.
  V := Universe(L1);
  K := BaseRing(V);
  if ISA(Type(K), FldAlg) then
    M := MaximalOrder(K);
    F := FieldOfFractions(M);
  end if;

  if K cmpeq Rationals() then
    if Contains cmpne false then
      return [*[Matrix(Contains, x) : x in L1]*];
    else
      return [*L1*];
    end if;
  end if;

  if WriteOver cmpne false then
    if not IsNormal(WriteOver) then
      error "Error: Sorry, can only realize representations over normal fields";
    end if;
  end if;

  assert #L1 eq MYNgens(G);


  //step 1:
  //find all s in Aut(K) which have some X_s sth. R X_s = X_s R^s
  // they should form a subgroup...
  // Also, since the rep corresponds to an algebra over the character field,
  // we need only the part of Aut(K) fixing the char. field.
  //OK: if we KNOW X_s, and X_t we can derive X_(s*t):
  //  R X_s = X_s R^s =>
  //  R X_t = X_t R^t =>
  //  R^t X_s^t = X^s_t R^st
  //  R^t = X_t^-1 R X_t thus
  //  X_t^-1 R X_t X_s^t = X_s^t R^st
  //  and finally:
  //  R X_t X_s^t = X_t X_s^t R^st
  //  induction will give it for all powers of s for example.
  //  For weird resons we DONT want it for s^n=1, instead we define X_1 = 1.
  //
  // step 2:
  // for all (s,t) in GxG find
  // l(s,t) such that
  // X_s^t X_t = l(s,t) X_st
  // if one transposeses enough, it should be a 2-cocyle.
  // I guess:
  // step 3 assert l is a 2-cocycle
  //
  // step 4: find the largest subgroup S of Aut(K) such that l restriced 
  // to S is a coboundary
  // Here one can do quite well: a cocycle that has locally order l say, 
  // will split locally exactly when the local degree is raised by l.
  // This can be used to sieve the subgroups: we need to find subgroups such 
  // that the induced local groups have the correct size.
  // Should be easy.
  //
  // step 5: find the corresponding 1-cocycle
  //
  // step 6: rewrite the representation.
  // difficult: actually, there is no real algorithm in the thesis. Needs
  // thinking. Done. Works exactly as in the cyclic case.
  // as a result of step 5 we have some x_s in K such that
  // l(s,t)=x_s^t x_t = x_st   (a 1-cocycle)
  // Then Y_s := X_s/x_s should have the property that
  // Y_s^t Y_t = Y_st
  // (Y_s^t Y_t = (X_s/x_s)^t X_t/x_t = X_s^t X_t / (x_s^t x_t)
  //  = X_st / l(s,t) = X_st/x_st = Y_st)
  // Thus, s -> Y_s is a 1-cocyle of matrices.
  // Now, Hilbert 90 for GL(n, K) (eg. Lorenz, Algebra 2) states that
  // H^1(G, GL(n, K)) = 1, ie. there is some A in GL(n, K) such that
  // Y_s = A^(1-s) for all s.
  // Now A^-1 R A is in GL(n, k).
  //
  // To find A:
  // as the cyclic case, for any B in GL(n, K) define
  // Psi(B) := sum Y_sB^s
  // Then 
  // Psi(B)^t = sum Y_s^t B^st
  //          = sum Y_t^-1 Y_st B^st
  //          = Y_t^-1 sum Y_st B^st
  //          = Y_t^-1 Psi(B)
  // And thus:
  // Psi(B)^(1-t) = Y_t 
  //
  // (A^-1 R A)^s = A^-s R^s A^s = A^-s Y_s^-1 R Y_s A^s
  //   = A^-s A^-(1-s) R A^1-s A^s
  //   = A^-1 R A.
  //
  //   TODO: according to Lorenz, Algebra II, last chapter, the co-cycle
  // lives over the character field, ie. the representation corresponds
  // to a central simple algebra over the character field. Thus we shuold
  // - compute the chararcter field
  // - compute the group fixing it
  // - only test for Galois morphisms outside the character field
  // Also, given that the Schurindicies for the representation should be
  // the same as for the algebra, we can replace IsLocallySplit by
  // a computation of the Schurindices of the character - which seems to be
  // faster.
  // Do regconize the cocyle as a coboundary, I should try to reduce the
  // support of the cochain before doing serious factorisations:
  // Let A be a set of ideals such that
  // - A is closed under the action of the Galois group
  // - the values of the cochain as principal ideals are in the ideal group
  //   generated by A
  // - A is closed under GCD
  // - A contains A_0 conaining all ramified primes of K and the primes where 
  //   the  cochain is not locally split.
  // Then for a in A \ A_0, the cochain with values in {a^s | s in G}
  // should be split and unramified, thus there should be some 1-chain
  // with value in the same set mapping to a. For the ideals in the image
  // of the 1-chain we find cannonical reps in the class group amd a
  // 1-chain with values in the field describing the difference.
  // Changing the 2-chain by this 1-chain over the field should remove the
  // ideal a from the support - and thus make the factorisation easier.
  // THis should probably be done in the global cohomology process.
  

  A, _, mA := AutomorphismGroup(K);
  if Char cmpeq false then
    char := Character(GModule(G, L1));
  else
    char := Char;
  end if;
  k_char := CharacterField(char);
  if k_char eq RationalField() then k_char := CyclotomicField(1); end if;
  vprint Reduce, 1: "Character field is", k_char;
  fl, pK := IsCoercible(K, PrimitiveElement(k_char));
  if not fl then
    fl, m := IsSubfield(k_char, K);
    assert fl;
    A := FixedGroup(K, PrimitiveElement(k_char)@m);
  else
    A := FixedGroup(K, pK);
  end if;
  //TODO: choose correct embedding by comparing character values!!!!!
  Schur := SchurIndices(char, k_char);
  vprint Reduce, 1: "Schur data over character field:", Schur;
  // before doing serious work here, let's see if K is already minimal
  if #Schur eq 0 then
    d := 1;
  else
    d := Lcm([x[2] : x in Schur]);
  end if;
  if Degree(k_char)*d eq Degree(K) and 
     WriteOver cmpeq false and Contains cmpeq false then
    vprint Reduce, 1: "nothing to do - Schur data sufficient";
    return [*L1*];
  end if;

  lambda, X, U := RepToCocylce(L1, A:ReduceX := ReduceX);

  n := Ncols(L1[1]);

  if #U lt 2 and WriteOver cmpeq false then
    vprint Reduce, 1: " does not give a reduction";
    return [*L1*];
  end if;

  _ := FactoredOrder(U);
  // actually, U should, at this point, always be the fixed group of the
  // character field.
  vprint Reduce, 1: "minimal field is fixed by at most ", U,
    "as a subgroup of ", A;

  // The data in Schur is in the character field, we need to lift it to the
  // actual field
  if IsSimple(k_char) then
    em := hom<k_char -> K | K!CoefficientField(char)!k_char.1>;
  else
    em := hom<k_char -> K | [K!CoefficientField(char)!k_char.i: i in [1..Ngens(k_char)]]>;
  end if;
  SchurK := &cat [ [<y[1], x[2]> : y in Decomposition(em, x[1])] : x in Schur];
  r := [<x[1], x[2], DecompositionGroup(x[1]) meet A> : x in SchurK];
  vprint Reduce, 1: "locally split returns", r;
  vprint Reduce, 1: "abs minimal field will have degree index ", 
    #U div Lcm([Integers()| x[2] : x in r]); 
  
  // now, we need to find subgroups of U of index at least 
  // &*[x[2] : x in r] that
  // will split lambda (ie. the local degrees are larger)
  // We want of all the subgroups with this property the maximal ones.
  // Dumb startegy: for all subgroups (all, not only up to conjugation!)
  // we need to find the local degrees at the places in [x[1] : x in r].
  // The subgroups we need are the ones where the degree is divisible by x[2].

  function FindField(U, r:Over := false, Cont := false)
    s := SubgroupLattice(U);

    function testOneSubgroup(X)
      assert X subset U;
      for p in r do
        d := #p[3] div #(p[3] meet X);
        if d mod p[2] ne 0 then
          return false;
        end if;
      end for;
      if Over cmpeq false then
        return true;
      else
        if Cont then
          return X subset Over;
        elif Subfield then
          return Over subset X;
        else
          return X eq Over;
        end if;
      end if;
    end function;

    found := [];
    for x in s do
      z := Group(x);
      for c in RightTransversal(U, Normalizer(U, z)) do
        g := z^c;
        if testOneSubgroup(g) then
          Append(~found, <x, c>);
        end if;
      end for;
    end for;

    // now found should contain all subgroups that fix a splitting field.
    // Let's find the maximal ones...
    rfound := [x : x in found | 
          forall{y : y in found | y[1] eq x[1] or not x[1] subset y[1]}];
    rfound := [x : x in rfound | #Group(x[1]) ne 1];      
    return rfound;
  end function;
  rfound := FindField(U, r);

  if WriteOver cmpne false or Contains cmpne false or
    forall{x : x in rfound| Index(U, Group(x[1])) gt Lcm([Integers()|x[2] : x in SchurK])} then
    if WriteOver cmpeq false then  
      vprint Reduce, 1: 
        "no abs. minimal field contained in this splitting field";
    end if;    
    if FindSmallest or WriteOver cmpne false or Contains cmpne false then
      if WriteOver cmpeq false and Contains cmpeq false then
        vprint Reduce, 1: "Finding minimal degree splitting field";
        vprint Reduce, 2: "with local data", Schur;
        KK := SplittingField(Schur);
        vprint Reduce, 2: "OK, a minimal splitting field is", KK;
        new_K := Compositum(K, KK:Automorphisms);
      elif WriteOver cmpne false then
        vprint Reduce, 1: "Building composite field";
        new_K := Compositum(K, WriteOver:Automorphisms);
        vprint Reduce, 1: "Done, now for the fixed field";
        Fix := FixedGroup(new_K, WriteOver);
        if #Fix eq 1 and not Subfield then
          return [*L1*];
        end if;
      else 
        Contains := Compositum(Contains, k_char);
        s := SchurIndices(char, Contains);
        vprint Reduce, 1: "Finding minimal degree splitting field";
        vprint Reduce, 2: "with local data", s;
        if #s ne 0 then
          KK := AbsoluteField(NumberField(SplittingField(s)));
          new_K := Compositum(K, KK);
        else
          new_K := Compositum(K, Contains);
        end if;
        Fix := FixedGroup(new_K, Contains);
        //TODO: derive the automorphism group of new_K from K and
        //WriteOver - currently both have to be normal.
      end if;
      // now we need
      // - the GaloisGroup(new_K/ k=char. field) as a subgroup of
      //   Gal(KK/k) times Gal(K/k)
      // - to "extend" the cohomology data to the larger group
      //   (both matrices and scalars)
      // - update r and U
      // General theory (it's easy to see) tell us that the new lambda
      // is just the inflation of the old, same for X_s
      // LiftCocycle does exatly that...
      // So, we need to identify the automorphisms, get the
      // A := Aut(new_K/Gal(K/k)=U) and a transversal Gal(new_K/k)/A -> U
      nG, _, mnG := AutomorphismGroup(new_K);
      // hopefully Compositum can get us a decent version!
      // we need a map from nG -> U
      pe := Set(Generators(K));
      new_pe := ChangeUniverse(pe, new_K);
      z := [<[s : s in nG | (s@mnG)(new_pe) eq (t@mA)(pe)], t> : t in U];
      find_t := function(x)
        if exists(i){ i : i in [1..#z] | x in z[i][1]} then
          return z[i][2];
        end if;
        error "thy wrong";
      end function;
      lift := map<nG -> U | x:->find_t(x)>;
      lambda := LiftCocycle(lift, lambda:NewCodomain := new_K, Level := 2);
      new_KA := MatrixAlgebra(new_K, n);
      X := LiftCocycle(lift, X:NewCodomain := new_KA, Level := 1);
      A := nG;
      U := FixedGroup(new_K, k_char);
      assert U subset nG;
      mA := mnG;
      K := new_K;
      SchurK := &cat [ [<y[1], x[2]> : y in Decomposition(EmbeddingMap(k_char, K), x[1])] : x in Schur];
      r := [<x[1], x[2], DecompositionGroup(x[1]) meet A> : x in SchurK];
      if WriteOver cmpeq false and Contains cmpeq false then
        rfound := FindField(U, r:Over := false, Cont := false);
      elif Contains cmpeq false then
        rfound := FindField(U, r:Over := Fix, Cont := false);
      else
        rfound := FindField(U, r:Over := Fix, Cont := true);
      end if;
    end if;  
  end if;
  
  if #rfound eq 0 then
    if Contains cmpne false then
      return [* [Matrix(new_K, x) : x in L1]*];
    elif WriteOver cmpne false then
      return [**];
    else
      return [*L1*];
    end if;
  end if;

  // now we need to rewrite the representation, either over a smallest field
  // or over all in rfound...
  // That implies the following steps for each subgroup V:
  //  - restrict lambda to V
  //  - find a 1-cocyle representing lambda|_V
  //  - scale the matrices X_s (in a[.][2])
  //  - apply Hilbert90
  //  - conjugate the representation down
  //  - compute the fixed field by V and coerce the matrices down
  if not All then
    // we want, among the largest groups, those where the cocycle is as close
    // to one as possible...
    _, p := Maximum([<#Group(x[1]), #{g :g in CartesianPower(Group(x[1])^x[2], 2) | lambda(g) eq 1}> : x in rfound]);
    rfound := [rfound[p]];
  end if;

  // maybe we don't need all of U?
  M := MaximalOrder(K);
  U := sub<U|FewGenerators(sub<U|[Group(x[1])^x[2] : x in rfound]>)>;
  S := {PowerIdeal(M)|Ideal(x[1]) : x in r | IsFinite(x[1])};
  // using reduction technology, the support of lambda is not neccessary
  // we only need the places with non-trivial Schur data and the class group
  // S join:= Support([lambda(<x,y>)*M : x,y in U]);
  // ClassGroup is sufficent, see comments there.

  res := [**];
  C := false;
  C_simple := false;
  for g in rfound do
    cU := Group(g[1])^g[2];
    vprint Reduce, 1: "Cohomology...";

    if exists{x : x in car<cU, cU> | lambda(x) ne 1} then
      if C cmpeq false then
        if UseMultGrp then
          vprint Reduce, 1: "building (simple) cohomology process in ", K;
          C := SimpleCohomologyProcess({lambda(x) : x in car<cU, cU>}, U 
                              :ClassGroup, S := S);
          C_simple := true;                    
        else
          vprint Reduce, 1: "building (serious) cohomology process in ", K;
          _ := ClassGroup(Ring(Universe(S)):Bound := 25*Degree(K));
          C := SUnitCohomologyProcess(S, U :ClassGroup);
          C_simple := false;                    
        end if;
      end if;
      fl, c := IsGloballySplit(C, lambda:Sub := cU);
      if not fl and C_simple then
        vprint Reduce, 1: "building (serious) cohomology process in ", K;
        _ := ClassGroup(Ring(Universe(S)):Bound := 25*Degree(K));
        C := SUnitCohomologyProcess(S, U :ClassGroup);
        C_simple := false;                    
        fl, c := IsGloballySplit(C, lambda:Sub := cU);
      end if;  
      assert fl;
    else
      vprint Reduce, 1: "cocycle is identical to 1, no cohomology needed";
      c := func<x|lambda(<cU.0, cU.0>)>;
    end if;
    vprint Reduce, 2: [<x, c(<x>)> : x in cU];
    vprint Reduce, 2: [<x,y, lambda(<x,y>)> : x,y in cU];
    Y := func<t|X(t)/c(t)>;
    Kn := MatrixAlgebra(K, n);
    c := map<cU -> Kn | x:-> Y(<x>)>;
    vprint Reduce, 1: "Hilbert90";
    A := Hilbert90(c);
    vprint Reduce, 1: "found A";
    Ai := A^-1; // replace by p-adic inverse for real examples
    vprint Reduce, 1: "found inverse";
//    assert forall{g : g in cU | c(g) eq A*InduceAut(Ai, g@mA)};
//    vprint Reduce, 1: "Hilbert90 OK";
    k := FixedField(K, cU);
    if OptimizeField and k cmpne Rationals() then
      k`MaximalOrder := MaximalOrder(EquationOrder(k):Discriminant := Discriminant(MaximalOrder(K)));
      k := OptimizedRepresentation(k);
    end if;
    vprint Reduce, 1: "fixed field is", k;
    assert k!K!k.1 eq k.1;
    Mk := MatrixAlgebra(k, n);
    l := [Mk!ChangeUniverse(Eltseq(Ai*(Kn!X)*A), k) : X in L1];

    if WriteOver cmpne false then
      Embed(k, WriteOver, WriteOver!K!k.1);
    end if;

    Append(~res, l);
    vprint Reduce, 1: "coerce fine";
  end for;

  
  return res;
end function;

intrinsic InternalAbsoluteModule(M::ModGrp:
         DoNice := false, All := false, 
         Char := false, FindSmallest := false, Contains := false,
         OptimizeField := true, ReduceX := "Auto") -> List 
  {}
  G := Group(M);
  R := Representation(M);
  L1 := [R(G.i) : i in [1..MYNgens(G)]];
  if Char cmpeq false and assigned M`Character then
    Char := M`Character;
  end if;
  return NonCyclicReduction(L1, G: DoNice := DoNice, All := All, Char := Char,
                                   FindSmallest := FindSmallest,
                                   ReduceX := ReduceX, Contains := Contains);
end intrinsic;


intrinsic InternalAbsoluteModuleOverMinimalField(M::ModGrp:
         DoNice := false, All := false, Contains := false,
         Char := false, FindSmallest := false,
         OptimizeField := true, ReduceX := "Auto") -> List 
  {}
  require Characteristic(BaseRing(M)) eq 0: "Module must be defined over a number field for this function";
  G := Group(M);
  if MYNgens(G) eq 0 then
    if Type(G) eq GrpPC then
      R := GModule(Group(M), [GL(Dimension(M), Rationals())|1]);
    else
      R := GModule(Group(M), [GL(Dimension(M), Rationals())|]);
    end if;
    return [* R *];
  end if;
  R := Representation(M);
  L1 := [R(G.i) : i in [1..MYNgens(G)]];
  if Char cmpeq false and assigned M`Character then
    Char := M`Character;
  end if;
  R := NonCyclicReduction(L1, G: DoNice := DoNice, All := All, 
                                 Char := Char, FindSmallest := FindSmallest,
                                 ReduceX := ReduceX, Contains := Contains);
  return [*GModule(G, x) : x in R*];
end intrinsic;

intrinsic InternalAbsoluteModuleOverMinimalField(R::Map:
         DoNice := false, All := false, 
         Char := false, FindSmallest := false,
         OptimizeField := true, ReduceX := "All") -> List
  {}
  G := Domain(R);
  require ISA(Type(G), Grp) and IsFinite(G):
    "Argument must be a representation of a finite group";
  L1 := [R(G.i) : i in [1..MYNgens(G)]];
  require Characteristic(CoefficientRing(L1[1])) eq 0: "Representation must be defined over a number field for this function";
  R := NonCyclicReduction(L1, G: DoNice := DoNice, All := All, Char := Char, FindSmallest := FindSmallest, ReduceX := ReduceX);
  return [*Representation(GModule(G, x)) : x in R*];
end intrinsic;

intrinsic WriteRepresentationOver(R::Map, K::FldAlg:Char := false, Subfield := false) -> Map
  {Tries to write the representation over a minimal degree subfield of K}
  require IsAbsoluteField(K) and IsNormal(K) :
    "The 2nd argument must be a normal extension of Q";
  G := Domain(R);
  require Characteristic(K) eq 0: "Representation must be defined over a number field for this function";
  L1 := [R(G.i) : i in [1..MYNgens(G)]];
  L := NonCyclicReduction(L1, G:Char := Char, WriteOver := K, Subfield := Subfield);
  if #L eq 0 then
    require false: "The representation cannot be realised over K";
  end if;
  assert #L eq 1;
  if not Subfield or Degree(CoefficientRing(L[1][1][1])) eq Degree(K) then
    L := [ Matrix(K, x) : x in L[1]];
    return Representation(GModule(G, L));
  end if;
  return Representation(GModule(G, L[1]));
end intrinsic;

intrinsic WriteGModuleOver(M::ModGrp, K::FldAlg:Char := false, Subfield := false) -> ModGrp
  {Tries to write the G-module over (a minimial degree subfield of) K}
"finally in WriteGModuleOver";
  require Characteristic(BaseRing(M)) eq 0: "Module must be defined over a number field for this function";
  require IsAbsoluteField(K) and IsNormal(K) :
    "The 2nd argument must be a normal extension of Q";
  R := Representation(M);  
  G := Domain(R);
  L1 := [R(G.i) : i in [1..MYNgens(G)]];
  if Char cmpeq false and assigned M`Character then
    Char := M`Character;
  else
    Char := Character(M);
  end if;
  require IsSubfield(CharacterField(Char), K): "The target field has to contain the character field";  
  L := NonCyclicReduction(L1, G:Char := Char, WriteOver := K, Subfield := Subfield);
  if #L eq 0 then
    require false: "The G-module cannot be realised over K";
  end if;
  assert #L eq 1;
  if not Subfield or Degree(CoefficientRing(L[1][1][1])) eq Degree(K) then
    L := [ Matrix(K, x) : x in L[1]];
    return GModule(G, L);
  end if;
  return GModule(G, L[1]);
end intrinsic;

intrinsic WriteGModuleOverExtensionOf(M::ModGrp, K::FldAlg:Char := false) -> ModGrp
  {Tries to write the G-module over a minimal degree extension of K}

  require Characteristic(BaseRing(M)) eq 0: "Module must be defined over a number field for this function";
  if IsSubfield(BaseRing(M), K) then
      return ChangeRing(M, K);
  end if;
  require IsAbsoluteField(K) and IsNormal(K) :
    "The 2nd argument must be a normal extension of Q";
  R := Representation(M);  
  G := Domain(R);
  L1 := [R(G.i) : i in [1..MYNgens(G)]];
  if Char cmpeq false and assigned M`Character then
    Char := M`Character;
  end if;
  L := NonCyclicReduction(L1, G:Char := Char, Contains := K, Subfield);
  if #L eq 0 then
    require false: "The G-module cannot be realised over K";
  end if;
  assert #L eq 1;
  if IsIsomorphic(CoefficientRing(L[1][1][1]), K) then
    L := [ Matrix(K, x) : x in L[1]];
    return GModule(G, L);
  end if;
  return GModule(G, L[1]);
end intrinsic;

intrinsic WriteGModuleOverExtensionOf(M::ModGrp, K::FldRat :Char := false) -> ModGrp
  {"} // "
  return AbsoluteModuleOverMinimalField(M:Character := Char);
end intrinsic;

intrinsic Hilbert90(M::Map[GrpPerm, AlgMat]) -> Mtrx
  {Given a 1-cochain M:G -> GL(n, K), find A in GL(n, K) such that M(g) = A^(1-g)}

  G := Domain(M);
  C := M(G.0);
  n := Nrows(C);
  K := CoefficientRing(C);
  require Characteristic(K) eq 0: "Module must be defined over a number field for this function";
  au, _, mau := AutomorphismGroup(K);
  function Psi(B)
    return &+ [M(g) * InduceAut(B, g@mau) : g in G];
  end function;

  b := 1;
  t := 1;
  X := IdentityMatrix(K, n);
  M := MaximalOrder(K);
  lp := Decomposition(M, NextPrime(2^20))[1][1];
  F, mF := ResidueClassField(lp);
  p := &* Generators(K);

  tr := 0;
  repeat
    tr +:= 1;
    if tr gt 50*n then
      X := IdentityMatrix(K, n);
      tr := 0;
    end if;
    vprint Isomorphic, 1: "fail";
    for i in [1..Maximum([Floor(n/2), 1])] do
      X[Random(n-1)+1][Random(n-1)+1] +:= p^Random(Degree(K))*Random(0,1);
    end for;
    A := Psi(X);
  // TODO: do a proper modular test instead if a complete determinant 
  vprint Isomorphic, 1: "test";
  until Determinant(InduceAut(A, mF)) ne 0;
  vprint Isomorphic, 1: "OK";

  return A, Psi;
end intrinsic;

intrinsic Hilbert90(M::Map[GrpPerm, FldAlg]) -> FldAlgElt
  {Given a 1-cochain M:G -> K^*, find A such that M(g) = A^(1-g)}

  G := Domain(M);
  C := M(G.0);
  K := Parent(C);
  require Characteristic(K) eq 0: "Module must be defined over a number field for this function";
  au, _, mau := AutomorphismGroup(K);
  function Psi(B)
    return &+ [M(g) * B@(g@mau) : g in G];
  end function;

  b := 1;
  t := 1;
  X := K!1;
  M := MaximalOrder(K);
  p := &* Generators(K);

  tr := 0;
  repeat
    tr +:= 1;
    if tr gt 50 then
      X := K!1;
      tr := 0;
    end if;
    vprint Isomorphic, 1: "fail";
    X +:= p^Random(Degree(K))*Random(0,1);
    A := Psi(X);
  vprint Isomorphic, 1: "test";
  until A ne 0;
  vprint Isomorphic, 1: "OK";

  return A, Psi;
end intrinsic;

 
