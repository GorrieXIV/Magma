freeze;

import "ClassField1.m" : CreateHom;

intrinsic NumberField(F::FldAb) -> FldNum
{The NumberField corresponding to F}
  return NumberField(EquationOrder(F));
end intrinsic;  

/*
intrinsic AbelianExtension(K::FldAlg) -> FldAb
{Defines the Hilbert-Class field of K as an Abelian extension}
  _, m := ClassGroup(K);
  return AbelianExtension(m);
end intrinsic;  

intrinsic AbelianExtension(M::RngOrd) -> FldAb
{Defines the Hilbert-Class field of M as an Abelian extension}
  _, m := ClassGroup(M);
  return AbelianExtension(m);
end intrinsic;  
*/

intrinsic HilbertClassField(K::FldAlg[FldRat]) -> FldAlg
{Computes the Hilbert Class field of K}
  _, m := RayClassGroup(1*MaximalOrder(K)); // can't use ClassGroup
  // for quadratics, the class group comes without disc log!!!
  return NumberField(AbelianExtension(m));
end intrinsic;

intrinsic AbelianExtension(I::RngOrdIdl[RngOrd[RngInt]]) -> FldAb
{The Ray class field modulo I}
  _, m := RayClassGroup(I);
  return AbelianExtension(m);
end intrinsic;  

intrinsic AbelianExtension(I::RngOrdIdl[RngOrd[RngInt]], P :: [RngIntElt] ) -> FldAb
{The Ray class field modulo I and the infinite places in P}
  _, m := RayClassGroup(I, P);
  return AbelianExtension(m);
end intrinsic;  

intrinsic Generators(A::FldAb) -> [ ], [ ], [ ]
{}
  K := NumberField(A);
  c := A`Components;
  h := [* *];
  i := [* *];
  for j in c do
    Append(~h, FieldOfFractions(j`O)!j`ClassField.2);
    Append(~i, j`GenAut);
  end for;
  return GeneratorsSequence(K), h, i;
end intrinsic;


// TODO: make this work in the arbitrary situation!
function coeffs_in_r(e, r)
  deg := function(r)
    if r cmpeq Integers() then
      return 1;
    else
      return AbsoluteDegree(r);
    end if;
  end function;  
  p := Parent(e);
  e := [e];
  while deg(p) gt deg(r) do
    e := &cat [Eltseq(x) : x in e];
    p := Parent(e[1]);
  end while;
  if not deg(p) eq deg(r) then
    error "Error: no known subring";
  end if;  
  ChangeUniverse(~e, r);
  return e;
end function;


intrinsic Eltseq(e::FldAlgElt, k::RngInt) -> [ ]
{}
  return coeffs_in_r(e, k);
end intrinsic;

intrinsic Eltseq(e::FldAlgElt, k::FldRat) -> [ ]
{Returns coefficents over k}
  return coeffs_in_r(e, k);
end intrinsic;

intrinsic Eltseq(e::FldAlgElt, k::FldAlg) -> [ ]
{Returns coefficents over k}
  return coeffs_in_r(e, k);
end intrinsic;

/*
intrinsic AutOrder (O :: RngOrd, aut::Map) -> RngOrd
{Applies an automorphisms of the number field to an order}
  M := Module(O);
  B := BasisMatrix(O);
  M := PseudoGenerators(M);
  n := Degree(O);

  nb := [ ];
  ni := [ ];
  o := CoefficientRing(O);
  fo := FieldOfFractions(o);
  fE := FieldOfFractions(EquationOrder(O));
  "start loop";
  for i:= 1 to n do
    i;
    time Append(~nb, fE!aut(O.i));
    time Append(~ni, ideal<o | [ fo!aut(x) : x in Generators(M[i][1])]>);
  end for;
  M := KSpace(FieldOfFractions(o), n);
  m := [ <ni[i], M!Eltseq(nb[i])> : i in [1..n] ];
  "start module";
  time m := Module(m);
  "start order";
  return Order(EquationOrder(O), m);
end intrinsic;
*/

function MyEq(a,b)
  K := Domain(a);
  g := GeneratorsSequence(K);
  while BaseField(K) cmpne Rationals() do
    K := BaseField(K);
    g := g cat ChangeUniverse(GeneratorsSequence(K), Domain(a));
  end while;  
  return forall{ x : x in g |a(x) eq b(x)};
end function;

function MyMult(a,b)
  K := Domain(a);
  G := GeneratorsSequence(K);
  c := a*b;
  I := [ c(i) : i in G];
  k := BaseField(K);
  if k cmpeq Rationals() then
    return hom<K->K | I>;
  else
    g := GeneratorsSequence(k);
    i := [ c(i) : i in g];
    
    return hom<K->K | hom<k->K | i>, I>;
 end if;   
end function;

declare attributes FldNum: RelAut, Extensions;

function AbsAutomorphismExtendSingle(A, phi_orig: Check := false) 
  fp := Factorization(Degree(A));

  k := NumberField(A);
  full_c := A`Components;
  c := [i`ClassField : i in full_c];
  
  CE := BaseRing(A)`CyclotomicExtensions;
  IM := [[k|0 : i in c] : j in phi_orig];

  _, id, _ := NormGroup(A);

  if assigned k`Extensions then
    vprint ClassField, 2: "Trying to reuse former extensions";
    l := k`Extensions;
    phi := [ ];
    for f in phi_orig do
      if forall(a){ x[2] : x in l | not MyEq(x[1], f)} then
        Append(~phi, f);
      end if;
    end for;  
    vprint ClassField, 2: "OK, only ", #phi, " automorphisms to go";

    if #phi eq 0 then
      phi := [ ];
      for f in phi_orig do
        if exists(a){ x[2] : x in l | MyEq(x[1], f)} then
            Append(~phi, a);
        else
          assert false;
        end if;
      end for;  
      
      return phi;
    end if;  

  else
    phi := phi_orig;
  end if;  
      

  for ip in fp do
    p := ip[1];
    vprintf ClassField: "extending to %o-power degree subfields\n", p;
    
    pmax := Maximum([Degree(i) : i in c| Degree(i) mod p eq 0]);
    C := CE[Position([i`p2n : i in CE], pmax)];
    
    
    // OK, now we have to convert all elements of g to elements of C...
    G := [C`Abs|];
    for i in [1..#c] do
      pm := Degree(c[i]);
      if pm mod p ne 0 then
        Append(~G, 1);
        continue;
      end if;  
      ce := CE[Position([i`p2n : i in CE], pm)];
      // now the embedding from ce -> C:
      if pm ne pmax then
        Embed(NumberField(ce`Rel), NumberField(C`Rel), 
              NumberField(C`Rel).1^(pmax div pm));
      end if;
      Append(~G, full_c[i]`Gen);
    end for;

    vprintf ClassField, 3: "embedded the CyclotomicExtensions\n";

    // now we have the minor problem that the degree over C`Abs could be
    // smaller than for the original CyclotomicExtension.
    // We have to correct this:
    // meaning, we have to 
    //  - decompose the sunits (or the generator) into the sunits of C`Abs
    //  - check the individual degree and (this is bad) eventual dependencies

    base := Position([ BaseRing(i`O) : i in full_c], C`Rel);
    c_base := full_c[base];
    assert BaseRing(c_base`O) eq C`Rel;

    new_gen := [ ];
    new_ord := [ ];
    new_rep := [ ];
    new_nrep := [ ];

    // next, extend phi to C
    // if zeta is a zero of the defining polynomial of C`Rel (as it ought to)
    // things are easy: we map it to some power which happens to be a zero of 
    // the image of the defining polynomial under phi.
    zeta := C`Zeta;
    Phi := [ ];

    if Evaluate(DefiningPolynomial(C`Rel), C`Rel!zeta) eq 0 then
      assert Evaluate(DefiningPolynomial(NumberField(C`Rel)), zeta) eq 0;
      ff := DefiningPolynomial(C`Rel);
      ff := Eltseq(ff);
      for f in phi do
        coef := map<NumberField(BaseRing(A)) -> NumberField(C`Rel) |
                                       x :-> NumberField(C`Rel)!f(x)>;
        F := Polynomial([f(x) : x in ff]);
        i := 1;
        while Evaluate(F, zeta) ne 0 do
          i +:= 1;
          zeta *:= C`Zeta;
        end while;  
        Append(~Phi, hom<NumberField(C`Rel) -> NumberField(C`Rel) | 
                                       coef, NumberField(C`Rel).1^i>);
      end for;
    else
      error "Error: strange cyclotomic extension found";
    end if;

    vprintf ClassField, 3: "extended to the maximal CyclotomicExtension\n";

    single_frob := function(elt, P, zeta, pn)
      ff, mf := ResidueClassField(P);
      
      p := mf(elt);
      if p eq 0 then 
      //  "single_frob( ", elt, ", ", P, ", ", zeta, ", ", pn, " );"; 
        return false;
      end if;

      z := mf(zeta);
      assert (Norm(P)-1) mod pn eq 0;
      p := p^((Norm(P)-1) div pn);
      n := 0;
      s := ff!1;
      while s ne p  and n le pmax do
        n +:= 1;
        s *:= z;
      end while;
      assert n lt pmax;
      return n;
    end function;

    Zp := Integers(pmax);
    nc := Ncols(c_base`UnitsRaw);
    dk := [Degree(i`O) : i in full_c];
    ii := 0;

    // We have to avoid anything touching c_base`S:
    coprime := Lcm([Minimum(i) : i in c_base`S]);
    for i in [1..#c] do
      ci := full_c[i];
      // painfull, but even if the degree is the same, and S is the same
      // the Basis may vary due to the reduction in intersect.c
      if Degree(c[i]) mod p ne 0 then
        vprint ClassField, 2 :
                    "Skipping ", i, "(p:", p, ", deg:", Degree(c[i]), ")";
        Append(~new_ord, 0);
        Append(~new_rep, Matrix(Zp, nc, [0 : j in [1..nc]]));
        Append(~new_nrep, [Matrix(Zp, nc, [0 : j in [1..nc]]) : f in phi]);
        continue;
      end if;  
      ii +:= 1;

      mp := c_base`Artin;
      pp := Maximum([Degree(pp) : pp in c]);
      img := [ ];
      new := [ ];
      nnew := [ ];
      repeat
        repeat 
          pp := NextPrime(pp);
        until Gcd(pp, coprime) eq 1;
        lp := Decomposition(C`Abs, pp);
        S := sub<Domain(mp)|img>;
        for j in lp do
          // not "really" neccessary, but to consider only ideals of 
          // small norm - or ideals of degree 1 speeds up things
          // considerably.
          if Norm(j[1]) gt 1000 and Degree(j[1]) ne 1 then
            continue;
          end if;  
          vtime ClassField, 5: si := j[1] @@ mp;
          if si notin S then
            vtime ClassField, 5 : 
              s1 := single_frob(G[i]^(pmax div dk[i]), j[1], C`Zeta, pmax);
            if s1 cmpeq false then
              vprintf ClassField, 5 : "(3)ignoring %o\n", j[1];
              continue;
            end if;
            lf := [];
            for f in Phi do
              vtime ClassField, 5 : 
                s2 := single_frob(f(G[i]^(pmax div dk[i])), j[1], C`Zeta, pmax);
              if s2 cmpeq false then
                vprintf ClassField, 5 : "(2)ignoring %o\n", j[1];
                break;
              end if;
              Append(~lf, s2);
            end for;
            if #lf ne #Phi then
              vprintf ClassField, 5 : "(1)ignoring %o\n", j[1];
              continue;
            end if;
            Append(~new, s1);
            Append(~nnew, lf);
            Append(~img, si);
          else
            vprintf ClassField, 5 : "ignoring %o\n", j[1];
          end if;  
        end for;
        vprintf ClassField, 4: 
            "(currently using prime %o, #img is %o and #sub<>: %o of %o)\n",
                pp, #img, #sub<Domain(mp) | img>, #Domain(mp);
      until sub<Domain(mp) | img> eq Domain(mp);  
      img := [ Eltseq(x) : x in img];
      new := Matrix(Zp, #img, 1, new);
      nnew := Matrix(Zp, nnew);
      img := Transpose(Matrix(Zp, img));
      f, ns, _ := IsConsistent(img, Transpose(nnew));
      assert f;
      f, s, _ := IsConsistent(img, Transpose(new));
      assert f;
      ord := Order(Domain(mp)!Eltseq(s));
      Append(~new_ord, ord);
      Append(~new_rep, s);
      Append(~new_nrep, [Matrix(ns[i]) : i in [1..#Phi]]);
    end for;
    vprint ClassField : "Frob's done"; 

    tmp := Matrix(Zp, 
             [ Eltseq(new_rep[i]) : i in [1..#new_rep]] );
 
    // check if the degree is as it's supposed to
    // must be replaced by some more complicated scheme, as
    // C2xC4xC4 can be reduced to C2xC2xC4!
    new_gens, gen_trans := EchelonForm(tmp);
    n_dk := [ ];
    gen_tran := Matrix(Integers(), gen_trans);
    new_gens := gen_tran * Matrix(Integers(), tmp);
    for i in [1..Rank(new_gens)] do
      e := Eltseq(Matrix(new_gens[i]));
      d := Gcd(e);
      d := Gcd(d, pmax);
      Append(~n_dk, pmax div d);
    end for;  

    if &*n_dk lt &*dk then
      vprint ClassField : "Group decreased, adjusting things.";
      use_new_gens := true;
    else
      use_new_gens := false;
    end if;

    // OK, now we have everything as a power product of the c_base`Units
    // (Even if we don't have them, but who cares)
    // This means we're in a position to get generators for the large
    // Kummer extension: The class field + the pmax'th root of unity.

    nij := [ ];
    for f in [1..#phi] do
      ntmp := Matrix(Zp, 
               [ Eltseq(new_nrep[i][f]) : i in [1..#new_nrep]] );
      fl, ntmp, _ := IsConsistent(tmp, ntmp);         
      if not fl then
        return tmp, Matrix(Zp, 
               [ Eltseq(new_nrep[i][f]) : i in [1..#new_nrep]] );
      end if;         
      assert fl;
      Append(~nij, Matrix(Integers(), ntmp));
    end for;  
    
    // BIG step, the large Kummer extensions is generated by
    // ngens elements corresponding to gens (or trans)
    // but we won't do it, we'll work with an imaginary field instead.


    // and create the large field we have to work in:
    // XXX do I need this? And if yes: how do I create a correct version?
    // (this should be correct - up to the missing case gives the error above.
    // to be completely general however, the correct embedding have get
    // installed (the ones connecting K with NumberField(A))
   
    vprint ClassField, 2: "Creating K...";
    if use_new_gens then
      vprint ClassField, 2: "complicated case";
      nG := [ ]; nP := [ ]; n_dk := [ ];
      gen_tran := Matrix(Integers(), gen_trans);
      new_gens := gen_tran * Matrix(Integers(), tmp);
      for i in [1..Rank(new_gens)] do
        e := Eltseq(Matrix(new_gens[i]));
        d := Gcd(e);
        d := Gcd(pmax, d);
        e := [ x div d : x in e];
        e := Matrix([e]);
        x := e*Transpose(c_base`UnitsRaw);
        time x := PowerProduct(c_base`Basis, x);
        Append(~n_dk, pmax div d);
        Append(~nG, x);
        Append(~nP, ext<NumberField(C`Abs)|>.1^(pmax div d) 
                                                - NumberField(C`Abs)!x);
      end for;

      time K := NumberField(nP:Abs, Check := Check, DoLinearExtension);

      vprint ClassField, 2: "1:... done, starting on k->K:";

      inv := Matrix(Integers(), gen_trans^-1);
    
      GG := [K|];
      ii := 1;
      for i in [1..#c] do
        if Degree(c[i]) mod p eq 0 then
          x := 1;
          for j in [1..#nG] do
            x *:= K.j^inv[i][j];
          end for;  
          a := 1;
          for j in [1..#nG] do
            assert (dk[i] *inv[i][j]) mod n_dk[j] eq 0;
            a *:= nG[j]^(dk[i] * inv[i][j] div n_dk[j]);
          end for;  
          a := G[i]/a;
          f, r := IsPower(a, dk[i]);
          assert f;
          x *:= r;
          Append(~GG, x);
          ii +:= 1;
        else
          Append(~GG, 1);
        end if;
      end for;  

      im := [K| ];
      ii := 1;
      for i in [1..#c] do
        if Degree(c[i]) mod p ne 0 then
          Append(~im, 0);
        else  
//          assert Evaluate(
//                 MinimalPolynomial(NumberField(full_c[i]`O).1, Integers()),
//                 GG[i]) eq 0;
          Append(~im, hom<FieldOfFractions(full_c[i]`O) -> K|GG[i]>
                                                (full_c[i]`ClassField.2));
//          assert Evaluate(
//                 MinimalPolynomial(full_c[i]`ClassField.2, Integers()),
//                 im[i]) eq 0;
          ii +:= 1;
        end if;                                        
      end for;  
    else
      K := NumberField(
        [ext<NumberField(C`Abs)|>.1^dk[i]-NumberField(C`Abs)!G[i]
                 : i in [1..#c] | Degree(c[i]) mod p eq 0]:
                        Abs, DoLinearExtension, Check := false);
      vprint ClassField, 2: "2: ... done, starting on k->K:";

      GG := [K|];
      ii := 1;
      for i in c do
        if Degree(i) mod p eq 0 then
          Append(~GG, K.ii);
          ii +:= 1;
        else
          Append(~GG, 1);
        end if;
      end for;  

      im := [K| ];
      ii := 1;
      for i in [1..#c] do
        if Degree(c[i]) mod p ne 0 then
          Append(~im, 0);
        else  
//          assert Evaluate(
//                 MinimalPolynomial(NumberField(full_c[i]`O).1, Integers()),
//                 K.ii) eq 0;
          Append(~im, hom<FieldOfFractions(full_c[i]`O) -> K|K.ii>
                                                (full_c[i]`ClassField.2));
//          assert Evaluate(
//                 MinimalPolynomial(full_c[i]`ClassField.2, Integers()),
//                 im[i]) eq 0;
          ii +:= 1;
        end if;                                        
      end for;  


    end if;                    

   
//    assert forall{ im[i] eq 0 or
//             Evaluate(MinimalPolynomial(k.i, Integers()), im[i]) eq 0 :
//                                       i in [1..#im] };
    hkK := hom<k->K | im>;

    vprint ClassField, 2: "... done, building phi on K";
    
    B := [ ];
    d := [pmax div dk[i] : i in [1..#c]];
    for f in [1..#phi] do 
      BB := [ ];
      if use_new_gens then
        new_nij := Matrix(Integers(), 
                          gen_trans*Matrix(Zp, nij[f])*gen_trans^-1);
        dd := [pmax div i : i in n_dk];                  
        for i in [1..#nG] do
          a := &* [ nG[j]^Integers()!(dd[j]*new_nij[i][j] / dd[i])
                                                        : j in [1..#nG]];
          a := Phi[f](nG[i])/a;
          vprintf ClassField, 3: "(%oth root)", n_dk[i];
          vtime ClassField, 3: t, r := IsPower(a, n_dk[i]);
          if not t then
            return a, nG, n_dk, new_nij;
          end if;  
          assert t;
          vprint ClassField, 3: "(OK)";
          b := r * &* [ K.j^(new_nij[i][j]) : j in [1..#nG]];
          // time assert Evaluate(MinimalPolynomial(K.i, Integers()), b) eq 0;
          Append(~BB, b);
        end for;
      else
        for i in [1..#c] do
          if Degree(c[i]) mod p ne 0 then
            continue;
          end if;  

          e := [ d[j]*nij[f][i][j] / d[i] : j in [1..#c]];
          ChangeUniverse(~e, Integers());
          a := &* [ G[j] ^ e[j] : j in [1..#c]];
          a := Phi[f](G[i])/a;
          vprintf ClassField, 3: "(%oth root)", dk[i];
          vtime ClassField, 3: t, r := IsPower(a, dk[i]);
          assert t;
          vprint ClassField, 3: "(OK)";
          b := r * &* [ GG[j]^(nij[f][i][j]) : j in [1..#c]];
          // time assert Evaluate(MinimalPolynomial(K.i, Integers()), b) eq 0;
          Append(~BB, b);
        end for;  
      end if;  
      Append(~B, BB);
    end for; 

    vprint ClassField, 2: "... done, building phi on k";

    phi_K := [ ];
    for f in [1..#Phi] do
      PHI := hom<BaseField(K) -> K | K!Phi[f](BaseField(K).1)>;
      Append(~phi_K, hom<K->K | PHI, B[f]>);
    end for;  

    vprint ClassField, 2: "... done, starting on coercing the basis";

    bb := hkK(Basis(k, k));
    b := [x : x in bb | x ne 0];

    vprint ClassField, 2: "... done, building the matrix";

    /*
     * hard to believe, but the following function is actually a runtime
     * problem. One should think about this a but more
     */
    coeff := function(x)
      return ChangeUniverse(
             &cat [Eltseq(FieldOfFractions(C`Rel)!y) : y in Eltseq(x)],
                       BaseField(k));
    end function;  
    vtime ClassField, 3: M := Matrix([ coeff(x) : x in b]);


    // now restrict it to the field we're interested in.
    // this goes as follows: compute the image of c[i]`Gen
    // and solve some linear equation ...


    for i in [1..#c] do
      if Degree(c[i]) mod p ne 0 then
        continue;
      end if;  
      for f in [1..#phi] do
        m := VerticalJoin(M, Matrix([coeff(-phi_K[f](hkK(k.i)))]));
        vprintf ClassField, 3: "(kernel)";
        vtime ClassField, 3: m := KernelMatrix(m);
        vprint ClassField, 3: "(OK)";
        assert Nrows(m) eq 1;
        m := m/m[1][Ncols(m)];
        m := Matrix(BaseField(k), m);
        mm := [ ];
        ii := 1;
        for i in bb do 
          if i eq 0 then
            Append(~mm, 0);
          else
            Append(~mm, m[1][ii]);
            ii +:= 1;
          end if;
        end for;  
        IM[f][i] := k!mm;
      end for;  
    end for;
  end for;

  PHI := [map<BaseField(k) -> k | x:->k!f(x)> : f in phi];

  PHI := [hom<k -> k | PHI[f], IM[f]> : f in [1..#phi]];

  if assigned k`Extensions then
    l := k`Extensions;
  else
    l := [ ];
  end if;
  for i in [1..#phi] do
    Append(~l, <phi[i], PHI[i]>);
  end for;
  k`Extensions := l;

  phi := [ ];
  for f in phi_orig do
    if exists(a){ x[2] : x in l | MyEq(x[1], f)} then
        Append(~phi, a);
    else
      assert false;
    end if;
  end for;  
  
  return phi;
end function;

RelAutFormat := recformat<S, sS, s, img, mp>;
AutGFormat := recformat<AutomorphismGroup, CohomologyModule>;

intrinsic Automorphisms(A::FldAb: All := false, Over := false) -> []
{Computes the (relative) automorphisms of A}
  G, L, M := AutomorphismGroup(A:All := All, Over := Over);
  return L;
end intrinsic;

intrinsic AutomorphismGroup(A::FldAb: All := false, Over := false, Gens := false, Check := false) -> GrpAb, PowMap, Map 
{Computes the (relative) automorphisms of A}

  require All cmpeq false or Over cmpeq false:
   "All and Over cannont be combined";
  require Over cmpeq false or 
    ( Type(Over) eq SeqEnum and #Over ge 1 and Type(Over[1]) eq Map) :
    "Over must be a sequenc of Maps";

  if assigned A`Record and assigned A`Record`AutomorphismGroup and All then
    return Explode(A`Record`AutomorphismGroup);
  end if;


  _, g, gg := Generators(A);
  c := Components(A);

  K := NumberField(A);

  if assigned K`RelAut then
    ra := K`RelAut`mp;
    G := Domain(ra);
    P := Codomain(ra);
    m := ra;
  else  
    img := [* *];

    for i in [1..#g] do
      vprint ClassField, 1: "Computing generator ", i;
      a := g[i];
      F := Parent(a);
      l := [F|1, a];
      for j in [3..Degree(c[i])] do
        l[j] := l[j-1]*a;
      end for;
      ha := gg[i];

      vtime ClassField, 4: assert Evaluate(DefiningPolynomial(c[i]), ha) eq 0;
      
      Append(~l, -ha);

      l := [ &cat [ Eltseq(x) : x in Eltseq(y)] : y in l];
      L := Matrix(BaseField(A), l);
      vprintf ClassField, 3: "(Kernel)";
      vtime ClassField, 3: l := KernelMatrix(L);
                         // maybe use Newton instead??? TODO
      vprint ClassField, 3: "(done)";
      assert Nrows(l) eq 1;

      l := Eltseq(l);
      nn := NumberField(c[i]);
      n := 1/l[#l];
      l := [n * l[i] : i in [1..#l-1]];
      n := nn!l;
      vtime ClassField, 4: assert Evaluate(DefiningPolynomial(c[i]), n) eq 0;
      Append(~img, n);
      
    end for;

    G := AbelianGroup([Degree(c[i]) : i in [1..#g]]);

    P := Maps(K, K);
    S := {@ P| @};
    s := {@ @};
    sS := {@ @};

    Gen := GeneratorsSequence(K);
    for i in [1..#c] do
      gen := Gen;
      gen[i] := img[i];
      h := hom<K->K | gen>;
      Include(~S, h);
      Include(~s, G.i);
      Include(~sS, gen);
    end for;  

    K`RelAut := rec<RelAutFormat | S := S, sS := sS, s := s, img := img>;

    mp := function(x, K)
      S := K`RelAut`S;
      s := K`RelAut`s;
      i := Position(s, x);
      if i ne 0 then
        return S[i];
      end if;
      a := Eltseq(x);
      gen := [K|];
      img := K`RelAut`img;
      for i in [1..#a] do
        n := Parent(img[i]);
        h := hom<n->n | img[i]>;
        b := n.1;
        for j in [1..a[i]] do
          b := h(b);
        end for;
        gen[i] := b;
      end for;
      h := hom<K->K | gen>;
      Include(~K`RelAut`S, P!h);
      Include(~K`RelAut`s, x);
      Include(~K`RelAut`sS, gen);
      return P!h;
    end function;  

    imp := function(x, K)
      sS := K`RelAut`sS;
      s := K`RelAut`s;
      Gen := [x(t) : t in GeneratorsSequence(K)];
      i := Position(sS, Gen);
      if i ne 0 then
        return s[i];
      end if;
      G := Domain(K`RelAut`mp);
      for a in G do
        if a in s then
          continue;
        end if;  
        b := Eltseq(a);
        gen := [K|];
        img := K`RelAut`img;
        for i in [1..#b] do
          n := Parent(img[i]);
          h := hom<n->n | img[i]>;
          c := n.1;
          for j in [1..b[i]] do
            c := h(c);
          end for;
          gen[i] := c;
        end for;
        h := hom<K->K | gen>;
        Include(~K`RelAut`S, P!h);
        Include(~K`RelAut`s, a);
        Include(~K`RelAut`sS, gen);
        if gen eq Gen then
          return a;
        end if;  
      end for;  
      error "Error, this must not happen";
    end function;  

    m := map<G -> P | x :-> mp(x, K), y :-> imp(y, K)>;

    K`RelAut`mp := m;                  
  end if;  

  // now it's time to deal with the All and Over things...
  k := BaseField(K);
  if All cmpne false then
    vprint ClassField, 2: "Computing automorphisms of the base field...";
    g := Automorphisms(k);
    // reduce g to include only a (minimal) set of generators:
    vprint ClassField, 2: "... done. Computing GenericGroup...";
    g, mg := GenericGroup(g: Id := hom<k->k|GeneratorsSequence(k)>,
                             Eq := MyEq,
                             Mult := MyMult);
                             
    vprint ClassField, 2: "... done. Finding small set of generators...";
    g := FindGenerators(g);                         
    vprint ClassField, 2: "... done. Extending ", #g, " automorphisms";
    // extend them...
  else  
    g := Over; 
    if Over cmpne false then
      vprint ClassField, 2: "Extending ", #g, " automorphisms";
    else  
      vprint ClassField, 2: "Extending no automorphisms";
      if Gens then
        return [m(G.i) : i in [1..Ngens(G)]] ;
      end if;
      return G, P, m;
    end if;  
  end if;  

  h := AbsAutomorphismExtendSingle(A, g:Check := Check);
  // and build the large group!
  if Gens then
    return [m(G.i) : i in [1..Ngens(G)]] cat h;
  end if;
  vprint ClassField, 2: "... done. Computing large GenericGroup...";
  G, m := GenericGroup([m(G.i) : i in [1..Ngens(G)]] cat h:
                Id := hom<K->K | GeneratorsSequence(K)>,
                Eq := MyEq, Mult := MyMult);
  P := G`GenericGroup`elts;              

  if All then
    if assigned A`Record then
      A`Record := rec<AutGFormat| CohomologyModule := A`Record`CohomologyModule, AutomorphismGroup := <G, P, m>>;
    else
      A`Record := rec<AutGFormat|AutomorphismGroup := <G, P, m>>;
    end if;
  end if;
  return G, P, m;
end intrinsic;  
declare attributes FldNum: Artin;

intrinsic FrobeniusAutomorphism(A::FldAb, p::RngOrdIdl) -> Map
{The Frobenius automorphism corresponding to the prime p}

  require IsPrime(p) and Order(p) eq MaximalOrder(BaseRing(A)) :
     "Prime must be a prime ideal of the BaseRing";

  K := NumberField(A);
  if assigned K`Artin then
    return K`Artin(p);
  end if;  

  G, S, m := AutomorphismGroup(A);

  c := Components(A);

  K := NumberField(A);

  a := [K| ];

  for i in [1..#c] do
    q,mq := quo<c[i] | c[i] !! p>;
    pe := mq(c[i].2);
    e := Norm(p);  // use smaller exponent!!!
    pe := pe ^ e;
    pe := pe @@ mq;
    Append(~a, pe);
  end for;

  q,mq := ResidueClassField(p);

  S := {@ m(x) : x in G @};

  for i in S do
    im := [i(c[j].2) : j in [1..#c]];
    // this may fail!!! there could be "wrong" denominators in mq(w)
    if forall { j : j in [1..#im] | 
           forall { w : w in Eltseq(im[j] - a[j]) | IsZero(mq(w)) } } then
      found := i;     
      break;
    end if;
  end for;  
  if not assigned found then
    error "Error: Frobenius not found";
  end if;  
  return found;
end intrinsic;

intrinsic ArtinMap(A::FldAb) -> Map
{The Artin map of A. That is given an ideal this map will return the corresponding automorphism.}
  m, P, Inf := NormGroup(A);

  K := NumberField(A);
  if assigned K`Artin then
    return K`Artin;
  end if;  

  M := Order(P);

  G := Domain(m);
  gens := [ ];
  img := [ ];
  p := NextPrime(100);
  mP := Minimum(P);
  mP *:= Lcm([Integers()!Norm(Discriminant(Polynomial(BaseField(A), 
             DefiningPolynomial(x)))) : x in Components(A)]);
  while sub<G|img> ne G do
    while Gcd(mP, p) ne 1 do
      p := NextPrime(p);
    end while;  

    lp := Decomposition(M, p);
    for x in lp do
      i := x[1] @@ m;
      if i notin sub<G|img> then
        Append(~gens, x[1]);
        Append(~img, i);
      end if;  
    end for;
    p := NextPrime(p);
  end while;  

  GG, S, am := AutomorphismGroup(A);

  mp := [ ];
  for i in [1..#gens] do
    Append(~mp, <img[i], FrobeniusAutomorphism(A, gens[i])@@am>);
  end for;

  // h := hom<G -> GG | mp>;  // does not work ...
  h := CreateHom(G, GG, mp);

  K`Artin := Inverse(m)*h*am;

  return K`Artin;
end intrinsic;



// TODO AbelianExtension(K::FldNum) -> FldAb
//      AbelianExtension(K::FldNum, k::FldNum) -> FldAb
//      DecompositionType(K::FldNum, p::Prime) -> ...
//      DecompositionType(K::FldAb, p::Prime) -> ...
