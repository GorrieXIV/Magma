freeze;


declare verbose DeGraaf, 2;

intrinsic LinearRelations(f::RngUPolElt:
   kMax := Infinity(), LogLambdaMax := Infinity(), 
   Proof := true, UseAction := false, UseLLL := true,
   Power := 1,  
   Galois := false) -> Mtrx, GaloisData
  {Finds a Z-basis for the lattice of linear relations of the roots of the polynomial.}
  if Galois cmpne false then
    vprint DeGraaf, 1: "OK, reusing old results";
    G, _, S := Explode(Galois);
  else
    G, _, S := GaloisGroup(f);
  end if;
  M := S`max_comp^Power;
  r := Degree(f);
  n := #G;
  f := Degree(S`Ring);
  m := r^(r-1)*M^(r-1);
  vprint DeGraaf, 2: "m:", m;
  p := S`Prime;
  k_ex := n/f*Log(m*M)/Log(p);
  k_ex := Ceiling(k_ex);
  vprint DeGraaf, 1: "need at least precision of", k_ex, "for guaranteed results";
  vprint DeGraaf, 1: "and a precision of ", Ceiling(Log(m)/Log(p)), "for anything";
  k_ex +:= 2; // to give some space...
  log_Lambda := (n div 2)+Ilog2(2*m);
  k := Ceiling(Log(m)/Log(p))+2;
  if not Proof then
    k := Ceiling(k*1.5);
  end if;
  k := Minimum(k, kMax);
  log_Lambda_ex := Minimum(log_Lambda, LogLambdaMax);
  repeat
    log_Lambda := Minimum((2*k), log_Lambda_ex);
    vprint DeGraaf, 2: "k:", k, "Log(lambda):", Ceiling(log_Lambda);
    Z := Integers();

    gens := {G.0};
    while UseAction and #gens lt r+2 and #gens lt #G do
      repeat
        g := Random(G);
      until not g in gens;
      Include(~gens, g);
    end while;
    
    matrix := [];
    for g in gens do
      for j in [1..f] do
        ma := [];
        for i in [1..r] do
          Append(~ma, Z!Eltseq(GaloisRoot(i^g, S:Prec := k)^Power)[j]);
        end for;
        Append(~matrix, ma);
      end for;
    end for;

    matrix := Matrix(matrix);
    matrix := Transpose(matrix);
    if UseLLL then
      matrix := HorizontalJoin(IdentityMatrix(Integers(), Nrows(matrix)), 
                                                                matrix);
      matrix := VerticalJoin(matrix, 
        p^k*Matrix(
              IdentityMatrix(Integers(), Ncols(matrix))[r+1..Ncols(matrix)]));
      vprint DeGraaf, 2: "LLL...(", Nrows(matrix), Ncols(matrix), ")";        
      vtime DeGraaf, 2: l := LLL(matrix:
          UseGram, Fast := 1,
          Weight := [0: i in [1..r]] cat [log_Lambda : i in [r+1..Ncols(matrix)]]);
      sol := [];
      for i in [1..Nrows(l)] do
        if forall{j : j in [r+1..Ncols(l)] | l[i][j] eq 0} then
          s := Eltseq(l[i])[1..r];
          if &+ [ x*x : x in s] lt m^2 then
            Append(~sol, s);
          end if;
        end if;
      end for;
    else
      pk := p^k;
      vprint DeGraaf, 1: "HNF...";
      vtime DeGraaf, 1: sol := KernelMatrix(Matrix(Integers(pk), matrix));
      if Nrows(sol) eq 0 then
        kk := 0;
      else
        kk := Maximum([Valuation(Integers()!x, S`Prime) : x in Eltseq(sol) |x ne 0]);
      end if;
      Zkk := Integers(p^(k-kk));
      ss := [];
      for i in [1..Nrows(sol)] do
        sss := [];
        d := 1;
        for s in Eltseq(sol[i]) do
          fl, x := RationalReconstruction(Zkk!s);
          if not fl then
            vprint DeGraaf, 2: "Reconstruction error";
            k := Ceiling(1.2*k);
            break;
          end if;
          Append(~sss, x);
          d := Lcm(d, Denominator(x));
        end for;
        if #sss ne Ncols(sol) then
          break;
        end if;
        Append(~ss, [Integers()|x*d : x in sss]);
      end for;
      if #ss ne Nrows(sol) then
        continue;
      end if;
      sol := ss;
      if #sol ne 0 then
        sol := LLL(Saturation(Matrix(sol)));
        sol := [Eltseq(sol[i]) : i in [1..Nrows(sol)]];
      end if;
    end if;
    if exists{x : x in sol | &+ [y*y : y in x] gt m} then
      vprint DeGraaf, 1: "Sorry, I found a bad relation (too large)";
      k := Ceiling(k*2);
      continue;
    end if;
    if Proof then
      k_ex := Minimum(k_ex, kMax);
    else
      k_ex := Minimum(kMax, Ceiling(k*1.2));
    end if;
    vprint DeGraaf, 1: "lifting roots to", k_ex;
    vtime DeGraaf, 1: rt := [GaloisRoot(i, S:Prec := k_ex)^Power : i in [1..r]];
    vprint DeGraaf, 1: "Proving...";
    vtime DeGraaf, 1:
    if exists{x : x in sol | not IsWeaklyZero(&+ [rt[i]*x[i] : i in [1..r]])} then
      vprint DeGraaf, 1: "Sorry, I found a bad relation";
      k := Ceiling(k*1.2);
    else
      vprint DeGraaf, 1: "OK";
      return sol;
    end if;
  until false;
  return sol, S;
end intrinsic;

intrinsic LinearRelations(f::RngUPolElt, I::[]:
   kMax := Infinity(), LogLambdaMax := Infinity(),
   Proof := true, UseAction := false, UseLLL := true,
   Galois := false) -> Mtrx, GaloisData
  {For a polynomial f, and integral functions I on the roots, find a basis for the lattice of relations between the images of the roots under I.}
  if Galois cmpne false then
    vprint DeGraaf, 1: "OK, reusing old results";
    G, _, S := Explode(Galois);
  else
    G, _, S := GaloisGroup(f);
  end if;
  for i in I do 
    if "GalInvType" in GetAttributes(Type(i)) 
       and not assigned i`GalInvType then
      AssertAttribute(i, "GalInvType", "Other"); 
    end if;
  end for;

  M := Maximum([Bound(i, S`max_comp) : i in I]);
  r := #I;
  rr := Degree(f);
  n := #G;
  f := Degree(S`Ring);
  m := r^(r-1)*M^(r-1);
  vprint DeGraaf, 2: "m:", m;
  p := S`Prime;
  k_ex := n/f*Log(m*M)/Log(p);
  k_ex := Ceiling(k_ex);
  vprint DeGraaf, 1: 
    "need at least precision of", k_ex, "for guaranteed results";
  vprint DeGraaf, 1: 
    "and a precision of ", Ceiling(Log(m)/Log(p)), "for anything";
  k_ex +:= 2; // to give some space...
  log_Lambda := (n div 2)+Ilog2(2*m);
  k := Ceiling(Log(m)/Log(p))+2;
  if not Proof then
    k := Ceiling(k*1.5);
  end if;
  k := Minimum(k, kMax);
  log_Lambda_ex := Minimum(log_Lambda, LogLambdaMax);

  gens := {G.0};
  while UseAction and #gens lt r+2 and #gens lt #G do
    repeat
      g := Random(G);
    until not g in gens;
    Include(~gens, g);
  end while;

  repeat
    log_Lambda := Minimum((2*k), log_Lambda_ex);
    vprint DeGraaf, 1: "k:", k, "Log(lambda):", Ceiling(log_Lambda);
    Z := Integers();

    
    matrix := [];
    rt := [GaloisRoot(i, S:Prec := k) : i in [1..rr]];
    for g in gens do
      for j in [1..f] do
        ma := [];
        for i in I do
          Append(~ma, Z!Eltseq(Evaluate(i, PermuteSequence(rt, g)))[j]);
        end for;
        Append(~matrix, ma);
      end for;
    end for;

    matrix := Matrix(matrix);
    matrix := Transpose(matrix);
    if UseLLL then
      matrix := HorizontalJoin(IdentityMatrix(Integers(), Nrows(matrix)), 
                                                                matrix);
      matrix := VerticalJoin(matrix, 
        p^k*Matrix(
              IdentityMatrix(Integers(), Ncols(matrix))[r+1..Ncols(matrix)]));
      vprint DeGraaf, 1: "LLL...";        
      vtime DeGraaf, 1: l := LLL(matrix:
          UseGram, Fast := 1,
          Weight := [0: i in [1..r]] cat [log_Lambda : i in [r+1..Ncols(matrix)]]);
      sol := [];
      for i in [1..Nrows(l)] do
        if forall{j : j in [r+1..Ncols(l)] | l[i][j] eq 0} then
          s := Eltseq(l[i])[1..r];
          if &+ [ x*x : x in s] lt m^2 then
            Append(~sol, s);
          end if;
        end if;
      end for;
    else
      pk := p^k;
      vprint DeGraaf, 1: "HNF...(", Nrows(matrix), Ncols(matrix), ")";
      vtime DeGraaf, 1: sol := KernelMatrix(Matrix(Integers(pk), matrix));
      ss := [];
      if Nrows(sol) eq 0 then
        kk := 0;
      else
        kk := Maximum([Valuation(Integers()!x, S`Prime) : x in Eltseq(sol) |x ne 0]);
      end if;
      Zkk := Integers(p^(k-kk));
      for i in [1..Nrows(sol)] do
        sss := [Rationals()|];
        d := 1;
        for s in Eltseq(sol[i]) do
          fl, x := RationalReconstruction(Zkk!s);
          if not fl then
            vprint DeGraaf, 2: "Reconstruction error";
            x := #gens;
            while UseAction and #gens lt x*1.2 and #gens lt #G do
              repeat
                g := Random(G);
              until not g in gens;
              Include(~gens, g);
            end while;
            k := Ceiling(1.2*k);
            break;
          end if;
          Append(~sss, x);
          d := Lcm(d, Denominator(x));
        end for;
        if #sss eq Ncols(sol) then
          Append(~ss, [Integers()|x*d : x in sss]);
        end if;
      end for;
      if #ss ne Nrows(sol) then
        continue;
      end if;
      sol := ss;
      if #sol ne 0 then
        sol := LLL(Saturation(Matrix(sol)));
        sol := [Eltseq(sol[i]) : i in [1..Nrows(sol)]];
      end if;
    end if;
    if exists{x : x in sol | &+ [y*y : y in x] gt m} then
      vprint DeGraaf, 1: "Sorry, I found a bad relation (too large)";
      k := Ceiling(k*2);
      continue;
    end if;
    if Proof then
      k_ex := Minimum(k_ex, kMax);
    else
      k_ex := Minimum(kMax, Ceiling(k*1.2));
    end if;
    vprint DeGraaf, 1: "lifting roots to", k_ex;
    vtime DeGraaf, 1: rt := [GaloisRoot(i, S:Prec := k_ex) : i in [1..rr]];
    vprint DeGraaf, 1: "Evaluating";
    vtime DeGraaf, 1: rt := [Evaluate(i, rt) : i in I];
    vprint DeGraaf, 1: "Proving...";
    vtime DeGraaf, 1:  
    if exists{x : x in sol | not IsWeaklyZero(&+ [rt[i]*x[i] : i in [1..r]])} then
      vprint DeGraaf, 1: "Sorry, I found a bad relation";
      k := Ceiling(k*1.2);
      continue;
    else
      vprint DeGraaf, 1: "OK";
      return sol;
    end if;
  until false;
  return sol, S;
end intrinsic;

intrinsic VerifyRelation(f::RngUPolElt, I::RngSLPolElt: Galois := false,
      kMax := Infinity()) -> BoolElt
  {Let I be a multivariate polynomial in n := Degree(f) many variables. This functions verifies if I evaluated at the roots is zero.}
  if Galois cmpne false then
    vprint DeGraaf, 1: "OK, reusing old results";
    G, _, S := Explode(Galois);
  else
    G, _, S := GaloisGroup(f);
  end if;
  if "GalInvType" in GetAttributes(Type(I))  and
     not assigned I`GalInvType then
    AssertAttribute(I, "GalInvType", "Other"); 
  end if;

  M := Bound(I, S`max_comp);
  r := Degree(f);
  n := #G;
  f := Degree(S`Ring);
  p := S`Prime;
  k_ex := n/f*Log(M)/Log(p);
  k_ex := Ceiling(k_ex);
  vprint DeGraaf, 1: "need precision of", k_ex, "for guaranteed results";
  k_ex +:= 2; // to give some space...
  k := Minimum(k_ex, kMax);
  
  vprint DeGraaf, 1: "lifting roots to", k_ex;
  vtime DeGraaf, 1: rt := [GaloisRoot(i, S:Prec := k_ex) : i in [1..r]];
  vprint DeGraaf, 1: "Evaluating";
  vtime DeGraaf, 1:rt := Evaluate(I, rt);
  return IsWeaklyZero(rt);
end intrinsic;

/*
  <example>
    x := Qx.1;
    f := x^24-15*x^22+375/4*x^20-2405/8*x^18+65435/128*x^16-25905/64*x^14
           -181583/3072*x^12+8367137/18432*x^10-28198575/65536*x^8
           +1338226651/5308416*x^6-895964239/8847360*x^4+4234139/294912*x^2
           -24389830879/1592524800;
    G, _, S := GaloisGroup(f);
   time  LinearRelations(f:Proof := false, Galois := [*G, 1, S*]);
   time  LinearRelations(f:Proof, Galois := [*G, 1, S*]);

   f := x^6-5;
   G, R, S := GaloisGroup(f);
   s := LinearRelations(f:Galois := [*G, 1, S*]);
   s := sub<RSpace(Z, 6)|s>;
   R := SLPolynomialRing(Integers(), 6 : Global);
   q := &+[Random(-5, 5)*s.i : i in [1..4]];
   I := [&+[q[i]*R.i^k : i in [1..6]] : k in [1..8]];
   LinearRelations(f, I:Galois := [*G, 1, S*]);
   r := &+ [$1[#$1][i] * I[i] : i in [1..8]];
   VerifyRelation(f, r:Galois := [*G, 1, S*]);
   VerifyRelation(f, r+1:Galois := [*G, 1, S*]);

   I := [R.i : i in [1..6]];
   LinearRelations(f, I:Galois := [*G, 0,S*]);
   LinearRelations(f:Galois := [*G, 0,S*]);
   sub<RSpace(Z, 6)|$2> eq sub<RSpace(Z, 6)|$1>;

  </example>
*/

