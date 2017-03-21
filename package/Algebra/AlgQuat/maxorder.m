freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Maximal Orders for Quaternion Algebras
// November 2005-January 2006, John Voight
//
//////////////////////////////////////////////////////////////////////////////

import "hilbert.m" : EvenHilbertSymbol;

declare attributes AlgQuat: MaximalOrder;

//-------------
//
// Algorithm to compute a maximal order for a quaternion algebra over
// a general number field and associated routines.
//
//-------------

intrinsic SafeInverseUniformiser(p::RngOrdIdl) -> FldOrdElt
  {Returns an element pi such that v_p(pi) = -1, v_q(pi) >= 0 for all q,
   v_q(pi) = 0 for all other primes q which lie over the same rational 
   prime as p.}

  O := Order(p);
  if false and CoefficientRing(O) cmpne Integers() then
    O := AbsoluteOrder(O);
  end if;
  pp := O!!p;
  facts := Decomposition(Order(pp),Factorization(Norm(pp))[1][1]);
  I := [q[1] : q in facts | q[1] ne pp];
  V := [0 : i in I];
  w := WeakApproximation([pp] cat I, [-1] cat V);
  return FieldOfFractions(Order(p))!w;
end intrinsic;

intrinsic TameOrder(A::AlgQuat[FldAlg]) -> AlgAssVOrd
  {Computes an order O of the quaternion algebra A whose odd reduced
   discriminant is squarefree.}

  F := BaseField(A);

  // This might be an expensive step, but is necessary.
  // (And it should need to be only called once per F!)
  Z_F := MaximalOrder(F);

  // Correction factor for even primes
  dOfact := Factorization(ideal<Z_F | 1/4>);
  dO := ideal<Z_F | 1>;

  S := [];
  I := [];
  dKfacts := [];

  _, _, Astandard, phi := StandardForm(A);
  As := [Astandard.i@@phi : i in [1..3]];
  for i := 1 to 3 do
    // Force integrality
    alpha := As[i];
    alpha *:= Denominator(Z_F!Norm(alpha));
 
    f := MinimalPolynomial(alpha);
    if not IsIrreducible(f) then
      // alpha yields a zerodivisor
      alphabar := Roots(f)[1][1];
      // print alpha, f;
      M2F, phi := MatrixRing(A, alpha-alphabar);

      // Hard-coded matrix units; these generate the maximal order M_2(Z_F)
      mU := [Inverse(phi)(M2F.i) : i in [1..2]];
      O := Order(mU);
      O`Discriminant := ideal<Z_F | 1>;
      O`FactoredDiscriminant := []; 
      return O;
    end if;

    // We actually only want a maximal order away from 2, and want
    // the order generated by alpha at 2.  We also want to remember
    // the factorization of the discriminant of K.  So it seems best
    // to work directly, prime by prime.
    O_K := ext<Z_F | MinimalPolynomial(alpha)>;
    K := FieldOfFractions(O_K);
    dK := Z_F !! Discriminant(O_K);

    // The following should be the most expensive step.  But according 
    // to [Voight], computing maximal orders is probablistic 
    // polynomial-time equivalent to factorization, so it has to be done!
    dKfact := Factorization(dK);
    dKfactnew := [];
    for pp in dKfact do
      if AbsoluteNorm(pp[1]) mod 2 ne 0 then
        if pp[2] gt 1 then
          O_K := pMaximalOrder(O_K, pp[1]);
        end if;
        if pp[2] mod 2 eq 1 then
          Append(~dKfactnew, <pp[1],1>);
        end if;
      else
        // We ignore even primes.  (Adding 2-integral elements may not
        // even return an order!)
        Append(~dKfactnew, pp);
      end if;
    end for;

    // Now combine the factorizations of dKfactnew and dOfact.
    // Would be nice to do dOfact *:= dKfactnew, like we can for integers...
    for pp in dKfactnew do
      blfound := false;
      for j := 1 to #dOfact do
        if dOfact[j][1] eq pp[1] then
          dOfact[j][2] +:= pp[2];
          blfound := true;
          break j;
        end if;
      end for;
      if not blfound then
        Append(~dOfact, pp);
      end if;
    end for; 

    // Store the new generator as an element of the quaternion algebra,
    // and store the coefficient ideal
    // Assumes (correctly for now anyway) that the pseudobases of the 
    // modules O_K have 1 as their first generator.
    S[i] := Eltseq(K ! O_K.2)[2]*alpha;
    I[i] := PseudoBasis(Module(O_K))[2][1];
    dKfacts[i] := dKfactnew;
  end for;

  sortFact := function(pp,qq);
    p := Generator(pp[1] meet Integers());
    q := Generator(qq[1] meet Integers());
    if p lt q then
      return -1;
    elif p gt q then
      return 1;
    else
      return 0;
    end if;
  end function;

  O := Order(S, I);
  O`FactoredDiscriminant := Sort([<pp[1], pp[2] div 2> : pp in dOfact], sortFact); 
  O`Discriminant := &*[ pp[1]^pp[2] : pp in O`FactoredDiscriminant];
  dKs := [ &*[ pp[1]^pp[2] : pp in dKfacts[i] ] : i in [1..3]];
  O`TraceZeroInternalData := <S, I, dKs>;
  return O;
end intrinsic;

// Computes a pp-maximal order for pp an even prime.
function pEvenMaximalOrder(O,pp);
  Oold := O;
  A := Algebra(O);

  // The output of EvenHilbertSymbol includes an element xi such that
  // Z_F[xi] has discriminant not divisible by pp.

  k, mk := ResidueClassField(pp);
  h, xi := EvenHilbertSymbol(A, pp);
  if h eq -1 and Valuation(Discriminant(O),pp) eq 1 then
    return O;
  end if;

  J := ideal<O | [xi-1] cat Generators(pp)>;
  O := RightOrder(J);
 
  // Compute a tame pp-order containing O by finding linear combinations of 
  // the two elements zeta which have norm with valuation >= 2 at pp.
  piinvFp := SafeInverseUniformiser(pp);
  repeat
    // Find elements zeta in O which are locally linearly independent 
    // generators for O and have trace zero (hence orthogonal to xi).
    B := TraceZeroSubspace(O);
    zetas := [ [gi*(A ! B[i][2]) : gi in Generators(B[i][1]) ] : i in [1..3] ];
    for i in [1..3] do
      _, t := Min([Valuation(Norm(z), pp) : z in zetas[i]]);
      zetas[i] := [zetas[i][t]];
    end for;
    zetas := &cat(zetas);
    T := [Valuation(Norm(z), pp) : z in zetas];
    mt, t := Max(T);

    // print Valuation(Discriminant(O), pp), T;
    if zetas[t] in ideal<O | Generators(pp)> then
      J := ideal<O | [zetas[t]*piinvFp] cat Generators(pp)>;
    else
      if mt le 1 then
        // Just normalize the quadratic form to find a tame element.
        T0 := [t : t in [1..3] | T[t] eq 0];
        for i in T0 do
          zetas[i] *:= Sqrt(1/mk(Norm(zetas[i])))@@mk;
        end for;
        for i := 2 to #T0 do
          zetas[T0[i]] +:= zetas[T0[1]];
        end for;
        T := [Valuation(Norm(z), pp) : z in zetas];
        mt, t := Max(T);
        if mt le 1 then
          J := ideal<O | [z : z in zetas | Valuation(Norm(z),pp) gt 0] cat Generators(pp)>;
        else
          J := ideal<O | [zetas[t]] cat Generators(pp)>;
        end if;      
      else
        J := ideal<O | [zetas[t]] cat Generators(pp)>;
      end if;
      if RightOrder(J) eq O then
        J +:= ideal<O | xi-1>;
      end if;
    end if;
    O := RightOrder(J);
  until Valuation(Discriminant(O), pp) le 1;

  rts := Roots(PolynomialRing(k) ! [mk(Norm(xi)), -mk(Trace(xi)), 1]);

  // Case that A is unramified at pp and O is not yet pp-maximal 
  if h eq 1 and Valuation(Discriminant(O), pp) eq 1 then
    if Valuation(Discriminant(O), pp) gt 0 then 
      // Case that k[xi] splits
      if #rts eq 2 then
        mkz := rts[1];
        z := mkz[1]@@mk;

        // Compute an element zeta in the pp-radical, i.e. 
        // Norm(zeta) = -zeta^2 is in pp  
        zetasgt0 := [zetas[t] : t in [1..#T] | T[t] gt 0];
        zetas0 := [zetas[t] : t in [1..#T] | T[t] eq 0];
        if zetasgt0 eq [] then
          zeta1 := zetas0[1];
          zeta2 := zetas0[#zetas0];
          zeta := (Sqrt(mk(Norm(zeta1)))@@mk)*zeta2 + 
                  (Sqrt(mk(Norm(zeta2)))@@mk)*zeta1;
        else
          zeta := zetasgt0[1];
        end if;

        J := ideal<O | [xi-z,zeta] cat Generators(pp)>;
        O := RightOrder(J);
        while Valuation(Discriminant(O), pp) gt 0 do
          ezeta := Valuation(Norm(zeta), pp);
          if ezeta eq 0 then
            if zeta in O then
              // Valuation (ezeta) is zero; need to add to it another
              // element of valuation zero to get something of larger
              // valuation.
              if #zetas0 gt 0 then
                zeta := (Sqrt(mk(Norm(zetas0[1])))@@mk)*zeta +
                        (Sqrt(mk(Norm(zeta)))@@mk)*zetas0[1];
              else
                zeta := zetasgt0[2];
              end if;
            else
              O := Adjoin(O, zeta);
            end if;
          elif ezeta gt 1 then
            zeta *:= piinvFp;
          end if;
          J := ideal<O | [xi-z,zeta] cat Generators(pp)>;
          O := RightOrder(J);
        end while;
      else
        // Case that k[xi] is unramified field extension
        zetas0 := [z : z in zetas | Valuation(Norm(z), pp) eq 0];
        zeta := zetas0[1];
        z := mk(Norm(zeta));
        z := Sqrt(z)@@mk;

        J := ideal<O | [zeta-z] cat Generators(pp)>;
        O := RightOrder(J);
      end if;
    end if;
  end if;

  if assigned Oold`TraceZeroInternalData then
    O`TraceZeroInternalData := Oold`TraceZeroInternalData;
  end if;

  O`FactoredDiscriminant := [qq : qq in FactoredDiscriminant(Oold) | qq[1] ne pp];
  O`Discriminant := 1*BaseRing(O);
  for qq in [qq : qq in O`FactoredDiscriminant] do
    O`Discriminant *:= qq[1]^qq[2];
  end for;

  if h eq -1 then
    O`FactoredDiscriminant cat:= [<pp, 1>];
    O`Discriminant *:= pp;
    return O, 1;
  else
    return O, 0;
  end if;
end function;

intrinsic pMaximalOrder(O::AlgAssVOrd[RngOrd[RngInt]], p::RngOrdIdl) -> AlgAssVOrd, RngIntElt
  {Computes a p-maximal order O' containing O in a quaternion algebra A defined
   over a number field and ord_p(disc(O')).}

    require IsPrime(p) : "Argument 2 must be a prime ideal";
    require IsCoercible(PowerIdeal(CoefficientRing(O)), p) : "Argument 2 must be an ideal of the coefficient ring of argument 1";

  // Just a different name.
  pp := p;

  if assigned O`FactoredDiscriminant and
    pp notin [qq[1] : qq in O`FactoredDiscriminant] then
    return O;
  end if;

  vdpp := Valuation(Discriminant(O), pp);
  if vdpp eq 0 or
    (vdpp eq 1 and HilbertSymbol(Algebra(O), pp) eq -1) then
    return O;
  end if;
  Oold := O;

  if Generator(pp meet Integers()) eq 2 then
    return pEvenMaximalOrder(O,pp);
  end if;

  Z_F := BaseRing(O);

  // Check to see if results from the calculation of the tame order exist
  pi := SafeUniformiser(pp);
  piinv := SafeInverseUniformiser(pp);

  if assigned O`TraceZeroInternalData then
    S := O`TraceZeroInternalData[1];
    I := O`TraceZeroInternalData[2];
    discs := O`TraceZeroInternalData[3];
  else
    Tr0 := TraceZeroSubspace(O);
    S := [Tr0[i][2] : i in [1..3]];
    I := [Tr0[i][1] : i in [1..3]];
    discs := [I[i]^2*Norm(S[i]) : i in [1..3]];
    O`TraceZeroInternalData := <S, I, discs>;
  end if;

  for i := 1 to 3 do
    if IsZero(discs[i]) then
      M2F, phi := MatrixRing(Algebra(O), S[i]);

      // Hard-coded matrix units; these generate the maximal order M_2(Z_F)
      mU := [Inverse(phi)(M2F.i) : i in [1..2]];
      O := Order(mU);
      O`Discriminant := ideal<Z_F | 1>;
      O`FactoredDiscriminant := []; 
      return O;
    end if;
    
    edisc := Floor(Valuation(discs[i],pp)/2);
    pival := Valuation(I[i],pp);
    if pival gt 0 then
      O := RightOrder(ideal<O | [S[i]*pi^pival] cat Generators(pp^edisc)>);
    else
      O := RightOrder(ideal<O | [S[i]*piinv^Abs(pival)] cat Generators(pp^edisc)>);
    end if;
  end for;
  
  assert Valuation(Discriminant(O),pp) le 2;

  repeat
  Tr0 := TraceZeroSubspace(O);
  S := [Tr0[i][2] : i in [1..3]];
  I := [Tr0[i][1] : i in [1..3]];
  discs := [I[i]^2*Norm(S[i]) : i in [1..3]];

  for i := 1 to 3 do
    agens := Generators(I[i]);
    if Valuation(I[i],pp) gt 0 then
      calpha := SafeUniformizer(pp)^Valuation(I[i],pp);
    else
      calpha := piinv^(-Valuation(I[i],pp));
    end if;
    S[i] := calpha*S[i];
    I[i] /:= calpha;

    assert Valuation(I[i],pp) eq 0;

    calpha := 1;
    while piinv*S[i] in O do
      calpha *:= piinv;
    end while;
    S[i] := calpha*S[i];
    discs[i] /:= calpha^2;
  end for;

  // Find the index of a maximal commutative suborder with 
  // discriminant prime to pp
  if Valuation(Discriminant(O),pp) gt 0 then
  for i := 1 to 3 do
    if Valuation(discs[i], pp) gt 1 then
      O := RightOrder(ideal<O | [S[i]] cat Generators(pp)>);
    elif Valuation(discs[i], pp) eq 0 then
      alpha  := S[i];
      // O is maximal at pp if and only if a is not a square modulo pp
      k, mk := ResidueClassField(pp);
      mka := mk(Norm(alpha));
      rts := Roots(PolynomialRing(k) ! [mka,0,1]);
      if #rts ne 0 then
        z := rts[1][1]@@mk;
        O := RightOrder(ideal<O | [alpha-z] cat Generators(pp)>);
      end if;
    end if;
    if Valuation(Discriminant(O),pp) eq 0 then
      break i;
    end if;
  end for;
  end if;
  until Valuation(Discriminant(O),pp) eq 0 or
    (HilbertSymbol(Algebra(O),pp) eq -1 and Valuation(Discriminant(O),pp) eq 1);

  _ := Discriminant(O : Recompute := true);
  O`FactoredDiscriminant := Factorization(Discriminant(O));

  if Valuation(Discriminant(O),pp) eq 1 then
    return O, 1;
  else
    return O, 0;
  end if;
end intrinsic;

/*
intrinsic MaximalOrder(A::AlgQuat[FldNum]) -> AlgAssVOrd
  {Computes a maximal order O in a quaternion algebra A defined 
   over a number field.}

  FZF := FieldOfFractions(MaximalOrder(BaseField(A)));
  AFZF, m := ChangeRing(A, FZF);
  M := MaximalOrder(AFZF);
  M`ChangeRingMap := m;
  return M;
end intrinsic;
*/

intrinsic MaximalOrder(A::AlgQuat[FldAlg[FldRat]]) -> AlgAssVOrd
  {Computes a maximal order O in a quaternion algebra A defined 
   over a number field.}
  if assigned A`MaximalOrder then
    return A`MaximalOrder;
  end if;

  F := BaseField(A);

  // This might be an expensive step, but is necessary.
  // And it should need to be only called once per F.
  Z_F := MaximalOrder(F);

  // First compute a tame order, then make it maximal
  Otame := TameOrder(A);
  O := MaximalOrder(Otame);
  A`MaximalOrder := O;
  return O;
end intrinsic;

function QuaternionMaximalOrder(O)
//::AlgAssVOrd[RngOrd]) -> AlgAssVOrd
//{Computes a maximal order containing the order O (in a quaternion algebra).}

  if assigned O`IsMaximal and O`IsMaximal then
    return O;
  end if;

  A := Algebra(O);

  assert ISA(Type(A), AlgQuat);
  // absolute extensions only have been handled here
  assert CoefficientRing(CoefficientRing(O)) cmpeq Integers();

  if assigned A`MaximalOrder and &and[x in A`MaximalOrder : x in ZBasis(O)] then
    return A`MaximalOrder;
  end if;

  dOfact := FactoredDiscriminant(O);

  // Second step: for each odd prime, compute a p-maximal order 
  dOfacteven := [];
  dOfactfinal := [];
  for pp in dOfact do 
    // Skip the even primes; treat them below
    if Generator(pp[1] meet Integers()) eq 2 then
      Append(~dOfacteven, pp[1]);
      continue pp;
    end if;
    O := pMaximalOrder(O, pp[1]);
  end for;

  // Last major step: Cope with the even primes
  for pp in dOfacteven do 
    O := pEvenMaximalOrder(O, pp);
  end for;

  assert O`Discriminant eq Discriminant(O : Recompute := true);

  O`IsMaximal := true;
  return O;  
end function;

intrinsic IspMaximal(O::AlgAssVOrd[RngOrd], p::RngOrdIdl) -> BoolElt
  {Returns true iff O is a maximal order at p.}

  if assigned O`IsMaximal and O`IsMaximal then
    return true;
  end if;
  A := Algebra(O);
  require Type(A) eq AlgQuat : "Only implemented for orders in quaternion algebras";

  require IsPrime(p) : "Argument 2 must be prime";
  require IsCoercible(PowerIdeal(CoefficientRing(O)), p) : "Argument 2 must be an ideal of the coefficient ring of argument 1";
  v:= Valuation(Discriminant(O), p);
  return (v eq 0) or (v eq 1 and HilbertSymbol(A,p) eq -1);
end intrinsic;

intrinsic IspMaximal(O::AlgQuatOrd, p::RngElt) -> BoolElt
  {"} // "

  if assigned O`IsMaximal and O`IsMaximal then
    return true;
  end if;
  A := Algebra(O);

  ok, p:= IsCoercible(Integers(BaseField(A)), p);
  require ok and IsPrime(p) : "p must be prime ideal of the maximal order of the base field";
  v:= Valuation(Discriminant(O), p);
  return (v eq 0) or (v eq 1 and HilbertSymbol(A,p) eq -1);
end intrinsic;

intrinsic IsMaximal(O::AlgAssVOrd) -> BoolElt
  {Returns true iff O is a maximal order.}

  A := Algebra(O);
  require Type(A) eq AlgQuat : "Only implemented for orders in quaternion algebras";

  if not assigned O`IsMaximal then
    dfacts := FactoredDiscriminant(O);
    O`IsMaximal := forall{ f : f in dfacts | f[2] eq 1 } and
                   forall{ f : f in dfacts | HilbertSymbol(A, f[1]) eq -1 };
    if O`IsMaximal and not assigned A`MaximalOrder then
      A`MaximalOrder:= O;
    end if;
  end if;

  return O`IsMaximal;
end intrinsic;

//-------------
//
// Bibliography
//
//-------------

/*

[Vigneras] 
Marie-France Vigneras, Arithmetique des algebres de quaternions, Lecture notes in mathematics, vol. 800, Springer, Berlin, 1980.

[Voight] 
John Voight, Quadratic forms and quaternion algebras: Algorithms and 
arithmetic, Ph.D. thesis, University of California, Berkeley, 2005.

*/