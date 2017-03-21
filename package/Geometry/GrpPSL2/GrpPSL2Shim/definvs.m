freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Invariants for definite quaternion orders
// August 2008, John Voight
//
//////////////////////////////////////////////////////////////////////////////

import "shimura.m" : OddLocalEmbeddingNumber, EvenLocalEmbeddingNumber;
import "../../../Algebra/AlgAss/enum.m": MassInfinity;

declare attributes FldNum : TotallyPositiveUnits;
declare attributes FldRat : TotallyPositiveUnits;

TotallyPositiveUnits := function(Z_F, UF, mUF);
  // Stupid function, the isomorphism {1,-1} -> {0,1}.
  hiota := function(u);
    if u eq -1 then
      return 1;
    else
      return 0;
    end if;
  end function;

  F := NumberField(Z_F);
  UZd := AbelianGroup([2 : i in [1..Degree(F)]]);
  phi := hom<UF -> UZd |
               [[hiota(Sign(Evaluate(mUF(UF.i), v))) : v in RealPlaces(F)] :
                i in [1..#Generators(UF)]]>;
  UFmodsq, fsq := quo<UF | [2*u : u in Generators(UF)]>;
  return fsq(Kernel(phi)), fsq;
end function;

declare attributes FldNum: DefiniteCyclotomicClassNumbers;

intrinsic DefiniteClassNumber(D::RngOrdFracIdl, N::RngOrdFracIdl : Bound:=0) -> RngIntElt
  {Returns the class number of the Eichler order of level N in the
   quaternion algebra of discriminant D, for ideals N and D in a 
   totally real field.}

  Dprod := D;
  Nprod := N;

  Z_F := Order(Dprod);
  F := NumberField(Z_F);

  require IsAbsoluteField(F) : 
         "Currently implemented only for absolute extensions of Q";

  require IsTotallyReal(F) : "The field is not totally real";

  sig := [];
  mass:= MassInfinity(F);
  DF := Factorization(D);
  DN := Factorization(N);
  if #DF gt 0 then
    mass *:= &*[ Norm(p[1])-1 : p in DF];
  end if;
  if #DN gt 0 then
    mass *:= &*[ (Norm(p[1])^-1+1) * Norm(p[1])^p[2] : p in DN];
  end if;

  D := [pp[1] : pp in Factorization(Dprod)];
  N := Factorization(Nprod);

  // If F is the rationals, then there is an easy formula.
  if Type(F) eq FldRat then
    if N mod 4 eq 0 then
      e2 := 0;
    else
      e2 := &*[1-KroneckerSymbol(-4,p) : p in D];
      if N gt 1 then
        e2 *:= &*[1+KroneckerSymbol(-4,p) : p in PrimeDivisors(N)];
      end if;
    end if;
    if N mod 9 eq 0 then 
      e3 := 0;
    else       
      e3 := &*[1-KroneckerSymbol(-3,p) : p in D];
      if N gt 1 then
        e3 *:= &*[1+KroneckerSymbol(-3,p) : p in PrimeDivisors(N)];
      end if;
    end if;
    sig := [<2, e2>, <3, e3>];

  // Otherwise, we gotta work.
  else
    if Type(F) eq FldOrd then
      F := NumberField(F);
    end if;
    Z_F := MaximalOrder(F);

    sig := [];
   
    // Compute the unit group and class group.
    hF := ClassNumber(Z_F);
    UF, mUF := UnitGroup(Z_F);

    if not assigned F`DefiniteCyclotomicClassNumbers then

      S := LCM(CyclotomicQuadraticExtensions(F));
      // S = all prime powers m such that [F(zeta_m):F] = 2
      // Now get all possible m such that [F(zeta_m):F] = 2
      Sdiv := [m : m in Divisors(S) | m ne 1 and Valuation(m,2) ne 1]; // avoid repetition
      Sdiv := [m : m in Sdiv | 
                   forall{ f : f in Factorization(CyclotomicPolynomial(m), F) | Degree(f[1]) eq 2} ];
      Sdiv := [IsEven(m) select m else 2*m : m in Sdiv];
//"Values for q:", Sdiv;

      hKs := [];
      Rs := [];
      Z_Ks := [];

      for i := 1 to #Sdiv do
        s := Sdiv[i];
        fs := Factorization(CyclotomicPolynomial(s), F)[1][1];
        K := ext<F | fs>;
        Z_K := MaximalOrder(K);
        Z_Ks[i] := Z_K;

        Z_Kabs := AbsoluteOrder(Z_K);
        assert Z_Kabs`Maximal;
        Kabs := NumberField(Z_Kabs);

        // This is the hugely expensive step.
        vprintf Shimura : "Computing class number for %o ... ", s;
        vtime Shimura :
        if Bound cmpeq 0 then
          hK := ClassNumber(Z_Kabs);
        elif Bound cmpeq "BachBound" then
          hK := ClassNumber(Z_Kabs : Bound := Floor(BachBound(Kabs)/40));
        else
          hK := ClassNumber(Z_Kabs : Bound := Bound);
        end if;
        hKs[i] := hK;

        // Compute the order Oq = Z_F[zeta_2s] and its conductor.
        Oq := Order([K.1]);
        Dq := Discriminant(MinimalPolynomial(K.1));
        ff := SquareRoot(Z_F!!Discriminant(Oq)/Discriminant(Z_K));

        _ := IndependentUnits(Z_Kabs);
        SetOrderUnitsAreFundamental(Z_Kabs);
        UK, mUK := UnitGroup(Z_Kabs);
        // This is necessary so that the UnitGroup(s) below are done
        // with the same level of rigour as the ClassGroup above.
        // Without this, the UnitGroup would be done with full rigour,
        // But that is pointless: if hK was heuristic and incorrect,
        // then our answer will be wrong even if we get the units right.
        // (Oct 2010, SRD)

        wK := #TorsionSubgroup(UK);

        Rdata := [];

        // Loop over orders by their conductor dff.
        for jf := 1 to #Divisors(ff) do
          dff := Divisors(ff)[jf];

          // if Z_K is maximal, we have Cl(O_dff)/Cl(K) = 1.
          if dff eq ideal<Z_F | 1> then
            Oq := Z_Kabs; // not used
            UOq := UK;
            mUOq := map< UK -> UK | u :-> u, u :-> u >;
            wOq := wK;
            hOq := 1;
          // Otherwise, use the classic formula to compute the relative class number.
          else
            assert Z_K.1 eq 1;
            CI := CoefficientIdeals(Z_K);
            Oqbas := Basis(CI[1]) cat [z*Z_K.2 : z in Basis(dff*CI[2])];
            Oqbas := ChangeUniverse(Oqbas, Z_Kabs);
            Oq := sub< Z_Kabs | Oqbas >;
            assert Index(Z_Kabs, Oq) eq Norm(dff);
            
            UOq, mUOq := UnitGroupAsSubgroup(Oq, Z_Kabs:UG := <UK, mUK>);
            wOq := #TorsionSubgroup(UOq);
            hOq := 1/#quo<UK | [UK| mUOq(u) : u in Generators(UOq)]> * AbsoluteNorm(dff) *
                           &*[1-UnramifiedSquareSymbol(Dq,pp[1])/
                              AbsoluteNorm(pp[1]) : pp in Factorization(dff)];
          end if;

          // We only take orders where Oq has exact torsion unit group of order s.
          if wOq ne s*2/Gcd(2,s) then
            hQOq := 0;
          else
            hQOq := hOq;
          end if;

          QOq := #quo<UOq | [(Z_Kabs!mUF(u)) @@mUK @@mUOq : u in Generators(UF)] cat [UOq.1]>;

          Append(~Rdata, <dff, hQOq, QOq>);
        end for;
  
        Rs cat:= [Rdata];
      end for;

      UFplus, mUFplus := TotallyPositiveUnits(Z_F, UF, mUF);
      UFpluses := [mUF(u@@mUFplus) : u in UFplus | u ne UFplus!0];
      for u in UFpluses do
        K := ext<F | Polynomial([u,0,1])>;
        Z_K := MaximalOrder(K);
        Append(~Sdiv, 2);
        Append(~Z_Ks, Z_K);

        Z_Kabs := AbsoluteOrder(Z_K);
        assert Z_Kabs`Maximal;
        Kabs := NumberField(Z_Kabs);

        // This is the hugely expensive step.
        vprintf Shimura : "Computing class number for %o ... ", u;
        vtime Shimura :
        if Bound cmpeq 0 then
          hK := ClassNumber(Z_Kabs);
        elif Bound cmpeq "BachBound" then
          hK := ClassNumber(Z_Kabs : Bound := Floor(BachBound(Kabs)/40));
        else
          hK := ClassNumber(Z_Kabs : Bound := Bound);
        end if;
        Append(~hKs, hK);

        Oq := Order([K.1]);
        Dq := Discriminant(MinimalPolynomial(K.1));
        ff := SquareRoot(Z_F!!Discriminant(Oq)/Discriminant(Z_K));

        // See comment where this occurs above
        _ := IndependentUnits(Z_Kabs);
        SetOrderUnitsAreFundamental(Z_Kabs); 
        UK, mUK := UnitGroup(Z_Kabs);

        wK := #TorsionSubgroup(UK);

        Rdata := [];

        // Loop over orders by their conductor dff.
        for jf := 1 to #Divisors(ff) do
          dff := Divisors(ff)[jf];

          // if Z_K is maximal, we have Cl(O_dff)/Cl(K) = 1.
          if dff eq ideal<Z_F | 1> then
            Oq := Z_Kabs; // not used
            UOq := UK;
            mUOq := map< UK -> UK | u :-> u, u :-> u >;
            wOq := wK;
            hOq := 1;
          // Otherwise, use the classic formula to compute the relative class number.
          else
            assert Z_K.1 eq 1;
            CI := CoefficientIdeals(Z_K);
            Oqbas := Basis(CI[1]) cat [z*Z_K.2 : z in Basis(dff*CI[2])];
            Oqbas := ChangeUniverse(Oqbas, Z_Kabs);
            Oq := sub< Z_Kabs | Oqbas >;
            assert Index(Z_Kabs, Oq) eq Norm(dff);

            UOq, mUOq := UnitGroupAsSubgroup(Oq, Z_Kabs:UG := <UK, mUK>);
            wOq := #TorsionSubgroup(UOq);
            hOq := 1/#quo<UK | [UK| mUOq(u) : u in Generators(UOq)]> * AbsoluteNorm(dff) *
                           &*[1-UnramifiedSquareSymbol(Dq,pp[1])/
                              AbsoluteNorm(pp[1]) : pp in Factorization(dff)];
          end if;

          // We only take orders where Oq has exact torsion unit group of order 2.
          if wOq ne 2 then
            hQOq := 0;
          else
            hQOq := hOq;
          end if;

          QOq := #quo<UOq | [(Z_Kabs!mUF(u)) @@mUK @@mUOq : u in Generators(UF)] cat [UOq.1]>;

          Append(~Rdata, <dff, hQOq, QOq>);
        end for;  
 
        Rs cat:= [Rdata];
      end for;

      tup := <Sdiv, Z_Ks, hKs, Rs>;
      F`DefiniteCyclotomicClassNumbers := tup;
    end if;
    Fshim := F`DefiniteCyclotomicClassNumbers;

    // Iterate over each possible elliptic cycle order length s.
    for i := 1 to #Fshim[1] do
      s := Fshim[1][i];
      es := [Rationals()|];

      Z_K := Fshim[2][i];

      for R in Fshim[4][i] do
        if R[1] + Dprod ne ideal<Z_F | 1> then
          Append(~es, 0);
          continue;
        end if;

        dff := R[1];
        es0 := R[2];

        // The local embedding numbers are easy for primes dividing the discriminant of B.
        if #D gt 0 then
          for p in D do
            pKfact := Factorization(Z_K!!p);
            if #pKfact eq 2 then 
              es0 *:= 0;
            elif pKfact[1][2] eq 1 then
              es0 *:= 2;
            end if;
          end for;
        end if;

        // Embedding numbers for primes dividing N are complicated!
        if #N gt 0 then
          for qq in N do
            dffzk := dff*PseudoBasis(Module(Z_K))[2][1];
            e := Valuation(dffzk,qq[1]);
            if dffzk eq qq[1]^e then
              dffzkpF := [];
            else
              dffzkpF := Factorization(dffzk/qq[1]^e);
            end if;
            u := WeakApproximation([pp[1] : pp in dffzkpF] cat [qq[1]],
                                   [pp[2] : pp in dffzkpF] cat [0]);
            pi := SafeUniformiser(qq[1]);
            alpha := u*Z_K.2*pi^e;
            f := Eltseq(MinimalPolynomial(alpha));

            if Norm(qq[1]) mod 2 eq 0 then
              es0 *:= EvenLocalEmbeddingNumber(-f[2],f[1], qq[2], qq[1]);
            else
              es0 *:= OddLocalEmbeddingNumber(f[2]^2-4*f[1], qq[2], Valuation(dff,qq[1]), qq[1]);
            end if;
          end for;
        end if;
        es0 *:= 1-1/((s div 2)*R[3]);
        Append(~es, es0);
/*
"R";
R;
"s =", s;
1-1/((s div 2)*R[3]);
es0;
*/
      end for;

      hK := Fshim[3][i];
      e := hK*&+es;
      if e gt 0 then
        Append(~sig, <s div 2, e>);
      end if;
/*
es;
s;
<s div 2, e>;
*/
    end for;
  end if;

  if #sig eq 0 then
    h := mass;
  else
    h := mass + 1/2*&+[q[2] : q in sig];
  end if;
  bool, h := IsCoercible(Integers(), h);
  error if not bool, "Class number not an integer!", mass, sig;
  return h;
end intrinsic;

