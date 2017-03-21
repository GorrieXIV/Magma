/*
AKS 29/4/96.
CF added Z
*/

freeze;

Inf := Infinity();

intrinsic Completion(K::FldRat, p::RngIntElt : Precision := Inf) -> FldPad, Map
{The completion of the rationals at prime p}

    require IsPrime(p): "Ideal is not prime";

  if Category(Precision) eq Category(Inf) then
      S := pAdicField(p);
    else
      S := pAdicField(p, Precision);
    end if;
    return S, Coercion(K, S);
end intrinsic;

intrinsic Completion(K::FldRat, P::RngInt : Precision := Inf) -> FldPad, Map
{The completion of the rationals at prime ideal P}

    g := Generator(P);
    require IsPrime(g): "Ideal is not prime";

  if Category(Precision) eq Category(Inf) then
      S := pAdicField(Generator(P));
    else
      S := pAdicField(Generator(P), Precision);
    end if;
    return S, Coercion(K, S);
end intrinsic;

// Steve did these two.
// The previous Completion(K::FldFunRat, P::RngUPol) was nonsense.

intrinsic Completion(K::FldFunRat, p::RngElt : Precision:=0) -> RngSerPow, Map
{The completion of K at prime element p}

    KK := ext<K| Polynomial([K|-1,1])>;
    OKK := MaximalOrderFinite(KK);
    P := ideal<OKK| OKK!p>;
    require IsPrime(P) : "The element p does not generate a prime ideal";
    if Precision cmpeq 0 then
       KK_P, KKmap := Completion(KK, Place(P));
    else 
       KK_P, KKmap := Completion(KK, Place(P) : Precision:=Precision);
    end if;
    Kmap := map< K -> KK_P | k:->KKmap(KK!k), kk:->K!(kk@@KKmap) >;
    return KK_P, Kmap;
end intrinsic;

intrinsic Completion(K::FldFunRat, P::RngUPol : Precision:=0) -> RngSerPow, Map
{The completion of K at prime ideal P}

    R := IntegerRing(K);
    require IsCompatible(R, P): "Arguments are not compatible";
    C := CoefficientRing(R);
    require IsField(C): "Coefficient ring is not a field";
    require IsPrime(P) : "The ideal P is not prime";
    
    return Completion(K, Generator(P) : Precision:=Precision);
end intrinsic;

// neccesary for comp<Z | ...> :
intrinsic IntegerRing(Z::RngInt) -> RngInt
{Returns Z}
  require Z eq Integers(): "Ring must be Z";
  return Z;
end intrinsic;

intrinsic Completion(Z::RngInt, P::RngInt : Precision := Inf) -> RngPad, Map
{Returns the completion of Z at P}
  require Z eq Integers(): "Ring must be Z";
  require IsPrime(P): "Ideal must be a prime ideal";
  if Category(Precision) eq Category(Inf) then
    R := pAdicRing(Generator(P));
  else
    R := pAdicRing(Generator(P), Precision);
  end if;
  return R, Coercion(Z, R);
end intrinsic;

