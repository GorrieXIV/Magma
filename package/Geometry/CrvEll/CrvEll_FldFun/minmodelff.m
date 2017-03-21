freeze;

/************************************************************************
minmodelff.m

Date: 12/02/2006
Some function related to reduction types and models of elliptic curves
over function fields. 

Date: 09/07/2006
Excluded the place at infinity in BadPlaces if there is good reduction there 
and added a new intrinsic IsConstantCurve.

Date: 15/08/2006 (TD) 
Call TateAlgorithm from ../minmodel.m instead of reimplementing it
(in intrinsic LocalInformation(E::CrvEll[FldFun], P::PlcFunElt))
Removed ScaleCurve and rst_transform

Interface presently:

intrinsic LocalInformation(E::CrvEll, P::PlcFunElt) -> Tup, CrvEll

  Returns:

    <P, vpd, fp, c_p, K, split>, Emin

  where 
    P = the place
    vpd = valuation of local minimal discriminant
    fp = valuation of conductor
    K = Kodaira Symbol
    cp = Tamagawa number
    split is a boolean that is false if reduction is nonsplit-multiplicative,
       and true otherwise
    Emin is a model (integral and) minimal at P



intrinsic LocalInformation(E::CrvEll) -> SeqEnum

  Returns local reduction data at all bad places.

intrinsic Conductor(E::CrvEll) -> DivFunElt

  Conductor of an elliptic curve E over a function field

intrinsic MinimalModel(E::CrvEll) -> CrvEll, MapIsoSch

  Model of E that is minimal at all finite places. Only implemented for
    function fields of genus 0.

intrinsic LocalMinimalModel(E::CrvEll, P::RngOrdIdl) -> CrvEll, RngIntElt

  local minimal model of an elliptic curve E at prime ideal P;
  this is a faster algorithm than the one used in LocalInformation for
  primes of residue characteristic bigger than 3. For residue characteristics
  2 and 3, this routine simply returns data computed by LocalInformation


***********************************************************************/

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                TATE'S ALGORITHM OVER FUCTION FIELDS                //
//                           Jasper Scholten                          //
//                                                                    //
//             (Adaptation of the number field code of                //
//                             John Cremona)                          //
//                                                                    //
////////////////////////////////////////////////////////////////////////


import "../minmodel.m": rst_transform,TateAlgorithm;


intrinsic LocalInformation(E::CrvEll[FldFun], P::PlcFunElt) -> Tup,CrvEll
  {Tate's algorithm to determine reduction type}

  // Check cache
  if assigned E`LocalInformation and IsDefined(E`LocalInformation,P) 
     and assigned E`MinimalModels and IsDefined(E`MinimalModels,P)
  then
     return E`LocalInformation[P], E`MinimalModels[P];
  end if;

  _,red:=ResidueClassField(Ideal(P));
  val:=func<x|Valuation(x,P)>;
  pi:=UniformizingElement(P);
  info, Emin := TateAlgorithm(E,P,red,val,pi: IsPowerF:=IsPower);

  // Cache results
  if not assigned E`LocalInformation then
     E`LocalInformation := AssociativeArray(Parent(P));
  end if;
  if not assigned E`MinimalModels then
     E`MinimalModels := AssociativeArray(Parent(P));
  end if;
  E`LocalInformation[P] := info;
  E`MinimalModels[P] := Emin;

  return info, Emin;
end intrinsic;


// TO DO: FldFunRat signatures are inefficient

intrinsic LocalInformation(E::CrvEll[FldFunRat], P::PlcFunElt) -> Tup,CrvEll
{Tate's algorithm to determine reduction type of an elliptic curve
defined over a rational function field F(t), at the place specified by P,
which may be specified as a place or as a prime element. 
For the infinite place use 1/t.}

  K:=FunctionField(P);
  E1:=ChangeRing(E,K);
  return LocalInformation(E1,P);
end intrinsic;


intrinsic LocalInformation(E::CrvEll[FldFunRat], P::RngUPolElt) -> Tup,CrvEll
{"} // "

  return LocalInformation(E, BaseRing(E) ! P);
end intrinsic;


intrinsic LocalInformation(E::CrvEll[FldFunRat], P::FldFunRatUElt) -> Tup,CrvEll
{"} // "

  K:=BaseRing(E); t := K.1;
  require Parent(P) eq K :
    "Elliptic Curve and place are not over the same field";
  R:=PolynomialRing(K); x := R.1;
  L:=ext<K | x-t>; s := L.1;   // make field of type FldFun
  num:=Numerator(P);
  den:=Denominator(P);
  if Degree(num) eq 0 then
    error if Degree(den) ne 1, "2nd argument does not correspond to a place";
    Q:=Poles(s)[1];
  else
    error if Degree(den) ne 0, "2nd argument does not correspond to a place";
    // if not IsIrreducible(num) then print Factorisation(Numerator(P)); end if;
    error if not IsIrreducible(num), "2nd argument does not correspond to a place";
    Q:=Zeroes(Evaluate(num,s))[1];
  end if;
  
  E2:=ChangeRing(E,L);

  tup,E3:=LocalInformation(E2,Q);

  E4:=ChangeRing(E3,K);
  return tup,E4;
end intrinsic;


intrinsic MinimalModel(E::CrvEll[FldFunG], P::PlcFunElt) -> CrvEll
{A local minimal model of the elliptic curve E at the place P}

  _, Emin := LocalInformation(E, P);
  return Emin;
end intrinsic;

intrinsic MinimalModel(E::CrvEll[FldFunRat], P::RngUPolElt) -> CrvEll
{"} // "

  _, Emin := LocalInformation(E, P);
  return Emin;
end intrinsic;

intrinsic MinimalModel(E::CrvEll[FldFunRat], P::FldFunRatUElt) -> CrvEll
{"} // "

  _, Emin := LocalInformation(E, P);
  return Emin;
end intrinsic;


intrinsic NumberOfComponents(K::SymKod) -> RngIntElt
  { Number of components of Kodaira symbol}
  s := Sprint(K);
  case s:
  when "I0":
    return 1;
  when "II":
    return 1;
  when "III":
    return 2;
  when "IV":
    return 3;
  when "II*":
    return 9;
  when "III*":
    return 8;
  when "IV*":
    return 7;
  end case;
  // Final case: K = In or In* with n > 0
  l := #s;
  if s[l] eq "*" then
    n := eval s[2 .. l-1]; 
    return n+5;
  else
    n := eval s[2 .. l]; 
    return n;
  end if;
end intrinsic;


intrinsic KodairaSymbols(E::CrvEll[FldFunG]) -> SeqEnum
{A sequence of tuples < KS, n >, giving the Kodaira symbol and degree of each place of bad reduction 
for the elliptic curve E.}

  K:=BaseRing(E);
  // disallow multivariate rational function fields
  if ISA(Type(K), FldFunRat) then
    require ISA(Type(Integers(K)), RngUPol) : 
           "Not implemented for curves over multivariate function fields";
  end if;

  lijst:=[];
  if Type(K) eq FldFunRat then
    factoren:=&join[{K!b[1]} : b in Factorisation(Denominator(a)), a in aInvariants(E)];
    factoren join:=&join[{K!b[1]} : b in Factorisation(Numerator(Discriminant(E)))];
    factoren join:={1/K.1};
  else
    factoren:=&join[SequenceToSet(Poles(a)): a in aInvariants(E)| not IsZero(a)];
    factoren join:=SequenceToSet(Zeroes(Discriminant(E)));;
  end if;
  for f in factoren do
    locinfo:=LocalInformation(E,f);
    if locinfo[3] ne 0 then 
      Append(~lijst,<locinfo[5],Degree(locinfo[1])>);
    end if;
  end for;
  return lijst;
end intrinsic;



intrinsic Conductor(E::CrvEll[FldFun]) -> DivFunElt
{The conductor of the elliptic curve E (defined over a function field)}

  K:=BaseRing(E);

  // TO DO
  // if Characteristic(K) gt 3 then

  Div:=DivisorGroup(K);
  D:=Div!0;
  factoren:=&join[SequenceToSet(Poles(a)): a in aInvariants(E)| not IsZero(a)];
  factoren join:=SequenceToSet(Zeroes(Discriminant(E)));;
  for f in factoren do
    locinfo:=LocalInformation(E,f);
    D+:=locinfo[3]*locinfo[1];
  end for;
  return D;
end intrinsic;


// Changed return type
// Oct 2012, SRD
intrinsic Conductor(E::CrvEll[FldFunRat]) -> SeqEnum
{"} // "

  K := BaseRing(E);
  R := Integers(K);

  if Characteristic(K) le 3 then

    L := ext<K | Polynomial([K| -1, 1]) >;
    PL, E := Support(Conductor(ChangeRing(E,L)));

    N := [ < K!Minimum(PL[i]), E[i] > : i in [1..#PL] ];

  else

    // Avoid Tate's algorithm

    EE := IntegralModel(E);
    C  := cInvariants(EE);
    c4 := R! C[1];
    c6 := R! C[2];
    D  := R! Discriminant(EE);
    j  := jInvariant(EE);

    N := [];

    // infinite place
    level := Min([-Degree(c4) div 4, -Degree(c6) div 6]);
    vD := -Degree(D) - 12*level;
assert vD ge 0;
    if vD ne 0 then
      vj := Degree(Denominator(j)) - Degree(Numerator(j));
      if vj ge 0 then
        Append(~N, <1/K.1,2>);
      elif vj eq -vD then
        Append(~N, <1/K.1,1>);
      else
        assert vD eq 6 - vj;
        Append(~N, <1/K.1,2>);
      end if;
    end if;

    // finite places
    for p in [R| t[1] : t in Factorization(D)] do
      level := Min(Valuation(c4,p) div 4, Valuation(c6,p) div 6);
      vD := Valuation(D,p) - 12*level; // valuation of minimal discriminant
assert vD ge 0;
      if vD ne 0 then
        vj := Valuation(j,p);
        if vj ge 0 then
          Append(~N, <K!p,2>);
        elif vj eq -vD then
          Append(~N, <K!p,1>);
        else
          assert vD eq 6 - vj;
          Append(~N, <K!p,2>);
        end if;
      end if;
    end for;

    /*
    L := ext<K | Polynomial([K| -1, 1]) >;
    PL, E := Support(Conductor(ChangeRing(E,L)));

    assert Seqset(N) eq { < K!Minimum(PL[i]), E[i] > : i in [1..#PL] };
    */

  end if;

  return N;
end intrinsic;


intrinsic LocalInformation(E::CrvEll[FldFunG]) -> SeqEnum
  { Sequence of tuples of local information at all places of bad reduction }

  K:=BaseRing(E);

  // disallow multivariate rational function fields
  if ISA(Type(K), FldFunRat) then
    require ISA(Type(Integers(K)), RngUPol) : 
           "Not implemented for curves over multivariate function fields";
  end if;

  lijst:=[];
/*
  if Type(K) eq FldFunRat then
    factoren:=&join[{K!b[1]} : b in Factorisation(Denominator(a)), a in aInvariants(E)];
    factoren join:=&join[{K!b[1]} : b in Factorisation(Numerator(Discriminant(E)))];
    factoren join:={1/K.1};
  else
    factoren:=&join[SequenceToSet(Poles(a)): a in aInvariants(E)| not IsZero(a)];
    factoren join:=SequenceToSet(Zeroes(Discriminant(E)));;
  end if;
*/
  factoren:=BadPlaces(E);
  for f in factoren do
    locinfo:=LocalInformation(E,f);
    if locinfo[3] ne 0 then 
      Append(~lijst,locinfo);
    end if;
  end for;
  return lijst;
end intrinsic;


intrinsic BadPlaces(E::CrvEll[FldFunG]) -> SeqEnum
{The places of bad reduction for E.}
  if assigned E`BadPlaces then 
    return E`BadPlaces;
  end if;

  K:=BaseRing(E);
  lijst:=[];
  if Type(K) eq FldFunRat then
    factoren:=&join[{K!b[1]} : b in Factorisation(Denominator(a)), a in aInvariants(E)];
    D:=Discriminant(E);
    factoren join:=&join[{K!b[1]} : b in Factorisation(Numerator(D))];
    for a in (aInvariants(E) cat [1/D]) do
      if Degree(Numerator(a)) gt Degree(Denominator(a)) then     
        factoren join:={1/K.1}; 
        break a;
      end if;
    end for;
    if IsEmpty(factoren) then 
      factoren:={K|};
    end if;
  else
    factoren:=&join[SequenceToSet(Poles(a)): a in aInvariants(E)| not IsZero(a)];
    factoren join:=SequenceToSet(Zeroes(Discriminant(E)));
    if IsEmpty(factoren) then
      factoren:={Places(K)|};
    end if;
  end if;

/*
  for f in factoren do
    locinfo:=LocalInformation(E,f);
    if locinfo[3] ne 0 then 
      Append(~lijst,locinfo[1]);
    end if;
  end for;
*/
  E`BadPlaces:= SetToSequence(factoren);
  return E`BadPlaces;
end intrinsic;

intrinsic MinimalModel(E::CrvEll[FldFunG]) -> CrvEll, MapIsoSch
  { Returns a model of an elliptic curve E that is minimal at all finite places
    together with the map E:->M.  E must be defined over a function field of genus 0 }

  K := BaseRing(E);

  // disallow multivariate rational function fields
  if ISA(Type(K), FldFunRat) then
    require ISA(Type(Integers(K)), RngUPol) : 
           "Not implemented for curves over multivariate function fields";
  end if;
  require Genus(K) eq 0: "Only implemented for genus 0!";

  if Type(K) eq FldFunRat then
    factoren:=&join[{K!b[1]} : b in Factorisation(Denominator(a)), a in aInvariants(E)];
    factoren join:=&join[{K!b[1]} : b in Factorisation(Numerator(Discriminant(E)))];
  else
    factoren:=&join[SequenceToSet(Poles(a)): a in aInvariants(E)| not IsZero(a)];
    factoren join:=SequenceToSet(Zeroes(Discriminant(E)));
    factoren diff:=SequenceToSet(InfinitePlaces(K));
  end if;

  Emin:=E;
  for P in factoren do
    _,Emin:=LocalInformation(Emin,P);
  end for;

  return Emin, Isomorphism(E, Emin);
end intrinsic;


intrinsic MinimalDegreeModel(E::CrvEll[FldFunRat]) -> CrvEll, Map, Map
  {Model with the Weierstrass a_i coefficients polynomials such that the
      quantity Max([Degree(a_i)/i]) is minimal.}
// Also returns the Ceiling of
//    this maximum.
  K:=BaseRing(E);
  F:=CoefficientRing(K);
  a1,a2,a3,a4,a6:=Explode(aInvariants(SimplifiedModel(E)));
  case Characteristic(F):
    when 2:
      E1:=MinimalModel(SimplifiedModel(E));
      a6:=aInvariants(E1)[5];
      a6_8:=Coefficient(Numerator(a6),8);
      a2:=aInvariants(E1)[2];
      a2_4:=Coefficient(Numerator(a2),4);
      E2:=rst_transform(E1,[0,Sqrt(a2_4)*(K.1)^2,Sqrt(a6_8)*(K.1)^4]);
      return E2;
    when 3:
      return MinimalModel(SimplifiedModel(E));
    else
      Na6:=Numerator(a6);
      A:=Factorisation(GCD(Numerator(a4),Na6));
      for f in A do
        k:=Floor(f[2]/4);
        while not IsZero(Na6 mod f[1]^(6*k)) do
          k-:=1;
        end while;
        a4/:=f[1]^(4*k);
        a6/:=f[1]^(6*k);
      end for;
      A:=Factorisation(Denominator(a4));
      for f in A do
        a4*:=f[1]^(4*Ceiling(f[2]/4));
        a6*:=f[1]^(6*Ceiling(f[2]/4));
      end for;
      A:=Factorisation(Denominator(a6));
      for f in A do
        a4*:=f[1]^(4*Ceiling(f[2]/6));
        a6*:=f[1]^(6*Ceiling(f[2]/6));
      end for;
  end case;
  Em:=EllipticCurve([a1,a2,a3,a4,a6]);
  _,a:=IsIsomorphic(E,Em);
  return Em,a;
end intrinsic;

intrinsic IsConstantCurve(E::CrvEll[FldFunRat]) -> BoolElt,CrvEll
  {Determines if E is a constant curve, and returns a model defined 
    over the field of constants if this is the case}
  j:=jInvariant(E);
  if not IsConstant(j) then 
    return false,_;
  elif not IsZero(#LocalInformation(E)) then
    return false,_;
  end if;
  K:=BaseRing(E);
  F:=ConstantField(K);
  E:=MinimalModel(E);
  _,E:=LocalInformation(E,1/K.1);
  return true,ChangeRing(E,F);
end intrinsic;
