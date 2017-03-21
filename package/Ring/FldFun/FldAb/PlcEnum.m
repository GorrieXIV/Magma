freeze;
//

declare type PlcEnum;
declare attributes PlcEnum:
                K,
                Coprime,
                BCpolys,
                BCoffset,
                decom,
                all,  
                offset;
                    
intrinsic Print(r::PlcEnum, s::MonStgElt)
  {}
  // TODO: check s for "Maximal" or so....
  if r`Coprime cmpeq false then
    "Places of ", r`K;
  else
    "Places of ", r`K, " coprime to ", r`Coprime;
  end if;
end intrinsic;

intrinsic IsCoercible(x::PlcEnum, y::.) -> BoolElt, .
  {}
  return false, "Illegal coercion";
end intrinsic;
intrinsic 'in'(x::., y::PlcEnum) -> BoolElt
  {}
  return false;
end intrinsic;

intrinsic PlaceEnumInit(K::FldFunG : Coprime := false, All := false) -> PlcEnum
{Creates an environment to enumerate all places of K.}

  if All then // start with the infinite primes...
    pp := [];
  else  
    pp := PrimePolynomials(PolynomialRing(ConstantField(K)), 1);
  end if;

  if Coprime cmpne false then
    if Type(Coprime) ne SetEnum then
      Coprime := Set(Support(Coprime));
    end if;
  end if;

  r := New(PlcEnum);
  r`all := All;
  r`K := K;
  r`Coprime := Coprime;
  r`BCpolys := pp;
  r`BCoffset := 1;
  if All then
    pp := PrimePolynomials(PolynomialRing(ConstantField(K)), 1)[1];
    r`decom :=[x : x in Support(Divisor(K!pp)) | not IsFinite(x)];
    r`BCpolys := [Minimum(r`decom[1])];
  else
    r`decom :=[x : x in Support(Divisor(K!pp[1])) | IsFinite(x)];
  end if;
  r`offset := 0;

  return r;
end intrinsic;

intrinsic PlaceEnumInit(P::PlcFunElt : Coprime := false) -> PlcEnum
{Creates an environment to enumerate all places of K, starting at P.}

  d := Minimum(P);
  K := FunctionField(P);
  if IsFinite(P) then
    pp := PrimePolynomials(PolynomialRing(ConstantField(K)), Degree(d));
    All := false;
  else
    pp := [];
    All := true;
  end if;

  if Coprime cmpne false then
    if Type(Coprime) ne SetEnum then
      Coprime := Set(Support(Coprime));
    end if;
  end if;

  r := New(PlcEnum);
  r`K := K;
  r`all := All;
  r`Coprime := Coprime;
  r`BCpolys := pp;
  if All then
    r`BCoffset := 1;
    r`decom :=[x : x in Support(Divisor(K!d)) | not IsFinite(x)];
    r`BCpolys := [Minimum(r`decom[1])];
  else
    r`BCoffset := Position(pp, d);
    r`decom :=[x : x in Support(Divisor(K!d)) | IsFinite(x)];
  end if;
  r`offset := Position(r`decom, P);

  return r;
end intrinsic;

intrinsic PlaceEnumInit(K::FldFun, Pos::[RngIntElt] : Coprime := false) -> PlcEnum
{Creates an environment to enumerate all places of K, starting at Pos.}

  if Pos[1] lt 0 then
    All := true;
    pp := [];
  else
    pp := PrimePolynomials(PolynomialRing(ConstantField(K)), Pos[1]);
    All := false;
  end if;

  if Coprime cmpne false then
    if Type(Coprime) ne SetEnum then
      Coprime := Set(Support(Coprime));
    end if;
  end if;

  r := New(PlcEnum);
  r`K := K;
  r`all := All;
  r`Coprime := Coprime;
  r`BCpolys := pp;
  r`BCoffset := Pos[2];
  if All then
    d := PrimePolynomials(PolynomialRing(ConstantField(K)), 1)[1];
    r`decom :=[x : x in Support(Divisor(K!d)) | not IsFinite(x)];
    r`BCpolys := [Minimum(r`decom[1])];
  else
    r`decom :=[x : x in Support(Divisor(K!pp[Pos[2]])) | IsFinite(x)];
  end if;
  r`offset := Pos[3];

  return r;
end intrinsic;


intrinsic PlaceEnumCopy(R::PlcEnum) -> PlcEnum
{Creates an environment to enumerate all places of K.}

  r := New(PlcEnum);
  r`K := R`K;
  r`Coprime := R`Coprime;
  r`BCpolys := R`BCpolys;
  r`BCoffset := R`BCoffset;
  r`decom := R`decom;
  r`offset := R`offset;

  return r;
end intrinsic;

intrinsic PlaceEnumPosition(R::PlcEnum) -> []
  {Returns a "position" information.}
  if Type(R`BCpolys[1]) eq RngUPolElt then  
    return [Degree(R`BCpolys[1]), R`BCoffset, R`offset];
  else
    return [-1, R`BCoffset, R`offset];
  end if;
end intrinsic;

intrinsic PlaceEnumNext(R::PlcEnum) -> PlcFunElt
{Returns the "next" place.}
  r := R;
  repeat
    r`offset +:= 1;
    if r`offset gt #r`decom then
      r`BCoffset +:= 1;
      if r`BCoffset gt #r`BCpolys then
        r`BCoffset := 1;
        if Type(r`BCpolys[1]) eq RngUPolElt then
          r`BCpolys := PrimePolynomials(PolynomialRing(ConstantField(r`K)),
                                      Degree(r`BCpolys[1])+1);
        else
          r`BCpolys := PrimePolynomials(PolynomialRing(ConstantField(r`K)),1);
        end if;
      end if;
      // what I really want is all Places above the prime poly. Since I don't
      // know how to do this directly...
      s := Support(Divisor(r`K!r`BCpolys[r`BCoffset]));
      r`decom := [x : x in s | IsFinite(x)];
      r`offset := 1;
    end if;
  until r`Coprime cmpeq false or
        not r`decom[r`offset] in r`Coprime;

  return r`decom[r`offset];
end intrinsic;

intrinsic PlaceEnumCurrent(R::PlcEnum) -> PlcFunElt
{Returns the "current" place.}
  require R`offset ne 0 : "There is no current place yet";
  return R`decom[R`offset];
end intrinsic;

