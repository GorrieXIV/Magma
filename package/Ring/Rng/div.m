freeze;

intrinsic IsRootOfUnity( a::RngElt ) -> BoolElt, RngIntElt
{Is a a root of unity?  If so, return the order}

  if a eq 1 then
    return true, 1;
  elif a eq -1 then
    return true, 2;
  end if;
  if not IsUnit(a) then
    return false;
  end if;

  R := Parent(a);
  if Type(R) in {FldCyc, RngCyc} then
    if Type(R) eq RngCyc then  // otherwise we won't have the sparse
                               // representation!
      K := FieldOfFractions(R);
      a := K!a;
      R := K;
    end if;
    s := Eltseq(a:Sparse);

    c := Conductor(R);
    d := CyclotomicOrder(R);

    if #s eq 1 then
      if #s[1][2] eq 1 then // dense case
        dd := d div Gcd(d, s[1][2][1]);
        if s[1][1] eq 1 then
          return true, dd;
        elif s[1][1] eq -1 then
          if IsOdd(dd) then
            return true, 2*dd;
          else
            return true, dd;
          end if;
        else
          return false, _;
        end if;
      else // sparse case!
        n := Factorisation(d);
        dd := Lcm([ m div Gcd(m, s[1][2][i]) 
                     where m := EulerPhi([<n[i][1],n[1][2]>]) : i in [1..#n]]);
        if s[1][1] eq 1 then
          return true, dd;
        elif s[1][1] eq -1 then
          if IsOdd(dd) then
            return true, 2*dd;
          else
            return true, dd;
          end if;
        else
          return false;
        end if;
      end if;
    else // not an obvious root of unity
      // I'm lazy for now.
      phi := MinimalPolynomial(a);
    end if;
  elif Type(R) in {FldNum, FldOrd, RngOrd, RngQuad} then
    if not IsField(R) then
      R := FieldOfFractions(R);
    end if;
    if BaseField(R) eq Rationals() and Signature(R) ne 0 then
      return false, _; // remember: the trivial cases (1, -1) are handled
                       // above!
    else 
      phi := AbsoluteMinimalPolynomial(a);
    end if;
  elif Type(R) in {FldFun, RngFunOrd, FldFunG, RngFunOrdG} then
    if not IsField(R) then
      R := FieldOfFractions(R);
    end if;
    if Characteristic(R) eq 0 then
      require false:
        "function field must be in positive characteristic";
    end if;
    if not IsConstant(a) then
      return false, _;
    else
      F, mF := ExactConstantField(R);
      a := a@@mF;
      return true, Order(a);
    end if;
  elif Type(R) eq FldFin then
    return true, Order(a);
  elif Type(R) in {RngInt, FldRat} then
    if a eq 1 then 
      return true, 1;
    elif a eq -1 then
      return true, 2;
    else
      return false, _;
    end if;
  elif Type(R) eq RngIntRes then
    // It has already been checked that a is a unit, so the order
    // is well-defined.
    return true, Order(a);
  elif Type(R) in {FldPad,RngPad} then
    if Valuation(a) ne 0 then return false,_; end if;
    p:=Prime(R); e:=Precision(R);
    _,m:=MultiplicativeGroup(R); return true,Order(a@@m);
  elif Type(R) eq RngPadRes then
    return true,Order(Integers(Modulus(R))!Integers()!a);
  elif Type(R) eq RngPadResExt then _,m:=MultiplicativeGroup(R);
    return true,Order(a@@m);
  else
    require false:
      "Sorry can't handle this ring";
  end if;  

  for n in EulerPhiInverse( Degree( phi ) ) do 
    if (a^n-1) eq 0 then 
      return true,n; 
    end if;
  end for;
  return false, _;
end intrinsic;

