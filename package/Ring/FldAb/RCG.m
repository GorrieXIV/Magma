freeze;


/* The divisors interface to RayClassGroups and related stuff...
 */

 
intrinsic Ideal(D::DivNumElt) -> RngOrdIdl
  {The (fractional) ideal representing the finite part of D}
  
  a,b := Support(D);
  I := 1*MaximalOrder(NumberField(D));
  for i in [1..#a] do
    if IsFinite(a[i]) then
      I*:= Ideal(a[i])^b[i];
    end if;
  end for;

  return I;
end intrinsic;

function split_D(D, name)
  if Type(D) eq PlcNumElt then
    f, n := IsInfinite(D);
    if f then
      return 1*MaximalOrder(NumberField(D)), [n];
    else 
      return Ideal(D), [];
    end if;
  end if;
  m := Ideal(D);
  a,b := Support(D);
  m0 := [];
  for i in [1..#a] do
    f, n := IsInfinite(a[i]);
    if f then
      if IsReal(a[i]) then
        Append(~m0, n);
      else
        error name * ": the divisor should not contain infinite places";
      end if;
    end if;
  end for;

  return m, m0;
end function;

intrinsic RayClassGroup(D::PlcNumElt[FldNum[FldRat]]) -> GrpAb, Map
  {The ray class group modulo D}
 
  m, m0 := split_D(D, "RayClassGroup");  
  if #m0 eq 0 then
    return RayClassGroup(m);
  else
    return RayClassGroup(m, m0);
  end if;
end intrinsic;

intrinsic RayClassGroup(D::DivNumElt[FldNum[FldRat]]) -> GrpAb, Map
  {The ray class group modulo D}
 
  m, m0 := split_D(D, "RayClassGroup");  
  if #m0 eq 0 then
    return RayClassGroup(m);
  else
    return RayClassGroup(m, m0);
  end if;
end intrinsic;

intrinsic RayResidueRing (D::PlcNumElt[FldNum[FldRat]]) -> GrpAb, Map
  {The residue ring mod^* D}
    
  m, m0 := split_D(D, "RayResidueRing");  
  if #m0 eq 0 then
    return RayResidueRing(m);
  else
    return RayResidueRing(m, m0);
  end if;
end intrinsic;

intrinsic RayResidueRing (D::DivNumElt[FldNum[FldRat]]) -> GrpAb, Map
  {The residue ring mod^* D}
    
  m, m0 := split_D(D, "RayResidueRing");  
  if #m0 eq 0 then
    return RayResidueRing(m);
  else
    return RayResidueRing(m, m0);
  end if;
end intrinsic;

intrinsic RayClassField(D::DivNumElt[FldNum[FldRat]]) -> FldAb
  {The ray class field modulo D}

  m, m0 := split_D(D, "RayClassField");
  if #m0 eq 0 then
    return RayClassField(m);
  else
    return RayClassField(m, m0);
  end if;
end intrinsic;

intrinsic RayClassField(D::PlcNumElt[FldNum[FldRat]]) -> FldAb
  {The ray class field modulo D}

  m, m0 := split_D(D, "RayClassField");
  if #m0 eq 0 then
    return RayClassField(m);
  else
    return RayClassField(m, m0);
  end if;
end intrinsic;


