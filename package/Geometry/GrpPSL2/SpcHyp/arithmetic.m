freeze;

////////////////////////////////////////////////////////////////
//                                                            //
//                     Arithmetic                             //
//                                                            //
//                                                            //
////////////////////////////////////////////////////////////////



intrinsic '*' (a::RngElt,x::SpcHypElt) -> SpcHypElt
   {}
   // Multiplication of elements of the upper half plane by
   // some rational.
   // Warning, the following does not really result in something
   // in the upper half plane, but is useful for applying the
   // action of some congruence subgroup (GrpPSL2).
   require Type(a) in {FldRatElt,RngIntElt}:
       "Argument 1 must be an integer, rational";
   if a eq 0 then
      z := New(SpcHypElt);   
      z`is_exact     := true;
      z`is_cusp      := true;
      z`complex_value   := 0;
      z`exact_value := Cusps()!0;
      z`parent:=x`parent;
      return z;
   end if;
   z := New(SpcHypElt);   
   z`is_exact     := x`is_exact;
   z`is_cusp      := x`is_cusp;     
   z`complex_value   := a*x`complex_value;     
   if x`is_cusp then
      u,v:=Explode(Eltseq(x`exact_value));
      a1 := Rationals()!a;
      b := Numerator(a1);
      c := Denominator(a1);
      z`exact_value := Cusps()![b*u,c*v];
   elif z`is_exact then
       z`exact_value := a*x`exact_value;
    end if;
    z`parent:=x`parent;
   return z;
end intrinsic;

intrinsic '*' (x::SpcHypElt,a::RngElt) -> SpcHypElt
   {}
   // Multiplication of elements of the upper half plane by
   // some rational.
   return a*x;
end intrinsic;


intrinsic '*' (a::RngElt,x::[SpcHypElt]) -> SeqEnum
    {}
    require Type(a) in {FldRatElt,RngIntElt}:
    "Argument 1 must be an integer, rational";
    return [a*v : v in x];
end intrinsic;


intrinsic '*' (a::RngIntElt,x::SetCspElt) -> SetCspElt
    {}
    u,v:=Explode(Eltseq(x));
    if v eq 0 then return Cusps()![1,0];
    else
	return Cusps()!(a*u/v);
    end if;
 end intrinsic;

 intrinsic '*' (a::FldRatElt,x::SetCspElt) -> SetCspElt
    {}
    u,v:=Explode(Eltseq(x));
    if v eq 0 then return Cusps()![1,0];
    else
	return Cusps()!(a*u/v);
    end if;
end intrinsic;


intrinsic '*' (a::RngIntElt,x::[SetCspElt]) -> SeqEnum
    {}
    return [a*v : v in x];
end intrinsic;


intrinsic '*' (a::FldRatElt,x::[SetCspElt]) -> SeqEnum
    {}
    return [a*v : v in x];
end intrinsic;


intrinsic '+' (x::SpcHypElt,b::RngIntElt) -> SpcHypElt
   {}
// Warning, this is defined for use for giving
// action of some congruence subgroup (GrpPSL2).
   z := New(SpcHypElt);
   z`is_exact     := x`is_exact;
   z`is_cusp      := x`is_cusp;     
   z`complex_value := b + x`complex_value;     
   if x`is_cusp then
       u,v := Explode(Eltseq(x`exact_value));
       z`exact_value := Cusps()![u + b*v,v];
   elif z`is_exact then
       z`exact_value := b + x`exact_value;
   end if;
   z`parent      := x`parent;     
   return z;
end intrinsic;


intrinsic '+' (x::SpcHypElt,b::FldRatElt) -> SpcHypElt
   {}
// Warning, this is defined for use for giving
// action of some congruence subgroup (GrpPSL2).
   z := New(SpcHypElt);
   z`is_exact     := x`is_exact;
   z`is_cusp      := x`is_cusp;     
   z`complex_value := b + x`complex_value;     
   if x`is_cusp then
       u,v := Explode(Eltseq(x`exact_value));
       a := Numerator(b);
       c := Denominator(b);
       z`exact_value := Cusps()![u*c+a*v,v*c];
   elif z`is_exact then
       z`exact_value := b + x`exact_value;
   end if;
   z`parent      := x`parent;     
   return z;
end intrinsic;


intrinsic '-' (x::SpcHypElt,b::RngIntElt) -> SpcHypElt
   {}
// Warning, this is defined for use for giving
// action of some congruence subgroup (GrpPSL2).
   return x + (-b);
end intrinsic;


intrinsic '-' (x::SpcHypElt,b::FldRatElt) -> SpcHypElt
   {}
// Warning, this is defined for use for giving
// action of some congruence subgroup (GrpPSL2).
   return x + (-b);
end intrinsic;


intrinsic '/' (x::SpcHypElt,y::RngIntElt) -> SpcHypElt
    {division of a point in the upper half plane by
    a positive integer}
    require y gt 0:
    "Dividing by negative integers is not allowed";
    H := UpperHalfPlaneWithCusps();
    return  (1/y)*x;
end intrinsic;
