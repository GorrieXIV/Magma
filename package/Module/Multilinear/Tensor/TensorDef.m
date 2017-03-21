freeze;

/*
  This file contains all the low-level definitions for tensors (TenSpcElt).
*/


import "Tensor.m" : __GetTensor;

// ------------------------------------------------------------------------------
//                                      Print
// ------------------------------------------------------------------------------
intrinsic Print( t::TenSpcElt )
{Print t}
  D := t`Domain;
  if t`Cat`Contra then
    s := Sprintf( "Cotensor of valence %o, ", Valence(t) );
    i := t`Valence;
    while i gt 1 do
      s cat:= Sprintf( "U%o x ", i);
      i -:= 1;
    end while;
    s cat:= Sprintf( "U1 >-> K" );
    i := t`Valence;
    for X in D do
      s cat:= Sprintf( "\nU%o : %o", i, X );
      i -:= 1;
    end for;
    printf s;
  else
    s := Sprintf( "Tensor of valence %o, ", t`Valence );
    i := t`Valence;
    while i gt 1 do
      s cat:= Sprintf( "U%o x ", i);
      i -:= 1;
    end while;
    s cat:= Sprintf( "U1 >-> U0" );
    i := t`Valence;
    for X in D do
      s cat:= Sprintf( "\nU%o : %o", i, X );
      i -:= 1;
    end for;
    printf s cat "\nU0 : %o", t`Codomain;
  end if;
end intrinsic;

// ------------------------------------------------------------------------------
//                                    Compare
// ------------------------------------------------------------------------------
intrinsic 'eq'( t::TenSpcElt, s::TenSpcElt ) -> BoolElt
{t eq s}
  if (t`Cat eq s`Cat) and (BaseRing(t) cmpeq BaseRing(s)) and (t`Domain cmpeq s`Domain) then
    try 
      _ := StructureConstants(t);
      _ := StructureConstants(s);
    catch e
      return forall{ x : x in CartesianProduct( <Generators(X) : X in t`Domain > ) | (x @ t) eq (x @ s) };
    end try;
    return t`CoordImages eq s`CoordImages;
  end if;
  return false;
end intrinsic;

// ------------------------------------------------------------------------------
//                                   Evaluation
// ------------------------------------------------------------------------------
intrinsic '@'( x::Tup, t::TenSpcElt ) -> .
{x @ t}
  if IsCoercible( Domain(t`Map), x ) then
    x := Domain(t`Map)!x;
  else
    require assigned t`Coerce : "Argument not in the domain.";
    require forall{ i : i in [1..#x] | IsCoercible( Domain(t`Coerce[i]), x[i] ) } : "Argument not in the domain.";
    x := < (Domain(t`Coerce[i])!x[i]) @ t`Coerce[i] : i in [1..#x] >;
  end if;
  return x @ t`Map;
end intrinsic;

// ------------------------------------------------------------------------------
//                                   Composition
// ------------------------------------------------------------------------------
intrinsic '*'( t::TenSpcElt, f::Map ) -> TenSpcElt
{t * f} 
  require not t`Cat`Contra : "Tensor must be covariant.";
  F := function(x)
    return x @ t @ f;
  end function;
  return __GetTensor( t`Domain, Codomain(f), F );
end intrinsic;

// ------------------------------------------------------------------------------
//                                     Parent
// ------------------------------------------------------------------------------
intrinsic Parent( t::TenSpcElt ) -> TenSpc
{Returns the parent of t.}
  if assigned t`Parent then
    return t`Parent;
  end if;
  require Type(BaseRing(t)) ne BoolElt : "Tensor has no base ring.";
  try
    if t`Cat`Contra then
      P := CotensorSpace( [* Generic(X) : X in Frame(t) *], t`Cat );
    else
      P := TensorSpace( [* Generic(X) : X in Frame(t) *], t`Cat );
    end if;
  catch err
    try 
      if t`Cat`Contra then
        P := CotensorSpace( [* Parent(X) : X in Frame(t) *], t`Cat );
      else
        P := TensorSpace( [* Parent(X) : X in Frame(t) *], t`Cat );
      end if;
    catch err
      if t`Cat`Contra then
        K := BaseRing(t);
        require ISA(Type(K),Fld) : "Base ring of cotensor must be a field.";
        P := KCotensorSpace( K, [ Dimension(X) : X in Frame(t) ], t`Cat ); 
      else
        P := RTensorSpace( BaseRing(t), [ Dimension(X) : X in Frame(t) ], t`Cat ); 
      end if;
    end try;
  end try;
  t`Parent := P;
  return P;
end intrinsic;

// ------------------------------------------------------------------------------
//                                Module Operations
// ------------------------------------------------------------------------------
intrinsic '+'( t::TenSpcElt, s::TenSpcElt ) -> TenSpcElt
{t+s}
  require Parent(t) eq Parent(s) : "Arguments are not compatible.";
  if (assigned t`Coerce) and (assigned s`Coerce) and (t`Coerce cmpeq s`Coerce) then
    coerce := t`Coerce;
  else
    coerce := false;
  end if;
  Mt := t`Map;
  Ms := s`Map;
  F := function(x)
    return (x@Mt) + (x@Ms);
  end function;
  return __GetTensor( Domain(t), Codomain(t), F : Par := Parent(t), Co := coerce, Cat := t`Cat );
end intrinsic;

intrinsic '*'( r::RngElt, t::TenSpcElt ) -> TenSpcElt
{r*t}
  R := BaseRing(t);
  require IsCoercible(R,r) : "Arguments are not compatible.";
  M := t`Map;
  F := function(x)
    return (R!r)*(x @ M);
  end function;
  if assigned t`Coerce then
    coerce := t`Coerce;
  else
    coerce := false;
  end if;
  if assigned t`Parent then
    parent := t`Parent;
  else
    parent := false;
  end if;
  return __GetTensor( Domain(t), Codomain(t), F : Par := parent, Co := coerce, Cat := t`Cat );
end intrinsic;
