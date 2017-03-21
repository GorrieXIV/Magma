freeze;

/*
  This file contains low-level definitions the bimap types: BmpU, BmpV, BmpUElt, 
  and BmpVElt.
*/


// ------------------------------------------------------------------------------
//                                      Print
// ------------------------------------------------------------------------------
intrinsic Print( U::BmpU )
{Print U}
  printf "Bimap space U: %o", U`Space;
end intrinsic;

intrinsic Print( V::BmpV )
{Print V}
  printf "Bimap space V: %o", V`Space;
end intrinsic;

intrinsic Print( u::BmpUElt )
{Print u}
  printf "Bimap element of U: %o", u`Element;
end intrinsic;

intrinsic Print( v::BmpVElt )
{Print v}
  printf "Bimap element of V: %o", v`Element;
end intrinsic;

// ------------------------------------------------------------------------------
//                                     Coerce
// ------------------------------------------------------------------------------
// Need to check if Generators will return erorrs on x. 
// If it will return an error, this function returns false.
__IsSpace := function( x )
  try 
    gens := Generators(x);
  catch e
    if assigned e`Object then
      return false;
    end if;
  end try;
  return true;
end function;

intrinsic IsCoercible( U::BmpU, x::. ) -> BoolElt, BmpUElt
{Decides if x can be coerced into U, and if so, returns the result.}
  B := Parent(U);
  if assigned B`Coerce then // first check we have a coerce function
    if IsCoercible(Domain(B`Coerce[1]),x) then // is it an element?
      x := (Domain(B`Coerce[1])!x) @ B`Coerce[1];
    else
      if __IsSpace(x) and forall{ g : g in Generators(x) | IsCoercible(Domain(B`Coerce[1]),g) } then // is it a space?
        x := sub< Codomain(B`Coerce[1]) | [ (Domain(B`Coerce[1])!g) @ B`Coerce[1] : g in Generators(x) ] >;
      end if;
    end if;
  end if;
  if IsCoercible( U`Space, x ) then
    u := New(BmpUElt);
    u`Parent := U;
    u`Element := U`Space!x;
    return true, u;
  elif Type( U`Space ) eq Type( x ) and forall{ g : g in Generators(x) | IsCoercible( U`Space, g ) } then
    X := New(BmpU);
    X`Parent := B;
    X`Space := sub< U`Space | [ U`Space!g : g in Generators(x) ] >;
    return true, X;
  else
    return false,"Arguments are incompatible.";
  end if;
end intrinsic;

intrinsic IsCoercible( V::BmpV, x::. ) -> BoolElt, BmpVElt
{Decides if x can be coerced into V, and if so, returns the result.}
  B := Parent(V);
  if assigned B`Coerce then // first check we have a coerce function
    if IsCoercible(Domain(B`Coerce[2]),x) then // is it an element?
      x := (Domain(B`Coerce[2])!x) @ B`Coerce[2];
    else
      if __IsSpace(x) and forall{ g : g in Generators(x) | IsCoercible(Domain(B`Coerce[2]),g) } then // is it a space?
        x := sub< Codomain(B`Coerce[2]) | [ (Domain(B`Coerce[2])!g) @ B`Coerce[2] : g in Generators(x) ] >;
      end if;
    end if;
  end if;
  if IsCoercible( V`Space, x ) then
    v := New(BmpVElt);
    v`Parent := V;
    v`Element := V`Space!x;
    return true, v;
  elif Type( V`Space ) eq Type( x ) and forall{ g : g in Generators(x) | IsCoercible( V`Space, g ) } then
    X := New(BmpV);
    X`Parent := Parent(V);
    X`Space := sub< V`Space | [ V`Space!g : g in Generators(x) ] >;
    return true, X;
  else
    return false,"Arguments are incompatible.";
  end if;
end intrinsic;

// ------------------------------------------------------------------------------
//                                     Parent
// ------------------------------------------------------------------------------
intrinsic Parent( U::BmpU ) -> TenSpcElt
{Returns the parent bilinear map for U.}
  return U`Parent;
end intrinsic;

intrinsic Parent( V::BmpV ) -> TenSpcElt
{Returns the parent bilinear map for V.}
  return V`Parent;
end intrinsic;

intrinsic Parent( u::BmpUElt ) -> BmpU
{Returns the parent U for u.}
  return u`Parent;
end intrinsic;

intrinsic Parent( v::BmpVElt ) -> BmpV
{Returns the parent V for v.}
  return v`Parent;
end intrinsic;

intrinsic LeftDomain( B::TenSpcElt ) -> BmpU
{Returns the left domain of B used for coercion.}
  require B`Valence eq 2 : "Must be a 2-tensor.";
  return B`Bimap`U;
end intrinsic;

intrinsic RightDomain( B::TenSpcElt ) -> BmpV
{Returns the right domain of B used for coercion.}
  require B`Valence eq 2 : "Must be a 2-tensor.";
  return B`Bimap`V;
end intrinsic;

// ------------------------------------------------------------------------------
//                                     Compare
// ------------------------------------------------------------------------------
intrinsic 'eq'( u1::BmpUElt, u2::BmpUElt ) -> BoolElt
{Decides if u1 and u2 are the same.}
  return u1`Element eq u2`Element;
end intrinsic;

intrinsic 'eq'( v1::BmpVElt, v2::BmpVElt ) -> BoolElt
{Decides if v1 and v2 are the same.}
  return v1`Element eq v2`Element;
end intrinsic;

intrinsic 'eq'( U1::BmpU, U2::BmpU ) -> BoolElt
{Decides if U1 and U2 are the same.}
  return U1`Space eq U2`Space;
end intrinsic;

intrinsic 'eq'( V1::BmpV, V2::BmpV ) -> BoolElt
{Decides if V1 and V2 are the same.}
  return V1`Space eq V2`Space;
end intrinsic;

// ------------------------------------------------------------------------------
//                             Multiplication : x * y
// ------------------------------------------------------------------------------
// Elements
intrinsic '*'( u::BmpUElt, v::BmpVElt ) -> .
{u * v}
  require Parent(Parent(u)) eq Parent(Parent(v)) : "Elements come from different bimaps.";
  B := Parent(Parent(u));
  x := u`Element;
  y := v`Element;
  return <x,y> @ B`Map;
end intrinsic;

// Subspaces
intrinsic '*'( X::BmpU, Y::BmpV ) -> .
{X * Y}
  require Parent(X) eq Parent(Y) : "Subspaces come from different bimaps.";
  B := Parent(X);
  S := X`Space;
  T := Y`Space;
  Z := sub< B`Codomain | [ <x,y> @ B`Map : x in Generators(S), y in Generators(T) ] >;
  return Z;
end intrinsic;

// Mixed: elements and subspaces
intrinsic '*'( x::BmpUElt, Y::BmpV ) -> .
{x * Y}
  require Parent(Parent(x)) eq Parent(Y) : "Arguments come from different bimaps.";
  B := Parent(Y);
  u := x`Element;
  S := Y`Space;
  Z := sub< B`Codomain | [ <u,y> @ B`Map : y in Generators(S) ] >;
  return Z;
end intrinsic;

// Mixed: subspaces and elements
intrinsic '*'( X::BmpU, y::BmpVElt ) -> .
{X * Y}
  require Parent(X) eq Parent(Parent(y)) : "Arguments come from different bimaps.";
  B := Parent(X);
  S := X`Space;
  v := y`Element;
  Z := sub< B`Codomain | [ <x,v> @ B`Map : x in Generators(S) ] >;
  return Z;
end intrinsic;


// The following are possible user errors. The goal is to have all the possibilities defined,
// so that the error statement points to the problem instead of saying the product isn't defined.
//1
intrinsic '*'( x::BmpVElt, y::BmpUElt ) -> .
{x * y}
  require Parent(Parent(x)) eq Parent(Parent(y)) : "Elements come from different bimaps.";
  B := Parent(Parent(x));
  require IsCoercible( B`Bimap`U`Space, x`Element ) : "Argument 1 not in left domain.";
  x := B`Bimap`U`Space!(x`Element);
  require IsCoercible( B`Bimap`V`Space, y`Element ) : "Argument 2 not in right domain.";
  y := B`Bimap`V`Space!(y`Element);
  return (B`Bimap`U!x) * (B`Bimap`V!y);
end intrinsic;

//2
intrinsic '*'( X::BmpV, y::BmpUElt ) -> .
{X * y}
  require Parent(X) eq Parent(Parent(y)) : "Elements come from different bimaps.";
  B := Parent(X);
  require forall{ x : x in Generators(X`Space) | IsCoercible( B`Bimap`U`Space, x ) } : "Argument 1 not in left domain.";
  X := sub< B`Bimap`U`Space | [ B`Bimap`U`Space!x : x in Generators(X`Space) ] >;
  require IsCoercible( B`Bimap`V`Space, y`Element ) : "Argument 2 not in right domain.";
  y := B`Bimap`V`Space!(y`Element);
  return (B`Bimap`U!X) * (B`Bimap`V!y);
end intrinsic;

//3
intrinsic '*'( x::BmpVElt, Y::BmpU ) -> .
{x * Y}
  require Parent(Parent(x)) eq Parent(Y) : "Elements come from different bimaps.";
  B := Parent(Y);
  require IsCoercible( B`Bimap`U`Space, x`Element ) : "Argument 1 not in left domain.";
  x := B`Bimap`U`Space!(x`Element);
  require forall{ y : y in Generators(Y`Space) | IsCoercible( B`Bimap`V`Space, y ) } : "Argument 2 not in right domain.";
  Y := sub< B`Bimap`V`Space | [ B`Bimap`V`Space!y : y in Generators(Y`Space) ] >;
  return (B`Bimap`U!x) * (B`Bimap`V!Y);
end intrinsic;

//4
intrinsic '*'( X::BmpV, Y::BmpU ) -> .
{X * Y}
  require Parent(X) eq Parent(Y) : "Elements come from different bimaps.";
  B := Parent(X);
  require forall{ x : x in Generators(X`Space) | IsCoercible( B`Bimap`U`Space, x ) } : "Argument 1 not in left domain.";
  X := sub< B`Bimap`U`Space | [ B`Bimap`U`Space!x : x in Generators(X`Space) ] >;
  require forall{ y : y in Generators(Y`Space) | IsCoercible( B`Bimap`V`Space, y ) } : "Argument 2 not in right domain.";
  Y := sub< B`Bimap`V`Space | [ B`Bimap`V`Space!y : y in Generators(Y`Space) ] >;
  return (B`Bimap`U!X) * (B`Bimap`V!Y);
end intrinsic;

//5
intrinsic '*'( x::BmpUElt, y::BmpUElt ) -> .
{x * y}
  require Parent(Parent(x)) eq Parent(Parent(y)) : "Elements come from different bimaps.";
  B := Parent(Parent(x));
  require IsCoercible( B`Bimap`V`Space, y`Element ) : "Argument 2 not in right domain.";
  y := B`Bimap`V`Space!(y`Element);
  return x * (B`Bimap`V!y);
end intrinsic;

//6
intrinsic '*'( X::BmpU, y::BmpUElt ) -> .
{X * y}
  require Parent(X) eq Parent(Parent(y)) : "Elements come from different bimaps.";
  B := Parent(X);
  require IsCoercible( B`Bimap`V`Space, y`Element ) : "Argument 2 not in right domain.";
  y := B`Bimap`V`Space!(y`Element);
  return X * (B`Bimap`V!y);
end intrinsic;

//7
intrinsic '*'( x::BmpUElt, Y::BmpU ) -> .
{x * Y}
  require Parent(Parent(x)) eq Parent(Y) : "Elements come from different bimaps.";
  B := Parent(Y);
  require forall{ y : y in Generators(Y`Space) | IsCoercible( B`Bimap`V`Space, y ) } : "Argument 2 not in right domain.";
  Y := sub< B`Bimap`V`Space | [ B`Bimap`V`Space!y : y in Generators(Y`Space) ] >;
  return x * (B`Bimap`V!Y);
end intrinsic;

//8
intrinsic '*'( X::BmpU, Y::BmpU ) -> .
{X * Y}
  require Parent(X) eq Parent(Y) : "Elements come from different bimaps.";
  B := Parent(X);
  require forall{ y : y in Generators(Y`Space) | IsCoercible( B`Bimap`V`Space, y ) } : "Argument 2 not in right domain.";
  Y := sub< B`Bimap`V`Space | [ B`Bimap`V`Space!y : y in Generators(Y`Space) ] >;
  return X * (B`Bimap`V!Y);
end intrinsic;

//9
intrinsic '*'( x::BmpVElt, y::BmpVElt ) -> .
{x * y}
  require Parent(Parent(x)) eq Parent(Parent(y)) : "Elements come from different bimaps.";
  B := Parent(Parent(x));
  require IsCoercible( B`Bimap`U`Space, x`Element ) : "Argument 1 not in left domain.";
  x := B`Bimap`U`Space!(x`Element);
  return (B`Bimap`U!x) * y;
end intrinsic;

//10
intrinsic '*'( X::BmpV, y::BmpVElt ) -> .
{X * y}
  require Parent(X) eq Parent(Parent(y)) : "Elements come from different bimaps.";
  B := Parent(X);
  require forall{ x : x in Generators(X`Space) | IsCoercible( B`Bimap`U`Space, x ) } : "Argument 1 not in left domain.";
  X := sub< B`Bimap`U`Space | [ B`Bimap`U`Space!x : x in Generators(X`Space) ] >;
  return (B`Bimap`U!X) * y;
end intrinsic;

//11
intrinsic '*'( x::BmpVElt, Y::BmpV ) -> .
{x * Y}
  require Parent(Parent(x)) eq Parent(Y) : "Elements come from different bimaps.";
  B := Parent(Y);
  require IsCoercible( B`Bimap`U`Space, x`Element ) : "Argument 1 not in left domain.";
  x := B`Bimap`U`Space!(x`Element);
  return (B`Bimap`U!x) * Y;
end intrinsic;

//12
intrinsic '*'( X::BmpV, Y::BmpV ) -> .
{X * Y}
  require Parent(X) eq Parent(Y) : "Elements come from different bimaps.";
  B := Parent(X);
  require forall{ x : x in Generators(X`Space) | IsCoercible( B`Bimap`U`Space, x ) } : "Argument 1 not in left domain.";
  X := sub< B`Bimap`U`Space | [ B`Bimap`U`Space!x : x in Generators(X`Space) ] >;
  return (B`Bimap`U!X) * Y;
end intrinsic;

// ------------------------------------------------------------------------------
//                            Muliplication : x * B * y
// ------------------------------------------------------------------------------
intrinsic '*'( x::., B::TenSpcElt ) -> TenSpcElt
{x * B}
  require B`Valence le 2 : "Operation only defined for 2-tensors.";
  if B`Valence eq 1 then
    try
      return <x> @ B;
    catch err
      error "Argument not contained in the domain.";
    end try;
  end if;
  try
    x := B`Domain[1]!x;
  catch err
    try
      x := (Domain(B`Coerce[1])!x) @ B`Coerce[1];
    catch err
      error "Argument not contained in left domain.";
    end try;
  end try;
  V := B`Domain[2];
  W := B`Codomain;
  F := function(y)
    return < x,y[1] > @ B;
  end function;
  L := Tensor( [V,W], F );
  if assigned B`Coerce then
    L`Coerce := B`Coerce[2..3];
  end if;
  return L;
end intrinsic;

intrinsic '*'( B::TenSpcElt, y::. ) -> .
{B * y}
  require B`Valence le 2 : "Operation only defined for 2-tensors.";
  if B`Valence eq 1 then
    try
      return <y> @ B;
    catch err
      error "Argument not contained in the domain.";
    end try;
  end if;
  try
    y := B`Domain[2]!y;
  catch err
    try
      y := (Domain(B`Coerce[2])!y) @ B`Coerce[2];
    catch err
      error "Argument not contained in right domain.";
    end try;
  end try;
  U := B`Domain[1];
  W := B`Codomain;
  F := function(x)
    return < x[1],y > @ B;
  end function;
  L := Tensor( [U,W], F );
  if assigned B`Coerce then
    L`Coerce := B`Coerce[[1,3]];
  end if;
  return L;
end intrinsic;
