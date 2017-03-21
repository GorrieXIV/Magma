freeze;

/*
  This file contains all the low-level definitions for homotopisms (Hmtp).
*/


import "Hom.m" : __GetHomotopism;
// ------------------------------------------------------------------------------
//                                     Print
// ------------------------------------------------------------------------------
intrinsic Print( H::Hmtp )
{Print H}
  A := H`Cat`Arrows;
  v := H`Domain`Valence;
  s := Sprintf( "Maps from " );
  for i in [1..v-1] do
    s cat:= Sprintf( "U%o x ", v-i+1 );
  end for;
  s cat:= Sprintf( "U1 >-> U0 to " );
  for i in [1..v-1] do
    s cat:= Sprintf( "V%o x ", v-i+1 );
  end for;
  s cat:= Sprintf( "V1 >-> V0." );
  t := H`Domain;
  for i in Reverse([1..v]) do
    if ISA(Type(H`Maps[v-i+1]),Mtrx) then
      u := "\n";
    else
      u := "";
    end if;
    if i @ A eq 1 then
      s cat:= Sprintf( "\nU%o -> V%o: " cat u cat "%o", i, i, H`Maps[v-i+1] );
    elif i @ A eq -1 then
      s cat:= Sprintf( "\nU%o <- V%o: " cat u cat "%o", i, i, H`Maps[v-i+1] );
    else
      s cat:= Sprintf( "\nU%o == V%o: " cat u cat "%o", i, i, H`Maps[v-i+1] );
    end if;
  end for;
  if ISA(Type(H`Maps[v+1]),Mtrx) then
    u := "\n";
  else
    u := "";
  end if;
  if H`Cat`Contra then
    printf s;
  else
    if 0 @ A eq 1 then
      printf s cat Sprintf( "\nU0 -> V0: " cat u cat "%o", H`Maps[v+1] );
    elif 0 @ A eq -1 then
      printf s cat Sprintf( "\nU0 <- V0: " cat u cat "%o", H`Maps[v+1] );
    else
      printf s cat Sprintf( "\nU0 == V0: " cat u cat "%o", H`Maps[v+1] );
    end if;
  end if;
end intrinsic;

// ------------------------------------------------------------------------------
//                                   Composition
// ------------------------------------------------------------------------------
intrinsic '*'( H1::Hmtp, H2::Hmtp ) -> Hmtp
{H1 * H2}
  dom := H1`Domain;
  cod := H2`Codomain;
  require H1`Cat eq H2`Cat: "Categories are incompatible.";
  M := [* *];
  for i in Reverse([0..dom`Valence]) do
    if i @ H1`Cat`Arrows eq -1 then
      f := H2`Maps[dom`Valence-i+1];
      g := H1`Maps[dom`Valence-i+1];
    else
      f := H1`Maps[dom`Valence-i+1];
      g := H2`Maps[dom`Valence-i+1];
    end if;
    try
      Append(~M,f*g);
    catch err
      error "Cannot compose maps.";
    end try;
  end for;
  return __GetHomotopism( dom, cod, M );
end intrinsic;
