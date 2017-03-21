freeze;

intrinsic GaloisGroup( E::FldFin, F::FldFin ) -> GrpPerm, []
{The Galois group of a finite extension of a finite field and the roots.}

  require F subset E:
    "F must be a subfield of E";

  d := Degree( E, F );  q := #F;

  sigma := hom< E -> E | x :-> x^q, x :-> x^(q^(d-1)) >;
  sigma`IsInjective := true; sigma`IsSurjective := true;

  x := Generator(E, F);
  l := [x];
  for i in [2..d] do 
    Append(~l, sigma(l[i-1]));
  end for;

  return CyclicGroup( GrpPerm, d ), l;
end intrinsic;

intrinsic AutomorphismGroup(E::FldFin, F::FldFin) -> GrpPerm, PowMap, Map
{The Automorphism group of E over F.}

  require F subset E: "F must be a subfield of E";

  d := Degree( E, F );  q := #F;

     id := hom< E -> E | x :-> x,   x :-> x           >;
  sigma := hom< E -> E | x :-> x^q, x :-> x^(q^(d-1)) >;
     id`IsInjective := true;    id`IsSurjective := true;
  sigma`IsInjective := true; sigma`IsSurjective := true;

  l := [id];
  for i in [2..d] do 
    Append(~l, l[i-1]*sigma);
  end for;

  C := CyclicGroup(GrpPerm, d);
  a := AbelianGroup([d]);
  b := hom<C -> a | a.1>;
//  a,b := AbelianGroup(C); // SLOW
  m := map<C -> Universe(l) | x :-> (x eq Id(C)) select l[1] else l[Eltseq(b(x))[1]+1]>;

  return C, l, m;
end intrinsic;
