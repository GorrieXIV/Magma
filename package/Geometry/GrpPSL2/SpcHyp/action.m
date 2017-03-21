freeze;

intrinsic Stabilizer(a::SpcHypElt,G::GrpPSL2) -> GrpPSL2Elt
   {returns a generator of the stabilizer subgroup of a in G}
   // we will make some assumptions about the point:
   require IsExact(a): "stabilizers are only computed for exact
   values";
   require IsCongruence(G): "G must be a congruence subgroup";
   
   SL2 := PSL2(Integers());
   if IsCusp(a) then
      _,g := EquivalentPoint(a);
      w := CuspWidth(G,ExactValue(a));
      T := SL2![1,1,0,1];
      return G!(g^(-1)*T^w*g);
   end if;

   // we assume that G is a congruence subgroup, so non cusps
   // which are real are only fixed by the identity:
   if Imaginary(a) eq 0 then
      return G!1;
   end if;

   // for other points, they can only have non trivial
   // stabilizer if they are in some quadratic extension
   // with discriminant -3 or -4, and that such points are
   // equivalent to i or r (r^3 = -1)
   // they are fixed by matrixes that have order 2 or 3,
   // so if such a matrix is not in G, then the only powers
   // of it that are are the identity (we are assuming that
   // matrices are considered projectively here, since non
   // projectively, we may have x not in G, but x^2 in G)
   if Type(ExactValue(a)) ne FldQuadElt then
      return G!1;
   end if;
   
   z,g := EquivalentPoint(a);
   K := Parent(ExactValue(z));
   d := -Rationals()!((K![0,1])^2);
   real,imag := Explode(Eltseq(ExactValue(z)));
   abs_square := (real)^2 + d*imag^2;
   if abs_square gt 1 then
      return G!1;
   end if;

   SL := PSL2(Integers());
   S := SL![0,-1,1,0];   
   R := SL![0,1,-1,1];
   
   if real eq 0 then
      matrix := g^(-1)*S*g;
      if matrix in G then
	 return G!matrix;
      end if;
   end if;

   if real eq 1/2 then
      matrix := g^(-1)*R*g;
      if matrix in G then
	 return G!matrix;
      end if;
   end if;

   return G!1;
end intrinsic;

