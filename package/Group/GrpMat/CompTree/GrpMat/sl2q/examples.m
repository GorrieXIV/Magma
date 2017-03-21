// load "gamma.m";
// load "symmetric-power.m";

MySymmetricPower := function (G, n)
   M:=GModule (G);
   A := SymmetricPower (M, n);
   return ActionGroup (A);
end function;

/* given matrix x, return result of applying Frobenius automorphism 
   x[i][j] --> x[i][j]^n to it */

GammaLMatrix := function (x, n)

   G := Parent (x);
   G := GL (Degree (G), BaseRing (G));
   e := Eltseq (x);
   ee := [y^n : y in e];
   return G!ee;
     
end function;

TwistedSymmetricPower := function (G, s, f)
   d := Degree (G);
   F := BaseRing (G);
   p := Characteristic (F);
   S := MySymmetricPower (G, s);
   Gens := [S.i : i in [1..Ngens (G)]];
   Twisted := [GammaLMatrix (Gens[i], p^f) : i in [1..#Gens]];
   return sub <GL (Degree (S), F) | Twisted>;
end function;
 
/* tensor product of twisted symmetric powers defined
   over GF (p^e); s lists the symmetric powers,
   f is the twisting via powers of the Frobenius 
   automorphism to be applied to each symmetric power */

SymmetricPowerExample := function (p, e, s, f: Tensor := true)

   F := GF (p, e);
   L := SL (2, F);
   G := TwistedSymmetricPower (L, s[1], f[1]);

   if Tensor eq false then return G; end if;

   for i in [2..#s] do 
      T2 := TwistedSymmetricPower (L, s[i], f[i]);
      G := sub <GL (Degree (G) * Degree (T2), F ) | 
                 [TensorProduct (G.i, T2.i): i in [1..Ngens (G)]]>;
   end for;

   return G;

end function;
